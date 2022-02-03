// SPDX-FileCopyrightText: 2022 Florian Märkl <info@florianmaerkl.de>
// SPDX-License-Identifier: LGPL-3.0-only

#include <rz_analysis.h>
#include <capstone.h>

#include "arm_cs.h"
#include "arm_accessors32.h"

#include <rz_il/rz_il_opbuilder_begin.h>

/**
 * All regs available as global IL variables
 */
static const char *regs_bound_32[] = {
	"lr", "sp",
	"vf", "cf", "zf", "nf",
	"r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8", "r9", "r10", "r11", "r12",
	"q0", "q1", "q2", "q3", "q4", "q5", "q6", "q7", "q8", "q9", "q10", "q11", "q12", "q13", "q14", "q15",
	NULL
};

/**
 * Variable name for a register given by cs
 */
static const char *reg_var_name(arm_reg reg) {
	const char *names[] = {
		// TODO: check how well-packed this is and maybe use switch instead
		[ARM_REG_LR] = "lr",
		[ARM_REG_SP] = "sp",
		[ARM_REG_Q0] = "q0",
		[ARM_REG_Q1] = "q1",
		[ARM_REG_Q2] = "q2",
		[ARM_REG_Q3] = "q3",
		[ARM_REG_Q4] = "q4",
		[ARM_REG_Q5] = "q5",
		[ARM_REG_Q6] = "q6",
		[ARM_REG_Q7] = "q7",
		[ARM_REG_Q8] = "q8",
		[ARM_REG_Q9] = "q9",
		[ARM_REG_Q10] = "q10",
		[ARM_REG_Q11] = "q11",
		[ARM_REG_Q12] = "q12",
		[ARM_REG_Q13] = "q13",
		[ARM_REG_Q14] = "q14",
		[ARM_REG_Q15] = "q15",
		[ARM_REG_R0] = "r0",
		[ARM_REG_R1] = "r1",
		[ARM_REG_R2] = "r2",
		[ARM_REG_R3] = "r3",
		[ARM_REG_R4] = "r4",
		[ARM_REG_R5] = "r5",
		[ARM_REG_R6] = "r6",
		[ARM_REG_R7] = "r7",
		[ARM_REG_R8] = "r8",
		[ARM_REG_R9] = "r9",
		[ARM_REG_R10] = "r10",
		[ARM_REG_R11] = "r11",
		[ARM_REG_R12] = "r12"
	};
	if (reg < 0 || reg >= RZ_ARRAY_SIZE(names)) {
		return NULL;
	}
	return names[reg];
}

/**
 * IL to read the given capstone reg
 */
static RzILOpBitVector *read_reg(ut64 pc, arm_reg reg) {
	if (reg == ARM_REG_PC) {
		return U32(pc);
	}
	const char *var = reg_var_name(reg);
	return var ? VARG(var) : NULL;
}

#define PC(addr, is_thumb) ((addr + (is_thumb ? 4 : 8)) & ~3)
#define REG_VAL(id)        read_reg(PC(insn->address, is_thumb), id)
#define REG(n)             REG_VAL(REGID(n))
#define MEMBASE(x)         REG_VAL(insn->detail->arm.operands[x].mem.base)
#define MEMINDEX(x)        REG_VAL(insn->detail->arm.operands[x].mem.index)

/**
 * IL to write the given capstone reg
 */
static RzILOpEffect *write_reg(arm_reg reg, RZ_OWN RZ_NONNULL RzILOpBitVector *v) {
	rz_return_val_if_fail(v, NULL);
	const char *var = reg_var_name(reg);
	return var ? SETG(var, v) : NULL;
}

/**
 * IL for arm condition
 * unconditional is returned as NULL (rather than true), for simpler code
 */
static RZ_NULLABLE RzILOpBool *cond(arm_cc c) {
	switch (c) {
	case ARM_CC_EQ:
		return VARG("zf");
	case ARM_CC_NE:
		return INV(VARG("zf"));
	case ARM_CC_HS:
		return VARG("cf");
	case ARM_CC_LO:
		return INV(VARG("cf"));
	case ARM_CC_MI:
		return VARG("nf");
	case ARM_CC_PL:
		return INV(VARG("nf"));
	case ARM_CC_VS:
		return VARG("vf");
	case ARM_CC_VC:
		return INV(VARG("vf"));
	case ARM_CC_HI:
		return AND(VARG("cf"), INV(VARG("zf")));
	case ARM_CC_LS:
		return OR(INV(VARG("cf")), VARG("zf"));
	case ARM_CC_GE:
		return INV(XOR(VARG("nf"), VARG("vf")));
	case ARM_CC_LT:
		return XOR(VARG("nf"), VARG("vf"));
	case ARM_CC_GT:
		return AND(INV(VARG("zf")), INV(XOR(VARG("nf"), VARG("vf"))));
	case ARM_CC_LE:
		return OR(VARG("zf"), XOR(VARG("nf"), VARG("vf")));
	case ARM_CC_AL:
	default:
		return NULL;
	}
}

static RZ_NULLABLE RzILOpBitVector *shift(RzILOpBitVector *val, arm_shifter type, ut8 dist) {
	switch (type) {
	case ARM_SFT_ASR:
		return SHIFTRA(val, UN(5, dist));
	case ARM_SFT_LSL:
		return SHIFTL0(val, UN(5, dist));
	case ARM_SFT_LSR:
		return SHIFTR0(val, UN(5, dist));
	case ARM_SFT_ROR:
		return LOGOR(
			SHIFTR0(val, UN(5, dist)),
			SHIFTL0(DUP(val), UN(5, 32 - dist)));
	case ARM_SFT_RRX:
		return SHIFTR(VARG("cf"), val, UN(5, 1));
	default:
		return val;
	}
}

/**
 * IL to retrieve the value of the \p n -th arg of \p insn
 * \p carry_out filled with the carry value of NULL if it does not change
 */
static RzILOpBitVector *arg(cs_insn *insn, bool is_thumb, int n, RZ_NULLABLE RzILOpBool **carry_out) {
	if (carry_out) {
		*carry_out = NULL;
	}
	cs_arm_op *op = &insn->detail->arm.operands[n];
	switch (op->type) {
	case ARM_OP_REG: {
		RzILOpBitVector *r = REG(n);
		return r ? shift(r, op->shift.type, op->shift.value) : NULL;
	}
	case ARM_OP_IMM: {
		ut32 imm = IMM(n);
		if (carry_out) {
			// Some "movs"s leave c alone, some set it to the highest bit of the result.
			// Determining which one it is from capstone's info is tricky:
			// Arm defines that it is set when the imm12's rotate value is not 0.
			// This is the case when:
			// * capstone disassembles to something like "movs r0, 0, 2", giving us an explicit third operand
			// * capstone disassembles to something like "movs r0, 0x4000000" without the third operand,
			//   but we can see that the value is larger than 8 bits, so there must be a shift.
			if (ISIMM(n + 1) || imm > 0xff) {
				*carry_out = (imm & (1 << 31)) ? IL_TRUE : IL_FALSE;
			}
		}
		return U32(imm);
	}
	case ARM_OP_MEM: {
		RzILOpBitVector *addr = MEMBASE(n);
		int disp = MEMDISP(n);
		if (disp > 0) {
			addr = ADD(addr, U32(disp));
		} else if (disp < 0) {
			addr = SUB(addr, U32(-disp));
		}
		if (op->mem.index != ARM_REG_INVALID) {
			addr = ADD(addr, shift(MEMINDEX(n), op->shift.type, op->shift.value));
		}
		return addr;
	}
	default:
		break;
	}
	return NULL;
}

#define ARG_C(n, carry) arg(insn, is_thumb, n, carry)
#define ARG(n)          ARG_C(n, NULL)

/**
 * zf := v == 0
 * nf := msb v
 */
static RzILOpEffect *update_flags_zn(RzILOpBitVector *v) {
	return SEQ2(
		SETG("zf", IS_ZERO(v)),
		SETG("nf", MSB(DUP(v))));
}

/**
 * Carry resulting from a + b (+ cf)
 */
static RZ_OWN RzILOpBool *add_carry(RZ_OWN RzILOpBitVector *a, RZ_OWN RzILOpBitVector *b, bool with_carry) {
	RzILOpBitVector *r = ADD(UNSIGNED(33, a), UNSIGNED(33, b));
	if (with_carry) {
		r = ADD(r, ITE(VARG("cf"), UN(33, 1), UN(33, 0)));
	}
	return MSB(r);
}

/**
 * Carry resulting from a - b
 */
static RZ_OWN RzILOpBool *sub_carry(RZ_OWN RzILOpBitVector *a, RZ_OWN RzILOpBitVector *b) {
	return ULE(b, a);
}

/**
 * Overflow (V) resulting from a + b
 */
static RZ_OWN RzILOpBool *add_overflow(RZ_OWN RzILOpBitVector *a, RZ_OWN RzILOpBitVector *b, RZ_OWN RzILOpBitVector *res) {
	return AND(INV(XOR(MSB(a), MSB(b))), XOR(MSB(DUP(a)), MSB(res)));
}

/**
 * Overflow (V) resulting from a - b
 */
static RZ_OWN RzILOpBool *sub_overflow(RZ_OWN RzILOpBitVector *a, RZ_OWN RzILOpBitVector *b, RZ_OWN RzILOpBitVector *res) {
	return AND(XOR(MSB(a), MSB(b)), XOR(MSB(DUP(a)), MSB(res)));
}

/**
 * Capstone: ARM_INS_MOV, ARM_INS_MOVW
 * ARM: mov, movs, movw
 */
static RzILOpEffect *mov(cs_insn *insn, bool is_thumb) {
	if (!ISREG(0) || (!ISIMM(1) && !ISREG(1))) {
		return NULL;
	}
	bool update_flags = insn->detail->arm.update_flags;
	RzILOpBool *carry;
	RzILOpPure *val = ARG_C(1, update_flags ? &carry : NULL);
	if (!val) {
		return NULL;
	}
	if (REGID(0) == ARM_REG_PC) {
		if (insn->detail->arm.update_flags) {
			// TODO: ALUExceptionReturn()
			goto err;
		} else {
			return JMP(val);
		}
	}
	RzILOpEffect *eff = write_reg(REGID(0), val);
	if (!eff) {
		goto err;
	}
	if (update_flags) {
		RzILOpEffect *zn = update_flags_zn(DUP(val));
		return carry
			? SEQ3(eff, SETG("cf", carry), zn)
			: SEQ2(eff, zn);
	}
	return eff;
err:
	rz_il_op_pure_free(carry);
	rz_il_op_pure_free(val);
	return NULL;
}

/**
 * Capstone: ARM_INS_MOVT
 * ARM: movt
 */
static RzILOpEffect *movt(cs_insn *insn, bool is_thumb) {
	if (!ISREG(0) || !ISIMM(1)) {
		return NULL;
	}
	RzILOpPure *regval = REG(0);
	if (!regval) {
		return NULL;
	}
	return write_reg(REGID(0), APPEND(U16(IMM(1)), UNSIGNED(16, regval)));
}

/**
 * Capstone: ARM_INS_ADD, ARM_INS_ADC, ARM_INS_SUB
 * ARM: add, adds, adc, adcs, sub, subs
 */
static RzILOpEffect *add_sub(cs_insn *insn, bool is_thumb) {
	if (!ISREG(0)) {
		return NULL;
	}
	bool is_sub = insn->id == ARM_INS_SUB;
	RzILOpBitVector *a = ARG(OPCOUNT() > 2 ? 1 : 0);
	RzILOpBitVector *b = ARG(OPCOUNT() > 2 ? 2 : 1);
	if (!a || !b) {
		rz_il_op_pure_free(a);
		rz_il_op_pure_free(b);
		return NULL;
	}
	RzILOpBitVector *res = is_sub ? SUB(a, b) : ADD(a, b);
	bool with_carry = insn->id == ARM_INS_ADC;
	if (with_carry) {
		res = ADD(res, ITE(VARG("cf"), U32(1), U32(0)));
	}
	if (REGID(0) == ARM_REG_PC) {
		if (insn->detail->arm.update_flags) {
			// TODO: ALUExceptionReturn()
			rz_il_op_pure_free(res);
			return NULL;
		} else {
			return JMP(res);
		}
	}
	RzILOpEffect *set = write_reg(REGID(0), res);
	bool update_flags = insn->detail->arm.update_flags;
	if (!strcmp(insn->mnemonic, "adc")) {
		// capstone is wrong about this, only "adcs" sets flags
		update_flags = false;
	}
	if (update_flags) {
		return SEQ6(
			SETL("a", DUP(a)),
			SETL("b", DUP(b)),
			set,
			SETG("cf", is_sub ? sub_carry(VARL("a"), VARL("b")) : add_carry(VARL("a"), VARL("b"), with_carry)),
			SETG("vf", (is_sub ? sub_overflow : add_overflow)(VARL("a"), VARL("b"), REG(0))),
			update_flags_zn(REG(0)));
	}
	return set;
}

/**
 * Capstone: ARM_INS_MUL
 * ARM: mul, muls
 */
static RzILOpEffect *mul(cs_insn *insn, bool is_thumb) {
	if (!ISREG(0)) {
		return NULL;
	}
	RzILOpBitVector *a = ARG(OPCOUNT() > 2 ? 1 : 0);
	RzILOpBitVector *b = ARG(OPCOUNT() > 2 ? 2 : 1);
	if (!a || !b) {
		rz_il_op_pure_free(a);
		rz_il_op_pure_free(b);
		return NULL;
	}
	RzILOpEffect *eff = write_reg(REGID(0), MUL(a, b));
	if (!eff) {
		return NULL;
	}
	return insn->detail->arm.update_flags ? SEQ2(eff, update_flags_zn(REG(0))) : eff;
}

/**
 * Capstone: ARM_INS_LDR, ARM_INS_LDRB, ARM_INS_LDRH, ARM_INS_LDRT, ARM_INS_LDRBT, ARM_INS_LDRHT
 * ARM: ldr, ldrb, ldrh, ldrt, ldrbt, ldrht
 */
static RzILOpEffect *ldr(cs_insn *insn, bool is_thumb) {
	size_t mem_idx = 1;
	if (!ISREG(0) || !ISMEM(mem_idx)) {
		return NULL;
	}
	RzILOpBitVector *addr = ARG(mem_idx);
	if (!addr) {
		return NULL;
	}
	bool writeback = insn->detail->arm.writeback;
	if (ISIMM(mem_idx + 1)) {
		// capstone incorrectly sets writeback to false for e.g. 0400b1e4 ldrt r0, [r1], 4
		writeback = true;
	}
	RzILOpEffect *writeback_eff = NULL;
	bool writeback_post = false;
	if (writeback) {
		arm_reg base = insn->detail->arm.operands[mem_idx].mem.base;
		if (ISIMM(mem_idx + 1)) {
			// "ldr r0, [r1], 4" is treated as an extra operand after the mem
			addr = insn->detail->arm.operands[mem_idx + 1].subtracted
				? SUB(addr, ARG(mem_idx + 1))
				: ADD(addr, ARG(mem_idx + 1));
			writeback_post = true;
		}
		writeback_eff = write_reg(base, addr);
		if (writeback_eff) {
			addr = MEMBASE(mem_idx);
		}
	}
	RzILOpBitVector *data;
	switch (insn->id) {
	case ARM_INS_LDRB:
	case ARM_INS_LDRBT:
		data = UNSIGNED(32, LOAD(addr));
		break;
	case ARM_INS_LDRH:
	case ARM_INS_LDRHT:
		data = UNSIGNED(32, LOADW(16, addr));
		break;
	default: // ARM_INS_LDR, ARM_INS_LDRT
		data = LOADW(32, addr);
		break;
	}
	RzILOpEffect *eff;
	if (REGID(0) == ARM_REG_PC) {
		eff = JMP(data);
		if (writeback_post) {
			// can't have writeback after the jmp, so need to handle this special case with a local var
			return SEQ3(
				SETL("tgt", data),
				writeback_eff,
				JMP(VARL("tgt")));
		}
	} else {
		eff = write_reg(REGID(0), data);
	}
	if (writeback_eff) {
		return writeback_post ? SEQ2(eff, writeback_eff) : SEQ2(writeback_eff, eff);
	}
	return eff;
}

/**
 * Capstone: ARM_INS_STR, ARM_INS_STRB, ARM_INS_STRH, ARM_INS_STRT, ARM_INS_STRBT, ARM_INS_STRHT
 * ARM: str, strb, strh, strt, strbt, strht
 */
static RzILOpEffect *str(cs_insn *insn, bool is_thumb) {
	size_t mem_idx = 1;
	if (!ISREG(0) || !ISMEM(mem_idx)) {
		return NULL;
	}
	RzILOpBitVector *addr = ARG(mem_idx);
	if (!addr) {
		return NULL;
	}
	bool writeback = insn->detail->arm.writeback;
	if (ISIMM(mem_idx + 1)) {
		// capstone incorrectly sets writeback to false for e.g. 04b0ade4 strt fp, [sp], 4
		writeback = true;
	}
	RzILOpEffect *writeback_eff = NULL;
	bool writeback_post = false;
	if (writeback) {
		arm_reg base = insn->detail->arm.operands[mem_idx].mem.base;
		if (ISIMM(mem_idx + 1)) {
			// "str r0, [r1], 4" is treated as an extra operand after the mem
			addr = insn->detail->arm.operands[mem_idx + 1].subtracted
				? SUB(addr, ARG(mem_idx + 1))
				: ADD(addr, ARG(mem_idx + 1));
			writeback_post = true;
		}
		writeback_eff = write_reg(base, addr);
		if (writeback_eff) {
			addr = MEMBASE(mem_idx);
		}
	}
	RzILOpBitVector *val = ARG(0);
	if (!val) {
		rz_il_op_pure_free(addr);
		return NULL;
	}
	RzILOpEffect *eff;
	switch (insn->id) {
	case ARM_INS_STRB:
	case ARM_INS_STRBT:
		eff = STORE(addr, UNSIGNED(8, val));
		break;
	case ARM_INS_STRH:
	case ARM_INS_STRHT:
		eff = STOREW(addr, UNSIGNED(16, val));
		break;
	default: // ARM_INS_STR, ARM_INS_STRT
		eff = STOREW(addr, val);
		break;
	}
	if (writeback_eff) {
		return writeback_post ? SEQ2(eff, writeback_eff) : SEQ2(writeback_eff, eff);
	}
	return eff;
}

/**
 * Capstone: ARM_INS_AND, ARM_INS_ORR, ARM_INS_EOR
 * ARM: and, ands, orr, orrs, orn, orns, eor, eors
 */
static RzILOpEffect *bitwise(cs_insn *insn, bool is_thumb) {
	if (!ISREG(0)) {
		return NULL;
	}
	bool update_flags = insn->detail->arm.update_flags;
	RzILOpBitVector *a = ARG(1);
	RzILOpBool *carry = NULL;
	RzILOpBitVector *b = ARG_C(2, update_flags ? &carry : NULL);
	if (!a || !b) {
		rz_il_op_pure_free(a);
		rz_il_op_pure_free(b);
		rz_il_op_pure_free(carry);
		return NULL;
	}
	RzILOpBitVector *res;
	switch (insn->id) {
	case ARM_INS_AND:
		res = LOGAND(a, b);
		break;
	case ARM_INS_ORR:
		res = LOGOR(a, b);
		break;
	case ARM_INS_ORN:
		res = LOGOR(a, LOGNOT(b));
		break;
	case ARM_INS_EOR:
		res = LOGXOR(a, b);
		break;
	default:
		rz_il_op_pure_free(a);
		rz_il_op_pure_free(b);
		rz_il_op_pure_free(carry);
		return NULL;
	}
	if (REGID(0) == ARM_REG_PC) {
		if (insn->detail->arm.update_flags) {
			// TODO: ALUExceptionReturn()
			rz_il_op_pure_free(res);
			rz_il_op_pure_free(carry);
			return NULL;
		} else {
			return JMP(res);
		}
	}
	RzILOpEffect *eff = write_reg(REGID(0), res);
	if (update_flags) {
		if (carry) {
			return SEQ3(
				eff,
				SETG("cf", carry),
				update_flags_zn(REG(0)));
		} else {
			return SEQ2(eff, update_flags_zn(REG(0)));
		}
	}
	return eff;
}

/**
 * Capstone: ARM_INS_UXTB, ARM_INS_UXTH, ARM_INS_UXTAB, ARM_INS_UXTAH
 * ARM: uxtb, uxth, uxtab, uxtah
 */
static RzILOpEffect *uxt(cs_insn *insn, bool is_thumb) {
	if (!ISREG(0)) {
		return NULL;
	}
	bool is_add = insn->id == ARM_INS_UXTAB || insn->id == ARM_INS_UXTAH || insn->id == ARM_INS_UXTAB16;
	RzILOpBitVector *src = ARG(is_add ? 2 : 1);
	if (!src) {
		return NULL;
	}
	ut32 src_bits = (insn->id == ARM_INS_UXTH || insn->id == ARM_INS_UXTAH) ? 16 : 8;
	RzILOpBitVector *val = UNSIGNED(32, UNSIGNED(src_bits, src));
	if (is_add) {
		RzILOpBitVector *b = ARG(1);
		if (!b) {
			rz_il_op_pure_free(val);
			return NULL;
		}
		val = ADD(b, val);
	}
	return write_reg(REGID(0), val);
}

/**
 * Capstone: ARM_INS_UXTB16, ARM_INS_UXTAB16
 * ARM: uxtb16, uxtab16
 */
static RzILOpEffect *uxt16(cs_insn *insn, bool is_thumb) {
	if (!ISREG(0)) {
		return NULL;
	}
	bool is_add = insn->id == ARM_INS_UXTAB16;
	RzILOpBitVector *src = ARG(is_add ? 2 : 1);
	if (!src) {
		return NULL;
	}
	RzILOpBitVector *l = UNSIGNED(16, UNSIGNED(8, VARLP("x")));
	RzILOpBitVector *h = UNSIGNED(16, UNSIGNED(8, SHIFTR0(VARLP("x"), UN(5, 16))));
	if (is_add) {
		RzILOpBitVector *b = ARG(1);
		if (!b) {
			rz_il_op_pure_free(src);
			rz_il_op_pure_free(l);
			rz_il_op_pure_free(h);
			return NULL;
		}
		l = ADD(UNSIGNED(16, b), l);
		h = ADD(UNSIGNED(16, SHIFTR0(DUP(b), UN(5, 16))), h);
	}
	return write_reg(REGID(0), LET("x", src, APPEND(h, l)));
}

/**
 * Capstone: ARM_INS_CMP, ARM_INS_CMN
 * ARM: cmp, cmn
 */
static RzILOpEffect *cmp(cs_insn *insn, bool is_thumb) {
	if (!ISREG(0)) {
		return NULL;
	}
	bool is_sub = insn->id == ARM_INS_CMP;
	RzILOpBitVector *a = ARG(0);
	RzILOpBitVector *b = ARG(1);
	if (!a || !b) {
		rz_il_op_pure_free(a);
		rz_il_op_pure_free(b);
		return NULL;
	}
	return SEQ6(
		SETL("a", a),
		SETL("b", b),
		SETL("res", is_sub ? SUB(VARL("a"), VARL("b")) : ADD(VARL("a"), VARL("b"))),
		SETG("cf", is_sub ? sub_carry(VARL("a"), VARL("b")) : add_carry(VARL("a"), VARL("b"), false)),
		SETG("vf", (is_sub ? sub_overflow : add_overflow)(VARL("a"), VARL("b"), VARL("res"))),
		update_flags_zn(VARL("res")));
}

/**
 * Capstone: ARM_INS_STMDB, ARM_INS_PUSH
 * ARM: stmdb (stmfb), push
 */
static RzILOpEffect *stmdb(cs_insn *insn, bool is_thumb) {
	size_t op_first;
	arm_reg ptr_reg;
	bool writeback;
	if (insn->id == ARM_INS_PUSH) {
		op_first = 0;
		ptr_reg = ARM_REG_SP;
		writeback = true;
	} else { // ARM_INS_STMDB
		if (!ISREG(0)) {
			return NULL;
		}
		op_first = 1;
		ptr_reg = REGID(0);
		writeback = insn->detail->arm.writeback;
	}
	size_t op_count = OPCOUNT() - op_first;
	if (!op_count) {
		return NOP;
	}
	RzILOpBitVector *ptr = REG_VAL(ptr_reg);
	if (!ptr) {
		return NULL;
	}
	RzILOpEffect *eff = NULL;
	// build up in reverse order so the result recurses in the second arg of seq (for tail-call optimization)
	if (writeback) {
		eff = write_reg(ptr_reg, SUB(DUP(ptr), U32(op_count * 4)));
	}
	for (size_t i = 0; i < op_count; i++) {
		size_t idx = op_first + (op_count - 1 - i);
		RzILOpPure *val;
		if (!ISREG(idx) || !(val = REG(idx))) {
			rz_il_op_pure_free(ptr);
			rz_il_op_effect_free(eff);
			return NULL;
		}
		RzILOpEffect *store = STOREW(SUB(DUP(ptr), U32((i + 1) * 4)), val);
		eff = eff ? SEQ2(store, eff) : store;
	}
	rz_il_op_pure_free(ptr);
	return eff;
}

/**
 * Capstone: ARM_INS_LDM, ARM_INS_POP
 * ARM: ldm (ldmia, ldmfd), pop
 */
static RzILOpEffect *ldm(cs_insn *insn, bool is_thumb) {
	size_t op_first;
	arm_reg ptr_reg;
	bool writeback;
	if (insn->id == ARM_INS_POP) {
		op_first = 0;
		ptr_reg = ARM_REG_SP;
		writeback = true;
	} else { // ARM_INS_LDM
		if (!ISREG(0)) {
			return NULL;
		}
		op_first = 1;
		ptr_reg = REGID(0);
		writeback = insn->detail->arm.writeback;
	}
	size_t op_count = OPCOUNT() - op_first;
	if (!op_count) {
		return NOP;
	}
	RzILOpBitVector *ptr = REG_VAL(ptr_reg);
	if (!ptr) {
		return NULL;
	}
	RzILOpEffect *eff = NULL;
	// build up in reverse order so the result recurses in the second arg of seq (for tail-call optimization)
	for (size_t i = 0; i < op_count; i++) {
		size_t idx = op_first + (op_count - 1 - i);
		if (ISREG(idx) && REGID(idx) == ARM_REG_PC) {
			// jmp goes last
			eff = JMP(VARL("tgt"));
		}
	}
	if (writeback) {
		RzILOpEffect *wb = write_reg(ptr_reg, ADD(DUP(ptr), U32(op_count * 4)));
		eff = eff ? SEQ2(wb, eff) : wb;
	}
	for (size_t i = 0; i < op_count; i++) {
		size_t idx = op_first + (op_count - 1 - i);
		if (!ISREG(idx)) {
			rz_il_op_pure_free(ptr);
			rz_il_op_effect_free(eff);
			return NULL;
		}
		RzILOpPure *val = LOADW(32, ADD(DUP(ptr), U32((op_count - i - 1) * 4)));
		RzILOpEffect *load;
		if (REGID(idx) == ARM_REG_PC) {
			load = SETL("tgt", val);
		} else {
			load = write_reg(REGID(idx), val);
		}
		eff = eff ? SEQ2(load, eff) : load;
	}
	rz_il_op_pure_free(ptr);
	return eff;
}

/**
 * Capstone: ARM_INS_BL, ARM_INS_BLX
 * ARM: bl, blx
 */
static RzILOpEffect *bl(cs_insn *insn, bool is_thumb) {
	RzILOpBitVector *tgt = ARG(0);
	if (!tgt) {
		return NULL;
	}
	return SEQ2(
		SETG("lr", U32(((insn->address + insn->size) & ~1) | (is_thumb ? 1 : 0))),
		JMP(tgt));
}

static RzILOpEffect *il_unconditional(csh *handle, cs_insn *insn, bool is_thumb) {
	switch (insn->id) {
	case ARM_INS_B:
	case ARM_INS_BX: {
		RzILOpBitVector *dst = ARG(0);
		return dst ? JMP(dst) : NULL;
	}
	case ARM_INS_BL:
	case ARM_INS_BLX:
		return bl(insn, is_thumb);
	case ARM_INS_MOV:
	case ARM_INS_MOVW:
		return mov(insn, is_thumb);
	case ARM_INS_MOVT:
		return movt(insn, is_thumb);
	case ARM_INS_ADD:
	case ARM_INS_ADC:
	case ARM_INS_SUB:
		return add_sub(insn, is_thumb);
	case ARM_INS_MUL:
		return mul(insn, is_thumb);
	case ARM_INS_LDR:
	case ARM_INS_LDRB:
	case ARM_INS_LDRH:
	case ARM_INS_LDRT:
	case ARM_INS_LDRBT:
	case ARM_INS_LDRHT:
		return ldr(insn, is_thumb);
	case ARM_INS_STR:
	case ARM_INS_STRB:
	case ARM_INS_STRH:
	case ARM_INS_STRT:
	case ARM_INS_STRBT:
	case ARM_INS_STRHT:
		return str(insn, is_thumb);
	case ARM_INS_AND:
	case ARM_INS_ORR:
	case ARM_INS_ORN:
	case ARM_INS_EOR:
		return bitwise(insn, is_thumb);
	case ARM_INS_UXTB:
	case ARM_INS_UXTAB:
	case ARM_INS_UXTH:
	case ARM_INS_UXTAH:
		return uxt(insn, is_thumb);
	case ARM_INS_UXTB16:
	case ARM_INS_UXTAB16:
		return uxt16(insn, is_thumb);
	case ARM_INS_CMP:
	case ARM_INS_CMN:
		return cmp(insn, is_thumb);
	case ARM_INS_PUSH:
	case ARM_INS_STMDB:
		return stmdb(insn, is_thumb);
	case ARM_INS_POP:
	case ARM_INS_LDM:
		return ldm(insn, is_thumb);
	default:
		return NULL;
	}
}

RZ_IPI RzILOpEffect *rz_arm_cs_32_il(csh *handle, cs_insn *insn, bool thumb) {
	RzILOpEffect *eff = il_unconditional(handle, insn, thumb);
	if (!eff) {
		return NULL;
	}
	RzILOpBool *c = cond(insn->detail->arm.cc);
	if (c) {
		return BRANCH(c, eff, NOP);
	}
	return eff;
}

#include <rz_il/rz_il_opbuilder_end.h>

RZ_IPI RzAnalysisILConfig *rz_arm_cs_32_il_config(bool big_endian) {
	RzAnalysisILConfig *r = rz_analysis_il_config_new(32, big_endian, 32);
	r->reg_bindings = regs_bound_32;
	return r;
}
