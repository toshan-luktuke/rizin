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
#define REG(n)             read_reg(PC(insn->address, is_thumb), REGID(n))
#define MEMBASE(x)         read_reg(PC(insn->address, is_thumb), insn->detail->arm.operands[x].mem.base)
#define MEMINDEX(x)        read_reg(PC(insn->address, is_thumb), insn->detail->arm.operands[x].mem.index)

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
		return AND(INV(VARG("cf")), VARG("zf"));
	case ARM_CC_GE:
		return INV(XOR(VARG("nf"), VARG("vf")));
	case ARM_CC_LT:
		return XOR(VARG("nf"), VARG("vf"));
	case ARM_CC_GT:
		return AND(INV(VARG("zf")), INV(XOR(VARG("nf"), VARG("vf"))));
	case ARM_CC_LE:
		return AND(VARG("zf"), XOR(VARG("nf"), VARG("vf")));
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
	RzILOpBitVector *r;
	if (carry_out) {
		*carry_out = NULL;
	}
	cs_arm_op *op = &insn->detail->arm.operands[n];
	switch (op->type) {
	case ARM_OP_REG:
		r = REG(n);
#if 0
		if (ISSHIFTED(n)) {
			sprintf(buf, "%u,%s,%s",
				LSHIFT2(n),
				rz_str_get_null(cs_reg_name(*handle,
					insn->detail->arm.operands[n].reg)),
				DECODE_SHIFT(n));
		} else {
#endif
		return r;
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

#define ARG(n) arg(insn, is_thumb, n, NULL)

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
 * Capstone: ARM_INS_MOV, ARM_INS_MOVW
 * ARM: mov, movs, movw
 */
static RzILOpEffect *mov(cs_insn *insn, bool is_thumb) {
	if (!ISREG(0) || (!ISIMM(1) && !ISREG(1))) {
		return NULL;
	}
	bool update_flags = insn->detail->arm.update_flags;
	RzILOpBool *carry;
	RzILOpPure *val = arg(insn, is_thumb, 1, update_flags ? &carry : NULL);
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
		if (is_sub) {
			return SEQ6(
				SETL("a", DUP(a)),
				SETL("b", DUP(b)),
				set,
				SETG("cf", ULT(VARL("a"), VARL("b"))),
				SETG("vf", AND(XOR(MSB(VARL("a")), MSB(VARL("b"))), XOR(MSB(VARL("a")), MSB(REG(0))))),
				update_flags_zn(REG(0)));
		} else {
			RzILOpBitVector *extended_res = ADD(UNSIGNED(33, VARL("a")), UNSIGNED(33, VARL("b")));
			if (with_carry) {
				extended_res = ADD(extended_res, ITE(VARG("cf"), UN(33, 1), UN(33, 0)));
			}
			return SEQ6(
				SETL("a", DUP(a)),
				SETL("b", DUP(b)),
				set,
				SETG("cf", MSB(extended_res)),
				SETG("vf", AND(INV(XOR(MSB(VARL("a")), MSB(VARL("b")))), XOR(MSB(VARL("a")), MSB(REG(0))))),
				update_flags_zn(REG(0)));
		}
	}
	return set;
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

static RzILOpEffect *il_unconditional(csh *handle, cs_insn *insn, bool is_thumb) {
	switch (insn->id) {
	case ARM_INS_B: {
		RzILOpBitVector *dst = ARG(0);
		return dst ? JMP(dst) : NULL;
	}
	case ARM_INS_MOV:
	case ARM_INS_MOVW:
		return mov(insn, is_thumb);
	case ARM_INS_MOVT:
		return movt(insn, is_thumb);
	case ARM_INS_ADD:
	case ARM_INS_ADC:
	case ARM_INS_SUB:
		return add_sub(insn, is_thumb);
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
