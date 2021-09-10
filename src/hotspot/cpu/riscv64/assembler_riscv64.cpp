/*
 * Copyright (c) 1997, 2012, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2014, Red Hat Inc. All rights reserved.
 * Copyright (c) 2020, 2021, Huawei Technologies Co., Ltd. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

#include <stdio.h>
#include <sys/types.h>

#include "precompiled.hpp"
#include "asm/assembler.hpp"
#include "asm/assembler.inline.hpp"
#include "compiler/disassembler.hpp"
#include "interpreter/interpreter.hpp"
#include "memory/resourceArea.hpp"
#include "runtime/interfaceSupport.inline.hpp"
#include "runtime/sharedRuntime.hpp"
#include "nativeInst_riscv64.hpp"

int AbstractAssembler::code_fill_byte() {
  return 0;
}

// C-Ext: Compressed Instructions
#define FUNC(NAME, funct3, bits)                                                   \
  bool Assembler::NAME(Register rs1, Register rd_rs2, int32_t imm12, bool ld) {    \
    return rs1 == sp &&                                                            \
      is_unsigned_imm_in_range(imm12, bits, 0) &&                                  \
      (intx(imm12) & funct3) == 0x0 &&                                             \
      (!ld || rd_rs2 != x0);                                                       \
  }                                                                                \

  FUNC(is_cldsdsp,  0b111, 9);
  FUNC(is_clwswsp,  0b011, 8);

#undef FUNC

#define FUNC(NAME, funct3, bits)                                                   \
  bool Assembler::NAME(Register rs1, Register rd_rs2, int32_t imm12) {             \
    return rs1->is_compressed_valid() &&                                           \
      rd_rs2->is_compressed_valid() &&                                             \
      is_unsigned_imm_in_range(imm12, bits, 0) &&                                  \
      (intx(imm12) & funct3) == 0x0;                                               \
  }                                                                                \

  FUNC(is_cldsd,  0b111, 8);
  FUNC(is_clwsw,  0b011, 7);

#undef FUNC

bool Assembler::emit_compressed_ld_st(unsigned int insn, bool ld) {
  uint32_t funct3 = Assembler::extract(insn, 14, 12);
  uint32_t rs1_bits = Assembler::extract(insn, 19, 15);
  uint32_t rd_rs2_bits = 0;
  int32_t imm12 = 0;
  if (ld) {
    rd_rs2_bits = Assembler::extract(insn, 11, 7);
    imm12 = Assembler::sextract(insn, 31, 20);
  } else {
    rd_rs2_bits = Assembler::extract(insn, 24, 20);
    imm12 = Assembler::sextract(insn, 31, 25);
    imm12 = (imm12 << 5) | Assembler::extract(insn, 11, 7);
  }
  guarantee(is_imm_in_range(imm12, 12, 0), "must be");
  Register rs1 = as_Register(rs1_bits);
  Register rd_rs2 = as_Register(rd_rs2_bits);
  if (funct3 == 0b011) {  // ld/sd
    // ld/sd(Rd, Address(sp, 8n)), which n >= 0
    if (is_cldsdsp(rs1, rd_rs2, imm12, ld)) {
      if (ld) {
        c_ldsp(rd_rs2, imm12);
      } else {
        c_sdsp(rd_rs2, imm12);
      }
      return true;
    } else
    // ld/sd(compressed_Rd, Address(compressed_Rs, 8n)), which n >= 0
    if (is_cldsd(rs1, rd_rs2, imm12)) {
      if (ld) {
        c_ld(rd_rs2, rs1, imm12);
      } else {
        c_sd(rd_rs2, rs1, imm12);
      }
      return true;
    }
  } else if (funct3 == 0b010) {  // lw
    // lw/sw(Rd, Address(sp, 4n)), which n >= 0
    if (is_clwswsp(rs1, rd_rs2, imm12, ld)) {
      if (ld) {
        c_lwsp(rd_rs2, imm12);
      } else {
        c_swsp(rd_rs2, imm12);
      }
      return true;
    } else
    // lw/sw(compressed_Rd, Address(compressed_Rs1, 4n)), which n >= 0
    if (is_clwsw(rs1, rd_rs2, imm12)) {
      if (ld) {
        c_lw(rd_rs2, rs1, imm12);
      } else {
        c_sw(rd_rs2, rs1, imm12);
      }
      return true;
    }
  }
  return false;
}

bool Assembler::emit_compressed_fld_fst(unsigned int insn, bool ld) {
  uint32_t funct3 = Assembler::extract(insn, 14, 12);
  uint32_t rs1 = Assembler::extract(insn, 19, 15);
  uint32_t rd_rs2 = 0;
  int32_t imm12 = 0;
  if (ld) {
    rd_rs2 = Assembler::extract(insn, 11, 7);
    imm12 = Assembler::sextract(insn, 31, 20);
  } else {
    rd_rs2 = Assembler::extract(insn, 24, 20);
    imm12 = Assembler::sextract(insn, 31, 25);
    imm12 = (imm12 << 5) | Assembler::extract(insn, 11, 7);
  }
  guarantee(is_imm_in_range(imm12, 12, 0), "must be");
  if (funct3 == 0b011) {  // fld/fsd
    // fld/fsd(Rd, Address(sp, 8n)), which n >= 0
    if (as_Register(rs1) == sp &&
        is_unsigned_imm_in_range(imm12, 9, 0) &&
        (intx(imm12) & 0b111) == 0x0
        ) {
      if (ld) {
        c_fldsp(as_FloatRegister(rd_rs2), imm12);
      } else {
        c_fsdsp(as_FloatRegister(rd_rs2), imm12);
      }
      return true;
    } else
    // ld/sd(compressed_Rd, Address(compressed_Rs, 8n)), which n >= 0
    if (as_Register(rs1)->is_compressed_valid() &&
        as_FloatRegister(rd_rs2)->is_compressed_valid() &&
        is_unsigned_imm_in_range(imm12, 8, 0) &&
        (intx(imm12) & 0b111) == 0x0
        ) {
      if (ld) {
        c_fld(as_FloatRegister(rd_rs2), as_Register(rs1), imm12);
      } else {
        c_fsd(as_FloatRegister(rd_rs2), as_Register(rs1), imm12);
      }
      return true;
    }
  }
  return false;
}

// C-Ext: here is our implicit phase to emit compressed instruction.
//   We will hook instructions emitted from Assembler::emit_may_compress()
//   and see if it can do some compression - if able to, then
//   we will emit a 16-bit compressed instruction instead of the 32-bit
//   instruction. All below logic follows Chapter -
//   "C" Standard Extension for Compressed Instructions, Version 2.0.
//   We can get performance improvement and code size reduction with this,
//   considering the code density increment and reduction of instruction size.
bool Assembler::emit_compressed_instruction(unsigned insn) {
  if (!UseCExt) {
    return false;
  }

  uint32_t opcode = Assembler::extract(insn, 6, 0);
  if (opcode == 0b0010011) {
    uint32_t funct3 = Assembler::extract(insn, 14, 12);
    uint32_t rs1 = Assembler::extract(insn, 19, 15);
    uint32_t rd = Assembler::extract(insn, 11, 7);
    if (funct3 == 0b000) {  // addi
      if (as_Register(rs1) == sp) {
        int32_t imm12 = Assembler::sextract(insn, 31, 20);
        if (imm12 != 0 && is_imm_in_range(imm12, 10, 0) &&
            rd == rs1 && (imm12 & 0b1111) == 0x0) {
          c_addi16sp(imm12);
          return true;
        }
        uint32_t uimm12 = Assembler::extract(insn, 31, 20);
        if (uimm12 != 0 && is_unsigned_imm_in_range(uimm12, 10, 0)
            && rd != rs1 && as_Register(rd)->is_compressed_valid() && (uimm12 & 0b11) == 0x0) {
          c_addi4spn(as_Register(rd), uimm12);
          return true;
        }
      }
      int32_t imm12 = Assembler::sextract(insn, 31, 20);
      guarantee(is_imm_in_range(imm12, 12, 0), "must be");
      if (imm12 == 0 && as_Register(rd) != x0 && as_Register(rs1) != x0) {
        c_mv(as_Register(rd), as_Register(rs1));
        return true;
      } else if (rd == rs1 && is_imm_in_range(imm12, 6, 0)) { // [-32, 31]
        if (as_Register(rd) != x0) {
          c_addi(as_Register(rd), imm12);
        } else if (imm12 == 0) {
          c_nop();
        }
        return true;
      }
    } else if (funct3 == 0b111) {  // andi
      int32_t imm12 = Assembler::sextract(insn, 31, 20);
      guarantee(is_imm_in_range(imm12, 12, 0), "must be");
      if (rd == rs1 && is_imm_in_range(imm12, 6, 0) &&
          as_Register(rd)->is_compressed_valid()
              ) { // [-32, 31]
        c_andi(as_Register(rd), imm12);
        return true;
      }
    } else if (funct3 == 0b001) {  // slli
      uint32_t shamt = Assembler::extract(insn, 25, 20);
      guarantee(shamt <= 0x3f, "Shamt is invalid");
      if (rd == rs1 && as_Register(rd) != x0 && shamt != 0) {
        c_slli(as_Register(rd), shamt);
        return true;
      }
    } else if (funct3 == 0b101) {  // sr(l/a)i
      if (rd == rs1 && as_Register(rd)->is_compressed_valid()) {
        uint32_t shamt = Assembler::extract(insn, 25, 20);
        guarantee(shamt <= 0x3f, "Shamt is invalid");
        if (shamt != 0) {
          uint32_t funct6 = Assembler::extract(insn, 31, 26);
          if (funct6 == 0b000000) {  // srli
            c_srli(as_Register(rd), shamt);
            return true;
          } else if (funct6 == 0b010000) {  // srai
            c_srai(as_Register(rd), shamt);
            return true;
          } else {
            ShouldNotReachHere();
          }
        }
      }
    }
  } else if (opcode == 0b0110011 || opcode == 0b0111011) {  // sub/add/subw/addw
    uint32_t rs2 = Assembler::extract(insn, 24, 20);
    uint32_t rs1 = Assembler::extract(insn, 19, 15);
    uint32_t rd = Assembler::extract(insn, 11, 7);
    uint32_t funct3 = Assembler::extract(insn, 14, 12);
    uint32_t funct7 = Assembler::extract(insn, 31, 25);
    if (funct3 == 0b000 && funct7 == 0b0000000) {  // add/addw
      Register src = noreg;
      if (opcode == 0b0110011) {  // add
        if (as_Register(rs1) != x0 &&
            as_Register(rs2) != x0 &&
            ((src = as_Register(rs1), rs2 == rd) || (src = as_Register(rs2), rs1 == rd))
                ) {
          c_add(as_Register(rd), src);
          return true;
        }
      } else if (opcode == 0b0111011) {  // addw
        if (as_Register(rs1)->is_compressed_valid() &&
            as_Register(rs2)->is_compressed_valid() &&
            ((src = as_Register(rs1), rs2 == rd) || (src = as_Register(rs2), rs1 == rd))
                ) {
          c_addw(as_Register(rd), src);
          return true;
        }
      } else {
        ShouldNotReachHere();
      }
    } else if (funct3 == 0b000 && funct7 == 0b0100000) {  // sub/subw
      if (rs1 == rd &&
          as_Register(rd)->is_compressed_valid() &&
          as_Register(rs2)->is_compressed_valid()
              ) {
        if (opcode == 0b0110011) {  // sub
          c_sub(as_Register(rd), as_Register(rs2));
        } else if (opcode == 0b0111011) {  // subw
          c_subw(as_Register(rd), as_Register(rs2));
        } else {
          ShouldNotReachHere();
        }
        return true;
      }
    } else if (funct7 == 0b0000000 &&
               (funct3 == 0b100 || funct3 == 0b110 || funct3 == 0b111)  // xor/or/and
            ) {
      Register src = noreg;
      if (as_Register(rs1)->is_compressed_valid() &&
          as_Register(rs2)->is_compressed_valid() &&
          ((src = as_Register(rs1), rs2 == rd) || (src = as_Register(rs2), rs1 == rd))
              ) {
        if (funct3 == 0b100) {  // xor
          c_xor(as_Register(rd), src);
        } else if (funct3 == 0b110) {  // or
          c_or(as_Register(rd), src);
        } else if (funct3 == 0b111) {  // and
          c_and(as_Register(rd), src);
        } else {
          ShouldNotReachHere();
        }
        return true;
      }
    }
  } else if (opcode == 0b0011011) {
    uint32_t funct3 = Assembler::extract(insn, 14, 12);
    uint32_t rs1 = Assembler::extract(insn, 19, 15);
    uint32_t rd = Assembler::extract(insn, 11, 7);
    if (funct3 == 0b000) {  // addiw
      int32_t imm12 = Assembler::sextract(insn, 31, 20);
      guarantee(is_imm_in_range(imm12, 12, 0), "must be");
      if (rd == rs1 && as_Register(rd) != x0 && is_imm_in_range(imm12, 6, 0)) { // [-32, 31]
        c_addiw(as_Register(rd), imm12);
        return true;
      }
    }
  } else if (opcode == 0b0000011) {  // ld family
    if (emit_compressed_ld_st(insn, true)) {
      return true;
    }
  } else if (opcode == 0b0100011) {  // sd family
    if (emit_compressed_ld_st(insn, false)) {
      return true;
    }
  } else if (opcode == 0b0000111) {  // fld family
    if (emit_compressed_fld_fst(insn, true)) {
      return true;
    }
  } else if (opcode == 0b0100111) {  // fsd family
    if (emit_compressed_fld_fst(insn, false)) {
      return true;
    }
  } else if (opcode == 0b0110111) {  // lui
    // lui's imm20 has already left shifted by 12.
    int32_t imm20 = Assembler::sextract(insn, 31, 12) << 12;
    uint32_t rd = Assembler::extract(insn, 11, 7);
    Register rd_reg = as_Register(rd);
    if (is_imm_in_range(imm20, 18, 0) && rd_reg != x0 && rd_reg != x2 && imm20 != 0) {
      c_lui(rd_reg, imm20);
      return true;
    }
  } else if (opcode == 0b1110011) {
    if (Assembler::extract(insn, 14, 12) == 0x0 &&
        Assembler::extract(insn, 31, 20) == 0x1) {  // ebreak
      c_ebreak();
      return true;
    }
  } else if (opcode == 0b1100111) {  // jalr/jr
    uint32_t rs1 = Assembler::extract(insn, 19, 15);
    uint32_t rd = Assembler::extract(insn, 11, 7);
    int32_t imm12 = Assembler::sextract(insn, 31, 20);
    if (imm12 == 0 && as_Register(rs1) != x0) {
      if (as_Register(rd) == x1) {
        c_jalr(as_Register(rs1));
        return true;
      } else if (as_Register(rd) == x0) {
        c_jr(as_Register(rs1));
        return true;
      }
    }
  } else if (opcode == 0b1101111) {  // j
    assert(NativeInstruction::is_jal_at((address)&insn), "sanity");
    uint32_t rd = Assembler::extract(insn, 11, 7);
    long offset = get_offset_of_jal(insn);
    // TODO: Removing the 'offset != 0' check needs us to fix lots of '__ j''s to '__ j_nc' manually everywhere.
    if (offset != 0 && is_imm_in_range(offset, 11, 1) && as_Register(rd) == x0) {
      c_j(offset);
      return true;
    }
  } else if (opcode == 0b1100011) {  // beqz/bnez
    uint32_t funct3 = Assembler::extract(insn, 14, 12);
    if (funct3 == 0b000 || funct3 == 0b001) {  // beqz/bnez
      uint32_t rs2 = Assembler::extract(insn, 24, 20);
      uint32_t rs1 = Assembler::extract(insn, 19, 15);
      long offset = get_offset_of_conditional_branch(insn);
      // TODO: Removing the 'offset != 0' check needs us to fix lots of '__beqz / __benz''s to '__beqz_nc / __bnez_nc' everywhere.
      if (offset != 0 &&
          is_imm_in_range(offset, 8, 1) &&
          as_Register(rs2) == x0 &&
          as_Register(rs1)->is_compressed_valid()
              ) {
        if (funct3 == 0b000) {
          c_beqz(as_Register(rs1), offset);
        } else if (funct3 == 0b001) {
          c_bnez(as_Register(rs1), offset);
        } else {
          ShouldNotReachHere();
        }
        return true;
      }
    }
  }
  return false;
}

void Assembler::emit_may_compress(unsigned insn) {
  if (!emit_compressed_instruction(insn)) {
    emit((jint)insn);
  }
}

void Assembler::add(Register Rd, Register Rn, int64_t increment, Register temp) {
  if (is_imm_in_range(increment, 12, 0)) {
    addi(Rd, Rn, increment);
  } else {
    assert_different_registers(Rn, temp);
    li(temp, increment);
    add(Rd, Rn, temp);
  }
}

void Assembler::addw(Register Rd, Register Rn, int64_t increment, Register temp) {
  if (is_imm_in_range(increment, 12, 0)) {
    addiw(Rd, Rn, increment);
  } else {
    assert_different_registers(Rn, temp);
    li(temp, increment);
    addw(Rd, Rn, temp);
  }
}

void Assembler::sub(Register Rd, Register Rn, int64_t decrement, Register temp) {
  if (is_imm_in_range(-decrement, 12, 0)) {
    addi(Rd, Rn, -decrement);
  } else {
    assert_different_registers(Rn, temp);
    li(temp, decrement);
    sub(Rd, Rn, temp);
  }
}

void Assembler::subw(Register Rd, Register Rn, int64_t decrement, Register temp) {
  if (is_imm_in_range(-decrement, 12, 0)) {
    addiw(Rd, Rn, -decrement);
  } else {
    assert_different_registers(Rn, temp);
    li(temp, decrement);
    subw(Rd, Rn, temp);
  }
}

void Assembler::li(Register Rd, int64_t imm) {
  if (UseCExt && is_imm_in_range(imm, 6, 0) && Rd != x0) {
    c_li(Rd, imm);
    return;
  }

  // int64_t is in range 0x8000 0000 0000 0000 ~ 0x7fff ffff ffff ffff
  int shift = 12;
  int64_t upper = imm, lower = imm;
  // Split imm to a lower 12-bit sign-extended part and the remainder, because addi will sign-extend the lower imm.
  lower = ((int32_t)imm << 20) >> 20;
  upper -= lower;

  // Test whether imm is a 32-bit integer.
  if (!(((imm) & ~(int64_t)0x7fffffff) == 0 ||
        (((imm) & ~(int64_t)0x7fffffff) == ~(int64_t)0x7fffffff))) {
    while (((upper >> shift) & 1) == 0) { shift++; }
    upper >>= shift;
    li(Rd, upper);
    slli(Rd, Rd, shift);
    if (lower != 0) {
      addi(Rd, Rd, lower);
    }
  }
  else {
    // 32-bit integer
    Register hi_Rd = zr;
    if (upper != 0) {
      lui(Rd, (int32_t)upper);
      hi_Rd = Rd;
    }
    if (lower != 0 || hi_Rd == zr) {
      addiw(Rd, hi_Rd, lower);
    }
  }
}

void Assembler::li64(Register Rd, int64_t imm) {
   // Load upper 32 bits. Upper = imm[63:32], but if imm[31] = 1 or (imm[31:28] == 0x7ff && imm[19] == 1),
   // upper = imm[63:32] + 1.
   int64_t lower = imm & 0xffffffff;
   lower -= ((lower << 44) >> 44);
   int64_t tmp_imm = ((uint64_t)(imm & 0xffffffff00000000)) + (uint64_t)lower;
   int32_t upper = (tmp_imm - (int32_t)lower) >> 32;

   // Load upper 32 bits
   int64_t up = upper, lo = upper;
   lo = (lo << 52) >> 52;
   up -= lo;
   up = (int32_t)up;
   lui_nc(Rd, up);
   addi_nc(Rd, Rd, lo);

   // Load the rest 32 bits.
   slli(Rd, Rd, 12);
   addi_nc(Rd, Rd, (int32_t)lower >> 20);
   slli(Rd, Rd, 12);
   lower = ((int32_t)imm << 12) >> 20;
   addi_nc(Rd, Rd, lower);
   slli(Rd, Rd, 8);
   lower = imm & 0xff;
   addi_nc(Rd, Rd, lower);
}

void Assembler::li32(Register Rd, int32_t imm) {
  // int32_t is in range 0x8000 0000 ~ 0x7fff ffff, and imm[31] is the sign bit
  int64_t upper = imm, lower = imm;
  lower = (imm << 20) >> 20;
  upper -= lower;
  upper = (int32_t)upper;
  // lui Rd, imm[31:12] + imm[11]
  lui_nc(Rd, upper);
  // use addiw to distinguish li32 to li64
  addiw_nc(Rd, Rd, lower);
}

#define COMPRESSED    true
#define NORMAL        false

#define INSN(NAME, REGISTER, compressed)                                   \
  void Assembler::NAME(const address &dest, Register temp) {               \
    assert_cond(dest != NULL);                                             \
    int64_t distance = dest - pc();                                        \
    if (is_imm_in_range(distance, 20, 1)) {                                \
      EMIT_MAY_COMPRESS_NAME(compressed, jal, (REGISTER, distance));       \
    } else {                                                               \
      assert(temp != noreg, "temp must not be empty register!");           \
      int32_t offset = 0;                                                  \
      movptr_with_offset(temp, dest, offset, compressed);                  \
      EMIT_MAY_COMPRESS_NAME(compressed, jalr, (REGISTER, temp, offset));  \
    }                                                                      \
  }                                                                        \
  void Assembler::NAME(Label &l, Register temp) {                          \
    EMIT_MAY_COMPRESS_NAME(compressed, jal, (REGISTER, l, temp));          \
  }                                                                        \

  INSN(j,    x0, COMPRESSED);
  INSN(jal,  x1, COMPRESSED);

  // C-Ext: uncompressed version
  INSN(j_nc,   x0, NORMAL);
  INSN(jal_nc, x1, NORMAL);

#undef INSN

#define INSN(NAME, REGISTER, compressed)                           \
  void Assembler::NAME(Register Rs) {                              \
    EMIT_MAY_COMPRESS_NAME(compressed, jalr, (REGISTER, Rs, 0));   \
  }

  INSN(jr,      x0, COMPRESSED);
  INSN(jalr,    x1, COMPRESSED);

  // C-Ext: uncompressed version
  INSN(jr_nc,   x0, NORMAL);
  INSN(jalr_nc, x1, NORMAL);

#undef INSN

void Assembler::ret() {
  jalr(x0, x1, 0);
}

#define INSN(NAME, REGISTER, compressed)                                  \
  void Assembler::NAME(const address &dest, Register temp) {              \
    assert_cond(dest != NULL);                                            \
    assert(temp != noreg, "temp must not be empty register!");            \
    int64_t distance = dest - pc();                                       \
    if (is_offset_in_range(distance, 32)) {                               \
      auipc(temp, distance + 0x800);                                      \
      EMIT_MAY_COMPRESS_NAME(compressed, jalr, (REGISTER, temp, ((int32_t)distance << 20) >> 20));   \
    } else {                                                              \
      int32_t offset = 0;                                                 \
      movptr_with_offset(temp, dest, offset, compressed);                 \
      EMIT_MAY_COMPRESS_NAME(compressed, jalr, (REGISTER, temp, offset)); \
    }                                                                     \
  }

  INSN(call, x1, COMPRESSED);
  INSN(tail, x0, COMPRESSED);

  // C-Ext: uncompressed version
  INSN(call_nc, x1, NORMAL);
  INSN(tail_nc, x0, NORMAL);

#undef INSN

#define INSN(NAME, REGISTER, NAME_NC, compressed)              \
  void Assembler::NAME(const Address &adr, Register temp) {    \
    switch(adr.getMode()) {                                    \
      case Address::literal: {                                 \
        code_section()->relocate(pc(), adr.rspec());           \
        NAME_NC(adr.target(), temp);                           \
        break;                                                 \
      }                                                        \
      case Address::base_plus_offset:{                         \
        int32_t offset = 0;                                    \
        baseOffset(temp, adr, offset);                         \
        jalr(REGISTER, temp, offset);                          \
        break;                                                 \
      }                                                        \
      default:                                                 \
        ShouldNotReachHere();                                  \
    }                                                          \
  }

  INSN(j,    x0, j_nc,    COMPRESSED);
  INSN(jal,  x1, jal_nc,  COMPRESSED);
  INSN(call, x1, call_nc, COMPRESSED);
  INSN(tail, x0, tail_nc, COMPRESSED);

  // C-Ext: uncompressed version
  INSN(j_nc,   x0, j_nc,   NORMAL);
  INSN(jal_nc, x1, jal_nc, NORMAL);

#undef INSN

#undef NORMAL
#undef COMPRESSED

void Assembler::wrap_label(Register r1, Register r2, Label &L, compare_and_branch_insn insn,
                           compare_and_branch_label_insn neg_insn, bool is_far) {
  if (is_far) {
    Label done;
    (this->*neg_insn)(r1, r2, done, /* is_far */ false);
    j_nc(L);
    bind(done);
  } else {
    if (L.is_bound()) {
      (this->*insn)(r1, r2, target(L));
    } else {
      L.add_patch_at(code(), locator());
      (this->*insn)(r1, r2, pc());
    }
  }
}

void Assembler::wrap_label(Register Rt, Label &L, Register tmp, load_insn_by_temp insn) {
  if (L.is_bound()) {
    (this->*insn)(Rt, target(L), tmp);
  } else {
    L.add_patch_at(code(), locator());
    (this->*insn)(Rt, pc(), tmp);
  }
}

void Assembler::wrap_label(Register Rt, Label &L, jal_jalr_insn insn) {
  if (L.is_bound()) {
    (this->*insn)(Rt, target(L));
  } else {
    L.add_patch_at(code(), locator());
    (this->*insn)(Rt, pc());
  }
}

void Assembler::wrap_label(Label &L, c_j_insn insn) {
  if (L.is_bound()) {
    (this->*insn)(target(L));
  } else {
    L.add_patch_at(code(), locator());
    (this->*insn)(pc());
  }
}

void Assembler::wrap_label(Label &L, Register r, c_compare_and_branch_insn insn) {
  if (L.is_bound()) {
    (this->*insn)(r, target(L));
  } else {
    L.add_patch_at(code(), locator());
    (this->*insn)(r, pc());
  }
}

void Assembler::movptr_with_offset(Register Rd, address addr, int32_t &offset, bool compressed) {
  uintptr_t imm64 = (uintptr_t)addr;
#ifndef PRODUCT
  {
    char buffer[64];
    snprintf(buffer, sizeof(buffer), "0x%" PRIx64, imm64);
    block_comment(buffer);
  }
#endif
  assert(is_unsigned_imm_in_range(imm64, 47, 0) || (imm64 == (uintptr_t)-1), "48-bit overflow in address constant");
  // Load upper 32 bits
  int32_t imm = imm64 >> 16;
  int64_t upper = imm, lower = imm;
  lower = (lower << 52) >> 52;
  upper -= lower;
  upper = (int32_t)upper;
  if (compressed) {
    lui(Rd, upper);
    addi(Rd, Rd, lower);
  } else {
    lui_nc(Rd, upper);
    addi_nc(Rd, Rd, lower);
  }

  // Load the rest 16 bits.
  slli(Rd, Rd, 11);
  if (compressed) {
    addi(Rd, Rd, (imm64 >> 5) & 0x7ff);
  } else {
    addi_nc(Rd, Rd, (imm64 >> 5) & 0x7ff);
  }
  slli(Rd, Rd, 5);

  // Here, remove the addi instruct and return the offset directly. This offset will be used by following jalr/ld.
  offset = imm64 & 0x1f;
}

void Assembler::movptr(Register Rd, uintptr_t imm64, bool compressed) {
  movptr(Rd, (address)imm64, compressed);
}

void Assembler::movptr(Register Rd, address addr, bool compressed) {
  int offset = 0;
  movptr_with_offset(Rd, addr, offset, compressed);
  if (compressed) {
    addi(Rd, Rd, offset);
  } else {
    addi_nc(Rd, Rd, offset);
  }
}

void Assembler::ifence() {
  fence_i();
  if (UseConservativeFence) {
    fence(ir, ir);
  }
}

#define INSN(NAME, NEG_INSN)                                                               \
  void Assembler::NAME(Register Rs, Register Rt, const address &dest) {                    \
    NEG_INSN(Rt, Rs, dest);                                                                \
  }                                                                                        \
  void Assembler::NAME(Register Rs, Register Rt, Label &l, bool is_far) {                  \
    NEG_INSN(Rt, Rs, l, is_far);                                                           \
  }

  INSN(bgt,  blt);
  INSN(ble,  bge);
  INSN(bgtu, bltu);
  INSN(bleu, bgeu);
#undef INSN

#undef __

Address::Address(address target, relocInfo::relocType rtype) : _base(noreg), _offset(0), _mode(literal) {
  _target = target;
  switch (rtype) {
    case relocInfo::oop_type:
    case relocInfo::metadata_type:
      // Oops are a special case. Normally they would be their own section
      // but in cases like icBuffer they are literals in the code stream that
      // we don't have a section for. We use none so that we get a literal address
      // which is always patchable.
      break;
    case relocInfo::external_word_type:
      _rspec = external_word_Relocation::spec(target);
      break;
    case relocInfo::internal_word_type:
      _rspec = internal_word_Relocation::spec(target);
      break;
    case relocInfo::opt_virtual_call_type:
      _rspec = opt_virtual_call_Relocation::spec();
      break;
    case relocInfo::static_call_type:
      _rspec = static_call_Relocation::spec();
      break;
    case relocInfo::runtime_call_type:
      _rspec = runtime_call_Relocation::spec();
      break;
    case relocInfo::poll_type:
    case relocInfo::poll_return_type:
      _rspec = Relocation::spec_simple(rtype);
      break;
    case relocInfo::none:
      _rspec = RelocationHolder::none;
      break;
    default:
      ShouldNotReachHere();
  }
}

