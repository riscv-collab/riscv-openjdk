/*
 * Copyright (c) 2018, 2020, Oracle and/or its affiliates. All rights reserved.
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
 *
 */

#include "precompiled.hpp"
#include "code/codeCache.hpp"
#include "code/nativeInst.hpp"
#include "gc/shared/barrierSetNMethod.hpp"
#include "logging/log.hpp"
#include "memory/resourceArea.hpp"
#include "runtime/sharedRuntime.hpp"
#include "runtime/registerMap.hpp"
#include "runtime/thread.hpp"
#include "utilities/align.hpp"
#include "utilities/debug.hpp"

class NativeNMethodBarrier: public NativeInstruction {
public:
  enum {
    total_normal_guard_offset     = 12 * instruction_size,
    total_compressed_guard_offset = 10 * instruction_size + 2 * compressed_instruction_size,

    total_normal_size             = total_normal_guard_offset + 4,
    total_compressed_size         = total_compressed_guard_offset + 4,
  };

private:
  address instruction_address() const { return addr_at(0); }

  int *guard_addr() {
    /* auipc + lwu + fence + lwu + beq + lui + addi + (C)slli + addi + (C)slli + jalr + j */
    return reinterpret_cast<int*>(instruction_address() + guard_offset());
  }

public:
  int get_value() {
    return Atomic::load_acquire(guard_addr());
  }

  void set_value(int value) {
    Atomic::release_store(guard_addr(), value);
  }

  void verify() const;

  static int guard_offset() {
    return UseCExt ? total_compressed_guard_offset : total_normal_guard_offset;
  }
};

int nmethod_barrier_guard_offset() {
  return NativeNMethodBarrier::guard_offset();
}

// Store the instruction bitmask, bits and name for checking the barrier.
struct CheckInsn {
  uint32_t mask;
  uint32_t bits;
  const char *name;
  int instruction_size;
};

static const struct CheckInsn barrierInsn[] = {
  { 0x00000fff, 0x00000297, "auipc  t0, 0           ", NativeInstruction::instruction_size},
  { 0x000fffff, 0x0002e283, "lwu    t0, 48(t0)      ", NativeInstruction::instruction_size},
  { 0xffffffff, 0x0aa0000f, "fence  ir, ir          ", NativeInstruction::instruction_size},
  { 0x000fffff, 0x000be303, "lwu    t1, 36(xthread) ", NativeInstruction::instruction_size},
  { 0x01fff07f, 0x00628063, "beq    t0, t1, skip    ", NativeInstruction::instruction_size},
  { 0x00000fff, 0x000002b7, "lui    t0, imm0        ", NativeInstruction::instruction_size},
  { 0x000fffff, 0x00028293, "addi   t0, t0, imm1    ", NativeInstruction::instruction_size},
  { 0xffffffff, 0x00b29293, "slli   t0, t0, 11      ", NativeInstruction::instruction_size},
  { 0x000fffff, 0x00028293, "addi   t0, t0, imm2    ", NativeInstruction::instruction_size},
  { 0xffffffff, 0x00529293, "slli   t0, t0, 5       ", NativeInstruction::instruction_size},
  { 0x000fffff, 0x000280e7, "jalr   lr, imm3(t0)    ", NativeInstruction::instruction_size},
  { 0x00000fff, 0x0000006f, "j      skip            ", NativeInstruction::instruction_size}
  /* guard: */
  /* 32bit nmethod guard value */
  /* skip: */
};

static const struct CheckInsn barrierCInsn[] = {
  { 0x00000fff, 0x00000297, "auipc  t0, 0           ", NativeInstruction::instruction_size},
  { 0x000fffff, 0x0002e283, "lwu    t0, 44(t0)      ", NativeInstruction::instruction_size},
  { 0xffffffff, 0x0aa0000f, "fence  ir, ir          ", NativeInstruction::instruction_size},
  { 0x000fffff, 0x000be303, "lwu    t1, 36(xthread) ", NativeInstruction::instruction_size},
  { 0x01fff07f, 0x00628063, "beq    t0, t1, skip    ", NativeInstruction::instruction_size},
  { 0x00000fff, 0x000002b7, "lui    t0, imm0        ", NativeInstruction::instruction_size},
  { 0x000fffff, 0x00028293, "addi   t0, t0, imm1    ", NativeInstruction::instruction_size},
  { 0x00000fff, 0x02ae,     "c.slli t0, t0, 11      ", NativeInstruction::compressed_instruction_size},
  { 0x000fffff, 0x00028293, "addi   t0, t0, imm2    ", NativeInstruction::instruction_size},
  { 0x0000ffff, 0x0296,     "c.slli t0, t0, 5       ", NativeInstruction::compressed_instruction_size},
  { 0x000fffff, 0x000280e7, "jalr   lr, imm3(t0)    ", NativeInstruction::instruction_size},
  { 0x00000fff, 0x0000006f, "j      skip            ", NativeInstruction::instruction_size}
  /* guard: */
  /* 32bit nmethod guard value */
  /* skip: */
};

// The encodings must match the instructions emitted by
// BarrierSetAssembler::nmethod_entry_barrier. The matching ignores the specific
// register numbers and immediate values in the encoding.
void NativeNMethodBarrier::verify() const {
  intptr_t addr = (intptr_t) instruction_address();
  const struct CheckInsn *insns;
  size_t size;
  if (!UseCExt) {
    insns = barrierInsn;
    size = sizeof(barrierInsn) / sizeof(struct CheckInsn);
  } else {
    insns = barrierCInsn;
    size = sizeof(barrierCInsn) / sizeof(struct CheckInsn);
  }
  for(unsigned int i = 0; i < size; i++ ) {
    uint32_t inst = insns[i].instruction_size == NativeInstruction::compressed_instruction_size ? *((uint16_t*) addr) : *((uint32_t*) addr);
    if ((inst & insns[i].mask) != insns[i].bits) {
      tty->print_cr("Addr: " INTPTR_FORMAT " Code: 0x%x", addr, inst);
      fatal("not an %s instruction.", insns[i].name);
    }
    addr += insns[i].instruction_size;
  }
}


/* We're called from an nmethod when we need to deoptimize it. We do
   this by throwing away the nmethod's frame and jumping to the
   ic_miss stub. This looks like there has been an IC miss at the
   entry of the nmethod, so we resolve the call, which will fall back
   to the interpreter if the nmethod has been unloaded. */
void BarrierSetNMethod::deoptimize(nmethod* nm, address* return_address_ptr) {

  typedef struct {
    intptr_t *sp; intptr_t *fp; address lr; address pc;
  } frame_pointers_t;

  frame_pointers_t *new_frame = (frame_pointers_t *)(return_address_ptr - 5);

  JavaThread *thread = JavaThread::current();
  RegisterMap reg_map(thread, false);
  frame frame = thread->last_frame();

  assert(frame.is_compiled_frame() || frame.is_native_frame(), "must be");
  assert(frame.cb() == nm, "must be");
  frame = frame.sender(&reg_map);

  LogTarget(Trace, nmethod, barrier) out;
  if (out.is_enabled()) {
    ResourceMark mark;
    log_trace(nmethod, barrier)("deoptimize(nmethod: %s(%p), return_addr: %p, osr: %d, thread: %p(%s), making rsp: %p) -> %p",
                                nm->method()->name_and_sig_as_C_string(),
                                nm, *(address *) return_address_ptr, nm->is_osr_method(), thread,
                                thread->get_thread_name(), frame.sp(), nm->verified_entry_point());
  }

  new_frame->sp = frame.sp();
  new_frame->fp = frame.fp();
  new_frame->lr = frame.pc();
  new_frame->pc = SharedRuntime::get_handle_wrong_method_stub();
}

// This is the offset of the entry barrier from where the frame is completed.
// If any code changes between the end of the verified entry where the entry
// barrier resides, and the completion of the frame, then
// NativeNMethodCmpBarrier::verify() will immediately complain when it does
// not find the expected native instruction at this offset, which needs updating.
// Note that this offset is invariant of PreserveFramePointer.

// see BarrierSetAssembler::nmethod_entry_barrier
// auipc + lwu + fence + lwu + beq + movptr_with_offset(5 instructions) + jalr + j + int32
static const int entry_barrier_normal_offset = -NativeNMethodBarrier::total_normal_size;
static const int entry_barrier_compressed_offset = -NativeNMethodBarrier::total_compressed_size;

static const int entry_barrier_offset() {
  return !UseCExt ? entry_barrier_normal_offset : entry_barrier_compressed_offset;
}

static NativeNMethodBarrier* native_nmethod_barrier(nmethod* nm) {
  address barrier_address = nm->code_begin() + nm->frame_complete_offset() + entry_barrier_offset();
  NativeNMethodBarrier* barrier = reinterpret_cast<NativeNMethodBarrier*>(barrier_address);
  debug_only(barrier->verify());
  return barrier;
}

void BarrierSetNMethod::disarm(nmethod* nm) {
  if (!supports_entry_barrier(nm)) {
    return;
  }

  // Disarms the nmethod guard emitted by BarrierSetAssembler::nmethod_entry_barrier.
  NativeNMethodBarrier* barrier = native_nmethod_barrier(nm);

  barrier->set_value(disarmed_value());
}

bool BarrierSetNMethod::is_armed(nmethod* nm) {
  if (!supports_entry_barrier(nm)) {
    return false;
  }

  NativeNMethodBarrier* barrier = native_nmethod_barrier(nm);
  return barrier->get_value() != disarmed_value();
}
