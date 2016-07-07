
/*--------------------------------------------------------------------*/
/*--- Opgrind: A  minimal Valgrind tool.                 nl_main.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Opgrind, the minimal Valgrind tool,
   which does no instrumentation or analysis.

   Copyright (C) 2016 Marcel Schneider
     marcel.andre.schneider@cern.ch

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_options.h"
#include "pub_tool_machine.h"     // VG_(fnptr_to_fnentry)


/* Table of opcodes. Generate like this:
 ( for op in $(grep -oE 'Iop_[^, =()]*,' libvex_ir.h | tr -d ','); do 
    printf '[%-20s-Iop_INVALID] = 1' $op 
    [[ $op =~ (32|64)F ]]               && printf ' | BIT(OP_FP)'    # mostly vector things
    [[ $op =~ (8|16|32|64)(U|I|S) ]]    && printf ' | BIT(OP_INT)'   # should be exclusive wrt above
    [[ $op =~ x(2|4|8|16)|V(128|256) ]] && printf ' | BIT(OP_VEC)'   # all SIMD
    [[ $op =~ D(32|64|128) ]]           && printf ' | BIT(OP_DEC)'   # Decimal encoding, should not appear in amd64
    [[ $op =~ F(32|64|128) ]]           && printf ' | BIT(OP_OLDFP)' # Scalar FP (x87), should not appear
    [[ $op =~ (U|I|S)(8|16|32|64) ]]    && printf ' | BIT(OP_INT)'   # Scalar int
    [[ $op =~ [UISFD][0-9]+|[0-9]+[UISFD] ]] || printf ' | BIT(OP_BITS)' # none of the above
    [[ $op =~ Mul ]]                    && printf ' | BIT(OP_MUL)'   # 
    [[ $op =~ Div ]]                    && printf ' | BIT(OP_DIV)'   # 
    [[ $op =~ Add ]]                    && printf ' | BIT(OP_ADD)'   # 
    [[ $op =~ Sub ]]                    && printf ' | BIT(OP_SUB)'   # 
    [[ $op =~ Cmp ]]                    && printf ' | BIT(OP_CMP)'   # 
    [[ $op =~ 32F0x4 ]]                 && printf ' | BIT(OP_SSE_SS)'   # addss and friends
    [[ $op =~ 64F0x2 ]]                 && printf ' | BIT(OP_SSE_SD)'   # addsd and friends
    [[ $op =~ 32Fx4  ]]                 && printf ' | BIT(OP_SSE_PS)'   # addps and friends
    [[ $op =~ 64Fx2  ]]                 && printf ' | BIT(OP_SSE_PD)'   # addpd and friends
    [[ $op =~ 32Fx8  ]]                 && printf ' | BIT(OP_AVX_PS)'   # vaddps and friends
    [[ $op =~ 64Fx4  ]]                 && printf ' | BIT(OP_AVX_PD)'   # vaddpd and friends
    # Mul, Div, Add, Sub, conv ('to'), Sqrt, Cmp could also be easily marked.
    printf ',\n'
 done ) > op_types.inc
 *
 * Index with Iop_INVALID+opcode.
 */
#define BIT(flag) (1 << flag)
enum Op_Types {
  OP_ALL=0, OP_MEM, OP_FP, OP_INT, OP_VEC, OP_DEC, OP_OLDFP, OP_BITS, 
  OP_MUL, OP_DIV, OP_ADD, OP_SUB, OP_CMP,
  OP_SSE_SS, OP_SSE_SD, OP_SSE_PS, OP_SSE_PD, OP_AVX_PS, OP_AVX_PD,
  OP_CALL,
  N_OPS
};
static const UInt op_types[] = {
#include "op_types.inc"
0 /* dummy for syntax */ };

static const UInt code_types[] = {
  [0xe8] = BIT(OP_CALL),
  [0xFF] = BIT(OP_CALL)
};

typedef union {
  struct { ULong longs[4];} packed;
  struct { UChar bytes[N_OPS];} unpacked;
} Buffer_t;

static ULong global_ctrs[N_OPS];
static ULong global_jumps;
static ULong sb_ctr;

static void record_counts(ULong ctrs1, 
                          ULong ctrs2, 
                          ULong ctrs3,
                          ULong ctrs4)
{
#ifdef SLOW_CTRS
  Buffer_t buffer = { .packed = {{ctrs1, ctrs2, ctrs3, ctrs4}} };
  for (int i = 0; i < N_OPS; i++) {
    global_ctrs[i] += buffer.unpacked.bytes[i];
  }
#else
  // Endianness-dependent, fully unrolled code
#define UNPACK_ONE(x, field, to) if (to < N_OPS) global_ctrs[to] += 0xFF & (x >> (8*field))
#define UNPACK(x, to) UNPACK_ONE(x, 0, to + 0); \
                      UNPACK_ONE(x, 1, to + 1); \
                      UNPACK_ONE(x, 2, to + 2); \
                      UNPACK_ONE(x, 3, to + 3); \
                      UNPACK_ONE(x, 4, to + 4); \
                      UNPACK_ONE(x, 5, to + 5); \
                      UNPACK_ONE(x, 6, to + 6); \
                      UNPACK_ONE(x, 7, to + 7); 
  UNPACK(ctrs1, 0);
  UNPACK(ctrs2, 8);
  UNPACK(ctrs3, 16);
  UNPACK(ctrs4, 24);
#endif

  global_jumps++;
}

static void og_post_clo_init(void)
{
}

static void
increment_counters(Buffer_t* insts, Buffer_t* is_flags) {
  for (int i = 0; i < N_OPS; i++) {
    if (is_flags->unpacked.bytes[i])
      insts->unpacked.bytes[i]++;
    tl_assert(insts->unpacked.bytes[i] < 0xFF);
    is_flags->unpacked.bytes[i] = 0;
  }
}

static void
addCounterStmt(IRSB* sbOut, Buffer_t* insts) {
  tl_assert(N_OPS <= sizeof(Buffer_t));
  IRDirty*   di;
  di = unsafeIRDirty_0_N( 0, "record_counts", 
          VG_(fnptr_to_fnentry)( &record_counts ), 
          mkIRExprVec_4(
           IRExpr_Const(IRConst_U64(insts->packed.longs[0])),
           IRExpr_Const(IRConst_U64(insts->packed.longs[1])),
           IRExpr_Const(IRConst_U64(insts->packed.longs[2])),
           IRExpr_Const(IRConst_U64(insts->packed.longs[3]))
          ));
  addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
  *insts = (Buffer_t) { .packed = {{0}} };
}

static
IRSB* og_instrument ( VgCallbackClosure* closure,
                      IRSB* sbIn,
                      const VexGuestLayout* layout, 
                      const VexGuestExtents* vge,
                      const VexArchInfo* archinfo_host,
                      IRType gWordTy, IRType hWordTy )
{
   IRSB*      sbOut;
   Int        i;

   Buffer_t insts = { .unpacked = {{0}} };
   Buffer_t is_flags = { .unpacked = {{0}} };

   if (gWordTy != hWordTy) {
      /* We don't currently support this case. */
      VG_(tool_panic)("host/guest word size mismatch");
   }

   /* Set up SB */
   sbOut = deepCopyIRSBExceptStmts(sbIn);

   // Copy verbatim any IR preamble preceding the first IMark
   i = 0;
   while (i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark) {
      addStmtToIRSB( sbOut, sbIn->stmts[i] );
      i++;
   }

   for (/*use current i*/; i < sbIn->stmts_used; i++) {
      IRStmt* st = sbIn->stmts[i];
      if (!st || st->tag == Ist_NoOp) continue;
      
      switch (st->tag) {
         case Ist_NoOp:
         case Ist_AbiHint:
         case Ist_Put:
         case Ist_PutI:
         case Ist_MBE:
         case Ist_Dirty:
            addStmtToIRSB( sbOut, st );
            break;

         case Ist_IMark: {
            increment_counters(&insts, &is_flags);
            addStmtToIRSB( sbOut, st );

            // we look at the original instruction here, that should use x86 decoding...
            Addr a = st->Ist.IMark.addr;
            UInt op_flags = code_types[*((UChar*)(a))]; // first op byte
            for (int f = 0; f < N_OPS; f++) {
              if (op_flags & (1 << f)) {
                is_flags.unpacked.bytes[f] = 1;
              }
            }
            break;
         }

         case Ist_WrTmp: {
            IRExpr* data = st->Ist.WrTmp.data;
            if (data->tag == Iex_Load) {
              is_flags.unpacked.bytes[OP_MEM] = 1;
            }
            IRExpr* expr = st->Ist.WrTmp.data;
            UInt op = 0;
            if (expr->tag == Iex_Qop) op = expr->Iex.Qop.details->op;
            if (expr->tag == Iex_Triop) op = expr->Iex.Triop.details->op;
            if (expr->tag == Iex_Binop) op = expr->Iex.Binop.op;
            if (expr->tag == Iex_Unop) op = expr->Iex.Unop.op;
            if (op != 0)  {
              tl_assert(op > Iop_INVALID && op < Iop_LAST);
              UInt op_flags = op_types[op - Iop_INVALID];
              for (int f = 0; f < N_OPS; f++) {
                if (op_flags & (1 << f)) {
                  is_flags.unpacked.bytes[f] = 1;
                }
              }
            }

            addStmtToIRSB( sbOut, st );
            break;
         }

         case Ist_Store:
         case Ist_StoreG:
         case Ist_LoadG: 
         case Ist_CAS:
         case Ist_LLSC: {
            is_flags.unpacked.bytes[OP_MEM] = 1;
            addStmtToIRSB( sbOut, st );
            break;
         }

         case Ist_Exit: {
            // the last op is not followed by an imark, so have it here
            increment_counters(&insts, &is_flags);
            addCounterStmt(sbOut, &insts);

            addStmtToIRSB( sbOut, st );      // Original statement
            break;
         }

         default:
            ppIRStmt(st);
            tl_assert(0);
      }
    }

    increment_counters(&insts, &is_flags);
    // record final counts, in case of fallthrough
    addCounterStmt(sbOut, &insts);
    
    //if (sb_ctr++ % 100 == 0) {
      //VG_(umsg)("At SB %d\n", sb_ctr);
      //ppIRSB(sbOut);
    //}
         
    return sbOut;
}

static void og_fini(Int exitcode)
{
  VG_(umsg)("Executed %'llu instructions.\n", global_ctrs[OP_ALL]);
  VG_(umsg)("   %'15llu jumps\n", global_jumps);
  VG_(umsg)("   %'15llu memory access related instructions\n", global_ctrs[OP_MEM]);
  VG_(umsg)("   %'15llu bitwise operations\n", global_ctrs[OP_BITS]);
  VG_(umsg)("   %'15llu integer operations\n", global_ctrs[OP_INT]);
  VG_(umsg)("   %'15llu floating-point operations\n", global_ctrs[OP_FP]);
  VG_(umsg)("   %'15llu vector/SIMD operations\n", global_ctrs[OP_VEC]);
  VG_(umsg)("   %'15llu strange decimal operations\n", global_ctrs[OP_DEC]);
  VG_(umsg)("   %'15llu strange fp operations\n", global_ctrs[OP_OLDFP]);
  VG_(umsg)("   %'15llu muls\n", global_ctrs[OP_MUL]);
  VG_(umsg)("   %'15llu divs\n", global_ctrs[OP_DIV]);
  VG_(umsg)("   %'15llu adds\n", global_ctrs[OP_ADD]);
  VG_(umsg)("   %'15llu subs\n", global_ctrs[OP_SUB]);
  VG_(umsg)("   %'15llu cmps\n", global_ctrs[OP_CMP]);
  VG_(umsg)("   %'15llu SSE SS\n", global_ctrs[OP_SSE_SS]);
  VG_(umsg)("   %'15llu SSE SD\n", global_ctrs[OP_SSE_SD]);
  VG_(umsg)("   %'15llu SSE PS\n", global_ctrs[OP_SSE_PS]);
  VG_(umsg)("   %'15llu SSE PD\n", global_ctrs[OP_SSE_PD]);
  VG_(umsg)("   %'15llu AVX PS\n", global_ctrs[OP_AVX_PS]);
  VG_(umsg)("   %'15llu AVX PD\n", global_ctrs[OP_AVX_PD]);
  VG_(umsg)("   %'15llu call ops\n", global_ctrs[OP_CALL]);
  VG_(umsg)("Exit code:       %d\n", exitcode);
}

static void og_pre_clo_init(void)
{
   VG_(details_name)            ("Opgrind");
   VG_(details_version)         (NULL);
   VG_(details_description)     ("a minimal, statistical Valgrind tool");
   VG_(details_copyright_author)(
      "Copyright (C) 2016, and GNU GPL'd, by Marcel Schneider.");
   VG_(details_bug_reports_to)  (VG_BUGS_TO);

   VG_(details_avg_translation_sizeB) ( 275 );

   VG_(basic_tool_funcs)        (og_post_clo_init,
                                 og_instrument,
                                 og_fini);

   /* No needs, no core events to track */
}

VG_DETERMINE_INTERFACE_VERSION(og_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
