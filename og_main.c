
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
    # Mul, Div, Add, Sub, conv ('to'), Sqrt, Cmp could also be easily marked.
    printf ',\n'
 done ) > op_types.inc
 *
 * Index with Iop_INVALID+opcode.
 */
#define BIT(flag) (1 << flag)
enum Op_Types {
  OP_ALL=0, OP_MEM, OP_FP, OP_INT, OP_VEC, OP_DEC, OP_OLDFP, OP_BITS, 
  N_OPS
};
static const UInt op_types[] = {
#include "op_types.inc"
0 /* dummy for syntax */ };

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
  Buffer_t buffer = { .packed = {{ctrs1, ctrs2, ctrs3, ctrs4}} };
  for (int i = 0; i < N_OPS; i++) {
    global_ctrs[i] += buffer.unpacked.bytes[i];
  }

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
            // we could look at the original instruction here, but that would need x86 decoding...
            increment_counters(&insts, &is_flags);
            addStmtToIRSB( sbOut, st );
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
  VG_(umsg)("   %'llu jumps\n", global_jumps);
  VG_(umsg)("   %'llu memory access related instructions\n", global_ctrs[OP_MEM]);
  VG_(umsg)("   %'llu bitwise operations\n", global_ctrs[OP_BITS]);
  VG_(umsg)("   %'llu integer operations\n", global_ctrs[OP_INT]);
  VG_(umsg)("   %'llu floating-point operations\n", global_ctrs[OP_FP]);
  VG_(umsg)("   %'llu vector/SIMD operations\n", global_ctrs[OP_VEC]);
  VG_(umsg)("   %'llu strange decimal operations\n", global_ctrs[OP_DEC]);
  VG_(umsg)("   %'llu strange fp operations\n", global_ctrs[OP_OLDFP]);
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
