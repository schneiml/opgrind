
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
    printf '[%-20s-Iop_INVALID] = 0' $op 
    [[ $op =~ (32|64)F ]]               && printf ' | OP_FP'    # mostly vector things
    [[ $op =~ (8|16|32|64)(U|I|S) ]]    && printf ' | OP_INT'   # should be exclusive wrt above
    [[ $op =~ x(2|4|8|16)|V(128|256) ]] && printf ' | OP_VEC'   # all SIMD
    [[ $op =~ D(32|64|128) ]]           && printf ' | OP_DEC'   # Decimal encoding, should not appear in amd64
    [[ $op =~ F(32|64|128) ]]           && printf ' | OP_OLDFP' # Scalar FP (x87), should not appear
    [[ $op =~ (U|I|S)(8|16|32|64) ]]    && printf ' | OP_INT'   # Scalar int
    [[ $op =~ [UISFD][0-9]+|[0-9]+[UISFD] ]] || printf ' | OP_BITS' # none of the above
    # Mul, Div, Add, Sub, conv ('to'), Sqrt, Cmp could also be easily marked.
    printf ',\n'
 done ) > op_types.inc
 *
 * Index with Iop_INVALID+opcode.
 */
enum Op_Types {
  OP_FP = 1, OP_INT = 2, OP_VEC = 4, OP_DEC = 8, OP_OLDFP = 16, OP_BITS = 32
};
static const UInt op_types[] = {
#include "op_types.inc"
0 /* dummy for syntax */ };

static void og_post_clo_init(void)
{
}

static ULong global_guest_insts,
             global_mem_insts,
             global_bit_insts,
             global_int_insts,
             global_float_insts,
             global_vec_insts,
             global_misc_insts,
             global_jumps;

static ULong sb_ctr;

static void record_counts(ULong guest, 
                          ULong mem, 
                          ULong bit,
                          ULong ints, 
                          ULong floats, 
                          ULong vec
                          /*ULong misc*/)
{
   global_guest_insts += guest;
   global_mem_insts += mem;
   global_bit_insts += bit;
   global_int_insts += ints;
   global_float_insts += floats;
   global_vec_insts += vec;
   //global_misc_insts += misc;

   global_jumps++;
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
   IRDirty*   di;
   Int        i;

   UInt        guest_insts = 0;
   UInt        mem_insts   = 0;
   UInt        bit_insts   = 0;
   UInt        int_insts   = 0;
   UInt        float_insts = 0;
   UInt        vec_insts   = 0;
   UInt        misc_insts  = 0;
   Bool is_mem = False, is_bit = False, is_int = False, 
        is_float = False, is_vec = False, is_misc = False;

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
            guest_insts++;
            if (is_mem  ) {mem_insts++;   is_mem = False;}
            if (is_bit  ) {bit_insts++;   is_bit = False;}
            if (is_int  ) {int_insts++;   is_int = False;}
            if (is_float) {float_insts++; is_float = False;}
            if (is_vec  ) {vec_insts++;   is_vec = False;}
            if (is_misc ) {misc_insts++;  is_misc = False;}
            addStmtToIRSB( sbOut, st );
            break;
         }

         case Ist_WrTmp: {
            IRExpr* data = st->Ist.WrTmp.data;
            if (data->tag == Iex_Load) {
              is_mem = True;
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
              if (op_flags & OP_FP)  is_float = True;
              if (op_flags & OP_INT) is_int = True;
              if (op_flags & OP_VEC) is_vec = True;
              if (op_flags & OP_BITS) is_bit = True;
              if (op_flags & OP_OLDFP || op_flags & OP_DEC) 
                is_misc = True;
            }

            // TODO: look at opcodes to see what is done.
            // on amd64, we will mostly see vector ops for
            // FP (no x87), so we have to look at all of these.
            addStmtToIRSB( sbOut, st );
            break;
         }

         case Ist_Store:
         case Ist_StoreG:
         case Ist_LoadG: 
         case Ist_CAS:
         case Ist_LLSC: {
            is_mem = True;
            addStmtToIRSB( sbOut, st );
            break;
         }

         case Ist_Exit: {
            // the last op is not followed by an imark, so have it here
            if (is_mem  ) {mem_insts++;   is_mem = False;}
            if (is_bit  ) {bit_insts++;   is_bit = False;}
            if (is_int  ) {int_insts++;   is_int = False;}
            if (is_float) {float_insts++; is_float = False;}
            if (is_vec  ) {vec_insts++;   is_vec = False;}
            if (is_misc ) {misc_insts++;  is_misc = False;}
            di = unsafeIRDirty_0_N( 0, "record_counts", 
                    VG_(fnptr_to_fnentry)( &record_counts ), 
                    mkIRExprVec_6(
                     IRExpr_Const(IRConst_U64(guest_insts)),
                     IRExpr_Const(IRConst_U64(mem_insts  )),
                     IRExpr_Const(IRConst_U64(bit_insts  )),
                     IRExpr_Const(IRConst_U64(int_insts  )),
                     IRExpr_Const(IRConst_U64(float_insts)),
                     IRExpr_Const(IRConst_U64(vec_insts  ))
                     /*IRExpr_Const(IRConst_U64(misc_insts ))*/));
            addStmtToIRSB( sbOut, IRStmt_Dirty(di) );

            guest_insts = mem_insts = bit_insts = int_insts 
              = float_insts = vec_insts = misc_insts= 0;

            addStmtToIRSB( sbOut, st );      // Original statement
            break;
         }

         default:
            ppIRStmt(st);
            tl_assert(0);
      }
    }
    // the last op is not followed by an imark, so have it here
    if (is_mem  ) {mem_insts++;   is_mem = False;}
    if (is_bit  ) {bit_insts++;   is_bit = False;}
    if (is_int  ) {int_insts++;   is_int = False;}
    if (is_float) {float_insts++; is_float = False;}
    if (is_vec  ) {vec_insts++;   is_vec = False;}
    if (is_misc ) {misc_insts++;  is_misc = False;}
    // record final counts, in case of fallthrough
    di = unsafeIRDirty_0_N( 0, "record_counts", 
            VG_(fnptr_to_fnentry)( &record_counts ), 
            mkIRExprVec_6(
             IRExpr_Const(IRConst_U64(guest_insts)),
             IRExpr_Const(IRConst_U64(mem_insts  )),
             IRExpr_Const(IRConst_U64(bit_insts  )),
             IRExpr_Const(IRConst_U64(int_insts  )),
             IRExpr_Const(IRConst_U64(float_insts)),
             IRExpr_Const(IRConst_U64(vec_insts  ))
             /*IRExpr_Const(IRConst_U64(misc_insts ))*/));
    addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
    
    if (sb_ctr++ % 100 == 0) {
      VG_(umsg)("At SB %d\n", sb_ctr);
      ppIRSB(sbOut);
    }

         
    return sbOut;
}

static void og_fini(Int exitcode)
{
  VG_(umsg)("Executed %'llu instructions.\n", global_guest_insts);
  VG_(umsg)("   %'llu jumps\n", global_jumps);
  VG_(umsg)("   %'llu memory access related instructions\n", global_mem_insts);
  VG_(umsg)("   %'llu bitwise operations\n", global_bit_insts);
  VG_(umsg)("   %'llu integer operations\n", global_int_insts);
  VG_(umsg)("   %'llu floating-point operations\n", global_float_insts);
  VG_(umsg)("   %'llu vector/SIMD operations\n", global_vec_insts);
  //VG_(umsg)("   %'llu strange operations\n", global_misc_insts);
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
