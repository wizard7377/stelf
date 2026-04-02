(* # 1 "src/int_inf/IntInf_.sig.ml" *)

(* # 1 "src/int_inf/IntInf_.fun.ml" *)

(* # 1 "src/int_inf/IntInf_.sml.ml" *)
open Basis
open IntInfSig

(* int-inf.sml
 *
 * COPYRIGHT (c) 1995 by AT&T Bell Laboratories. See COPYRIGHT file for details.
 *
 * This package is derived from Andrzej Filinski's bignum package.  It is versy
 * close to the definition of the optional IntInf structure in the SML'97 basis.
 *
 * It is implemented almost totally on the abstraction presented by
 * the BigNat structure. The only concrete type information it assumes
 * is that BigNat.bignat = 'a list and that BigNat.zero = [].
 * Some trivial additional efficiency could be obtained by assuming that
 * type bignat is really int list, and that if (v : bignat) = [d], then
 * bignat d = [d].
 *
 * At some point, this should be reimplemented to make use of Word32, or
 * have compiler/runtime support.
 *
 * Also, for booting, this module could be broken into one that has
 * all the types and arithmetic functions, but doesn't use NumScan,
 * constructing values from strings using bignum arithmetic. Various
 * integer and word scanning, such as NumScan, could then be constructed
 * from IntInf. Finally, a user-level IntInf could be built by
 * importing the basic IntInf, but replacing the scanning functions
 * by more efficient ones based on the functions in NumScan.
 *
 *)

module IntInf : INT_INF
