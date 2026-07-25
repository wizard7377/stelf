(* # 1 "src/frontend/Version.sig.ml" *)

(* # 1 "src/frontend/Version.fun.ml" *)

(* # 1 "src/frontend/Version.sml.ml" *)
open! Basis

module Version : sig
  val current_version : string
  val current_version_revision : string
  val build_revision : string
  val build_date : string
  val build_hostname : string
  val official : bool
  val external_ : bool
  val version_string : string
end
