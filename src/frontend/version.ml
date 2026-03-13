(* # 1 "src/frontend/version.sig.ml" *)

(* # 1 "src/frontend/version.fun.ml" *)

(* # 1 "src/frontend/version.sml.ml" *)
open! Basis

module Version = struct
  let current_version = "1.7.1"
  let current_version_revision = "1813"
  let build_revision = "exported"
  let build_date = "unknown-date"
  let build_hostname = "unknown-host"

  let rec maybe arg__0 arg__1 =
    begin match (arg__0, arg__1) with true, x -> x | false, x -> ""
    end

  let official = build_revision = current_version_revision
  let external_ = build_revision = "exported"

  let version_string =
    (((((((("Twelf " ^ current_version) ^ maybe (not official) "+") ^ " (")
        ^ maybe ((not external_) && not official) (("r" ^ build_revision) ^ ", ")
        )
       ^ "built ")
      ^ build_date)
     ^ " on ")
    ^ build_hostname)
    ^ ")"
end
