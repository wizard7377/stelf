open! Basis;;
module Debug : DEBUG =
  struct
    exception Assert of exn ;;
    let assert' = ref true;;
    let print' = ref true;;
    let rec enable () = begin
                          assert' := true;print' := true
                          end;;
    let rec disable () = begin
                           assert' := true;print' := true
                           end;;
    let rec enable_assertions () = assert' := true;;
    let rec disable_assertions () = assert' := false;;
    let rec enable_printing () = print' := true;;
    let rec disable_printing () = print' := false;;
    let rec assert_ (c, exn) = begin
      if ! assert' then begin if c then () else raise ((Assert exn)) end else
      () end;;
    let rec print s = begin if ! print' then TextIO.print (s ^ "\n") else ()
      end;;
    end;;