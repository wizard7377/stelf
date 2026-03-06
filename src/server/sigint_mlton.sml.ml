open! Basis;;
module SigINT : SIGINT =
  struct
    let rec interruptLoop ((loop : unit -> unit)) =
      let _ =
        MLton.Cont.callcc
        (function 
                  | k
                      -> MLton.Signal.setHandler
                         (Posix.Signal.int,
                          MLton.Signal.Handler.handler
                          (function 
                                    | _
                                        -> MLton.Thread.prepare
                                           (MLton.Thread.new_
                                            (function 
                                                      | ()
                                                          -> MLton.Cont.throw
                                                             (k, ())),
                                            ()))))
        in loop () (* open MLton *);;
    end;;