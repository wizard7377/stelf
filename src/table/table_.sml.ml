(* Re-export Queue sig and module that would otherwise be shadowed by stdlib Queue *)
module type QUEUE = Queue.QUEUE

module Queue = Queue.Queue
