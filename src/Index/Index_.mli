open! Table
open! Global.Global_
include module type of INDEX
module MakeIndex (Global : GLOBAL) (Queue : Queue.QUEUE) : INDEX
module Index : INDEX
include INDEX
