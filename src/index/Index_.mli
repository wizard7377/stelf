include module type of Index_intf

module MakeIndex (Global : GLOBAL) (Queue : Queue.QUEUE) : INDEX

module Index : INDEX
include INDEX
