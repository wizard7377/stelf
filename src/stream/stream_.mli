include module type of Stream_intf

module BasicStream : BASIC_STREAM

module BasicMemoStream : BASIC_STREAM

module MakeStream (Stream__0 : sig
  module BasicStream : BASIC_STREAM
end) : STREAM

module Stream : STREAM

module MStream : STREAM
