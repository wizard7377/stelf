include module type of Stream_intf

module BasicStream : BASIC_STREAM

module BasicMemoStream : BASIC_STREAM

module MakeStream (BasicStream : BASIC_STREAM) : STREAM

module Stream : STREAM

module MStream : STREAM
