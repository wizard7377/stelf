open Table_
include module type of SparseArray_intf

module SparseArray (SparseArray__0 : sig
  module IntTable : TABLE with type key = int
end) : SPARSE_ARRAY
