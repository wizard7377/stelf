open Table_
include module type of SparseArray2_intf

module SparseArray2 (SparseArray2__0 : sig
  module IntTable : TABLE with type key = int
end) : SPARSE_ARRAY2
