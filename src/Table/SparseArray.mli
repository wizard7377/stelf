open Table_
include module type of SPARSEARRAY

module SparseArray (SparseArray__0 : sig
  module IntTable : TABLE with type key = int
end) : SPARSE_ARRAY
