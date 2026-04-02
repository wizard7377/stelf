include module type of Abstract_intf

module MakeAbstract
    (Whnf : Whnf.WHNF)
    (Unify : Unify.UNIFY)
    (Constraints : Constraints.CONSTRAINTS) :
  ABSTRACT
