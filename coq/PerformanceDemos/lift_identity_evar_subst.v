(** * Performance Criterion: lifting identity evar substitution should Õ(1) *)

(** For this test, we construct [x] evars each with context size [y]
    and then we β-reduce to move them under a context with an
    additional [z] elements.  We also check to see how long it takes
    to β reduce the evars when β-reduction is the identity.  We
    contrast this to doing the same thing except using [x] copies of
    [tt] instead. *)
