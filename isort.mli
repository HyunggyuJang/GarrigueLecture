
type __ = Obj.t

type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val sub : nat -> nat -> nat

type reflect =
| ReflectT
| ReflectF

val iffP : bool -> reflect -> reflect

val idP : bool -> reflect

type 't pred = 't -> bool

type 't rel = 't -> 't pred

module Equality :
 sig
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  val op : 'a1 mixin_of -> 'a1 rel

  type coq_type = __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort mixin_of
 end

val eq_op : Equality.coq_type -> Equality.sort rel

val eqn : nat -> nat -> bool

val eqnP : nat Equality.axiom

val nat_eqMixin : nat Equality.mixin_of

val nat_eqType : Equality.coq_type

val subn_rec : nat -> nat -> nat

val subn : nat -> nat -> nat

val leq : nat -> nat -> bool

val insert :
  Equality.coq_type -> (Equality.sort -> Equality.sort -> bool) -> Equality.sort
  -> Equality.sort list -> Equality.sort list

val isort :
  Equality.coq_type -> (Equality.sort -> Equality.sort -> bool) -> Equality.sort
  list -> Equality.sort list

val isortn : nat list -> nat list
