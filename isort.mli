
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

val sub : nat -> nat -> nat

val subn_rec : nat -> nat -> nat

val subn : nat -> nat -> nat

val insert : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list

val isort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list

val safe_isort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list

val leq' : nat -> nat -> bool

val isort_leq : nat list -> nat list
