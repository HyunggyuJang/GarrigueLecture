
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

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val subn_rec : nat -> nat -> nat **)

let subn_rec =
  sub

(** val subn : nat -> nat -> nat **)

let subn =
  subn_rec

(** val insert : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec insert le a l = match l with
| Nil -> Cons (a, Nil)
| Cons (b, l') ->
  (match le a b with
   | True -> Cons (a, l)
   | False -> Cons (b, (insert le a l')))

(** val isort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec isort le = function
| Nil -> Nil
| Cons (a, l') -> insert le a (isort le l')

(** val safe_isort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let safe_isort =
  isort

(** val leq' : nat -> nat -> bool **)

let leq' m n =
  match subn m n with
  | O -> True
  | S _ -> False

(** val isort_leq : nat list -> nat list **)

let isort_leq =
  safe_isort leq'
