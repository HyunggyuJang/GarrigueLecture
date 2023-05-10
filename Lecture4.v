Require Import ssreflect.
(* 偶数の定義 *)
Inductive even : nat -> Prop :=
| even_O : even O
| even_SS : forall n, even n -> even (S (S n)).
Module Odd.
  Inductive odd : nat -> Prop :=
  | odd_1 : odd 1
  | odd_SS : forall n, odd n -> odd (S (S n)).
  Theorem even_odd n : even n -> odd (S n).
  Proof. elim=> [|m IH]; [apply: odd_1 |apply: odd_SS]. Qed.
  Theorem odd_even n : odd n -> even (S n).
  Proof. elim=> [|m IH]; apply: even_SS. apply: even_O. Qed.
  Theorem even_not_odd n : even n -> ~odd n.
  Proof. elim=> [contr | m _ H contr]; by inversion contr. Qed.
End Odd.
