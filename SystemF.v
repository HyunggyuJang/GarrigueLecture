Require Import ssreflect.
Section SystemF.
  Definition Fand P Q := forall X : Prop, (P -> Q -> X) -> X.
  Definition For P Q := forall X : Prop, (P -> X) -> (Q -> X) -> X.
  Definition Ffalse := forall X : Prop, X.
  Definition Ftrue := forall X : Prop, (X -> X).
  Definition Feq {T} (x y : T) := forall P, Fand (P x -> P y) (P y -> P x).
  Definition Fex {T} (P : T -> Prop) := forall X : Prop, (forall x, P x -> X) -> X.
  Theorem Fand_ok (P Q : Prop) : Fand P Q <-> P /\ Q.
  Proof.
    split => [pq | [p q] X].
    - split; by apply: pq.
    - by apply.
  Qed.
  Theorem For_ok (P Q : Prop) : For P Q <-> P \/ Q.
  Proof.
    split => [porq | [p | q] X px qx].
    - apply: porq => H; by [left | right].
    - by apply: px.
    - by apply: qx.
  Qed.
  Theorem Ffalse_ok : Ffalse <-> False.
  Proof. split => [ffalse | //]. apply: ffalse. Qed.
  Theorem Ftrue_ok : Ftrue <-> True.
  Proof. split => // _ //. Qed.
  Theorem Feq_ok T (x y : T) : Feq x y <-> x = y.
  Proof.
    split => [/(_ (fun x => x = y))/Fand_ok [_ H]| -> P X].
    - by apply: H.
    - by apply.
  Qed.
  Theorem Fex_ok T (P : T -> Prop) : Fex P <-> exists x, P x.
  Proof.
    split => [fex | [x px]].
    - apply: fex => x px. by exists x.
                              - move => X H. by apply: (H x px).
  Qed.
  Definition Nat := forall X : Prop, (X -> X) -> X -> X.
  Definition Zero : Nat := fun X f x => x.
  Definition Succ (N : Nat) : Nat := fun X f x => f (N X f x).
  Definition Plus (M N : Nat) : Nat := fun X f x => M X f (N X f x).
  Definition Mult (M N : Nat) : Nat := fun X f x => M X (N X f) x.
  (* こちらの定義はより直感的だが，非可述的である *)
  Definition Plus' (M N : Nat) : Nat := M Nat Succ N. (* 1 を M 回足す *)
  Definition Mult' (M N : Nat) : Nat := M Nat (Plus' N) Zero. (* N を M 回足す *)
  Fixpoint Nat_of_nat n : Nat := (* 自然数を Nat に変換 *)
    match n with 0 => Zero | S m => Succ (Nat_of_nat m) end.
  Definition eq_Nat (M N : Nat) := forall X f x, M X f x = N X f x.
  Definition eq_Nat_fun F f := forall n,
      eq_Nat (F (Nat_of_nat n)) (Nat_of_nat (f n)).
  Definition eq_Nat_op Op op := forall m n,
      eq_Nat (Op (Nat_of_nat m) (Nat_of_nat n)) (Nat_of_nat (op m n)).
  Theorem Succ_ok : eq_Nat_fun Succ S. Proof. by elim. Qed. (* 実は自明 *)
  Theorem Plus_ok : eq_Nat_op Plus plus.
  Proof.
    move=> m n X f x.
    elim: m => //= m IH.
    by rewrite [in RHS]/Succ -IH.
  Qed.
  Theorem Mult_ok : eq_Nat_op Mult mult.
  Proof.
    move=> m n X f x.
    elim: m => //= m IH.
    by rewrite -Plus_ok /Plus -IH.
  Qed.

  Definition Pow (M N : Nat) := fun X => N _ (M X). (* M の N 乗 *)
  Fixpoint pow m n := match n with 0 => 1 | S n => m * pow m n end.
  Lemma Nat_of_nat_eq : forall n X f1 f2 x,
      (forall y, f1 y = f2 y) ->
      Nat_of_nat n X f1 x = Nat_of_nat n X f2 x.
  Proof.
    move => n X f1 f2 x H.
    elim: n => //= n IH.
    by rewrite /Succ -IH.
  Qed.

  Theorem Pow_ok : eq_Nat_op Pow pow.
  Proof.
    move=> m n X f x.
    elim: n x => //= n IH x.
    rewrite -Mult_ok /Mult.
    rewrite (Nat_of_nat_eq _ _ (Nat_of_nat (pow m n) X f) (Pow (Nat_of_nat m) (Nat_of_nat n) X f)).
    by (move => y; rewrite IH).
    done.
  Qed.

  Section ProdSum. (* 値の対と直和も定義できます *)
    Variables X Y : Prop.
    Definition Prod := forall Z : Prop, (X -> Y -> Z) -> Z.
    Definition Pair (x : X) (y : Y) : Prod := fun Z f => f x y.
    Definition Fst (p : Prod) := p _ (fun x y => x).
    Definition Snd (p : Prod) := p _ (fun x y => y).
    Definition Sum := forall Z : Prop, (X -> Z) -> (Y -> Z) -> Z.
    Definition InL x : Sum := fun Z f g => f x.
    Definition InR x : Sum := fun Z f g => g x.
  End ProdSum.
  Arguments Pair [X Y]. Arguments Fst [X Y]. Arguments Snd [X Y].
  Arguments InL [X] Y. Arguments InR X [Y]. (* 型引数を省略できるようにする *)
  Definition Pred (N : Nat) := (* 前者関数の定義は工夫が必要 *)
    Fst (N _ (fun p : Prod Nat Nat => Pair (Snd p) (Succ (Snd p)))
           (Pair Zero Zero)).
  Theorem Pred_ok : eq_Nat_fun Pred pred.
  Proof.
    move => n X f x.
    elim: n => //= n.
    case: n => //= n IH.
    by rewrite [in RHS]/Succ -IH.
  Qed.
  (* Nat が Set で定義されているときだけ証明可能 *)
  Lemma Nat_of_nat_ok : forall n, Nat_of_nat n _ S O = n. Abort.
End SystemF.
