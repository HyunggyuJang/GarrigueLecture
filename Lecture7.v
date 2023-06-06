From mathcomp Require Import all_ssreflect.

Section Sort.
  Variables (A:Set) (le:A->A->bool). (* データ型 A とのその順序 le *)
  (* 既に整列されたリスト l の中に a を挿入する *)
  Fixpoint insert a (l: list A) :=
    match l with
    | nil => (a :: nil)
    | b :: l' => if le a b then a :: l else b :: insert a l'
    end.
  (* 繰り返しの挿入でリスト l を整列する *)
  Fixpoint isort (l : list A) : list A :=
    match l with
    | nil => nil
    | a :: l' => insert a (isort l')
    end.
  (* le は推移律と完全性をみたす *)
  Hypothesis le_trans: forall x y z, le x y -> le y z -> le x z.
  Hypothesis le_total: forall x y, ~~ le x y -> le y x.
  (* le_list x l : x はあるリスト l の全ての要素以下である *)
  Inductive All (P : A -> Prop) : list A -> Prop :=
  | All_nil : All P nil
  | All_cons : forall y l, P y -> All P l -> All P (y::l).
  Notation "'le_list' x" := (All (fun y => le x y)) (at level 0).
  (* sorted l : リスト l は整列されている *)
  Inductive sorted : list A -> Prop :=
  | sorted_nil : sorted nil
  | sorted_cons : forall a l,
      le_list a l -> sorted l -> sorted (a::l).
  Hint Constructors All sorted. (* auto の候補にする *)
  Lemma le_list_insert a b l :
    le a b -> le_list a l -> le_list a (insert b l).
  Proof.
    move=> leab; elim: l/ => [|c l] /=. info_auto.
    case: ifPn. info_auto. info_auto.
  Qed.
  Lemma le_list_trans a b l :
    le a b -> le_list b l -> le_list a l.
  Proof.
    move=> leab; elim: l/. info_auto.
    info_eauto. (* 推移律は eauto が必要 *)
  Qed.
  Hint Resolve le_list_insert le_list_trans. (* 補題も候補に加える *)
  Theorem insert_ok a l : sorted l -> sorted (insert a l).
  Proof.
    elim: l/ => [|c l] /=. info_auto.
    case: ifPn. info_eauto. info_eauto.
  Qed.
  Theorem isort_ok l : sorted (isort l).
  Proof.
    elim: l => [|c l] //.
    apply/insert_ok.
  Qed.
  (* Permutation l1 l2 : リスト l2 は l1 の置換である *)
  Inductive Permutation : list A -> list A -> Prop :=
  | perm_nil: Permutation nil nil
  | perm_skip: forall x l l',
      Permutation l l' -> Permutation (x::l) (x::l')
  | perm_swap: forall x y l, Permutation (y::x::l) (x::y::l)
  | perm_trans: forall l l' l'',
      Permutation l l' ->
      Permutation l' l'' -> Permutation l l''.
  Hint Constructors Permutation.
  Theorem Permutation_refl l : Permutation l l.
  Proof.
    elim: l => [|c l] //. info_auto.
  Qed.
  Theorem insert_perm l a : Permutation (a :: l) (insert a l).
  Proof.
    elim: l => [|c l] /=. info_auto.
    case: ifPn. info_eauto. info_eauto.
  Qed.
  Theorem isort_perm l : Permutation l (isort l).
  Proof.
    elim: l => [|c l] /=. info_auto.
    info_eauto using insert_perm.
  Qed.
  (* 証明付き整列関数 *)
  Definition safe_isort l : {l'|sorted l' /\ Permutation l l'}.
    exists (isort l).
    auto using isort_ok, isort_perm.
  Defined.
  Print safe_isort.
End Sort.
Check safe_isort. (* le と必要な補題を与えなければならない *)
Require Extraction.
Extraction leq. (* mathcomp の eqType の抽出が汚ない *)
Definition leq' m n := if m - n is 0 then true else false.
Extraction leq'. (* こちらはすっきりする *)
Lemma leq'E m n : leq' m n = (m <= n).
Proof. rewrite /leq' /leq. by case: (m-n). Qed.
Lemma leq'_trans m n p : leq' m n -> leq' n p -> leq' m p.
Proof. rewrite !leq'E; apply leq_trans. Qed.
Lemma leq'_total m n : ~~ leq' m n -> leq' n m.
Proof.
  apply/implyP.
  rewrite implyNb !leq'E.
  apply/leq_total.
Qed.
Definition isort_leq := safe_isort nat leq' leq'_trans leq'_total.
Eval compute in proj1_sig (isort_leq (3 :: 1 :: 2 :: 0 :: nil)).
Extraction "isort.ml" isort_leq.
