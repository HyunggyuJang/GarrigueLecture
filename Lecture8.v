From mathcomp Require Import all_ssreflect.
Section sort.
  Variable A : eqType.
  Variable le : A -> A -> bool.
  Variable le_trans: forall x y z, le x y -> le y z -> le x z.
  Variable le_total: forall x y, ~~ le x y -> le y x.
  Fixpoint insert a l := match l with
                         | nil => (a :: nil)
                         | b :: l' => if le a b then a :: l else b :: insert a l'
                         end.
  Fixpoint isort l :=
    if l is a :: l' then insert a (isort l') else nil.
  Fixpoint sorted l := (* all を使って bool 上の述語を定義する *)
    if l is a :: l' then all (le a) l' && sorted l' else true.
  Lemma le_seq_insert a b l :
    le a b -> all (le a) l -> all (le a) (insert b l).
  Proof.
    elim: l => /= [-> // | c l IH].
    move=> leab /andP [leac leal].
    case: ifPn => lebc /=.
    - by rewrite leab leac.
    - by rewrite leac IH.
  Qed.
  Lemma mem_insert a b l : (a \in insert b l) = (a == b) || (a \in l).
  Proof.
    elim: l => //= c l IH.
    case: ifPn => //= _. rewrite inE IH inE orbCA //.
  Qed.
  Lemma le_seq_insert' a b l :
    le a b -> all (le a) l -> all (le a) (insert b l).
  Proof.
    move=> leab /allP Hl. apply/allP => c.
    rewrite mem_insert => /orP [/eqP -> | /Hl] //.
  Qed.
  Lemma insertP a b l : reflect (a = b \/ a \in l) (a \in insert b l).
  Proof.
    rewrite mem_insert. apply (iffP orP) => -[]. (* - is for recursive destruction *)
    move/eqP; auto. by right.
    move=> ->; by left. by right.
  Qed.
  Lemma le_seq_insert'' a b l :
    le a b -> all (le a) l -> all (le a) (insert b l).
  Proof.
    move=>leab /allP Hl. apply/allP => c.
    by case/insertP => [-> | /Hl].
  Qed.
  Lemma le_seq_trans a b l :
    le a b -> all (le b) l -> all (le a) l.
  Proof.
    move=> leab /allP lebl.
    apply/allP => x Hx.
    by apply/le_trans/lebl.
  Qed.
  Theorem insert_ok a l : sorted l -> sorted (insert a l).
  Proof.
    elim: l => /= [// | c l IH].
    move/andP => [Hall Hsorted].
    case: ifPn => leac //=.
    - rewrite leac Hsorted Hall /=.
      by rewrite (le_seq_trans a c).
    - rewrite IH. rewrite (le_seq_insert c a) => //.
      - by apply: le_total.
      - done.
  Qed.
  Theorem isort_ok l : sorted (isort l).
  Proof.
    elim: l => /= [// | c l IH].
    by apply: insert_ok.
  Qed.
  (* perm_eq が seq で定義されているが補題だけを使う *)
  Theorem insert_perm l a : perm_eq (a :: l) (insert a l).
  Proof.
    elim: l => //= b l pal.
    case: ifPn => //= leab.
    by rewrite (perm_catCA [:: a] [:: b]) perm_cons.
  Qed.
  Theorem isort_perm l : perm_eq l (isort l).
  Proof.
    elim: l => //= b l pal.
    eapply perm_trans.
    - erewrite perm_cons. apply: pal.
    apply/insert_perm.
  Qed.
End sort.

Definition isortn : seq nat -> seq nat := isort _ leq.
Definition sortedn := sorted _ leq.
Lemma leq_total' a b : ~~ (a <= b) -> b <= a.
Proof.
  apply/implyP.
  rewrite implyNb.
  apply/leq_total.
Qed.

Theorem isortn_ok l : sortedn (isortn l) && perm_eq l (isortn l).
Proof.
  rewrite/sortedn/isortn isort_ok => //=.
  rewrite isort_perm => //.
  - move => n m p. apply leq_trans.
  by apply: leq_total'.
Qed.

Require Import Extraction.
Extraction "isort.ml" isortn. (* コードが分かりにくい *)

Section even_odd.
  Notation even n := (~~ odd n). (* 単なる表記なので，展開が要らない *)
  Theorem even_double n : even (n + n).
  Proof. elim: n => // n. by rewrite addnS /= negbK. Qed.
  (* 等式を使って n に対する通常の帰納法を可能にする *)
  Theorem even_plus m n : even m -> even n = even (m + n).
  Proof.
    elim: n => /= [|n IH] Hm.
    - by rewrite addn0.
    - by rewrite addnS IH.
  Qed.
  Theorem one_not_even : ~~ even 1.
  Proof. reflexivity. Qed.
  Theorem even_not_odd n : even n -> ~~ odd n.
  Proof. done. Qed.
  Theorem even_odd n : even n -> odd n.+1.
  Proof. done. Qed.
  Theorem odd_even n : odd n -> even n.+1.
  Proof. by rewrite negbK. Qed.
  Theorem even_or_odd n : even n || odd n.
  Proof. by rewrite orNb. Qed.
  Theorem odd_odd_even m n : odd m -> odd n = even (m+n).
  Proof. rewrite addnC. elim: n => /= [-> // | n IH Hm]. by rewrite IH. Qed.

End even_odd.
