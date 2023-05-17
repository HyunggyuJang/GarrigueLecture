From mathcomp Require Import all_ssreflect.
Module Equalities.
  Theorem square_sum a b : (a + b)^2 = a^2 + 2 * a * b + b^2.
  Proof. by rewrite sqrnD addnAC mulnA. Qed.
  Theorem diff_square m n : m >= n -> m^2 - n^2 = (m+n) * (m-n).
  Proof.
    move => le_nm.
    rewrite mulnDl !mulnBr [n * m]mulnC addnCBA.
    rewrite subnKC // leq_mul //.
    rewrite leq_mul //.
  Qed.
  Theorem square_diff m n : m >= n -> (m-n)^2 = m^2 + n^2 - 2 * m * n.
  Proof. move => le_nm. rewrite sqrnB //. by rewrite mulnA. Qed.
End Equalities.

Require Import Wf_nat Recdef.

Function gcd (m n : nat) {wf lt m} : nat :=
  if m is 0 then n else gcd (modn n m) m.
Proof.
  - move=> m n m0 _. apply/ltP.
    by rewrite ltn_mod.
  - exact: lt_wf.
Qed.

Theorem gcd_divides m n : (gcd m n %| m) && (gcd m n %| n).
Proof.
  functional induction (gcd m n).
    by rewrite dvdn0 dvdnn.
  move: IHn0 => /andP.
  move => [gcd_mod_mn gcd_m].
  apply/andP. split => //.
  rewrite [X in _ %| X](divn_eq n m).
  rewrite dvdn_add //.
  rewrite dvdn_mull //.
Qed.

Theorem gcd_max g m n : g %| m -> g %| n -> g %| gcd m n.
Proof.
  functional induction (gcd m n).
    by done.
  move => mod_gm mod_gn.
  apply/IHn0 => //.
  rewrite [X in _ %| X](divn_eq n m) in mod_gn.
  have mod_mulm: (g %| n %/ m * m).
    by rewrite dvdn_mull.
  rewrite dvdn_addr in mod_gn => //.
Qed.

Lemma odd_square n : odd n = odd (n*n).
Proof. rewrite oddM. case: (odd n) => //. Qed.

Lemma even_double_half n : ~~odd n -> n./2.*2 = n.
Proof. by apply: even_halfK. Qed.

(* 本定理 *)
Theorem main_thm (n p : nat) : n * n = (p * p).*2 -> p = 0.
Proof.
  elim/lt_wf_ind: n p => n. (* 整礎帰納法 *)
  case: (posnP n) => [-> _ [] // | Hn IH p Hnp].
  have even_n: ~~odd n.
    by rewrite odd_square Hnp odd_double.
  move: (Hnp).
  rewrite -(even_double_half n) //.
  rewrite -doubleMl -doubleMr.
  rewrite -mul2n -[RHS]mul2n.
  move/eqP. rewrite eqn_mul2l => /orP [contr | /eqP/esym even_p] //.
  have half_n0: n./2 = 0.
  { apply/(IH _ _ _ even_p)/ltP.
    rewrite -ltn_sqr.
    rewrite -!mulnn Hnp -muln2.
    rewrite -[ltnLHS]muln1.
    rewrite ltn_mul2l.
    apply/andP. split => //.
    move: Hn.
    by rewrite -sqrn_gt0 -mulnn Hnp double_gt0.
  }
  apply/eqP.
  move: even_p.
  rewrite half_n0 -muln2 !mul0n /=.
  move/eqP.
  rewrite muln_eq0.
  case: (p == 0) => //.
Qed.


(* 無理数 *)
Require Import Reals Field. (* 実数とそのための field タクティク *)
Definition irrational (x : R) : Prop :=
  forall (p q : nat), q <> 0 -> x <> (INR p / INR q)%R.
Theorem irrational_sqrt_2: irrational (sqrt (INR 2)).
Proof.
  move=> p q Hq Hrt.
  apply /Hq /(main_thm p) /INR_eq.
  rewrite -mul2n !mult_INR -(sqrt_def (INR 2)) ?Hrt; last by auto with real.
  have Hqr : INR q <> 0%R by auto with real.
  by field.
Qed.
