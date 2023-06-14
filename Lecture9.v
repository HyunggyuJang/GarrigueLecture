From mathcomp Require Import all_ssreflect.
Section Nagoya2013.
  Definition Sk k n := \sum_(1 <= i < n.+1) i^k.
  Variable m : nat.
  Hypothesis Hm : m > 1.
  Definition Tm n := \sum_(1 <= k < m) 'C(m,k) * Sk k n. (* binomial.v 参照 *)
  Lemma Sk1 k : Sk k 1 = 1.
  Proof. by rewrite /Sk big_nat1 exp1n. Qed.
  Lemma Tm1 : Tm 1 = 2^m - 2.
  Proof.
    rewrite /Tm.
    rewrite [in 2^m](_ : 2 = 1+1) //.
    rewrite Pascal. (* 二項公式 *)
    transitivity ((\sum_(0 <= k < m.+1) 'C(m,k)) - 2).
      symmetry.
      rewrite (@big_cat_nat _ _ _ m) //=.
      rewrite (@big_cat_nat _ _ _ 1) //=; last by apply ltnW.
      rewrite addnAC !big_nat1 bin0 binn addKn.
      apply eq_bigr => i H.
      by rewrite Sk1 muln1.
    rewrite big_mkord.
    congr (_ - _).
    apply eq_bigr => i _.
    by rewrite !exp1n !muln1.
  Qed.
  Lemma Tm2 : Tm 2 = 3^m - 3.
  Proof.
    rewrite /Tm.
    have -> : 3^m - 3 = 2^m - 2 + (3^m - 1 - 2^m).
    {
      have H: 2 ^ m <= 3 ^ m - 1. admit.
      have H': 1 <= 3 ^ m. admit.
      rewrite !addnBA => //.
      move => {H} {H'}.
      have -> : 2 ^ m - 2 + 3 ^ m - 1 = 2 ^ m + (3 ^ m - 3).
        rewrite addnC.
        have H : 2 ^ m >= 2. admit.
        rewrite addnBA => //.
        move => {H}.
        rewrite -subnDA.
        rewrite addnC.
        have H : 3 ^ m >= 3. admit.
        by rewrite addnBA => //.
      by rewrite addKn.
    }
    rewrite -Tm1.
    rewrite [in 3^m](_ : 3 = 1+2) //.
    rewrite Pascal.
    transitivity (Tm 1 + (\sum_(1 <= k < m) 'C(m,k) * 2^k)).
    rewrite -big_split /=.
    apply eq_bigr => i _.
    rewrite /Sk !big_cons !big_nil.
    by rewrite !addn0 -mulnDr.
    congr (_ + _).
    transitivity ((\sum_(0 <= k < m.+1) 'C(m,k) * 2^k) - 1 - 2^m).
  Admitted.
  Theorem Tmn n : Tm n.+1 = n.+2^m - n.+2.
  Proof.
    elim:n => [|n IHn] /=.
    by apply Tm1.
    have Hm': m > 0 by apply ltnW.
    have ->: n.+3 ^ m - n.+3 = n.+2 ^ m - n.+2 + (n.+3 ^ m - 1 - n.+2 ^ m).
  Admitted.
  Theorem Skp p k : p > 2 -> prime p -> 1 <= k < p.-1 -> p %| Sk k p.-1.
  Admitted.
End Nagoya2013.
