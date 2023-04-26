Require Import ssreflect.
Section Coq1.
Variables P Q R : Prop.
Theorem imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  move=> pq qr /pq //.
Qed.
Theorem not_false : ~False.
Proof.
  done.
Qed.
Theorem double_neg : P -> ~~P.
Proof.
  move => p np //.
Qed.
Theorem contraposition : (P -> Q) -> ~Q -> ~P.
Proof.
  move => pq nq /pq //.
Qed.
Theorem and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  move => [p [q r]] //.
Qed.
Theorem and_distr : P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  move => [p [q | r]]; [left | right]; done.
Qed.
Theorem absurd : P -> ~P -> Q.
Proof.
  move => p np; done.
Qed.
Definition DM_rev := forall P Q, ~ (~P /\ ~Q) -> P \/ Q.
Definition EM := forall P : Prop, P \/ ~ P.
Theorem DM_rev_is_EM : DM_rev <-> EM.
Proof.
  split => [dm | em].
  - move => P'.
    apply: (dm P' (~P')).
    by move => [np' nnp'].
  - move => P' Q'.
    move: (em P') => [p' | np'].
    + by left.
    + move: (em Q') => [q' | nq'].
      * by right.
      * elim; done.
Qed.
End Coq1.
