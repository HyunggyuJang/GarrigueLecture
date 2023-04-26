Require Import ssreflect.
Section Eq.
  Variable T : Type.
  Lemma symmetry : forall x y : T, x = y -> y = x.
  Proof.
    move=> x y exy.
    rewrite exy. (* x を y に書き換える *)
    done. (* 反射率で終わらせる *)
    Restart.
    by move=> x y ->. (* => の後ろなら -> で書き換えられる *)
  Qed.
  Lemma transitivity : forall x y z : T, x = y -> y = z -> x = z.
  Proof. by move => x y z ->. Qed.
End Eq.

Section Group.
  Variable G : Set.
  Variable e : G.
  Variable op : G -> G -> G.
  Notation "a * b" := (op a b). (* op を * と書けるようにする *)
  Variable inv : G -> G.
  Hypothesis associativity : forall a b c, (a * b) * c = a * (b * c).
  Hypothesis left_identity : forall a, e * a = a.
  Hypothesis right_identity : forall a, a * e = a.
  Hypothesis left_inverse : forall a, inv a * a = e.
  Hypothesis right_inverse : forall a, a * inv a = e.
  Lemma unit_unique : forall e', (forall a, a * e' = a) -> e' = e.
  Proof.
    move=> e' He'.
    rewrite -[RHS]He'. (* 右辺を書き換える *)
    rewrite (left_identity e'). (* 公理をの引数を指定する *)
    done.
  Qed.
  Lemma inv_unique : forall a b, a * b = e -> a = inv b.
  Proof.
    move=> a b abe.
    have : a * b * inv b = e * inv b.
      by rewrite abe.
    rewrite associativity right_inverse left_identity right_identity.
    done. (* 書き換えはまとめて書ける *)
  Qed.
  Lemma inv_involutive : forall a, inv (inv a) = a.
    move => a.
    have : inv (inv a) = inv (inv a) * (inv a * a).
      by rewrite left_inverse right_identity.
    move ->; by rewrite -associativity left_inverse left_identity.
  Qed.
End Group.

Section Coq3.
  Variable A : Set.
  Variable R : A -> A -> Prop.
  Variables P Q : A -> Prop.
  Theorem exists_postpone :
    (exists x, forall y, R x y) -> (forall y, exists x, R x y).
  Proof.
    move => [x r] y; by exists x.
  Qed.
  Theorem exists_mp : (forall x, P x -> Q x) -> ex P -> ex Q.
  Proof.
    move => pq [y p].
    by exists y; apply /pq.
  Qed.
  Theorem or_exists :
    (exists x, P x) \/ (exists x, Q x) -> exists x, P x \/ Q x.
  Proof.
    move => [[x p] | [x q]]; exists x; by [left | right].
  Qed.
  Hypothesis EM : forall P, P \/ ~ P. (* 残りは排中律を使う *)
  Variables InPub Drinker : A -> Prop.
  Theorem drinkers_paradox :
    (exists consumer, InPub consumer) -> (* パブには客がいる *)
    exists man, InPub man /\ (* 彼が飲むと全員が読むような客がいる *)
             (Drinker man -> forall other, InPub other -> Drinker other).
  Proof.
    move => [consumer consumer_in_pub].
    suff : (exists man, InPub man /\ ~Drinker man) \/ (forall other, InPub other -> Drinker other).
    move => [[man [in_pub not_drink]] | FH].
    - exists man. done.
    - exists consumer. done.
    - case: (EM (exists man, InPub man /\ ~Drinker man)); first by left.
      move => no_drinker.
      right.
      move => other other_in_pub.
      case: (EM (Drinker other)); first done.
      move => other_not_drink; elim no_drinker.
      exists other; done.
  Qed.
  Theorem remove_c : forall a,
    (forall x y, Q x -> Q y) ->
    (forall c, ((exists x, P x) -> P c) -> Q c) -> Q a.
  Proof.
    move => a qxy Hc.
    case: (EM (exists x, P x)) => [[x px] | contr].
    - apply /(qxy x).
      apply: Hc; done.
    - apply: Hc; done.
  Qed.
End Coq3.
