Require Import ssreflect.
Module MyNat. (* nat を新しく定義する *)
  Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.
  Fail Fixpoint plus (m n : nat) {struct m} : nat := (* 帰納法の対象を明示する *)
    match m with (* 減らないとエラーになる *)
    | O => n
    | S m' => S (plus m n)
    end.
  Fixpoint plus (m n : nat) {struct m} : nat := (* 同じ型の引数をまとめる *)
    match m with
    | O => n
    | S m' => S (plus m' n) (* 正しい定義 *)
    end.
  Print plus.
  Check plus (S (S O)) (S O). (* 式の型を調べる *)
  Eval compute in plus (S (S O)) (S O). (* 式を評価する *)
  Fixpoint mult (m n : nat) {struct m} : nat :=
    match m with
    | O => O
    | S m' => plus (mult m' n) n
    end.
  Eval compute in mult (S (S O)) (S O).
End MyNat.

Lemma plusnS m n : m + S n = S (m + n). (* m, n は仮定 *)
Proof.
  elim: m => /=. (* nat_ind を使う *)
  - done. (* O の場合 *)
  - move => m IH. (* S の場合 *)
    by rewrite IH. (* 帰納法の仮定で書き換える *)
    Restart.
    elim: m => /= [|m ->] //. (* 一行にまとめた *)
Qed.
Check plusnS. (* ∀ m n : nat, m + S n = S (m + n) *)
Lemma plusSn m n : S m + n = S (m + n).
Proof. rewrite /=. done. Show Proof. Qed. (* 簡約できるので帰納法は不要 *)
Lemma plusn0 n : n + 0 = n.
Proof. by elim: n. Qed.
Lemma plusC m n : m + n = n + m.
Proof. elim: m => /= [|m ->] //. Qed.
Lemma plusA m n p : m + (n + p) = (m + n) + p.
Proof. elim: m => /= [|m ->] //. Qed.
Lemma multnS m n : m * S n = m + m * n.
Proof.
  elim: m => /= [|m ->] //.
  by rewrite !plusA [n + m]plusC.
Qed.

Lemma multn0 n : n * 0 = 0.
Proof. elim: n => //=. Qed.
Lemma multC m n : m * n = n * m.
Proof. elim: m => [|m] //= ->. by rewrite multnS. Qed.
Lemma multnDr m n p : (m + n) * p = m * p + n * p.
Proof.
  elim: p => [|p] //=.
    by rewrite !multn0.
  rewrite !multnS => ->.
  rewrite -!plusA.
  apply: f_equal2_plus => //.
  rewrite plusC.
  rewrite -!plusA.
  apply: f_equal2_plus => //.
  by rewrite plusC.
Qed.

Lemma multA m n p : m * (n * p) = (m * n) * p.
Proof.
  elim: m => [|m /= ->] //.
  by rewrite multnDr.
Qed.
Fixpoint sum n := if n is S m then n + sum m else 0.
Print sum. (* if .. is は match .. with に展開される *)
Lemma double_sum n : 2 * sum n = n * (n + 1).
Proof.
  elim: n => [|n] //=.
  rewrite !plusn0.
  rewrite multnS => <- /=.
  apply: eq_S.
  rewrite -!plusA.
  apply: f_equal2_plus => //=.
  rewrite plusC.
  rewrite plusSn.
  apply: eq_S.
  by rewrite plusA.
Qed.

Lemma square_eq a b : (a + b) * (a + b) = a * a + 2 * a * b + b * b.
Proof.
  rewrite !multnDr.
  repeat rewrite multC multnDr; simpl.
  rewrite plusn0.
  rewrite -!plusA.
  apply: f_equal2_plus => //.
  rewrite [b * (a + b)]multC multnDr.
  by rewrite multC.
Qed. (* 帰納法なしで証明できる *)
