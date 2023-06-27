From mathcomp Require Import all_ssreflect all_algebra. (* 代数ライブラリ *)
Local Open Scope ring_scope. (* 環構造を使う *)
Import GRing.Theory.
Section Problem1.
  Variable K : fieldType. (* 体 *)
  Variable E : vectType K. (* 有限次元ベクトル空間 *)
  Variable f : 'End(E). (* 線形変換 *)
  Theorem equiv1 : (limg f + lker f)%VS = fullv <-> limg f = limg (f \o f).
  Proof.
    split.
    - move/(f_equal (lfun_img f)).
      rewrite limgD limg_comp.
      have /eqP->: (f @: lker f == 0)%VS by rewrite -lkerE.
      by rewrite addv0 => ->.
    - rewrite limg_comp => Hf'.
      move: (limg_ker_dim f (limg f)).
      rewrite -[RHS]add0n -Hf' => /eqP.
      rewrite eqn_add2r dimv_eq0 => /eqP /dimv_disjoint_sum Hdim.
      apply/eqP. rewrite eqEdim.
      rewrite Hdim. rewrite subvf => /=.
      rewrite -(limg_ker_dim f fullv).
      by rewrite capfv addnC.
  Qed.
End Problem1.
Section Problem2.
  Variable K : numFieldType. (* ノルム付き体 *)
  Variable E : vectType K.
  Variable p q : 'End(E).
  Definition projection (f : 'End(E)) := forall x, f (f x) = f x.
  Lemma proj_idE f : projection f <-> {in limg f, f =1 id}.
  Proof.
    split => Hf x.
    - by move/limg_lfunVK => <-.
    - by rewrite Hf // memv_img ?memvf.
  Qed.
  Hypothesis proj_p : projection p.
  Hypothesis proj_q : projection q.
  Section a.
    Lemma f_g_0 f g x :
      projection f -> projection g -> projection (f+g) -> f (g x) = 0.
    Proof.
      move=> Pf Pg /(_ (g x)).
      rewrite !add_lfunE !linearD /=.
      rewrite !Pf !Pg => /eqP.
      rewrite -subr_eq !addrA addrK.
      rewrite addrAC eq_sym -subr_eq eq_sym subrr => /eqP Hfg.
      move: (f_equal g Hfg).
      rewrite !linearD /= Pg linear0 => /eqP.
      rewrite -mulr2n -scaler_nat scaler_eq0 Num.Theory.pnatr_eq0 /=.
      move: Hfg => /[swap] /eqP ->.
      by rewrite addr0.
    Qed.
    Theorem equiv2 : projection (p + q) <-> (forall x, p (q x) = 0 /\ q (p x) = 0).
    Proof.
      split=> H x.
        by rewrite !f_g_0 // addrC.
        rewrite !add_lfunE !linearD /=.
        by rewrite !(proj1 (H x)) !(proj2 (H x)) addr0 add0r proj_p proj_q.
    Qed.
  End a.
  Section b.
    Hypothesis proj_pq : projection (p + q).
    Lemma b1a x : x \in limg p -> x \in limg q -> x = 0.
    Proof.
      move => Pp Pq.
      have <- : p (q x) = x.
        rewrite (proj1 (proj_idE q)) //.
        rewrite (proj1 (proj_idE p)) //.
      by rewrite f_g_0.
    Qed.
    Lemma b1b : directv (limg p + limg q).
    Proof.
      apply/directv_addP/eqP.
      rewrite -subv0.
      apply/subvP => u /memv_capP [Hp Hq].
      rewrite memv0.
      by rewrite (b1a u) //.
    Qed.
    Lemma limg_sub_lker f g :
      projection f -> projection g -> projection (f+g) -> (limg f <= lker g)%VS.
    Proof.
      move => Pf Pg Pfg.
      apply/subvP => u.
      move => ImgF.
      have : g (f u) = 0 by rewrite f_g_0 // addrC //.
      rewrite (proj1 (proj_idE f)) //.
      move/eqP.
      by rewrite -memv_ker.
    Qed.
    Lemma b1c : (limg p <= lker q)%VS.
    Proof.
      apply: limg_sub_lker => //.
    Qed.
    Lemma b1c' : (limg q <= lker p)%VS.
    Proof.
      apply: limg_sub_lker => //.
      by rewrite addrC.
    Qed.
    Lemma limg_addv (f g : 'End(E)) : (limg (f + g)%R <= limg f + limg g)%VS.
    Proof.
      apply/subvP => x /memv_imgP [u _ ->].
      by rewrite add_lfunE memv_add // memv_img // memvf.
    Qed.
    Theorem b1 : limg (p+q) = (limg p + limg q)%VS.
    Proof.
      apply/eqP; rewrite eqEsubv limg_addv /=.
      apply/subvP => x /memv_addP [u Hu] [v Hv ->].
      have -> : u + v = (p + q) (u + v).
      rewrite lfun_simp !linearD /=.
      rewrite (proj1 (proj_idE p)) // (proj1 (proj_idE q) _ v) //.
      apply (subvP b1c) in Hu.
      apply (subvP b1c') in Hv.
      move: Hu Hv.
      rewrite !memv_ker.
      move/eqP->.
      move/eqP->.
      by rewrite addr0 add0r.
      by rewrite memv_img // memvf.
    Qed.
    Theorem b2 : lker (p+q) = (lker p :&: lker q)%VS.
    Proof.
      apply/vspaceP => x.
      rewrite memv_cap !memv_ker add_lfunE.
      case Hpx: (p x == 0).
      move/eqP: Hpx => ->.
      by rewrite add0r.
      apply/eqP => /=.
      move=> /(f_equal p).
      rewrite linearD /= proj_p f_g_0 // addr0 linear0.
      move/eqP.
      by rewrite Hpx.
    Qed.
  End b.
End Problem2.
