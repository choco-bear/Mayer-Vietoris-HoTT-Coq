From HoTT Require Import HoTT Utf8.

Require Import Basics.
Require Import Cohomology.
Require Import MVSequence.

Set Implicit Arguments.

Section MVExactness.
  Context {_Funext: Funext} {_Univalence: Univalence}.
  Context {C A B: Type} (f: C → A) (g: C → B).
  Context [G: AbGroup] (n: nat).

  Local Notation "⇑" := (pequiv_loops_em_em G).

  Definition IsComplex {F X Y: pType} := @ExactSequence.IsComplex F X Y.

  Definition IsExact {F X Y: pType} := @ExactSequence.IsExact (Tr (-1)) F X Y.

  Definition mv_complex_res_diff: IsComplex (mv_res' f g G n) (mv_diff' f g G n).
  Proof.
    srapply phomotopy_homotopy_hset.
    refine (Trunc_ind _ (λ u, _)).
    cbn. unfold Cohomology._mon_unit.
    refine (ap tr (path_forall _ _ (λ c, _))).
    refine (equiv_inj (⇑ n) _).
    rewrite eisretr, point_eq.
    refine (ap (λ x, concat x _) _ • concat_pV (⇑ n (u (pushr (g c))))).
    exact (ap _ (ap _ (pglue c))).
  Defined.

  Lemma mv_complex_diff_delta: ExactSequence.IsComplex (mv_diff' f g G n) (mv_delta' f g G n).
  Proof.
    srapply phomotopy_homotopy_hset.
    refine (prod_rect _ _ _ (Trunc_ind _ (λ u, Trunc_ind _ (λ v, _)))).
    cbn. unfold Cohomology._mon_unit.
    refine (ap tr (path_forall _ _ (Pushout_ind_FlFr _ _ (⇑ n ∘ u) (⇑ n ∘ v) (λ c, _)))).
    refine (ap (λ x, concat x _) (mv_delta_fun_beta_pglue f g n _ c) • _).
    refine (ap (λ x, concat x _) (eisretr (⇑ n) _) • _).
    refine (_ • (concat_p1 _)⁻¹ • ap (concat _) (ap_const _ _)⁻¹).
    refine (concat_pV_p _ _ • 1).
  Defined.

  Lemma mv_complex_delta_res: ExactSequence.IsComplex (mv_delta' f g G n) (mv_res' f g G (S n)).
  Proof.
    srapply phomotopy_homotopy_hset.
    exact (Trunc_ind _ (λ u, 1)).
  Defined.

  Theorem mv_exact_res_diff: IsExact (mv_res' f g G n) (mv_diff' f g G n).
  Proof.
    snrapply ExactSequence.Build_IsExact.
    { exact mv_complex_res_diff. }
    intros [[x y] q]. revert x y q.
    refine (Trunc_ind _ (λ u, Trunc_ind _ (λ v q, _))).
    cbn in q. unfold Cohomology._mon_unit in q.
    pose proof (hq := (equiv_path_Tr (λ c : C,  (⇑ n)⁻¹ (⇑ n (u (f c)) • (⇑ n (v (g c)))⁻¹)) (λ _ : C, pt))⁻¹ q).
    strip_truncations. apply ap10 in hq.
    pose (w := Pushout_rec (K(G,n)) u v (λ c, em_diff_eq_pt n (u (f c)) (v (g c)) (hq c))).
    rapply contr_inhabited_hprop. apply tr.
    exists (tr w). apply path_sigma_hprop.
    exact (path_prod _ _ 1 1).
  Defined.

  Theorem mv_exact_diff_delta: IsExact (mv_diff' f g G n) (mv_delta' f g G n).
  Proof.
    snrapply ExactSequence.Build_IsExact.
    { exact mv_complex_diff_delta. }
    intros [x q]. revert x q.
    refine (Trunc_ind _ (λ u q, _)).
    cbn in q. unfold Cohomology._mon_unit in q.
    pose proof (hq := (equiv_path_Tr (mv_delta_fun n u) (λ _ : Pushout f g, pt))⁻¹ q).
    strip_truncations. apply ap10 in hq.
    pose (a := λ x : A, (pequiv_loops_em_em G n)⁻¹ (hq (pushl x))).
    pose (b := λ y : B, (pequiv_loops_em_em G n)⁻¹ (hq (pushr y))).
    rapply contr_inhabited_hprop. apply tr.
    exists (tr a, tr b). apply path_sigma_hprop. cbn.
    refine (ap tr (path_forall _ _ (λ c, equiv_inj (⇑ n) _))).
    rewrite !eisretr.
    pose proof (concat_Ap hq (pglue c)) as Hnat.
    rewrite mv_delta_fun_beta_pglue in Hnat.
    rewrite ap_const, concat_p1 in Hnat.
    exact (ap (λ x, concat x _) Hnat⁻¹ • concat_pp_V _ _).
  Defined.

  Theorem mv_exact_delta_res: IsExact (mv_delta' f g G n) (mv_res' f g G (S n)).
  Proof.
    snrapply ExactSequence.Build_IsExact.
    { exact mv_complex_delta_res. }
    intros [x q]. revert x q.
    refine (Trunc_ind _ (λ u q, _)).
    cbn in q. unfold Cohomology._mon_unit in q.
    pose proof (ql := ap fst q).
    pose proof (qr := ap snd q).
    cbn in ql, qr.
    pose proof (hl := (equiv_path_Tr (λ x : A, u (pushl x)) (λ _ : A, pt))⁻¹ ql).
    pose proof (hr := (equiv_path_Tr (λ x : B, u (pushr x)) (λ _ : B, pt))⁻¹ qr).
    strip_truncations. apply ap10 in hl. apply ap10 in hr.
    pose (w := λ c : C, (⇑ n)⁻¹ ((hl (f c))^ • ap u (pglue c) • hr (g c))).
    rapply contr_inhabited_hprop. apply tr.
    exists (tr w). apply path_sigma_hprop. cbn.
    refine (ap tr (path_forall _ _ (Pushout_ind_FlFr _ _
      (λ a, (hl a)^) (λ b, (hr b)^) (λ c, _)))).
    rewrite mv_delta_fun_beta_pglue, eisretr.
    rewrite concat_pp_p, concat_pV, concat_p1.
    reflexivity.
  Defined.
End MVExactness.