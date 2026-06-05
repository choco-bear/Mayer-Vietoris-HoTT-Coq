From HoTT Require Import HoTT Utf8.

Open Scope mc_add_scope.
Open Scope pointed_scope.

(** Cohomology *)
(** This module defines the cohomology groups of a space with coefficients in an abelian group. *)
Module Cohomology.
  Section Cohomology.
    Context {_Funext: Funext} {_Univalence: Univalence}.
    Context (X: Type) (G: AbGroup).

    Local Notation "⇑" := (pequiv_loops_em_em G).
    
    Definition _t (n: nat): Type := Trunc 0 (X → K(G,n)).

    Instance _is_hset (n: nat): IsHSet (_t n) := _.

    Instance _sg_op (n: nat): SgOp (_t n) :=
      Trunc_rec (λ f, Trunc_rec (λ g, tr (λ x, (⇑ n)⁻¹ (⇑ n (f x) • ⇑ n (g x))))).

    Instance _assoc (n: nat): Associative (_sg_op n).
    Proof.
      refine (Trunc_ind _ (λ f, Trunc_ind _ (λ g, Trunc_ind _ (λ h, ap tr (path_forall _ _ (λ x, ap _ _)))))).
      by rewrite !eisretr, concat_p_pp.
    Qed.

    Instance _is_sg (n: nat): IsSemiGroup (_t n) := Build_IsSemiGroup _ _ _ _.

    Instance _mon_unit (n: nat): MonUnit (_t n) := tr (λ x, pt).

    Program Instance _is_monoid (n: nat): IsMonoid (_t n) := Build_IsMonoid _ _ _ _ _ _.
    Next Obligation.
      refine (λ n, Trunc_ind _ (λ f, ap tr (path_forall _ _ (λ x, _)))).
      by rewrite point_eq, concat_1p, eissect.
    Qed.
    Next Obligation.
      refine (λ n, Trunc_ind _ (λ f, ap tr (path_forall _ _ (λ x, _)))).
      by rewrite point_eq, concat_p1, eissect.
    Qed.

    Instance _inv (n: nat): Inverse (_t n) :=
      Trunc_rec (λ f, tr (λ x, (⇑ n)⁻¹ ((⇑ n (f x))⁻¹)%path)).

    Program Instance _is_group (n: nat): IsGroup (_t n) := Build_IsGroup _ _ _ _ _ _ _.
    Next Obligation.
      refine (λ n, Trunc_ind _ (λ f, ap tr (path_forall _ _ (λ x, ap (⇑ n)⁻¹ _ • eissect _ _)))).
      by rewrite eisretr, concat_Vp, point_eq.
    Qed.
    Next Obligation.
      refine (λ n, Trunc_ind _ (λ f, ap tr (path_forall _ _ (λ x, ap (⇑ n)⁻¹ _ • eissect _ _)))).
      by rewrite eisretr, concat_pV, point_eq.
    Qed.

    Instance _comm (n: nat): Commutative (_sg_op n).
    Proof.
      refine (Trunc_ind _ (λ f, Trunc_ind _ (λ g, ap tr (path_forall _ _ (λ x, _))))).
      cut (∀ a b : pt = pt :> K(G, S n), a • b = b • a); eauto.
      intros a b. pose (peq := point_eq (⇑ n.+1)).

      assert (H_dist: ∀ (y: loops K(G, n.+2)) (p: ⇑ n.+1 pt = y) (X Y: ⇑ n.+1 pt = ⇑ n.+1 pt),
                          p⁻¹ • (X • Y) • p = (p⁻¹ • X • p) • (p⁻¹ • Y • p)).
      { intros. by rewrite !concat_p_pp, concat_pp_V. }

      assert (H_cancel: ∀ (y: loops K(G, n.+2)) (p: ⇑ n.+1 pt = y) (X Y: ⇑ n.+1 pt = ⇑ n.+1 pt),
                          p⁻¹ • X • p = p⁻¹ • Y • p → X = Y).
      { intros. cut (X0 • p = Y • p).
        { intro. pose proof (ap (λ t, t • p⁻¹) X2); simpl in *. by rewrite !concat_pp_V in X3. }
        rewrite !concat_pp_p in X1. pose proof (ap (concat p) X1). by rewrite !concat_p_Vp in X2.
      }

      cut (ap (⇑ n.+1) (a • b) = ap (⇑ n.+1) (b • a)); cycle 1.
      { rapply (H_cancel _ peq). rewrite !ap_pp, !H_dist. apply eckmann_hilton. }

      intro H. refine ((ap_idmap _)⁻¹ @ _ @ ap_idmap _).
      refine (transport (λ f, ap f (a • b) = ap f (b • a)) (path_forall _ _ (eissect (⇑ n.+1))) _).
      refine (ap_compose (⇑ n.+1) (⇑ n.+1)⁻¹ _ • ap _ H • (ap_compose (⇑ n.+1) (⇑ n.+1)⁻¹ _)⁻¹).
    Qed.

    Program Instance _is_ab_group (n: nat): IsAbGroup (_t n) := Build_IsAbGroup _ _ _ _ _ _.
  End Cohomology.

  Definition pullback {X Y: Type} (f: Y → X) (G: AbGroup) (n: nat): _t X G n → _t Y G n :=
    Trunc_rec (λ hx, tr (λ y, hx (f y))).
End Cohomology.

Definition add_pt (X: Type): pType := Build_pType (X + Unit) (inr tt).

Definition unpointed_equiv_pointed {_Funext: Funext} {X: Type} {Y: pType} {_HSpace: IsHSpace Y}:
  (X → Y) ≃ (add_pt X ->* Y).
Proof.
  srapply equiv_adjointify.
  - exact (λ f, Build_pMap _ _ (sum_rec _ f (λ _, pt)) 1).
  - exact (λ g x, g (inl x)).
  - refine (λ g, hspace_path_pforall_from_path_arrow (path_forall _ _ _)).
    exact (sum_ind _ (λ x, 1) (Unit_ind ((dpoint_eq _)⁻¹)%path)).
  - exact (λ f, path_forall _ f (λ x, 1)).
Qed.