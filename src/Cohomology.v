From HoTT Require Import HoTT Utf8.

Require Import Basics.

Set Implicit Arguments.

(** Cohomology *)
(** This module defines the cohomology groups of a space with coefficients in an abelian group. *)
Module Cohomology.
  Section Cohomology.
    Context {_Funext: Funext} {_Univalence: Univalence}.
    Context (n: nat) (X: Type) (G: AbGroup).

    Local Notation "⇑" := (pequiv_loops_em_em G).
    
    Definition _t: Type := Trunc 0 (X → K(G,n)).

    Instance _is_hset: IsHSet _t := _.

    Instance _sg_op: SgOp _t :=
      Trunc_rec (λ f, Trunc_rec (λ g, tr (λ x, (⇑ n)⁻¹ (⇑ n (f x) • ⇑ n (g x))))).

    Instance _assoc: Associative _sg_op.
    Proof.
      refine (Trunc_ind _ (λ f, Trunc_ind _ (λ g, Trunc_ind _ (λ h, ap tr (path_forall _ _ (λ x, ap _ _)))))).
      by rewrite !eisretr, concat_p_pp.
    Qed.

    Instance _is_sg: IsSemiGroup _t := Build_IsSemiGroup _ _ _ _.

    Instance _mon_unit: MonUnit _t := tr (λ x, pt).

    Program Instance _is_monoid: IsMonoid _t := Build_IsMonoid _ _ _ _ _ _.
    Next Obligation.
      refine (Trunc_ind _ (λ f, ap tr (path_forall _ _ (λ x, _)))).
      by rewrite point_eq, concat_1p, eissect.
    Qed.
    Next Obligation.
      refine (Trunc_ind _ (λ f, ap tr (path_forall _ _ (λ x, _)))).
      by rewrite point_eq, concat_p1, eissect.
    Qed.

    Instance _inv: Inverse _t :=
      Trunc_rec (λ f, tr (λ x, (⇑ n)⁻¹ ((⇑ n (f x))⁻¹)%path)).

    Program Instance _is_group: IsGroup _t := Build_IsGroup _ _ _ _ _ _ _.
    Next Obligation.
      refine (Trunc_ind _ (λ f, ap tr (path_forall _ _ (λ x, ap (⇑ n)⁻¹ _ • eissect _ _)))).
      by rewrite eisretr, concat_Vp, point_eq.
    Qed.
    Next Obligation.
      refine (Trunc_ind _ (λ f, ap tr (path_forall _ _ (λ x, ap (⇑ n)⁻¹ _ • eissect _ _)))).
      by rewrite eisretr, concat_pV, point_eq.
    Qed.

    Definition _grp: Group := Build_Group _t _sg_op _ _ _.
    
    Instance _comm: Commutative _sg_op.
    Proof.
      refine (Trunc_ind _ (λ f, Trunc_ind _ (λ g, ap tr (path_forall _ _ (λ x, _))))).
      by rewrite em_loop_comm.
    Qed.

    Program Instance _is_ab_group: IsAbGroup _t := Build_IsAbGroup _ _ _ _ _ _.

    Definition _ab_grp: AbGroup := Build_AbGroup _grp _.

    Definition H := _ab_grp.
  End Cohomology.

  Section Suspension.
    Context {_Funext: Funext} {_Univalence: Univalence}.
    Context [X: Type] [G: AbGroup] (n: nat).

    Local Notation "⇑" := (pequiv_loops_em_em G).

    Definition coboundary_susp_map: H n X G → H n.+1%nat (Σ X) G :=
      Trunc_rec (λ u, tr (Susp_rec pt pt (⇑ n ∘ u))).

    Lemma coboundary_susp_preserves_op: IsSemiGroupPreserving coboundary_susp_map.
    Proof.
      refine (Trunc_ind _ (λ u, Trunc_ind _ (λ v, ap tr (path_forall _ _ _)))).
      unshelve simple refine (Susp_ind_FlFr _ _ (em_add_pt_pt n.+1) (em_add_pt_pt n.+1) (λ x, _)).
      rewrite Susp_rec_beta_merid.
      rewrite pequiv_loops_em_em_preserves_add.
      refine (_ @ (ap (concat (em_add_pt_pt n.+1)) (ap011_diag (em_add n.+1)
        (Susp_rec pt pt (⇑ n ∘ u))
        (Susp_rec pt pt (⇑ n ∘ v)) (merid x)))^).
      rewrite !Susp_rec_beta_merid.
      snrapply em_add_loop.
    Qed.
      
    Definition coboundary_susp: H n X G $-> H n.+1%nat (Σ X) G :=
      Build_GroupHomomorphism coboundary_susp_map coboundary_susp_preserves_op.
  End Suspension.

  Section Pullback.
    Context {_Funext: Funext} {_Univalence: Univalence}.

    Definition pullback_map X Y (f: Y → X) G n: H n X G → H n Y G := Trunc_rec (λ u, tr (u ∘ f)).

    Lemma pullback_preserves_op
          X Y (f: Y → X) G n:
      IsSemiGroupPreserving (@pullback_map X Y f G n).
    Proof.
      by refine (Trunc_ind _ (λ u, Trunc_ind _ (λ v, _))).
    Qed.

    Definition pullback X Y (f: Y → X) G n: H n X G $-> H n Y G :=
      Build_GroupHomomorphism (@pullback_map X Y f G n) (@pullback_preserves_op X Y f G n).
  End Pullback.
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

Notation H := Cohomology.H.
Notation "f ∗" := (Cohomology.pullback f _ _) (at level 8, left associativity, format "f ∗").
Notation δ := (Cohomology.coboundary_susp _).
Notation "δ@{ n }" := (Cohomology.coboundary_susp n) (at level 8, left associativity, only parsing).