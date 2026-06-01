From HoTT Require Import HoTT Utf8.

Open Scope mc_add_scope.
Open Scope pointed_scope.

Module Cohomology.
  Section Cohomology.
    Context `{Funext} `{Univalence}.
    Context (X: Type) (G: AbGroup).
    
    Definition _t (n: nat): Type := Trunc 0 (X → K(G,n)).

    Instance _is_hset (n: nat): IsHSet (_t n) := _.

    Instance _sg_op (n: nat): SgOp (_t n).
    Proof.
      refine (Trunc_rec (λ f, Trunc_rec (λ g, tr (λ x, _ (f x) (g x))))).
      clear f g x. intros x y.
      destruct (pequiv_loops_em_em G n) as [[e ?] [inv ? ? ?]]; simpl in *.
      exact (inv ((e x) @ (e y))).
    Defined.

    Instance _assoc (n: nat): Associative (_sg_op n).
    Proof.
      refine (Trunc_ind _ (λ f, Trunc_ind _ (λ g, Trunc_ind _ (λ h, _)))); simpl.
      refine (ap tr (path_forall _ _ (λ x, _))).
      destruct (pequiv_loops_em_em G n) as [[e ?] [inv ? ? ?]]; simpl in *.
      refine (ap inv _). rewrite !eisretr. apply concat_p_pp.
    Qed.

    Instance _is_sg (n: nat): IsSemiGroup (_t n) := Build_IsSemiGroup _ _ _ _.

    Instance _mon_unit (n: nat): MonUnit (_t n) := tr (λ x, pt).

    Program Instance _is_monoid (n: nat): IsMonoid (_t n) := Build_IsMonoid _ _ _ _ _ _.
    Next Obligation.
      refine (λ n, Trunc_ind _ (λ f, _)); unfold sg_op, mon_unit; simpl.
      refine (ap tr (path_forall _ _ (λ x, _))).
      destruct (pequiv_loops_em_em G n) as [[e ?] [inv ? ? ?]]; simpl in *.
      by rewrite dpoint_eq, concat_1p, eissect.
    Qed.
    Next Obligation.
      refine (λ n, Trunc_ind _ (λ f, _)); unfold sg_op, mon_unit; simpl.
      refine (ap tr (path_forall _ _ (λ x, _))).
      destruct (pequiv_loops_em_em G n) as [[e ?] [inv ? ? ?]]; simpl in *.
      by rewrite dpoint_eq, concat_p1, eissect.
    Qed.

    Instance _inv (n: nat): Inverse (_t n).
    Proof.
      refine (Trunc_rec (λ f, tr (λ x, _))).
      destruct (pequiv_loops_em_em G n) as [[e ?] [inv ? ? ?]]; simpl in *.
      refine (inv ((e (f x))⁻¹)%path).
    Defined.

    Program Instance is_group (n: nat): IsGroup (_t n) := Build_IsGroup _ _ _ _ _ _ _.
    Next Obligation.
      refine (λ n, Trunc_ind _ (λ f, _)); unfold _sg_op, _inv, _mon_unit; simpl.
      refine (ap tr (path_forall _ _ (λ x, _))).
      destruct (pequiv_loops_em_em G n) as [[e ?] [inv ? ? ?]]; simpl in *.
      refine (ap inv _ @ ap inv (dpoint_eq)⁻¹ @ (eissect pt)).
      by rewrite eisretr, concat_Vp.
    Qed.
    Next Obligation.
      refine (λ n, Trunc_ind _ (λ f, _)); unfold _sg_op, _inv, _mon_unit; simpl.
      refine (ap tr (path_forall _ _ (λ x, _))).
      destruct (pequiv_loops_em_em G n) as [[e ?] [inv ? ? ?]]; simpl in *.
      refine (ap inv _ @ ap inv (dpoint_eq)⁻¹ @ (eissect pt)).
      by rewrite eisretr, concat_pV.
    Qed.

    Instance _comm (n: nat): Commutative (_sg_op n).
    Proof.
      refine (Trunc_ind _ (λ f, Trunc_ind _ (λ g, _))); unfold _sg_op; simpl.
      refine (ap tr (path_forall _ _ (λ x, _))).
      destruct (pequiv_loops_em_em G n) as [[e ?] [inv ? ? ?]]; simpl in *.
      (* TODO: Prove commutativity *)
    Admitted.

    Program Instance is_ab_group (n: nat): IsAbGroup (_t n) := Build_IsAbGroup _ _ _ _ _ _.
  End Cohomology.

  Definition pullback {X Y: Type} (f: Y → X) (G: AbGroup) (n: nat): _t X G n → _t Y G n :=
    Trunc_functor 0 (λ (hx : X → K(G,n)), hx o f).
End Cohomology.