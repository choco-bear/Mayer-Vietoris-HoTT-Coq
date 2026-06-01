From HoTT Require Import HoTT Utf8.

Open Scope mc_add_scope.
Open Scope pointed_scope.

Module Cohomology.
  Section Cohomology.
    Context `{Funext} `{Univalence}.
    Context (X: Type) (G: AbGroup).
    
    Definition _t (n: nat): Type := Trunc 0 (X → K(G,n)).

    Instance _is_hset (n: nat): IsHSet (_t n) := _.

    Instance _sg_op (n: nat): SgOp (_t n) :=
      Trunc_rec (λ f, Trunc_rec (λ g, tr (λ x, f x + g x))).

    Instance _assoc (n: nat): Associative (_sg_op n).
    Proof.
      refine (Trunc_ind _ (λ f, Trunc_ind _ (λ g, Trunc_ind _ (λ h, _)))).
      unfold _sg_op. simpl. rapply ap.
    Admitted.

    Instance _is_sg (n: nat): IsSemiGroup (_t n) := Build_IsSemiGroup _ _ _ _.

    Instance _mon_unit (n: nat): MonUnit (_t n) := tr (λ x, pt).

    Program Instance _is_monoid (n: nat): IsMonoid (_t n) := Build_IsMonoid _ _ _ _ _ _.
    Next Obligation. Admitted.
    Next Obligation. Admitted.

    Instance inverse (n: nat): Inverse (_t n).
    Proof. Admitted.

    Program Instance is_group (n: nat): IsGroup (_t n) := Build_IsGroup _ _ _ _ _ _ _.
    Next Obligation. Admitted.
    Next Obligation. Admitted.

    Program Instance is_ab_group (n: nat): IsAbGroup (_t n) := Build_IsAbGroup _ _ _ _ _ _.
    Next Obligation. Admitted.
  End Cohomology.

  Definition pullback {X Y: Type} (f: Y → X) (G: AbGroup) (n: nat): _t X G n → _t Y G n :=
    Trunc_functor 0 (λ (hx : X → K(G,n)), hx o f).
End Cohomology.