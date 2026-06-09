From HoTT Require Import HoTT Utf8.

Require Import Basics.
Require Import Cohomology.

Section MVSequence.
  Context {_Funext: Funext} {_Univalence: Univalence}.
  Context {C A B: Type} (f: C → A) (g: C → B).

  Definition X := Pushout f g.

  Context [G: AbGroup] (n: nat).

  Local Notation "⇑" := (pequiv_loops_em_em G).

  Definition mv_res_map: H n X G → (H n A G) ⊕ (H n B G) :=
    Trunc_rec (λ u, (tr (u ∘ pushl), tr (u ∘ pushr))).

  Instance mv_res_preserves_op: IsSemiGroupPreserving mv_res_map :=
    Trunc_ind _ (λ u, Trunc_ind _ (λ v, path_prod _ _ 1 1)).

  Definition mv_res: H n X G $-> (H n A G) ⊕ (H n B G) := Build_GroupHomomorphism mv_res_map _.

  Definition mv_diff_map: (H n A G) ⊕ (H n B G) → H n C G :=
    prod_rect _ _ _ (Trunc_rec (λ u, Trunc_rec(
      λ v, tr (λ c, (⇑ n)⁻¹ (⇑ n (u (f c)) • (⇑ n (v (g c)))⁻¹))
    ))).

  Instance mv_diff_preserves_op: IsSemiGroupPreserving mv_diff_map.
  Proof.
    refine (prod_ind _ (Trunc_ind _ (λ xu, Trunc_ind _ (λ xv, _)))).
    refine (prod_ind _ (Trunc_ind _ (λ yu, Trunc_ind _ (λ yv, _)))).
    refine (ap tr (path_forall _ _ (λ c, ap (⇑ n)⁻¹ _))).
    rewrite !eisretr, inv_pp.
    apply em_loop_shuffle.
  Defined.

  Definition mv_diff: (H n A G) ⊕ (H n B G) $-> H n C G := Build_GroupHomomorphism mv_diff_map _.

  Definition mv_delta: H n C G $-> H (S n) X G := pushout_to_suspension ∗ $o δ.
End MVSequence.
