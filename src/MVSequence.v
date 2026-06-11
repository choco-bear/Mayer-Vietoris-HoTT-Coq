From HoTT Require Import HoTT Utf8.

Require Import Basics.
Require Import Cohomology.

Set Implicit Arguments.

Section MVSequence.
  Context {_Funext: Funext} {_Univalence: Univalence}.
  Context {C A B: Type} (f: C → A) (g: C → B).

  Local Notation X := (Pushout f g).

  Context [G: AbGroup] (n: nat).

  Local Notation "⇑" := (pequiv_loops_em_em G).

  Section Restriction.
    Definition mv_res_map: H n X G → (H n A G) ⊕ (H n B G) :=
      Trunc_rec (λ u, (tr (u ∘ pushl), tr (u ∘ pushr))).

    Instance mv_res_preserves_op: IsSemiGroupPreserving mv_res_map :=
      Trunc_ind _ (λ u, Trunc_ind _ (λ v, path_prod _ _ 1 1)).

    Definition mv_res: H n X G $-> (H n A G) ⊕ (H n B G) := Build_GroupHomomorphism mv_res_map _.
  End Restriction.

  Section Difference.
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
  End Difference.

  Definition mv_delta_fun (u: C → K(G,n)): X → K(G,S n) :=
    Susp_rec pt pt (⇑ n ∘ u) ∘ pushout_to_suspension.

  Lemma mv_delta_fun_beta_pglue (u: C → K(G,n)) (c: C):
    ap (mv_delta_fun u) (pglue c) = ⇑ n (u c).
  Proof.
    unfold mv_delta_fun, pushout_to_suspension.
    rewrite ap_compose.
    rewrite Pushout_rec_beta_pglue.
    exact (Susp_rec_beta_merid (H_merid:=⇑ n ∘ u) c).
  Defined.

  Definition mv_delta: H n C G $-> H (S n) X G := pushout_to_suspension ∗ $o δ.
End MVSequence.

Section MVSequence_.
  Context {_Funext: Funext} {_Univalence: Univalence}.
  Context {C A B: Type} (f: C → A) (g: C → B).
  Context (G: AbGroup) (n: nat).

  Definition mv_res' := @mv_res _ _ _ _ _ f g G n.
  Definition mv_diff' := @mv_diff _ _ _ _ _ f g G n.
  Definition mv_delta' := @mv_delta _ _ _ _ _ f g G n.
End MVSequence_.