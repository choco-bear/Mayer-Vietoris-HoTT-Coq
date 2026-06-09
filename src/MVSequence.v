From HoTT Require Import HoTT Utf8.

Require Import Basics.
Require Import Cohomology.

Section MVSequence.
  Context {_Funext: Funext} {_Univalence: Univalence}.
  Context {C A B : Type} (f : C → A) (g : C → B).

  Definition X := Pushout f g.

  Context (G : AbGroup) {n : nat}.

  Local Notation "⇑" := (pequiv_loops_em_em G).

  Definition mv_res_map: H n X G → (H n A G) ⊕ (H n B G) :=
    Trunc_rec (λ u, (tr (u ∘ pushl), tr (u ∘ pushr))).

  Definition mv_diff_map: (H n A G) ⊕ (H n B G) → H n C G :=
    prod_rect _ _ _ (Trunc_rec (λ u, Trunc_rec(
      λ v, tr (λ c, (⇑ n)⁻¹ (⇑ n (u (f c)) • (⇑ n (v (g c)))⁻¹))
    ))).

  Definition mv_delta_map: H n C G → H (S n) X G.
  Proof. (* TODO *) Admitted.

  Definition mv_res: H n X G $-> (H n A G) ⊕ (H n B G).
  Proof.
    refine (Build_GroupHomomorphism mv_res_map _).
    refine (Trunc_ind _ (λ u, Trunc_ind _ (λ v, path_prod _ _ 1 1))).
  Qed.

  Definition mv_diff: (H n A G) ⊕ (H n B G) $-> H n C G.
  Proof.
    refine (Build_GroupHomomorphism mv_diff_map _).
    refine (prod_ind _ (Trunc_ind _ (λ xu, Trunc_ind _ (λ xv, _)))).
    refine (prod_ind _ (Trunc_ind _ (λ yu, Trunc_ind _ (λ yv, _)))).
    refine (ap tr (path_forall _ _ (λ c, ap (⇑ n)^-1 _))).
    rewrite !eisretr, inv_pp.
    apply em_loop_shuffle.
  Qed.

  Definition mv_delta: H n C G $-> H (S n) X G.
  Proof.
    refine (Build_GroupHomomorphism mv_delta_map _).
    refine (Trunc_ind _ (λ u, Trunc_ind _ (λ v, _))).
    (* TODO *) admit.
  Admitted.
End MVSequence.
