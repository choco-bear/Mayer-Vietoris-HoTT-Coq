From HoTT Require Import HoTT Utf8.

Open Scope mc_add_scope.
Open Scope pointed_scope.

Notation "A ⊕ B" := (ab_biprod A B) (at level 50, left associativity).

Section BasicLemmas.
  Context {_Funext: Funext} {_Univalence: Univalence}.
  Context {G : AbGroup} {n : nat}.

  Local Notation "⇑" := (pequiv_loops_em_em G).

  Lemma em_loop_comm (a b : pt = pt :> K(G, S n)) : a • b = b • a.
  Proof.
    pose (peq := point_eq (⇑ n.+1)).

    assert (H_dist: ∀ (y: loops K(G, n.+2)) (p: ⇑ n.+1 pt = y) (X Y: ⇑ n.+1 pt = ⇑ n.+1 pt),
                        p⁻¹ • (X • Y) • p = (p⁻¹ • X • p) • (p⁻¹ • Y • p)).
    { intros. by rewrite !concat_p_pp, concat_pp_V. }

    assert (H_cancel: ∀ (y: loops K(G, n.+2)) (p: ⇑ n.+1 pt = y) (X Y: ⇑ n.+1 pt = ⇑ n.+1 pt),
                        p⁻¹ • X • p = p⁻¹ • Y • p → X = Y).
    { intros. cut (X • p = Y • p).
      { intro. pose proof (ap (λ t, t • p⁻¹) X1); simpl in *. by rewrite !concat_pp_V in X2. }
      rewrite !concat_pp_p in X0. pose proof (ap (concat p) X0). by rewrite !concat_p_Vp in X1.
    }

    cut (ap (⇑ n.+1) (a • b) = ap (⇑ n.+1) (b • a)); cycle 1.
    { rapply (H_cancel _ peq). rewrite !ap_pp, !H_dist. apply eckmann_hilton. }

    intro H. refine ((ap_idmap _)⁻¹ @ _ @ ap_idmap _).
    refine (transport (λ f, ap f (a • b) = ap f (b • a)) (path_forall _ _ (eissect (⇑ n.+1))) _).
    refine (ap_compose (⇑ n.+1) (⇑ n.+1)⁻¹ _ • ap _ H • (ap_compose (⇑ n.+1) (⇑ n.+1)⁻¹ _)⁻¹).
  Qed.

  Lemma em_loop_shuffle (a b c d : pt = pt :> K(G, S n)) :
    (a • b) • (d • c) = (a • c) • (b • d).
  Proof.
    rewrite (em_loop_comm d c).
    refine (concat_pp_p a b (c • d) @ _).
    refine (ap (concat a) (concat_p_pp b c d) @ _).
    refine (ap (concat a) (ap (λ t, t • d) (em_loop_comm b c)) @ _).
    refine (ap (concat a) (concat_pp_p c b d) @ _).
    exact (concat_p_pp a c (b • d)).
  Qed.
End BasicLemmas.