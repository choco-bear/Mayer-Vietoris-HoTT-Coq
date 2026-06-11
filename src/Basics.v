From HoTT Require Import HoTT Utf8.

Local Set Implicit Arguments.

Open Scope mc_add_scope.
Open Scope pointed_scope.

Notation "A ⊕ B" := (ab_biprod A B) (at level 50, left associativity).

Section Lemmas.
  Context {_Funext: Funext} {_Univalence: Univalence}.
  
  Lemma ap011_diag {A B C D: Type} (f: B → C → D)
        (g: A → B) (h: A → C) {x y: A} (p: x = y):
    ap (λ z, f (g z) (h z)) p = ap011 f (ap g p) (ap h p).
  Proof. by path_induction. Qed.

  Lemma inverse_concat_A1p {A: Type} {f: A → A}
        (h: forall x, f x = x) {x y: A} (q: x = y):
    (h y)⁻¹ • (ap f q)⁻¹ = q⁻¹ • (h x)⁻¹.
  Proof.
    refine ((inv_pp _ _)⁻¹ • _ • inv_pp _ _).
    exact (ap inverse (concat_A1p h q)).
  Qed.

  Lemma naturality_cancelR {A: Type} {x y: A} (e: x = y)
        {r: x = x} {c: y = y}:
    r • e = e • c -> c • e⁻¹ = e⁻¹ • r.
  Proof. destruct e. by rewrite !concat_1p, !concat_p1. Qed.

  Lemma ap011_homotopic {A B C: Type} (f g: A → B → C)
        (h: forall x y, f x y = g x y)
        {x x': A} {y y': B} (p: x = x') (q: y = y'):
    ap011 f p q • h x' y' = h x y • ap011 g p q.
  Proof. path_induction. by rewrite concat_1p, concat_p1. Qed.

  Lemma concat_point_eq_square {Y: Type} {y: Y}
        (a: y = y) (pa: 1 = a) (P Q: a = a):
    (P • Q) • (ap (concat a) pa⁻¹ • concat_p1 a)⁻¹ =
    (ap (concat a) pa⁻¹ • concat_p1 a)⁻¹ • ap011 concat P Q.
  Proof.
    induction pa.
    rewrite ap011_is_ap.
    rewrite (ap_homotopic_id concat_p1 P).
    rewrite (ap_homotopic_id concat_1p Q).
    simpl.
    rewrite !concat_p1, !concat_1p.
    reflexivity.
  Qed.

  Lemma concat_point_eq_square_r {Y: Type} {y: Y}
        (a: y = y) (pa: a = 1) (P Q: a = a):
    (P • Q) • (ap (concat a) pa • concat_p1 a)⁻¹ =
    (ap (concat a) pa • concat_p1 a)⁻¹ • ap011 concat P Q.
  Proof.
    rewrite <- (inv_V pa).
    exact (@concat_point_eq_square Y y a pa⁻¹ P Q).
  Qed.

  Lemma loop_moveL_1M {X: pType} {x y: pt = pt :> X}:
    x • y⁻¹ = 1 -> x = y.
  Proof.
    intro h.
    refine ((concat_p1 x)⁻¹ • _).
    refine (ap (concat x) (concat_Vp y)⁻¹ • _).
    rewrite concat_p_pp.
    refine (ap (λ t, t • y) h • _).
    apply concat_1p.
  Defined.

  Definition Pushout_ind_FlFr {A B C Y: Type} {f: A → B} {g: A → C}
        (F G: Pushout f g → Y)
        (Hl: forall b, F (pushl b) = G (pushl b))
        (Hr: forall c, F (pushr c) = G (pushr c))
        (Hglue: forall a, ap F (pglue a) • Hr (g a) = Hl (f a) • ap G (pglue a)):
    F == G.
  Proof.
    srapply Pushout_ind.
    - exact Hl.
    - exact Hr.
    - intro a. nrapply transport_paths_FlFr'. exact (Hglue a).
  Defined.
End Lemmas.

Local Notation "⇑" := pequiv_loops_em_em.

Section EM.
  Context {_Univalence: Univalence}.
  Context [G: AbGroup] (n: nat).

  Definition em_add (a b: K(G,n)): K(G,n) := (⇑ G n)⁻¹ (⇑ G n a • ⇑ G n b).

  Definition em_add_pt_pt: pt = em_add pt pt.
  Proof.
    refine ((eissect (⇑ G n) pt)⁻¹ • ap (⇑ G n)⁻¹ _⁻¹).
    exact (ap (concat _) (point_eq (⇑ G n)) • concat_p1 _).
  Defined.

  Lemma em_loop_comm (a b: pt = pt :> K(G, S n)): a • b = b • a.
  Proof.
    pose (peq := point_eq (⇑ G n.+1)).

    assert (H_dist: ∀ (y: loops K(G, n.+2)) (p: ⇑ G n.+1 pt = y) (X Y: ⇑ G n.+1 pt = ⇑ G n.+1 pt),
                        p⁻¹ • (X • Y) • p = (p⁻¹ • X • p) • (p⁻¹ • Y • p)).
    { intros. by rewrite !concat_p_pp, concat_pp_V. }

    assert (H_cancel: ∀ (y: loops K(G, n.+2)) (p: ⇑ G n.+1 pt = y) (X Y: ⇑ G n.+1 pt = ⇑ G n.+1 pt),
                        p⁻¹ • X • p = p⁻¹ • Y • p → X = Y).
    { intros. cut (X • p = Y • p).
      { intro. pose proof (ap (λ t, t • p⁻¹) X1); simpl in *. by rewrite !concat_pp_V in X2. }
      rewrite !concat_pp_p in X0. pose proof (ap (concat p) X0). by rewrite !concat_p_Vp in X1.
    }

    cut (ap (⇑ G n.+1) (a • b) = ap (⇑ G n.+1) (b • a)); cycle 1.
    { rapply (H_cancel _ peq). rewrite !ap_pp, !H_dist. apply eckmann_hilton. }

    intro H. refine ((ap_idmap _)⁻¹ • _ • ap_idmap _).
    refine (transport (λ f, ap f (a • b) = ap f (b • a)) (path_forall _ _ (eissect (⇑ G n.+1))) _).
    refine (ap_compose (⇑ G n.+1) (⇑ G n.+1)⁻¹ _ • ap _ H • (ap_compose (⇑ G n.+1) (⇑ G n.+1)⁻¹ _)⁻¹).
  Qed.

  Lemma em_loop_shuffle (a b c d: pt = pt :> K(G, S n)):
    (a • b) • (d • c) = (a • c) • (b • d).
  Proof.
    rewrite (em_loop_comm d c).
    refine (concat_pp_p a b (c • d) • _).
    refine (ap (concat a) (concat_p_pp b c d) • _).
    refine (ap (concat a) (ap (λ t, t • d) (em_loop_comm b c)) • _).
    refine (ap (concat a) (concat_pp_p c b d) • _).
    exact (concat_p_pp a c (b • d)).
  Qed.

  Lemma pequiv_loops_em_em_preserves_add (a b: K(G,n)):
    ⇑ G n (em_add a b) = ⇑ G n a • ⇑ G n b.
  Proof. by rewrite eisretr. Qed.

  Lemma em_add_loop (p q: pt = pt :> K(G,n)):
    (p • q) • em_add_pt_pt = em_add_pt_pt • ap011 em_add p q.
  Proof.
    apply (equiv_inj (ap (⇑ G n))).
    rewrite !ap_pp, !ap_V.
    rewrite <- !eisadj.
    rewrite <- !(ap_compose (⇑ G n)⁻¹ (⇑ G n)).
    rewrite !(inverse_concat_A1p (eisretr (⇑ G n))).
    rewrite <- (ap011_compose em_add (⇑ G n) p q).
    pose proof (ap011_homotopic
      (λ a b, ⇑ G n (em_add a b))
      (λ a b, ⇑ G n a • ⇑ G n b)
      (λ a b, eisretr (⇑ G n) (⇑ G n a • ⇑ G n b)) p q) as Hnat.
    rewrite (ap011_compose' concat (⇑ G n) (⇑ G n) p q) in Hnat.
    rewrite (concat_p_pp (ap (⇑ G n) p • ap (⇑ G n) q)
      (ap (concat (⇑ G n pt)) (point_eq (⇑ G n)) • concat_p1 (⇑ G n pt))⁻¹).
    rewrite (@concat_point_eq_square_r K(G,n.+1) pt (⇑ G n pt)
      (point_eq (⇑ G n)) (ap (⇑ G n) p) (ap (⇑ G n) q)).
    rewrite (concat_pp_p
      (ap (concat (⇑ G n pt)) (point_eq (⇑ G n)) • concat_p1 (⇑ G n pt))⁻¹
      (ap011 concat (ap (⇑ G n) p) (ap (⇑ G n) q))
      (eisretr (⇑ G n) (⇑ G n pt • ⇑ G n pt))⁻¹).
    rewrite (concat_pp_p
      (ap (concat (⇑ G n pt)) (point_eq (⇑ G n)) • concat_p1 (⇑ G n pt))⁻¹
      (eisretr (⇑ G n) (⇑ G n pt • ⇑ G n pt))⁻¹
      (ap011 (λ x y: K(G,n), ⇑ G n (em_add x y)) p q)).
    apply whiskerL.
    exact (naturality_cancelR _ Hnat).
  Qed.

  Lemma em_diff_eq_pt (a b: K(G,n)):
    (⇑ G n)⁻¹ (⇑ G n a • (⇑ G n b)⁻¹) = pt -> a = b.
  Proof.
    intro p.
    apply (equiv_inj (⇑ G n)).
    apply loop_moveL_1M.
    refine ((eisretr (⇑ G n) _)⁻¹ • ap (⇑ G n) p • _).
    exact (point_eq (⇑ G n)).
  Defined.
End EM.

Definition pushout_to_suspension {C A B: Type} {f: C → A} {g: C → B}: Pushout f g → Σ C :=
  Pushout_rec _ (λ a, North) (λ b, South) merid.