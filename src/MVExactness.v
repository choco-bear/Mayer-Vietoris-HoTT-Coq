From HoTT Require Import HoTT Utf8.

Require Import Basics.
Require Import Cohomology.
Require Import MVSequence.

Set Implicit Arguments.

Section MVExactness.
  Context {_Funext: Funext} {_Univalence: Univalence}.
  Context {C A B: Type} (f: C → A) (g: C → B).
  Context [G: AbGroup] (n: nat).

  Definition IsExact {F X Y: pType} := @ExactSequence.IsExact (Tr (-1)) F X Y.

  Theorem mv_exact_res_diff: IsExact (mv_res' f g G n) (mv_diff' f g G n).
  Proof. (* TODO *) Admitted.

  Theorem mv_exact_diff_delta: IsExact (mv_diff' f g G n) (mv_delta' f g G n).
  Proof. (* TODO *) Admitted.

  Theorem mv_exact_delta_res: IsExact (mv_delta' f g G n) (mv_res' f g G (S n)).
  Proof. (* TODO *) Admitted.
End MVExactness.