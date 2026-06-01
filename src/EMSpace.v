From HoTT Require Import HoTT Utf8.

Module EMSpace.
  Section EMSpace.
    Context `{Funext} `{Univalence}.
    Context (G: AbGroup) (n: nat).
    
    Instance _is_hspace: IsHSpace K(G,n) :=
      ishspace_cohhspace K(G,n) (iscohhspace_em n).

    Instance _sg_op: SgOp (K(G,n)) := @hspace_op _ _is_hspace.
  End EMSpace.
End EMSpace.
Existing Instance EMSpace._is_hspace.
Existing Instance EMSpace._sg_op.