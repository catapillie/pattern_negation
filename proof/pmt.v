
From Stdlib Require Import Ensembles.
Scheme All for list.
Scheme All for list_all.

Inductive typ :=
  | Tctor : list typ -> typ.

Definition ctor_typ := list typ.

Axiom sig : typ -> Ensemble (ctor_typ).
Definition sigmem (c: ctor_typ) (t: typ) := (sig t) c. 

Inductive empty_typ : typ -> Type :=
  | empty_ctor : forall t,
    (forall c, (sigmem c t -> list_all typ empty_typ c)) ->
    empty_typ t.

Definition empty_sig (t: typ) := forall c, sigmem c t -> False.

Lemma empty_sig_is_empty_typ : forall t, empty_sig t -> empty_typ t.
Proof.
    constructor. intros.
    unfold empty_sig in H.
    exfalso. apply (H c). trivial.
Qed.

Inductive val :=
  | Vctor : list val -> val.

Inductive pat :=
  | Pomega : pat
  | Pctor : list pat -> pat
  | Por : pat -> pat -> pat
  | Pand : pat -> pat -> pat
  | Pnot : pat -> pat.
