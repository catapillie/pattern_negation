Parameter ctor : Set.

Inductive pat :=
  | Pomega : pat
  | Por : pat -> pat -> pat
  | Pnot : pat -> pat.

Inductive subpat : pat -> pat -> Prop :=
  | sub_eq   : forall p, p = p -> subpat p p
  | sub_or_l : forall s p1 p2, subpat s p1 -> subpat s (Por p1 p2)
  | sub_or_r : forall s p1 p2, subpat s p2 -> subpat s (Por p1 p2)
  | sub_not  : forall s p, subpat s p -> subpat s (Pnot p).

Lemma subpat_refl : forall p, subpat p p.
Proof.
  constructor; reflexivity.
Qed.

Theorem pat_ind_strong :
  forall (P: pat -> Prop),
    P Pomega ->
    (forall p1, (forall s, subpat s p1 -> P s) ->
      forall p2, (forall s, subpat s p2 -> P s) ->
      P (Por p1 p2)) ->
    (forall p, (forall s, subpat s p -> P s) ->
      P (Pnot p)) ->
    forall p, P p.
Proof.
  intros P Homega Hor Hnot p. eapply ((pat_ind (fun p => forall s, subpat s p -> P s)) _ _ _ p).
  apply subpat_refl.
  Unshelve.
  - simpl. intros. inversion H. exact Homega.
  - simpl. intros. inversion H1.
    + apply Hor. trivial. trivial.
    + apply H. trivial.
    + apply H0. trivial.
  - simpl. intros. inversion H0.
    + apply Hnot. trivial.
    + apply H. trivial.
Qed. 

Inductive ge_pat : pat -> pat -> Prop :=
  | ge_lomega : forall p, ge_pat Pomega p

  | ge_lor_l : forall p1 p2 q, ge_pat p1 q -> ge_pat (Por p1 p2) q
  | ge_lor_r : forall p1 p2 q, ge_pat p2 q -> ge_pat (Por p1 p2) q
  | ge_ror   : forall p q1 q2, ge_pat p q1 -> ge_pat p q2 -> ge_pat p (Por q1 q2)
  
  | ge_lnotor : forall p1 p2 q, ge_pat (Pnot p1) q -> ge_pat (Pnot p2) q -> ge_pat (Pnot (Por p1 p2)) q
  | ge_lnotnot : forall p q, ge_pat p q -> ge_pat (Pnot (Pnot p)) q
  
  | ge_rnotomega : forall p, ge_pat p (Pnot Pomega)
  | ge_rnotor_l : forall p q1 q2, ge_pat p (Pnot q1) -> ge_pat p (Pnot (Por q1 q2))
  | ge_rnotor_r : forall p q1 q2, ge_pat p (Pnot q2) -> ge_pat p (Pnot (Por q1 q2))
  | ge_rnotnot : forall p q, ge_pat p q -> ge_pat p (Pnot (Pnot q)).

Lemma ge_refl: forall p, ge_pat p p.
Proof.
  induction p using pat_ind_strong.
  - constructor.
  - apply ge_ror.
    + apply ge_lor_l. apply H. apply subpat_refl.
    + apply ge_lor_r. apply H0. apply subpat_refl.
  - induction p using pat_ind_strong.
    + constructor.
    + apply ge_lnotor.
      ++ apply ge_rnotor_l. apply H0. apply subpat_refl. 
         intros. apply H. apply sub_or_l. trivial.
      ++ apply ge_rnotor_r. apply H1. apply subpat_refl.
         intros. apply H. apply sub_or_r. trivial.
    + constructor. constructor. apply H. constructor. constructor. trivial.
Qed.

