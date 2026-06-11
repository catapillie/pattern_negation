Parameter ctor : Set.

Inductive pat :=
  | Pomega : pat
  | Pctor  : ctor -> pats -> pat
  | Por    : pat -> pat -> pat
  | Pand   : pat -> pat -> pat
  | Pnot   : pat -> pat

with pats :=
  | PSnil : pats
  | PScons : pat -> pats -> pats.

Inductive ge_pat : pat -> pat -> Prop :=
  | ge_l_omega : forall p, ge_pat Pomega p

  | ge_ctor : forall c ps qs, ge_pats ps qs -> ge_pat (Pctor c ps) (Pctor c qs)

  | ge_lor_l : forall p1 p2 q, ge_pat p1 q -> ge_pat (Por p1 p2) q
  | ge_lor_r : forall p1 p2 q, ge_pat p2 q -> ge_pat (Por p1 p2) q
  | ge_ror   : forall p q1 q2, ge_pat p q1 -> ge_pat p q2 -> ge_pat p (Por q1 q2)

  | ge_land   : forall p1 p2 q, ge_pat p1 q -> ge_pat p2 q -> ge_pat (Pand p1 p2) q
  | ge_rand_l : forall p q1 q2, ge_pat p q1 -> ge_pat p (Pand q1 q2)
  | ge_rand_r : forall p q1 q2, ge_pat p q2 -> ge_pat p (Pand q1 q2)

  | ge_lnot : forall p q, disj_pat p q -> ge_pat (Pnot p) q
  | ge_rnot : forall p q, disj_pat (Pnot p) (Pnot q) -> ge_pat p (Pnot q)

with ge_pats : pats -> pats -> Prop :=
  | ge_ps_nil  : ge_pats PSnil PSnil
  | ge_ps_cons : forall p ps q qs, ge_pat p q -> ge_pats ps qs -> ge_pats (PScons p ps) (PScons q qs)

with disj_pat : pat -> pat -> Prop :=
  | disj_ctor : forall ca cb ps qs, ca <> cb -> disj_pat (Pctor ca ps) (Pctor cb qs)
  | disj_args : forall c ps qs, disj_pats ps qs -> disj_pat (Pctor c ps) (Pctor c qs)

  | disj_lor : forall p1 p2 q, disj_pat p1 q -> disj_pat p2 q -> disj_pat (Por p1 p2) q
  | disj_ror : forall p q1 q2, disj_pat p q1 -> disj_pat p q2 -> disj_pat p (Por q1 q2)

  | disj_land_l : forall p1 p2 q, disj_pat p1 q -> disj_pat (Pand p1 p2) q
  | disj_land_r : forall p1 p2 q, disj_pat p2 q -> disj_pat (Pand p1 p2) q
  | disj_rand_l : forall p q1 q2, disj_pat p q1 -> disj_pat p (Pand q1 q2)
  | disj_rand_r : forall p q1 q2, disj_pat p q2 -> disj_pat p (Pand q1 q2)

  | disj_lnot : forall p q, ge_pat p q -> disj_pat (Pnot p) q
  | disj_rnot : forall p q, ge_pat q p -> disj_pat p (Pnot q)

with disj_pats : pats -> pats -> Prop :=
  | disj_ps_hd : forall p ps q qs, disj_pat p q -> disj_pats (PScons p ps) (PScons q qs)
  | disj_ps_tl : forall p ps q qs, disj_pats ps qs -> disj_pats (PScons p ps) (PScons q qs).

Definition equiv_pat (p: pat) (q: pat): Prop := ge_pat p q /\ ge_pat q p.

Fixpoint ge_pat_refl : forall p, ge_pat p p
    with ge_pats_refl : forall ps, ge_pats ps ps.
Proof.
  - induction p.
    + constructor.
    + constructor; apply ge_pats_refl.
    + apply ge_ror.
      ++ apply ge_lor_l; assumption.
      ++ apply ge_lor_r; assumption.
    + apply ge_land.
      ++ apply ge_rand_l; assumption.
      ++ apply ge_rand_r; assumption.
    + repeat constructor; trivial.
  - induction ps.
    + constructor.
    + constructor.
      ++ apply ge_pat_refl.
      ++ assumption.
Qed.

Lemma equiv_pat_not_not : forall p, equiv_pat (Pnot (Pnot p)) p.
Proof.
  intro p. unfold equiv_pat.
  split.
  - constructor; constructor; apply ge_pat_refl.
  - constructor; apply disj_rnot; apply ge_pat_refl.
Qed.

Fixpoint disj_pat_sym : forall p q, disj_pat p q -> disj_pat q p
    with disj_pats_sym : forall ps qs, disj_pats ps qs -> disj_pats qs ps.
Proof.
  - intros. induction H.
    + constructor. apply not_eq_sym. trivial.
    + apply disj_args. apply disj_pats_sym. trivial.
    + constructor. assumption. assumption.
    + constructor. assumption. assumption.
    + apply disj_rand_l. assumption.
    + apply disj_rand_r. assumption.
    + apply disj_land_l. assumption.
    + apply disj_land_r. assumption.
    + constructor. assumption.
    + constructor. assumption.
  - intros. induction H.
    + apply disj_ps_hd. apply disj_pat_sym. trivial.
    + apply disj_ps_tl. trivial.
Qed.

Fixpoint disj_or_destruct_l : forall p1 p2 q, disj_pat (Por p1 p2) q -> disj_pat p1 q /\ disj_pat p2 q
    with ge_or_destruct_r : forall p q1 q2, ge_pat p (Por q1 q2) -> ge_pat p q1 /\ ge_pat p q2.
Proof.
  - intros. induction q.
    + inversion H. split. trivial. trivial.
    + inversion H. split. trivial. trivial.
    + inversion H.
      ++ split. trivial. trivial.
      ++ split.
         constructor.
          assert (disj_pat p1 q1 /\ disj_pat p2 q1). apply IHq1. trivial. destruct H5. trivial.
          assert (disj_pat p1 q2 /\ disj_pat p2 q2). apply IHq2. trivial. destruct H5. trivial.
         constructor.
          assert (disj_pat p1 q1 /\ disj_pat p2 q1). apply IHq1. trivial. destruct H5. trivial.
          assert (disj_pat p1 q2 /\ disj_pat p2 q2). apply IHq2. trivial. destruct H5. trivial.
    + inversion H.
      ++ split. trivial. trivial.
      ++ split.
        apply disj_rand_l.
        assert (disj_pat p1 q1 /\ disj_pat p2 q1). apply IHq1. trivial. destruct H4. trivial.
        apply disj_rand_l.
        assert (disj_pat p1 q1 /\ disj_pat p2 q1). apply IHq1. trivial. destruct H4. trivial.
      ++ split.
         apply disj_rand_r.
          assert (disj_pat p1 q2 /\ disj_pat p2 q2). apply IHq2. trivial. destruct H4. trivial.
         apply disj_rand_r.
          assert (disj_pat p1 q2 /\ disj_pat p2 q2). apply IHq2. trivial. destruct H4. trivial.
    + inversion H.
      ++ split. trivial. trivial.
      ++ split.
         constructor. assert (ge_pat q p1 /\ ge_pat q p2). apply ge_or_destruct_r. trivial. destruct H3. trivial.
         constructor. assert (ge_pat q p1 /\ ge_pat q p2). apply ge_or_destruct_r. trivial. destruct H3. trivial.

  - induction p.
    + split. constructor. constructor.
    + intros. inversion H. split. trivial. trivial.
    + intros. inversion H.
      ++ split.
        apply ge_lor_l.
          assert (ge_pat p1 q1 /\ ge_pat p1 q2). apply IHp1. trivial.
          destruct H4. trivial.
        apply ge_lor_l.
          assert (ge_pat p1 q1 /\ ge_pat p1 q2). apply IHp1. trivial.
          destruct H4. trivial.
      ++ split.
        apply ge_lor_r.
          assert (ge_pat p2 q1 /\ ge_pat p2 q2). apply IHp2. trivial.
          destruct H4. trivial.
        apply ge_lor_r.
          assert (ge_pat p2 q1 /\ ge_pat p2 q2). apply IHp2. trivial.
          destruct H4. trivial.
      ++ split. trivial. trivial.
    + intros. inversion H.
      ++ split. trivial. trivial.
      ++ split.
        constructor.
          assert (ge_pat p1 q1 /\ ge_pat p1 q2). apply IHp1. trivial.
          destruct H5. trivial.
          assert (ge_pat p2 q1 /\ ge_pat p2 q2). apply IHp2. trivial.
          destruct H5. trivial.
        constructor.
          assert (ge_pat p1 q1 /\ ge_pat p1 q2). apply IHp1. trivial.
          destruct H5. trivial.
          assert (ge_pat p2 q1 /\ ge_pat p2 q2). apply IHp2. trivial.
          destruct H5. trivial.
    + intros. inversion H.
      ++ split. trivial. trivial.
      ++ assert (disj_pat q1 p /\ disj_pat q2 p).
                apply disj_or_destruct_l. apply disj_pat_sym. trivial.
                destruct H3.
         split.
          constructor. apply disj_pat_sym; trivial.
          constructor. apply disj_pat_sym; trivial.
Qed.




Fixpoint ge_pat_trans : forall p q, ge_pat p q -> forall v, ge_pat q v -> ge_pat p v
    with ge_pats_trans : forall ps qs, ge_pats ps qs -> forall vs, ge_pats qs vs -> ge_pats ps vs.
Proof.
  - intros p q Hpq.
    induction Hpq.
    + constructor.
    + induction v.
      ++ intro. inversion H0.
      ++ intro. inversion H0.
         constructor. apply (ge_pats_trans _ qs). trivial. trivial.
      ++ intro. inversion H0.
         constructor. apply IHv1; trivial. apply IHv2; trivial.
      ++ intro. inversion H0.
         apply ge_rand_l. apply IHv1; trivial.
         apply ge_rand_r. apply IHv2; trivial.
      ++ admit.
    + intros. apply ge_lor_l. apply IHHpq. trivial.
    + intros. apply ge_lor_r. apply IHHpq. trivial.
    + intros. induction v.
      ++ inversion H.
         apply IHHpq1. trivial.
         apply IHHpq2. trivial.
      ++ inversion H.
         apply IHHpq1. trivial.
         apply IHHpq2. trivial.
      ++ inversion H.
         apply IHHpq1. trivial.
         apply IHHpq2. trivial.
         constructor.
           apply IHv1. trivial.
           apply IHv2. trivial.
      ++ inversion H.
         apply IHHpq1. trivial.
         apply IHHpq2. trivial.
         apply ge_rand_l. apply IHv1. trivial.
         apply ge_rand_r. apply IHv2. trivial.
      ++ admit.
    + intros.
      constructor.
        apply IHHpq1. trivial.
        apply IHHpq2. trivial.
    + intros.  induction v.
      ++ inversion H. apply IHHpq. trivial.
      ++ inversion H. apply IHHpq. trivial.
      ++ inversion H. constructor.
          apply IHv1. trivial.
          apply IHv2. trivial.
         apply IHHpq. trivial.
      ++ inversion H.
         apply IHHpq. trivial.
         apply ge_rand_l. apply IHv1. trivial.
         apply ge_rand_r. apply IHv2. trivial.
      ++ admit.
    + intros. induction v.
      ++ inversion H. apply IHHpq. trivial.
      ++ inversion H. apply IHHpq. trivial.
      ++ inversion H. constructor.
          apply IHv1. trivial.
          apply IHv2. trivial.
         apply IHHpq. trivial.
      ++ inversion H.
         apply IHHpq. trivial.
         apply ge_rand_l. apply IHv1. trivial.
         apply ge_rand_r. apply IHv2. trivial.
      ++ admit.
    + admit.
    + admit.

  - induction ps.
    + intros. inversion H.
      rewrite <- H2 in H0. inversion H0.
      constructor.
    + intros. inversion H.
      rewrite <- H4 in H0. inversion H0.
      constructor.
      apply (ge_pat_trans _ q). assumption. assumption.
      apply (IHps qs0). assumption. assumption.
Admitted.

Lemma disj_pat_value_incl : forall p q, (forall v, ge_pat q v -> ge_pat p v) -> ge_pat p q.
Proof.
  intros. apply H. apply ge_pat_refl.
Qed.
