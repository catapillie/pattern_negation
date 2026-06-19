
From Stdlib Require Import Ensembles.
From Stdlib Require Import List.
Import ListNotations.
Scheme All for list.

Axiom typ : Set.
Axiom ctor : Set.
Definition sig_ctor: Set := ctor * list typ.

Axiom sig : typ -> Ensemble sig_ctor.
Definition sig_mem (c: sig_ctor) (t: typ) := (sig t) c.
Axiom sig_fun : forall c t ts1 ts2, sig_mem (c, ts1) t -> sig_mem (c, ts2) t -> ts1 = ts2.


Inductive val :=
  | Vctor : ctor -> list val -> val.

Inductive tc : val -> typ -> Prop :=
  | tc_ctor : forall c vs t ts, sig_mem (c, ts) t -> tcs vs ts -> tc (Vctor c vs) t
with tcs : list val -> list typ -> Prop :=
  | tcs_nil : tcs [] []
  | tcs_cons : forall v vs t ts, tc v t -> tcs vs ts -> tcs (v::vs) (t::ts).

Scheme tc_ind' := Induction for tc Sort Prop
  with tcs_ind' := Induction for tcs Sort Prop.
Combined Scheme tc_tcs_mutint from tc_ind', tcs_ind'.


Inductive pat :=
  | Pomega : pat
  | Pctor : ctor -> list pat -> pat
  | Por : pat -> pat -> pat
  | Pand : pat -> pat -> pat
  | Pnot : pat -> pat.

Inductive pm : val -> pat -> typ -> Prop :=
  | pm_omega : forall v t, tc v t -> pm v Pomega t
  | pm_ctor : forall c vs ps t ts, sig_mem (c, ts) t -> pms vs ps ts -> pm (Vctor c vs) (Pctor c ps) t
  | pm_or_l : forall v p1 p2 t, pm v p1 t -> pm v (Por p1 p2) t
  | pm_or_r : forall v p1 p2 t, pm v p2 t -> pm v (Por p1 p2) t
  | pm_and  : forall v p1 p2 t, pm v p1 t -> pm v p2 t -> pm v (Pand p1 p2) t
  | pm_notctor : forall ca cb vs ps t tsa tsb, ca <> cb -> sig_mem (ca, tsa) t -> sig_mem (cb, tsb) t -> tcs vs tsb -> pm (Vctor cb vs) (Pnot (Pctor ca ps)) t
  | pm_notargs : forall c vs ps t ts, sig_mem (c, ts) t -> not_pms vs ps ts -> pm (Vctor c vs) (Pnot (Pctor c ps)) t
  | pm_notor : forall v p1 p2 t, pm v (Pnot p1) t -> pm v (Pnot p2) t -> pm v (Pnot (Por p1 p2)) t
  | pm_notand_l : forall v p1 p2 t, pm v (Pnot p1) t -> pm v (Pnot (Pand p1 p2)) t
  | pm_notand_r : forall v p1 p2 t, pm v (Pnot p2) t -> pm v (Pnot (Pand p1 p2)) t
  | pm_notnot : forall v p t, pm v p t -> pm v (Pnot (Pnot p)) t
with pms : list val -> list pat -> list typ -> Prop :=
  | pms_nil  : pms [] [] []
  | pms_cons : forall v vs p ps t ts, pm v p t -> pms vs ps ts -> pms (v::vs) (p::ps) (t::ts)
with not_pms : list val -> list pat -> list typ -> Prop :=
  | not_pms_hd : forall v vs p ps t ts, tc v t -> tcs vs ts -> pm v (Pnot p) t -> not_pms (v::vs) (p::ps) (t::ts)
  | not_pms_tl : forall v vs p ps t ts, tc v t -> tcs vs ts -> not_pms vs ps ts -> not_pms (v::vs) (p::ps) (t::ts).

Scheme pm_ind' := Induction for pm Sort Prop
  with pms_ind' := Induction for pms Sort Prop
  with not_pms_ind' := Induction for not_pms Sort Prop.
Combined Scheme pm_pms_notpms_mutind from pm_ind', pms_ind', not_pms_ind'.


Lemma pm_pms_notpms_negation
   : (forall v p t, pm v p t -> pm v (Pnot p) t -> False)
  /\ (forall vs ps ts, pms vs ps ts -> not_pms vs ps ts -> False)
  /\ (forall vs ps ts, not_pms vs ps ts -> pms vs ps ts -> False).
Proof.
  apply pm_pms_notpms_mutind.
  - intros. inversion H.
  - intros. inversion H0.
    + apply H5. reflexivity.
    + apply H. assert (ts = ts0).
      apply (sig_fun c t). trivial. trivial.
      rewrite H7. assumption.
  - intros. inversion H0. apply H. assumption.
  - intros. inversion H0. apply H. assumption.
  - intros. inversion H1.
    + apply H; assumption.
    + apply H0; assumption.
  - intros. inversion H. inversion H2.
    apply n. symmetry; assumption.
  - intros. inversion H0. inversion H3.
    apply H. assert (ts = ts0).
    apply (sig_fun c t). trivial. trivial.
    rewrite H11. assumption.
  - intros. inversion H1.
    inversion H4.
    + apply H. constructor. trivial.
    + apply H0. constructor. trivial.
  - intros. inversion H0. inversion H3.
    apply H. constructor. trivial.
  - intros. inversion H0. inversion H3.
    apply H. constructor. trivial.
  - intros. inversion H0. apply H. trivial.
  - intros. inversion H.
  - intros. inversion H1.
    + apply H. trivial.
    + apply H0. trivial.
  - intros. inversion H0.
    apply H. constructor. trivial.
  - intros. inversion H0.
    apply H. trivial.
Qed.

Lemma pm_negation : forall v p t, pm v p t -> pm v (Pnot p) t -> False.
Proof.
  destruct pm_pms_notpms_negation; exact H.
Qed.

Lemma pms_negation : forall vs ps ts, pms vs ps ts -> not_pms vs ps ts -> False.
Proof.
  destruct pm_pms_notpms_negation. destruct H0. exact H0.
Qed.



Lemma pm_pms_notpms_tc_tcs_tcs
   : (forall v p t, pm v p t -> tc v t)
  /\ (forall vs ps ts, pms vs ps ts -> tcs vs ts)
  /\ (forall vs ps ts, not_pms vs ps ts -> tcs vs ts).
  intros. apply pm_pms_notpms_mutind.
  + trivial.
  + intros. apply (tc_ctor _ _ _ ts). 
    trivial. trivial.
  + trivial.
  + trivial.
  + trivial.
  + intros. apply (tc_ctor _ _ _ tsb). 
    trivial. trivial.
  + intros. apply (tc_ctor _ _ _ ts).
    trivial. trivial.
  + trivial.
  + trivial.
  + trivial.
  + trivial.
  + constructor.
  + intros. constructor. trivial. trivial.
  + intros. constructor. trivial. trivial.
  + intros. constructor. trivial. trivial.
Qed.

Lemma pm_tc : forall v p t, pm v p t -> tc v t.
Proof.
  destruct pm_pms_notpms_tc_tcs_tcs. exact H.
Qed.

Lemma pms_tcs : forall vs ps ts, pms vs ps ts -> tcs vs ts.
Proof.
  destruct pm_pms_notpms_tc_tcs_tcs. destruct H0. exact H0.
Qed.

Lemma notpms_tcs : forall vs ps ts, not_pms vs ps ts -> tcs vs ts.
Proof.
  destruct pm_pms_notpms_tc_tcs_tcs. destruct H0. exact H1.
Qed.


Definition sem (p: pat) (t: typ) : Ensemble val :=
  fun v => pm v p t.
Definition sems (ps: list pat) (ts: list typ) : Ensemble (list val) :=
  fun vs => pms vs ps ts.

Definition Set_is_empty {U} (s: Ensemble U) := forall x, Ensembles.In _ s x -> False.

Lemma sem_notomega_empty : forall t, Set_is_empty (sem (Pnot Pomega) t).
Proof.
  unfold Set_is_empty. intros. inversion H.
Qed.

Lemma sem_or_union : forall t p1 p2, sem (Por p1 p2) t = Union _ (sem p1 t) (sem p2 t).
Proof.
  intros. apply Extensionality_Ensembles.
  split.
  - unfold Included. intros. inversion H.
    + apply Union_introl; trivial.
    + apply Union_intror; trivial.
  - unfold Included. intros. inversion H.
    + apply pm_or_l; trivial.
    + apply pm_or_r; trivial.
Qed.

Lemma sem_and_inter : forall t p1 p2, sem (Pand p1 p2) t = Intersection _ (sem p1 t) (sem p2 t).
Proof.
  intros. apply Extensionality_Ensembles.
  split.
  - unfold Included. intros. inversion H.
    constructor. trivial. trivial.
  - unfold Included. intros. inversion H.
    constructor. trivial. trivial.
Qed.

Definition sem_not_complement : forall t p, sem (Pnot p) t = Setminus _ (sem Pomega t) (sem p t).
Proof.
  intros. apply Extensionality_Ensembles.
  split.
  - unfold Included. intros. constructor.
    + constructor. apply (pm_tc _ (Pnot p)). trivial.
    + unfold not. intro.
      apply (pm_negation x p t). trivial. trivial.
  - unfold Included. intros. destruct H. 
    admit.
Admitted. 