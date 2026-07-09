From Equations Require Import Equations.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.
From Stdlib Require Import List.
Import ListNotations.
Scheme All for list.


Axiom typ : Set.

Axiom ctor : Set.
Axiom veq_ctor : ctor -> ctor -> bool.
Axiom veq_ctor_true : forall c c', veq_ctor c c' = true <-> c = c'.
Axiom veq_ctor_false : forall c c', veq_ctor c c' = false <-> c <> c'.
Axiom eq_ctor_decide : forall a b : ctor, a = b \/ a <> b.

Definition sig_ctor: Set := ctor * list typ.

Axiom sig : typ -> Ensemble sig_ctor.
Definition sig_mem (c: sig_ctor) (t: typ) := (sig t) c.
Axiom sig_fun : forall c t ts1 ts2, sig_mem (c, ts1) t -> sig_mem (c, ts2) t -> ts1 = ts2.


Definition row t := list t.
Definition mat t := list (row t).

Inductive val :=
  | Vctor : ctor -> row val -> val.

Inductive tc : val -> typ -> Prop :=
  | tc_ctor : forall c vs t ts, sig_mem (c, ts) t -> tcs vs ts -> tc (Vctor c vs) t
with tcs : row val -> row typ -> Prop :=
  | tcs_nil : tcs [] []
  | tcs_cons : forall v vs t ts, tc v t -> tcs vs ts -> tcs (v::vs) (t::ts).

Scheme tc_ind' := Induction for tc Sort Prop
  with tcs_ind' := Induction for tcs Sort Prop.
Combined Scheme tc_tcs_mutint from tc_ind', tcs_ind'.


Inductive pat :=
  | Pomega : pat
  | Pctor : ctor -> row pat -> pat
  | Por : pat -> pat -> pat
  | Pand : pat -> pat -> pat
  | Pnot : pat -> pat.

Fixpoint pat_size p :=
  match p with
  | Pomega => 0
  | Pctor _ ps => 1 + list_sum (List.map pat_size ps)
  | Por p1 p2 => 1 + pat_size p1 + pat_size p2 
  | Pand p1 p2 => 1 + pat_size p1 + pat_size p2 
  | Pnot p => 1 + pat_size p
  end.

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
with pms : row val -> row pat -> row typ -> Prop :=
  | pms_nil  : pms [] [] []
  | pms_cons : forall v vs p ps t ts, pm v p t -> pms vs ps ts -> pms (v::vs) (p::ps) (t::ts)
with not_pms : row val -> row pat -> row typ -> Prop :=
  | not_pms_hd : forall v vs p ps t ts, tc v t -> tcs vs ts -> pm v (Pnot p) t -> not_pms (v::vs) (p::ps) (t::ts)
  | not_pms_tl : forall v vs p ps t ts, tc v t -> tcs vs ts -> not_pms vs ps ts -> not_pms (v::vs) (p::ps) (t::ts).

Scheme pm_ind' := Induction for pm Sort Prop
  with pms_ind' := Induction for pms Sort Prop
  with not_pms_ind' := Induction for not_pms Sort Prop.
Combined Scheme pm_pms_notpms_mutind from pm_ind', pms_ind', not_pms_ind'.

Inductive pmm : row val -> mat pat -> row typ -> Prop :=
  | pmm_hd : forall vs ps pss ts, pms vs ps ts -> pmm vs (ps::pss) ts
  | pmm_tl : forall vs ps pss ts, pmm vs pss ts -> pmm vs (ps::pss) ts.

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

Lemma pm_excluded_middle : forall p v t, tc v t -> pm v p t \/ pm v (Pnot p) t.
Proof.
  induction p.
  - left. constructor. trivial.
  - destruct v. intros.
    destruct (eq_ctor_decide c c0).
    + admit.
    + right. admit.
  - intros. destruct (IHp1 v t).
    + assumption.
    + left. apply pm_or_l. trivial.
    + destruct (IHp2 v t).
      ++ assumption.
      ++ left. apply pm_or_r. trivial.
      ++ right. constructor.
         trivial. trivial.
  - intros. destruct (IHp1 v t).
    + assumption.
    + destruct (IHp2 v t).
      ++ assumption.
      ++ left. constructor.
         trivial. trivial.
      ++ right. apply pm_notand_r. trivial. 
    + right. apply pm_notand_l. trivial.
  - intros. destruct (IHp v t).
    + assumption.
    + right. constructor. trivial.
    + left. trivial.
Admitted.

Lemma pm_false_not_pm : forall v p t, tc v t -> (pm v p t -> False) -> pm v (Pnot p) t.
Proof.
  intros. destruct (pm_excluded_middle p v t).
  - assumption.
  - destruct H0. trivial.
  - trivial.
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
Definition sems (ps: row pat) (ts: row typ) : Ensemble (row val) :=
  fun vs => pms vs ps ts.
Definition semm (pss: mat pat) (ts: row typ) : Ensemble (row val) :=
  fun vs => pmm vs pss ts.

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
    apply pm_false_not_pm.
    + inversion H. trivial.
    + trivial.
Qed.


Fixpoint omegas {T} (l: list T) :=
  match l with
  | [] => []
  | _ :: xs => Pomega :: omegas xs
  end.

Lemma tcs_pms_omegas : forall vs ts, tcs vs ts -> pms vs (omegas ts) ts.
Proof.
  intros. induction H.
  - constructor.
  - simpl. constructor.
    + constructor. trivial.
    + trivial.
Qed.


Definition matdisj (m1: mat pat) (m2: mat pat) : mat pat :=
  m1 ++ m2.

Lemma pmm_matdisj_l : forall vs m1 m2 ts, pmm vs m1 ts -> pmm vs (matdisj m1 m2) ts.
Proof.
  intros. unfold matdisj.
  induction H.
  - simpl. apply pmm_hd. trivial.
  - simpl. apply pmm_tl. trivial.
Qed.

Lemma pmm_matdisj_r : forall vs m1 m2 ts, pmm vs m2 ts -> pmm vs (matdisj m1 m2) ts.
Proof.
  intros. induction m1.
  + trivial.
  + simpl. apply pmm_tl. trivial. 
Qed.


Definition matconj (m1: mat pat) (m2: mat pat) : mat pat :=
  List.map (fun (r12: row pat * row pat) =>
    let (r1, r2) := r12 in
    List.map (fun (p12: pat * pat) =>
      let (p1, p2) := p12 in
      Pand p1 p2
    ) (List.combine r1 r2 )
  ) (list_prod m1 m2).

Lemma pmm_matconj : forall vs m1 m2 ts, pmm vs m1 ts -> pmm vs m2 ts -> pmm vs (matconj m1 m2) ts.
Admitted. (* for now *)


Fixpoint negate_row (r: row pat): mat pat :=
  match r with
  | [] => []
  | p :: ps => [(Pnot p) :: omegas ps]
    ++ List.map (fun r => Pomega :: r) (negate_row ps)
  end.

Equations? spec (p: pat) (sc: sig_ctor) : mat pat
by wf (pat_size p) :=
  spec Pomega (_, ts) := [omegas ts];
  spec (Pctor c' ps) (c, _) := if veq_ctor c c' then [ps] else [];
  spec (Por p1 p2) cc := matdisj (spec p1 cc) (spec p2 cc);
  spec (Pand p1 p2) cc := matconj (spec p1 cc) (spec p2 cc);
  spec (Pnot (Pomega)) cc := [];
  spec (Pnot (Pctor c' ps)) (c, ts) := if veq_ctor c c' then negate_row ps else [omegas ts];
  spec (Pnot (Por p1 p2)) cc := matconj (spec (Pnot p1) cc) (spec (Pnot p2) cc);
  spec (Pnot (Pand p1 p2)) cc := matdisj (spec (Pnot p1) cc) (spec (Pnot p2) cc);
  spec (Pnot (Pnot p)) cc := spec p cc.
Proof.
  all: lia.
Qed.


Lemma pm_ctor_spec : forall c vs p t ts, sig_mem (c, ts) t -> tcs vs ts -> pm (Vctor c vs) p t -> pmm vs (spec p (c, ts)) ts.
Proof.
  intros. induction p.
  - rewrite spec_equation_1.
    constructor. apply tcs_pms_omegas. trivial.
  - rewrite spec_equation_2. 
    destruct (veq_ctor c c0) eqn:Hveq.
    + rewrite veq_ctor_true in Hveq.
      constructor. inversion H1.
      assert (ts=ts0). apply (sig_fun c t).
      trivial. trivial. rewrite Hveq. trivial.
      rewrite H9. trivial.
    + rewrite veq_ctor_false in Hveq.
      inversion H1. destruct Hveq. trivial.
  - rewrite spec_equation_3. inversion H1.
    + apply pmm_matdisj_l. apply IHp1. trivial.
    + apply pmm_matdisj_r. apply IHp2. trivial.
  - rewrite spec_equation_4. inversion H1.
    apply pmm_matconj.
    apply IHp1. trivial.
    apply IHp2. trivial.
  - admit.
Admitted.
