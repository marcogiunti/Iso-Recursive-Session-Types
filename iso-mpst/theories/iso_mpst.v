(** Iso-Recursive MPST -- mgiunti@ualg.pt *)

Require Import String.
Require Import PeanoNat.
Require Import Program.Equality.
Require Import List.
Require Import Coq.FSets.FSetInterface.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Classes.RelationClasses.
Require Import FunInd.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FinFun.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.
Require Import ZArith.

Require Import header.
Require Import operations.
Require Import CpdtTactics LibTactics.

Import ListNotations.
Import Notations.

Hint Resolve classic.

(** Total Functions *)
Definition injective {A B} (f : A -> B) :=
  forall x y, f x = f y -> x = y.

(** Partial functions *)
Definition t  (A : Type) := option A.
Definition _return {a : Set} (x_value : a) : t a := Some x_value.
Definition raise {a : Set} : t a := None.
Definition partial_fun A B := A -> t B.
Definition fresh {A B} (g : partial_fun A B) (x : A) := g x = None.
Definition consistent {A} (eqb : A -> A -> bool) :=
  forall x1 x2, eqb x1 x2 = true <-> x1 = x2.

Lemma consistent_true A eqb : consistent eqb -> forall x:A, eqb x x = true.
  introv CNS; intros x.
  assert(x=x) by tauto.
  eapply CNS in H.
  assumption.
Defined.

Function extend {A B} (eqb : A -> A -> bool) (g : partial_fun A B)
  (x : A) (s : B) (pf : fresh g x) : partial_fun A B :=
  fun y =>
    if eqb x y
    then
      Some s
    else
      g y.

Definition disjoint_domain {A B} (g : partial_fun A B)
  (h : partial_fun A B) :=
  forall x,
    (g x <> None -> h x = None) /\
      (h x <> None -> g x = None).

Function cat {A B} 
  (g : partial_fun A B)
  (h : partial_fun A B)
  (pf : disjoint_domain g h ) : partial_fun A B :=
  fun y =>
    match g y with
    | Some s =>
        Some s
    | None =>
        h y
    end.

Function update {A B} (eqb : A -> A -> bool) (g : partial_fun A B)
  (x : A) (s : B) : partial_fun A B :=
  fun y =>
    if eqb x y
    then
      Some s
    else
      g y.

(** Finite atoms *)
Notation atom := nat (only parsing).
Definition var := atom.

(** Types *)
Inductive participant : Set :=
| pyp : nat -> participant.
Inductive label : Set :=
| lbl : nat -> label.

Add Printing Let participant.
Add Printing Let label.

Definition participant_beq p1 p2 :=
  match p1, p2 with
  | pyp r1, pyp r2 =>
      r1 =? r2
  end.

Definition label_beq p1 p2 :=
  match p1, p2 with
  | pyp r1, pyp r2 =>
      r1 =? r2
  end.

Lemma participant_beq_eq :
  forall (p1 p2 : participant),
    participant_beq p1 p2 = true <-> p1 = p2.
Proof with eauto.
  split; introv EQ.
  induction p1, p2;
    simpl in EQ;
    rewrite Nat.eqb_eq in EQ;
    subst;
    try tauto.
  subst.
  induction p2; simpl...
  rewrite Nat.eqb_eq...
Qed.

Corollary participant_beq_eq_true :
  forall p,
    participant_beq p p = true.
  intros; assert (p =p) by tauto.
  rewrite <- participant_beq_eq in H.
  assumption.
Defined.

Hint Rewrite  participant_beq_eq_true.

Lemma label_beq_eq :
  forall p1 p2,
    label_beq p1 p2 = true <-> p1 = p2.
Proof with eauto.
  split; introv EQ.
  induction p1, p2;
    simpl in EQ;
    rewrite Nat.eqb_eq in EQ;
    subst;
    try tauto.
  subst.
  induction p2; simpl...
  rewrite Nat.eqb_eq...
Qed.

Notation pbeq := participant_beq.
Notation lbeq := label_beq.

Inductive styp : Set :=
| styp_int   : styp
| styp_nat   : styp
| styp_bool  : styp
| styp_unit  : styp.

Scheme Equality for styp.

Inductive typ : Set :=
| typ_var  : var -> typ
| typ_mu :    var -> typ -> typ
| typ_sum : typ -> typ -> typ
| typ_input : participant -> label -> styp -> typ -> typ
| typ_output : participant -> label -> styp -> typ -> typ
| typ_end   : typ.

Function  top t :=
  match t with
  | typ_input p _ _ _ 
  | typ_output p _ _ _ =>
      [p]
  | typ_sum t1 t2 =>
      top t1 ++ top t2
  | _ =>
      []
  end.

Fixpoint tbranch_r t :=
  match t with
  | typ_input _ _ _ _ =>
      True
  | typ_sum t1 t2 =>
      tbranch_r t1 /\ tbranch_r t2
  | _ =>
      False
  end.

Fixpoint nodup l :=
  match l with
  | [] => []
  | x::xs =>
      if existsb (fun y => pbeq x y) xs
      then
        nodup xs
      else x::(nodup xs)
  end.

Lemma tbranchr_part t :
  tbranch_r t ->
  top t <> [].
Proof with eauto.
  introv TB;
    induction t;
    simpl...
  unfold tbranch_r in TB; fold tbranch_r in *; intuition.
  destruct ( top t1); inv H...
  discriminate.
Qed.

Definition single_party (l : list participant) :=
  l <> [] /\
    forall p q,
      In p l -> In q l -> p = q. 

Definition tbranch t :=
  tbranch_r t /\ 
    single_party ( top t).

Fixpoint tselect_r t :=
  match t with
  | typ_output _ _ _ _ =>
      True
  | typ_sum t1 t2 =>
      tselect_r t1 /\ tselect_r t2
  | _ =>
      False
  end.

Lemma tselectr_part t :
  tselect_r t ->
  top t <> [].
Proof with eauto.
  introv TB;
    induction t;
    simpl...
  unfold tselect_r in TB; fold tselect_r in *; intuition.
  destruct ( top t1); inv H...
  discriminate.
Qed.

Definition tselect t :=
  tselect_r t /\
    single_party ( top t).

Lemma eqb_eq2 n m:
  true = (n =? m)  <-> n = m.
Proof with eauto.
  rewrite <-Nat.eqb_eq...
  intuition.
Qed.

Lemma andb_true_eq2 a b :
  a && b = true -> true = a /\ true = b.
Proof with eauto.  
  introv EQ.
  eapply andb_true_eq...
Qed.

Function substT T1 X T2 :=
  match T1 with
  | typ_var Y =>
      if X =? Y then T2 else T1
  | typ_mu Y T =>
      if X =? Y then T1 else typ_mu Y (substT T X T2)
  | typ_sum U1 U2 =>
      typ_sum (substT U1 X T2) (substT U2 X T2)
  | typ_input p l s T =>
      typ_input p l s (substT T X T2)
  | typ_output p l s T =>
      typ_output p l s (substT T X T2)
  | _ => T1
  end.

Notation "X '£' T" := (substT T X (typ_mu X T)) (at level 40).

Lemma sp_app l1 l2:
  l1 <> [] ->
  l2 <> [] ->
  single_party (l1 ++ l2) ->
  single_party l1 /\ single_party l2.
Proof with eauto using in_eq.  
  introv DF1 DF2 SP.
  destruct SP as [DF3 SP].
  destruct l1, l2;
    try contradiction;
    unfold single_party;
    repeat split;
    intros...
  - inv H; inv H0;
      try eapply SP...
    all:
      try eapply in_app_iff; try left; try right...
  - inv H; inv H0;
      try eapply SP...
    all:
      try eapply in_app_iff; try right...
    all: right...
Qed.

Lemma tbranch_sum t1 t2 :
  tbranch (typ_sum t1 t2) ->
  tbranch t1 /\ tbranch t2.
Proof with eauto using tbranchr_part, tselectr_part.
  introv TB.
  inverts TB as TR;
    inv TR;
    split;
    try econstructor;
    try tauto.
  unfold top in H0;
    fold top in H0.
  eapply  sp_app in H0...
  intuition.
  eapply  sp_app in H0...
  intuition.
Qed.

Lemma tselect_sum t1 t2 :
  tselect (typ_sum t1 t2) ->
  tselect t1 /\ tselect t2.
Proof with eauto using tbranchr_part, tselectr_part.
  introv TB.
  inverts TB as TR;
    inv TR;
    split;
    try econstructor;
    try tauto.
  unfold top in H0;
    fold top in H0.
  eapply  sp_app in H0...
  intuition.
  eapply  sp_app in H0...
  intuition.
Qed.

Lemma tbranch_party_subst t1 x t2:
  tbranch t1 ->
  top t1 = top (substT t1 x t2).
Proof
  with
  eauto
  using
  tbranch_sum,
    tbranchr_part,
    tselectr_part,
    sp_app.
  introv TB.
  induction t1;
    inverts TB as K;
    inv K;
    simpl;
    try rewrite IHt1_1;
    try rewrite IHt1_2;
    unfold tbranch;
    repeat split;
    intros;
    simpl in H0;
    destruct H0 as [K IH]...
  eapply IH;
    try eapply in_app_iff; right...
  eapply IH;
    try eapply in_app_iff; left...
Qed.

Lemma tbranch_subst t1 x t2:
  tbranch t1 ->
  tbranch (substT t1 x t2).
Proof
  with
  eauto
  using
  tbranch_party_subst.
  introv TB.
  dependent induction t1;
    assert (TB2 := TB);
    try inverts TB2 as K;
    try inv K;
    try simpl...
  assert (TB2 := TB).
  eapply tbranch_party_subst
    with (x :=x) (t2 := t2)
    in TB2...
  unfold top in H0;
    fold top in H0.
  destruct H0 as [K1 SP].
  unfold tbranch;
    repeat split...
  - eapply IHt1_1;
      unfold tbranch;
      split;
      try tauto;
      try eapply sp_app in H0 as [K _]...
    eapply  tbranch_sum in TB as [K2 _];
      destruct K2 as [_ K3]...
  - eapply IHt1_2;
      unfold tbranch;
      split;
      try tauto;
      try eapply sp_app in H0 as [_ K]...
    eapply  tbranch_sum in TB as [_ K2];
      destruct K2 as [_ K3]...
  - assert (IH: tbranch (substT t1_1 x t2)).
    eapply IHt1_1...
    eapply tbranch_sum in TB as [K _]...
    simpl;
      destruct IH as [K _];
      try eapply  tbranchr_part in K...
    destruct ( top (substT t1_1 x t2));
      try discriminate...
  - intros.
    assert (EQ: top t1_1 ++ top t1_2 =
                  top (typ_sum t1_1 t1_2))...
    rewrite EQ,TB2 in SP...
Qed.

Lemma tselect_party_subst t1 x t2:
  tselect t1 ->
  top t1 = top (substT t1 x t2).
Proof
  with
  eauto
  using
  tbranch_sum,
    tbranchr_part,
    tselectr_part,
    sp_app.
  introv TB.
  induction t1;
    inverts TB as K;
    inv K;
    simpl;
    try rewrite IHt1_1;
    try rewrite IHt1_2;
    unfold tselect;
    repeat split;
    intros;
    simpl in H0;
    destruct H0 as [K IH]...
  eapply IH;
    try eapply in_app_iff; right...
  eapply IH;
    try eapply in_app_iff; left...
Qed.

Lemma tselect_subst t1 x t2:
  tselect t1 ->
  tselect (substT t1 x t2).
Proof
  with
  eauto
  using
  tselect_party_subst.
  introv TB.
  dependent induction t1;
    assert (TB2 := TB);
    try inverts TB2 as K;
    try inv K;
    try simpl...
  assert (TB2 := TB).
  eapply tselect_party_subst
    with (x :=x) (t2 := t2)
    in TB2...
  unfold top in H0;
    fold top in H0.
  destruct H0 as [K1 SP].
  unfold tselect;
    repeat split...
  - eapply IHt1_1;
      unfold tselect;
      split;
      try tauto;
      try eapply sp_app in H0 as [K _]...
    eapply  tselect_sum in TB as [K2 _];
      destruct K2 as [_ K3]...
  - eapply IHt1_2;
      unfold tselect;
      split;
      try tauto;
      try eapply sp_app in H0 as [_ K]...
    eapply  tselect_sum in TB as [_ K2];
      destruct K2 as [_ K3]...
  - assert (IH: tselect (substT t1_1 x t2)).
    eapply IHt1_1...
    eapply tselect_sum in TB as [K _]...
    simpl;
      destruct IH as [K _];
      try eapply  tselectr_part in K...
    destruct ( top (substT t1_1 x t2));
      try discriminate...
  - intros.
    assert (EQ: top t1_1 ++ top t1_2 =
                  top (typ_sum t1_1 t1_2))...
    rewrite EQ,TB2 in SP...
Qed.



Notation "p ? l s . t" := (typ_input p l s t) (at level 40).
Notation "p ! l  s . t" := (typ_output p l s t) (at level 40).
Notation "-I" := (styp_int)  (at level 40).
Notation "-B" := (styp_bool)  (at level 40).
Notation "-U" := (styp_unit)  (at level 40).
Notation "-E" := (typ_end)  (at level 40).
Notation "# X" := (typ_var X)  (at level 40).
Notation "@ X T" := (typ_mu X T)  (at level 40).

Function tbranch_labels t :=
  match t with
  | typ_input _ l s _ =>
      [l]
  | typ_sum t1 t2 =>
      tbranch_labels t1 ++ tbranch_labels t2
  | _ =>
      []
  end.

Lemma tbranch_label_subst t1 x t2:
  tbranch t1 ->
  tbranch_labels t1 = tbranch_labels(substT t1 x t2).
Proof
  with
  eauto
  using
  tbranch_sum,
    tbranchr_part,
    tselectr_part,
    sp_app.
  introv TB.
  induction t1;
    inverts TB as K;
    inv K;
    simpl;
    try rewrite IHt1_1;
    try rewrite IHt1_2;
    unfold tbranch;
    repeat split;
    intros;
    simpl in H0;
    destruct H0 as [K IH]...
  eapply IH;
    try eapply in_app_iff; right...
  eapply IH;
    try eapply in_app_iff; left...
Qed.

Function tselect_labels ts :=
  match ts with
  | typ_output _ l s _ =>
      [l]
  | typ_sum t1 t2 =>
      tselect_labels t1 ++ tselect_labels t2
  | _ =>
      []
  end.

Lemma tselect_label_subst t1 x t2:
  tselect t1 ->
  tselect_labels t1 = tselect_labels(substT t1 x t2).
Proof
  with
  eauto
  using
  tbranch_sum,
    tbranchr_part,
    tselectr_part,
    sp_app.
  introv TB.
  induction t1;
    inverts TB as K;
    inv K;
    simpl;
    try rewrite IHt1_1;
    try rewrite IHt1_2;
    unfold tbranch;
    repeat split;
    intros;
    simpl in H0;
    destruct H0 as [K IH]...
  eapply IH;
    try eapply in_app_iff; right...
  eapply IH;
    try eapply in_app_iff; left...
Qed.

(** [ndl t = True] means no duplicate labels in branch and selection *)
Fixpoint ndl t :=
  match t with
  | typ_var _
  | typ_end =>
      True
  | typ_mu _ t =>
      ndl t
  | typ_sum t1 t2 =>
      ((tbranch t /\ NoDup (tbranch_labels t)) \/
         (tselect t /\ NoDup (tselect_labels t))) /\ 
        ndl t1 /\
        ndl t2
  | typ_input _ _ _ t 
  | typ_output _ _ _ t =>
      ndl t
  end.

Fixpoint remove X l   :=
  match l with
  | [] => []
  | Y::tl =>
      if X =? Y
      then
        remove X tl
      else
        Y :: (remove X tl)
  end.

(** Free variables of typ *)
Function fvT t :=
  match t with
  | typ_var X =>
      [X]
  | typ_end =>
      nil
  | typ_mu X t1 =>
      remove X (fvT t1)
  | typ_sum t1 t2 =>
      fvT t1 ++ fvT t2
  | typ_input _ _ _ t1
  | typ_output _ _ _ t1 =>
      fvT t1
  end.

(** Bound variables of typ *)
Function bvT t :=
  match t with
  | typ_var _ 
  | typ_end =>
      nil
  | typ_mu X t1 =>
      [X] ++ bvT t1
  | typ_sum t1 t2 =>
      bvT t1 ++ bvT t2
  | typ_input _ _ _ t1
  | typ_output _ _ _ t1 =>
      bvT t1
  end.

Definition closed t :=
  fvT t = nil.

(** Well-formed types *)
Definition wf t := ndl t.

Lemma wf_mu x t:
  wf (typ_mu x t) ->
  wf t.
Proof with eauto.
  introv WF.
  simpl in *...
Qed.  

Lemma wf_sum t1 t2:
  wf (typ_sum t1 t2) ->
  wf t1 /\ wf t2.
Proof with eauto.
  introv WF.
  unfold wf, ndl in *;
    intuition.
Qed. 

Lemma wf_input p l s t:
  wf (typ_input p l s t) ->
  wf t.
Proof with eauto.
  introv WF.
  unfold wf, ndl in *;
    intuition.
Qed.

Lemma wf_output p l s t:
  wf (typ_output p l s t) ->
  wf t.
Proof with eauto.
  introv WF.
  unfold wf, ndl in *;
    intuition.
Qed.

Lemma ndl_substT X T1 T2:
  ndl T1 ->
  ndl T2 ->
  ndl (substT T1 X T2).
Proof
  with
  eauto
  using
  tbranch_subst,
    tbranch_label_subst.
  introv ND1 ND2.
  induction T1;
    simpl;
    try destruct (X =? v)...
  destruct ND1 as ([(TB &SL) | (TS &SL)] & [NDL1 NDL2]).
  repeat split.
  - left; split...
    eapply tbranch_subst in TB...
    rewrite tbranch_label_subst
      with (x := X) (t2 := T2)
      in SL...
  - eauto.
  - eauto.
  - split...
    right; split...
    eapply tselect_subst in TS...
    rewrite tselect_label_subst
      with (x := X) (t2 := T2)
      in SL...
Qed.

Lemma wf_substT_gen X T1 T2:
  wf T1 ->
  wf T2 ->
  wf (substT T1 X T2).
Proof
  with
  eauto
  using
  wf_sum,
    wf_input,
    wf_output.
  introv WF1 WF2.
  dependent induction T1;
    simpl;
    try destruct (X =? v)...
  - unfold wf; simpl; repeat split.
    * destruct WF1 as ([(TB &SL) | (TS &SL)] &[NDL1 NDL2]).
      left; split...
      eapply tbranch_subst in TB...
      rewrite tbranch_label_subst
        with (x := X) (t2 := T2)
        in SL...
      right; split...
      eapply tselect_subst in TS...
      rewrite tselect_label_subst
        with (x := X) (t2 := T2)
        in SL...
    * eapply ndl_substT...
      eapply wf_sum in WF1 as [K _]...
    * eapply ndl_substT...
      eapply wf_sum in WF1 as [_ K]...
Qed.

Lemma wf_substT X T:
  wf (typ_mu X T) ->
  wf (X £ T).
Proof with eauto using  wf_substT_gen.
  introv WF...
Qed.


(** Processes *)
Inductive evar : Set :=
| evar_var : nat -> evar.

Definition evar_beq e1 e2 :=
  match e1, e2 with
  | evar_var n1, evar_var n2 =>
      n1 =? n2
  end.

Lemma evar_beq_eq x1 x2:
  evar_beq x1 x2 = true <-> x1 = x2.
Proof with eauto.
  split; introv EQ.
  induction x1, x2;
    simpl in EQ;
    rewrite Nat.eqb_eq in EQ;
    subst;
    try tauto.
  subst.
  induction x2; simpl...
  rewrite Nat.eqb_eq...
Qed.

Lemma evar_beq_true x:
  evar_beq x x = true.
Proof with eauto.
  intros. rewrite evar_beq_eq...
Qed.

Inductive value : Set :=
| value_nat : nat -> value
| value_int : Z -> value
| value_bool : bool -> value
| value_unit : value.

Inductive expr : Set :=
| expr_var : evar -> expr
| expr_val : value -> expr
| expr_succ : expr -> expr
| expr_neg : expr -> expr.

Inductive eval_expr : expr -> value -> Prop :=
| eval_val v:
  eval_expr (expr_val v) v
| eval_succ n:
  eval_expr
    (expr_succ (expr_val (value_nat n))) (value_nat (S n))
| eval_neg b:
  eval_expr
    (expr_neg (expr_val (value_bool b))) (value_bool (negb b)).

Inductive process_var : Set :=
| pvar : nat -> process_var.

Definition process_var_beq e1 e2 :=
  match e1, e2 with
  | pvar n1, pvar n2 =>
      n1 =? n2
  end.

Lemma process_var_beq_eq x1 x2:
  process_var_beq x1 x2 = true <-> x1 = x2.
Proof with eauto.
  split; introv EQ.
  induction x1, x2;
    simpl in EQ;
    rewrite Nat.eqb_eq in EQ;
    subst;
    try tauto.
  subst.
  induction x2; simpl...
  rewrite Nat.eqb_eq...
Qed.

Lemma process_var_beq_true x:
  process_var_beq x x = true.
Proof with eauto.
  rewrite process_var_beq_eq...
Qed.

Fixpoint removev x l   :=
  match l with
  | [] => []
  | y :: tl =>
      if evar_beq x y
      then
        removev x tl
      else
        y :: (removev x tl)
  end.

Fixpoint removeV x l   :=
  match l with
  | [] => []
  | y :: tl =>
      if process_var_beq x y
      then
        removeV x tl
      else
        y :: (removeV x tl)
  end.

Inductive session : Set :=
| single_session :
  (participant * process) -> session
| parallel_session :
  session -> session -> session

with process : Set :=
| proc_input :
  participant -> label -> evar -> styp -> process -> process
| proc_output :
  participant -> label -> expr -> styp -> process -> process
| proc_sum : process -> process -> process
| proc_conditional : expr -> process -> process -> process
| proc_var : process_var -> process
| proc_zero : process
| proc_mu :  process_var -> process -> process.

Definition shiftv (M : nat) x :=
  match x with
  |  evar_var y =>
       evar_var (y + M)
  end.

Definition shiftV (M : nat) X :=
  match X with
  |  pvar y =>
       pvar (y + M)
  end.

Function shiftE (M : nat) e :=
  match e with
  | expr_var x =>
      expr_var (shiftv M x)
  | expr_val _ =>
      e
  | expr_succ e1 =>
      expr_succ (shiftE M e1)
  | expr_neg e1 =>
      expr_neg (shiftE M e1)
  end.

Function shiftP (M : nat) (P : process) :=
  match P with
  | proc_input p l y s Q =>
      proc_input p l (shiftv M y) s (shiftP M Q)
  | proc_output p l e s Q =>
      proc_output p l (shiftE M e) s (shiftP M Q)
  | proc_sum P1 P2 =>
      proc_sum (shiftP M P1) (shiftP M P2)
  | proc_conditional e P1 P2 =>
      proc_conditional
        (shiftE M e) (shiftP M P1) (shiftP M P2)
  | proc_var x =>
      proc_var (shiftV M x)
  | proc_zero =>
      proc_zero
  | proc_mu X Q =>
      proc_mu (shiftV M X) (shiftP M Q)
  end.

Function substE e v x :=
  match e with
  | expr_var y =>
      if evar_beq x y then expr_val v else e
  | expr_val _ =>
      e
  | expr_succ e1 =>
      expr_succ (substE e1 v x)
  | expr_neg e1 =>
      expr_neg (substE e1 v x)
  end.

(** Substitution of variable [substV P v x] is P{v/x} *)
Function substV  P v x :=
  match P with
  | proc_input p l y s Q =>
      proc_input p l y s (substV Q v x)
  | proc_output p l e s Q =>
      proc_output p l (substE e v x) s (substV Q v x)
  | proc_sum P1 P2 =>
      proc_sum (substV P1 v x) (substV P2 v x)
  | proc_conditional e P1 P2 =>
      proc_conditional
        (substE e v x) (substV P1 v x) (substV P2 v x)
  | proc_var _ 
  | proc_zero =>
      P
  | proc_mu X Q =>
      proc_mu X (substV Q v x)
  end.

(** Substitution of process [substV P Q X] is P{Q/X} *)
Function substP P Q X :=
  match P with
  | proc_input p l x s P1 =>
      proc_input p l x s (substP P1 Q X)
  | proc_output p l e s P1 =>
      proc_output p l e s (substP P1 Q X)
  | proc_sum P1 P2 =>
      proc_sum (substP P1 Q X) (substP P2 Q X)  
  | proc_conditional e P1 P2 =>
      proc_conditional
        e (substP P1 Q X) (substP P2 Q X)
  | proc_var Y =>
      if process_var_beq X Y then Q else P
  | proc_zero =>
      proc_zero
  | proc_mu Y R =>
      proc_mu Y (substP R Q X)
  end.

Inductive proc_equiv : session -> session -> Prop :=
| pe_refl M:
  proc_equiv M M
| pe_commut s1 s2:
  proc_equiv
    (parallel_session s1 s2)
    (parallel_session s2 s1).

Hint Constructors proc_equiv.

Inductive exchange : Set :=
| exc : participant -> label -> participant -> exchange.

(** Labeleled transition system of sessions *)
Inductive proc_action : Set :=
| ainput : participant -> label -> value -> proc_action
| aoutput :  participant -> label -> value -> proc_action
| aunfold : participant -> proc_action
| atau : option exchange -> proc_action.

(** Type system *)
Definition typ_env := partial_fun evar styp.
Definition empty_env : typ_env := fun _ => None.
Notation "g ',,' x '-:' t @ pf" :=
  (extend evar_beq g x t pf) (at level 40).

Definition proc_env := partial_fun process_var typ.
Definition empty_penv : proc_env := fun _ => None.
Notation "h ',,' x '=:' t @ pf" :=
  (extend process_var_beq h x t pf) (at level 40).

Definition part_env := partial_fun participant typ.
Definition empty_ptenv : part_env := fun _ => None.
Notation "d ',,' p '#:' t @ pf" :=
  (extend participant_beq d p t pf) (at level 40).
Notation "d '<-' p '#:' t" :=
  (update participant_beq d p t) (at level 40).
Lemma fresh_none {A B} (p:A):
  fresh (fun _ => None : option B) p.
Proof. intros; unfold fresh; tauto. Defined.
Definition singleton p t : part_env :=
  empty_ptenv,, p #: t @ fresh_none p.
Notation "d1 '@@' d2 @ pf" :=
  (cat d1 d2 pf)  (at level 40).

Lemma singleton_eq p tp :
  singleton p tp p = Some tp.
Proof with eauto.
  unfold singleton, extend.
  rewrite participant_beq_eq_true...
Qed.

Inductive stypes (g : typ_env) : expr -> styp -> Prop :=
| s_var x s:
  g x = Some s ->
  stypes g (expr_var x) s
| s_val_nat x:
  stypes g (expr_val (value_nat x)) styp_nat
| s_val_int x:
  stypes g (expr_val (value_int x)) styp_int
| s_val_bool x:
  stypes g (expr_val (value_bool x)) styp_bool
| s_val_unit :
  stypes g (expr_val (value_unit)) styp_unit
| s_succ e:
  stypes g e styp_nat ->
  stypes g (expr_succ e) styp_nat
| s_neg e:
  stypes g e styp_bool ->
  stypes g (expr_neg e) styp_bool.

Inductive types (g : typ_env) (h : proc_env) :
  process -> typ -> Prop :=
| t_zero :
  types g h proc_zero typ_end
| t_fold X T t P pf:
  h X = None ->
  types g (h,, X=: typ_mu t T @ pf) P (t £ T) ->
  types g h (proc_mu X P) (typ_mu t T)
| t_var X t T:
  h X = Some (typ_mu t T) ->
  types g h (proc_var X) (typ_mu t T)
| t_input p x l s t P pf:
  types (g,, x-:s @ pf) h P t ->
  types g h
    (proc_input p l x s P)
    (typ_input p l s t)
| t_output  p e l s t P:
  stypes g e s ->
  types g h P t ->
  types g h
    (proc_output p l e s P)
    (typ_output p l s t)
| t_branch p l x s P Q t1 t2:
  types g h (proc_input p l x s P) t1 ->
  types g h Q t2 ->
  types g h
    (proc_sum (proc_input p l x s P) Q)
    (typ_sum t1 t2)
| t_select_l p e l P s t1 t2:
  types g h (proc_output p l e s P) t1 ->
  types g h
    (proc_output p l e s P)
    (typ_sum t1 t2)
| t_select_r p e l P s t1 t2:
  types g h (proc_output p l e s P) t2 ->
  types g h
    (proc_output p l e s P)
    (typ_sum t1 t2)
| t_conditional e P Q t:
  stypes g e styp_bool ->
  types g h P t ->
  types g h Q t ->
  types g h
    (proc_conditional e P Q) t.

Hint Constructors stypes types.


Function parties t :=
  match t with
  | typ_input p _ _ t1 
  | typ_output p _ _ t1 =>
      p :: parties t1
  | typ_sum t1 t2 =>
      parties t1 ++ parties t2
  | typ_mu _ t => parties t  
  | _ =>
      []
  end.

Definition parties_disjoint (d1 : part_env) (d2 : part_env) :=
  forall p q tp tq,
    d1 p = Some tp ->
    d2 q = Some tq ->
    disjoint (parties tp) (parties tq).

(* d1 \subseteq d2 *)
Definition sub_env (d1 d2 : part_env) :=
  forall p,
    d1 p <> None ->
    d2 p = d1 p.

Definition diff d1 d2 (ld : list part_env) :=
  exists n1 n2,
    nth_error ld n1 = Some d1 /\
      nth_error ld n2 = Some d2 /\
      n1 <> n2.

Definition partition (d : part_env) (ld : list part_env) :=
  (forall d',
      In d' ld -> sub_env d' d) /\ 
    (forall d1 d2,
        In d1 ld -> In d2 ld -> diff d1 d2 ld->
        disjoint_domain d1 d2 /\ parties_disjoint d1 d2).
        
Definition partition_closed (d: part_env) :=
forall p t, 
d p = Some t ->
(forall q, In q ( parties t) -> d q <> None).        

Parameter compliance : part_env -> Prop.

Inductive types_session (g : typ_env) (h : proc_env)
  : session -> part_env  -> Prop :=
| ts_single p P T1:
  wf T1 ->
  types g h P T1 ->
  types_session g h
    (single_session (p, P))
    (singleton p T1)
(* Note that in the paper there is the notion of min_partition,
while in the mechanisation we exploit the assumption that 
compliance is only defined for minimal environments.
Check the OCaml/Why3 implementation of compliance:
let[@ghost] history1 = history @ [env]
  in
  if not (minimal env)
  then
    raise (NotMinimal history1)
  else ...
 *)
| ts_parallel s1 d1 s2 d2 ld pf:
  types_session g h s1 d1 ->
  types_session g h s2 d2 ->
  partition (d1 @@ d2 @pf) ld ->
  (forall d, In d ld -> partition_closed d /\ compliance d) ->
  types_session g h 
    (parallel_session s1 s2)
    (d1 @@ d2 @pf).

Hint Constructors types_session.

(** Free variables of process *)
Function fv p :=
  match p with 
  | proc_input _ _ x _ P =>
      removev x (fv P)
  | proc_output _ _ (expr_var x) _ P =>
      x :: fv P
  | proc_output _ _ _ _ P =>
      fv P
  | proc_mu _ P => 
      fv P
  | proc_sum P1 P2  
  | proc_conditional _ P1 P2 =>
      fv P1 ++ fv P2
  | proc_var _ 
  | proc_zero =>
      []
  end.  

(** Free process variables of process *)
Function fvP p :=
  match p with 
  | proc_input _ _ _ _ P 
  | proc_output _ _ _ _ P =>
      fvP P     
  | proc_sum P1 P2  
  | proc_conditional _ P1 P2 =>
      fvP P1 ++ fvP P2
  | proc_var X =>
      [X]
  | proc_zero =>
      []
  | proc_mu Y R =>
      removeV Y (fvP R)
  end.

(** Bound variables of process *)
Function bv p :=
  match p with 
  | proc_input _ _ x _ P =>
      x :: bv P
  | proc_output _ _ _ _ P =>
      bv P
  | proc_sum P1 P2  
  | proc_conditional _ P1 P2 =>
      bv P1 ++ bv P2
  | proc_var _ 
  | proc_zero =>
      []
  | proc_mu Y R =>
      bv R
  end.

(** Bound process variables of process *)
Function bvP p :=
  match p with 
  | proc_input _ _ _ _ P 
  | proc_output _ _ _ _ P =>
      bvP P
  | proc_sum P1 P2  
  | proc_conditional _ P1 P2 =>
      bvP P1 ++ bvP P2
  | proc_var _ 
  | proc_zero =>
      []
  | proc_mu Y R =>
      Y :: bvP R
  end.

(** Seeds of processes *)
Definition seeds_evar :=
  fun x =>
    match x with
    | evar_var n => n
    end.

Definition seedsv l :=
  List.map seeds_evar l.

Definition seeds_pvar :=
  fun x =>
    match x with
    | pvar n => n
    end.

Definition seedsV l :=
  List.map  seeds_pvar l.

Definition seeds p :=
  seedsv (bv p) ++ seedsV (bvP p).

Function maxL (l : list nat) :=
  match l with
  | [] => 0
  | h :: tl =>
      let m := maxL tl
      in
      max h m
  end.

Definition max_seed p := maxL (seeds p).

(** Session semantics *)
Inductive lts : session -> proc_action -> session -> Prop :=
| r_input p q l x s v P :
  stypes empty_env (expr_val v) s ->
  lts
    (single_session
       (p, proc_input q l x s P))
    (ainput q l v)
    (single_session (p, substV P v x))
| r_output p q l e v s P:
  eval_expr e v ->
  lts
    (single_session
       (p, proc_output q l  e s P))
    (aoutput q l v)
    (single_session (p, P))
| r_sum p P a P' Q:
  lts
    (single_session (p, P))
    a
    (single_session (p, P')) ->
  lts
    (single_session (p, proc_sum P Q))
    a
    (single_session (p, P'))
| r_comm p q l v  P P' Q Q' s:
  lts
    (single_session (p, P))
    (ainput q l v)
    (single_session (p, P')) ->
  lts
    (single_session (q, Q))
    (aoutput p l v)
    (single_session (q, Q')) ->
  lts
    (parallel_session
       (parallel_session
          (single_session (p, P))
          (single_session (q, Q)))
       s)
    (atau (Some (exc p l q)))
    (parallel_session
       (parallel_session
          (single_session (p, P'))
          (single_session (q, Q')))
       s)
| r_rec p X P RP M s:
  max_seed (proc_mu X P) < M ->
  RP = shiftP M (proc_mu X P) ->
  lts
    (parallel_session
       (single_session (p, proc_mu X P))
       s)
    (aunfold p)
    (parallel_session
       (single_session (p,  substP P RP X))
       s)
| r_true p e P1 P2 s:
  eval_expr e (value_bool true) ->
  lts
    (parallel_session
       (single_session (p,  proc_conditional e P1 P2))
       s)
    (atau None)
    (parallel_session
       (single_session (p, P1))
       s)

| r_false p e P1 P2 s:
  eval_expr e (value_bool false) ->
  lts
    (parallel_session
       (single_session (p,  proc_conditional e P1 P2))
       s)
    (atau None)
    (parallel_session
       (single_session (p, P2))
       s)
| r_struct a M1' M1 M2 M2':
  proc_equiv M1' M1 ->
  lts M1 a M2 ->
  proc_equiv M2 M2' ->
  lts M1' a M2'.

Hint Constructors lts.

Definition ndp (p : process) :=
  NoDup (bv p).
Definition ndP p := NoDup (bvP p).
Definition wfp p :=
  ndp p /\ ndP p.

Function wfm M :=
  match M with
  | single_session (_, P) =>
      wfp P
  | parallel_session s1 s2  =>
      wfm s1 /\ wfm s2
  end.

Lemma fv_sum p1 p2:
  fv (proc_sum p1 p2) = [] ->
  fv p1 = [] /\
    fv p2 = [].
Proof with eauto using app_eq_nil.
  introv FV.
  simpl in *...
Qed.

Lemma fvP_sum p1 p2:
  fvP (proc_sum p1 p2) = [] ->
  fvP p1 = [] /\
    fvP p2 = [].
Proof with eauto using app_eq_nil.
  introv FV.
  simpl in *...
Qed.

Definition closedP P :=
  fv P = nil /\
    fvP P = nil.

(** Closed session *)
Function closedS M :=
  match M with
  | single_session (_, p) =>
      closedP p
  | parallel_session m1 m2 =>
      closedS m1 /\
        closedS m2
  end.

Lemma nin_cons {A} (x : A) y l:
  ~In x (y :: l) ->
  x <> y /\ ~ In x l.
Proof with eauto using in_eq.
  introv NIN.
  split; introv ABS.
  subst.
  assert (In y (y :: l))...
  assert (In x (y :: l)).
  right...
  contradiction.
Qed.

Lemma extend_match A B (g : partial_fun A B) x s pf s1 eqb:
  consistent eqb ->
  (extend eqb g x s pf) x = Some s1 ->
  s1 = s.
Proof with eauto.
  introv EBQ EQ.
  unfold extend in EQ.
  rewrite consistent_true in *...
  inv EQ...
Qed.

Lemma extend_mismatch A B (g : partial_fun A B) x s pf x0 s1 eqb:
  consistent eqb ->
  eqb x x0 = false ->   
  (extend eqb g x s pf) x0 = Some s1 ->
  g x0 = Some s1.
Proof with eauto.
  introv EQb DIFF EQ.
  unfold extend in EQ.
  rewrite DIFF in *...
Qed.

Lemma substitutionE G x s s1 e v pf:
  stypes (G,, x -: s @pf) e s1 ->
  stypes G (expr_val v) s ->
  stypes G (substE e v x) s1.
Proof
  with
  eauto
  using
  extend_match,
    extend_mismatch.
  
  introv ST STVAL.
  dependent induction ST;
    try econstructor...
  case_eq (evar_beq x x0);
    intros EQ;
    try rewrite evar_beq_eq in *;
    subst.
  assert (s0 = s);
    unfold extend in H;
    rewrite evar_beq_true in *;
    try inversion H...
  subst s0.
  simpl;
    try rewrite evar_beq_true in *;
    try inv H1...
  simpl;
    unfold extend in H;
    try rewrite EQ in *;
    econstructor...
Qed.

Lemma fresh_absurd  A B (g : partial_fun A B) x s eqb pf:
  consistent eqb ->
  fresh (extend eqb g x s pf) x ->
  False.
Proof with eauto.
  introv EQB FH.
  unfold fresh,extend in FH.
  rewrite consistent_true in *;
    try discriminate...
Qed.

Lemma fresh_cons  A B (g : partial_fun A B) x s eqb pf x0:
  consistent eqb ->
  fresh  (extend eqb g x s pf) x0 ->
  fresh g x0.
Proof with eauto.
  introv EQB FH.
  unfold fresh, extend in *;
    destruct (eqb x x0);
    try discriminate...
Qed.

Lemma fresh_diff  A B (g : partial_fun A B) x s pf x0 eqb:
  consistent eqb ->
  fresh (extend eqb g x s pf) x0 ->
  eqb x x0 = false.
Proof with eauto.
  introv EQB FH.
  unfold fresh, extend in *;
    destruct (eqb x x0);
    try discriminate...
Qed.

Lemma diff_fresh  A B (g : partial_fun A B) x s pf x0 eqb:
  consistent eqb ->
  fresh g x0 ->
  eqb x0 x = false ->
  fresh (extend eqb g x s pf) x0.
Proof with eauto.
  introv EQB FH NEQ.
  unfold consistent, fresh, extend in *...
  case_eq ( eqb x x0);
    introv ABS;
    try rewrite EQB in *;
    subst;
    try rewrite consistent_true in *;
    try discriminate...
Qed.

Lemma extend_swap  A B (g : partial_fun A B)
  eqb x0 s0 x s pf pf0 pf01 pf1:
  consistent eqb ->
  extend eqb
    (extend eqb g x s pf)
    x0 s0 pf0 =
    extend eqb
      (extend eqb g x0 s0 pf01)
      x s pf1.
Proof
  with
  eauto
  using
  fresh_diff.

  introv EQB.
  unfold extend,consistent in *.
  apply functional_extensionality;
    intros y.
  case_eq (eqb x0 y);
    intros EQ;
    try rewrite EQB in *;
    try subst y...
  assert (EQ: eqb x x0 = false)...
  rewrite EQ...
  Unshelve.
  assumption.
Qed.

Lemma consistent_evar_beq : consistent evar_beq.
Proof.
  unfold consistent.  
  apply evar_beq_eq.
Qed.

Lemma fresh_nin_bv G x s pf H P t:
  types (G,, x -: s @ pf) H P t ->
  ~In x (bv P).
Proof
  with
  eauto
  using
  fresh_absurd,
    fresh_cons,
    extend_swap,
    diff_fresh,
    fresh_diff,
    nin_cons,
    consistent_evar_beq.

  introv TC.
  dependent induction TC...
  - simpl;
      intros [ABS | ABS];
      try subst...
    
    assert (pf01 : fresh G x0)...
    remember  (G,, x0 -: s0 @ pf01) as G1.
    assert (pf1 : fresh G1 x).
    subst...
    specialize IHTC with 
      (x :=x) (s := s)
      (G := G1) (pf := pf1).
    eapply IHTC; subst.
    erewrite extend_swap...
    tauto.
  - unfold bv; fold bv.
    assert (EQ: evar_beq x x0 = false)...
    inv TC1...
    introv ABS.
    inv ABS.
    rewrite evar_beq_true in EQ;
      discriminate.
    eapply in_app_iff in H as [K1 | K2].
    specialize IHTC1 with (pf := pf).
    assert ( ~ In x (bv (proc_input p l x0 s0 P)))...
    unfold bv in H; fold bv in H...
    assert (~In x (bv P))...
    eapply nin_cons...
    eapply IHTC2...
  - simpl;
      introv ABS;
      eapply in_app_iff in ABS as [K1 | K2]...
    eapply IHTC1...
    eapply IHTC2...
Qed.

(** Substitution lemma, values *)
Lemma substitution G x s H P t v pf:
  types (G,, x -: s @ pf) H P t ->
  stypes G (expr_val v) s ->
  types G H (substV P v x) t.
Proof
  with
  eauto
  using
  substitutionE,
    fresh_absurd,
    fresh_cons,
    extend_swap,
    diff_fresh,
    fresh_diff,
    nin_cons,
    fresh_nin_bv,
    consistent_evar_beq.
  
  introv TC STC.
  assert (NIN: ~In x (bv P))...
  dependent induction TC;
    intros;
    simpl...
  - assert (DIFF: evar_beq x x0 = false)...
    assert (pf1 : fresh G x0)...
    eapply t_input with (pf := pf1)...
    assert (pf2: fresh  (G,, x0 -: s0 @ pf1) x)...
    eapply IHTC with (s :=s) (pf := pf2)...
    erewrite extend_swap...
    inv STC; econstructor...
    eapply nin_cons...
  - eapply t_branch...
  - econstructor...
Qed.

(** Lts of types *)
Inductive typ_lts : typ -> proc_action -> typ -> Prop :=
| e_fold X T p :
  typ_lts
    (typ_mu X T)
    (aunfold p)
    (X £ T)
| e_input p l v s t :
  typ_lts
    (typ_input p l s t)
    (ainput p l v)
    t
| e_output p l v s t :
  typ_lts
    (typ_output p l s t)
    (aoutput p l v)
    t
| e_branch_l t1 t2 p l v  t' :
  typ_lts t1 (ainput p l v) t' ->
  typ_lts
    (typ_sum t1 t2)
    (ainput p l v)
    t'
| e_branch_r t1 t2 p l v  t' :
  typ_lts t2 (ainput p l v) t' ->
  typ_lts
    (typ_sum t1 t2)
    (ainput p l v)
    t'
| e_select_l t1 t2 p l v t' :
  typ_lts t1 (aoutput p l v) t' ->
  typ_lts
    (typ_sum t1 t2)
    (aoutput p l v)
    t'
| e_select_r t1 t2 p l v t' :
  typ_lts t2 (aoutput p l v) t' ->
  typ_lts
    (typ_sum t1 t2)
    (aoutput p l v)
    t'.

Hint Constructors typ_lts.

Lemma types_output g h p l e s P t :
  types g h (proc_output p l e s P) t ->
  In l (tselect_labels t).
Proof with eauto.
  introv TC.
  dependent induction t;
    try inv TC;
    try simpl...
  try eapply in_app_iff...
  try eapply in_app_iff;
    right...
Qed.

Lemma types_input g h p l e s P t :
  types g h (proc_input p l e s P) t ->
  In l (tbranch_labels t).
Proof with eauto.
  introv TC.
  dependent induction t;
    try inv TC;
    try simpl...
Qed.

Lemma lts_output p l v t  t1:
  typ_lts t (aoutput p l v) t1 ->
  In l (tselect_labels t).
Proof with eauto.
  introv LTS.
  dependent induction LTS;
    try simpl;
    try eapply in_app_iff...
Qed.

Lemma lts_input p l v t  t1:
  typ_lts t (ainput p l v) t1 ->
  In l (tbranch_labels t).
Proof with eauto.
  introv LTS.
  dependent induction LTS;
    try simpl;
    try eapply in_app_iff...
Qed.

Lemma NoDup_app {A} (l1 : list A) (l2 : list A) x :
  NoDup (l1 ++ l2) ->
  In x l1 ->
  In x l2 ->
  False.
Proof with eauto using in_eq.
  introv ND IN1 IN2.
  assert (disjoint l1 l2).
  eapply no_dup_iff...
  assert False.
  eapply disjoint_absurd...
  contradiction.
Qed.

Lemma tselect_nil_branch t:
  tselect t ->
  tbranch_labels t = [].
Proof with eauto using tselect_sum.
  introv TS.
  dependent induction t;
    simpl;
    try rewrite IHt1, IHt2...
  eapply tselect_sum in TS as [_ K]...
  eapply tselect_sum in TS as [K _]...
  inv TS; inv H.
Qed.

Lemma tbranch_nil_select t:
  tbranch t ->
  tselect_labels t = [].
Proof with eauto using tbranch_sum.
  introv TS.
  dependent induction t;
    simpl;
    try rewrite IHt1, IHt2...
  eapply tbranch_sum in TS as [_ K]...
  eapply tbranch_sum in TS as [K _]...
  inv TS; inv H.
Qed.

Lemma tbranch_absurd l t1 t2:
  wf (typ_sum t1 t2) ->
  In l (tbranch_labels t1) ->
  In l (tbranch_labels t2) ->
  False.
Proof with eauto using NoDup_app, tselect_nil_branch.
  introv [[(TB &ND) | ABS] _] IN1 IN2.
  simpl in ND.
  assert False.
  eapply NoDup_app...
  contradiction.
  assert ( tbranch_labels (typ_sum t1 t2) = []).
  intuition...
  simpl in H.
  eapply app_eq_nil in H as [EQ1 EQ2].
  rewrite EQ1, EQ2 in *;
    contradiction.
Qed.

Lemma tselect_absurd l t1 t2:
  wf (typ_sum t1 t2) ->
  In l (tselect_labels t1) ->
  In l (tselect_labels t2) ->
  False.
Proof with eauto using NoDup_app, tbranch_nil_select.
  introv [[ABS | (TB &ND)] _] IN1 IN2.
  assert ( tselect_labels (typ_sum t1 t2) = []).
  intuition...
  simpl in H.
  eapply app_eq_nil in H as [EQ1 EQ2].
  rewrite EQ1, EQ2 in *;
    contradiction.
  simpl in ND.
  assert False.
  eapply NoDup_app...
  contradiction.
Qed.

Lemma wf_sum_out_false_l t1 t2 g h p l e P v s t'':
  wf (typ_sum t1 t2) ->
  types g h (proc_output p l e s P) t1 ->
  typ_lts t2 (aoutput p l v) t'' ->
  False.
Proof with eauto using types_output, lts_output, tselect_absurd.
  introv WF TC LTS.
  assert (IN1:  In l (tselect_labels t1))...
Qed.

Lemma wf_sum_out_false_r t1 t2 g h p l e P v s t':
  wf (typ_sum t1 t2) ->
  types g h (proc_output p l e s P) t2 ->
  typ_lts t1 (aoutput p l v) t' ->
  False.
Proof with eauto using types_output, lts_output, tselect_absurd.
  introv WF TC LTS.
  assert (IN1:  In l (tselect_labels t1))...
Qed.

Lemma wf_sum_inp_false_l t1 t2 g h p l x v s P t'':
  wf (typ_sum t1 t2) ->
  types g h (proc_input p l x s  P) t1 ->
  typ_lts t2 (ainput p l v) t'' ->
  False.
Proof with eauto using types_input, lts_input, tbranch_absurd.
  introv WF TC LTS.
  assert (IN1:  In l (tbranch_labels t1))...
Qed.

Lemma wf_sum_inp_false_r t1 t2 g h p l x v s  P t':
  wf (typ_sum t1 t2) ->
  types g h (proc_input p l x s P) t2 ->
  typ_lts t1 (ainput p l v) t' ->
  False.
Proof with eauto using types_input, lts_input, tbranch_absurd.
  introv WF TC LTS.
  assert (IN1:  In l (tbranch_labels t1))...
Qed.

Lemma lts_input_output_false p p1 l1 x p2 l2 v s1 P M:
  lts
    (single_session (p, proc_input p1 l1 x s1 P))
    (aoutput p2 l2 v)
    M ->
  False.
Proof with eauto.
  introv LTS.
  dependent induction LTS...
  inv H...
Qed.

Lemma lts_typ_mu_output_false G H P X T p p2 l2 v M:
  types G H P (typ_mu X T) ->
  lts
    (single_session (p, P))
    (aoutput p2 l2 v)
    M ->
  False.
Proof with eauto.
  introv TC LTS.
  dependent induction LTS...
  inv TC.
  inv TC.
  inv H0...
Qed.

Lemma lts_typ_mu_input_false G H P X T p p2 l2 v M:
  types G H P (typ_mu X T) ->
  lts
    (single_session (p, P))
    (ainput p2 l2 v)
    M ->
  False.
Proof with eauto.
  introv TC LTS.
  dependent induction LTS...
  inv TC.
  inv TC.
  inv H0...
Qed.



Lemma lts_input_typ p P q l v M G H T:
  lts (single_session (p, P)) (ainput q l v) M ->
  types G H P T ->
  exists U,
    typ_lts T (ainput q l v) U.
Proof with eauto.    
  introv LTS TC.
  gen G H T.
  dependent induction LTS; intros...
  inv TC...
  inverts TC as TC1 TC2.
  eapply IHLTS in TC1 as (U &E1)...
  inv H...
Qed.

Lemma lts_output_typ p P q l v M G H T:
  lts (single_session (p, P)) (aoutput q l v) M ->
  types G H P T ->
  exists U,
    typ_lts T (aoutput q l v) U.
Proof with eauto.    
  introv LTS TC.
  gen G H T.
  dependent induction LTS; intros...
  dependent induction TC...
  try eapply IHTC in H as (U&E1)...
  try eapply IHTC in H as (U&E1)...
  inverts TC as TC1 TC2.
  eapply IHLTS in TC1 as (U &E1)...
  eapply IHLTS in TC as (U &E1)...
  inv H...
Qed.

Definition  action_dual a b p q :=
  match a, b with
  | ainput p1 l1 v1, aoutput p2 l2 v2  =>
      p1 = p /\ p2 = q /\ l1 = l2 /\ v1 = v2
  | aoutput p1 l1 v1, ainput p2 l2 v2 =>
      p1 = p /\ p2 = q /\ l1 = l2 /\ v1 = v2
  | _, _ =>
      False
  end.

Inductive clos_sym (R : relation typ) : relation typ  :=
| rst_step x y : R x y -> clos_sym R x y
| rst_sym x y : clos_sym R x y -> clos_sym R y x.

Hint Constructors clos_sym.

Lemma symmetric_clos_sym R:
  symmetric typ (clos_sym R).
Proof with eauto.
  unfold symmetric; introv EQ...
Qed.



Lemma tbranch_output_false t p l v u:
  tbranch t ->
  typ_lts t (aoutput p l v) u ->
  False.
Proof with eauto using lts_output, tbranch_nil_select.
  intros.
  assert (In l (tselect_labels t))...
  assert (EQ:(tselect_labels t)=[])...
  rewrite EQ in *;
    contradiction.
Qed.

Lemma tselect_input_false t p l v u:
  tselect t ->
  typ_lts t (ainput p l v) u ->
  False.
Proof with eauto using lts_input, tselect_nil_branch.
  intros.
  assert (In l (tbranch_labels t))...
  assert (EQ:(tbranch_labels t)=[])...
  rewrite EQ in *;
    contradiction.
Qed.

Lemma tselect_sum_l t1 t2:
  tselect (typ_sum t1 t2) ->
  tselect t1.
Proof.
  eapply tselect_sum.
Qed.

Lemma tselect_sum_r t1 t2:
  tselect (typ_sum t1 t2) ->
  tselect t2.
Proof.
  eapply tselect_sum.
Qed.

Lemma tbranch_sum_l t1 t2:
  tbranch (typ_sum t1 t2) ->
  tbranch t1.
Proof.
  eapply tbranch_sum.
Qed.

Lemma tbranch_sum_r t1 t2:
  tbranch (typ_sum t1 t2) ->
  tbranch t2.
Proof.
  eapply tbranch_sum.
Qed.



Inductive elts : part_env -> proc_action -> part_env -> Prop :=
| SeRec d p t t':
  typ_lts t (aunfold p) t' ->
  d p = Some t ->
  elts d (aunfold p) (d <- p #: t')
| SeCom p q l v d tp tp' tq tq':
  typ_lts tp (ainput q l v) tp' ->
  typ_lts tq (aoutput p l v) tq' ->
  d p = Some tp ->
  d q = Some tq ->
  elts
    d
    (atau (Some (exc p l q)))
    ((d <- p #: tp') <- q #: tq').

Axiom elts_compliance :
  forall d1 a d2,
    compliance d1 ->
    elts d1 a d2 ->
    compliance d2.

Lemma stypes_empty G e t:
  stypes empty_env e t ->
  stypes G e t.
Proof with eauto.
  introv ST.
  dependent induction ST; try econstructor...
  inv H...
Qed.

Lemma bv_recp X x P:
  ~ In X (bvP (proc_mu x P)) ->
  ~ In X (bvP P).
Proof with eauto.  
  introv NIN.
  simpl in NIN...
Qed.

Lemma bv_sum_l X p1 p2:
  ~ In X (bvP (proc_sum p1 p2)) ->
  ~ In X (bvP p1).
Proof with eauto.  
  introv NIN.
  simpl in NIN;
    eapply not_in_app_and in NIN;
    intuition.
Qed.

Lemma bv_sum_r X p1 p2:
  ~ In X (bvP (proc_sum p1 p2)) ->
  ~ In X (bvP p2).
Proof with eauto.  
  introv NIN.
  simpl in NIN;
    eapply not_in_app_and in NIN;
    intuition.
Qed.

Lemma stypes_weak g x s' e s pf:
  stypes g e s ->
  stypes (g,, x -: s' @ pf) e s.
Proof with eauto.
  introv ST.
  induction ST; econstructor...
  case_eq (evar_beq x x0);
    intros ABS;
    try rewrite evar_beq_eq in *;
    subst.
  unfold fresh in pf; 
    try rewrite pf in *;
    try discriminate.
  unfold extend;
    rewrite ABS...
Qed.

Lemma types_weakTE g h Q T x s pf:
  ~In x (bv Q) ->
  types g h Q T ->
  types (g,, x -: s @ pf) h Q T.
Proof
  with
  eauto
  using
  in_cons,
    stypes_weak,
    consistent_evar_beq.
  
  introv NIN TC.
  induction TC;
    assert (NIN2 := NIN);
    simpl in NIN2...
  - assert (pf1 : fresh (g,, x -: s @ pf) x0).
    eapply diff_fresh...
    eapply nin_cons in NIN2 as [K _]...
    case_eq ( evar_beq x0 x); introv ABS;
      try rewrite evar_beq_eq in *;
      subst;
      try contradiction...
    eapply t_input with (pf := pf1)...
    erewrite extend_swap...
  - eapply t_branch...
    eapply IHTC1; simpl;
      try introv [ABS | ABS]; intuition.
    eapply IHTC2; simpl;
      try introv [ABS | ABS]; intuition.
  - econstructor...
    eapply IHTC1; simpl;
      try introv [ABS | ABS]; intuition.
    eapply IHTC2; simpl;
      try introv [ABS | ABS]; intuition.
    Unshelve.
    eapply diff_fresh, fresh_diff...
Qed.

Lemma consistent_process_var_beq:
  consistent process_var_beq.
Proof.
  assert (K := process_var_beq_eq).
  unfold consistent; auto.
Qed.

Lemma types_weakPE g h Q T x s pf:
  ~In x (bvP Q) ->
  types g h Q T ->
  types g (h,, x =: s @ pf) Q T.
Proof with
  eauto
  using
  in_cons,
    stypes_weak,
    consistent_process_var_beq.
  
  introv NIN TC.
  induction TC;
    assert (NIN2 := NIN);
    simpl in NIN2...
  - assert (pf1 : fresh (h,, x =: s @ pf) X).
    eapply diff_fresh...
    eapply nin_cons in NIN2 as [K _]...
    case_eq ( process_var_beq X x); introv ABS;
      try rewrite process_var_beq_eq in *;
      subst;
      try contradiction...
    eapply t_fold with (pf := pf1)...
    erewrite extend_swap...
  - case_eq ( process_var_beq x X);
      intros ABS;
      try rewrite process_var_beq_eq in *;
      subst.
    rewrite pf in H; discriminate.
    econstructor;
      unfold extend;
      rewrite ABS...
  - eapply t_branch...
    eapply IHTC1; simpl;
      try introv [ABS | ABS]; intuition.
    eapply IHTC2; simpl;
      try introv [ABS | ABS]; intuition.
  - econstructor...
    eapply IHTC1; simpl;
      try introv [ABS | ABS]; intuition.
    eapply IHTC2; simpl;
      try introv [ABS | ABS]; intuition.
    Unshelve.
    eapply diff_fresh, fresh_diff...
Qed.


Lemma nin_remove x y l:
  process_var_beq x y = false ->
  ~ In x (removeV y l) ->
  ~ In x l.
Proof with eauto using in_eq, nin_cons.
  introv PNEQ NIN ABS.
  induction l;
    intros;
    try destruct y, a;
    unfold removeV in *;
    fold removeV in *...
  case_eq (process_var_beq (pvar n) (pvar n0));
    intros EQ;
    try rewrite EQ in *;
    try rewrite process_var_beq_eq in *;
    try inv EQ...
  inv ABS...
  rewrite process_var_beq_true in *;
    discriminate.
  inv ABS...
  eapply nin_cons in NIN as (NIN1 &NIN2)...
Qed.

Lemma types_nin_strength G K Q X T R pf:
  ~ In X (fvP Q) ->
  types G (K,, X =: T @ pf) Q R->
  types G K Q R.
Proof
  with
  eauto
  using
  fresh_cons,
    consistent_evar_beq,
    consistent_process_var_beq,
    fresh_diff,
    diff_fresh,
    nin_remove,
    not_in_app_and.
  
  introv CLS TC.
  dependent induction TC...
  - assert (DIFF: process_var_beq X X0= false)...
    assert (pf1: fresh K X0)...
    eapply t_fold with (pf := pf1)...
    specialize IHTC with (K := (K,, X0 =: typ_mu t0 T0 @ pf1)).
    eapply IHTC with (X := X) (T := T);
      try eauto.
    eapply nin_remove...
    unfold fvP in CLS;
      fold fvP in CLS.
    erewrite extend_swap...
    Unshelve.
    eapply diff_fresh...
  - simpl in CLS;
      econstructor;
      unfold extend in H...
    case_eq (process_var_beq X X0);
      introv ABS;
      try rewrite process_var_beq_eq in *;
      intuition;
      try rewrite ABS in *...
  - econstructor;
      unfold fvP in *;
      fold fvP in *;
      try eapply not_in_app_and in CLS;
      intuition...
  - econstructor;
      unfold fvP in *;
      fold fvP in *;
      try eapply not_in_app_and in CLS;
      intuition...   
Qed.

Lemma types_strengthP G K Q X T R pf:
  closedP Q ->
  types G (K,, X =: T @ pf) Q R->
  types G K Q R.
Proof with eauto using types_nin_strength.
  introv CLS TC.
  destruct CLS as [_ CLS].
  assert (~ In X (fvP Q)).
  rewrite CLS...
  eapply types_nin_strength...
Qed.

(** Substitution lemma, processes *)
Lemma types_substP P Q T U G K X pf:
  closedP Q ->
  disjoint (bv P) (bv Q) ->
  disjoint (bvP P) (bvP Q) ->
  types G (K,, X =: T @ pf) P U ->
  types G K Q T -> 
  types G K (substP P Q X) U.
Proof
  with
  eauto
  using
  bv_sum_l,
    bv_sum_r,
    in_eq,
    types_weakTE,
    types_weakPE,
    disjoint_l_cons,
    disjoint_r_cons,
    disjoint_app_l,
    disjoint_app_r,
    consistent_evar_beq,
    consistent_process_var_beq,
    fresh_cons,
    extend_swap,
    types_strengthP.
  
  introv CLS DIS DIS2 TYP1 TYP2.
  gen X T G K U Q.
  dependent induction P;
    intros;
    unfold substP;
    fold substP...
  - remember e as x.
    subst e.
    
    dependent induction TYP1...
    eapply t_input with (pf := pf0)...
    eapply IHP, types_weakTE...
    all:
      unfold bv in DIS; fold bv in DIS;
      eapply disjoint_l_cons...
    
  - remember e as x.
    subst e.
    dependent induction TYP1...
    
  - dependent induction TYP1;
      unfold substP;
      fold substP;
      econstructor...
  - dependent induction TYP1;
      econstructor...
  - case_eq (process_var_beq X p).
    intros BEQ.
    rewrite process_var_beq_eq in BEQ.
    subst p.
    inverts TYP1 as EN2.
    assert (T = typ_mu t0 T0).
    unfold extend in EN2;
      rewrite process_var_beq_true in EN2;
      inv EN2...
    subst...
    intros BNEQ.
    inverts TYP1 as EN2.
    unfold extend in EN2;
      rewrite BNEQ in EN2;
      inv EN2...
  - inv TYP1...
  - assert (DIFF: X <> p).
    inv TYP1...
    assert (J1 := pf0).
    unfold fresh,extend in J1.
    case_eq(process_var_beq X p);
      intros ABS;
      rewrite ABS in *;
      try discriminate...
    intros ABS2; subst.
    rewrite process_var_beq_true in *;
      try discriminate.
    assert (In p (bvP (proc_mu p P))).
    unfold bvP; fold bvP...
    
    dependent induction TYP1;
      unfold substP;
      fold substP...
    assert (pf1: fresh K p)...
    eapply t_fold with (pf := pf1)...
    
    assert (J1 := pf0).
    unfold fresh,extend in J1.
    case_eq(process_var_beq X p);
      intros ABS;
      rewrite ABS in *;
      try discriminate...

    clear IHTYP1.
    remember ((K,, X =: T @ pf),, p =: typ_mu t0 T0 @ pf0) as K1.
    assert (pf01: fresh (K,, p =: typ_mu t0 T0 @ pf1) X).
    eapply diff_fresh...
    
    assert
      (EQ: K1 =
             (K,, p =: typ_mu t0 T0 @ pf1),, X =: T @ pf01).         
    subst K1...
    
    specialize IHP
      with
      (Q := Q)
      (U := (t0 £ T0))
      (T := T)
      (pf := pf01).
    eapply IHP; clear IHP...

    rewrite <-EQ...
    
    eapply types_weakPE with
      (x := p)
      (s := (typ_mu t0 T0))
      in TYP2...
    
    all:
      unfold bvP in DIS2;
      fold bvP in DIS2;
      eapply disjoint_l_cons in DIS2;
      intuition.

    eapply types_weakPE...
    Unshelve.
    eapply fresh_cons...
Qed.

Lemma swap_disjoint_domain {A B} (d1 : partial_fun A B) d2 :
  disjoint_domain d1 d2 ->
  disjoint_domain d2 d1.
Proof with eauto.
  introv DIS.
  unfold disjoint_domain in *;
    intros x.
  specialize DIS with x;
    destruct DIS as [DIS1 DIS2].
  split;
    introv SOME.
  eapply DIS2...
  eapply DIS1...
Qed.

Lemma update_disjoint_domain_l {A B} (d1 : partial_fun A B) d2 beq x t (pf: forall p1 p2, beq p1 p2 = true <-> p1 = p2):
  disjoint_domain d1 d2 ->
  d1 x <> None ->
  disjoint_domain (update beq d1 x t) d2.
Proof with eauto.
  introv DIS SOME.
  unfold disjoint_domain in *;
    intros y;
    split;
    introv K.
  specialize DIS with y;
    destruct DIS as (DIS1 &DIS2).
  case_eq (beq x y);
    introv BEQ;
    try rewrite pf in BEQ;
    subst...
  unfold update in K.
  rewrite BEQ in K...

  specialize DIS with y;
     destruct DIS as (DIS1 &DIS2).
  unfold update.
  case_eq (beq x y);
    introv BEQ;
    try rewrite pf in BEQ;
    subst...
  intuition.
Qed.
  
Lemma update_disjoint_domain_r {A B} (d1 : partial_fun A B) d2 beq x t (pf: forall p1 p2, beq p1 p2 = true <-> p1 = p2):
  disjoint_domain d1 d2 ->
  d2 x <> None ->
  disjoint_domain d1 (update beq d2 x t).
Proof
  with
  eauto
  using
  swap_disjoint_domain,
    update_disjoint_domain_l.
  introv DIS SOME...
Qed.

Lemma swap_cat {A B} (d1 : partial_fun A B) d2 pf:
  d1 @@ d2 @pf =
    d2 @@ d1 @ (swap_disjoint_domain d1 d2 pf).
Proof with eauto.
  remember (swap_disjoint_domain d1 d2 pf) as pf1.
  apply functional_extensionality.
  intros.
  unfold cat.
  unfold disjoint_domain in *.
  case_eq (d1 x). intros.
  assert (K := pf).
  specialize K with x.
  assert (EQ: d2 x = None).
  eapply K;
    try rewrite H;
    try discriminate...
  rewrite EQ...
  case_eq (d2 x); introv...
Qed.

Lemma swap_partition: forall d1 d2 ld pf,
    partition (d1 @@ d2 @pf) ld ->
    partition
      (d2 @@ d1 @ (swap_disjoint_domain d1 d2 pf)) ld.
Proof with eauto.
  intros.
  rewrite swap_cat...
Qed.

Lemma types_struct G H M1 M2 U:
  types_session G H M1 U ->
  proc_equiv M1 M2 ->
  types_session G H M2 U.
Proof with eauto.
  introv TC ST.
  destruct ST...
  inv TC...
  rewrite swap_cat...
  econstructor...
  apply swap_partition...
Qed.


Lemma ndm_sum_l r p1 p2:
  wfm (single_session (r, proc_sum p1 p2)) ->
  wfm (single_session (r, p1)).
Proof with eauto.
  introv WF.
  unfold wfm,wfp,ndp,ndP,bv,bvP in *;
    fold bv in *;
    fold bvP in *;
    repeat rewrite no_dup_iff in *;
    intuition.
Qed.

Lemma ndm_sum_r r p1 p2:
  wfm (single_session (r, proc_sum p1 p2)) ->
  wfm (single_session (r, p2)).
Proof with eauto.
  introv WF.
  unfold wfm,wfp,ndp,ndP,bv,bvP in *;
    fold bv in *;
    fold bvP in *;
    repeat rewrite no_dup_iff in *;
    intuition.
Qed.

Lemma proc_equiv_single_inv M1 M2:
  proc_equiv (single_session M1) M2 ->
  M2 = (single_session M1).
Proof with eauto.
  introv PE.
  dependent induction PE...
Qed.

Lemma lts_proc_input p q r l1 l2 x s v Q M:
  lts
    (single_session (p, proc_input q l1 x s Q))
    (ainput r l2 v) M ->
  q = r /\ l1 = l2.
Proof with eauto using proc_equiv_single_inv.
  introv LTS.
  dependent induction LTS...
Qed.

Lemma lts_proc_output p q r l1 l2 x s v Q M:
  lts
    (single_session (p, proc_output q l1 x s Q))
    (aoutput r l2 v) M ->
  q = r /\ l1 = l2.
Proof with eauto using proc_equiv_single_inv.
  introv LTS.
  dependent induction LTS...
Qed.

Lemma ndm_par_l M1 M2:
  wfm (parallel_session M1 M2) ->
  wfm M1.
Proof with eauto.
  introv WF.
  induction M1, M2;
    unfold wfm,wfp,ndp,ndP,bv,bvP in *;
    fold bv in *;
    fold bvP in *;
    repeat rewrite no_dup_iff in *;
    intuition.
Qed.

Lemma ndm_par_r M1 M2:
  wfm (parallel_session M1 M2) ->
  wfm M2.
Proof with eauto.
  introv WF.
  induction M1, M2;
    unfold wfm,wfp,ndp,ndP,bv,bvP in *;
    fold bv in *;
    fold bvP in *;
    repeat rewrite no_dup_iff in *;
    intuition.
Qed.

Lemma removev_inj  f l x:
  injective f ->
  removev (f x) (map f l) =
    map f (removev x l).
Proof with eauto.
  introv INJ.
  induction l...
  rewrite map_cons.
  unfold removev; fold removev.
  case_eq (evar_beq (f x) (f a));
    introv EQ.
  rewrite evar_beq_eq in *.
  assert (EQ2: x = a)...
  rewrite <-evar_beq_eq in EQ2;
    rewrite EQ2...
  case_eq (evar_beq x a);
    intros ABS;
    try rewrite ABS;
    try rewrite map_cons, IHl...
  rewrite evar_beq_eq in *;
    subst;
    rewrite evar_beq_true in *;
    discriminate.
Qed.

Lemma removeV_inj  f l x:
  injective f ->
  removeV (f x) (map f l) =
    map f (removeV x l).
Proof with eauto.
  introv INJ.
  induction l...
  rewrite map_cons.
  unfold removeV; fold removeV.
  case_eq (process_var_beq (f x) (f a));
    introv EQ.
  rewrite process_var_beq_eq in *.
  assert (EQ2: x = a)...
  rewrite <-process_var_beq_eq in EQ2;
    rewrite EQ2...
  case_eq (process_var_beq x a);
    intros ABS;
    try rewrite ABS;
    try rewrite map_cons, IHl...
  rewrite process_var_beq_eq in *;
    subst;
    rewrite process_var_beq_true in *;
    discriminate.
Qed.

Open Scope nat.
Lemma add_n_injective : forall n p M,
    n + M = p + M -> n = p.
Proof.
  intros; induction M; lia.
Qed.

Lemma shiftv_injective M : injective (shiftv M).
Proof with eauto using add_n_injective.
  unfold injective, shiftv;
    intros;
    destruct x, y;
    inv H...
Qed.

Lemma shiftV_injective M : injective (shiftV M).
Proof with eauto using add_n_injective.
  unfold injective, shiftV;
    intros;
    destruct x, y;
    inv H...
Qed.

Lemma shift_fv M P:
  fv (shiftP M P) = List.map (shiftv M) (fv P).
Proof
  with
  eauto
  using
  shiftv_injective,
    removev_inj.
  
  unfold closedP in *.
  dependent induction P;
    unfold shiftP;
    fold shiftP;
    simpl;
    try rewrite IHP...
  - destruct e...
  - rewrite IHP1, IHP2, map_app...
  - rewrite IHP1, IHP2, map_app...
Qed.

Lemma shift_fvP M P:
  fvP (shiftP M P) = List.map (shiftV M) (fvP P).
Proof
  with
  eauto
  using
  shiftV_injective,
    removeV_inj.
  
  unfold closedP in *.
  dependent induction P;
    unfold shiftP;
    fold shiftP;
    simpl;
    try rewrite IHP...
  - rewrite IHP1, IHP2, map_app...
  - rewrite IHP1, IHP2, map_app...
Qed.

Lemma shift_bv M P:
  bv (shiftP M P) = List.map (shiftv M) (bv P).
Proof
  with
  eauto
  using
  shiftv_injective,
    removev_inj.
  
  unfold closedP in *.
  dependent induction P;
    unfold shiftP;
    fold shiftP;
    simpl;
    try rewrite IHP...
  - rewrite IHP1, IHP2, map_app...
  - rewrite IHP1, IHP2, map_app...
Qed.

Lemma shift_bvP M P:
  bvP (shiftP M P) = List.map (shiftV M) (bvP P).
Proof
  with
  eauto
  using
  shiftV_injective,
    removeV_inj.
  
  unfold closedP in *.
  dependent induction P;
    unfold shiftP;
    fold shiftP;
    simpl;
    try rewrite IHP...
  - rewrite IHP1, IHP2, map_app...
  - rewrite IHP1, IHP2, map_app...
Qed.

Lemma shift_closed M P:
  closedP P->
  closedP (shiftP M P).
Proof with eauto using shift_fv, shift_fvP.
  introv CLS.
  unfold closedP in *;
    destruct CLS as [CLS1 CLS2];
    split;
    try erewrite shift_fv;
    try erewrite shift_fvP;
    try erewrite CLS1;
    try erewrite CLS2...
Qed.

Definition split_max :=  Nat.max_lub_lt_iff.

Lemma shiftv_nin x M l:
  maxL (seedsv l) < M ->
  ~In (shiftv M x) l.
Proof with eauto.
  introv LT.
  dependent induction l;
    intros ABS;
    try inv ABS;
    unfold seedsv in *;
    fold seedsv in *;
    rewrite map_cons in LT...
  simpl in LT.
  destruct x;
    unfold shiftv, seeds_evar in LT.
  eapply split_max in LT as [K _];
    lia.
  unfold maxL in LT; fold maxL in LT;
    eapply split_max in LT as [_ K].
  intuition.
Qed.

Lemma shiftV_nin x M l:
  maxL (seedsV l) < M ->
  ~In (shiftV M x) l.
Proof with eauto.
  introv LT.
  dependent induction l;
    intros ABS;
    try inv ABS;
    unfold seedsV in *;
    fold seedsV in *;
    rewrite map_cons in LT...
  simpl in LT.
  destruct x;
    unfold shiftV, seeds_pvar in LT.
  eapply split_max in LT as [K _];
    lia.
  unfold maxL in LT; fold maxL in LT;
    eapply split_max in LT as [_ K].
  intuition.
Qed.

Lemma maxL_app l1 l2 M:
  maxL (l1 ++ l2) <M ->
  maxL l1 < M /\
    maxL l2 < M.
Proof with eauto.
  introv LT.
  induction l1, l2;
    split;
    simpl in *;
    try lia...
Qed.  

Definition shifter {A} f (l : list A) :=
  forall x,
    In x l ->
    ~ In (f x) l.

Lemma shifter_cons {A} f a (l : list A):
  shifter f (a :: l) ->
  shifter f l.
Proof with eauto.
  introv SH.
  unfold shifter;
    introv IN ABS.
  assert (~In (f x) (a :: l)).
  eapply SH; right...
  eapply nin_cons in H;
    intuition.
Qed.

Lemma disjoint_map {A} f (l : list A):
  shifter f l ->
  disjoint l (map f l).
Proof with eauto using shifter_cons, in_eq.
  intros NIN.
  induction l...
  simpl...
  eapply disjoint_cons_l;
    split...
  rewrite map_cons.
  eapply disjoint_cons_r;
    split...
  assert (~In (f a) (a :: l)).
  eapply NIN...
  eapply nin_cons in H;
    intuition.

  assert (SH: ~In (f a) (a :: l)).
  eapply NIN...
  rewrite map_cons;
    intros ABS;
    inv ABS...
  rewrite H in *;
    intuition.
  eapply in_map_iff in H;
    unpack;
    subst.
  assert (~ In (f x) (f x :: l)).
  eapply NIN; right...
  intuition.
Qed.

Lemma maxL_absurd n M l:
  maxL l < M ->
  In (n + M) l ->
  False.
Proof with eauto.
  introv LT ABS.
  induction l;
    try inv ABS;
    simpl in *;
    intuition.
Qed.  

Lemma shifter_shiftv l M:
  maxL (seedsv l) < M ->
  shifter (shiftv M) l.
Proof with eauto using maxL_absurd.
  introv LT.
  induction l;
    unfold shifter;
    introv IN ABS;
    try inv ABS;
    try destruct x;
    unfold shiftv, seedsv in *...
  rewrite map_cons in LT.
  unfold seeds_evar, maxL in LT;
    fold maxL in LT.
  eapply split_max in LT; intuition.
  rewrite map_cons in LT.
  unfold maxL in LT; fold maxL in LT.
  eapply split_max in LT; intuition.
  assert (ABS: In (n + M) (map seeds_evar l)).
  eapply in_map with (f := seeds_evar) in H...
  eapply maxL_absurd...
Qed.

Lemma shifter_shiftV l M:
  maxL (seedsV l) < M ->
  shifter (shiftV M) l.
Proof with eauto using maxL_absurd.
  introv LT.
  induction l;
    unfold shifter;
    introv IN ABS;
    try inv ABS;
    try destruct x;
    unfold shiftV, seedsV in *...
  rewrite map_cons in LT.
  unfold seeds_pvar, maxL in LT;
    fold maxL in LT.
  eapply split_max in LT; intuition.
  rewrite map_cons in LT.
  unfold maxL in LT; fold maxL in LT.
  eapply split_max in LT; intuition.
  assert (ABS: In (n + M) (map seeds_pvar l)).
  eapply in_map with (f := seeds_pvar) in H...
  eapply maxL_absurd...
Qed.

Lemma shift_disjoint M P :
  max_seed P < M ->
  disjoint (bv P) (bv (shiftP M P)).
Proof
  with
  eauto
  using
  shiftv_nin,
    maxL_app,
    shifter_shiftv.
  introv LT.
  rewrite shift_bv.
  apply disjoint_map;
    intros;
    unfold max_seed, seeds in LT;
    eapply  maxL_app in LT as [K _]...
Qed.

Lemma shift_disjointP M P :
  max_seed P < M ->
  disjoint (bvP P) (bvP (shiftP M P)).
Proof
  with
  eauto
  using
  shiftV_nin,
    maxL_app,
    shifter_shiftV.
  introv LT.
  rewrite shift_bvP.
  apply disjoint_map;
    intros;
    unfold max_seed, seeds in LT;
    eapply  maxL_app in LT as [_ K]...
Qed.

Definition shiftTE (M : nat) (g : typ_env) :=
  fun y =>
    match y with evar_var n =>
                   if n <? M
                   then
                     raise
                   else
                     let m := n - M
                     in
                     g (evar_var m)
    end.

Definition shiftPE (M : nat) (g : proc_env) :=
  fun y =>
    match y with pvar n =>
                   if n <? M
                   then
                     raise
                   else
                     let m := n - M
                     in
                     g (pvar m)
    end.

Lemma shiftTE_pres M h x t :
  h (evar_var x) = t ->
  (shiftTE M h) (evar_var (x + M)) = t.
Proof with eauto using Nat.ltb_irrefl.
  introv EQ.
  unfold shiftTE.
  assert (NEG: x + M < M -> False).
  lia.
  case_eq (x + M <? M); intros ABS...
  rewrite Nat.ltb_lt in ABS;
    contradiction.
  erewrite Nat.add_sub...
Qed.

Lemma shiftPE_pres M h x t :
  h (pvar x) = t ->
  (shiftPE M h) (pvar (x + M)) = t.
Proof with eauto using Nat.ltb_irrefl.
  introv EQ.
  unfold shiftPE.
  assert (NEG: x + M < M -> False).
  lia.
  case_eq (x + M <? M); intros ABS...
  rewrite Nat.ltb_lt in ABS;
    contradiction.
  erewrite Nat.add_sub...
Qed.

Lemma shiftPE_fresh h n M:  
  fresh h (pvar n) ->
  fresh (shiftPE M h) (pvar (n + M)).
Proof with eauto.
  introv FH;
    unfold fresh, shiftPE in *;
    intros.
  case_eq ( n + M <? M); intros ABS...
  erewrite Nat.add_sub...
Qed.

Lemma shiftTE_fresh h n M:  
  fresh h (evar_var n) ->
  fresh (shiftTE M h) (evar_var (n + M)).
Proof with eauto.
  introv FH;
    unfold fresh, shiftTE in *;
    intros.
  case_eq ( n + M <? M); intros ABS...
  erewrite Nat.add_sub...
Qed.

Lemma shiftPE_extend M h n t pf pf1:
  shiftPE M (h,, pvar n =: t @ pf) =
    shiftPE M h,, pvar (n + M) =: t @ pf1.
Proof with eauto using  Nat.sub_add.
  unfold shiftPE, extend.
  apply functional_extensionality; intros.
  destruct x...
  case_eq (n0 <? M); intros ABS...
  case_eq (process_var_beq (pvar (n + M)) (pvar n0));
    intros ABS2...
  rewrite process_var_beq_eq in *; inv ABS2...
  assert (n + M >= M).
  lia.
  rewrite Nat.ltb_lt in *.
  lia.
  case_eq  (process_var_beq (pvar n) (pvar (n0 - M)));
    intros EQ1...
  case_eq (process_var_beq (pvar (n + M)) (pvar n0));
    intros EQ2...
  - rewrite process_var_beq_eq in EQ1;
      inv EQ1...
    assert (K :=  Nat.add_sub).
    specialize K with n0 M.
    Open Scope nat.
    assert (n0 -M + M = n0).
    rewrite <-K at 2.
    rewrite <-Nat.add_sub_assoc,Nat.sub_diag,Nat.add_0_r.
    eapply Nat.sub_add...
    rewrite Nat.ltb_ge in *.
    lia.
    lia.
    assert (pvar ((n0 - M) + M) = pvar n0)...
    rewrite <-process_var_beq_eq in *;
      rewrite EQ2 in *;
      discriminate.
  -  case_eq (process_var_beq (pvar (n + M)) (pvar n0));
       intros EQ2...
     rewrite process_var_beq_eq in *.
     inv EQ2.
     assert ((n + M) - M = n).
     rewrite <-Nat.add_sub_assoc,Nat.sub_diag,Nat.add_0_r...
     rewrite H in *.
     rewrite process_var_beq_true in *;
       discriminate.
Qed.

Lemma shiftTE_extend M h n t pf pf1:
  shiftTE M (h,, evar_var n -: t @ pf) =
    shiftTE M h,, evar_var (n + M) -: t @ pf1.
Proof with eauto using  Nat.sub_add.
  unfold shiftTE, extend.
  apply functional_extensionality; intros.
  destruct x...
  case_eq (n0 <? M); intros ABS...
  case_eq (evar_beq (evar_var (n + M)) (evar_var n0));
    intros ABS2...
  rewrite evar_beq_eq in *; inv ABS2...
  assert (n + M >= M).
  lia.
  rewrite Nat.ltb_lt in *.
  lia.
  case_eq  (evar_beq (evar_var n) (evar_var (n0 - M)));
    intros EQ1...
  case_eq (evar_beq (evar_var (n + M)) (evar_var n0));
    intros EQ2...
  - rewrite evar_beq_eq in EQ1;
      inv EQ1...
    assert (K :=  Nat.add_sub).
    specialize K with n0 M.
    Open Scope nat.
    assert (n0 -M + M = n0).
    rewrite <-K at 2.
    rewrite <-Nat.add_sub_assoc,Nat.sub_diag,Nat.add_0_r.
    eapply Nat.sub_add...
    rewrite Nat.ltb_ge in *.
    lia.
    lia.
    assert (evar_var ((n0 - M) + M) = evar_var n0)...
    rewrite <-evar_beq_eq in *;
      rewrite EQ2 in *;
      discriminate.
  -  case_eq (evar_beq (evar_var (n + M)) (evar_var n0));
       intros EQ2...
     rewrite evar_beq_eq in *.
     inv EQ2.
     assert ((n + M) - M = n).
     rewrite <-Nat.add_sub_assoc,Nat.sub_diag,Nat.add_0_r...
     rewrite H in *.
     rewrite evar_beq_true in *;
       discriminate.
Qed.

Lemma shift_stypes M G e T:
  stypes G e T ->
  stypes
    (shiftTE M G)
    (shiftE M e)
    T.
Proof
  with
  eauto
  using
  shiftTE_pres,
    shiftTE_pres,
    shiftTE_fresh.
  introv TC.
  gen M.
  dependent induction TC;
    intros;
    try destruct x;
    unfold shiftE;
    fold shiftE...
Qed.  

Lemma shift_types M G H P T:
  types G H P T ->
  types
    (shiftTE M G)
    (shiftPE M H)
    (shiftP M P)
    T.
Proof
  with
  eauto
  using
  shiftTE_pres,
    shiftPE_pres,
    shiftPE_fresh,
    shiftTE_pres,
    shiftTE_fresh,
    shift_stypes.
  
  introv TC.
  gen M.
  dependent induction TC;
    intros;
    try
      match goal with
      | _ : _ |- types _ _ _ (typ_mu _ _) =>
          unfold shiftP;
          fold shiftP;
          try destruct X;
          unfold shiftV;
          eauto
      | _ : _ |- types _ _ _ (typ_input _ _ _ _) =>
          unfold shiftP;
          fold shiftP;
          unfold shiftv;
          fold shiftv;
          destruct x;
          eauto
      | _ =>
          eauto
      end.
  - Case t_fold.
    assert (pf1 : fresh (shiftPE M h) (pvar (n + M)))...
    eapply t_fold with pf1...
    erewrite <-shiftPE_extend...
  - Case t_var.
    econstructor...
  - Case t_input.
    assert (pf1 : fresh (shiftTE M g) (evar_var (n + M)))...
    eapply t_input with pf1...
    erewrite <-shiftTE_extend...
  - Case t_output.
    econstructor...
  - Case t_branch.
    econstructor...
  - Case t_select_l.
    econstructor...
  - Case t_select_r.
    eapply t_select_r...
  - Case t_conditional.
    econstructor...
Qed.

Lemma shift_empty_env M:
  shiftTE M empty_env = empty_env.
Proof with eauto.
  unfold shiftTE, empty_env.
  apply functional_extensionality;
    intros;
    try destruct x;
    try destruct (n<? M)...
Qed.

Lemma shift_empty_penv M:
  shiftPE M empty_penv = empty_penv.
Proof with eauto.
  unfold shiftPE, empty_env.
  apply functional_extensionality;
    intros;
    try destruct x;
    try destruct (n<? M)...
Qed.

Lemma  closed_cond e P1 P2:
  closedP (proc_conditional e P1 P2) ->
  closedP P1 /\ closedP P2.
Proof with eauto using app_eq_nil.
  introv CLS.
  unfold closedP in *.
  unfold fv, fvP in CLS;
    fold fv in *;
    fold fvP in *;
    intuition;
    try apply app_eq_nil in H;
    try eapply app_eq_nil in H0;
    intuition.
Qed.


(** I/O Subject reduction *)
Lemma io_subject_reduction U p P a P' U':
  let M := single_session (p, P)
  in
  let M' := single_session (p, P')
  in
  closedS M ->
  wfm M ->
  wf U ->
  types empty_env empty_penv P U  ->
  lts M a M' ->
  typ_lts U a U' ->
  types empty_env empty_penv P' U'.
Proof
  with
  eauto
  using
  substitution,
    wf_input, wf_output, 
    wf_substT,
    wf_sum_out_false_l, wf_sum_inp_false_l,
    wf_sum_out_false_r, wf_sum_inp_false_r,
    lts_input_output_false,
    lts_typ_mu_output_false, lts_typ_mu_input_false,
    lts_input_typ, lts_output_typ,
    stypes_empty,
    types_struct,
    ndm_sum_l, ndm_sum_r,
    ndm_par_l, ndm_par_r,
    process_var_beq_true,
    lts_proc_input, lts_proc_output,
    shift_closed, shift_disjoint,
    shift_disjointP, shift_types,
    disjoint_l_cons,
    closed_cond.
  
  introv CLS WFM WF TS LTS ELTS.
  gen U U'.
  dependent induction LTS; intros;
    remember empty_env as G;
    remember empty_penv as K;
    assert (WFM2 := WFM);
    try destruct WFM2 as [NDP NDM]...

  - Case r_input.

    try destruct WF as [NDP NDM].
    inverts TS as TC1.
    inverts ELTS as E1.
    assert (ST : stypes G (expr_val v) s)...
    
  - Case r_output.

    
    dependent induction TS;
      inv ELTS...
    
    eapply IHTS...

    eapply wf_sum in WF as (WF1 &WF2)...

    assert False...
    contradiction.
    
    assert False...
    contradiction.

    eapply IHTS...
    eapply wf_sum in WF as (WF1 &WF2)...

  - Case r_sum.

    try destruct WF as [NDP NDM].
    move LTS at bottom.
    inverts TS as TC1 TC2.

    assert (closedS (single_session (p, proc_input p0 l0 x s P))).
    inverts CLS as F1 F2; econstructor...
    eapply fv_sum in F1; intuition.
    eapply fvP_sum in F2; intuition.
    inv LTS.
    
    * inverts ELTS as E1...
      inverts E1 as SUMRED...
      
      ** eapply IHLTS with
           (U := typ_input p0 l0 s0 U')...        
         eapply wf_sum in WF.
         intuition.
      **
        eapply IHLTS with (U := typ_sum t0 t3)...
        eapply wf_sum in WF.
        intuition.
      **
        eapply IHLTS with (U := typ_sum t0 t3)...
        eapply wf_sum in WF.
        intuition.
      ** 
        assert False...
        contradiction.

    * inverts ELTS as E1.
      
      **  assert (EQ: p0 = p1 /\ l0 = l1).
          inv H0...
          destruct EQ. subst.
          inverts E1 as SUMRED...
          ***
            eapply IHLTS with
              (U := typ_input p1 l1 s0 U')...
            eapply wf_sum in WF.
            intuition.
          ***
            eapply IHLTS with (U := typ_sum t0 t3)...
            eapply wf_sum in WF.
            intuition.
          ***
            eapply IHLTS with (U := typ_sum t0 t3)...
            eapply wf_sum in WF.
            intuition.

      ** inv H0. inv H2. inv H1.
         assert False...
         contradiction.
         assert (EQ: p0 = p1 /\ l0 = l1).
         inv H0...
         intuition; subst.
         assert False...
         contradiction.

      ** inv H0. 
         assert False...
         contradiction.

      ** inv H0.
         assert False...
         contradiction.
         
  - Case r_struct.
    
    assert (closedS M1).
    inv H...
    assert (wfm M1).
    inv H...
    inv H0.
    eapply IHLTS...
    inv H...
Qed.

Lemma elts_inversion D a D':
  elts D a D' ->
  ((exists ex, a = atau (Some ex)) \/
     (exists p,
         a = aunfold p)).
Proof with eauto.
  introv ELTS.
  dependent induction ELTS...
Qed.

Lemma singleton_inv p t p1 t1 :
  singleton p t p1 = Some t1 ->
  p = p1 /\ t = t1.
Proof with eauto.
  introv EQ.
  unfold singleton, extend in *.
  case_eq (pbeq p p1);
    introv PEQ;
    rewrite PEQ in EQ;
    try inv EQ...
  rewrite participant_beq_eq in PEQ;
    subst;
    intuition.
Qed.

Lemma typ_lts_io_absurd t q1 l1 v1 q2 l2 v2 t1 t2:
  wf t ->
  typ_lts t (ainput q1 l1 v1) t1 ->
  typ_lts t (aoutput q2 l2 v2) t2 ->
  False.
Proof with eauto.
  introv WF ABS1 ABS2.
  dependent induction t...
  - inv ABS1.
  - inv ABS1.
  - destruct WF as
      ([(TB &_) | (TS &_)] &_ &_).
    eapply tbranch_output_false in ABS2;
      try contradiction...
    eapply tselect_input_false in ABS1;
      try contradiction...
  - inv ABS2.
  - inv ABS1.
  - inv ABS1.
Qed.

Lemma elts_singleton_inv p t ea d' :
  wf t ->
  elts (singleton p t) ea d' ->
  exists x t1,
    t = typ_mu x t1 /\
      ea = aunfold p/\
      d' =
        singleton p (x £ t1).
Proof with eauto.
  introv WF ELTS.
  assert (ELTS1 := ELTS).
  eapply elts_inversion in ELTS1 as [ABS | UNFOLD ];
    unpack; subst.
  - inv ELTS.
    eapply singleton_inv in H2.
    eapply singleton_inv in H4.
    intuition;
      subst.
    eapply  typ_lts_io_absurd in H0...
    contradiction.
  - inv ELTS.
    inv H0.
    exists X T...
    eapply singleton_inv in H2;
      intuition;
      subst...
    unfold singleton, extend, update.
    apply functional_extensionality; intros...
    destruct (pbeq p0 x)...
Qed.

Lemma cat_hit_left {A B} (d1 : partial_fun A B) d2 pf x t t1:
  (d1 @@ d2 @ pf) x = Some t ->
  d1 x = Some t1 ->
  t = t1.
Proof with eauto.
  introv EQ1 EQ2.
  unfold cat in *;
    rewrite EQ2 in *;
    inv EQ1...
Qed.

Lemma cat_hit_right {A B} (d1 : partial_fun A B) d2 pf x t t1:
  (d1 @@ d2 @ pf) x = Some t ->
  d2 x = Some t1 ->
  t = t1.
Proof with eauto.
  introv EQ1 EQ2.
  unfold cat in *.
  assert (EQ3: d1 x = None).
  unfold disjoint_domain in pf.
  specialize pf with x.
  intuition.
  eapply H0;
    rewrite EQ2;
    intros;
    discriminate...
  rewrite EQ3,EQ2 in *;
    inv EQ1...
Qed.

Lemma typ_input_change_payload t q l v t' v': 
  typ_lts t (ainput q l v) t' ->
  typ_lts t (ainput q l v') t'.
Proof with eauto.  
  introv LTS.
  dependent induction LTS...
Qed.

Lemma typ_output_change_payload t q l v t' v': 
  typ_lts t (aoutput q l v) t' ->
  typ_lts t (aoutput q l v') t'.
Proof with eauto.  
  introv LTS.
  dependent induction LTS...
Qed.

Lemma wf_reduction t a t':
  wf t ->
  typ_lts t a t' ->
  wf t'.
Proof with eauto using
           wf_substT.
  introv WF LTS.
  dependent induction LTS...
  - inv LTS...
    all:eapply wf_sum in WF as [K _]...
  - inv LTS...
    all:eapply wf_sum in WF as [_ K]...
  - inv LTS...
    all:eapply wf_sum in WF as [K _]...
  - inv LTS...
    all:eapply wf_sum in WF as [_ K]...
Qed.

Function update_partition (ld : list part_env) x t :=
  match ld with
  | [] => []
  | d :: ld' =>
      match d x  with
      | Some _ =>
          d <- x #: t :: ld'
      | None =>
          d :: update_partition ld' x t
      end
  end.

  
Lemma disjoint_incl {A}: forall (l1 l2 m : list A),
    disjoint l1 l2 ->
    incl m l2 ->
    disjoint l1 m.
Proof with eauto using in_eq.
  intros.
  dependent induction m; erewrite disjoint_commute...
  simpl...
  eapply disjoint_cons_l...
  split...
  eapply incl_app_inv with (l1 := a::nil) in H0 as [ _ K];
    erewrite disjoint_commute...
  intros ABS.
  assert (In a l2). eapply H0...
  eapply disjoint_absurd...
Qed.

Lemma participants_subst T X U: 
incl 
(parties (substT T X U))
(parties T ++ parties U).
Proof with eauto using incl_refl, incl_nil_l, 
incl_appl, incl_appr, incl_app_app, in_eq.
functional induction (substT T X U); simpl...
- 
assert (
incl
  (parties (substT U1 X T2) ++
   parties (substT U2 X T2))
   ((parties U1 ++ parties T2) ++
   (parties U2 ++ parties T2)))...
unfold incl in *; introv IN; eapply in_app_iff in IN as [L | R].
assert (In a
      ((parties U1 ++ parties T2) ++
       parties U2 ++ parties T2)).
       eapply H...
eapply in_app_iff; left... 
eapply in_app_iff in H0; intuition.
eapply in_app_iff in H1; intuition.
eapply in_app_iff in H1; intuition.
assert (In a
      ((parties U1 ++ parties T2) ++
       parties U2 ++ parties T2)).
       eapply H...
eapply in_app_iff; right... 
eapply in_app_iff in H0; intuition.
eapply in_app_iff in H1; intuition.
eapply in_app_iff in H1; intuition.
- unfold incl in *; introv IN; inv IN...
right...
- unfold incl in *; introv IN; inv IN...
right...
Qed.


Lemma participants_typ_lts_redex t1 a t2:
  typ_lts t1 a t2 ->
  incl (parties t2) (parties t1).
Proof with eauto using incl_refl.
introv LTS.
dependent induction LTS; simpl...
eapply incl_tran.
Unset Printing Notations.
eapply participants_subst...
unfold parties; fold parties... 
eapply incl_app...
right...
right...
eapply incl_appl...
eapply incl_appr...
eapply incl_appl...
eapply incl_appr...
Qed.

Lemma disjoint_domain_absurd (d1 d2 : part_env) p P:
  disjoint_domain d1 d2 ->
  d1 p <> None ->
  d2 p <> None  ->
  P.
Proof with eauto.
introv DIS SOME1 SOME2.
assert (d1 p = None).
eapply DIS...
rewrite H in *; contradiction.
Qed.


Lemma partition_cons d a ld:
  partition d (a:: ld) ->
  partition d ld.
Proof with eauto.  
  introv PAR.
  econstructor;
    intros.
  unfold sub_env;
    introv IN.
  eapply PAR;
    repeat right...
  assert (diff d1 d2 (a :: ld)).
  destruct H1 as (n1 &n2 &DIFF).
  exists (S n1) (S n2);
    rewrite nth_error_S;
    simpl;
    intuition.
  split;
  eapply PAR;
  repeat right...
Qed.

Lemma update_app d0 l1 l2 d p tp tp':
  partition d0 (l1 ++ d :: l2) ->
  d p = Some tp ->
  update_partition (l1 ++ d :: l2) p tp' =
    l1 ++ (d <- p #: tp') :: l2.
Proof with eauto using partition_cons.
introv PAR EQ.  
induction l1, l2;
  simpl;
  try rewrite EQ...
case_eq (a p);
  introv EQ2...
assert False.
eapply disjoint_domain_absurd
  with (d1 := a ) (d2 := d);
  try eapply PAR;
  try rewrite EQ;
  try rewrite EQ2;
  try discriminate...
simpl...
simpl; repeat right; eapply in_app_iff...
right; simpl...
exists 0 (S(length(l1)));
  simpl;
  intuition.
rewrite nth_error_app2;
  simpl...
assert (Datatypes.length l1 - Datatypes.length l1 = 0).
lia...
rewrite H; simpl...
contradiction.

erewrite IHl1...

case_eq (a p);
  introv EQ2...
assert False.
eapply disjoint_domain_absurd
  with (d1 := a ) (d2 := d);
  try eapply PAR;
  try rewrite EQ;
  try rewrite EQ2;
  try discriminate...
simpl...
simpl; repeat right; eapply in_app_iff...
right; simpl...
exists 0 (S(length(l1)));
  simpl;
  intuition.
rewrite nth_error_app2;
  simpl...
assert (Datatypes.length l1 - Datatypes.length l1 = 0).
lia...
rewrite H; simpl...
contradiction.

erewrite IHl1...
Qed.


Lemma update_app_none l1 l2 d p tp':
  d p = None ->
  exists l' l'',
  update_partition (l1 ++ d :: l2) p tp' =
    l' ++ d :: l''.
Proof with eauto.
introv NONE.
induction l1, l2...
exists ([]: list part_env)([]: list part_env); simpl;
rewrite NONE...
case_eq (o p).
introv SOME.
exists ([]: list part_env)(o<- p #: tp'::l2);simpl;
rewrite NONE, SOME... 
introv NONE1.
exists ([]: list part_env)(o::update_partition l2 p tp');simpl;
rewrite NONE, NONE1...
unpack.
assert (EQ:(a :: l1) ++ [d] = a :: l1 ++ [d])...
rewrite EQ.
case_eq (a p);
introv SOME;
unfold update_partition;
try rewrite SOME;
fold update_partition...
exists (a <- p #: tp' :: l1) ([]: list part_env)...
exists (a  :: l') l''; rewrite H...
unpack.
assert (EQ:(a :: l1) ++ d :: o :: l2 = a :: l1 ++ d:: o :: l2)...
rewrite EQ.
 case_eq (a p);
introv SOME;
unfold update_partition;
try rewrite SOME;
fold update_partition...
exists (a <- p #: tp' :: l1) (o::l2)...
exists (a  :: l') l''; rewrite H...
Qed.

Lemma update_inv_some d0 ld d p tp:
  partition d0 ld ->
  d p <> None ->
  In d (update_partition ld p tp) ->
  exists l' l'' d0,
  ld = l' ++ d0 :: l'' /\
  update_partition ld p tp =
    l' ++ d :: l'' /\
    d = d0 <- p #: tp.
Proof with eauto.
introv PAR. intros.
induction ld...
simpl in H0; inv H0.
case_eq (a p).
introv SOME.
unfold update_partition in *;
rewrite SOME in *;
fold update_partition in *...
inv H0...
exists ([]:list part_env) ld a...
assert False.
eapply disjoint_domain_absurd
with (d1 := a) (d2 := d)...
eapply PAR...
eapply in_eq...
right...
eapply In_nth_error in H1; unpack.
exists 0 (S n)...
rewrite SOME; discriminate.
contradiction.
introv NONE.
unfold update_partition in *;
rewrite NONE in *;
fold update_partition in *...
inv H0...
rewrite NONE in *; contradiction.
eapply IHld in H1...
unpack.
subst ld.
rewrite H1.
exists (a::l') l'' d1...
eapply partition_cons...
Qed.

Lemma update_inv_none d0 ld d p tp:
  partition d0 ld ->
  d p = None ->
  In d (update_partition ld p tp) ->
  exists l1 l2 l' l'',
  ld = l' ++ d :: l'' /\
  update_partition ld p tp =
    l1 ++ d :: l2.
Proof with eauto using partition_cons.
introv PAR NONE IN.
induction ld...
simpl in IN; inv IN.
case_eq (a p); introv SOME; unfold update_partition in *;
rewrite SOME in *; fold update_partition in *.
inv IN...
unfold update in NONE; rewrite participant_beq_eq_true in NONE;
try rewrite NONE in *; try discriminate.
eapply in_split in H; unpack.
subst.
exists (a <- p #: tp :: l1) l2 (a :: l1) l2...
inv IN...
exists (nil : list part_env) (update_partition ld p tp).
exists (nil : list part_env) ld...
eapply IHld in H; unpack; subst...
rewrite H0.
exists ( a :: l1) l2.
exists ( a :: l') l''...
Qed.

Lemma update_inv d ld d' x t t' y:
 partition d ld ->
 In d' (update_partition ld x t) ->
 d' y = Some t' ->
 (pbeq x y = true -> t = t') /\ 
    (pbeq x y = false -> d y = d' y).
Proof with eauto using in_eq, partition_cons.
introv PAR IN ENT.
induction ld;
assert (IN2 := IN);
simpl in IN; 
try contradiction.
case_eq (a x);
introv SOME;
rewrite SOME in *.
- 
inv IN...
*
case_eq (pbeq x y); 
introv PEQ; 
split;
introv EQ;
unfold update in ENT;
rewrite PEQ in ENT;
inv ENT;
try discriminate...
unfold update;
rewrite PEQ;
eapply PAR...
rewrite H0;
discriminate...
*
case_eq (pbeq x y); 
  introv PEQ;
  try rewrite participant_beq_eq in PEQ;
  subst...
assert (ABS:disjoint_domain a d').
eapply PAR...
repeat right...
eapply In_nth_error in H;
  unpack.
exists 0 (S n)...
assert (a y = None).
eapply ABS;
  rewrite ENT;
try discriminate...
rewrite SOME in *;
  discriminate.
rewrite PEQ in *;
  eapply IHld...
eapply in_split in H;
  unpack;
  subst.

case_eq (d' x).
introv ABS.
assert False.
eapply disjoint_domain_absurd with (d1 := a ) (d2 := d');
try rewrite SOME;
try rewrite ABS;
try discriminate...
eapply PAR...
right; erewrite in_app_iff...
exists 0 (S(length l1));
simpl;
intuition.
rewrite nth_error_app2...
assert (EQ: Datatypes.length l1 - Datatypes.length l1 = 0).
 lia.
rewrite EQ; simpl...
contradiction.

introv NONE.
eapply update_app_none in NONE.
unpack.
erewrite H...
eapply in_app_iff; right...

- inv IN...
case_eq (pbeq x y); 
introv PEQ;
try rewrite participant_beq_eq in PEQ;
subst;
rewrite ENT in *;
try discriminate...
split; intros; try discriminate... 
rewrite <-ENT; eapply PAR...
rewrite ENT; discriminate.
Qed.


Lemma update_ntherror_none d0 ld x t n d:
partition d0 ld ->
nth_error (update_partition ld x t) n = Some d ->
d x = None ->
nth_error ld n = Some d.
Proof with eauto using partition_cons.
introv PAR NTH NONE.
gen n.
induction ld; intros...
case_eq (a x);
introv SOME;
unfold update_partition in NTH;
rewrite SOME in NTH;
fold update_partition in *.
destruct n.
simpl in NTH; inv NTH.
unfold update in NONE; 
rewrite participant_beq_eq_true in NONE; discriminate.
simpl in *...
destruct n.
simpl in NTH; inv NTH.
simpl...
simpl in NTH...
Qed.


Lemma update_cons_idem d a x t ld :
partition d (a :: ld) ->
a x <> None ->
update_partition ld x t = ld.
Proof with eauto using in_eq.
introv PAR SOME.
induction ld...
case_eq (a0 x);
introv SOME0...
assert False.
eapply disjoint_domain_absurd with (d1 := a) (d2 := a0)...
eapply PAR...
right...
exists 0 1...
rewrite SOME0; discriminate...
contradiction.
unfold update_partition; 
rewrite SOME0;
fold update_partition in *.
rewrite IHld...
econstructor; intros...
eapply PAR...
inv H...
repeat right...
inv H; inv H0...

- destruct H1 as (n1 &n2 &IN1 &IN2 &DIFF).
destruct n1, n2; try contradiction.

simpl in *.
eapply disjoint_domain_absurd with (d1 := d2) (d2 := d2)...
eapply PAR...
exists 0 (S (S (n2))); simpl; intuition...

simpl in *.
eapply disjoint_domain_absurd with (d1 := d2) (d2 := d2)...
eapply PAR...
exists 0 (S (S (n1))); simpl; intuition...

simpl in *.
split; eapply PAR...
exists (S (S n1)) (S (S n2)); simpl; intuition...
exists (S (S n1)) (S (S n2)); simpl; intuition...

- destruct H1 as (n1 &n2 &IN1 &IN2 &DIFF).
destruct n1, n2; try contradiction;
simpl in *.
eapply PAR...
repeat right...
exists 0 (S (S n2)); simpl; intuition...
inv IN2.
eapply disjoint_domain_absurd with (d1 := d2) (d2 := d2)...
eapply PAR...
exists 0 (S (S (n1))); simpl; intuition...
eapply PAR...
repeat right...
exists (S (S n1)) (S (S n2)); simpl; intuition...

-  destruct H1 as (n1 &n2 &IN1 &IN2 &DIFF).
destruct n1, n2; try contradiction;
simpl in *.
inv IN1.
eapply disjoint_domain_absurd with (d1 := d1) (d2 := d1)...
eapply PAR...
exists 0 (S (S n2))...
eapply PAR...
repeat right...
exists (S (S n1)) 0; simpl; intuition...
eapply PAR...
repeat right...
exists (S (S n1)) (S (S n2)); simpl; intuition...

- eapply PAR; repeat right...
destruct H1 as (n1 &n2 &IN1 &IN2 &DIFF).
destruct n1, n2; try contradiction;
simpl in *.
inv IN1.
exists 0 (S (S n2))...
inv IN2.
exists (S (S n1)) 0; simpl; intuition...
exists (S (S n1)) (S (S n2)); simpl; intuition...
Qed.  

Lemma update_partition_app2 d l' d0 l'' x t0:
partition d (l' ++ d0 :: l'') ->
update_partition (l' ++ d0 :: l'') x t0 =
     l' ++ d0 <- x #: t0 :: l'' ->
     d0  x<> None.
Proof with eauto using partition_cons.
introv PAR EQ.
gen d0 x t0;
induction l', l''; 
intros; 
simpl in *; introv NONE...
  - try rewrite NONE in *;
  try inv EQ;
  try rewrite H0 in *;
  try unfold update in *;
  try rewrite participant_beq_eq_true in *;
  try discriminate...
  - try rewrite NONE in *;
  try inv EQ;
  try rewrite H0 in *;
  try unfold update in *;
  try rewrite participant_beq_eq_true in *;
  try discriminate...
  - case_eq (a x); introv SOME; 
  rewrite SOME in *;
  inv EQ...
  assert (d0 x <> None).
  eapply IHl' with (t0 := t0)...
  eapply app_inv_head in H1.
  inv H1.
  assert (d0 x = Some t0).  
  rewrite H2; unfold update. 
  rewrite participant_beq_eq_true...
  rewrite NONE in *; discriminate.
  rewrite NONE in *; contradiction.
  assert (d0 x <> None).
  eapply IHl' with (t0 := t0)...
  rewrite NONE in *; contradiction.
 - case_eq (a x); introv SOME; 
  rewrite SOME in *;
  inv EQ...
  assert (d0 x <> None).
  eapply IHl' with (t0 := t0)...
  eapply app_inv_head in H1.
  inv H1.
  assert (d0 x = Some t0).  
  rewrite H2; unfold update. 
  rewrite participant_beq_eq_true...
  rewrite NONE in *; discriminate.
  rewrite NONE in *; contradiction.
  assert (d0 x <> None).
  eapply IHl' with (t0 := t0)...
  rewrite NONE in *; contradiction.
Qed. 
  
  
  
  
  
Lemma partition_update_partition t0 act d ld x t:
    typ_lts t0 act t ->
    d x = Some t0 ->  
    partition d ld ->
    partition (d <- x #: t) (update_partition ld x t).
Proof
  with
  eauto
  using 
  in_eq,
  partition_cons.
  
introv LTS DEQ PAR.
econstructor.
- introv IN.  
  gen d' x t t0 d act.
  dependent induction ld; intros...
  simpl in IN; inv IN...
  case_eq (a x).
  introv SOMEx. 
  unfold update_partition in IN;
  rewrite SOMEx in IN...
  inv IN...
  unfold sub_env; introv SOMEp.
  case_eq (pbeq x p); introv PEQ;
  unfold update in *;
  rewrite PEQ in *...
  eapply PAR...  
  * unfold sub_env; introv SOMEp.
  case_eq (pbeq x p); introv PEQ;
  unfold update in *;
  rewrite PEQ in *...
  
  rewrite participant_beq_eq in PEQ; subst.
  assert False.
  eapply disjoint_domain_absurd
  with (d1 := a) (d2 := d')...
  eapply PAR...
  repeat right...
  eapply In_nth_error in H.
  unpack.
  exists 0 (S n)...
  rewrite SOMEx; discriminate.
  contradiction.
  
  eapply PAR;
  repeat right...
  
  * introv NONE.
    unfold update_partition in IN;
    rewrite NONE in IN;
    fold update_partition in IN...
    inv IN...
    unfold disjoint_domain;
    introv IN...
    case_eq (pbeq x p).
    introv ABS.
    rewrite participant_beq_eq in ABS;
    subst.
    rewrite NONE in IN; contradiction.
    introv NEQ.
    unfold update; rewrite NEQ.
    eapply PAR...
    
- introv IN1 IN2 DIFF. 
split.
* gen d1 d2 x t t0 d act.
  dependent induction ld; intros...
  simpl in IN1; inv IN1...
  case_eq (a x).
  introv ENT.
  unfold update_partition in IN1, IN2, DIFF;
  rewrite ENT in *.
  inv IN1; inv IN2...
  
  ** destruct DIFF as (n1 &n2 &IN1 &IN2 &DIFF).
      destruct n1, n2; try contradiction.
        
        simpl in IN1; inv IN1.
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := a) (d2 := (a <- x #: t0))...
        eapply PAR...
        assert (IN3 := IN2).
        simpl in IN2;
        eapply nth_error_In in IN2...
        repeat right...
        exists 0 (S n2);
        simpl;
        intuition...
        rewrite ENT; discriminate...
        unfold update;
        rewrite participant_beq_eq_true;
        discriminate...
        contradiction.
        
        simpl in IN2; inv IN2.
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := a) (d2 := (a <- x #: t0))...
        eapply PAR...
        repeat right...
        simpl in IN1; eapply nth_error_In in IN1...
        exists 0 (S n1);
        simpl;
        intuition...
        rewrite ENT; discriminate...
        unfold update;
        rewrite participant_beq_eq_true;
        discriminate...
        contradiction.
        
        rewrite nth_error_S in *;
        assert (K1 := IN1).
        assert (K2 := IN2).
        simpl in K1;
        eapply nth_error_In in K1. 
        eapply PAR;
        repeat right...
        exists (S n1) (S n2);
        intuition...
        
        ** unfold disjoint_domain; intros p.
        case_eq (pbeq x p).
        introv PEQ.
        unfold update; rewrite PEQ.
        rewrite participant_beq_eq in *; subst.
        split.
        introv _.
        eapply PAR...
        repeat right...
        eapply In_nth_error in H; unpack.
        exists (S n) 0; simpl; split...
        rewrite ENT; discriminate.
        introv ABS.
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := a) (d2 := d2)...
        eapply PAR...
        repeat right...
        eapply In_nth_error in H; unpack.
        exists 0 (S n)...
        rewrite ENT; discriminate.
        contradiction.

        introv NEQ.
        unfold update; rewrite NEQ.
        eapply PAR...
        repeat right...  
        eapply In_nth_error in H; unpack.
        exists 0 (S n)...
        
        ** unfold disjoint_domain; intros p.
        case_eq (pbeq x p).
        introv PEQ.
        unfold update; rewrite PEQ.
        rewrite participant_beq_eq in *; subst.
        split.
        introv SOMEp.
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := a) (d2 := d1)...
        eapply PAR...
        repeat right...
        eapply In_nth_error in H; unpack.
        exists 0 (S n)...
        rewrite ENT; discriminate.
        contradiction.

        introv _.
        eapply PAR...
        repeat right...
        eapply In_nth_error in H; unpack.
        exists (S n) 0; simpl; split...
        rewrite ENT; discriminate.
        

        introv NEQ.
        unfold update; rewrite NEQ.
        eapply PAR...
        repeat right...  
        eapply In_nth_error in H; unpack.
        exists (S n) 0...
        
        ** assert (EQU: update_partition ld x t0 = ld).
        eapply update_cons_idem;
        try rewrite ENT; 
        try discriminate...
        assert (PAR2: partition d ld)...
        destruct DIFF as (n1 &n2 &IN1 &IN2 &DIFF).
      destruct n1, n2; try contradiction.
        simpl in IN1; inv IN1.
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := a) (d2 := (a <- x #: t0))...
        eapply PAR...
        repeat right...
        eapply In_nth_error in H; unpack...
        exists 0 (S n);
        simpl;
        intuition...
        rewrite ENT; discriminate...
        unfold update;
        rewrite participant_beq_eq_true;
        discriminate...
        contradiction.
        
        simpl in IN2; inv IN2.
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := a) (d2 := (a <- x #: t0))...
        eapply PAR...
        repeat right...
        eapply In_nth_error in H0;
        unpack...
        exists 0 (S n);
        simpl;
        intuition...
        rewrite ENT; discriminate...
        unfold update;
        rewrite participant_beq_eq_true;
        discriminate...
        contradiction.
        
        rewrite nth_error_S in *;
        assert (K1 := IN1).
        assert (K2 := IN2).
        simpl in K1;
        eapply nth_error_In in K1. 
        eapply PAR;
        repeat right...
        exists (S n1) (S n2);
        intuition...
      
      ** introv NONE.
      unfold disjoint_domain; intros p.
      unfold update_partition in IN1, IN2, DIFF;
      rewrite NONE in *;
      fold update_partition in *... 
      split; introv SOMEp.
      *** inv IN1; inv IN2...
      
       destruct DIFF as (n1 &n2 &IN1 &IN2 &DIFF).
      destruct n1, n2; try contradiction.
        **** simpl in IN1; inv IN1.
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := d2) (d2 := d2)...
        eapply PAR...
        exists 0 (S n2);
        simpl;
        intuition...
        simpl in IN2...
        eapply update_ntherror_none...
        contradiction.
        ****
        simpl in IN1; inv IN1.
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := d2) (d2 := d2)...
        eapply PAR...
        exists 0 (S n1);
        simpl;
        intuition...
        simpl in IN2...
        eapply update_ntherror_none...
        contradiction.
        **** 
        eapply PAR...
        exists (S n1) (S n2); simpl; intuition...
        eapply update_ntherror_none...
         eapply update_ntherror_none...
        ****
        case_eq (d2 p); introv ABS...
        eapply update_inv with (x := x)(t := t0)in ABS...
        case_eq (pbeq x p); introv PEQ; intuition.
        rewrite participant_beq_eq in PEQ; subst; intuition.
       assert (d p = d1 p).
       eapply PAR...
       case_eq (d1 p); introv SOME.
       rewrite SOME in H1;
       rewrite H1 in H2.
       case_eq (d2 x).
       introv SOMEx.
       assert (IN := H).
       eapply update_inv_some in H...
       unpack.
       assert False.
       eapply disjoint_domain_absurd with (d1 := d1) 
       (d2 := d0).  
       eapply PAR...
       subst;
       right;
       eapply in_app_iff;
       right...
       rewrite H3 in IN.
       subst.
       exists 0 (S(length l')); simpl; intuition...
       erewrite nth_error_app2...
       assert (EQ: Datatypes.length l' - Datatypes.length l' = 0).
       lia.
       rewrite EQ; simpl... 
       rewrite SOME; discriminate. 
       subst d2.
       unfold update in H2; rewrite PEQ in *;
       rewrite <-H2; discriminate...
       contradiction.  
        
       rewrite SOMEx; discriminate.
       introv ABS.
       
       assert (IN := H).
       eapply update_inv_none in H...
       unpack.
       assert False.
       eapply disjoint_domain_absurd with (d1 := d1) 
       (d2 := d2).  
       eapply PAR...
       subst;
       right;
       eapply in_app_iff;
       right...
       rewrite H3 in IN.
       subst.
       exists 0 (S(length l')); simpl; intuition...
       erewrite nth_error_app2...
       assert (EQ: Datatypes.length l' - Datatypes.length l' = 0).
       lia.
       rewrite EQ; simpl... 
       rewrite SOME; discriminate. 
       rewrite <-H2; discriminate...
       contradiction.
       
       intuition.  
       
       unfold update_partition;
       rewrite NONE;
       fold update_partition...
       right...
       
       
       ****
        case_eq (d1 x).
        introv SOMEx. 
        eapply update_inv_some in H...
        unpack.
        subst.
        case_eq (pbeq x p).
        introv PEQ.
        rewrite participant_beq_eq in PEQ;
        subst...
        introv NEQ.
        unfold update in SOMEp;
        rewrite NEQ in SOMEp...
        case_eq (d2 p); introv ABS...
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := d2) (d2 := d0)...
        eapply PAR...
        right.
        eapply in_app_iff; right...
        exists 0 (S (length l')); simpl;split; intuition...
        erewrite nth_error_app2...
        assert (EQD:Datatypes.length l' - Datatypes.length l' = 0) by lia.
        rewrite EQD...
        rewrite ABS; discriminate.
        contradiction.
        
        rewrite SOMEx; discriminate.
        
        introv NONE1.
         eapply update_inv_none in H...
        unpack.
        subst.
        case_eq (d2 p); introv ABS...
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := d2) (d2 := d1)...
        eapply PAR...
        right.
        eapply in_app_iff; right...
        exists 0 (S (length l')); simpl;split; intuition...
        erewrite nth_error_app2...
        assert (EQD:Datatypes.length l' - Datatypes.length l' = 0) by lia.
        rewrite EQD...
        rewrite ABS; discriminate.
        contradiction.
        
        **** 
        assert (DIFF2 := DIFF).
        destruct DIFF2 as (n1 &n2 &IN1 &IN2 &DIFF2).
        destruct n1, n2; try contradiction.
        simpl in IN1, IN2.
        inv IN1.
        eapply update_inv_none in H...
        unpack...
        subst...
         eapply disjoint_domain_absurd with
        (d1 := d1) (d2 := d1)...
        eapply PAR...
        exists 0 (S (length l')); simpl;split; intuition...
        erewrite nth_error_app2...
        assert (EQD:Datatypes.length l' - Datatypes.length l' = 0) by lia.
        rewrite EQD...
        simpl in IN1, IN2.
        inv IN2.
        eapply update_inv_none in H0...
        unpack...
        subst...
        rewrite H1 in *.
        case_eq (d2 p); introv  ABS...
         eapply disjoint_domain_absurd with
        (d1 := d2) (d2 := d2)...
        eapply PAR...
        exists 0 (S (length l')); simpl;split; intuition...
        erewrite nth_error_app2...
        assert (EQD:Datatypes.length l' - Datatypes.length l' = 0) by lia.
        rewrite EQD...
        rewrite ABS; discriminate.
        rewrite ABS; discriminate.
        
        eapply IHld with (d1 := d1)...
        simpl in *...
        exists n1 n2;
        intuition...   
        
        *** 
        inv IN1; inv IN2...
      
       destruct DIFF as (n1 &n2 &IN1 &IN2 &DIFF).
      destruct n1, n2; try contradiction.
        **** simpl in IN1; inv IN1.
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := d2) (d2 := d2)...
        eapply PAR...
        exists 0 (S n2);
        simpl;
        intuition...
        simpl in IN2...
        eapply update_ntherror_none...
        contradiction.
        ****
        simpl in IN1; inv IN1.
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := d2) (d2 := d2)...
        eapply PAR...
        exists 0 (S n1);
        simpl;
        intuition...
        simpl in IN2...
        eapply update_ntherror_none...
        contradiction.
        **** 
        eapply PAR...
        exists (S n1) (S n2); simpl; intuition...
        eapply update_ntherror_none...
         eapply update_ntherror_none...
        ****
        case_eq (pbeq x p); introv PEQ; intuition.
        rewrite participant_beq_eq in PEQ; subst; intuition.
        case_eq (d2 x); introv SOME.
        
        eapply update_inv_some in H;
        try rewrite SOME;
        try discriminate...
        unpack; subst.
        unfold update in SOMEp, SOME; rewrite PEQ in *.
        case_eq (d1 p); introv ABS...
        eapply disjoint_domain_absurd 
        with (d1 := d1) (d2 := d0)... 
        eapply PAR...
        right; eapply in_app_iff; right...
        exists 0 (S(length l')); simpl; intuition...
        rewrite nth_error_app2... 
        assert (EQ: Datatypes.length l' - Datatypes.length l' = 0) by lia.
        rewrite EQ...
        rewrite ABS; discriminate.
        
        eapply update_inv_none in H;
        unpack;
        subst...
        case_eq (d1 p); introv ABS...
         eapply disjoint_domain_absurd 
        with (d1 := d1) (d2 := d2)... 
        eapply PAR...
        right; eapply in_app_iff; right...
        exists 0 (S(length l')); simpl; intuition...
        rewrite nth_error_app2... 
        assert (EQ: Datatypes.length l' - Datatypes.length l' = 0) by lia.
        rewrite EQ...
        rewrite ABS; discriminate.  
       
       
       ****
        case_eq (d1 x).
        introv SOMEx. 
        eapply update_inv_some in H...
        unpack.
        subst.
        
        case_eq (pbeq x p).
        introv PEQ.
        rewrite participant_beq_eq in PEQ;
        subst...
        rewrite NONE in *; contradiction.
        introv NEQ.
        unfold update;
        rewrite NEQ...
        
        case_eq (d0 p); introv ABS...
        eapply disjoint_domain_absurd with
        (d1 := d2) (d2 := d0)...
        eapply PAR...
        right.
        eapply in_app_iff; right...
        exists 0 (S (length l')); simpl;split; intuition...
        erewrite nth_error_app2...
        assert (EQD:Datatypes.length l' - Datatypes.length l' = 0) by lia.
        rewrite EQD...
        rewrite ABS; discriminate.
        
        
        rewrite SOMEx; discriminate.
        
        introv NONE1.
         eapply update_inv_none in H...
        unpack.
        subst.
        case_eq (d1 p); introv ABS...
        eapply disjoint_domain_absurd with
        (d1 := d2) (d2 := d1)...
        eapply PAR...
        right.
        eapply in_app_iff; right...
        exists 0 (S (length l')); simpl;split; intuition...
        erewrite nth_error_app2...
        assert (EQD:Datatypes.length l' - Datatypes.length l' = 0) by lia.
        rewrite EQD...
        rewrite ABS; discriminate.
        
        **** 
        assert (DIFF2 := DIFF).
        case_eq (d1 p); introv ABSp...
        destruct DIFF2 as (n1 &n2 &IN1 &IN2 &DIFF2).
        destruct n1, n2; try contradiction.
        
        ***** simpl in IN1, IN2.
        inv IN1.
        eapply update_inv_none in H...
        unpack...
        subst...
         eapply disjoint_domain_absurd with
        (d1 := d1) (d2 := d1);
        try rewrite ABSp;
        try discriminate...
        eapply PAR...
        exists 0 (S (length l')); simpl;split; intuition...
        erewrite nth_error_app2...
        assert (EQD:Datatypes.length l' - Datatypes.length l' = 0) by lia.
        rewrite EQD...
        ***** simpl in IN1, IN2.
        inv IN2.
        eapply update_inv_none in H0...
        unpack...
        subst...
        rewrite H1 in *.
        case_eq (d2 p); introv  ABS...
         eapply disjoint_domain_absurd with
        (d1 := d2) (d2 := d2)...
        eapply PAR...
        exists 0 (S (length l')); simpl;split; intuition...
        erewrite nth_error_app2...
        assert (EQD:Datatypes.length l' - Datatypes.length l' = 0) by lia.
        rewrite EQD...
        rewrite ABS in *; contradiction.
        ***** 
        simpl in *.
        eapply disjoint_domain_absurd with
        (d1 := d1) (d2 := d2)...
        eapply IHld...
        exists n1 n2;
        intuition... 
        rewrite ABSp; discriminate.
  * 
  gen d1 d2 x t t0 d act.
  dependent induction ld; intros...
  simpl in IN1; inv IN1...
  case_eq (a x).
  introv ENT.
  unfold update_partition in IN1, IN2, DIFF;
  rewrite ENT in *.
  inv IN1; inv IN2...
  
   ** destruct DIFF as (n1 &n2 &IN1 &IN2 &DIFF).
      destruct n1, n2; try contradiction.
        
        simpl in IN1; inv IN1.
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := a) (d2 := (a <- x #: t0))...
        eapply PAR...
        assert (IN3 := IN2).
        simpl in IN2;
        eapply nth_error_In in IN2...
        repeat right...
        exists 0 (S n2);
        simpl;
        intuition...
        rewrite ENT; discriminate...
        unfold update;
        rewrite participant_beq_eq_true;
        discriminate...
        contradiction.
        
        simpl in IN2; inv IN2.
        assert False.
        eapply disjoint_domain_absurd with
        (d1 := a) (d2 := (a <- x #: t0))...
        eapply PAR...
        repeat right...
        simpl in IN1; eapply nth_error_In in IN1...
        exists 0 (S n1);
        simpl;
        intuition...
        rewrite ENT; discriminate...
        unfold update;
        rewrite participant_beq_eq_true;
        discriminate...
        contradiction.
        
        rewrite nth_error_S in *;
        assert (K1 := IN1).
        assert (K2 := IN2).
        simpl in K1;
        eapply nth_error_In in K1. 
        eapply PAR;
        repeat right...
        exists (S n1) (S n2);
        intuition...
        
        ** assert (EQ: parties_disjoint a d2).
        eapply PAR...
        repeat right...
        eapply In_nth_error in H.
        unpack.
        exists 0 (S n)...
        unfold parties_disjoint in *; introv EQP EQQ.
        
        case_eq (pbeq x p).
        introv PEQ.
        unfold update in *; rewrite PEQ in *.
        rewrite participant_beq_eq in PEQ; 
        try inv EQP; try inv PEQ.
        assert (d p = a p).
        eapply PAR...
        rewrite ENT; discriminate.
        rewrite DEQ, ENT in H0; inv H0...
        rewrite disjoint_commute.
        eapply disjoint_incl, participants_typ_lts_redex...
        erewrite disjoint_commute...
        
        introv NEQ.
        unfold update in EQP; rewrite NEQ in EQP.  
        eapply EQ...
        
        ** assert (EQ: parties_disjoint a d1).
        eapply PAR...
        repeat right...
        eapply In_nth_error in H.
        unpack.
        exists 0 (S n)...
        unfold parties_disjoint in *; introv EQP EQQ.
        
        case_eq (pbeq x q).
        introv PEQ.
        unfold update in *; rewrite PEQ in *.
        rewrite participant_beq_eq in PEQ; 
        try inv EQQ; try inv PEQ.
        assert (d q = a q).
        eapply PAR...
        rewrite ENT; discriminate.
        rewrite DEQ, ENT in H0; inv H0...
        eapply disjoint_incl, participants_typ_lts_redex...
        erewrite disjoint_commute...
        
        introv NEQ.
        unfold update in *; rewrite NEQ in *.  
        eapply EQ in EQP...
        erewrite disjoint_commute...
        
        ** eapply PAR;
        repeat right...
        
        destruct DIFF as (n1 &n2 &IN1 &IN2 &DIFF).
      destruct n1, n2; try contradiction.
        
        simpl in *; inv IN1.
        eapply disjoint_domain_absurd with
        (d1 := a) (d2 := (a <- x #: t0))...
        eapply PAR...
        repeat right...
        eapply In_nth_error in H;
        unpack.
        exists 0 (S n);
        simpl;
        intuition...
        rewrite ENT; discriminate...
        unfold update;
        rewrite participant_beq_eq_true;
        discriminate...
        
        simpl in *; inv IN2.
        eapply disjoint_domain_absurd with
        (d1 := a) (d2 := (a <- x #: t0))...
        eapply PAR...
        repeat right...
        eapply In_nth_error in H0;
        unpack.
        exists 0 (S n);
        simpl;
        intuition...
        rewrite ENT; discriminate...
        unfold update;
        rewrite participant_beq_eq_true;
        discriminate...
        
        simpl in *.
        exists (S n1) (S n2);
        simpl;
        intuition...
        
        ** introv NONE.
          unfold update_partition in *;
          rewrite NONE in *;
          fold update_partition in *.
          inv IN1; inv IN2...
          
          ***
           destruct DIFF as (n1 &n2 &IN1 &IN2 &DIFF).
           destruct n1, n2; try contradiction.
           simpl in *; inv IN1.
           assert (K := IN2).
           eapply nth_error_In in K.
           eapply update_inv_none in K...
           unpack.
           subst.
           rewrite H0 in *.
           eapply PAR...
           exists 0 (S (length l'));
           simpl;
           intuition...
           erewrite nth_error_app2...
           assert (EQ: 
           Datatypes.length l' - Datatypes.length l' = 0) by lia.
           rewrite EQ; simpl...
           
           simpl in *; inv IN2.
           assert (K := IN1).
           eapply nth_error_In in K.
           eapply update_inv_none in K...
           unpack.
           subst.
           rewrite H0 in *.
           eapply PAR...
           exists 0 (S (length l'));
           simpl;
           intuition...
           erewrite nth_error_app2...
           assert (EQ: 
           Datatypes.length l' - Datatypes.length l' = 0) by lia.
           rewrite EQ; simpl...
            
           simpl in *. 
           eapply PAR...
           exists (S n1) (S n2); simpl; intuition...
           eapply update_ntherror_none...
           eapply update_ntherror_none...
           
           ***
           unfold parties_disjoint in *; introv EQP EQQ.
           case_eq (d2 x); introv SOME.
           eapply update_inv_some in H;
           try rewrite SOME;
           try discriminate...
           unpack.
           subst.
           
           rewrite H0 in *.
           unfold update in SOME;
           rewrite participant_beq_eq_true in SOME;
           inv SOME.
           case_eq (pbeq x q); introv PEQ.
           unfold update in EQQ.
           rewrite PEQ in *;
           inv EQQ.
           rewrite participant_beq_eq in *; subst.
           assert (d0 q <> None).
           eapply update_partition_app2...
           assert (EQ: d q = d0 q).
           eapply PAR...
           right; eapply in_app_iff; right...
           rewrite DEQ in EQ.
           eapply disjoint_incl
           with (l2 := parties t1)...
           eapply PAR with (d2 := d0)...
            right; eapply in_app_iff; right...
            exists 0 (S (length l'));
           simpl;
           intuition...
           erewrite nth_error_app2...
           assert (EQL: 
           Datatypes.length l' - Datatypes.length l' = 0) by lia.
           rewrite EQL; simpl...
           eapply participants_typ_lts_redex...
           
           unfold update in EQQ;
           rewrite PEQ in EQQ.
           eapply PAR
           with (d2 := d0)...
            right; eapply in_app_iff; right...
            exists 0 (S (length l'));
           simpl;
           intuition...
           erewrite nth_error_app2...
           assert (EQL: 
           Datatypes.length l' - Datatypes.length l' = 0) by lia.
           rewrite EQL; simpl...
           
          eapply update_inv_none in H...
          unpack.
          subst.
          eapply PAR with (d2 := d2)...
           right; eapply in_app_iff; right...
            exists 0 (S (length l'));
           simpl;
           intuition...
           erewrite nth_error_app2...
           assert (EQL: 
           Datatypes.length l' - Datatypes.length l' = 0) by lia.
           rewrite EQL; simpl...
           
           
           ***
           unfold parties_disjoint in *; introv EQP EQQ.
           case_eq (d1 x); introv SOME.
           eapply update_inv_some in H;
           try rewrite SOME;
           try discriminate...
           unpack.
           subst.
           
           rewrite H0 in *.
           unfold update in SOME;
           rewrite participant_beq_eq_true in SOME;
           inv SOME.
           case_eq (pbeq x p); introv PEQ.
           unfold update in EQP.
           rewrite PEQ in *;
           inv EQP.
           rewrite participant_beq_eq in *; subst.
           assert (d0 p <> None).
           eapply update_partition_app2...
           assert (EQ: d p = d0 p).
           eapply PAR...
           right; eapply in_app_iff; right...
           rewrite DEQ in EQ.
           erewrite disjoint_commute.
           eapply disjoint_incl
           with (l2 := parties t1)...
           eapply PAR with (d2 := d0)...
            right; eapply in_app_iff; right...
            exists 0 (S (length l'));
           simpl;
           intuition...
           erewrite nth_error_app2...
           assert (EQL: 
           Datatypes.length l' - Datatypes.length l' = 0) by lia.
           rewrite EQL; simpl...
           eapply participants_typ_lts_redex...
           
           unfold update in EQP;
           rewrite PEQ in EQP.
           erewrite disjoint_commute.
           eapply PAR
           with (d2 := d0)...
            right; eapply in_app_iff; right...
            exists 0 (S (length l'));
           simpl;
           intuition...
           erewrite nth_error_app2...
           assert (EQL: 
           Datatypes.length l' - Datatypes.length l' = 0) by lia.
           rewrite EQL; simpl...
           
          eapply update_inv_none in H...
          unpack.
          subst.
          rewrite H0 in *.
          eapply PAR in EQP...
           right; eapply in_app_iff; right...
            exists (S (length l')) 0;
           simpl;
           intuition...
           erewrite nth_error_app2...
           assert (EQL: 
           Datatypes.length l' - Datatypes.length l' = 0) by lia.
           rewrite EQL; simpl...
           
           *** destruct DIFF as (n1 &n2 &IN1 &IN2 &DIFF).
               destruct n1, n2; try contradiction.
               
               simpl in *; inv IN1.
               eapply update_inv_none with (ld := ld)
               in NONE...
               unpack; subst.
               rewrite H2 in *.
               assert (disjoint_domain d1 d1).
               eapply PAR...
               exists 0 (S (length l'));
               simpl;
               intuition...
               erewrite nth_error_app2...
               assert (EQL: 
               Datatypes.length l' - Datatypes.length l' = 0) by lia.
               rewrite EQL; simpl...
               unfold parties_disjoint; introv EQP EQQ.
               assert (d1 p = None).
               eapply H1; rewrite EQP; discriminate...
               rewrite EQP in *; discriminate.
           
               simpl in *;
               inv IN2. 
               eapply update_inv_none with (ld := ld)
               in NONE...
               unpack; subst.
               rewrite H2 in *.
               assert (disjoint_domain d2 d2).
               eapply PAR...
               exists 0 (S (length l'));
               simpl;
               intuition...
               erewrite nth_error_app2...
               assert (EQL: 
               Datatypes.length l' - Datatypes.length l' = 0) by lia.
               rewrite EQL; simpl...
               unfold parties_disjoint; introv EQP EQQ.
               assert (d2 q = None).
               eapply H1; rewrite EQQ; discriminate...
               rewrite EQQ in *; discriminate.
               
               simpl in *...  
               eapply IHld...
               exists n1 n2; simpl; intuition... 
Qed.               
           
  
Lemma parties_input tp q l v tp' :
typ_lts tp (ainput q l v) tp' ->
In q (parties tp).
Proof with eauto using lts_input.
introv LTS.
dependent induction LTS; simpl; try eapply in_app_iff...
Qed.

Lemma parties_output tp q l v tp' :
typ_lts tp (aoutput q l v) tp' ->
In q ( parties tp).
Proof with eauto using lts_input.
introv LTS.
dependent induction LTS; simpl; try eapply in_app_iff...
Qed.


  
Lemma wf_io_diff d tp tq p q l v tp' tq':
  wf tp ->
  wf tq ->
  d p = Some tp ->
  d q = Some tq ->
  typ_lts tp (ainput q l v) tp' ->
  typ_lts tq (aoutput p l v) tq' ->
  pbeq p q = false.
Proof with eauto.
  introv WF1 WF2 EQ1 EQ2 LTS1 LTS2.
  case_eq (pbeq p q); introv ABS...
  rewrite participant_beq_eq in ABS; subst.
  rewrite EQ1 in EQ2; inv EQ2.            
  clear EQ1 d.
  assert False.
  eapply typ_lts_io_absurd...
  contradiction.
Qed.  
                    
Lemma partition_rcomm ld d p q tp tq l v d0 tp' tq':
  partition d ld ->
  (forall r, In r ld -> partition_closed r) ->
  d p = Some tp ->
  d q = Some tq ->
  wf tp ->
  wf tq ->
  typ_lts tp (ainput q l v) tp' ->
  typ_lts tq (aoutput p l v) tq' ->
  In d0 (update_partition (update_partition ld p tp') q tq') ->
  In d0 ld \/
  exists d1,
    In d1 ld /\ Some tp = d1 p /\ Some tq = d1 q/\
      d0 = (d1 <- p #: tp') <- q #: tq'.
Proof 
with 
eauto 
using 
in_eq, 
parties_input, 
parties_output,
partition_cons,
wf_io_diff.

introv PAR PCLS EQ1 EQ2 WF1 WF2 LTS1 LTS2 IN.
induction ld...
move IN at bottom.
assert (NEQ: pbeq p q = false)...

case_eq (a p); introv SOME.
unfold update_partition in IN; rewrite SOME in IN;
fold update_partition in IN.
- case_eq (a q); introv SOME1.
unfold update in IN; rewrite SOME1, NEQ in IN.
assert ((fun y : participant =>
         if pbeq q y
         then Some tq'
         else if pbeq p y then Some tp' else a y) = 
         (a <- p #: tp') <- q #: tq').
apply functional_extensionality; intros; unfold update...   
assert (IN2: In d0 (((a <- p #: tp') <- q #: tq') :: ld)).
erewrite <- H...
* inv IN2...
right. exists a; intuition.
rewrite <-EQ1;
eapply PAR;
try rewrite SOME; 
try discriminate...
rewrite <-EQ2;
eapply PAR;
try rewrite SOME1; 
try discriminate...
left; repeat right...
* assert (a q <> None).
eapply PCLS...
assert (EQ3: d p = a p).
eapply PAR;
try rewrite SOME;
try discriminate... 
rewrite EQ1, SOME in EQ3; inversion EQ3; subst t0...
Search typ_lts top.
rewrite SOME1 in *; contradiction.

- unfold update_partition in IN; rewrite SOME in IN;
fold update_partition in IN.
case_eq (a q); introv SOME0...
assert (a p <> None).
eapply PCLS with (p:= q)...
assert (EQ3:d q = a q).
eapply PAR;
try rewrite SOME0;
try discriminate...
rewrite EQ2, SOME0 in EQ3; inversion EQ3...
subst t0...
rewrite SOME in *; contradiction.
rewrite SOME0 in IN.
inv IN...
eapply IHld in H...
inv H...
left; repeat right...
unpack.
right.
exists d1; intuition...
intros; eapply PCLS...
repeat right...
Qed.

Lemma partition_rrec ld d p tp tp' d0:
  partition d ld ->
  d p = Some tp ->
  typ_lts tp (aunfold p) tp' ->
  In d0 (update_partition ld p tp') ->
  In d0 ld \/
  exists d1,
    In d1 ld /\ Some tp = d1 p /\ 
      d0 = (d1 <- p #: tp').
Proof with eauto using in_eq, partition_cons.
introv PAR EQ LTS IN.
induction ld...
case_eq ( a p); introv SOME;
unfold update_partition in IN; rewrite SOME in IN;
fold update_partition in IN.
inv IN...
right. exists a; intuition...
rewrite <-EQ; eapply PAR; try erewrite SOME; try discriminate...
left. right...
inv IN...
eapply IHld in H as [A | B]...
left. right...
unpack; subst.
right; exists d1; intuition.
Qed.




Lemma update_cat_l (d1 :part_env) d2 p tp tp' pf:
  d1 p = Some tp ->
  exists pf', 
    (d1 @@ d2 @ pf) <- p #: tp' =
      (d1 <- p #: tp') @@ d2 @ pf'.
Proof with eauto using participant_beq_eq.
  introv EQ.
  assert (K := pf).
  eapply update_disjoint_domain_l
    with
    (beq := pbeq)
    (d1 := d1)
    (x := p)
    (t := tp') in K...
  exists K...
  eapply functional_extensionality.
  intros;
    subst;
    unfold singleton, update, extend, cat.
  destruct ( pbeq p x);
    simpl...
  rewrite EQ; discriminate.
Qed.

Lemma update_cat_l2 (d1 :part_env) d2 p tp tp' pf pf':
  d1 p = Some tp ->
    (d1 @@ d2 @ pf) <- p #: tp' =
      (d1 <- p #: tp') @@ d2 @ pf'.
Proof with eauto using participant_beq_eq.
  introv EQ.
  assert (K := pf).
  eapply update_disjoint_domain_l
    with
    (beq := pbeq)
    (d1 := d1)
    (x := p)
    (t := tp') in K...
  eapply functional_extensionality.
  intros;
    subst;
    unfold singleton, update, extend, cat.
  destruct ( pbeq p x);
    simpl...
  rewrite EQ; discriminate.
Qed.

Lemma update_cat_r (d1 :part_env) d2 p tp tp' pf:
  d2 p = Some tp ->
  exists pf', 
    (d1 @@ d2 @ pf) <- p #: tp' =
      d1 @@ (d2 <- p #: tp') @ pf'.
Proof with eauto using participant_beq_eq.
  introv EQ.
  assert (W := pf).
  assert (K := pf).
  eapply update_disjoint_domain_r
    with
    (beq := pbeq)
    (d2 := d2)
    (x := p)
    (t := tp') in K...
  exists K...
  eapply functional_extensionality.
  intros;
    subst;
    unfold singleton, update, extend, cat.
  case_eq ( pbeq p x);
    introv PEQ;
    simpl...
  case_eq (d1 x); introv ABS...
  unfold disjoint_domain in W;
    specialize W with x;
    destruct W...
  rewrite participant_beq_eq in PEQ;
    subst x.
  assert (ABS2: d2 p = None).
  eapply H;
    rewrite ABS;
    discriminate.
  rewrite ABS2 in *;
    discriminate.
  rewrite EQ; discriminate.
Qed.


Lemma cat_singleton_l p tp q tq pf:
  (singleton p tp @@ singleton q tq @ pf) p = Some tp.
Proof with eauto.
  unfold cat.
  rewrite singleton_eq...
Qed.


Lemma cat_singleton_r p tp q tq pf:
  (singleton p tp @@ singleton q tq @ pf) q = Some tq.
Proof with eauto.
  unfold cat. rewrite singleton_eq...
  unfold cat, singleton, extend, empty_ptenv.
  assert (DIFF: pbeq p q = false).
  case_eq (pbeq p q); introv ABS...
  rewrite participant_beq_eq in ABS; subst.
  assert (K := pf).
  unfold disjoint_domain in K.
  specialize K with q.
  destruct K as [K1 _].
  assert (ABS: singleton q tq q = None)...
  eapply K1;
    rewrite singleton_eq;
    try discriminate...
  rewrite singleton_eq in *;
    try discriminate...
  rewrite DIFF...
Qed.

Lemma cat_left (d1 : part_env) d2 pf p t:
  d1 p = Some t ->
  (d1 @@ d2 @ pf) p = Some t.
Proof with eauto.
  introv EQ.
  unfold cat.
  rewrite EQ...
Qed.

Lemma cat_right (d1 : part_env) d2 pf p t:
  d2 p = Some t ->
  (d1 @@ d2 @ pf) p = Some t.
Proof with eauto.
  introv EQ.
  unfold cat.
  case_eq (d1 p); introv ABS.
  unfold disjoint_domain in pf;
    specialize pf with p.
  intuition.
  assert (d2 p = None).
  eapply H;
    rewrite ABS;
    try discriminate...
  rewrite EQ in *;
    try discriminate...
  assumption.
Qed.

Lemma update_hit  (d : part_env) p tp q tq :
  d q = Some tq ->
  pbeq p q = false ->
  (d <- p #: tp) q = Some tq.
Proof with eauto.
introv EQ NEQ.
unfold update; rewrite NEQ...
Qed.

Lemma singleton_update p tp tp':
  singleton p tp <- p #: tp' =
    singleton p tp'.
Proof with eauto.
unfold singleton, update, empty_ptenv, extend. 
apply functional_extensionality; intros;
destruct (pbeq p x)...
Qed.

Lemma partition_closed_rcomm d1 p tp tp' q tq tq' l v:
partition_closed d1 ->
d1 p = Some tp ->
d1 q = Some tq ->
 wf tp ->
  wf tq ->
typ_lts tp (ainput q l v) tp' ->
typ_lts tq (aoutput p l v) tq' ->
partition_closed ((d1 <- p #: tp') <- q #: tq').
Proof 
with 
eauto 
using 
in_eq, 
parties_input, 
parties_output,
partition_cons,
wf_io_diff.


introv PC EQ1 EQ2 WF1 WF2 LTS1 LTS2.
assert (NEQ: pbeq p q = false)...
case_eq (pbeq q p); introv NEQ2.
try rewrite participant_beq_eq in *; subst.
rewrite participant_beq_eq_true in *; discriminate.
unfold partition_closed. intros r tr; introv IN1 IN2.
case_eq (pbeq p r); introv EQR; 
try rewrite participant_beq_eq in *; subst.

assert (tp' = tr).
unfold update in IN1. 
rewrite NEQ2 in *...
rewrite participant_beq_eq_true in *; inv IN1...
subst. 
assert (In q0 (parties tp))...
eapply participants_typ_lts_redex...
assert (d1 q0 <> None).
eapply PC with (p := r)...
unfold update. 
destruct (pbeq q q0); try destruct (pbeq r q0);
try discriminate...


case_eq (pbeq q r); introv EQRw; 
try rewrite participant_beq_eq in *; subst.
assert (tq' = tr).
unfold update in IN1.
rewrite participant_beq_eq_true in *; inv IN1...
subst. 
assert (In q0 (parties tq))...
eapply participants_typ_lts_redex...
assert (d1 q0 <> None).
eapply PC with (p := r)...
unfold update. 
destruct (pbeq r q0); try destruct (pbeq p q0);
try discriminate...

assert (d1 r = Some tr).
unfold update in IN1.
rewrite EQRw, EQR in IN1...
unfold update.
destruct (pbeq q q0); try destruct (pbeq p q0);
try discriminate...
Qed.


Lemma partition_closed_rrec d1 p tp tp':
partition_closed d1 ->
d1 p = Some tp ->
typ_lts tp (aunfold p) tp' ->
partition_closed (d1 <- p #: tp') .
Proof with eauto using in_eq, partition_cons.
introv PC EQ LTS.
unfold partition_closed. intros r tr; introv IN1 IN2.
case_eq (pbeq p r); introv EQR; 
try rewrite participant_beq_eq in *; subst.

assert (tp' = tr).
unfold update in IN1. 
rewrite participant_beq_eq_true in *; inv IN1...
subst. 
assert (In q (parties tp))...
eapply participants_typ_lts_redex...
assert (d1 q <> None).
eapply PC with (p := r)...
unfold update. 
destruct (pbeq r q); 
try discriminate...


assert (d1 r = Some tr).
unfold update in IN1.
rewrite EQR in IN1...
unfold update.
destruct (pbeq p q);
try discriminate...
Qed.


(** Subject reduction *)
Lemma subject_reduction U M a M' U':
  closedS M ->
  wfm M ->
  types_session empty_env empty_penv M U ->
  lts M a M' ->
  elts U a U' ->
  types_session  empty_env empty_penv M' U'.
Proof
  with
  eauto
  using
  substitution,
    wf_input, wf_output, 
    wf_substT,
    wf_sum_out_false_l, wf_sum_inp_false_l,
    wf_sum_out_false_r, wf_sum_inp_false_r,
    lts_input_output_false,
    lts_typ_mu_output_false, lts_typ_mu_input_false,
    lts_input_typ, lts_output_typ,
    stypes_empty,
    types_struct,
    ndm_sum_l, ndm_sum_r,
    ndm_par_l, ndm_par_r,
    process_var_beq_true,
    lts_proc_input, lts_proc_output,
    shift_closed, shift_disjoint,
    shift_disjointP, shift_types,
    disjoint_l_cons,
    closed_cond,
    io_subject_reduction,
    wf_reduction,
    cat_singleton_l, cat_singleton_r,
    cat_left, cat_right,
    update_cat_l, update_cat_r,
    singleton_eq,
    in_eq,
    update_hit,
    partition_closed_rcomm,
    partition_closed_rrec.
  
  introv CLS WF TS LTS ELTS.
  gen U U'.
  dependent induction LTS; intros;
    assert (WFM := WF);
    remember empty_env as G;
    remember empty_penv as K...

  
  
  
  - Case r_input.

    try destruct WF as [NDP NDM].
    inverts TS as WF TC.
    inverts TC as TC1.
    eapply elts_singleton_inv in ELTS;
      unpack;
      subst;
      try discriminate...

  
  - Case r_output.

    try destruct WF as [NDP NDM].
    inverts TS as WF TC.
    
    
    dependent induction TC;
      try eapply elts_singleton_inv in ELTS;
      unpack;
      subst;
      try discriminate...
    
  
    
  - Case r_sum.

    try destruct WF as [NDP NDM].
    move LTS at bottom.
    inverts TS as WF TC.
    inverts TC as TC1 TC2.

    assert (closedS (single_session (p, proc_input p0 l0 x s P0))).
    inverts CLS as F1 F2; econstructor...
    eapply fv_sum in F1; intuition.
    eapply fvP_sum in F2; intuition.

    
    inv LTS.

    all:
      eapply elts_singleton_inv in ELTS;
      unpack;
      subst;
      try discriminate...

  - Case r_comm.

    

    
    try destruct WF as [NDP NDM].
    assert (CL: closedS (single_session (p, P))/\
                  closedS (single_session (q, Q))).
    unfold closedS in CLS; intuition.
    destruct CL as (CLQ &CLP).
    
    inverts TS as TC1 TC2 EQ1 EQ2.
    assert (TC1' := TC1).
    assert (TC2' := TC2).
    inverts TC1' as TC3 TC4 EQ3 EQ4.
    inverts TC3 as WF3 TC3.
    inverts TC4 as WF4 TC4.

    assert (DIFF: pbeq p q = false).
    case_eq (pbeq p q); introv ABS...
    rewrite participant_beq_eq in ABS; subst.
    assert (K := pf0).
    unfold disjoint_domain in K.
    specialize K with q.
    destruct K as [K1 K2].
    assert (EN1: singleton q T1 q = Some T1).
    unfold singleton,extend, empty_env;
      try rewrite participant_beq_eq_true...
    assert (EN2: singleton q T0 q = Some T0).
    unfold singleton,extend, empty_env;
      try rewrite participant_beq_eq_true...
    rewrite EN1, EN2 in *.
    assert ( Some T0 = None).
    eapply K1;
      try discriminate...
    discriminate.

    inverts ELTS as E1.
    
    move LTS1 at bottom.
    move LTS2 at bottom.

    eapply cat_hit_left with
      (d1 := ((singleton p T1 @@ singleton q T0 @ pf0)))
      (d2 := d2)
      (t1 := T1)
      in H6...
    eapply cat_hit_left with
      (d1 := ((singleton p T1 @@ singleton q T0 @ pf0)))
      (d2 := d2)
      (t1 := T0)
      in H7...
    subst T0 T1.

    eapply typ_input_change_payload with (v' := v) in E1.
    eapply typ_output_change_payload with (v' := v) in H4.

    eapply io_subject_reduction
      with (P := P) (P' := P')  in E1 as TCINP;
      try rewrite HeqG, HeqK in *...

    eapply io_subject_reduction
      with (P := Q) (P' := Q')  in H4 as TCOUT;
      try rewrite HeqG, HeqK in *...


    assert (TTC1:
             types_session G K
               (single_session (p, P'))
               (singleton p tp')).
    subst;
      try econstructor...

    assert (TTC2:
             types_session G K
               (single_session (q, Q'))
               (singleton q tq')).
    subst;
      try econstructor...

    
    assert (W := pf0).
    eapply update_cat_l
      with (p:= p) (tp := tp) (tp' := tp')
      in W...
    assert (pf01:
             disjoint_domain
               (singleton p tp')
               (singleton q tq)).
    assert (W2 := pf).
    rewrite singleton_update in W...

    assert (W3 := pf01).
    eapply update_cat_r
      with
      (d2 := singleton q tq)
      (p := q)
      (tp' := tq') in W3...
    assert (pf1':
             disjoint_domain
               (singleton p tp')
               (singleton q tq')).

    assert (W4 := W3).
    rewrite singleton_update in W4...

    
    assert
      (TTC12:
        types_session G K
          ((parallel_session
              (single_session (p, P'))
              (single_session (q, Q'))))
          ((singleton p tp') @@
             (singleton q tq') @ pf1')).
    
    subst;
      eapply ts_parallel with
      (ld := update_partition
               (update_partition ld0 p tp')
               q tq')...
    assert
      (P1: partition
             (singleton p tp'
                @@ singleton q tq @ pf01)
             (update_partition ld0 p tp')).
    remember (singleton p tp
                @@ singleton q tq @ pf0 <- p #: tp') as f.
    remember ( (singleton p tp'
                  @@ singleton q tq @ pf01)) as g.
    assert (EQ: f = g).
    apply functional_extensionality; intros.
    subst.
    unfold update, cat, singleton, extend;
      destruct ( pbeq p x)...
    rewrite <-EQ.
    subst;
      eapply partition_update_partition...

    remember (singleton p tp' @@ singleton q tq @ pf01 <- q #: tq') as f.
    remember (singleton p tp' @@ singleton q tq' @ pf1') as g.
    assert (EQ: f = g).
    apply functional_extensionality; intros.
    subst.
    unfold update, cat, singleton, extend...
    case_eq ( pbeq q x); introv ABS1...
    case_eq ( pbeq p x); introv ABS2...
    rewrite participant_beq_eq in *; subst.
    unfold disjoint_domain in pf01.
    assert (K := pf01).
    specialize K with x.
    destruct K as [ABS _].
    assert (EQ: forall A, singleton x A x = Some A)... 
    intros; unfold singleton, extend;
      try rewrite participant_beq_eq_true...
    rewrite EQ in ABS...
    assert (ABS2 : singleton x tq x = None).
    eapply ABS; try discriminate...
    unfold singleton, extend in ABS2;
      try rewrite participant_beq_eq_true in ABS2...
    discriminate.
    rewrite <-EQ.
    subst;
      eapply partition_update_partition...
    
    introv IN.
    assert (E' := E1).
    
    eapply partition_rcomm in IN...
    destruct IN...
    unpack.
    
    split.
    subst...
    eapply partition_closed_rcomm;
    try eapply EQ4...


    subst d;
      eapply elts_compliance
      with (d1 := d1)...
    eapply EQ4;
      try eapply in_app_iff;
      try right;
      try left...
    econstructor...
    eapply EQ4;
      try eapply in_app_iff;
      repeat right...
    

    move EQ1 at bottom.

    assert (pf11:
             disjoint_domain
               (singleton p tp'
                  @@ singleton q tq' @ pf1')
               d2).
    assert (K1 := pf).
    unfold disjoint_domain in K1.
    unfold disjoint_domain;
      split; try introv DIFF2.
    unfold cat, singleton, extend, empty_penv in DIFF2.
    case_eq (pbeq p x);
      introv PEQ;
      try rewrite PEQ in *;
      try rewrite participant_beq_eq in PEQ;
      try subst x;
      try discriminate...
    
    eapply K1...
    unfold cat, singleton, extend, empty_ptenv;
      try rewrite participant_beq_eq_true;
      try discriminate...
    unfold empty_ptenv in DIFF2.
    
    unfold empty_ptenv in *.
    case_eq (pbeq q x);
      introv PEQ2;
      try rewrite PEQ2 in *;
      try rewrite participant_beq_eq in *;
      try subst x;
      try discriminate...
    eapply K1...
    unfold cat, singleton, extend, empty_ptenv;
      try rewrite participant_beq_eq_true;
      try rewrite DIFF;
      try discriminate...
    contradiction.
    eapply K1 in DIFF2...
    unfold cat, singleton, extend, empty_ptenv in *.
    case_eq (pbeq p x);
      introv PEQ;
      try rewrite PEQ in *;
      try rewrite participant_beq_eq in PEQ;
      try subst x;
      try discriminate...
    case_eq (pbeq q x);
      introv PEQ2;
      try rewrite PEQ2 in *;
      try rewrite participant_beq_eq in *;
      try subst x;
      try discriminate...

    
    remember ((singleton p tp @@ singleton q tq @ pf0)) as d1.
    assert (pf' : d1 p = Some tp).
    subst...
    eapply update_cat_l
      with (d2 := d2) (pf := pf) (tp' := tp')
      in pf'...
    unpack.
    assert (pf'' : (d1 <- p #: tp') q = Some tq).
    subst...
    eapply update_cat_l
      with (d2 := d2) (pf := pf'0) (tp' := tq')
      in pf''...
    unpack.
    rewrite <-H in H0.
    
    assert (EQ := H0).
    subst d1.
          
    assert
      (PA1:
        partition
          (((singleton p tp
               @@ singleton q tq @ pf0)
              @@ d2 @ pf) <- p #: tp')
          (update_partition ld p tp')).
    eapply partition_update_partition...
    assert
      (PA2:
        partition
          ((((singleton p tp
                @@ singleton q tq @ pf0)
               @@ d2 @ pf)
            <- p #: tp')
           <- q #: tq') 
          (update_partition
             (update_partition ld p tp')
             q tq')).
    eapply partition_update_partition...
    rewrite EQ in *.
    econstructor...
    + assert
        (PA3:
          partition
            ((singleton p tp
                @@ singleton q tq @ pf0)
             <- p #: tp')
            (update_partition ld0 p tp')).
      eapply partition_update_partition...
      assert
        (PA4:
          partition
            (((singleton p tp
                 @@ singleton q tq @ pf0)
              <- p #: tp')
             <- q #: tq')
            (update_partition
               (update_partition ld0 p tp')
               q tq')).
      eapply partition_update_partition...
      
      
      assert
        (EQENV:
          (((singleton p tp @@ singleton q tq @ pf0) <- p #: tp') <-
             q #: tq') =
            (singleton p tp' @@ singleton q tq' @ pf1')).
      apply functional_extensionality; intros.
      unfold cat, update, singleton, empty_ptenv, extend.
      case_eq ( pbeq q x); introv PEQ;
        try rewrite PEQ.
      case_eq (pbeq p x); introv ABS;
        try rewrite ABS...
      try rewrite participant_beq_eq in *;
        subst;
        try rewrite participant_beq_eq_true in DIFF;
        try discriminate...
      case_eq (pbeq p x); introv PEQ2;
        try rewrite PEQ2...

      rewrite EQENV...

      eapply ts_parallel with
        (ld :=
           (update_partition
              (update_partition ld0 p tp') q tq'))...

       rewrite <-EQENV...
      

      introv IN.
      move EQ4 at bottom.
      assert (Z := EQ4).
      specialize Z
        with d.

     eapply partition_rcomm in IN...
     destruct IN...
      unpack.
      split...
      subst...
      eapply partition_closed_rcomm...
      eapply EQ4...
        
      subst.
      eapply elts_compliance with (d1 := d1)...
      eapply EQ4...
      eapply SeCom...
      eapply EQ4... 
      
    + introv IN.
      move EQ2 at bottom.
      assert (Z := EQ2).
      specialize Z
        with d.

      eapply partition_rcomm in IN...
      destruct IN...
      unpack.
      subst; split.
      eapply partition_closed_rcomm...
      eapply EQ2...

      eapply elts_compliance with (d1 := d1)...
       eapply EQ2...
      eapply SeCom...
      eapply EQ2...

  - Case r_rec.

    try destruct WF as [WFP1 WFP2].
    try destruct WFP1 as [NDP1 NDM1].
    try destruct WFP2 as [NDP2 NDM2].


    inv ELTS.
    inverts TS as TS1 TS2 PA COMP.
    remember (shiftP M (proc_mu X P)) as RP.
    
    assert (CLMU: closedP (proc_mu X P)).
    unfold closedS in CLS. intuition.
    assert (IH: closedP RP).
    subst...
    
    assert (TS0 := TS1).
    inverts TS0 as WF TC.
    assert (SH := TC).
    inverts TC...
    
    assert (NIN: ~ In X (bvP P)).
    intros ABS.
    unfold ndP,bvP in NDM1; fold bvP in NDM1.
    eapply NoDup_cons_iff in NDM1.
    intuition.

    remember T as T3.
    assert (TCRP:
             types empty_env empty_penv RP
               (typ_mu t1 T3)).
    subst RP.
    move SH at bottom.
    eapply shift_types with (M := M) in SH...
    rewrite shift_empty_env, shift_empty_penv
      in SH...
    
    eapply types_substP
      with
      (P := P)
      (T := (typ_mu t1 T3))
      (U := t1 £ T3) in IH...
    
    move TS2 at bottom.
    assert (EQ: t0 = typ_mu t1 T3).
    eapply cat_hit_left...
    subst t0.
    assert (t' = t1 £ T3).
    inv H2...
    subst t'.

    
    assert
      (EX:
        exists pf',
          ((singleton p (typ_mu t1 T3) @@ d2 @ pf) <- p #: (t1 £ T3)) =
            ((singleton p (typ_mu t1 T3))<- p #: (t1 £ T3) @@ d2 @ pf') ).
    eapply update_cat_l...
    destruct EX as (pf2 &EQ).

    
    rewrite EQ.
    
    eapply ts_parallel with
      (ld := update_partition ld p (t1 £ T3)) ...
    rewrite singleton_update...

    rewrite <-EQ.
    eapply partition_update_partition...

    introv IN.
    assert (LTS := H2).
    assert (K := IN).
    eapply partition_rrec in K as [A | B]...
    unpack.
    eapply in_split in H0 as (l1 &l2 &EQ2)...
    subst ld.
    erewrite update_app in IN...
    eapply in_app_iff in IN as [A | [EQ3 | C]]...
    eapply COMP;
      eapply in_app_iff;
      try left...
    assert (elts d1 (aunfold p) d).
    subst;
      try econstructor...
    split.
    subst...
    eapply partition_closed_rrec...  
    eapply COMP;
      eapply in_app_iff;
      try right...
    eapply elts_compliance...
    eapply COMP;
      eapply in_app_iff;
      try right...
     eapply COMP;
      eapply in_app_iff;
      repeat right...

     move TS1 at bottom.
     inv TS1...
     assert
      (DIS :
        disjoint
          (bv (proc_mu X P))
          (bv (shiftP M (proc_mu X P)))).
    eapply shift_disjoint...
    simpl in DIS...

    subst.
     assert
      (DIS :
        disjoint
          (bvP (proc_mu X P))
          (bvP (shiftP M (proc_mu X P)))).
     eapply shift_disjointP...
     unfold bvP in DIS;
      fold bvP in DIS;
      eapply disjoint_l_cons in DIS as [W _];
      subst...
   
  - Case r_true.

    inv ELTS.

    

  - Case r_false.

    inv ELTS.

   
    
  - Case r_struct.
    
    assert (closedS M1).
    inv H...
    unfold closedS in CLS; intuition.
    econstructor...
    assert (wfm M1).
    inv H...
    unfold wfm in WFM;
      fold wfm in WFM;
      intuition;
      econstructor...
    inv H0.
    eapply IHLTS...
    inv H...
Qed.

Lemma lts_typ_lts p P a G H M T:
  lts (single_session (p, P)) a M ->
  types G H P T ->
  exists U,
    typ_lts T a U.
Proof with eauto using lts_input_typ, lts_output_typ.
  introv LTS TC.
  gen G H T.
  dependent induction LTS;
    intros.
  - inv TC...
  - dependent induction TC.
    eexists...
    all:
      eapply IHTC in H;
      try unpack; eexists...
  - inv TC.
    eapply IHLTS in H2;
      unpack...
    exists U...
    assert (exists v, a = ainput p0 l v).
    clear IHLTS H0 H4 G H.
    dependent induction LTS;
      unpack...
    inv H;
      inv H0...
    unpack; subst...
  -  inv H;
       inv H0...
Qed.

Lemma lts_aunfold_eq p0 p P P':
  lts (single_session (p0, P)) (aunfold p)
    (single_session (p0, P')) ->
  p0 = p.
Proof with eauto.
  introv LTS.
  dependent induction LTS...
  inv H0; inv H...
Qed.

Lemma lts_input_unfold_absurd p p1 q l x s P Q :
  lts
    (single_session (p, proc_input q l x s P))
    (aunfold p1)
    (single_session (p, Q)) ->
  False.
Proof with eauto using proc_equiv_single_inv.
  introv LTS.
  dependent induction LTS...
  assert (M1 = single_session (p, proc_input q l x s P))...
  subst...
  inv H0...
Qed.


Lemma lts_typ_lts_unfold M0 p G H M U:
  lts M0 (aunfold p) M ->
  types_session G H M0 U ->
  exists U',
    elts U (aunfold p) U'.
Proof with
  eauto
  using
  lts_typ_lts,  lts_aunfold_eq,
    lts_input_unfold_absurd,
    cat_left, singleton_eq,
    proc_equiv_single_inv.
  introv LTS TC.
  gen G H U.
  dependent induction LTS;
    intros;
    inv TC...
  - inv H4.
    assert False...
    contradiction.
  - inv H3...
    inv H9.
    exists ((singleton p (typ_mu  t0 T) @@ d2 @ pf) <- p #: (t0 £ T))...
    econstructor...
  - assert (M1 = single_session (p0, P))...
    subst.
    eapply IHLTS...
  - assert
      (TC :
        types_session G H1
          (parallel_session s1 s2)
          (d1 @@ d2 @ pf))...
    eapply types_struct in TC...
Qed.

Lemma lts_input_exc_absurd p exc q l x s P Q :
  lts
    (single_session (p, proc_input q l x s P))
    (atau exc)
    (single_session (p, Q)) ->
  False.
Proof with eauto using proc_equiv_single_inv.
  introv LTS.
  dependent induction LTS...
  assert (M1 = single_session (p, proc_input q l x s P))...
  subst...
  inv H0...
Qed.


Lemma lts_typ_lts_exc M0 exc G H M U:
  lts M0 (atau (Some exc)) M ->
  types_session G H M0 U ->
  exists U',
    elts U  (atau (Some exc)) U'.
Proof with
  eauto
  using
  lts_typ_lts,  
    lts_input_exc_absurd,
    cat_left, cat_right,
    singleton_eq,
    proc_equiv_single_inv.
  introv LTS TC.
  gen G H U.
  dependent induction LTS;
    intros;
    inv TC...
  - inv H4.
    assert False...
    contradiction.
  - clear IHLTS1 IHLTS2.
    inv H2...
    inv H5.
    eapply lts_input_typ in H11;
      unpack...
    inv H7.
    eapply lts_output_typ in H12;
      unpack...
    remember ((singleton p T1 @@ singleton q T0 @ pf0) @@ d2 @ pf) as d.
    exists ((d <- p #: U) <- q #: U0)...
    econstructor;
      subst...
  - assert (M1 = single_session (p, P))...
    subst.
    eapply IHLTS...
  - assert
      (TC :
        types_session G H1
          (parallel_session s1 s2)
          (d1 @@ d2 @ pf))...
    eapply types_struct in TC...
Qed.

Lemma lts_typ_if_then_else M M' U:
  lts M (atau None) M' ->
  types_session empty_env empty_penv M U ->
  types_session empty_env empty_penv M' U.
Proof with
  eauto
  using
  lts_input_exc_absurd,
    singleton_eq,
    proc_equiv_single_inv,
    types_struct.
  introv LTS TC.
  gen U.
  dependent induction LTS;
    intros;
    inv TC...
  - inv H3...
    assert False...
    contradiction.
  - inv H2.    
    inv H8...
  - inv H2.
    inv H8...
Qed.    
    
Definition elts_action a :=
  (exists p, a = aunfold p) \/
    exists exc, a = atau exc.

Theorem subject_reduction_standard U M a M':
  closedS M ->
  wfm M ->
  types_session empty_env empty_penv M U ->
  lts M a M' ->
  elts_action a ->
  types_session  empty_env empty_penv M' U \/
  exists U', 
    elts U a U' /\
      types_session  empty_env empty_penv M' U'.
Proof with
  eauto
  using
  subject_reduction,
    lts_typ_lts_unfold,
    lts_typ_lts_exc,
    lts_typ_if_then_else.
  introv CLS WF TC LTS EA.
  destruct EA as [(p &EQ) | (p &EQ)];
    subst a.
  - right.
  assert (exists U' : part_env,
    elts U (aunfold p) U')...
  unpack;
    try eexists...
  - destruct p.
    + right.
      assert (exists U' : part_env,
                 elts U (atau (Some e)) U')...
      unpack;
        try eexists...
    + left...
Qed.
