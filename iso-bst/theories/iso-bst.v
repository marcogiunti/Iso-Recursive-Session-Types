(** Iso-Recursive BST -- marco.giunti@cs.ox.ac.uk *)

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
  (x : A) (s : B) (pf : fresh g x) :=
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
| typ_end   : typ
| typ_bot : typ.

Function participants t :=
  match t with
  | typ_input p _ _ _ 
  | typ_output p _ _ _ =>
      [p]
  | typ_sum t1 t2 =>
      participants t1 ++ participants t2
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
  participants t <> [].
Proof with eauto.
  introv TB;
    induction t;
    simpl...
  unfold tbranch_r in TB; fold tbranch_r in *; intuition.
  destruct (participants t1); inv H...
  discriminate.
Qed.

Definition single_party (l : list participant) :=
  l <> [] /\
    forall p q,
      In p l -> In q l -> p = q. 

Definition tbranch t :=
  tbranch_r t /\ 
    single_party (participants t).

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
  participants t <> [].
Proof with eauto.
  introv TB;
    induction t;
    simpl...
  unfold tselect_r in TB; fold tselect_r in *; intuition.
  destruct (participants t1); inv H...
  discriminate.
Qed.

Definition tselect t :=
  tselect_r t /\
    single_party (participants t).

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
  unfold participants in H0;
    fold participants in H0.
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
  unfold participants in H0;
    fold participants in H0.
  eapply  sp_app in H0...
  intuition.
  eapply  sp_app in H0...
  intuition.
Qed.

Lemma tbranch_party_subst t1 x t2:
  tbranch t1 ->
  participants t1 = participants (substT t1 x t2).
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
  unfold participants in H0;
    fold participants in H0.
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
    destruct (participants (substT t1_1 x t2));
      try discriminate...
  - intros.
    assert (EQ: participants t1_1 ++ participants t1_2 =
                  participants (typ_sum t1_1 t1_2))...
    rewrite EQ,TB2 in SP...
Qed.

Lemma tselect_party_subst t1 x t2:
  tselect t1 ->
  participants t1 = participants (substT t1 x t2).
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
  unfold participants in H0;
    fold participants in H0.
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
    destruct (participants (substT t1_1 x t2));
      try discriminate...
  - intros.
    assert (EQ: participants t1_1 ++ participants t1_2 =
                  participants (typ_sum t1_1 t1_2))...
    rewrite EQ,TB2 in SP...
Qed.


Definition pdual : participant -> participant :=
  fun r =>
    match r with
    | pyp 0 =>
          pyp 1
    | pyp (S n) =>
        if Nat.even n
        then
          pyp n
        else
          pyp (S (S n))
    end.

Lemma pdual_involution :
  forall p, pdual (pdual p) = p.
Proof with eauto.
  intros p; destruct p; unfold pdual; induction n; try lia.
  unfold Nat.even; tauto.
  case_eq (Nat.even n); intros EV; destruct n; try tauto.
  rewrite Nat.even_succ, <-Nat.negb_even in EV.
  destruct (Nat.even n); unfold negb in *; try discriminate...
  unfold Nat.even in EV; discriminate.
  rewrite Nat.even_succ, <-Nat.negb_even in EV.
  rewrite Nat.even_succ_succ.
   destruct (Nat.even n); unfold negb in *; try discriminate...
Qed.

(** Adapted from https://softwarefoundations.cis.upenn.edu/ *)
Theorem involution_injective : forall (f : participant -> participant),
    (forall n, n = f (f n)) ->
    (forall n1 n2, f n1 = f n2 -> n1 = n2).
Proof.
  intros. rewrite H. rewrite <- H0. now rewrite <- H.
Qed.

Lemma pdual_injective :
  Injective pdual.
Proof with eauto using pdual_involution.
  unfold Injective; introv EQ.
  specialize involution_injective with (f := pdual) as K.
  eapply K...
Qed.

Definition pdual_beq p1 p2 :=
  pbeq p1 (pdual p2).           

Function typ_dual t :=
  match t with
  | typ_var _ 
  | typ_end
  | typ_bot =>
      t
  | typ_mu x t =>
      typ_mu x (typ_dual t)
  | typ_sum t1 t2 =>
      typ_sum (typ_dual t1) (typ_dual t2)
  | typ_input p l s t =>
      typ_output (pdual p) l s (typ_dual t)
  | typ_output p l s t =>
      typ_input (pdual p) l s (typ_dual t)
  end.

Hint Unfold typ_dual : ufdual.
Hint Rewrite pdual_involution : rwdual.

Lemma typ_dual_involution t :
  typ_dual (typ_dual t) = t.
Proof with eauto.
  dependent induction t;
    unfold typ_dual; fold typ_dual;
    try rewrite IHt;
    try rewrite IHt1;
    try rewrite IHt2;
    autorewrite with rwdual...
Qed.

Hint Rewrite typ_dual_involution : rwdual.

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
  | typ_end
  | typ_bot =>
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
  | typ_end
  | typ_bot =>
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
  | typ_end
  | typ_bot =>
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

Function bot_free t :=
  match t with
  | typ_var _ 
  | typ_end =>
      True
  | typ_bot =>
      False
  | typ_mu _ t1 =>
      bot_free t1
  | typ_sum t1 t2 =>
      bot_free t1 /\ bot_free t2
  | typ_input _ _ _ t1
  | typ_output _ _ _ t1 =>
      bot_free t1
  end.

(** Well-formed types *)
Definition wf t :=
  bot_free t /\ ndl t.

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
  unfold wf,bot_free, ndl in *;
    intuition.
Qed. 

Lemma wf_input p l s t:
  wf (typ_input p l s t) ->
  wf t.
Proof with eauto.
  introv WF.
  unfold wf,bot_free, ndl in *;
    intuition.
Qed.

Lemma wf_output p l s t:
  wf (typ_output p l s t) ->
  wf t.
Proof with eauto.
  introv WF.
  unfold wf,bot_free, ndl in *;
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
    * try eapply IHT1_1...
      eapply wf_sum in WF1 as [K _]...
    * try eapply IHT1_2...
      eapply wf_sum in WF1 as [_ K]...
    * destruct WF1 as [_ NDL].
      destruct NDL as ([(TB &SL) | (TS &SL)] &[NDL1 NDL2]).
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
      eapply wf_sum in WF1 as [[_ K] _]...
      destruct WF2 as [_ K]...
    * eapply ndl_substT...
      eapply wf_sum in WF1 as [_ [_ K]]...
      destruct WF2 as [_ K]...
Qed.

Lemma wf_substT X T:
  wf (typ_mu X T) ->
  wf (X £ T).
Proof with eauto using  wf_substT_gen.
  introv WF...
Qed.

Lemma participants_dual t :
  List.map pdual (participants t) =
    participants (typ_dual t).
Proof with eauto.
  dependent induction t;
    simpl;
    try rewrite map_app, IHt1,IHt2...
Qed.

Lemma tbranchr_tselectr t:
  tbranch_r t ->
  tselect_r (typ_dual t).
Proof with eauto.
  introv TB.
  dependent induction t;
    simpl;
    repeat split...
  eapply IHt1; simpl in TB; intuition...
  eapply IHt2; simpl in TB; intuition...
Qed.

Lemma tbranch_tselect t:
  tbranch t ->
  tselect (typ_dual t).
Proof with eauto using  tbranchr_tselectr.
  introv TB.
  dependent induction t;
    simpl...
  econstructor; destruct TB as [K SP]...
  eapply tbranchr_tselectr in K...
  - destruct SP as [DF SP].
    split...
    intros ABS.
    simpl in ABS.
    repeat rewrite <-participants_dual in ABS.
    rewrite <-map_app in ABS.
    assert (EQ:  (participants t1 ++ participants t2) = participants (typ_sum t1 t2))...
    rewrite EQ in ABS.
    eapply map_eq_nil in ABS.
    rewrite ABS in *; contradiction.
    intros.
    specialize SP with (pdual p) (pdual q).
    simpl in H, H0.
    repeat rewrite <-participants_dual in H.
    rewrite <-map_app in H.
    repeat rewrite <-participants_dual in H0.
    rewrite <-map_app in H0.
    assert (EQ:  (participants t1 ++ participants t2) = participants (typ_sum t1 t2))...
    rewrite EQ in *.
    assert (EQ2: pdual p = pdual q).
    eapply SP...
    all:
      try rewrite in_map_iff in *; unpack; subst;
      try rewrite pdual_involution...
    repeat rewrite pdual_involution in EQ2;
      subst...
  - unfold tselect;
      split...
    destruct TB as [TB _].
    eapply tbranchr_tselectr in TB...
    destruct TB as [_ SP];
      simpl;
      destruct SP as [DF SP];
      split;
      try discriminate;
      intros;
      try inv H;
      try inv H0...
    all:
      try inv H;
      try inv H1.
  - unfold tselect;
      split...
    destruct TB as [TB _].
    eapply tbranchr_tselectr in TB...
    destruct TB as [_ SP];
      simpl;
      destruct SP as [DF SP];
      split;
      try discriminate;
      intros;
      try inv H;
      try inv H0...
    all:
      try inv H;
      try inv H1.  
Qed.

Lemma tselectr_tbranchr t:
  tselect_r t ->
  tbranch_r (typ_dual t).
Proof with eauto.
  introv TB.
  dependent induction t;
    simpl;
    repeat split...
  eapply IHt1; simpl in TB; intuition...
  eapply IHt2; simpl in TB; intuition...
Qed.

Lemma tselect_tbranch t:
  tselect t ->
  tbranch (typ_dual t).
Proof with eauto using  tselectr_tbranchr.
  introv TB.
  dependent induction t;
    simpl...
  econstructor; destruct TB as [K SP]...
  eapply tselectr_tbranchr in K...
  - destruct SP as [DF SP].
    split...
    intros ABS.
    simpl in ABS.
    repeat rewrite <-participants_dual in ABS.
    rewrite <-map_app in ABS.
    assert (EQ:  (participants t1 ++ participants t2) = participants (typ_sum t1 t2))...
    rewrite EQ in ABS.
    eapply map_eq_nil in ABS.
    rewrite ABS in *; contradiction.
    intros.
    specialize SP with (pdual p) (pdual q).
    simpl in H, H0.
    repeat rewrite <-participants_dual in H.
    rewrite <-map_app in H.
    repeat rewrite <-participants_dual in H0.
    rewrite <-map_app in H0.
    assert (EQ:  (participants t1 ++ participants t2) = participants (typ_sum t1 t2))...
    rewrite EQ in *.
    assert (EQ2: pdual p = pdual q).
    eapply SP...
    all:
      try rewrite in_map_iff in *; unpack; subst;
      try rewrite pdual_involution...
    repeat rewrite pdual_involution in EQ2;
      subst...
  - unfold tbranch;
      split...
    destruct TB as [TB _].
    eapply tselectr_tbranchr in TB...
    destruct TB as [_ SP];
      simpl;
      destruct SP as [DF SP];
      split;
      try discriminate;
      intros;
      try inv H;
      try inv H0...
    all:
      try inv H;
      try inv H1.
  - unfold tbranch;
      split...
    destruct TB as [TB _].
    eapply tselectr_tbranchr in TB...
    destruct TB as [_ SP];
      simpl;
      destruct SP as [DF SP];
      split;
      try discriminate;
      intros;
      try inv H;
      try inv H0...
    all:
      try inv H;
      try inv H1.  
Qed.

Lemma tbranchl_tselectl t:
  tbranch t ->
  tbranch_labels t = tselect_labels (typ_dual t).
Proof with eauto using tbranch_sum.
  introv TB.
  dependent induction t;
    simpl;
    try rewrite IHt1, IHt2;
    try eapply tbranch_sum in TB;
    intuition.
Qed.

Lemma tselectl_tbranchl t:
  tselect t ->
  tselect_labels t = tbranch_labels (typ_dual t).
Proof with eauto using tbranch_sum.
  introv TB.
  dependent induction t;
    simpl;
    try rewrite IHt1, IHt2;
    try eapply tselect_sum in TB;
    intuition.
Qed.

Lemma wf_dual t:
  wf t ->
  wf (typ_dual t).
Proof
  with
  eauto
  using
  tbranch_tselect,
    tselect_tbranch,
    tbranchl_tselectl,
    tselectl_tbranchl.
  introv WF;
    dependent induction t;
    simpl;
    try eapply IHt...
  unfold wf; split.
  - simpl; split;
      try eapply IHt1, wf_sum with (t1 := t1) (t2 :=t2)...
    try eapply IHt2, wf_sum with (t1 := t1) (t2 :=t2)...
  - simpl; repeat split.
    destruct WF as [BF NDL].
    destruct NDL as [[(TB &SL) | (TS &SL)] [N1 N2]].
    right; split...
    eapply tbranch_tselect in TB...
    rewrite tbranchl_tselectl in SL...
    left; split...
    eapply tselect_tbranch in TS...
    rewrite tselectl_tbranchl in SL...
    eapply IHt1; eapply wf_sum in WF as [K _]...
    eapply IHt2; eapply wf_sum in WF as [_ K]...
Qed.

Lemma dual_substT0 T1 X T2:
  typ_dual (substT T1 X T2) =
    substT (typ_dual T1) X (typ_dual T2).
Proof with eauto.
  dependent induction T1;
    simpl...
  destruct (X =? v)...
  destruct (X =? v)...
  unfold typ_dual; fold typ_dual; rewrite IHT1...
  rewrite IHT1_1; rewrite IHT1_2...
  rewrite IHT1...
  rewrite IHT1...
Qed.

Lemma dual_substT X T:
  typ_dual (X £ T) = X £ typ_dual T.
Proof with eauto using dual_substT0.
  simpl...
Qed.

Hint Rewrite dual_substT : rwdual.

(** From https://github.com/rocq-archive/weak-up-to *)
Definition relation2(X Y: Type) := X -> Y -> Prop.
Definition relation (X: Type) := relation2 X X.
Definition relation_typ := relation typ.
Definition addR (R : relation_typ) t1 t2 :=
  fun s1 s2 => R s1 s2 \/ s1 = t1 /\ s2 = t2.
Notation "R -+ t1 , t2" := (addR R t1 t2) (at level 40).
Definition set(X: Type) := X -> Prop.
Section O.
  Variables X Y Z: Type.
  Definition union_st (P: set (relation2 X Y)) :=
    fun x y => exists2 R, P R & R x y.
End O.

Section Definitions.

  Variables X Y Z: Type.
  (** Inclusion *)
  Definition incl: relation (relation2 X Y) := fun R1 R2 => forall x y, R1 x y -> R2 x y.
  (** Extensional equality *)
  Definition eeq: relation (relation2 X Y) := fun R1 R2 => incl R1 R2 /\ incl R2 R1.

  Variable R: relation X.
  Definition reflexive     := forall x, R x x.
  Definition transitive    := forall y x z, R x y -> R y z -> R x z.
  Definition symmetric     := forall x y, R x y -> R y x.
  Definition antisymmetric := forall x y, R x y -> R y x -> x=y.

End Definitions.

(** Type equivalence *)
Definition equiv R :=
  forall t1 t2,
    R t1 t2 ->
    match t1, t2 with
    | typ_mu X1 U1, typ_mu X2 U2 =>
        R U1 U2 /\  R (X1 £ U1) t2 /\ R t1 (X2 £ U2)
    | typ_mu X U, _ =>
        R (X £ U) t2
    | _, typ_mu X U =>
        R t1 (X £ U)
    | typ_var X1, typ_var X2 =>
        True
    | typ_end, typ_end =>
        True
    | typ_sum (typ_input p1 l1 s1 u1) r1,
      typ_sum (typ_input p2 l2 s2 u2) r2 =>
        p1 = p2 /\ l1 = l2 /\ s1 = s2 /\ R u1 u2 /\ R r1 r2
    | typ_sum (typ_output p1 l1 s1 u1) r1,
      typ_sum (typ_output p2 l2 s2 u2) r2 =>
        p1 = p2 /\ l1 = l2 /\ s1 = s2 /\ R u1 u2 /\ R r1 r2
    | typ_input p1 l1 s1 u1, typ_input p2 l2 s2 u2 =>
        p1 = p2 /\ l1 = l2 /\ s1 = s2 /\ R u1 u2
    | typ_output p1 l1 s1 u1, typ_output p2 l2 s2 u2 =>
        p1 = p2 /\ l1 = l2 /\ s1 = s2 /\ R u1 u2
    | _, _ =>
        False
    end.

Definition struct_equiv R :=
  equiv R /\ symmetric typ R.

(** Type congruence *)
Definition typ_scongr :=
  union_st typ typ struct_equiv.

Notation "T1 == T2" := (typ_scongr T1 T2) (at level 40).

Lemma exists_struct_equiv R :
  forall t1 t2,
    struct_equiv  R ->
    R t1 t2 ->
    t1 == t2.
Proof with eauto.
  intros...
  unfold typ_scongr...
  econstructor...
Qed.

Ltac prove_scongr R  :=
  match goal with
  | |-  ?W1 == ?W2 =>
      eapply (exists_struct_equiv R); eauto
  end.

Lemma equiv_scongr: equiv typ_scongr.
Proof with eauto.
  unfold equiv, "=="; introv SE.
  inv SE.
  assert (SE := H).
  destruct H as [EQ OPT].
  eapply EQ in H0.
  destruct t1, t2; try econstructor;
    intuition; subst; try econstructor...
  destruct t1_1; try econstructor...
  destruct t1_1, t2_1;
    intuition; subst;
    try econstructor...
Qed.

Lemma scongr_symmetric:  
  symmetric typ typ_scongr.
Proof with eauto.
  unfold typ_scongr, union_st, struct_equiv, symmetric; introv EX.
  destruct EX as [R EX];
    destruct EX as (EQ &SYMM);
    try eexists...
Qed.

Hint Resolve
  scongr_symmetric
  exists_struct_equiv.

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
  (participant * process) -> (participant * process) -> session

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
| pe_commut p q  P Q:
  proc_equiv
    (parallel_session (p, P) (q, Q))
    (parallel_session (q, Q) (p, P)).

Hint Constructors proc_equiv.

(** Labeleled transition system of sessions *)
Inductive proc_action : Set :=
| ainput : participant -> label -> value -> proc_action
| aoutput :  participant -> label -> value -> proc_action
| aunfold : proc_action
| atau : proc_action.

(** Type system *)
Definition typ_env := partial_fun evar styp.
Definition empty_env : typ_env := fun _ => None.
Notation "g ',,' x '-:' t @ pf" :=
  (extend evar_beq g x t pf) (at level 40).

Definition proc_env := partial_fun process_var typ.
Definition empty_penv : proc_env := fun _ => None.
Notation "h ',,' x '=:' t @ pf" :=
  (extend process_var_beq h x t pf) (at level 40).

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

Inductive types_session (g : typ_env) (h : proc_env)
  : session -> typ  -> Prop :=
| ts_single p P T1:
  wf T1 ->
  types g h P T1 ->
  types_session g h
    (single_session (p, P))
    T1
| ts_parallel p P Q T1 T2:
  types_session g h
    (single_session (p, P)) T1 ->
  types_session g h
    (single_session (pdual p, Q)) T2 ->
  typ_dual T1 == T2 ->
  types_session g h
    (parallel_session (p, P) (pdual p, Q)) typ_bot.

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
| r_input p l x s v P:
  stypes empty_env (expr_val v) s ->
  lts
    (single_session
       (p, proc_input (pdual p) l x s P))
    (ainput (pdual p) l v)
    (single_session (p, substV P v x))
| r_output p l e v s P:
  eval_expr e v ->
  lts
    (single_session
       (p, proc_output (pdual p) l  e s P))
    (aoutput (pdual p) l v)
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
| r_comm p l v  P P' Q Q':
  lts
    (single_session (p, P))
    (ainput (pdual p) l v)
    (single_session (p, P')) ->
  lts
    (single_session (pdual p, Q))
    (aoutput p l v)
    (single_session (pdual p, Q')) ->
  lts
    (parallel_session (p, P) (pdual p, Q))
    atau
    (parallel_session (p, P') (pdual p, Q'))
| r_rec p X P Q RP M:
  max_seed (proc_mu X P) < M ->
  RP = shiftP M (proc_mu X P) ->
  lts
    (parallel_session (p, proc_mu X P) (pdual p, Q))
    aunfold
    (parallel_session
       (p,  substP P RP X)
       (pdual p, Q))
| r_true p e P1 P2 Q:
  eval_expr e (value_bool true) ->
  lts
    (parallel_session (p,  proc_conditional e P1 P2) (pdual p, Q))
    atau
    (parallel_session (p,  P1) (pdual p, Q))
| r_false p e P1 P2  Q:
  eval_expr e (value_bool false) ->
  lts
    (parallel_session (p,  proc_conditional e P1 P2) (pdual p, Q))
    atau
    (parallel_session (p, P2) (pdual p, Q))
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

Definition wfm M :=
  match M with
  | single_session (_, P) =>
      wfp P
  | parallel_session (_, P) (_, Q) =>
      wfp P /\ wfp Q
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
Definition closedS M :=
  match M with
  | single_session (_, p) =>
      closedP p
  | parallel_session (_,p) (_, q) =>
      closedP p /\
        closedP q
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
| e_fold X T :
  typ_lts
    (typ_mu X T)
    aunfold
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
    t'
| e_bot_tau :
  typ_lts
    typ_bot
    atau
    typ_bot
| e_bot_unfold :
  typ_lts
    typ_bot
    aunfold
    typ_bot.

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
  introv (_ &[[(TB &ND) | ABS] _]) IN1 IN2.
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
  introv (_ &[[ABS | (TB &ND)] _]) IN1 IN2.
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

Lemma scongr_input p l s t1 t2:
  typ_input p l s t1 == typ_input p l s t2 ->
  t1 == t2.
Proof with eauto.
  introv SC.
  unfold "==" in SC; destruct SC.
  prove_scongr x...
  destruct H as (EQ &_ ).
  eapply EQ in H0; intuition.
Qed.

Lemma scongr_output p l s t1 t2:
  typ_output p l s t1 == typ_output p l s t2 ->
  t1 == t2.
Proof with eauto.
  introv SC.
  unfold "==" in SC; destruct SC.
  prove_scongr x...
  destruct H as (EQ &_).
  eapply EQ in H0; intuition.
Qed.

Lemma typ_dual_inv t1 t2:
  typ_dual t1 = t2 ->
  t1 = typ_dual t2.
Proof with eauto.
  introv EQ.
  assert (typ_dual (typ_dual t1) = typ_dual t2).
  rewrite EQ...
  rewrite typ_dual_involution in *...
Qed.

Hint Unfold typ_dual : ufdual.

Lemma  dual_injective t1 t2:
  typ_dual t1 = typ_dual t2 ->
  t1 = t2.
Proof with eauto.
  introv DUAL.
  dependent induction t1;
    dependent induction t2;
    simpl in *;
    try discriminate;
    try inv DUAL;
    try erewrite IHt1;
    try erewrite IHt1_1;
    try erewrite IHt1_2;
    try eapply pdual_injective in H0;
    subst...
Qed.

Lemma scongr_dual T1 T2:
  T1 == T2 ->
  typ_dual T1 == typ_dual T2.
Proof
  with
  eauto
  using
  typ_dual_inv,
    typ_dual_involution,
    dual_substT,
    dual_injective.
  introv SC.
  assert (SC0 := SC).
  inv SC0...
  destruct H.
  assert (SYMM2 := scongr_symmetric).
  remember (fun t1 t2 => x (typ_dual t1) (typ_dual t2)) as R.
  prove_scongr R.
  split.
  introv REL1.
  rewrite HeqR in *.
  eapply H in REL1; intuition.
  - destruct t1, t2; simpl in REL1;
      try discriminate;
      intuition;
      simpl; try rewrite dual_substT...
    all: try destruct t1_1;
      try simpl in REL1;
      try discriminate;
      try contradiction...
    all: try destruct t2_1; simpl in *; intuition; subst;
      try discriminate;
      try eapply pdual_injective;
      try inv REL1...
  - unfold symmetric; intros; subst...
  - rewrite HeqR.
    repeat rewrite typ_dual_involution...
Qed.

Lemma lts_input_typ p P l v M G H T:
  lts (single_session (p, P)) (ainput (pdual p) l v) M ->
  types G H P T ->
  exists U,
    typ_lts T (ainput (pdual p) l v) U.
Proof with eauto.    
  introv LTS TC.
  gen G H T.
  dependent induction LTS; intros...
  inv TC...
  inverts TC as TC1 TC2.
  eapply IHLTS in TC1 as (U &E1)...
  inv H...
  all: eapply IHLTS;
    inv H...
  Unshelve.
  all:eauto.
Qed.

Lemma lts_output_typ p P l v M G H T:
  lts (single_session (p, P)) (aoutput (pdual p) l v) M ->
  types G H P T ->
  exists U,
    typ_lts T (aoutput (pdual p) l v) U.
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

Definition  action_dual a b :=
  match a, b with
  | ainput p1 l1 v1, aoutput p2 l2 v2  =>
      p1 = pdual p2 /\ l1 = l2 /\ v1 = v2
  | aoutput p1 l1 v1, ainput p2 l2 v2 =>
      p1 = pdual p2 /\ l1 = l2 /\ v1 = v2
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

Lemma input_scongr u1 u2 p l s:
  u1 == u2 ->
  typ_input p l s u1 ==  typ_input p l s u2.
Proof with eauto using symmetric_clos_sym.
  introv EQ.
  unfold "==" in EQ.
  inv EQ...
  remember
    (fun t1 t2 =>
       x t1 t2  \/
         (t1  = typ_input p l s u1 /\ 
            t2 =   typ_input p l s u2)) as R.
  prove_scongr (clos_sym R).
  subst R.
  repeat split...
  - unfold equiv.  introv CLS.
    dependent induction CLS...
    destruct H1 as [REL | IND].
    destruct H as (EQ & SYMM).
    eapply EQ in REL; intuition; unpack; subst...
    destruct x0, y;
      try destruct x0_1;
      try destruct y1;
      intuition; subst;
      try contradiction...
    destruct IND; subst; intuition...
    destruct x0, y;
      try destruct x0_1;
      try destruct y1;
      intuition; subst;
      try contradiction...
  - subst R; econstructor...
Qed.

Lemma output_scongr u1 u2 p l s:
  u1 == u2 ->
  typ_output p l s u1 ==  typ_output p l s u2.
Proof with eauto using symmetric_clos_sym.
  introv EQ.
  unfold "==" in EQ.
  inv EQ...
  remember
    (fun t1 t2 =>
       x t1 t2  \/
         (t1  = typ_output p l s u1 /\ 
            t2 =   typ_output p l s u2)) as R.
  prove_scongr (clos_sym R).
  subst R.
  repeat split...
  - unfold equiv.  introv CLS.
    dependent induction CLS...
    destruct H1 as [REL | IND].
    destruct H as (EQ & SYMM).
    eapply EQ in REL; intuition; unpack; subst...
    destruct x0, y;
      try destruct x0_1;
      try destruct y1;
      intuition; subst;
      try contradiction...
    destruct IND; subst; intuition...
    destruct x0, y;
      try destruct x0_1;
      try destruct y1;
      intuition; subst;
      try contradiction...
  - subst R; econstructor...                                   
Qed.

Lemma scongr_sum t1 t2 t3 t4 :
  typ_sum t1 t2 == typ_sum t3 t4 ->
  t1 == t3 /\ t2 == t4.
Proof with eauto using input_scongr, output_scongr.
  introv EQ.
  assert (K := equiv_scongr).
  eapply K in EQ; intuition; unpack; subst;
    try inv H;
    try inv H0...
  all:destruct t1, t3; simpl in *;
    intuition; subst;
    try contradiction...
Qed.

Lemma tbranch_labels_dual l t:
  In l (tbranch_labels t) ->
  In l (tselect_labels (typ_dual t)).
Proof with eauto.
  introv IN.
  dependent induction t;
    simpl in *...
  eapply in_app_iff in IN as [L | R];
    eapply in_app_iff...
Qed.

Lemma tselect_labels_dual l t:
  In l (tselect_labels t) ->
  In l (tbranch_labels (typ_dual t)).
Proof with eauto.
  introv IN.
  dependent induction t;
    simpl in *...
  eapply in_app_iff in IN as [L | R];
    eapply in_app_iff...
Qed.

Lemma scongr_input2 p1 p2 l1 l2 s1 s2 t1 t2:
  typ_input p1 l1 s1 t1 ==
    typ_input p2 l2 s2 t2 ->
  p1 = p2 /\ l1 = l2 /\ s1 = s2.
Proof with eauto.
  introv SC.
  assert (K := equiv_scongr).
  eapply K in SC;
    intuition.
Qed.
  
Lemma scongr_output2 p1 l1 s1 p2 l2 s2 t1 t2:
  typ_output p1 l1 s1 t1 ==
    typ_output p2 l2 s2 t2 ->
  p1 = p2 /\ l1 = l2 /\ s1 = s2.
Proof with eauto.
  introv SC.
  assert (K := equiv_scongr).
  eapply K in SC;
    intuition.
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


Lemma equiv_input_sum_false R p l s t t1 t2:
  equiv R ->
  R (typ_input p l s t) (typ_sum t1 t2) ->
  False.
Proof with eauto.
  introv EQ REL.
  eapply EQ in REL;
    intuition;
    unpack;
    try discriminate.
Qed.

Lemma scongr_input_sum_false p l s t t1 t2:
  (typ_input p l s t) == (typ_sum t1 t2) ->
  False.
Proof with eauto using equiv_input_sum_false.
  introv SC.
  destruct SC. destruct H.
  assert False...
Qed.

Lemma equiv_output_sum_false R p l s t t1 t2:
  equiv R ->
  R (typ_output p l s t) (typ_sum t1 t2) ->
  False.
Proof with eauto.
  introv EQ REL.
  eapply EQ in REL;
    intuition;
    unpack;
    try discriminate.
Qed.

Lemma scongr_output_sum_false p l s t t1 t2:
  (typ_output p l s t) == (typ_sum t1 t2) ->
  False.
Proof with eauto using  equiv_output_sum_false.
  introv SC.
  destruct SC. destruct H.
  assert False...
Qed.

(** Key lemma for subject reduction *)
Lemma elts_dual_scongr T1 T2 a U1 U2 b:
  wf T1 ->
  wf T2 ->
  T1 == typ_dual T2 ->
  typ_lts T1 a U1 ->
  typ_lts T2 b U2 ->
  action_dual a b ->
  U1 == typ_dual U2.
Proof with
  eauto using
  scongr_dual,
    scongr_input, scongr_output, 
    scongr_input2, scongr_output2,
    scongr_input_sum_false,
    scongr_output_sum_false,
    tbranch_output_false,  tselect_input_false,
    tselect_sum_l, tselect_sum_r,
    tbranch_sum_l, tbranch_sum_r,
    NoDup_app.
  introv WF1 WF2 SC E1 E2 DUAL.
  gen T2 U2.
  dependent induction E1;
    intros.
  - inv DUAL... 
  - Case e_input.
    dependent induction E2;
      eapply scongr_dual in SC;
      rewrite typ_dual_involution in SC;
      assert (SYMM2 := scongr_symmetric);
      unfold typ_dual in SC;
      fold typ_dual in SC;
      try inv DUAL;
      destruct H0;
      subst l0 v0;
      rewrite pdual_involution in *...
    assert (s = s0).
    eapply scongr_output2...
    subst s0.
    assert (typ_dual t0 == t1)...
    eapply scongr_dual in H;
      rewrite typ_dual_involution in *...
    assert False...
    contradiction.
    assert False...
    contradiction.
  - Case e_output.
    dependent induction E2;
      eapply scongr_dual in SC;
      rewrite typ_dual_involution in SC;
      assert (SYMM2 := scongr_symmetric);
      unfold typ_dual in SC;
      fold typ_dual in SC;
      try inv DUAL;
      destruct H0;
      subst l0 v0;
      rewrite pdual_involution in *...
    assert (s = s0).
    eapply scongr_input2...
    subst s0.
    assert (typ_dual t0 == t1)...
    eapply scongr_dual in H;
      rewrite typ_dual_involution in *...
    assert False...
    contradiction.
    assert False...
    contradiction.
  - Case e_branch_l.
    gen t1 t2.
    dependent induction E2;
      intros;
      eapply scongr_dual in SC;
      rewrite typ_dual_involution in SC;
      assert (SYMM2 := scongr_symmetric);
      unfold typ_dual in SC;
      fold typ_dual in SC;
      try inv DUAL;
      try destruct H0;
      try subst l0 v0...
    + eapply SYMM2 in SC.
      assert False...
      contradiction.
    + eapply IHE1 in E2;
        try tauto.
      eapply wf_sum in WF1; unpack...
      unfold action_dual...
      eapply wf_sum in WF2; unpack...
      assert (SC1 : typ_dual t0 == t1).
      eapply scongr_sum in SC;
        intuition.
      assert (SC2: typ_dual (typ_dual t0) == typ_dual t1)...
      rewrite typ_dual_involution in SC2...
    + move E1 at bottom.
      move E2 at bottom.

      clear IHE1 IHE2.
      assert False.
      assert (K := equiv_scongr).
      eapply SYMM2,K in SC.
      destruct t1, t0;
        try contradiction;
        inv E1.
      simpl in SC;
        unpack;
        subst.
      * destruct WF2 as [_ NDL];
        unfold ndl in NDL;
        fold ndl in NDL;
          destruct NDL as ([[ABS _] | [_ NDL]] &NDL1 &NDL2).
        unfold tbranch, tbranch_r in ABS;
          intuition.
        eapply lts_output in E2.
        simpl in NDL.
        eapply NoDup_cons_iff in NDL;
          intuition.
      * contradiction.
        
  - Case e_branch_r.
    gen t1 t2.
    dependent induction E2;
      intros;
      eapply scongr_dual in SC;
      rewrite typ_dual_involution in SC;
      assert (SYMM2 := scongr_symmetric);
      unfold typ_dual in SC;
      fold typ_dual in SC;
      try inv DUAL;
      try destruct H0;
      try subst l0 v0...
    + eapply SYMM2 in SC.
      assert False...
      contradiction.
    + move E1 at bottom.
      move E2 at bottom.

      clear IHE1 IHE2.
      assert False.
      assert (K := equiv_scongr).
      eapply SYMM2,K in SC.
      destruct t1, t0;
        try contradiction;
        try inv E2.
      simpl in SC;
        unpack;
        subst.
      * destruct WF1 as [_ NDL];
        unfold ndl in NDL;
        fold ndl in NDL;
          destruct NDL as ([[_ NDL]| [ABS _]] &NDL1 &NDL2).
        eapply lts_input in E1.
        simpl in NDL.
        eapply NoDup_cons_iff in NDL;
          intuition.
        unfold tselect, tselect_r in ABS;
          intuition.
      * contradiction.
      
    +  eapply IHE1 in E2;
         try tauto...
       eapply wf_sum in WF1; unpack...
       unfold action_dual...
       eapply wf_sum in WF2; unpack...
       assert (SC1 : typ_dual t3 == t2).
       eapply scongr_sum in SC;
         intuition.
       assert (SC2: typ_dual (typ_dual t3) == typ_dual t2)...
       rewrite typ_dual_involution in SC2...
       
  -  Case e_select_l.
     gen t1 t2.
     dependent induction E2;
       intros;
       eapply scongr_dual in SC;
       rewrite typ_dual_involution in SC;
       assert (SYMM2 := scongr_symmetric);
       unfold typ_dual in SC;
       fold typ_dual in SC;
       try inv DUAL;
       try destruct H0;
       try subst l0 v0...
     eapply SYMM2 in SC.
     assert False...
     contradiction.
     eapply IHE1 in E2;
       try tauto.
     eapply wf_sum in WF1; unpack...
     simpl...
     eapply wf_sum in WF2; unpack...
     assert (SC1 : typ_dual t0 == t1).
     eapply scongr_sum in SC;
       intuition.
     simpl...
     
     assert (SC2: typ_dual (typ_dual t0) == typ_dual t1)...
     rewrite typ_dual_involution in SC2...
     move E1 at bottom.
     move E2 at bottom.

     clear IHE1 IHE2.
     assert False.
     assert (K := equiv_scongr).
     eapply SYMM2,K in SC.
     destruct t1, t0;
       try contradiction;
       try inv E1.
     simpl in SC;
       unpack;
       subst.
     * destruct WF2 as [_ NDL];
         unfold ndl in NDL;
         fold ndl in NDL;
         destruct NDL as ([[_ NDL]| [ABS _]] &NDL1 &NDL2).
       eapply lts_input in E2.
       simpl in NDL.
       eapply NoDup_cons_iff in NDL;
         intuition.
       unfold tselect, tselect_r in ABS;
         intuition.
     * contradiction.

  -  Case e_select_r.
     gen t1 t2.
     dependent induction E2;
       intros;
       eapply scongr_dual in SC;
       rewrite typ_dual_involution in SC;
       assert (SYMM2 := scongr_symmetric);
       unfold typ_dual in SC;
       fold typ_dual in SC;
       try inv DUAL;
       try destruct H0;
       try subst l0 v0...

      + eapply SYMM2 in SC.
      assert False...
      contradiction.
    + move E1 at bottom.
      move E2 at bottom.

      clear IHE1 IHE2.
      assert False.
      assert (K := equiv_scongr).
      eapply SYMM2,K in SC.
      destruct t1, t0;
        try contradiction;
        try inv E2.
      simpl in SC;
        unpack;
        subst.
      * destruct WF1 as [_ NDL];
        unfold ndl in NDL;
        fold ndl in NDL;
          destruct NDL as ([[ABS _] | [_ NDL]] &NDL1 &NDL2).
        unfold tbranch, tbranch_r in ABS;
          intuition.
        eapply lts_output in E1.
        simpl in NDL.
        eapply NoDup_cons_iff in NDL;
          intuition.
      * contradiction.

    +  eapply IHE1 in E2;
         try tauto...
       eapply wf_sum in WF1; unpack...
       unfold action_dual...
       eapply wf_sum in WF2; unpack...
       assert (SC1 : typ_dual t3 == t2).
       eapply scongr_sum in SC;
         intuition.
       assert (SC2: typ_dual (typ_dual t3) == typ_dual t2)...
       rewrite typ_dual_involution in SC2...

  - inv DUAL.

  - inv DUAL.

Qed.

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

Lemma types_struct G H M1 M2 U:
  types_session G H M1 U ->
  proc_equiv M1 M2 ->
  types_session G H M2 U.
Proof with eauto using scongr_dual.
  introv TC ST.
  destruct ST...
  inv TC...
  remember (pdual p) as q.
  assert (EQ: p = pdual q).
  subst; rewrite pdual_involution...
  rewrite EQ.
  eapply ts_parallel;
    subst;
    try rewrite pdual_involution...
  assert (SYMM2 := scongr_symmetric);
    assert (typ_dual (typ_dual T1) == typ_dual T2)...
  rewrite typ_dual_involution in H0...
Qed.

Lemma substT_skip X T:
  X £ T = typ_bot ->
  T = typ_bot.
Proof with eauto.
  introv ABS.
  dependent induction T;
    unfold substT in ABS;
    fold substT in ABS;
    try destruct ( X =? v);
    try discriminate...
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
  wfm (single_session M1).
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
  wfm (single_session M2).
Proof with eauto.
  introv WF.
  induction M1, M2;
    unfold wfm,wfp,ndp,ndP,bv,bvP in *;
    fold bv in *;
    fold bvP in *;
    repeat rewrite no_dup_iff in *;
    intuition.
Qed.

Lemma equiv_comp R X T U:
  equiv R ->
  R (typ_mu X T) U ->
  R (X £ T) U.
Proof with eauto.
  introv EQ REL.
  eapply EQ in REL.
  destruct U; intuition...
Qed.

Lemma scongr_comp X T U:
  typ_mu X T == U ->
  X £ T == U.
Proof with eauto.
  introv SC.
  destruct SC.
  eapply equiv_comp in H0...
  destruct H; intuition. 
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
    
(** Subject reduction *)
Lemma subject_reduction U M a M' U':
  closedS M ->
  wfm M ->
  types_session empty_env empty_penv M U ->
  lts M a M' ->
  typ_lts U a U' ->
  types_session  empty_env empty_penv M' U'.
Proof
  with
  eauto
  using
  substitution,
    wf_input, wf_output, 
    wf_substT,
    scongr_dual,
    wf_sum_out_false_l, wf_sum_inp_false_l,
    wf_sum_out_false_r, wf_sum_inp_false_r,
    lts_input_output_false,
    scongr_input, scongr_output,
    lts_typ_mu_output_false, lts_typ_mu_input_false,
    lts_input_typ, lts_output_typ,
    elts_dual_scongr,
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
  
  introv CLS WF TS LTS ELTS.
  gen U U'.
  dependent induction LTS; intros;
    assert (WFM := WF);
    remember empty_env as G;
    remember empty_penv as K.

    try destruct WF as [NDP NDM]...

  - Case r_input.

    try destruct WF as [NDP NDM].
    inverts TS as WF TC.
    inverts TC as TC1.
    inverts ELTS as E1.
    assert (ST : stypes G (expr_val v) s)...
    
  - Case r_output.

    try destruct WF as [NDP NDM].
    inverts TS as WF TC.
    
    dependent induction TC;
      inv ELTS...
    
    eapply IHTC...

    eapply wf_sum in WF as (WF1 &WF2)...

    assert False...
    contradiction.
    
    assert False...
    contradiction.

    eapply IHTC...
    eapply wf_sum in WF as (WF1 &WF2)...

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
    
    * inverts ELTS as E1...
      inverts E1 as SUMRED...
      
      ** eapply IHLTS...
         econstructor...
         eapply wf_sum in WF.
         intuition.
      **
        eapply IHLTS with (U := typ_sum t0 t3)...
        econstructor...
        eapply wf_sum in WF.
        intuition.
      **
        eapply IHLTS with (U := typ_sum t0 t3)...
        econstructor...
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
            eapply IHLTS...
            econstructor...
            eapply wf_sum in WF.
            intuition.
          ***
            eapply IHLTS with (U := typ_sum t0 t3)...
            econstructor...
            eapply wf_sum in WF.
            intuition.
          ***
            eapply IHLTS with (U := typ_sum t0 t3)...
            econstructor...
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

  - Case r_comm.

    try destruct WF as [NDP NDM].
    assert (CL: closedS (single_session (pdual p, Q))/\
                  closedS (single_session (p, P))).
    unfold closedS in CLS; intuition.
    destruct CL as (CLQ &CLP).
    
    inverts TS as TC1 TC2 EQ1 EQ2 DUAL.
    inverts TC1 as WF1 TC1.
    inverts TC2 as WF2 TC2.
    inverts ELTS as E1.
    
    move LTS1 at bottom.
    move LTS2 at bottom.

    assert (EX1: exists U1,
               typ_lts T1 (ainput (pdual p) l v) U1)...
    assert (EX2: exists U2,
               typ_lts T2 (aoutput (pdual (pdual p)) l v) U2)...
    eapply lts_output_typ with (p := pdual p);
      try rewrite pdual_involution...
    destruct EX1 as (U1 &E1).
    destruct EX2 as (U2 &E2).
    rewrite pdual_involution in E2.
    assert (TTC1:
             types_session G K (single_session (p, P)) T1)...
    eapply IHLTS1 in TTC1...
    assert (TTC2:
             types_session G K (single_session (pdual p, Q)) T2)...
    eapply IHLTS2 with (U' := U2)in TTC2...

    assert (U1 == typ_dual U2)...
    assert (IH: typ_dual (typ_dual T1) == typ_dual T2)...
    eapply elts_dual_scongr in IH;
      try rewrite typ_dual_involution...
    simpl...
    econstructor...
    eapply scongr_dual in H...
    rewrite typ_dual_involution in H...

  - Case r_rec.

    try destruct WF as [WFP1 WFP2].
    try destruct WFP1 as [NDP1 NDM1].
    try destruct WFP2 as [NDP2 NDM2].


    inv ELTS.
    inv TS.
    remember (shiftP M (proc_mu X P)) as RP.
    
    assert (CLMU: closedP (proc_mu X P)).
    unfold closedS in CLS. intuition.
    assert (IH: closedP RP).
    subst...
    
    inverts TS as TS1 TS2 SC DUAL PDUAL.
    assert (TS0 := TS1).
    inverts TS0 as WF TC.
    inverts TC...
    
    assert (NIN: ~ In X (bvP P)).
    intros ABS.
    unfold ndP,bvP in NDM1; fold bvP in NDM1.
    eapply NoDup_cons_iff in NDM1.
    intuition.

    remember T as T3.
    eapply types_substP
      with
      (P := P)
      (T := (typ_mu t0 T3))
      (U := t0 £ T3) in IH...
    move TS2 at bottom.

    assert (typ_dual (t0 £ T3) ==  T2).
    inv SC.
    assert (x  (typ_dual (t0 £ T)) T2).
    simpl in H1.
    assert (x (t0 £ (typ_dual T)) T2).
    eapply equiv_comp...
    inv H2...
    destruct H0; intuition.
    rewrite dual_substT...

    prove_scongr x...
    eapply ts_parallel with (T1 := t0 £ T3)...

    inv TS1...
    assert
      (DIS :
        disjoint
          (bv (proc_mu X P))
          (bv (shiftP M (proc_mu X P))))...
    assert
      (DIS :
        disjoint
          (bvP (proc_mu X P))
          (bvP (shiftP M (proc_mu X P))))...
    unfold bvP in DIS;
      fold bvP in DIS;
      eapply disjoint_l_cons in DIS as [W _];
      subst...

    inv TS1...

    erewrite <-shift_empty_env, <-shift_empty_penv...

  - Case r_true.

    try destruct WF as [WFP1 WFP2].
    try destruct WFP1 as [NDP1 NDM1].
    try destruct WFP2 as [NDP2 NDM2].

    inv ELTS.
    assert (IH: closedS (single_session (p, P1))).
    unfold closedS in *;
      destruct CLS as [CLS1 CLS2];
      eapply closed_cond in CLS1 as [J _]...
    inverts TS as TS1 TS2.
    inverts TS1 as WF TC.
    inverts TC...

  - Case r_false.

    try destruct WF as [WFP1 WFP2].
    try destruct WFP1 as [NDP1 NDM1].
    try destruct WFP2 as [NDP2 NDM2].

    inv ELTS.
    assert (IH: closedS (single_session (p, P1))).
    unfold closedS in *;
      destruct CLS as [CLS1 CLS2];
      eapply closed_cond in CLS1 as [J _]...
    inverts TS as TS1 TS2.
    inverts TS1 as WF TC.
    inverts TC...
    
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
    intros...
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

Lemma lts_typ_ltsM M0 a G H M T:
  lts M0 a M ->
  types_session G H M0 T ->
  exists U,
    typ_lts T a U.
Proof with eauto using lts_typ_lts.
  introv LTS TC.
  gen G H T.
  dependent induction LTS;
    intros;
    inv TC...
  eapply types_struct in H...
Qed.

Theorem subject_reduction_standard U M a M':
  closedS M ->
  wfm M ->
  types_session empty_env empty_penv M U ->
  lts M a M' ->
  exists U', 
    typ_lts U a U' /\
      types_session  empty_env empty_penv M' U'.
Proof with eauto using subject_reduction.
  intros;
    destruct M, p;
    inv H1...
  - eapply lts_typ_lts in H2 as K;
      unpack...
  - eapply lts_typ_ltsM in H2 as K;
      unpack...
Qed.
