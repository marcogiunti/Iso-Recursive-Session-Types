

Require Import List Lia Permutation.
Require Import Coq.Logic.Classical_Prop Coq.Arith.Wf_nat.
Require Import Program.Equality.
Require Import header operations iso_mpst CpdtTactics LibTactics.
Import ListNotations.

(** * Part 1: rearranging sessions *)

Fixpoint leaves (M : session) : list (participant * process) :=
  match M with
  | single_session x => [x]
  | parallel_session A B => leaves A ++ leaves B
  end.

Inductive equiv_star : session -> session -> Prop :=
| es_refl M :
  equiv_star M M
| es_step M1 M2 M3 :
  proc_equiv M1 M2 ->
  equiv_star M2 M3 ->
  equiv_star M1 M3.

Hint Constructors equiv_star.

Lemma equiv_star_trans M1 M2 M3 :
  equiv_star M1 M2 -> equiv_star M2 M3 -> equiv_star M1 M3.
Proof. induction 1; eauto. Qed.

Lemma equiv_star_one M1 M2 : proc_equiv M1 M2 -> equiv_star M1 M2.
Proof. eauto. Qed.

Lemma equiv_star_par_l A A' B :
  equiv_star A A' -> equiv_star (parallel_session A B) (parallel_session A' B).
Proof. induction 1; eauto using pe_par_l. Qed.

Lemma equiv_star_par_r A B B' :
  equiv_star B B' -> equiv_star (parallel_session A B) (parallel_session A B').
Proof.
  intro E.
  eapply es_step; [apply pe_commut |].
  eapply equiv_star_trans; [apply equiv_star_par_l; exact E |].
  eapply es_step; [apply pe_commut | constructor].
Qed.

Lemma lts_equiv_star M N a N' :
  equiv_star M N -> lts N a N' -> lts M a N'.
Proof.
  induction 1; intros L; auto.
  eapply r_struct; [eauto | apply IHequiv_star; exact L | apply pe_refl].
Qed.

Lemma leaves_equiv M N :
  proc_equiv M N -> Permutation (leaves M) (leaves N).
Proof.
  induction 1; simpl.
  - reflexivity.
  - apply Permutation_app_comm.
  - rewrite app_assoc; reflexivity.
  - rewrite app_assoc; reflexivity.
  - apply Permutation_app_tail; assumption.
Qed.

Lemma leaves_equiv_star M N :
  equiv_star M N -> Permutation (leaves M) (leaves N).
Proof.
  induction 1; [reflexivity |].
  eapply perm_trans; [apply leaves_equiv; eassumption | assumption].
Qed.

Lemma leaves_nonempty M : leaves M <> [].
Proof.
  induction M; simpl; [discriminate |].
  destruct (leaves M1); [contradiction | discriminate].
Qed.

Lemma pull_left M x :
  In x (leaves M) ->
  (exists A B, M = parallel_session A B) ->
  exists R, equiv_star M (parallel_session (single_session x) R).
Proof.
  induction M as [y | A IHA B IHB]; intros IN PAR.
  - destruct PAR as (A & B & E); discriminate.
  - simpl in IN. apply in_app_or in IN as [IN | IN].
    + destruct A as [y | A1 A2].
      * simpl in IN; destruct IN as [<- | []].
        exists B; constructor.
      * destruct (IHA IN ltac:(eauto)) as (R & E).
        exists (parallel_session R B).
        eapply equiv_star_trans; [apply equiv_star_par_l; exact E |].
        apply equiv_star_one, pe_assoc_l.
    + destruct B as [y | B1 B2].
      * simpl in IN; destruct IN as [<- | []].
        exists A. apply equiv_star_one, pe_commut.
      * destruct (IHB IN ltac:(eauto)) as (R & E).
        exists (parallel_session R A).
        eapply es_step; [apply pe_commut |].
        eapply equiv_star_trans; [apply equiv_star_par_l; exact E |].
        apply equiv_star_one, pe_assoc_l.
Qed.

Lemma pull_left_ex M x :
  In x (leaves M) ->
  (exists A B, M = parallel_session A B) ->
  exists R, equiv_star M (parallel_session (single_session x) R).
Proof. apply pull_left. Qed.

Lemma length_leaves_parallel M :
  2 <= length (leaves M) -> exists A B, M = parallel_session A B.
Proof.
  destruct M as [x | A B]; simpl; intro L; [lia | eauto].
Qed.

Lemma pull_pair M x y :
  In x (leaves M) ->
  In y (leaves M) ->
  x <> y ->
  3 <= length (leaves M) ->
  exists S,
    equiv_star M
      (parallel_session
         (parallel_session (single_session x) (single_session y)) S).
Proof.
  intros INx INy NE L.
  destruct (pull_left M x INx (length_leaves_parallel M ltac:(lia))) as (R & E1).
  pose proof (leaves_equiv_star _ _ E1) as P1. simpl in P1.
  assert (INy' : In y (leaves R)).
  { apply (Permutation_in _ P1) in INy. destruct INy as [-> | ?]; tauto. }
  assert (LR : 2 <= length (leaves R)).
  { apply Permutation_length in P1. simpl in P1. lia. }
  destruct (pull_left R y INy' (length_leaves_parallel R LR)) as (S & E2).
  exists S.
  eapply equiv_star_trans; [exact E1 |].
  eapply equiv_star_trans; [apply equiv_star_par_r; exact E2 |].
  apply equiv_star_one, pe_assoc_r.
Qed.

Lemma rearrangement M :
  (forall x, In x (leaves M) -> 2 <= length (leaves M) ->
     exists R, equiv_star M (parallel_session (single_session x) R)) /\
  (forall x y, In x (leaves M) -> In y (leaves M) -> x <> y -> 3 <= length (leaves M) ->
     exists S, equiv_star M
                 (parallel_session (parallel_session (single_session x) (single_session y)) S)).
Proof.
  split.
  - intros x IN L. apply pull_left; [exact IN | apply length_leaves_parallel; exact L].
  - intros x y INx INy NE L. apply pull_pair; assumption.
Qed.

(** * Part 2: threads of stuck sessions *)

Lemma eval_total e s :
  stypes empty_env e s ->
  exists v, eval_expr e v /\ stypes empty_env (expr_val v) s.
Proof with eauto.
  introv ST.
  induction ST;
    try (eexists; split; constructor; fail).
  - inv H.
  - destruct IHST as (v & EV & SV). inv SV.
    eexists; split; econstructor...
  - destruct IHST as (v & EV & SV). inv SV.
    eexists; split; econstructor...
Qed.

Definition passive (P : process) :=
  match P with
  | proc_zero
  | proc_input _ _ _ _ _
  | proc_output _ _ _ _ _
  | proc_sum _ _ => True
  | _ => False
  end.

Lemma threads_leaf G H M d p P :
  types_threads G H M d ->
  In (p, P) (leaves M) ->
  exists T, wf T /\ types G H P T /\ d p = Some T.
Proof.
  induction 1; simpl; intros IN.
  - destruct IN as [E | []]; inversion E; subst.
    exists T1; repeat split; auto using singleton_eq.
  - apply in_app_or in IN as [IN | IN].
    + destruct (IHtypes_threads1 IN) as (T & WF & TP & E).
      exists T; repeat split; auto.
      unfold cat; rewrite E; reflexivity.
    + destruct (IHtypes_threads2 IN) as (T & WF & TP & E).
      exists T; repeat split; auto.
      unfold cat.
      destruct (pf p) as [_ K].
      rewrite K; [exact E | rewrite E; discriminate].
Qed.

Lemma types_session_threads G H s1 s2 d :
  types_session G H (parallel_session s1 s2) d ->
  types_threads G H (parallel_session s1 s2) d.
Proof.
  intro TS. eapply ts_parallel_inv in TS as (TT & _); exact TT.
Qed.

Lemma active_steps h p P T R :
  types empty_env h P T ->
  (forall X, P <> proc_var X) ->
  ~ passive P ->
  exists a M',
    elts_action a /\
      lts (parallel_session (single_session (p, P)) R) a M'.
Proof.
  intros TP NV NP.
  destruct P; simpl in NP; try tauto.
  -
    inv TP.
    match goal with ST: stypes _ _ styp_bool |- _ =>
      destruct (eval_total _ _ ST) as (v & EV & SV) end.
    inv SV. destruct x.
    + do 2 eexists; split; [right; eauto | apply r_true; exact EV].
    + do 2 eexists; split; [right; eauto | apply r_false; exact EV].
  - exfalso; eapply NV; eauto.
  -
    do 2 eexists; split; [left; eauto |].
    eapply r_rec with (M := S (max_seed (proc_mu p0 P))); [lia | reflexivity].
Qed.

Lemma no_var_empty G P T X :
  types G empty_penv P T -> P <> proc_var X.
Proof.
  intros TP E; subst. inv TP.
  match goal with K: empty_penv _ = Some _ |- _ => discriminate K end.
Qed.

Lemma stuck_passive M d :
  types_session empty_env empty_penv M d ->
  2 <= length (leaves M) ->
  (forall a M', elts_action a -> ~ lts M a M') ->
  forall p P, In (p, P) (leaves M) -> passive P.
Proof.
  intros TS L STUCK p P IN.
  destruct (length_leaves_parallel M L) as (A & B & ->).
  apply types_session_threads in TS.
  destruct (threads_leaf _ _ _ _ _ _ TS IN) as (T & WF & TP & _).
  assert (DEC : passive P \/ ~ passive P) by (destruct P; simpl; tauto).
  destruct DEC as [PA | NP]; [exact PA | exfalso].
  destruct (pull_left _ _ IN ltac:(eauto)) as (R & E).
  destruct (active_steps _ p P T R TP (fun X => no_var_empty _ _ _ X TP) NP)
    as (a & M' & EA & ST).
  eapply STUCK; [exact EA |].
  eapply lts_equiv_star; [exact E | exact ST].
Qed.

(** * Well-formed processes and sessions *)

Definition pol_beq (a b : pol) : bool :=
  match a, b with
  | input, input | output, output => true
  | _, _ => false
  end.

Fixpoint labelsP (P : process) : list label :=
  match P with
  | proc_input _ l _ _ _
  | proc_output _ l _ _ _ => [l]
  | proc_conditional _ P1 P2
  | proc_sum P1 P2 => labelsP P1 ++ labelsP P2
  | _ => []
  end.

Fixpoint polarityP (P : process) : option pol :=
  match P with
  | proc_input _ _ _ _ _ => Some input
  | proc_output _ _ _ _ _ => Some output
  | proc_conditional _ P1 P2
  | proc_sum P1 P2 =>
      match polarityP P1, polarityP P2 with
      | Some a, Some b => if pol_beq a b then Some a else None
      | _, _ => None
      end
  | _ => None
  end.

Fixpoint participantP (P : process) : option participant :=
  match P with
  | proc_input r _ _ _ _
  | proc_output r _ _ _ _ => Some r
  | proc_conditional _ P1 P2
  | proc_sum P1 P2 =>
      match participantP P1, participantP P2 with
      | Some r1, Some r2 => if pbeq r1 r2 then Some r1 else None
      | _, _ => None
      end
  | _ => None
  end.

Definition uniformP (P1 P2 : process) :=
  polarityP (proc_sum P1 P2) <> None /\
    participantP (proc_sum P1 P2) <> None /\
    NoDup (labelsP (proc_sum P1 P2)).

Inductive wf_proc : process -> Prop :=
| wf_inp_p r l x s P :
  wf_proc P -> wf_proc (proc_input r l x s P)
| wf_out_p r l e s P :
  wf_proc P -> wf_proc (proc_output r l e s P)
| wf_sum_p P1 P2 :
  uniformP P1 P2 -> wf_proc P1 -> wf_proc P2 -> wf_proc (proc_sum P1 P2)
| wf_if_p e P Q :
  wf_proc P -> wf_proc Q -> wf_proc (proc_conditional e P Q)
| wf_end_p :
  wf_proc proc_zero
| wf_rec_p X P :
  wf_proc P -> wf_proc (proc_mu X P)
| wf_var_p X :
  wf_proc (proc_var X).

Hint Constructors wf_proc.

Fixpoint wf_session (M : session) : Prop :=
  match M with
  | single_session (_, P) => wf_proc P
  | parallel_session A B => wf_session A /\ wf_session B
  end.

Section CondSummand.
  Let q := pyp 1.
  Let l1 := lbl 1.
  Let l2 := lbl 2.
  Let Bq := proc_input q l2 (evar_var 0) styp_unit proc_zero.
  Let Pc := proc_sum (proc_input q l1 (evar_var 0) styp_unit proc_zero)
                     (proc_conditional (expr_val (value_bool true)) Bq Bq).

  Lemma cond_summand_types :
    types empty_env empty_penv Pc
      (typ_sum (typ_input q l1 styp_unit typ_end) (typ_input q l2 styp_unit typ_end)).
  Proof.
    unfold Pc, Bq.
    apply t_branch.
    - eapply t_input with (pf := eq_refl); constructor.
    - constructor; [constructor |
        eapply t_input with (pf := eq_refl); constructor |
        eapply t_input with (pf := eq_refl); constructor].
  Qed.

  Lemma cond_summand_not_wf : ~ wf_proc Pc.
  Proof.
    unfold Pc, Bq; intro W; inversion W; subst.
    match goal with U: uniformP _ _ |- _ => destruct U as (_ & _ & ND) end.
    simpl in ND.
    inversion ND; subst.
    match goal with K: NoDup (l2 :: [l2]) |- _ => inversion K; subst end.
    match goal with K: ~ In l2 [l2] |- _ => apply K; left; reflexivity end.
  Qed.
End CondSummand.

Definition consumed (M : session) :=
  forall p P, In (p, P) (leaves M) -> P = proc_zero.

Definition session_deadlock (M : session) :=
  (forall a M', elts_action a -> ~ lts M a M') /\ ~ consumed M.

(** * Part 3a: type-level facts about remnants *)

Lemma sd_typ_lts_typ_lts t a t' o :
  sd_typ_lts t a t' o -> typ_lts t a t'.
Proof. induction 1; eauto. Qed.

Lemma value_sort_unique v S1 S2 :
  stypes empty_env (expr_val v) S1 ->
  stypes empty_env (expr_val v) S2 ->
  S1 = S2.
Proof. intros A B; inversion A; subst; inversion B; reflexivity. Qed.

Lemma typ_lts_input_sort t q l v t' :
  typ_lts t (ainput q l v) t' ->
  exists S,
    stypes empty_env (expr_val v) S /\
      forall w, stypes empty_env (expr_val w) S -> typ_lts t (ainput q l w) t'.
Proof.
  intro H; dependent induction H.
  - exists s; split; auto.
  - destruct (IHtyp_lts q l v eq_refl) as (S & SV & K).
    exists S; split; auto.
  - destruct (IHtyp_lts q l v eq_refl) as (S & SV & K).
    exists S; split; auto.
Qed.

Lemma typ_lts_output_same_sort t r l v w u1 u2 :
  wf t ->
  typ_lts t (aoutput r l v) u1 ->
  typ_lts t (aoutput r l w) u2 ->
  exists S,
    stypes empty_env (expr_val v) S /\ stypes empty_env (expr_val w) S.
Proof.
  intros WF H1; revert w u2.
  dependent induction H1; intros w u2 H2; inversion H2; subst;
    try (pose proof (wf_sum _ _ WF) as [WF1 WF2]); eauto.
  all: exfalso; eapply tselect_absurd;
    [ exact WF
    | eapply typ_lts_output_label; eassumption
    | eapply typ_lts_output_label; eassumption ].
Qed.

Fixpoint tsize (t : typ) : nat :=
  match t with
  | typ_sum t1 t2 => S (tsize t1 + tsize t2)
  | typ_input _ _ _ c
  | typ_output _ _ _ c
  | typ_mu _ c => S (tsize c)
  | _ => 1
  end.

Lemma tsize_pos t : 1 <= tsize t.
Proof. destruct t; simpl; lia. Qed.

Lemma rem_size t a t' o :
  sd_typ_lts t a t' o ->
  forall R, o = Some R -> tsize R < tsize t.
Proof.
  induction 1; intros R E; try discriminate.
  - destruct opt1 as [r1 |]; simpl in E; inversion E; subst; simpl.
    + specialize (IHsd_typ_lts r1 eq_refl); lia.
    + lia.
  - destruct opt2 as [r2 |]; simpl in E; inversion E; subst; simpl.
    + specialize (IHsd_typ_lts r2 eq_refl); lia.
    + lia.
  - destruct opt1 as [r1 |]; simpl in E; inversion E; subst; simpl.
    + specialize (IHsd_typ_lts r1 eq_refl); lia.
    + lia.
  - destruct opt2 as [r2 |]; simpl in E; inversion E; subst; simpl.
    + specialize (IHsd_typ_lts r2 eq_refl); lia.
    + lia.
Qed.

Lemma rem_sub t a t' o :
  sd_typ_lts t a t' o ->
  forall R, o = Some R ->
  forall q l w u,
    (typ_lts R (ainput q l w) u -> typ_lts t (ainput q l w) u) /\
      (typ_lts R (aoutput q l w) u -> typ_lts t (aoutput q l w) u).
Proof.
  induction 1; intros R E q0 l0 w u; try discriminate.
  all: match goal with
       | O: option typ |- _ => destruct O as [r |] eqn:EO
       end; simpl in E; inversion E; subst.
  all: try (split; intro L; eauto using e_branch_l, e_branch_r, e_select_l, e_select_r; fail).
  all: destruct (IHsd_typ_lts r eq_refl q0 l0 w u) as [IHi IHo];
       split; intro L; inversion L; subst;
       eauto using e_branch_l, e_branch_r, e_select_l, e_select_r.
Qed.

Lemma rem_keeps_out t r l v t' o :
  sd_typ_lts t (aoutput r l v) t' o ->
  forall l' w u,
    typ_lts t (aoutput r l' w) u ->
    l' <> l ->
    exists R, o = Some R /\ typ_lts R (aoutput r l' w) u.
Proof.
  intro H; dependent induction H; intros l' w u L NE.
  - inversion L; subst; contradiction.
  - inversion L; subst.
    + destruct (IHsd_typ_lts r l v eq_refl l' w u ltac:(eauto) NE) as (R & E & LR).
      subst; simpl; eauto using e_select_l.
    + destruct opt1 as [r1 |]; simpl; eexists; split; eauto using e_select_r.
  - inversion L; subst.
    + destruct opt2 as [r2 |]; simpl; eexists; split; eauto using e_select_l.
    + destruct (IHsd_typ_lts r l v eq_refl l' w u ltac:(eauto) NE) as (R & E & LR).
      subst; simpl; eauto using e_select_r.
Qed.

Lemma rem_top_incl t a t' o :
  sd_typ_lts t a t' o -> forall R, o = Some R -> incl (top R) (top t).
Proof.
  induction 1; intros R E; try discriminate.
  all: match goal with
       | O: option typ |- _ => destruct O as [r |]
       end; simpl in E; inversion E; subst; simpl.
  all: try (apply incl_app; [apply incl_appl; eauto | apply incl_appr; apply incl_refl]; fail).
  all: try (apply incl_app; [apply incl_appl; apply incl_refl | apply incl_appr; eauto]; fail).
  all: try (apply incl_appr; apply incl_refl; fail).
  all: try (apply incl_appl; apply incl_refl; fail).
Qed.

Lemma rem_labels_in t q l v t' o :
  sd_typ_lts t (ainput q l v) t' o ->
  (o = None -> tbranch_labels t = [l]) /\
    (forall R, o = Some R -> Permutation (tbranch_labels t) (l :: tbranch_labels R)).
Proof.
  intro H; dependent induction H.
  - split; [reflexivity | discriminate].
  - destruct (IHsd_typ_lts q l v eq_refl) as [N SM].
    split; [destruct opt1; discriminate |].
    intros R E; destruct opt1 as [r1 |]; simpl in E; inversion E; subst; simpl.
    + specialize (SM r1 eq_refl).
      apply Permutation_app_tail with (tl := tbranch_labels t2) in SM; exact SM.
    + rewrite (N eq_refl); reflexivity.
  - destruct (IHsd_typ_lts q l v eq_refl) as [N SM].
    split; [destruct opt2; discriminate |].
    intros R E; destruct opt2 as [r2 |]; simpl in E; inversion E; subst; simpl.
    + specialize (SM r2 eq_refl).
      eapply perm_trans; [apply Permutation_app_head; exact SM |].
      apply Permutation_sym, Permutation_middle.
    + rewrite (N eq_refl). apply Permutation_sym, Permutation_cons_append.
Qed.

Lemma rem_labels_out t q l v t' o :
  sd_typ_lts t (aoutput q l v) t' o ->
  (o = None -> tselect_labels t = [l]) /\
    (forall R, o = Some R -> Permutation (tselect_labels t) (l :: tselect_labels R)).
Proof.
  intro H; dependent induction H.
  - split; [reflexivity | discriminate].
  - destruct (IHsd_typ_lts q l v eq_refl) as [N SM].
    split; [destruct opt1; discriminate |].
    intros R E; destruct opt1 as [r1 |]; simpl in E; inversion E; subst; simpl.
    + specialize (SM r1 eq_refl).
      apply Permutation_app_tail with (tl := tselect_labels t2) in SM; exact SM.
    + rewrite (N eq_refl); reflexivity.
  - destruct (IHsd_typ_lts q l v eq_refl) as [N SM].
    split; [destruct opt2; discriminate |].
    intros R E; destruct opt2 as [r2 |]; simpl in E; inversion E; subst; simpl.
    + specialize (SM r2 eq_refl).
      eapply perm_trans; [apply Permutation_app_head; exact SM |].
      apply Permutation_sym, Permutation_middle.
    + rewrite (N eq_refl). apply Permutation_sym, Permutation_cons_append.
Qed.

Lemma rem_tbranch_r t q l v t' o :
  sd_typ_lts t (ainput q l v) t' o ->
  tbranch_r t -> forall R, o = Some R -> tbranch_r R.
Proof.
  intro H; dependent induction H; intros TB R E; try discriminate;
    simpl in TB; destruct TB as [TB1 TB2].
  - destruct opt1 as [r1 |]; simpl in E; inversion E; subst; simpl; eauto.
  - destruct opt2 as [r2 |]; simpl in E; inversion E; subst; simpl; eauto.
Qed.

Lemma rem_tselect_r t q l v t' o :
  sd_typ_lts t (aoutput q l v) t' o ->
  tselect_r t -> forall R, o = Some R -> tselect_r R.
Proof.
  intro H; dependent induction H; intros TB R E; try discriminate;
    simpl in TB; destruct TB as [TB1 TB2].
  - destruct opt1 as [r1 |]; simpl in E; inversion E; subst; simpl; eauto.
  - destruct opt2 as [r2 |]; simpl in E; inversion E; subst; simpl; eauto.
Qed.

Lemma single_party_incl xs ys :
  incl xs ys -> xs <> [] -> single_party ys -> single_party xs.
Proof.
  intros I NE (_ & SP); split; auto.
Qed.

Lemma NoDup_perm_cons {A} (xs ys : list A) x :
  NoDup xs -> Permutation xs (x :: ys) -> NoDup ys.
Proof.
  intros ND P. apply (Permutation_NoDup P) in ND.
  apply NoDup_cons_iff in ND; tauto.
Qed.

Lemma wf_rem_in t q l v t' o :
  wf t ->
  sd_typ_lts t (ainput q l v) t' o ->
  forall R, o = Some R -> wf R.
Proof.
  intros WF H; revert WF; dependent induction H; intros WF R E; try discriminate.
  - assert (LT : typ_lts (typ_sum t1 t2) (ainput q l v) t')
      by (apply e_branch_l; eapply sd_typ_lts_typ_lts; eauto).
    unfold wf in WF; simpl in WF. destruct WF as [[[TB ND] | [TS ND]] [W1 W2]].
    all: try (exfalso; eapply tselect_input_false; [exact TS | exact LT]).
    destruct TB as [TRr SP]. simpl in TRr. destruct TRr as [TR1 TR2].
    destruct opt1 as [r1 |]; simpl in E; inversion E; subst; [| exact W2].
    assert (TRR : tbranch_r r1) by (eapply rem_tbranch_r; eauto).
    assert (NE1 : top r1 <> []) by (apply tbranchr_part; exact TRR).
    assert (I1 : incl (top r1) (top t1)) by (eapply rem_top_incl; eauto).
    destruct (rem_labels_in _ _ _ _ _ _ H) as [_ PL]. specialize (PL r1 eq_refl).
    assert (WR : wf r1) by (eapply IHsd_typ_lts; eauto).
    unfold wf; simpl. split; [left; split | split; [exact WR | exact W2]].
    + split; [simpl; tauto |].
      simpl in SP |- *. eapply single_party_incl; [| | exact SP].
      * apply incl_app; [apply incl_appl; exact I1 | apply incl_appr, incl_refl].
      * destruct (top r1); [contradiction | discriminate].
    + simpl in ND |- *. eapply NoDup_perm_cons; [exact ND |].
      exact (Permutation_app_tail _ PL).
  - assert (LT : typ_lts (typ_sum t1 t2) (ainput q l v) t')
      by (apply e_branch_r; eapply sd_typ_lts_typ_lts; eauto).
    unfold wf in WF; simpl in WF. destruct WF as [[[TB ND] | [TS ND]] [W1 W2]].
    all: try (exfalso; eapply tselect_input_false; [exact TS | exact LT]).
    destruct TB as [TRr SP]. simpl in TRr. destruct TRr as [TR1 TR2].
    destruct opt2 as [r2 |]; simpl in E; inversion E; subst; [| exact W1].
    assert (TRR : tbranch_r r2) by (eapply rem_tbranch_r; eauto).
    assert (NE2 : top r2 <> []) by (apply tbranchr_part; exact TRR).
    assert (I2 : incl (top r2) (top t2)) by (eapply rem_top_incl; eauto).
    destruct (rem_labels_in _ _ _ _ _ _ H) as [_ PL]. specialize (PL r2 eq_refl).
    assert (WR : wf r2) by (eapply IHsd_typ_lts; eauto).
    unfold wf; simpl. split; [left; split | split; [exact W1 | exact WR]].
    + split; [simpl; tauto |].
      simpl in SP |- *. eapply single_party_incl; [| | exact SP].
      * apply incl_app; [apply incl_appl, incl_refl | apply incl_appr; exact I2].
      * destruct (top t1); [destruct (top r2); [contradiction | discriminate] | discriminate].
    + simpl in ND |- *. eapply NoDup_perm_cons; [exact ND |].
      eapply perm_trans; [apply Permutation_app_head; exact PL |].
      apply Permutation_sym, Permutation_middle.
Qed.

Lemma wf_rem_out t q l v t' o :
  wf t ->
  sd_typ_lts t (aoutput q l v) t' o ->
  forall R, o = Some R -> wf R.
Proof.
  intros WF H; revert WF; dependent induction H; intros WF R E; try discriminate.
  - assert (LT : typ_lts (typ_sum t1 t2) (aoutput q l v) t')
      by (apply e_select_l; eapply sd_typ_lts_typ_lts; eauto).
    unfold wf in WF; simpl in WF. destruct WF as [[[TB ND] | [TS ND]] [W1 W2]].
    all: try (exfalso; eapply tbranch_output_false; [exact TB | exact LT]).
    destruct TS as [TRr SP]. simpl in TRr. destruct TRr as [TR1 TR2].
    destruct opt1 as [r1 |]; simpl in E; inversion E; subst; [| exact W2].
    assert (TRR : tselect_r r1) by (eapply rem_tselect_r; eauto).
    assert (NE1 : top r1 <> []) by (apply tselectr_part; exact TRR).
    assert (I1 : incl (top r1) (top t1)) by (eapply rem_top_incl; eauto).
    destruct (rem_labels_out _ _ _ _ _ _ H) as [_ PL]. specialize (PL r1 eq_refl).
    assert (WR : wf r1) by (eapply IHsd_typ_lts; eauto).
    unfold wf; simpl. split; [right; split | split; [exact WR | exact W2]].
    + split; [simpl; tauto |].
      simpl in SP |- *. eapply single_party_incl; [| | exact SP].
      * apply incl_app; [apply incl_appl; exact I1 | apply incl_appr, incl_refl].
      * destruct (top r1); [contradiction | discriminate].
    + simpl in ND |- *. eapply NoDup_perm_cons; [exact ND |].
      exact (Permutation_app_tail _ PL).
  - assert (LT : typ_lts (typ_sum t1 t2) (aoutput q l v) t')
      by (apply e_select_r; eapply sd_typ_lts_typ_lts; eauto).
    unfold wf in WF; simpl in WF. destruct WF as [[[TB ND] | [TS ND]] [W1 W2]].
    all: try (exfalso; eapply tbranch_output_false; [exact TB | exact LT]).
    destruct TS as [TRr SP]. simpl in TRr. destruct TRr as [TR1 TR2].
    destruct opt2 as [r2 |]; simpl in E; inversion E; subst; [| exact W1].
    assert (TRR : tselect_r r2) by (eapply rem_tselect_r; eauto).
    assert (NE2 : top r2 <> []) by (apply tselectr_part; exact TRR).
    assert (I2 : incl (top r2) (top t2)) by (eapply rem_top_incl; eauto).
    destruct (rem_labels_out _ _ _ _ _ _ H) as [_ PL]. specialize (PL r2 eq_refl).
    assert (WR : wf r2) by (eapply IHsd_typ_lts; eauto).
    unfold wf; simpl. split; [right; split | split; [exact W1 | exact WR]].
    + split; [simpl; tauto |].
      simpl in SP |- *. eapply single_party_incl; [| | exact SP].
      * apply incl_app; [apply incl_appl, incl_refl | apply incl_appr; exact I2].
      * destruct (top t1); [destruct (top r2); [contradiction | discriminate] | discriminate].
    + simpl in ND |- *. eapply NoDup_perm_cons; [exact ND |].
      eapply perm_trans; [apply Permutation_app_head; exact PL |].
      apply Permutation_sym, Permutation_middle.
Qed.

Lemma input_tbranch_r t q l v u :
  wf t -> typ_lts t (ainput q l v) u -> tbranch_r t.
Proof.
  intros WF L; destruct t; inversion L; subst; simpl; auto;
    unfold wf in WF; simpl in WF;
    destruct WF as [[[TB _] | [TS _]] _];
    try (destruct TB; assumption);
    exfalso; eapply tselect_input_false; eauto.
Qed.

Lemma output_tselect_r t q l v u :
  wf t -> typ_lts t (aoutput q l v) u -> tselect_r t.
Proof.
  intros WF L; destruct t; inversion L; subst; simpl; auto;
    unfold wf in WF; simpl in WF;
    destruct WF as [[[TB _] | [TS _]] _];
    try (destruct TS; assumption);
    exfalso; eapply tbranch_output_false; eauto.
Qed.

Lemma tbranch_r_no_output t q l v u : tbranch_r t -> ~ typ_lts t (aoutput q l v) u.
Proof. induction t; simpl; intros TB L; inversion L; subst; intuition eauto. Qed.

Lemma tselect_r_no_input t q l v u : tselect_r t -> ~ typ_lts t (ainput q l v) u.
Proof. induction t; simpl; intros TS L; inversion L; subst; intuition eauto. Qed.

Lemma tbranch_r_no_unfold t p u : tbranch_r t -> ~ typ_lts t (aunfold p) u.
Proof. destruct t; simpl; intros TB L; inversion L; tauto. Qed.

Lemma tselect_r_no_unfold t p u : tselect_r t -> ~ typ_lts t (aunfold p) u.
Proof. destruct t; simpl; intros TS L; inversion L; tauto. Qed.

Lemma input_party_unique t q q' l l' v v' u u' :
  wf t -> typ_lts t (ainput q l v) u -> typ_lts t (ainput q' l' v') u' -> q = q'.
Proof.
  intros WF L1 L2.
  destruct (typ_lts_input_top _ _ _ _ _ WF L1) as (x1 & E1).
  destruct (typ_lts_input_top _ _ _ _ _ WF L2) as (x2 & E2).
  rewrite E1 in E2; inversion E2; reflexivity.
Qed.

Lemma output_party_unique t q q' l l' v v' u u' :
  wf t -> typ_lts t (aoutput q l v) u -> typ_lts t (aoutput q' l' v') u' -> q = q'.
Proof.
  intros WF L1 L2.
  destruct (typ_lts_output_top _ _ _ _ _ WF L1) as (x1 & E1).
  destruct (typ_lts_output_top _ _ _ _ _ WF L2) as (x2 & E2).
  rewrite E1 in E2; inversion E2; reflexivity.
Qed.

Lemma remnants t a t' R :
  wf t ->
  sd_typ_lts t a t' (Some R) ->
  wf R /\
    ((exists q l v, a = ainput q l v) -> tbranch_r t -> tbranch_r R) /\
    ((exists q l v, a = aoutput q l v) -> tselect_r t -> tselect_r R) /\
    tsize R < tsize t /\
    (forall q l w u,
        (typ_lts R (ainput q l w) u -> typ_lts t (ainput q l w) u) /\
          (typ_lts R (aoutput q l w) u -> typ_lts t (aoutput q l w) u)) /\
    (forall r l v, a = aoutput r l v ->
       forall l' w u, typ_lts t (aoutput r l' w) u -> l' <> l ->
       typ_lts R (aoutput r l' w) u).
Proof.
  intros WF H.
  destruct a as [q l v | q l v | p | o].
  - refine (conj (wf_rem_in _ _ _ _ _ _ WF H R eq_refl) _).
    split; [intros _ TB; eapply rem_tbranch_r; eauto |].
    split; [intros (q' & l' & v' & E); discriminate |].
    split; [eapply rem_size; eauto |].
    split; [intros; eapply rem_sub; eauto |].
    intros r l0 v0 E; discriminate.
  - refine (conj (wf_rem_out _ _ _ _ _ _ WF H R eq_refl) _).
    split; [intros (q' & l' & v' & E); discriminate |].
    split; [intros _ TS; eapply rem_tselect_r; eauto |].
    split; [eapply rem_size; eauto |].
    split; [intros; eapply rem_sub; eauto |].
    intros r l0 v0 E l' w u L NE; inversion E; subst.
    destruct (rem_keeps_out _ _ _ _ _ _ H _ _ _ L NE) as (R' & ER & LR).
    inversion ER; subst; exact LR.
  - inversion H.
  - inversion H.
Qed.

(** * Part 3b: compliance of residual environments *)

Definition res_env (d : part_env) r s (o1 : option typ) t2 : part_env :=
  (d <- r #: (match o1 with Some t1 => t1 | None => typ_end end)) <- s #: t2.

Lemma res_dcompliance d1 k1 k2 D r s l v tr ts tr' ts' o1 t2 :
  wfE d1 ->
  In (d1, k1) D ->
  dcompliance d1 k1 D ->
  d1 r = Some tr ->
  d1 s = Some ts ->
  sd_typ_lts tr (ainput s l v) tr' o1 ->
  sd_typ_lts ts (aoutput r l v) ts' (Some t2) ->
  dcompliance (res_env d1 r s o1 t2) k2 (removeD k1 D).
Proof.
  intros WF IN CMP Er Es SR SS.
  assert (MIN : ~ notMinimal d1) by (eapply dcompliance_minimal; eauto).
  unfold dcompliance in *. intros W tbl Z l2 HW FW HZ DC.
  destruct (dclosure_inv _ _ _ _ _ _ _ DC) as (tbl0 & ->).
  set (main := (d1 <- r #: tr') <- s #: ts').
  destruct (dclosure_exists W tbl0 Z (removeD k1 D) main (S k2)) as (l1 & DC1).
  assert (LR : typ_lts tr (ainput s l v) tr') by (eapply sd_typ_lts_typ_lts; eauto).
  assert (LS : typ_lts ts (aoutput r l v) ts') by (eapply sd_typ_lts_typ_lts; eauto).
  assert (DL : delts W Z (NatMap.add k1 d1 tbl0) (Some (atau (Some (exc r l s)))) D d1 k1
                 (atau (Some (exc r l s))) (removeD k1 D) main
                 (Some (res_env d1 r s o1 t2))).
  { eapply se_comD with (p := r) (q := s) (tp := tr) (tq := ts) (hl := Some l) (dom := []).
    - exact MIN.
    - apply (hinted_pair tr ts s r l v tr' ts' d1 k1 tbl0 W []);
        eauto.
    - exact Er.
    - exact Es.
    - apply HZ; [eapply typ_lts_input_label | eapply typ_lts_output_label]; eauto.
    - eapply sd_com; eauto.
      + intros t1' t2' E1 E2; unfold res_env; rewrite E1; inversion E2; reflexivity.
      + intros t2' E1 E2; unfold res_env; rewrite E1; inversion E2; reflexivity.
      + intros E; discriminate. }
  assert (DC0 : dclosure W Z (NatMap.add k1 d1 tbl0) D d1 k1 (l1 ++ l2))
    by (eapply c_tra; eauto).
  destruct (CMP W (NatMap.add k1 d1 tbl0) Z (l1 ++ l2) HW FW HZ DC0) as [NN ALL].
  split.
  - intro I; apply NN, in_or_app; right; exact I.
  - intros d0 I; apply ALL, in_or_app; right; exact I.
Qed.

Definition dcomp_all (e : part_env) :=
  forall D k, In (e, k) D -> dcompliance e k D.

Lemma res_all e r s l v tr ts tr' ts' o1 t2 :
  wfE e ->
  dcomp_all e ->
  e r = Some tr ->
  e s = Some ts ->
  sd_typ_lts tr (ainput s l v) tr' o1 ->
  sd_typ_lts ts (aoutput r l v) ts' (Some t2) ->
  dcomp_all (res_env e r s o1 t2).
Proof.
  intros WF ALL Er Es SR SS D' k' _.
  pose proof (res_dcompliance e 0 k' ((e, 0) :: D') r s l v tr ts tr' ts' o1 t2
                WF (in_eq _ _) (ALL _ _ (in_eq _ _)) Er Es SR SS) as K.
  simpl in K. exact K.
Qed.

(** * Part 3c: the invariant *)

Definition comm_pair (e : part_env) r s l v :=
  exists tr ts tr' ts',
    e r = Some tr /\ e s = Some ts /\
      typ_lts tr (ainput s l v) tr' /\ typ_lts ts (aoutput r l v) ts'.

Definition pending (e : part_env) r s :=
  exists tr ts l' v' u,
    e r = Some tr /\ e s = Some ts /\
      typ_lts ts (aoutput r l' v') u /\
      ~ (exists u', typ_lts tr (ainput s l' v') u').

Definition pending_env (e : part_env) (dom : list participant) :=
  wfE e /\
    (forall x X T, e x <> Some (typ_mu X T)) /\
    (forall r s l v, comm_pair e r s l v -> pending e r s) /\
    dcomp_all e /\
    (exists x t, e x = Some t /\ t <> typ_end) /\
    (forall x, e x <> None -> In x dom).

Definition sz (e : part_env) x :=
  match e x with Some t => tsize t | None => 0 end.

Fixpoint msr (e : part_env) (dom : list participant) : nat :=
  match dom with
  | [] => 0
  | x :: xs => sz e x + msr e xs
  end.

Lemma msr_mono e e' dom :
  (forall x, sz e' x <= sz e x) -> msr e' dom <= msr e dom.
Proof. intros H; induction dom; simpl; [lia | specialize (H a); lia]. Qed.

Lemma msr_strict e e' dom r :
  (forall x, sz e' x <= sz e x) -> In r dom -> sz e' r < sz e r ->
  msr e' dom < msr e dom.
Proof.
  intros H IN LT; induction dom as [| a dom IH]; simpl in *; [contradiction |].
  destruct IN as [-> | IN].
  - pose proof (msr_mono e e' dom H); lia.
  - specialize (IH IN). specialize (H a). lia.
Qed.

Lemma res_env_val e r s o1 t2 x :
  res_env e r s o1 t2 x =
    if pbeq s x then Some t2
    else if pbeq r x then Some (match o1 with Some t1 => t1 | None => typ_end end)
    else e x.
Proof. reflexivity. Qed.

Lemma pbeq_false x y : x <> y -> pbeq x y = false.
Proof.
  intro NE; destruct (pbeq x y) eqn:E; auto.
  apply participant_beq_eq in E; contradiction.
Qed.

Lemma no_end_input q l v u : ~ typ_lts typ_end (ainput q l v) u.
Proof. intro H; inversion H. Qed.

Lemma no_end_output q l v u : ~ typ_lts typ_end (aoutput q l v) u.
Proof. intro H; inversion H. Qed.

Lemma pending_step e dom r s l v :
  pending_env e dom -> comm_pair e r s l v ->
  exists e', pending_env e' dom /\ msr e' dom < msr e dom.
Proof.
  intros (WF & NM & PEND & DC & NE & DOM) C.
  pose proof C as (tr & ts & tr' & ts' & Er & Es & LR & LS).
  destruct (PEND _ _ _ _ C) as (tr0 & ts0 & l' & v' & u & Er0 & Es0 & LU & NA).
  rewrite Er in Er0; inversion Er0; subst tr0.
  rewrite Es in Es0; inversion Es0; subst ts0.
  assert (WR : wf tr) by (eapply WF; eauto).
  assert (WS : wf ts) by (eapply WF; eauto).
  assert (BR : tbranch_r tr) by (eapply input_tbranch_r; eauto).
  assert (SL : tselect_r ts) by (eapply output_tselect_r; eauto).
  assert (RS : r <> s).
  { intro E; subst s. rewrite Er in Es; inversion Es; subst ts.
    eapply tbranch_r_no_output; eauto. }

  assert (NL : l' <> l).
  { intro E; subst l'.
    destruct (typ_lts_output_same_sort _ _ _ _ _ _ _ WS LS LU) as (S0 & SV & SV').
    destruct (typ_lts_input_sort _ _ _ _ _ LR) as (Sr & SVr & K).
    rewrite (value_sort_unique _ _ _ SVr SV) in K.
    apply NA; eauto. }
  destruct (typ_lts_sd_typ_lts _ _ _ LR) as (o1 & SR).
  destruct (typ_lts_sd_typ_lts _ _ _ LS) as (o2 & SS).
  destruct (rem_keeps_out _ _ _ _ _ _ SS _ _ _ LU NL) as (t2 & -> & LU2).
  set (rr := match o1 with Some t1 => t1 | None => typ_end end).
  assert (Vs : res_env e r s o1 t2 s = Some t2)
    by (rewrite res_env_val, participant_beq_eq_true; reflexivity).
  assert (Vr : res_env e r s o1 t2 r = Some rr)
    by (rewrite res_env_val, (pbeq_false _ _ (not_eq_sym RS)), participant_beq_eq_true; reflexivity).
  assert (Vx : forall x, x <> r -> x <> s -> res_env e r s o1 t2 x = e x).
  { intros x N1 N2. rewrite res_env_val, (pbeq_false _ _ (not_eq_sym N2)),
      (pbeq_false _ _ (not_eq_sym N1)); reflexivity. }
  assert (WT2 : wf t2) by (eapply wf_rem_out; eauto).
  assert (ST2 : tselect_r t2) by (eapply rem_tselect_r; eauto).
  assert (WRR : wf rr).
  { unfold rr; destruct o1 as [t1 |];
      [exact (wf_rem_in _ _ _ _ _ _ WR SR t1 eq_refl) | exact I]. }

  assert (SUBr : forall q l0 w u0,
             (typ_lts rr (ainput q l0 w) u0 -> typ_lts tr (ainput q l0 w) u0) /\
               (typ_lts rr (aoutput q l0 w) u0 -> typ_lts tr (aoutput q l0 w) u0)).
  { intros q l0 w u0. unfold rr; destruct o1 as [t1 |].
    - eapply rem_sub; eauto.
    - split; intro K; inversion K. }
  assert (SUBs : forall q l0 w u0,
             (typ_lts t2 (ainput q l0 w) u0 -> typ_lts ts (ainput q l0 w) u0) /\
               (typ_lts t2 (aoutput q l0 w) u0 -> typ_lts ts (aoutput q l0 w) u0)).
  { intros q l0 w u0. eapply rem_sub; eauto. }
  exists (res_env e r s o1 t2). split.
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    +
      intros x t E.
      destruct (classic (x = s)) as [-> | N2]; [rewrite Vs in E; inversion E; subst; exact WT2 |].
      destruct (classic (x = r)) as [-> | N1]; [rewrite Vr in E; inversion E; subst; exact WRR |].
      rewrite (Vx x N1 N2) in E. eapply WF; eauto.
    +
      intros x X T E.
      destruct (classic (x = s)) as [-> | N2];
        [rewrite Vs in E; inversion E; subst; exact ST2 |].
      destruct (classic (x = r)) as [-> | N1].
      * rewrite Vr in E; inversion E; subst. unfold rr in *.
        destruct o1 as [t1 |]; [| discriminate].
        assert (BT : tbranch_r t1) by (eapply rem_tbranch_r; eauto).
        rewrite H0 in BT; exact BT.
      * rewrite (Vx x N1 N2) in E. eapply NM; eauto.
    +
      intros x y l0 v0 (tx & ty & tx' & ty' & Ex & Ey & Lx & Ly).
      destruct (classic (x = s)) as [-> | Nxs].
      { rewrite Vs in Ex; inversion Ex; subst.
        exfalso; eapply tselect_r_no_input; [exact SL | apply (proj1 (SUBs _ _ _ _)); eauto]. }
      destruct (classic (y = r)) as [-> | Nyr].
      { rewrite Vr in Ey; inversion Ey; subst.
        exfalso; eapply tbranch_r_no_output; [exact BR | apply (proj2 (SUBr _ _ _ _)); eauto]. }
      destruct (classic (x = r)) as [-> | Nxr].
      * rewrite Vr in Ex; inversion Ex; subst.
        assert (y = s).
        { symmetry; eapply input_party_unique; [exact WR | exact LR |].
          apply (proj1 (SUBr _ _ _ _)); eauto. }
        subst y.
        exists rr, t2, l', v', u. repeat split; auto.
        intros (u' & K). apply NA. exists u'. apply (proj1 (SUBr _ _ _ _)); exact K.
      * destruct (classic (y = s)) as [-> | Nys].
        { rewrite Vs in Ey; inversion Ey; subst.
          exfalso; apply Nxr. eapply output_party_unique; [exact WS | | exact LS].
          apply (proj2 (SUBs _ _ _ _)); eauto. }
        rewrite (Vx x Nxr Nxs) in Ex. rewrite (Vx y Nyr (fun E => Nys E)) in Ey.
        destruct (PEND x y l0 v0 ltac:(do 4 eexists; eauto))
          as (ax & ay & l1 & v1 & u1 & Ax & Ay & LA & NAA).
        exists ax, ay, l1, v1, u1. repeat split; auto.
        -- rewrite (Vx x Nxr Nxs); exact Ax.
        -- rewrite (Vx y Nyr Nys); exact Ay.
    +
      exact (res_all e r s l v tr ts tr' ts' o1 t2 WF DC Er Es SR SS).
    +
      exists s, t2; split; [exact Vs |].
      intro E; subst; simpl in ST2; exact ST2.
    +
      intros x NN.
      destruct (classic (x = s)) as [-> | N2]; [apply DOM; rewrite Es; discriminate |].
      destruct (classic (x = r)) as [-> | N1]; [apply DOM; rewrite Er; discriminate |].
      rewrite (Vx x N1 N2) in NN; auto.
  - apply (msr_strict e _ dom s).
    + intros x. unfold sz.
      destruct (classic (x = s)) as [-> | N2].
      { rewrite Vs, Es. pose proof (rem_size _ _ _ _ SS t2 eq_refl); lia. }
      destruct (classic (x = r)) as [-> | N1].
      { rewrite Vr, Er. unfold rr; destruct o1 as [t1 |].
        - pose proof (rem_size _ _ _ _ SR t1 eq_refl); lia.
        - pose proof (tsize_pos tr); simpl; lia. }
      rewrite (Vx x N1 N2); lia.
    + apply DOM; rewrite Es; discriminate.
    + unfold sz; rewrite Vs, Es. exact (rem_size _ _ _ _ SS t2 eq_refl).
Qed.

Lemma pending_final e dom :
  pending_env e dom -> (forall r s l v, ~ comm_pair e r s l v) -> False.
Proof.
  intros (WF & NM & PEND & DC & (x0 & t0 & E0 & NE0) & DOM) NC.
  assert (CMP : dcompliance e 0 [(e, 0)]) by (apply DC; left; reflexivity).
  assert (MIN : ~ notMinimal e) by (eapply dcompliance_minimal; eauto).
  assert (NOD : forall W Z tbl ha D k a D1 d1 d2, ~ delts W Z tbl ha D e k a D1 d1 d2).
  { intros W Z tbl ha D k a D1 d1 d2 H; inversion H; subst;
      match goal with S: sd_elts _ _ _ _ _ _ _ |- _ => inversion S; subst end.
    - match goal with K: sd_typ_lts _ (aunfold _) _ _ |- _ => inversion K; subst end.
      eapply NM; eauto.
    - match goal with
      | K1: e ?p = Some ?a, K2: e ?q = Some ?b,
        L1: sd_typ_lts ?a (ainput ?q ?l ?v) ?a' _,
        L2: sd_typ_lts ?b (aoutput ?p ?l ?v) ?b' _ |- _ =>
          apply (NC p q l v); exists a, b, a', b';
          split; [exact K1 | split; [exact K2 |
            split; eapply sd_typ_lts_typ_lts; eassumption]]
      end. }
  assert (DCL : dclosure W_canonical Z_canonical
                  (NatMap.add 0 e (NatMap.empty part_env)) [(e, 0)] e 0 [Some e]).
  { apply c_refl; [exact MIN | intros; apply NOD]. }
  destruct hinted_canonical as [HW FW].
  unfold dcompliance in CMP.
  destruct (CMP _ _ _ _ HW FW hintedL_canonical DCL) as [_ ALL].
  destruct (ALL e (or_introl eq_refl)) as [_ [(a & e1 & EL) | ALLEND]].
  - inversion EL; subst.
    + match goal with K: typ_lts _ (aunfold _) _ |- _ => inversion K; subst end.
      eapply NM; eauto.
    + match goal with
      | K1: e ?p = Some ?a, K2: e ?q = Some ?b,
        L1: typ_lts ?a (ainput ?q ?l ?v) ?a',
        L2: typ_lts ?b (aoutput ?p ?l ?v) ?b' |- _ =>
          apply (NC p q l v); exists a, b, a', b';
          split; [exact K1 | split; [exact K2 | split; assumption]]
      end.
  - apply NE0. eapply ALLEND; eauto.
Qed.

Lemma pending_false dom : forall n e, msr e dom = n -> pending_env e dom -> False.
Proof.
  intro n; induction n as [n IH] using lt_wf_ind; intros e En I.
  destruct (classic (exists r s l v, comm_pair e r s l v)) as [(r & s & l & v & C) | NC].
  - destruct (pending_step e dom r s l v I C) as (e' & I' & LT).
    eapply (IH (msr e' dom)); [lia | reflexivity | exact I'].
  - eapply pending_final; [exact I |].
    intros r s l v C; apply NC; eauto.
Qed.

Corollary no_pending_env e dom : ~ pending_env e dom.
Proof. intro I; eapply pending_false; [reflexivity | exact I]. Qed.

(** * Part 3d: processes of stuck sessions *)

Lemma threads_leaf_inv G H M d p T :
  types_threads G H M d ->
  d p = Some T ->
  exists P, In (p, P) (leaves M) /\ wf T /\ types G H P T.
Proof.
  induction 1; simpl; intros E.
  - unfold singleton, extend, empty_ptenv in E.
    destruct (pbeq p0 p) eqn:B; [| discriminate].
    apply participant_beq_eq in B; subst. inversion E; subst.
    exists P; repeat split; auto.
  - unfold cat in E. destruct (d1 p) as [t |] eqn:E1.
    + inversion E; subst.
      destruct (IHtypes_threads1 eq_refl) as (P & IN & W & TP).
      exists P; repeat split; auto using in_or_app.
    + destruct (IHtypes_threads2 E) as (P & IN & W & TP).
      exists P; repeat split; auto using in_or_app.
Qed.

Lemma threads_dom G H M d p :
  types_threads G H M d -> d p <> None -> In p (map fst (leaves M)).
Proof.
  intros TT NN. destruct (d p) as [T |] eqn:E; [| contradiction].
  destruct (threads_leaf_inv _ _ _ _ _ _ TT E) as (P & IN & _).
  apply in_map_iff; exists (p, P); auto.
Qed.

Lemma passive_not_mu G H P T : types G H P T -> passive P -> forall X U, T <> typ_mu X U.
Proof. intros TP PA X U E; subst; inversion TP; subst; simpl in PA; tauto. Qed.

Lemma passive_end G H P : types G H P typ_end -> passive P -> P = proc_zero.
Proof. intros TP PA; inversion TP; subst; simpl in PA; tauto. Qed.

Lemma out_not_branch G H r l e s0 P t :
  types G H (proc_output r l e s0 P) t -> ~ tbranch_r t.
Proof.
  intro TP; remember (proc_output r l e s0 P) as Q; induction TP; inversion HeqQ; subst;
    simpl; try tauto.
Qed.

Lemma lab_in G H P T q l v u :
  types G H P T -> wf T -> typ_lts T (ainput q l v) u -> In l (labelsP P).
Proof.
  intros TP; revert q l v u; induction TP; intros q0 l0 v0 u0 W L;
    inversion L; subst;
    try (pose proof (wf_sum _ _ W) as [W1 W2]).
  all: try (exfalso; eapply out_not_branch; [eassumption |];
            pose proof (input_tbranch_r _ _ _ _ _ W L) as K; simpl in K; tauto).
  all: try (match goal with
            | IH: forall q l v u, wf ?t -> typ_lts ?t _ _ -> _, K: typ_lts ?t (ainput _ _ _) _ |- _ =>
                pose proof (IH _ _ _ _ ltac:(assumption) K)
            end).
  all: simpl in *; try tauto; eauto using in_or_app.
Qed.

Lemma cond_summand_false G H P e B1 B2 T q l v u :
  wf_proc (proc_sum P (proc_conditional e B1 B2)) ->
  types G H (proc_conditional e B1 B2) T ->
  wf T ->
  typ_lts T (ainput q l v) u ->
  False.
Proof.
  intros W TP WT L. inversion W; subst.
  match goal with U: uniformP _ _ |- _ => destruct U as (_ & _ & ND) end.
  simpl in ND. apply NoDup_app_remove_l in ND.
  inversion TP; subst.
  eapply NoDup_app; [exact ND | eapply lab_in; eauto | eapply lab_in; eauto].
Qed.

Lemma input_complete h P T p q l v u :
  passive P ->
  wf_proc P ->
  types empty_env h P T ->
  wf T ->
  typ_lts T (ainput q l v) u ->
  exists P', lts (single_session (p, P)) (ainput q l v) (single_session (p, P')).
Proof.
  revert T u; induction P; intros T u PA W TP WT L; simpl in PA; try tauto.
  -
    inversion TP; subst; inversion L; subst.
    eexists; apply r_input; assumption.
  -
    inversion TP; subst; inversion L; subst; exfalso;
      match goal with
      | K: types _ _ (proc_output _ _ _ _ _) ?ta, L': typ_lts (typ_sum _ _) (ainput _ _ _) _ |- _ =>
          apply (out_not_branch _ _ _ _ _ _ _ _ K);
          pose proof (input_tbranch_r _ _ _ _ _ WT L') as KK; simpl in KK; tauto
      end.
  -
    inversion W; subst.
    inversion TP; subst.
    +
      pose proof (wf_sum _ _ WT) as [W1 W2].
      inversion L; subst.
      * destruct (IHP1 _ _ I ltac:(assumption) ltac:(eassumption) W1 ltac:(eassumption))
          as (P' & LP).
        exists P'; apply r_sum_l; exact LP.
      * destruct P2.
        -- destruct (IHP2 _ _ I ltac:(assumption) ltac:(eassumption) W2 ltac:(eassumption))
             as (P' & LP).
           exists P'; apply r_sum_r; exact LP.
        -- destruct (IHP2 _ _ I ltac:(assumption) ltac:(eassumption) W2 ltac:(eassumption))
             as (P' & LP).
           exists P'; apply r_sum_r; exact LP.
        -- destruct (IHP2 _ _ I ltac:(assumption) ltac:(eassumption) W2 ltac:(eassumption))
             as (P' & LP).
           exists P'; apply r_sum_r; exact LP.
        -- exfalso; eapply cond_summand_false; eauto.
        -- match goal with K: types _ _ (proc_var _) _ |- _ => inversion K; subst end.
           match goal with K: typ_lts (typ_mu _ _) _ _ |- _ => inversion K end.
        -- match goal with K: types _ _ proc_zero _ |- _ => inversion K; subst end.
           match goal with K: typ_lts typ_end _ _ |- _ => inversion K end.
        -- match goal with K: types _ _ (proc_mu _ _) _ |- _ => inversion K; subst end.
           match goal with K: typ_lts (typ_mu _ _) _ _ |- _ => inversion K end.
    +
      exfalso;
      match goal with
      | K: types _ _ (proc_output _ _ _ _ _) ?ta, L': typ_lts (typ_sum _ _) (ainput _ _ _) _ |- _ =>
          apply (out_not_branch _ _ _ _ _ _ _ _ K);
          pose proof (input_tbranch_r _ _ _ _ _ WT L') as KK; simpl in KK; tauto
      end.
  -
    inversion TP; subst; inversion L.
Qed.

Lemma out_expr_typed G H q l e s0 P t :
  types G H (proc_output q l e s0 P) t -> stypes G e s0.
Proof.
  intro TP; remember (proc_output q l e s0 P) as Q; induction TP; inversion HeqQ; subst; auto.
Qed.

Lemma in_not_select G H q l x s0 P t :
  types G H (proc_input q l x s0 P) t -> ~ tselect_r t.
Proof.
  intro TP; remember (proc_input q l x s0 P) as Q; induction TP; inversion HeqQ; subst;
    simpl; tauto.
Qed.

Lemma output_exists h P T p r l v u :
  passive P ->
  types empty_env h P T ->
  wf T ->
  typ_lts T (aoutput r l v) u ->
  exists l' v' P',
    lts (single_session (p, P)) (aoutput r l' v') (single_session (p, P')).
Proof.
  intros PA TP WT L.
  assert (OUT : forall q l0 e s0 P0,
             types empty_env h (proc_output q l0 e s0 P0) T ->
             exists v0, lts (single_session (p, proc_output q l0 e s0 P0))
                          (aoutput q l0 v0) (single_session (p, P0)) /\ q = r).
  { intros q l0 e s0 P0 TQ.
    destruct (eval_total _ _ (out_expr_typed _ _ _ _ _ _ _ _ TQ)) as (v0 & EV & _).
    exists v0. assert (LQ := r_output p q l0 e v0 s0 P0 EV). split; [exact LQ |].
    destruct (lts_output_typ _ _ _ _ _ _ _ _ _ LQ TQ) as (U & LU).
    eapply output_party_unique; eauto. }
  destruct P; simpl in PA; try tauto.
  -
    inversion TP; subst; inversion L.
  -
    destruct (OUT _ _ _ _ _ TP) as (v0 & LQ & ->). eauto.
  -
    inversion TP; subst.
    +
      exfalso. pose proof (output_tselect_r _ _ _ _ _ WT L) as K; simpl in K.
      match goal with K1: types _ _ (proc_input _ _ _ _ _) _ |- _ =>
        apply (in_not_select _ _ _ _ _ _ _ _ K1) end; tauto.
    +
      match goal with K1: types _ _ (proc_output ?q ?l0 ?e ?s0 ?P0) ?t1 |- _ =>
        destruct (eval_total _ _ (out_expr_typed _ _ _ _ _ _ _ _ K1)) as (v0 & EV & _);
        pose proof (r_output p q l0 e v0 s0 P0 EV) as LQ;
        destruct (lts_output_typ _ _ _ _ _ _ _ _ _ LQ K1) as (U & LU);
        assert (QR : q = r)
          by (eapply output_party_unique; [exact WT | apply e_select_l; exact LU | exact L]);
        subst q; do 3 eexists; apply r_sum_l; exact LQ
      end.
  -
    inversion TP; subst; inversion L.
Qed.

Lemma wf_session_leaf M p P : wf_session M -> In (p, P) (leaves M) -> wf_proc P.
Proof.
  induction M as [[q Q] | A IHA B IHB]; simpl; intros W IN.
  - destruct IN as [E | []]; inversion E; subst; exact W.
  - destruct W as [WA WB]. apply in_app_or in IN as [IN | IN]; eauto.
Qed.

(** * Deadlock freedom *)

Theorem deadlock_freedom :
   forall M d,
    types_session empty_env empty_penv M d ->
    wf_session M ->
    2 < length (leaves M) ->
    (forall a M', elts_action a -> ~ lts M a M') ->
    consumed M.
Proof.
  intros M d TS WFS LEN STUCK p P IN.
  assert (PAS := stuck_passive M d TS ltac:(lia) STUCK).
  destruct (classic (P = proc_zero)) as [Z | NZ]; [exact Z | exfalso].
  destruct (length_leaves_parallel M ltac:(lia)) as (A & B & ->).
  destruct (ts_parallel_inv _ _ _ _ _ TS) as (TT & ld & PA & (CPL & ADM) & CMP).
  destruct (threads_leaf _ _ _ _ _ _ TT IN) as (T0 & W0 & TP0 & E0).
  assert (NE0 : T0 <> typ_end)
    by (intro; subst; apply NZ; eapply passive_end; eauto).
  destruct (CPL p ltac:(rewrite E0; discriminate)) as (d' & IND & NN).
  assert (SUB : sub_env d' d) by (apply (proj1 PA); exact IND).
  apply (no_pending_env d' (map fst (leaves (parallel_session A B)))).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  -
    exact (ADM d' IND).
  -
    intros x X U E.
    assert (Ed : d x = Some (typ_mu X U)) by (rewrite <- E; apply SUB; rewrite E; discriminate).
    destruct (threads_leaf_inv _ _ _ _ _ _ TT Ed) as (Px & INx & Wx & TPx).
    exact (passive_not_mu _ _ _ _ TPx (PAS _ _ INx) X U eq_refl).
  -
    intros r s l v (tr & ts & tr' & ts' & Er & Es & LR & LS).
    assert (Dr : d r = Some tr) by (rewrite <- Er; apply SUB; rewrite Er; discriminate).
    assert (Ds : d s = Some ts) by (rewrite <- Es; apply SUB; rewrite Es; discriminate).
    destruct (threads_leaf_inv _ _ _ _ _ _ TT Dr) as (Pr & INr & Wr & TPr).
    destruct (threads_leaf_inv _ _ _ _ _ _ TT Ds) as (Ps & INs & Ws & TPs).
    destruct (output_exists _ _ _ s _ _ _ _ (PAS _ _ INs) TPs Ws LS)
      as (l' & v' & Ps' & LPs).
    destruct (lts_output_typ _ _ _ _ _ _ _ _ _ LPs TPs) as (u & LU).
    exists tr, ts, l', v', u. split; [exact Er | split; [exact Es | split; [exact LU |]]].
    intros (u' & LA).
    destruct (input_complete _ _ _ r _ _ _ _ (PAS _ _ INr) (wf_session_leaf _ _ _ WFS INr)
                TPr Wr LA) as (Pr' & LPr).
    assert (RS : r <> s).
    { intro E; subst s. rewrite Er in Es; inversion Es; subst ts.
      eapply tbranch_r_no_output; [eapply input_tbranch_r; eauto | exact LS]. }
    destruct (pull_pair _ (r, Pr) (s, Ps) INr INs ltac:(intro K; inversion K; contradiction)
                ltac:(lia)) as (S0 & EQ).
    eapply STUCK with (a := atau (Some (exc r l' s))); [right; eauto |].
    eapply lts_equiv_star; [exact EQ |].
    exact (r_comm r s l' v' Pr Pr' Ps Ps' S0 LPr LPs).
  -
    intros D k INk. exact (proj2 (CMP d' D k IND) INk).
  -
    exists p, T0. split; [rewrite <- (SUB p NN); exact E0 | exact NE0].
  -
    intros x NNx. eapply threads_dom; [exact TT |]. rewrite (SUB x NNx); exact NNx.
Qed.

