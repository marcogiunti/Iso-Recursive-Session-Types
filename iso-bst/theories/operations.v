Require Import
          Bool List PeanoNat Classical.

Require Import CpdtTactics LibTactics.  


Lemma ex_falso: forall T:Type, False -> T.
  inversion 1.
Qed.

Lemma NNP_iff_P (P : Prop) : ~~ P <-> P.
Proof. split; [apply NNPP | intuition]. Qed.

Section PairOperations.

  Lemma projections_injective : forall A (p1 p2 : A * A),
    p1  = p2 ->
    (fst p1 = fst p2 /\ snd p1 = snd p2).
  Proof.
    intros. split.  simpl. destruct p1. destruct p2.
    injection H. intros. tauto. 
    inversion H. tauto.
  Qed.

End PairOperations. 

Section ListOperations.

  Lemma rec_In : forall A (x:A) (l : list A),
    (fun (a0 : A) (l0 : list A)  =>
       match l0 with
       | nil => False
       | b :: m => b = a0 \/ In a0 m
       end) x l = 
    ((fix
        In (a0 : A) (l0 : list A) {struct l0} : 
        Prop :=
        match l0 with
        | nil => False
        | b :: m => b = a0 \/ In a0 m
        end) x l). 
  Proof. 
    intros.
    destruct l; simpl; auto.
  Qed.
  

  Lemma fold_In : forall A a (l : list A),
      In a l =
      ((fix
          In (a : A) (l : list A) {struct l} :
          Prop :=
          match l with
          | nil => False
          | b :: m => b = a \/ In a m
          end) a l).
  Proof.
    intros.
    destruct l; simpl; auto. 
  Qed.
  
  Lemma incl_distr : forall A (l1 l2 m : list A),
      incl (l1++l2) m -> incl l1 m /\ incl l2 m.
  Proof.
    intros.
    split.

    unfold incl.
    intros. 
    unfold incl in H.
    specialize H with (a := a).
    rewrite in_app_iff in H.
    intuition.

    unfold incl.
    intros. 
    unfold incl in H.
    specialize H with (a := a).
    rewrite in_app_iff in H.
    intuition.

  Qed.

  
  
  
  Fixpoint disjoint {A} (l1 l2 : list A) : Prop :=
    match l1 with
    | nil => True
    | x::t1 => ((In x l2) -> False) /\ disjoint t1 l2
    end.

  Lemma rec_disjoint : forall l m,
      (fun  {A} (l0 l2: list A)  =>
         match l0 with
         | nil => True
         | x :: t1 =>
           (In x l2 -> False) /\ disjoint t1 l2
         end) l m =
      ((fix disjoint {A} (l0 l2 : list A) {struct l0} :
          Prop :=
          match l0 with
          | nil => True
          | x :: t1 =>
            (In x l2 -> False) /\ disjoint t1 l2
          end) l  m).
  Proof.
    intros.
    destruct m; simpl; auto. 
  Qed.

  Lemma disjoint_cons_l : forall A a (l m : list A),
      disjoint l m /\ ~ In a m -> disjoint (a::l) m.
  Proof.
    intros.
    destruct H.
    induction l.
    unfold disjoint.
    auto.
    unfold disjoint.
    split.
    auto.
    split.
    assert (H1 := H).
    unfold disjoint in H.
    destruct H.
    auto.
    unfold disjoint in H.
    destruct H.
    auto.
  Qed. 

  Lemma disjoint_cons_r : forall A a (l m : list A),
      disjoint l m /\ ~ In a l -> disjoint l (a::m).
  Proof.
    intros.
    destruct H.
    induction l.
    unfold disjoint. 
    auto.
    unfold disjoint. 
    split.
    unfold disjoint in H.
    destruct H.
    apply not_in_cons.
    split.
    apply not_in_cons in H0.
    destruct H0.
    auto.
    auto.
    unfold disjoint in H.
    destruct H.
    apply not_in_cons in H0.
    destruct H0.
    intuition. 
  Qed. 

  Lemma disjoint_l_cons : forall A a (l m : list A),
      disjoint (a::l) m -> disjoint l m /\ ~ In a m.
  Proof.
    intros.
    split.
    unfold disjoint in H.
    destruct H. 
    tauto. 
    unfold disjoint in H. 
    destruct H; auto.
  Qed.

  Lemma disjoint_r_cons : forall A a (l m : list A),
      disjoint l (a :: m) -> disjoint l m /\ ~ In a l.
  Proof.
    intros.
    split.

    induction l. 
    unfold disjoint in H.
    destruct H.
    unfold disjoint; auto.   
    apply disjoint_l_cons in H. 
    destruct H.
    apply not_in_cons in H0.  
    intuition.   
    apply disjoint_cons_l.
    intuition.  

    induction l.
    auto.
    apply disjoint_l_cons in H.
    destruct H.
    intuition.
    destruct H1.
    rewrite H1 in H0. 
    intuition.
    intuition.
  Qed.

  Lemma disjoint_commute : forall A (l m : list A),
      disjoint l m <-> disjoint m l.
  Proof.
    intros. 
    induction l.
    unfold disjoint at 1.
    induction m.
    unfold disjoint; auto.
    intuition.
    assert (~In a nil) by auto.
    assert (disjoint m nil /\ ~ In a nil -> disjoint (a :: m) nil). 
    apply disjoint_cons_l. 
    intuition. 
    split.

    destruct IHl.  
    intros.
    assert (~ In a m). 
    unfold disjoint in H1.
    destruct H1; auto. 
    apply disjoint_l_cons in H1.
    destruct  H1.
    assert (disjoint m l); intuition.
    apply disjoint_cons_r.
    intuition.

    destruct IHl. 
    intros.
    assert (~ In a m).  
    unfold disjoint in H1. 
    apply disjoint_r_cons in H1.
    destruct  H1.
    assert (disjoint m l); intuition. 
    apply disjoint_r_cons in H1.
    destruct H1.
    intuition.
    apply disjoint_cons_l. 
    intuition.
  Qed.

  Lemma disjoint_app_l : forall A (l1 l2 m : list A),
      disjoint (l1 ++ l2) m -> disjoint l1 m.
  Proof.
    intros.
    induction l1.

    unfold disjoint; auto.
    apply disjoint_l_cons with (l := l1 ++ l2) in H.
    intuition. 
    apply disjoint_cons_l.
    intuition.
  Qed.

  Lemma disjoint_app_r : forall A (l1 l2 m : list A),
      disjoint (l1 ++ l2) m -> disjoint l2 m.
  Proof.
    intros.
    induction l1.

    unfold disjoint; auto.
    apply disjoint_l_cons with (l := l1 ++ l2) in H.
    intuition.  
  Qed.

  Inductive  disjoint_2 {A}: list A -> list A -> Prop :=
  | dis_nil : forall l : list A, disjoint_2 nil l 
  | dis_cons : forall (x:A) (l1 l2 : list A),
      (~ In x l2 /\ disjoint_2 l1 l2) -> disjoint_2 (x::l1) l2.

  Lemma disjoint_2_cons_l : forall A x (l1 l2 : list A),
      disjoint_2 (x::l1) l2 -> (~In x l2 /\ disjoint_2 l1 l2).
  Proof.
    intros. inversion H. tauto.
  Qed.

  Lemma disjoint_2_l_cons : forall A x (l1 l2 : list A),
      (~In x l2 /\ disjoint_2 l1 l2) -> disjoint_2 (x::l1) l2.
  Proof.
    intros. inversion H. apply dis_cons in H. tauto. 
  Qed.
  
  Lemma disjoint_car : forall A  (l1 l2 : list A),
      disjoint_2 l1 l2 <-> disjoint l1 l2.
  Proof.
    intros. intuition.
    induction l1. unfold disjoint. intuition.
    apply disjoint_2_cons_l in H. intuition.
    apply disjoint_cons_l. intuition.
    induction l1. apply dis_nil. apply disjoint_2_l_cons. 
    apply disjoint_l_cons in H. intuition.    
  Qed.

  Lemma disjoint_2_comm : forall A (l1 l2 : list A),
      disjoint_2 l1 l2 <-> disjoint_2 l2 l1.
  Proof.
    intros. rewrite disjoint_car. rewrite disjoint_car. apply disjoint_commute.
  Qed.
  
  Lemma not_in_app_and : forall A (l m:list A) (a:A), 
      ~In a (l ++ m) -> ~In a l /\ ~In a m. 
  Proof.
    intros.
    split.
    induction l; intuition.
    induction m; intuition.
  Qed.

  Lemma no_dup_app_l: forall A (x y : A) (l1 l2 : list A),
      (NoDup (l1 ++ y :: l2) /\ In x l1) ->
      x <> y.
  Proof.
    intros. destruct H. (*remember (l1 ++ y :: l2) as m.*)
    apply NoDup_remove in H. destruct H. intuition.
    rewrite in_app_iff in H1. rewrite <- H2 in H1. intuition.
  Qed.

  Lemma no_dup_app_r: forall A (x y : A) (l1 l2 : list A),
      (NoDup (l1 ++ y :: l2) /\ In x l2) ->
      x <> y.
  Proof.
    intros. destruct H.
    apply NoDup_remove in H. destruct H. intuition.
    rewrite in_app_iff in H1. rewrite <- H2 in H1. intuition.
  Qed.

  Lemma no_dup_distr : forall A (l1 l2 : list A),
      NoDup (l1 ++ l2) -> NoDup l1 /\ NoDup l2.
  Proof.
    intros.
    split.
    induction l2.
    assert (l1 = l1 ++ nil).
    intuition.
    rewrite <- H0 in H.
    tauto. 
    apply NoDup_remove in H.
    intuition.

    induction l1.  
    assert (nil ++ l2 = l2).
    intuition.
    rewrite -> H0 in H.
    tauto. 
    apply NoDup_cons_iff in H.
    destruct H.
    intuition.

  Qed. 
  
  
  Lemma no_dup_disjoint : forall A (l1 l2 : list A),
      NoDup (l1 ++ l2) -> disjoint l1 l2.
  Proof.
    intros.
    induction l1.
    unfold disjoint.
    auto.
    apply NoDup_cons_iff with (l:= l1++l2) in H.
    destruct H.
    intuition.
    apply not_in_app_and in H.
    destruct H.
    apply disjoint_cons_l.
    auto.
  Qed.

  Lemma no_dup_iff : forall A (l1 l2 : list A),
      NoDup (l1 ++ l2) <-> NoDup l1 /\ NoDup l2 /\ disjoint l1 l2.
  Proof.
    intros. intuition. apply no_dup_distr in H. intuition.
    apply no_dup_distr in H. intuition. apply no_dup_disjoint in H. tauto.
    induction l1. intuition. assert (H10 := H0).
    apply NoDup_cons_iff with (a := a) (l := l1++l2).
    apply NoDup_remove_1 with (l:= nil) in H0 . apply disjoint_l_cons in H2.
    intuition. apply in_app_iff in H2. intuition.
    apply NoDup_remove with (l := nil) in H10. intuition. 
  Qed.

  Lemma not_disjoint: forall A l1 l2,
    ~disjoint l1 l2 ->
    exists x:A, In x l1 /\ In x l2.
Proof with eauto using in_eq.
  intros.
  rewrite <-disjoint_car in H.
  induction l1, l2.
  specialize @dis_nil with (l:= nil : list A) as ABS...
  contradiction.
  specialize @dis_nil with (l:= a:: l2) as ABS...
  contradiction.
  specialize @dis_nil with (l:= a:: l1) as ABS...
  rewrite disjoint_2_comm in ABS; contradiction.
  rewrite disjoint_car in H.
  assert (a = a0 \/ In a l2 \/ ~disjoint l1 (a0 :: l2)).
  - apply Peirce. intros. elim H.
    assert (~~disjoint l1 (a0 :: l2)). intuition.
    rewrite !NNP_iff_P in H1.
    eapply disjoint_cons_l.
    split. assumption.
    assert (a <> a0)...
    rewrite not_in_cons.
    assert (~In a l2)...
  - destruct H0 as [K1 | [K2 | K3]].
    subst a0...
    exists a...
    split...
    eapply in_cons in K2...
    rewrite <-disjoint_car in K3.
    apply IHl1 in K3.
    destruct K3 as [x [IN1 IN2]].
    exists x...
    split...
    eapply in_cons in IN1...
Qed.

 Lemma disjoint_remove A eq_dec (x : A) l1 l2 l3:
    disjoint (List.remove eq_dec x l1) (l2 ++l3) ->
    ~In x l2 ->
    disjoint l1 l2.
  Proof with eauto.
    introv DIS NIN.
    induction l1...
    case_eq (eq_dec x a); introv EQ; subst; simpl in *; rewrite EQ in *; intuition.
    eapply disjoint_l_cons in DIS; intuition.
    eapply IHl1...
    eapply disjoint_l_cons in DIS; intuition.
  Qed.

  Hint Resolve in_eq.

  Lemma disjoint_absurd {A}: forall x (l m : list A) P,
    disjoint l m  -> In x l -> In x m -> P.
Proof with eauto.
  intros. apply ex_falso.
  eapply in_split in H0 as (l1 &l2 &ABS1).
  eapply in_split in H1 as (m1 &m2 &ABS2).
  subst. 
  eapply disjoint_app_r,disjoint_l_cons in H as [_ ABS].
  assert ( In x (m1 ++ x :: m2)).
  eapply in_app_iff; right...
  contradiction.
Qed.



End  ListOperations.
