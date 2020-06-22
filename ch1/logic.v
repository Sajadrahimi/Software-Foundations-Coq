Set Warnings "-notation-overridden,-parsing".
From LF Require Export tactics.



Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.



(** **** Exercise: 2 stars, standard (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros.
  apply and_intro.
  - (* n = 0 *)
    induction n.
    + reflexivity.
    + discriminate H.
  - (* m = 0 *)
    induction m.
    + reflexivity.
    + rewrite plus_comm in H. discriminate H.
Qed.
  

(** **** Exercise: 1 star, standard, optional (proj2)  *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [H1 H2].
  assumption.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.
Qed.


(** **** Exercise: 2 stars, standard (and_assoc) 

    (In the following proof of associativity, notice how the _nested_
    [intros] pattern breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP : P], [HQ : Q], and [HR : R].  Finish the proof from
    there.) *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  split; assumption.
  assumption.
Qed.


Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.


(** **** Exercise: 1 star, standard (mult_eq_0)  *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
    intros n m.
    destruct n as [|n'].
    - (* n = 0 *)
      intros.
      left.
      reflexivity.
    - (* n = S n' *)
      destruct m as [|m'].
        + (* m = 0 *)
          intros.
          right.
          reflexivity.
        + (* m = S m' *)
          intros contra.
          discriminate contra.
Qed.

(** **** Exercise: 1 star, standard (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  right. assumption.
  left. assumption.
Qed.



(** **** Exercise: 2 stars, standard, optional (not_implies_our_not) 

    Show that Coq's definition of negation implies the intuitive one
    mentioned above: *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros.
  contradiction.
Qed.


Theorem not_False :
  ~ False.
Proof.
  unfold not.
  intros H.
  destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G.
  apply G.
  apply H.
Qed.

(** **** Exercise: 2 stars, advanced (double_neg_inf) 

    Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P]. *)

(* By definition, the theorem is equivalent to:
      P -> ( P -> False ) -> False.

   Let P be a Prop, and hypothesize that ~P holdes, which by defnintion means
   P -> False holdes. Since we have P and (P -> False) in assumptions,
   by modus ponens we can deduce False.
   *)


(** **** Exercise: 2 stars, standard, recommended (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H HQ.
  unfold not.
  unfold not in HQ.
  intros HP.
  apply HQ.
  apply H.
  assumption.
Qed.

(** **** Exercise: 1 star, standard (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros.
  unfold not.
  intros [HP HPF].
  apply HPF.
  assumption.
Qed.


(** **** Exercise: 1 star, advanced (informal_not_PNP) 

    Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* 

  Let P be a Prop. By definition ~(P /\ ~P) is equivalent to
    ( P /\ ( P -> False ) ) -> False
  which means we have assuming P /\ ( P -> False ) we have P and ( P -> False ) in assumptions
  by modus ponens we can deduce False which is the goal here.
 *)


Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b.
  split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

(** **** Exercise: 1 star, standard, optional (iff_properties) 

    Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  split; intros; assumption.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R [HPQ HQP] [HQR HRQ].
  split.
  - intros.
    apply HPQ in H.
    apply HQR in H.
    assumption.
  - intros.
    apply HRQ in H.
    apply HQP in H.
    assumption.
Qed.

(** **** Exercise: 3 stars, standard (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
    intros. split.
    - intros [HP | [HQ HR]].
        + split.
            * left. apply HP.
            * left. apply HP.
        + split.
            * right. apply HQ.
            * right. apply HR.
    - intros [[HP | HQ] [HP1 | HR]].
        + left. apply HP.
        + left. apply HP.
        + left. apply HP1.
        + right. split.
            * apply HQ.
            * apply HR.
Qed.



From Coq Require Import Setoids.Setoid.


Lemma eq_mult_0 :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply eq_mult_0.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.



(** **** Exercise: 1 star, standard, recommended (dist_not_exists) 

    Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold."  (Hint: [destruct H as [x E]] works on
    existential assumptions!)  *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  intros [x Hx].
  apply Hx.
  apply H.
Qed.

(** **** Exercise: 2 stars, standard (dist_exists_or) 

    Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - (* -> *)
    intros [x [HPx | HQx]].
    + left. exists x. apply HPx.
    + right. exists x. apply HQx.
  - (* <- *)
    intros [ [x HPx] | [x HQx]].
    + exists x. left. apply HPx.
    + exists x. right. apply HQx.
Qed.



Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.


(** **** Exercise: 3 stars, standard (In_map_iff)  *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - (* -> *)
    induction l as [| h t].
    + (* l = [] *)
      intro.
      simpl in H.
      apply ex_falso_quodlibet.
      apply H.
    + (* l = h :: t *)
      intros [].
      * exists h.
        split.
        apply H.
        simpl.
        left. reflexivity.
      * apply IHt in H.
        destruct H as [HA [HF HIn]].
        exists HA.
        split.
        apply HF.
        simpl.
        right. apply HIn.
  - (* <- *)
    induction l as [| h t].
      + (* l = [] *)
        intros [].
        simpl in H.
        destruct H as [H0 H1].
        simpl.
        apply H1.

      + (* l = h :: t *)
        intros [].
        destruct H as [H0 [H1 | H2]].
        * rewrite <- H1 in H0.
          simpl.
          left. apply H0.
        * assert (H: f x = y /\ In x t). { split. apply H0. apply H2. }
          simpl.
          right.
          apply IHt. exists x. apply H.
Qed.


(** **** Exercise: 2 stars, standard (In_app_iff)  *)
Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - (* l = [] *)
    split.
    + (* -> *) simpl. intro. right. apply H.
    + (* <- *) simpl. intros []. 
      * apply ex_falso_quodlibet. apply H.
      * apply H.
  - (* l = h :: t *)
    split.
    + (* -> *)
      intros []. 
      * simpl. left. left. apply H.
      * simpl. apply or_assoc. right. apply IH. apply H.
    + (* <- *)
      intros [[H0 | H1] | H2].
      * simpl. left. apply H0.
      * simpl. right. apply IH. left. apply H1.
      * simpl. right. apply IH. right. apply H2.
Qed.

(** **** Exercise: 3 stars, standard, recommended (All) 

    Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x' :: l' => P x' /\ All P l'
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  split.
  - (* -> *)
    induction l as [| h t].
    + (* l = [] *)
      intros. simpl. apply I.
    + (* l = h :: t *)
      intros. simpl. split.
        * apply H. simpl. left. reflexivity.
        * apply IHt. intros. apply H. simpl. right. apply H0.
  - (* <- *)
    induction l as [| h t].
    + (* l = [] *)
      simpl.
      intros.
      apply ex_falso_quodlibet. apply H0.
    + (* l = h :: t *)
      intros.
      simpl in H0. simpl in H.
      destruct H as [PH APT].
      destruct H0 as [HX | IXT].
      * rewrite <- HX. apply PH.
      * apply IHt. apply APT. apply IXT.
Qed.

(** **** Exercise: 3 stars, standard (combine_odd_even) 

    Complete the definition of the [combine_odd_even] function below.
    It takes as arguments two properties of numbers, [Podd] and
    [Peven], and it should return a property [P] such that [P n] is
    equivalent to [Podd n] when [n] is odd and equivalent to [Peven n]
    otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
   fun n =>
    match oddb n with
      | true => Podd n
      | false => Peven n
    end.

(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n PO PE.
  destruct (oddb n) eqn:H.
  unfold combine_odd_even.
  - unfold combine_odd_even. rewrite H. apply PO. reflexivity.
  - unfold combine_odd_even. rewrite H. apply PE. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n H Ho.
  unfold combine_odd_even in H. rewrite Ho in H. apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
    intros Podd Peven n H He.
    unfold combine_odd_even in H. rewrite He in H. apply H.
Qed.


Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l eqn:HE.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.


Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.



(** **** Exercise: 4 stars, standard (tr_rev_correct) 

    One problem with the definition of the list-reversing function
    [rev] that we have is that it performs a call to [app] on each
    step; running [app] takes time asymptotically linear in the size
    of the list, which means that [rev] is asymptotically quadratic.
    We can improve this with the following definitions: *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** This version of [rev] is said to be _tail-recursive_, because the
    recursive call to the function is the last operation that needs to
    be performed (i.e., we don't have to execute [++] after the
    recursive call); a decent compiler will generate very efficient
    code in this case.

    Prove that the two definitions are indeed equivalent. *)

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  induction x.
  reflexivity.
  simpl.
  rewrite <- IHx.
  assert (H: forall T l1 l2, @rev_append T l1 l2 = @rev_append T l1 [] ++ l2).
  { intros T. induction l1 as [|h' t'].
      - reflexivity.
      - simpl. rewrite IHt'. intros. 
        rewrite (IHt' (h'::l2)).
        rewrite <- app_assoc. reflexivity. }
  apply H with (l2 := [x]).
Qed.



Lemma evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Check evenb_S.

(** **** Exercise: 3 stars, standard (evenb_double_conv)  *)
Lemma evenb_double_conv : forall n, exists k,
  n = if evenb n then double k else S (double k).
Proof.
  intros.
  induction n.
  - simpl.
    exists 0. reflexivity.
  - rewrite evenb_S. destruct IHn as [w H].
    destruct evenb.
    + simpl. exists w. rewrite H. reflexivity.
    + simpl. exists (S w). rewrite H. reflexivity.
Qed. 



(** **** Exercise: 2 stars, standard (logical_connectives) 

    The following lemmas relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)

Lemma andb_true_iff : forall b1 b2:bool,
  andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros.
  split.
  - (* -> *)
    intros. destruct b1.
    + destruct b2.
      * split; reflexivity.
      * discriminate H.
    + inversion H.
  - (* <- *)
    intros [].
    rewrite H. rewrite H0. reflexivity.
Qed. 

Lemma orb_true_iff : forall b1 b2,
  orb b1 b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros.
  split.
  - (* -> *)
    intros. destruct b1.
    + left. reflexivity.
    + destruct b2.
      * right. reflexivity.
      * discriminate H.
  - (* <- *)
    intros [H1 | H2].
      * rewrite H1. reflexivity.
      * rewrite H2.
        assert (H: forall b : bool, orb b true = true).
        { intros. destruct b; reflexivity. }
        apply H.
Qed. 

(** **** Exercise: 1 star, standard (eqb_neq) 

    The following theorem is an alternate "negative" formulation of
    [eqb_eq] that is more convenient in certain situations (we'll see
    examples in later chapters). *)

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros.
  split.
  - (* -> *)
    intros H F.
    rewrite F in H.
    rewrite eqb_refl in H.
    discriminate H.
  - (* <- *)
    intros H.
    destruct (eqb x y) eqn:E.
    + apply eqb_true in E.
      apply H in E. apply ex_falso_quodlibet. apply E.
    + reflexivity.
Qed.


(** **** Exercise: 3 stars, standard (eqb_list) 

    Given a boolean operator [eqb] for testing equality of elements of
    some type [A], we can define a function [eqb_list] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [eqb_list] function below.  To make sure that your
    definition is correct, prove the lemma [eqb_list_true_iff]. *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool := 
  match l1 with
  | [] => match l2 with
          | [] => true
          | _ => false
          end
  | h1 :: t1 => match l2 with
                | [] => false
                | h2 :: t2 => andb (eqb h1 h2) (eqb_list eqb t1 t2)
                end
  end.

Lemma eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H.
  induction l1 as [| h1 t1].
  - (* l = [] *)
    split.
    + (* -> *)
      intros.
      destruct l2.
        * reflexivity.
        * discriminate H0.
    + (* <- *)
      intros.
      destruct l2.
        * reflexivity.
        * discriminate H0.
  - (* l = h :: t *)
    induction l2 as [| h2 t2].
    + (* l2 = [] *)
      split.
      intros.
      * (* -> *)
        intros. discriminate H0.
      * (* <- *)
        intros. discriminate H0.
    + (* l2 = h2 :: t2 *)
      simpl.
      split.
      * (* -> *)
        intros H0.
        apply andb_true_iff in H0.
        destruct H0 as [H1 H2].
        apply H in H1.
        rewrite H1.
        apply IHt1 in H2.
        rewrite H2.
        reflexivity.
      * (* <- *)
        intros.
        inversion H0.
        apply andb_true_iff.
        split.
        apply H. reflexivity.
        rewrite <- H3.
        apply IHt1.
        reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, recommended (All_forallb) 

    Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Tactics]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

(** Prove the theorem below, which relates [forallb] to the [All]
    property defined above. *)

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test.
  induction l as [| h t].
  - (* l = [] *)
    split.
    + (* -> *)
      intros.
      reflexivity.
    + (* <- *)
      intros.
      reflexivity.
  - (* l = h :: t *)
    split.
    + (* -> *)
      intros.
      simpl.
      split.
      * simpl in H.
        apply andb_true_iff in H.
        destruct H as [H1 H2].
        apply H1.
      * apply IHt.
        simpl in H.
        apply andb_true_iff in H.
        destruct H as [H1 H2].
        apply H2.
    + (* <- *)
      intros.
      simpl.
      apply andb_true_iff.
      split.
        * apply H.
        * apply IHt. apply H.
Qed.

(** (Ungraded thought question) Are there any important properties of
    the function [forallb] which are not captured by this
    specification? *)

(* FILL IN HERE

    [] *)


Definition excluded_middle := forall P : Prop,
  P \/ ~ P.


(** **** Exercise: 3 stars, standard (excluded_middle_irrefutable) 

    Proving the consistency of Coq with the general excluded middle
    axiom requires complicated reasoning that cannot be carried out
    within Coq itself.  However, the following theorem implies that it
    is always safe to assume a decidability axiom (i.e., an instance
    of excluded middle) for any _particular_ Prop [P].  Why?  Because
    we cannot prove the negation of such an axiom.  If we could, we
    would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)] (since [P]
    implies [~ ~ P], by lemma [double_neg], which we proved above),
    which would be a  contradiction.  But since we can't, it is safe
    to add [P \/ ~P] as an axiom. *)


Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P.
  unfold not.
  intros.
  apply H.
  right. intros. apply H.
  left. apply H0.
Qed.

(** **** Exercise: 3 stars, advanced (not_exists_dist) 

    It is a theorem of classical logic that the following two
    assertions are equivalent:

    ~ (exists x, ~ P x)
    forall x, P x

    The [dist_not_exists] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle. *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  intros H X P.
  intros E x.
  assert (H1: P x \/ ~ P x). { apply H. }
  destruct H1 as [H2 | H3].
  - apply H2.
  - apply ex_falso_quodlibet.
    apply E. exists x. apply H3.
Qed.

(** **** Exercise: 5 stars, standard, optional (classical_axioms) 

    For those who like a challenge, here is an exercise taken from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following four statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.

    Prove that all five propositions (these four plus [excluded_middle])
    are equivalent.

    Hint: Rather than considering all pairs of statements pairwise,
    prove a single circular chain of implications that connects them
    all.
*)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).


Theorem EXM__de_morgan_not_and_not:
  excluded_middle <-> de_morgan_not_and_not.
Proof.
  unfold excluded_middle.
  unfold  de_morgan_not_and_not.
  split.
  - (* -> *)
    intros.
    unfold not in H0.
    destruct (H P).
      + (* P *) left. apply H1.
      + (* ~P *)
        destruct (H Q).
          * (* Q *) right. apply H2.
          * (* ~Q *) apply ex_falso_quodlibet. apply H0. split. apply H1. apply H2.
  - (* <- *)
    intros.
    apply H.
    unfold not.
    intros. apply H0. intro. apply H0 in H1. apply H1.
Qed.

Theorem EXM__implies_to_or:
  excluded_middle <-> implies_to_or.
Proof.
  unfold excluded_middle.
  unfold implies_to_or.
  split.
  - (* -> *)
    intros.
    destruct (H P).
      + right. apply H0 in H1. apply H1.
      + left. apply H1.
  - (* <- *)
    intros.
    apply or_commut.
    apply H.
    intros HP. apply HP.
Qed.

Theorem pierce__double_negation_elimination: 
  peirce <-> double_negation_elimination.
Proof.
  unfold peirce.
  unfold double_negation_elimination.
  split.
  - (* -> *)
    intros.
    unfold not in H0. apply H with (Q:=False).
    intros. apply H0 in H1. inversion H1.
  - (* <- *)
    intros.
    apply H.
    unfold not. intros.
    apply H1 in H0.
    + apply H0.
    + intro. apply H1 in H2. inversion H2.
Qed.

Theorem double_negation_elimination__EXM:
  double_negation_elimination <-> excluded_middle.
Proof.
  unfold excluded_middle.
  unfold double_negation_elimination.
  split.
  - (* -> *)
    intros. apply H.
    unfold not. intros.
    apply H0.
    right.
    intros.
    destruct H0. left. apply H1.
  - (* <- *)
    intros. unfold not in H0.
    destruct (H P).
      + apply H1.
      + unfold not in H1. apply H0 in H1. inversion H1.
Qed.

Theorem de_morgan_not_and_not__implies_to_or:
  de_morgan_not_and_not <-> implies_to_or.
Proof.
  unfold de_morgan_not_and_not.
  unfold implies_to_or.
  split.
  - (* -> *)
    intros. apply EXM__de_morgan_not_and_not.
      + (* Prove excluded_middle *)
        unfold excluded_middle.
        intros.
        apply H.
        unfold not.
        intros [H1 H2].
        apply H2. apply H1.
      + (* Prove ~ (~ ~ P /\ ~ Q) *)
        unfold not.
        intros [H1 H2].
        apply H1.
        intro.
        apply H2.
        apply H0.
        apply H3.
  - (* <- *)
    intros.
    apply EXM__de_morgan_not_and_not. unfold excluded_middle. intros.
    + apply or_comm. apply H. intro. apply H1.
    + apply H0.
Qed.

























