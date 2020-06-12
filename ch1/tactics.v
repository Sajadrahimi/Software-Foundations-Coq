From LF Require Export poly.
From LF Require Export lists.

(** **** Exercise: 2 stars, standard, optional (silly_ex) 

    Complete the following proof using only [intros] and [apply]. *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 4 = true ->
     oddb 3 = true.
Proof.
  intros.
  apply H0.
Qed.

(** To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal exactly -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)

Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5)  ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.
  

(** Here we cannot use [apply] directly, but we can use the [symmetry]
    tactic, which switches the left and right sides of an equality in
    the goal. *)

  symmetry.
  simpl. (** (This [simpl] is optional, since [apply] will perform
             simplification first, if needed.) *)
  apply H.  Qed.

(** **** Exercise: 3 stars, standard (apply_exercise1) 

    (_Hint_: You can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [Search] is
    your friend.) *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros.
  rewrite H.
  symmetry.
  apply rev_involutive.
Qed.

(** **** Exercise: 1 star, standard, optional (apply_rewrite) 

    Briefly explain the difference between the tactics [apply] and
    [rewrite].  What are the situations where both can usefully be
    applied? *)

(*
apply: Uses implications to transform goals and hypotheses.
rewrite: Replaces a term with an equivalent term if the equivalence of the terms has already been proven. 
*)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.
Qed.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(** **** Exercise: 3 stars, standard, optional (apply_with_exercise)  *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros.
  apply trans_eq with (m := m).
  apply H0.
  apply H.
Qed.

(** **** Exercise: 3 stars, standard (injection_ex3)  *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros.
  injection H as eq1 eq2.
  assert (H1 : y :: l = z :: l). { rewrite eq2. rewrite H0. reflexivity. }
  injection H1 as eq3.
  rewrite eq1.
  symmetry.
  assumption.
Qed.
  
  
(** **** Exercise: 1 star, standard (discriminate_ex3)  *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros.
  discriminate H.
Qed.



(** **** Exercise: 2 stars, standard (eqb_true)  *)
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n.
  induction n.
  - intros.
    destruct m.
      + reflexivity.
      + discriminate H.
  - intros.
    destruct m.
      + discriminate.
      + apply IHn in H. f_equal. assumption.
Qed.
  
(** **** Exercise: 2 stars, advanced (eqb_true_informal) 

    Give a careful informal proof of [eqb_true], being as explicit
    as possible about quantifiers. *)

(* FILL IN HERE *)


(** **** Exercise: 3 stars, standard, recommended (plus_n_n_injective) 

    In addition to being careful about how you use [intros], practice
    using "in" variants in this proof.  (Hint: use [plus_n_Sm].) *)
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - intros.
    destruct m.
      + reflexivity.
      + discriminate H.
  - intros.
    destruct m.
      + discriminate H.
      + simpl in H.
        rewrite <- plus_n_Sm in H.
        injection H as eq1.
        symmetry in eq1.
        rewrite <- plus_n_Sm in eq1.
        injection eq1 as eq2.
        symmetry in eq2.
        apply IHn' in eq2.
        f_equal.
        assumption.
Qed.


Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.

(** **** Exercise: 3 stars, standard, recommended (gen_dep_practice) 

    Prove this by induction on [l]. *)

Theorem nth_error_after_last:
  forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros.
  generalize dependent n.
  induction l.
  - reflexivity.
  - intros.
    destruct n.
      + discriminate H.
      + simpl in H.
        injection H as eq1.
        apply IHl in eq1.
        simpl.
        assumption.
Qed.


(** **** Exercise: 3 stars, standard, optional (combine_split) 

    Here is an implementation of the [split] function mentioned in
    chapter [Poly]: *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

(** Prove that [split] and [combine] are inverses in the following
    sense: *)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.

  intros X Y l.
  induction l as [| x l'].
  - intros l1 l2.
    simpl.
    intro H.
    injection H as eq1 eq2.
    rewrite <- eq1, <- eq2.
    reflexivity.
  - destruct x as [x0 x1].
    simpl.
    destruct (split l').
    intros l1 l2 H.
    injection H as eq1 eq2.
    rewrite <- eq1, <- eq2.
    simpl.
    assert ( Hc : combine x y = l'). { apply IHl'. reflexivity. }
    rewrite Hc.
    reflexivity.
Qed.


(** **** Exercise: 2 stars, standard (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros.
  destruct (f b) eqn:eqfb.
  - destruct b.
    + rewrite eqfb. apply eqfb.
    + destruct (f true) eqn:ftrue.
      * apply ftrue.
      * apply eqfb.
  - destruct b.
    + destruct (f false) eqn:ffalse.
      * apply eqfb.
      * apply ffalse.
    + rewrite eqfb. apply eqfb.
Qed.


(** **** Exercise: 3 stars, standard (eqb_sym)  *)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n.
  induction n.
  - destruct m.
    reflexivity.
    reflexivity.
  - destruct m.
    reflexivity.
    simpl.
    apply IHn.
Qed.

(** **** Exercise: 3 stars, advanced, optional (eqb_sym_informal) 

    Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any [nat]s [n] [m], [(n =? m) = (m =? n)].

   Proof: *)
   (* FILL IN HERE

    [] *)
Lemma eqb_refl:
  forall p,
    (p =? p) = true.
Proof.
  intros.
  induction p.
  reflexivity.
  simpl.
  apply IHp.
Qed.

(** **** Exercise: 3 stars, standard, optional (eqb_trans)  *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros.
  apply eqb_true in H.
  apply eqb_true in H0.
  rewrite H, H0.
  apply eqb_refl.
Qed.


(** **** Exercise: 3 stars, advanced (split_combine) 

    We proved, in an exercise above, that for all lists of pairs,
    [combine] is the inverse of [split].  How would you formalize the
    statement that [split] is the inverse of [combine]?  When is this
    property true?

    Complete the definition of [split_combine_statement] below with a
    property that states that [split] is the inverse of
    [combine]. Then, prove that the property holds. (Be sure to leave
    your induction hypothesis general by not doing [intros] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split (combine l1 l2) = (l1,l2)] to be true?) *)

Definition split_combine_statement : Prop :=
  forall (X Y : Type) (l : list (X * Y)) (l1 : list X) (l2 : list Y),
    length l1 = length l2 ->
      combine l1 l2 = l -> split l = (l1, l2).

Lemma prod_list_cons : 
      forall (X Y : Type) (x : X) (y : Y) l1 l2 l3 l4,
             (l1, l2) = (l3, l4) -> (x :: l1, y :: l2) = (x :: l3, y :: l4).
Proof.
  intros.
  injection H as eq1 eq2.
  rewrite eq1, eq2.
  reflexivity.
Qed.

Theorem split_combine : split_combine_statement.
Proof.
  unfold split_combine_statement.
  intros X Y l.
  induction l.
  - (* l = [] *) 
    intros l1 l2 H H1.
    destruct l1.
    + (* l1 = [] *)
      destruct l2.
        * (* l2 = [] *) reflexivity.
        * (* l2 = x :: l2 *) discriminate H.
    + (* l1 = x :: l1 *)
      destruct l2.
        * (* l2 = [] *) discriminate H.
        * (* l1 = x :: l2 *) discriminate H1.
  - (* l = x :: l *)
    intros l1 l2 H H1.
    destruct l1.
    + (* l1 = [] *)
      destruct l2.
        * (* l2 = [] *) discriminate H1.
        * (* l2 = x :: l2 *) discriminate H.
    + (* l1 = x :: l1 *)
      destruct l2.
        * (* l2 = [] *) discriminate H.
        * (* l2 = x :: l2 *)
          destruct x as [x y].
          injection H1 as eq1 eq2 H1'.
          rewrite eq1, eq2.
          simpl.
          destruct (split l).
          apply prod_list_cons.
          apply IHl.
          injection H as eqlen.
          assumption.
          assumption.
Qed.

(** **** Exercise: 3 stars, advanced (filter_exercise) 

    This one is a bit challenging. Pay attention to the form of your
    induction hypothesis. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l lf.
  generalize dependent x.
  induction l as [| h l'].
  - (* l = [] *)
    intros x H.
    discriminate H.
  - (* l = h l' *)
    simpl.
    destruct (test h) eqn:E.
    + (* test h = true *)
      intros x H.
      injection H as eq1 eq2.
      rewrite eq1 in E.
      apply E.
    + (* test h = false *)
      intros x H.
      apply IHl'.
      apply H.
Qed.

(** **** Exercise: 4 stars, advanced, recommended (forall_exists_challenge) 

    Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:

      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true

      forallb evenb [0;2;4;5] = false

      forallb (eqb 5) [] = true

    The second checks whether there exists an element in the list that
    satisfies a given predicate:

      existsb (eqb 5) [0;2;3;6] = false

      existsb (andb true) [true;true;false] = true

      existsb oddb [1;0;0;0;0;3] = true

      existsb evenb [] = false

    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].

    Finally, prove a theorem [existsb_existsb'] stating that
    [existsb'] and [existsb] have the same behavior.
*)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => match (test h) with
              | false => false
              | true => forallb test t
              end
  end.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.

Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | h :: t => match (test h) with
              | false => existsb test t
              | true => true
              end
  end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example test_existsb_4 : existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros.
  induction l.
  - (* l = [] *)
    reflexivity.
  - (* l = x :: l *)
    destruct (test x) eqn:testxeqn.
    + (* (test x) = true *)
      unfold existsb'.
      simpl.
      rewrite testxeqn.
      reflexivity.
    + (* (test x) = false *)
      simpl.
      rewrite testxeqn.
      unfold existsb'.
      simpl.
      rewrite testxeqn.
      simpl.
      rewrite -> IHl.
      reflexivity.
Qed.








































