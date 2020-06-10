From LF Require Export lists.


Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).


Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.


(** **** Exercise: 2 stars, standard (mumble_grumble) 

    Consider the following two inductively defined types. *)

Module MumbleGrumble.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?  (Add YES or NO to each line.)
      - [d (b a 5)]                   No: d's argument does not have type.
      - [d mumble (b a 5)]            YES
      - [d bool (b a 5)]              YES
      - [e bool true]                 YES
      - [e mumble (b c 0)]            YES
      - [e bool (b c 0)]              No: (b c 0) is not a bool.
      - [c]                           No: It's a mumble.
*)

End MumbleGrumble.


Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).



(** **** Exercise: 2 stars, standard, optional (poly_exercises) 

    Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Complete the proofs below. *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, optional (more_poly_exercises) 

    Here are some slightly more interesting ones... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1.
  rewrite app_nil_r.
  reflexivity.
  simpl.
  rewrite IHl1.
  rewrite app_assoc.
  reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite rev_app_distr.
  rewrite IHl.
  reflexivity.
Qed.



Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.



(** **** Exercise: 1 star, standard, optional (combine_checks) 

    Try answering the following questions on paper and
    checking your answers in Coq:
    - What is the type of [combine] (i.e., what does [Check
      @combine] print?)
    - What does

        Compute (combine [1;2] [false;false;true;true]).

      print?
*)

(* Just try them :) *)


(** **** Exercise: 2 stars, standard, recommended (split) 

    The function [split] is the right inverse of [combine]: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called [unzip].

    Fill in the definition of [split] below.  Make sure it passes the
    given unit test. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) := 
  match l with
  | [] => ([], [])
  | (x, y) :: t => match split t with
                   | (x1, y1) =>  (x :: x1, y :: y1)
                   end
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  reflexivity.
Qed.





Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** **** Exercise: 2 stars, standard (filter_even_gt7) 

    Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7. *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (7 <? n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof.
  reflexivity.
Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof.
  reflexivity.
Qed.


(** **** Exercise: 3 stars, standard (partition) 

    Use [filter] to write a Coq function [partition]:

      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X

   Given a set [X], a predicate of type [X -> bool] and a [list X],
   [partition] should return a pair of lists.  The first member of the
   pair is the sublist of the original list containing the elements
   that satisfy the test, and the second is the sublist containing
   those that fail the test.  The order of elements in the two
   sublists should be the same as their order in the original list. *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  (filter test l, filter (fun ntest => negb (test ntest)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof.
  reflexivity.
Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof.
  reflexivity.
Qed.




Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.




(** **** Exercise: 3 stars, standard (map_rev) 

    Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)
Lemma map_dstr :
  forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros.
  induction l1.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.


Theorem map_rev :
  forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite map_dstr.
  rewrite IHl.
  reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, recommended (flat_map) 

    The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:

        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y) :=
  match l with
  | [] => []
  | cons h t => f h ++ flat_map f t
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof.
  reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, optional (implicit_args) 

    The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  (This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.)
*)

(* Just do it! *)




Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** **** Exercise: 1 star, advanced (fold_types_different) 

    Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different? *)

(* ??? *)























