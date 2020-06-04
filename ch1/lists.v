From LF Require Export basics.


Inductive natprod : Type :=
| pair (n1 n2 : nat).

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** **** Exercise: 1 star, standard (snd_fst_is_swap)  *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros.
  destruct p.
  reflexivity.
Qed.


(** **** Exercise: 1 star, standard, optional (fst_swap_is_snd)  *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros.
  destruct p.
  reflexivity.
Qed.


Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.



(** **** Exercise: 2 stars, standard, recommended (list_funs) 

    Complete the definitions of [nonzeros], [oddmembers], and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => nonzeros t
  | h :: t => h :: (nonzeros t)
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
  reflexivity.
Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => 
              match oddb h with
              | true => h :: (oddmembers t)
              | false => (oddmembers t)
              end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
  reflexivity.
Qed.

Definition countoddmembers (l:natlist) : nat :=
  length ( oddmembers l ).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof.
  reflexivity.
Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof.
  reflexivity.
Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (alternate) 

    Complete the following definition of [alternate], which
    interleaves two lists into one, alternating between elements taken
    from the first list and elements from the second.  See the tests
    below for more specific examples.

    (Note: one natural and elegant way of writing [alternate] will
    fail to satisfy Coq's requirement that all [Fixpoint] definitions
    be "obviously terminating."  If you find yourself in this rut,
    look for a slightly more verbose solution that considers elements
    of both lists at the same time.  One possible solution involves
    defining a new kind of pairs, but this is not the only way.)  *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l2 with
  | [] => l1
  | h2 :: t2 => match l1 with
                  | [] => l2
                  | h1 :: t1 => h1 :: h2 :: (alternate t1 t2)
                end
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof.
  reflexivity.
Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof.
  reflexivity.
Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof.
  reflexivity.
Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof.
  reflexivity.
Qed.



Definition bag := natlist.

(** **** Exercise: 3 stars, standard, recommended (bag_functions) 

    Complete the following definitions for the functions
    [count], [sum], [add], and [member] for bags. *)

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | [] => 0
  | h :: t => match (eqb h v) with
              | true => 1 + (count v t)
              | false => (count v t)
              end
  end.

(** All these proofs can be done just by [reflexivity]. *)

Example test_count1:
  count 1 [1;2;3;1;4;1] = 3.
Proof.
  reflexivity.
Qed.

Example test_count2:
  count 6 [1;2;3;1;4;1] = 0.
Proof.
  reflexivity.
Qed.

(** Multiset [sum] is similar to set [union]: [sum a b] contains all
    the elements of [a] and of [b].  (Mathematicians usually define
    [union] on multisets a little bit differently -- using max instead
    of sum -- which is why we don't call this operation [union].)  For
    [sum], we're giving you a header that does not give explicit names
    to the arguments.  Moreover, it uses the keyword [Definition]
    instead of [Fixpoint], so even if you had names for the arguments,
    you wouldn't be able to process them recursively.  The point of
    stating the question this way is to encourage you to think about
    whether [sum] can be implemented in another way -- perhaps by
    using one or more functions that have already been defined.  *)

Definition sum : bag -> bag -> bag :=
  app.

Example test_sum1:
  count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof.
  reflexivity.
Qed.

Definition add (v:nat) (s:bag) : bag :=
  app [v] s.

Example test_add1:
  count 1 (add 1 [1;4;1]) = 3.
Proof.
  reflexivity.
Qed.

Example test_add2:
  count 5 (add 1 [1;4;1]) = 0.
Proof.
  reflexivity.
Qed.

Definition member (v:nat) (s:bag) : bool :=
  0 <? (count v s).

Example test_member1:
  member 1 [1;4;1] = true.
Proof.
  reflexivity.
Qed.

Example test_member2:
  member 2 [1;4;1] = false.
Proof.
  reflexivity.
Qed.



(** **** Exercise: 3 stars, standard, optional (bag_more_functions) 

    Here are some more [bag] functions for you to practice with. *)

(** When [remove_one] is applied to a bag without the number to
    remove, it should return the same bag unchanged.  (This exercise
    is optional, but students following the advanced track will need
    to fill in the definition of [remove_one] for a later
    exercise.) *)

Fixpoint remove_one (v:nat) (s:bag) : bag:=
  match s with
  | [] => []
  | h :: t =>
              match eqb h v with
              | true => t
              | false => h::(remove_one v t)
              end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof.
  reflexivity.
Qed.


Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof.
  reflexivity.
Qed.


Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof.
  reflexivity.
Qed.


Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof.
  reflexivity.
Qed.


Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | [] => []
  | h :: t =>
              match eqb h v with
              | true => (remove_all v t)
              | false => h::(remove_all v t)
              end
  end.

Example test_remove_all1:
  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof.
  reflexivity.
Qed.

Example test_remove_all2:
  count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof.
  reflexivity.
Qed.

Example test_remove_all3:
  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof.
  reflexivity.
Qed.

Example test_remove_all4:
  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof.
  reflexivity.
Qed.


Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | [] => true
  | h1 :: t1 => match member h1 s2 with
                | true => subset t1 (remove_one h1 s2)
                | false => false
                end
  end.

Example test_subset1:
  subset [1;2] [2;1;4;1] = true.
Proof.
  reflexivity.
Qed.

Example test_subset2:
  subset [1;2;2] [2;1;4;1] = false.
Proof.
  reflexivity.
Qed.





(** **** Exercise: 2 stars, standard, recommended (bag_theorem) 

    Write down an interesting theorem [bag_theorem] about bags
    involving the functions [count] and [add], and prove it.  Note
    that, since this problem is somewhat open-ended, it's possible
    that you may come up with a theorem that is true but whose proof
    requires techniques you haven't learned yet.  Ask for help if you
    get stuck! *)

(*

  You can find some cool basic properties of bags here and play around with them:
    https://en.wikipedia.org/wiki/Multiset

  You also can try proving this theorem:  
    forall n t: nat, forall s : bag,
      1 <=? bag_length s = true ->
          (bag_length s) <= bag_length (remove_one n s) +1 = true.

  This one is actually very tricky, but if you do it, it's gonna be so cool!


*)

Theorem bag_theorem:
  forall s1 s2 : bag,
    forall n : nat,
      count n ( sum s1 s2 ) = (count n s1) + (count n s2).
Proof.
  intros.
  induction s1.
  simpl.
  reflexivity.
  - destruct ( n0 =? n ) eqn:Hn.
    simpl.
    rewrite Hn.
    simpl.
    rewrite IHs1.
    reflexivity.
  simpl.
  rewrite Hn.
  rewrite IHs1.
  reflexivity.
Qed.


















