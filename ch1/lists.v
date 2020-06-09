From LF Require Export induction.
Module NatList.

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

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.


Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
  Qed.


Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'.
    rewrite plus_comm.
    reflexivity.
Qed.


(** ** List Exercises, Part 1 *)

(** **** Exercise: 3 stars, standard (list_exercises) 

    More practice with lists: *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1 as [| n l1'].
  simpl.
  rewrite app_nil_r. reflexivity.
  simpl.
  rewrite -> IHl1'.
  rewrite app_assoc.
  reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
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

(** There is a short solution to the next one.  If you find yourself
    getting tangled up, step back and try to look for a simpler
    way. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  rewrite app_assoc.
  rewrite app_assoc.
  reflexivity.
Qed.

(** An exercise about your implementation of [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros.
  induction l1.
  reflexivity.
  destruct n as [| n']; simpl; rewrite IHl1; reflexivity.
Qed.


(** **** Exercise: 2 stars, standard (eqblist) 

    Fill in the definition of [eqblist], which compares
    lists of numbers for equality.  Prove that [eqblist l l]
    yields [true] for every list [l]. *)

Fixpoint eqblist (l1 l2 : natlist) : bool :=
    match l1, l2 with
    | [], [] => true
    | h1 :: t1, h2 :: t2 => match (h1 =? h2) with
                            | true => eqblist t1 t2
                            | false => false
                            end
    | _, _ => false
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof.
  reflexivity.
Qed.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof.
  reflexivity.
Qed.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof.
  reflexivity.
Qed.

Lemma eqb_rfl :
  forall n : nat,
    true = (n =? n).
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  assumption.
Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite <- eqb_rfl.
  assumption.
Qed.



(** ** List Exercises, Part 2 *)

(** Here are a couple of little theorems to prove about your
    definitions about bags above. *)

(** **** Exercise: 1 star, standard (count_member_nonzero)  *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros.
  reflexivity.
Qed.

(** The following lemma about [leb] might help you in the next exercise. *)

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.
Qed.

(** Before doing the next exercise, make sure you've filled in the
   definition of [remove_one] above. *)
(** **** Exercise: 3 stars, advanced (remove_does_not_increase_count)  *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros.
  induction s.
  reflexivity.
  destruct n.
  simpl.
  rewrite leb_n_Sn.
  reflexivity.
  simpl.
  assumption.
Qed.



(** **** Exercise: 3 stars, standard, optional (bag_count_sum) 

    Write down an interesting theorem [bag_count_sum] about bags
    involving the functions [count] and [sum], and prove it using
    Coq.  (You may find that the difficulty of the proof depends on
    how you defined [count]!) *)
(* FILL IN HERE

    [] *)

(** **** Exercise: 4 stars, advanced (rev_injective) 

    Prove that the [rev] function is injective -- that is,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

    (There is a hard way and an easy way to do this.) *)
Theorem rev_injective_r :
  forall (l1 l2 : natlist), l1 = l2 -> rev l1 = rev l2.
Proof.
  intros.
  rewrite -> H.
  reflexivity.
Qed.

Theorem rev_injective:
  forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  rewrite <- rev_involutive with (l := l1).
  rewrite <- rev_involutive with (l := l2).
  rewrite rev_injective_r with (l1 := (rev l1))(l2 := (rev l2)).
  reflexivity.
  assumption.
Qed.



Inductive natoption : Type :=
  | Some (n : nat)
  | None.


Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.


Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.


(** **** Exercise: 2 stars, standard (hd_error) 

    Using the same idea, fix the [hd] function from earlier so we don't
    have to pass a default element for the [nil] case.  *)

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof.
  reflexivity.
Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof.
  reflexivity.
Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof.
  reflexivity.
Qed.


(** **** Exercise: 1 star, standard, optional (option_elim_hd) 

    This exercise relates your new [hd_error] to the old [hd]. *)

Theorem option_elim_hd :
  forall (l:natlist) (default:nat),
    hd default l = option_elim default (hd_error l).
Proof.
  intros.
  destruct l; reflexivity.
Qed.



Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.


(** **** Exercise: 1 star, standard (eqb_id_refl)  *)
Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  intros.
  induction x.
  simpl.
  rewrite <- eqb_rfl.
  reflexivity.
Qed.


Module PartialMap.


Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.


(** **** Exercise: 1 star, standard (update_eq)  *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros.
  simpl.
  rewrite <- eqb_id_refl.
  reflexivity.
Qed.
  

(** **** Exercise: 1 star, standard (update_neq)  *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.
End PartialMap.

(** **** Exercise: 2 stars, standard (baz_num_elts) 

    Consider the following inductive definition: *)

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

(** How _many_ elements does the type [baz] have? (Explain in words,
    in a comment.) *)
(* Read This:
  https://cs.stackexchange.com/questions/29365/baz-num-elts-exercise-from-software-foundations
*)



End NatList.












