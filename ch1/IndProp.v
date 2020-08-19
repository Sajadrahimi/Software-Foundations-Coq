Set Warnings "-notation-overridden,-parsing".
From LF Require Export logic.
Require Coq.omega.Omega.


Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).


(** **** Exercise: 1 star, standard (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros.
  induction n as [|n'].
    - (* n = 0 *) apply ev_0.
    - (* n = S n' *) simpl. apply ev_SS. apply IHn'.
Qed.


Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
    - (* E = ev_0 : ev 0 *)
      left. reflexivity.
    - (* E = ev_SS n' E' : ev (S (S n')) *)
      right. exists n'. split. reflexivity. apply E'.
Qed.


Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. apply ev_inversion in H. destruct H.
   - discriminate H.
   - destruct H as [n' [Hnm Hev]]. injection Hnm as Heq.
     rewrite Heq. apply Hev.
Qed.


(** **** Exercise: 1 star, standard (inversion_practice) 

    Prove the following result using [inversion].  (For extra practice,
    you can also prove it using the inversion lemma.) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem SSSSev__even___inversion_lemma : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  apply ev_inversion in H.
  destruct H as [H1 | H2].
  - discriminate H1.
  - destruct H2. destruct H.
    apply ev_inversion in H0.
    destruct H0 as [F | G].
    + rewrite F in H. discriminate H.
    + destruct G. destruct H0.
      rewrite H0 in H.
      injection H as E.
      rewrite <- E in H1.
      apply H1.
Qed.

(** **** Exercise: 1 star, standard (ev5_nonsense) 

    Prove the following result using [inversion]. *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

(** **** Exercise: 2 stars, standard (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m H H1.
  induction H as [| n'].
    - simpl. apply H1.
    - simpl. apply ev_SS. apply IHev.
Qed.

(** **** Exercise: 4 stars, advanced, optional (ev'_ev) 

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from [Logic]) of
    applying theorems to arguments, and note that the same technique
    works with constructors of inductively defined propositions. *)

Lemma SS_eq_plus_2: forall n, S (S n) = n + 2.
Proof.
  intros.
  induction n.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n.
  split.
    - intro.
      induction H.
      + apply ev_0.
      + apply ev_SS. apply ev_0.
      + apply ev_sum.
        * apply IHev'1.
        * apply IHev'2.
    - intro.
      induction H.
      + apply ev'_0.
      + simpl. rewrite SS_eq_plus_2. apply ev'_sum.
        * apply IHev.
        * apply ev'_2.
Qed.

(** **** Exercise: 3 stars, advanced, recommended (ev_ev__ev) 

    There are two pieces of evidence you could attempt to induct upon
    here. If one doesn't work, try the other. *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m H H1.
  induction H1.
  - simpl in H. apply H.
  - simpl in H. apply evSS_ev in H. apply IHev in H. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus) 

    This exercise just requires applying existing lemmas.  No
    induction or even case analysis is needed, though some of the
    rewriting may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p H.
  apply ev_ev__ev. rewrite plus_comm. rewrite plus_swap.
  rewrite <- plus_assoc. rewrite plus_assoc. apply ev_sum. 
  - apply H. 
  - rewrite <- double_plus. apply ev_double.
Qed.


Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_ev : nat -> nat -> Prop :=
  | ne_1 n (H: ev (S n))     : next_ev n (S n)
  | ne_2 n (H: ev (S (S n))) : next_ev n (S (S n)).

(** **** Exercise: 2 stars, standard, optional (total_relation) 

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)
Inductive universal_relation : nat -> nat -> Prop :=
  | uni : forall (n m :nat), universal_relation n m.


(** **** Exercise: 2 stars, standard, optional (empty_relation) 

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive null_relation : nat -> nat -> Prop :=.

(** **** Exercise: 3 stars, standard, optional (le_exercises) 

    Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H H1.
  induction H1.
  - apply H.
  - apply le_S. apply IHle. apply H.
Qed. 

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intro n.
  induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  inversion H.
  - apply le_n.
  - apply le_trans with (n:=S n).
    + apply le_S. apply le_n.
    + apply H2.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction a.
  - apply O_le_n.
  - simpl. apply n_le_m__Sn_le_Sm. apply IHa.
Qed.
  
Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m H.
  split.
  - (* n1 <= m *)
    induction n2.
    + rewrite <- plus_n_O in H. apply H.
    + apply IHn2. rewrite plus_comm in H. simpl in H. apply le_S in H.
      apply Sn_le_Sm__n_le_m in H. rewrite plus_comm in H. apply H.
  - (* n2 <= m *)
    induction n1.
    + rewrite plus_comm in H. rewrite <- plus_n_O in H. apply H.
    + apply IHn1. simpl in H. apply le_S in H.
      apply Sn_le_Sm__n_le_m in H. apply H.
Qed.

(** Hint: the next one may be easiest to prove by induction on [n]. *)
Lemma Sn_le_O: forall n,
  S n <= 0 <-> False.
Proof.
  intros.
  split.
    - intros. induction n.
      + inversion H.
      + inversion H.
    - intros. apply ex_falso_quodlibet. apply H.
Qed.

Theorem add_le_cases : forall n m p q,
    n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intros n m p q H.
  induction n.
  - left. apply O_le_n.
  - simpl in H. apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply IHn in H as [H1 | H2].
    + left.
      induction p.
      * Admitted.


Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros.
  apply le_S.
  apply H.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros.
  split.
  - (* S n1 <= m *)
    apply plus_le with (n1:=S(n1)) in H as [H1 H2]. apply H1.
  - (* S n2 <= m *)
    rewrite plus_n_Sm in H. apply plus_le with (n2:=S(n2)) in H as [H1 H2]. apply H2.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  induction n.
  - intros. apply O_le_n.
  - intros. destruct m.
    + inversion H.
    + apply n_le_m__Sn_le_Sm. simpl in H. apply IHn. apply H.
Qed. 

(** Hint: The next one may be easiest to prove by induction on [m]. *)

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros. generalize dependent n. induction m. 
  - intros. destruct n. 
    + reflexivity.
    + inversion H.
  - intros. destruct n. 
    + reflexivity.
    + apply IHm. apply Sn_le_Sm__n_le_m. apply H.
Qed. 


(** Hint: The next one can easily be proved without using [induction]. *)

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros.
  apply leb_correct.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply le_trans with (n:= m).
  - apply H.
  - apply H0.
Qed.

(** **** Exercise: 2 stars, standard, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros. split.
  - intro. apply leb_complete in H. apply H.
  - intro. apply leb_correct in H. apply H.
Qed.

Module R.

(** **** Exercise: 3 stars, standard, recommended (R_provability) 

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact) 

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq? *)

Definition fR : nat -> nat -> nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

End R.

(** **** Exercise: 2 stars, advanced (subsequence) 

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully! *)

Inductive subseq : list nat -> list nat -> Prop :=
(* FILL IN HERE *)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (R_provability2) 

    Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 n l (H: R n l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n l.

    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(* FILL IN HERE

    [] *)

