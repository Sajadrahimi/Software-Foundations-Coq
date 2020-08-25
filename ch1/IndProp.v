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
  induction n as [|n'].
  - left. apply O_le_n.
  - simpl in H. apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply IHn' in H as [H1 | H2].
    + left. Admitted.

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


(** **** Exercise: 3 stars, standard, optional (R_fact) 

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq? *)

Definition fR : nat -> nat -> nat:=
  (fun (x y : nat) => (x + y)).

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros.
  split.
  - (* -> *)
    intro.
    induction H; unfold fR.
      + reflexivity.
      + simpl. f_equal. apply IHR.
      + rewrite plus_comm. simpl. f_equal. rewrite plus_comm. apply IHR.
      + unfold fR in IHR. simpl in IHR. inversion IHR.
        rewrite <- plus_n_Sm in H1. inversion H1. reflexivity.
      + unfold fR in IHR. rewrite plus_comm in IHR. assumption.
  - (* <- *)
    intro.
    induction H. induction n.
      + induction m.
        * simpl. apply c1.
        * simpl. apply c2. apply IHm.
      + induction m.
        * simpl. apply c3. apply IHn.
        * simpl. apply c2. apply IHm. apply c3 in IHn. apply c4. apply IHn.
Qed.

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
  | sub_nil : forall l, subseq [] l
  | sub_cons1 : forall k l n, (subseq k l) -> (subseq k (n :: l))
  | sub_cons2 : forall k l n, (subseq k l) -> (subseq (n::k) (n::l))
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros.
  induction l.
  - apply sub_nil.
  - apply sub_cons2. apply IHl.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H.
  - apply sub_nil.
  - simpl. apply sub_cons1. apply IHsubseq.
  - simpl. apply sub_cons2. apply IHsubseq.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2. generalize dependent H1. generalize dependent l1.
  induction H2; intros.
  - inversion H1. apply sub_nil.
  - apply sub_cons1. apply IHsubseq. apply H1.
  - inversion H1.
    + apply sub_nil.
    + apply sub_cons1. apply IHsubseq. apply H3.
    + apply sub_cons2. apply IHsubseq. apply H3.
Qed.

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



Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.


(** **** Exercise: 3 stars, standard (exp_match_ex1) 

    The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 H.
  destruct H.
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H.
  induction ss as [|ss'].
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IHss. intros. apply H. simpl. right. apply H0.
Qed.

(** **** Exercise: 4 stars, standard, optional (reg_exp_of_list_spec) 

    Prove that [reg_exp_of_list] satisfies the following
    specification: *)
Lemma add_to_app: forall S (x:S) y, [x]++y = x::y.
Proof.
  intros S x y. simpl. reflexivity.
Qed.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2. 
  generalize dependent s1.
  induction s2 as [|h t].
  - (* s2 = [] *)
    split. 
    + intros H. simpl in H. inversion H. reflexivity.
    + intros H. simpl. rewrite H. apply MEmpty.
  - (* s2 = h::t *)
    intros s1. split. 
    + intros H. simpl in H. inversion H. 
      inversion H3. simpl. 
      rewrite (IHt s2) in H4. rewrite H4. reflexivity.
    + intros H. simpl. rewrite H.
      rewrite <- add_to_app. apply MApp.
      * apply MChar.
      * apply IHt. reflexivity.
Qed.


Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.

(** Something interesting happens in the [MApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re1]), and a second one that applies when [x]
    occurs in [s2] (which matches [re2]). *)

    rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.

(** Here again we get two induction hypotheses, and they illustrate
    why we need induction on evidence for [exp_match], rather than
    induction on the regular expression [re]: The latter would only
    provide an induction hypothesis for strings that match [re], which
    would not allow us to reason about the case [In x s2]. *)

    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.




(** **** Exercise: 4 stars, standard (re_not_empty) 

    Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
    | EmptySet => false
    | EmptyStr => true
    | Char _ => true
    | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
    | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
    | Star re1 => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re.
  split.
  - intros [s H].
    induction H.
    + (* EmptyStr *) reflexivity.
    + (* Char *) reflexivity.
    + (* App *) simpl. rewrite IHexp_match1. rewrite IHexp_match2. reflexivity.
    + (* UnionL *) simpl. rewrite IHexp_match. reflexivity.
    + (* UnionR *) simpl. rewrite IHexp_match. destruct (re_not_empty re1); reflexivity.
    + (* Star0 *) reflexivity.
    + (* StarApp *) reflexivity.
  - intros H.
    induction re.
    + (* EmptySet *) discriminate H.
    + (* EmptyStr *) exists []. apply MEmpty.
    + (* Char *) exists [t]. apply MChar.
    + (* App *) simpl in H. rewrite andb_true_iff in H. destruct H as [H1 H2].
      apply IHre1 in H1. destruct H1 as [s1 H1].
      apply IHre2 in H2. destruct H2 as [s2 H2].
      exists (s1++s2). apply MApp; assumption.
    + (* Union *) simpl in H. rewrite orb_true_iff in H.
      destruct H as [H1 | H2].
      * apply IHre1 in H1. destruct H1. exists x. apply MUnionL. apply H.
      * apply IHre2 in H2. destruct H2. exists x. apply MUnionR. apply H.
    + (* Start *) exists []. apply MStar0.
Qed.


(** **** Exercise: 4 stars, standard, optional (exp_match_ex2)  *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H.
  remember (Star re) as re'.
  induction H
    as [|x'|s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
        |re''|s1 s2 re'' Hmatch1 IH1 Hmatch2 IH2].
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - (* Star 0 *)
    exists []. split.
    + reflexivity. 
    + intros s' H. inversion H.
  - (* Star  *)
    destruct (IH2 Heqre') as [ss' [L R]].
    exists (s1::ss'). split.
    + simpl. rewrite <- L. reflexivity.
    + intros s' H. destruct H.
      * rewrite <- H. inversion Heqre'. rewrite H1 in Hmatch1. apply Hmatch1.
      * apply R. apply H.
Qed.




(** **** Exercise: 5 stars, advanced (weak_pumping) 

    One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].  (For the sake of simplicity in this
    exercise, we consider a slightly weaker theorem than is usually
    stated in courses on automata theory.)

    To get started, we need to define "sufficiently long."  Since we
    are working in a constructive logic, we actually need to be able
    to calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

(** You may find these lemmas about the pumping constant useful when
    proving the pumping lemma below. *)

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    1 <= pumping_constant re.
Proof.
  intros T re. induction re.
  - (* Emptyset *)
    apply le_n.
  - (* EmptyStr *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* App *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Union *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Star *)
    simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : 1 <= pumping_constant re).
  { apply pumping_constant_ge_1. }
  inversion Hp1.
  - rewrite H in H2. discriminate H2.
  - rewrite H in H0. discriminate H0.
Qed.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

(** This auxiliary lemma might also be useful in your proof of the
    pumping lemma. *)

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.


(** The (weak) pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3] will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

Lemma plus_le_one: forall n m,
      1 <= n + m -> 1 <= n \/ 1 <= m.
Proof.
  intros.
  generalize dependent n.
  induction m.
  - intros n H.  left. replace n with (n + 0).
    + assumption.
    + rewrite plus_n_O. reflexivity.
  - intros n H.
    right.
    apply n_le_m__Sn_le_Sm.
    apply O_le_n.
Qed.

Lemma length_le_one__neq_empty: forall (X:Type) (s:list X),
      1 <= length s -> s <> [].
Proof.
  intros.
  induction s.
  + simpl in H. apply Sn_le_O in H. apply ex_falso_quodlibet. assumption.
  + unfold not. intros. rewrite H0 in H. simpl in H. apply Sn_le_O in H.
    assumption.
Qed.

Lemma app_star: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)  inversion Heqre'.
  - (* MChar *)   inversion Heqre'.
  - (* MApp *)    inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.
  - (* MStar0 *)
    inversion Heqre'. intros s H. apply H.
  - (* MStarApp *)
    inversion Heqre'. rewrite H0 in IH2, Hmatch1.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You are to fill in the proof. Several of the lemmas about
    [le] that were in an optional exercise earlier in this chapter
    may be useful. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - (* Char *)
    simpl. intros contra. inversion contra. inversion H1.
  - (* App *)
    simpl. rewrite app_length. intros H. apply add_le_cases in H. destruct H as [H1 | H2].
      + apply IH1 in H1. destruct H1 as [s2' [s3' [s4' [H0 [H1 H2]]]]].
        exists s2'. exists s3'. exists (s4'++s2). split.
        * rewrite H0. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
        * split. apply H1.
          intros.
          replace (s2' ++ napp m s3' ++ s4' ++ s2) with ((s2' ++ napp m s3' ++ s4') ++ s2).
          apply (MApp (s2' ++ napp m s3' ++ s4')).
          apply H2.
          apply Hmatch2.
          rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
      + apply IH2 in H2. inversion H2 as [s2' [s3' [s4' [H0' [H1' H2']]]]].
        exists (s1++s2'). exists s3'. exists s4'.
        split.
        * rewrite H0'. rewrite <- app_assoc. reflexivity.
        * split. apply H1'.
          intros.
          rewrite <- app_assoc.
          apply MApp.
          apply Hmatch1.
          apply H2'.
  - (* Union L*)
    simpl. intros. apply plus_le in H as [H1 H2].
    apply IH in H1. inversion H1 as [s2' [s3' [s4' [H3 [H4 H5]]]]].
    exists s2'. exists s3'. exists s4'. split.
    +  rewrite H3. reflexivity.
    + split.
      * apply H4.
      * intros. apply MUnionL. apply H5.
  - (* Union R*)
    simpl. intros. apply plus_le in H as [H1 H2].
    apply IH in H2. inversion H2 as [s2' [s3' [s4' [H3 [H4 H5]]]]].
    exists s2'. exists s3'. exists s4'. split.
    +  rewrite H3. reflexivity.
    + split.
      * apply H4.
      * intros. apply MUnionR. apply H5.
  - (* Star *)
    simpl. intros. inversion H. apply pumping_constant_0_false in H2.
    apply ex_falso_quodlibet. apply H2.
  - (* Star *)
    simpl. simpl in IH2. intros. rewrite app_length in H.
    assert (Ht: 1 <= pumping_constant re).
    { apply pumping_constant_ge_1. }
    assert (H1: 1 <= length s1 + length s2).
    { apply le_trans with (n:= pumping_constant re). apply Ht. apply H. }
    assert (H2: 1 <= length s1 \/ 1 <= length s2).
    { apply plus_le_one in H1. apply H1. }
    destruct H2.
    + exists []. exists s1. exists s2.
      split.
      * reflexivity.
      * split.
        (* s1 <> [ ] *)
        unfold not. intro.
        assert (H2': length s1 = 0).
        { rewrite H2. reflexivity. }
        rewrite H2' in H0. apply Sn_le_O in H0. assumption.
        (* forall m : nat, [ ] ++ napp m s1 ++ s2 =~ Star re *)
        intros m. simpl. apply napp_star; assumption.
    + exists s1. exists s2. exists [].
      split.
      * rewrite app_nil_r. reflexivity.
      * split.
        (* s2 <> [ ] *)
        unfold not. intro.
        assert (H2': length s2 = 0).
        { rewrite H2. reflexivity. }
        rewrite H2' in H0. apply Sn_le_O in H0. assumption.
        (* forall m : nat, s1 ++ napp m s2 ++ [ ] =~ Star re *)
        intros m. rewrite app_nil_r. 
        apply app_star. replace s1 with (s1 ++ []). apply MStarApp. apply Hmatch1. 
        apply MStar0. rewrite app_nil_r. reflexivity.
        induction m.
        { simpl. apply MStar0. }
        { simpl. apply app_star. apply Hmatch2. apply IHm. }
Qed.

(** **** Exercise: 5 stars, advanced, optional (pumping) 

    Now here is the usual version of the pumping lemma. In addition to
    requiring that [s2 <> []], it also requires that [length s1 +
    length s2 <= pumping_constant re]. *)

Lemma app_length_le: forall (X:Type) (s1 s2:list X),
      length s2 <= length (s1 ++ s2).
Proof.
  intros.
  induction s1.
  - simpl. apply le_n.
  - simpl. apply le_S. apply IHs1.
Qed.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You may want to copy your proof of weak_pumping below. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - simpl. intros contra. inversion contra.
  - simpl. intros contra. inversion contra. inversion H1.
  - simpl. intros. rewrite app_length in H. apply add_le_cases in H. destruct H as [H1|H2].
      + apply IH1 in H1. destruct H1 as [s2' [s3' [s4' [H1 [H2 H3]]]]].
        exists s2'. exists s3'. exists (s4' ++ s2). split.
        * rewrite H1. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
        * split. apply H2.
          destruct H3.
          split.
          { apply le_trans with (n:= pumping_constant re1). apply H. apply le_plus_l. }
          { intros.
            replace (s2' ++ napp m s3' ++ s4' ++ s2) with ((s2' ++ napp m s3' ++ s4') ++ s2).
            apply (MApp (s2' ++ napp m s3' ++ s4')). apply H0. apply Hmatch2.
            rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
      + apply IH2 in H2. inversion H2 as [s2' [s3' [s4' [H1' [H2' H3']]]]].
        exists (s1++s2'). exists (s3'). exists s4'.
        split.
        * rewrite H1'. rewrite <- app_assoc. reflexivity.
        * split. apply H2'.
          split.
          {  destruct H3' as [H3' H4']. rewrite app_length.
            apply le_trans with (n:=pumping_constant re2).
             Admitted. }

End Pumping.


Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(** **** Exercise: 2 stars, standard, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. destruct H.
  - split.
    + (* -> *) reflexivity.
    + intros. assumption.
  - split.
    + intros. apply ex_falso_quodlibet. apply H. apply H0.
    + intros. discriminate.
Qed.

Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. assumption.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, recommended (eqbP_practice) 

    Use [eqbP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n.
  induction l.
  - unfold not. intros. simpl in H0. assumption.
  - simpl. destruct (eqbP n x) as [H1|H1].
    + intros. unfold not. intros. inversion H.
    + intros. unfold not. intros. apply IHl in H. destruct H0.
      * unfold not in H1. symmetry in H0. apply H1 in H0. assumption.
      * apply H. apply H0.
Qed.

(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, recommended (nostutter_defn) 

    Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence [[1;4;1]] repeats the element [1] but does not
    stutter.)  The property "[nostutter mylist]" means that [mylist]
    does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
  | ns_nil : nostutter []
  | ns_one : forall x, nostutter [x]
  | ns_con : forall x h t, nostutter (h :: t) ->  ~ (x = h) -> nostutter (x :: h :: t)
.

(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.

Example test_nostutter_2:  nostutter (@nil nat).
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.

Example test_nostutter_3:  nostutter [5].
  Proof. repeat constructor; apply eqb_false; auto. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto.
Qed.

(** **** Exercise: 4 stars, advanced (filter_challenge) 

    Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    Translate this specification into a Coq theorem and prove
    it.  (You'll need to begin by defining what it means for one list
    to be a merge of two others.  Do this with an inductive relation,
    not a [Fixpoint].)  *)

(* FILL IN HERE *)


(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) 

    A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

(* FILL IN HERE *)

(** **** Exercise: 4 stars, standard, optional (palindromes) 

    A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

(* FILL IN HERE *)


(** **** Exercise: 5 stars, standard, optional (palindrome_converse) 

    Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

(* FILL IN HERE

    [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup) 

    Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

(* FILL IN HERE *)

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

(* FILL IN HERE *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

(* FILL IN HERE *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle) 

    The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros.
  induction l as [| h t].
  - apply ex_falso_quodlibet. simpl in H. assumption.
  - inversion H.
    + exists []. exists t. rewrite H0. reflexivity. 
    + apply IHt in H0. inversion H0 as [l1 [l2]].
      exists (h :: l1). exists l2. simpl. rewrite H1. reflexivity.
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | repeats_in : forall (x:X) (l : list X), In x l -> repeats (x :: l)
  | repeats_nin : forall (x:X) (l : list X), repeats l -> repeats (x :: l)
.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
  intros X l1. induction l1 as [|x l1' IHl1'].
  - intros. destruct l2.
    + inversion H1.
    + inversion H1.
  - intros. apply repeats_in. inversion H1.
    + Admitted.


Require Import Coq.Strings.Ascii.
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match autmatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function that reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implemement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)


Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne) 

    [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne) 

    [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps) 

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl) 

    Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive) 

    Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 4 stars, standard, optional (derive_corr) 

    Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(** A function [m] matches regexes if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match) 

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_refl) 

    Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_refl : matches_regex regex_match.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


















