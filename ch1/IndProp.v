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









