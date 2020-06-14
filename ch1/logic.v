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


























