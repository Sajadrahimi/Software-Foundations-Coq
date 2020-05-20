(*  
    standard, recommended (basic_induction)
      Prove the following using induction. You might need previously proven results.
*)

From LF Require Export basics.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros.
  induction n.
  reflexivity.
  rewrite <- mult_n_O.
  reflexivity.
Qed.  


Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
Qed.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n.
  simpl.
  induction m.
  reflexivity.
  simpl.
  rewrite <- IHm.
  reflexivity.
  simpl.
  rewrite -> IHn.
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.
  

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
Qed.


(******************************)

(*  
    standard (double_plus)
      Consider the following function, which doubles its argument:

      Fixpoint double (n:nat) :=
        match n with
        | O ⇒ O
        | S n' ⇒ S (S (double n'))
        end.
      Use induction to prove this simple fact about double: 
*)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite -> IHn.
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.
  
(******************************)

(*  
    standard, optional (evenb_S)
      One inconvenient aspect of our definition of evenb n is the recursive call on-
      n - 2. This makes proofs about evenb n harder when done by induction on n,
      since we may need an induction hypothesis about n - 2.
      The following lemma gives an alternative characterization of evenb (S n) that-
      works better with induction: 
*)

Theorem negb_involutive : forall b:bool,
  negb (negb b) = b.
Proof.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros.
  induction n.
  reflexivity.
  rewrite -> IHn.
  rewrite -> negb_involutive.
  reflexivity.
Qed.












