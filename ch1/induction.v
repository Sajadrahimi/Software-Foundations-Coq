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

(******************************)

(*  
    standard, recommended (mult_comm)
      Use assert to help prove this theorem.-
      You shouldn't need to use induction on plus_swap. 
*)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n).
  rewrite plus_comm. reflexivity.
  rewrite -> H. reflexivity.
Qed.


(* Now prove commutativity of multiplication. 
   You will probably want to define and prove a "helper" theorem to be used in-
   the proof of this one. Hint: what is n × (1 + k)? 
*)

Theorem mult_1_plus_n : forall m n : nat,
  n * ( S m ) = n + ( n * m )
.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite -> plus_swap.
  f_equal.
  f_equal.
  assumption.
Qed.  


Theorem mult_comm : forall m n : nat,
  m * n = n * m.  

Proof.
  intros.
  induction n.
  rewrite <- mult_n_O.
  reflexivity.
  simpl.
  rewrite -> mult_1_plus_n.
  rewrite -> IHn.
  reflexivity.
Qed.
  

(******************************)

(*  standard, optional (more_exercises) 

      Take a piece of paper.  For each of the following theorems, first
      _think_ about whether (a) it can be proved using only
      simplification and rewriting, (b) it also requires case
      analysis ([destruct]), or (c) it also requires induction.  Write
      down your prediction.  Then fill in the proof.  (There is no need
      to turn in your piece of paper; this is just to encourage you to
      reflect before you hack!) *)

Check leb.

Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  assumption.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  intros.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  destruct b;reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros.
  induction p.
  assumption.
  assumption.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  intros.
  reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros.
  simpl.
  rewrite <- plus_n_O.
  reflexivity.
Qed.



Lemma excluded_middle: forall b : bool,
  orb b (negb b) = true.
Proof.
  intros.
  destruct b; reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros.
  destruct b.
  simpl.
  rewrite excluded_middle; reflexivity.
  reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite -> IHn.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite -> IHn.
  rewrite mult_plus_distr_r.
  reflexivity.
Qed.


(******************************)
(*  standard, recommended (binary_commute) 

    Recall the [incr] and [bin_to_nat] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that the following diagram commutes:

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    That is, incrementing a binary number and then converting it to
    a (unary) natural number yields the same result as first converting
    it to a natural number and then incrementing.
    Name your theorem [bin_to_nat_pres_incr] ("pres" for "preserves").
*)


Lemma S_m_n : forall n m : nat,
  S ( m + n ) = S m + n.
Proof.
  intros.
  induction n;reflexivity.
Qed.

Lemma incr_m_S_nat_m : forall m : bin,
  bin_to_nat m + 1 = S (bin_to_nat m).
Proof.
  intros.
  induction m.
  reflexivity.
  simpl.
  rewrite <- plus_n_O.
  rewrite <- plus_assoc.
  rewrite -> IHm.
  rewrite S_m_n.
  rewrite <- plus_comm.
  reflexivity.
  simpl.
  rewrite <- plus_n_O.
  rewrite -> S_m_n.
  rewrite <- plus_comm.
  reflexivity.
Qed.

Lemma bin_to_nat_pres_incr : forall m : bin,
  bin_to_nat (incr m) = S (bin_to_nat m).
Proof.
  intros m.
  induction m.
  reflexivity.
  simpl.
  rewrite <- plus_n_O.
  rewrite <- plus_assoc.
  rewrite plus_n_Sm.
  rewrite <- incr_m_S_nat_m.
  reflexivity.
  simpl.
  rewrite <- plus_n_O.
  rewrite <- plus_n_O.
  rewrite -> IHm.
  simpl.
  rewrite <- incr_m_S_nat_m.
  simpl.
  rewrite -> S_m_n.
  rewrite -> S_m_n.
  rewrite -> S_m_n.
  rewrite <- plus_assoc.
  reflexivity.
Qed.




(*  advanced (binary_inverse) 

    This is a further continuation of the previous exercises about
    binary numbers.  You may find you need to go back and change your
    earlier definitions to get things to work here.

    (a) First, write a function to convert natural numbers to binary
        numbers. *)

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

(** Prove that, if we start with any [nat], convert it to binary, and
    convert it back, we get the same [nat] we started with.  (Hint: If
    your definition of [nat_to_bin] involved any extra functions, you
    may need to prove a subsidiary lemma showing how such functions
    relate to [nat_to_bin].) *)

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite bin_to_nat_pres_incr.
  rewrite IHn.
  reflexivity.
Qed.

(** (b) One might naturally expect that we should also prove the
        opposite direction -- that starting with a binary number,
        converting to a natural, and then back to binary should yield
        the same number we started with.  However, this is not the
        case!  Explain (in a comment) what the problem is. *)

(**** The defined Binary Representation for each nat is not  unique.
   For example 0 can be represnted as Z, B Z, B B B Z, ... ****)


(** (c) Define a normalization function -- i.e., a function
        [normalize] going directly from [bin] to [bin] (i.e., _not_ by
        converting to [nat] and back) such that, for any binary number
        [b], converting [b] to a natural and then back to binary yields
        [(normalize b)].  Prove it.  (Warning: This part is a bit
        tricky -- you may end up defining several auxiliary lemmas.
        One good way to find out what you need is to start by trying
        to prove the main statement, see where you get stuck, and see
        if you can find a lemma -- perhaps requiring its own inductive
        proof -- that will allow the main proof to make progress.) Don't
        define this using [nat_to_bin] and [bin_to_nat]! *)



(* Double of Z is Z and double of anything else is just itself with another-
   zero in front of it *)
Fixpoint double_bin (b:bin) : bin :=
  match b with 
  | Z => Z
  | _ => A b
  end.

(* Normal of Z is Z,
   Normal of anything in form of "n'0" is normal of n' with 0 in front of it-
  (see double_bin definition)
   Normal of anything in form of "n'1" is normal of n' whit 1 in front of it

  This Definition can be rewrite without double, just using B as zero-concatinator
*)
Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z  => Z
  | A b' => double_bin( normalize b')
  | B b' => B (normalize b')
  end.


Lemma double_inc : forall m : bin,
  double_bin ( incr m ) = incr (incr ( double_bin m )).
Proof.
  intros.
  induction m; reflexivity.
Qed.

Lemma double_to_plus : forall n : nat, 
  nat_to_bin (n + n) = double_bin (nat_to_bin n). 
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite <- plus_n_Sm.
  simpl.
  rewrite -> IHn.
  simpl.
  rewrite double_inc.
  reflexivity.
Qed.

Lemma plus_1_to_inct : forall n : nat,
  nat_to_bin (n + 1) = incr (nat_to_bin n).
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma incr_double : forall m : bin,
  incr (double_bin m) = B m.
Proof.
  intros.
  induction m;reflexivity.
Qed.

Theorem bin_nat_bin: forall m : bin,
  nat_to_bin (bin_to_nat m) = normalize m.
Proof.
  intros.
  induction m.
  reflexivity.
  simpl.
  rewrite <- plus_n_O.
  rewrite double_to_plus.
  rewrite IHm; reflexivity.
  simpl.
  rewrite <- plus_n_O.
  rewrite plus_1_to_inct.
  rewrite  double_to_plus.
  rewrite IHm.
  rewrite incr_double.
  reflexivity.
Qed.

















