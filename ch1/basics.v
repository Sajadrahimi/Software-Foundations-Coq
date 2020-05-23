(* 
   standard (nandb) 
      The function should return true if either or both of its inputs are false. 
*)

Definition negb (b:bool):bool :=
  match b with
    | true => false
    | false => true
  end
.
Definition nandb (b1:bool) (b2:bool) : bool:=
  match b1 with
    | false => true
    | true => negb(b2)
  end
.


Example test_nandb1: (nandb true false) = true.
Proof.
  reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
  reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
Proof.
  reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
Proof.
  reflexivity.
Qed.

(******************************)

(*  
    standard (andb3) 
      This function should return true when all of its inputs are true, and false otherwise.
*)

 Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb b1 (andb b2 b3).

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_andb31: (andb3 true true true) = true.
Proof.
  unfold andb3, andb.
  reflexivity.
Qed.
Example test_andb32: (andb3 false true true) = false.
Proof.
  unfold andb3, andb.
  reflexivity.
Qed.
Example test_andb33: (andb3 true false true) = false.
Proof.
  unfold andb3, andb.
  reflexivity.
Qed.
Example test_andb34: (andb3 true true false) = false.
Proof.
  unfold andb3, andb.
  reflexivity.
Qed.

(******************************)

(*  
    standard (factorial) 
      Recall the standard mathematical factorial function:

         factorial(0)  =  1
         factorial(n)  =  n * factorial(n-1)     (if n>0)

      Translate this into Coq. 
*)

Fixpoint mult (n m : nat) : nat :=
    match n with
        | O     => O
        | S n'  => plus m (mult n' m)
    end.
Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S(O)
    | S(n') => mult n (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof.
  reflexivity.
Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
  reflexivity.
Qed.



(******************************)

(*  
    standard (ltb) 
      The ltb function tests natural numbers for less-than, yielding a boolean.
      Instead of making up a new Fixpoint for this one, define it in terms of a previously-
      defined function. (It can be done with just one previously defined function, but you can use-
      two if you want.) 
*)

Notation "x - y" := (minus x y)
                        (at level 50, left associativity)
                        : nat_scope.


(* if n = 0, then it is definitely lower than or equal to m. Else, if it's successor of some n',
   then check if m is 0 or not; if it is, it means m < n and return false, and if not,
   it means m is also successor of some m', in this case check if n' <= m'.
*)
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

(* Same as leb for eqb *)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

(* We define "lower than" as "n <= m and n is not equal to m" *)
Definition ltb (n m : nat) : bool :=
  (leb n m) && (negb (eqb n m )).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof.
  reflexivity.
Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof.
  reflexivity.
Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof.
  reflexivity.
Qed.


(******************************)

(*  
    standard (plus_id_exercise)
      Fill in the proof.
*)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.

Proof.
  intros.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
Qed.

(******************************)

(*  
    standard (mult_n_1)
      Fill in the proof.
*)


(* To introduce these lemmas about multiplication that are proved in the standard library *)
Check mult_n_Sm.
Check mult_n_O.

Theorem mult_n_1 : forall n : nat,
  n * 1 = n.
Proof.
  intros.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

(******************************)

(*  
    standard (andb_true_elim2)
      Prove the following claim, marking cases (and subcases) with bullets when you use destruct. 
*)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
(*  unfold andb. *)
  intros.
  destruct b, c.
  - reflexivity.
  - rewrite <- H. (* apply H *)
    + reflexivity.
  - reflexivity.
  - rewrite <- H.
    + reflexivity.
Qed.


(******************************)

(*  
    standard (zero_nbeq_plus_1)
        Fill in the proof.
*)

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros. 
  destruct n as [|n']; reflexivity. (* ";" means: apply whatever I'm writing after the ";" on every branch That'll be generated from here *)
Qed.



(******************************)

(*  
    standard (identity_fn_applied_twice)
        Use the tactics you have learned so far to prove the following theorem about boolean functions. 
*)


Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  (* For each case of b, apply H (:= f b = b) twice and verify using reflexivity*)
  destruct b; rewrite -> H; rewrite -> H; reflexivity.
Qed.
  

(******************************)

(*  
    standard (negation_fn_applied_twice)
        Now state and prove a theorem negation_fn_applied_twice similar to the-
        previous one but where the second hypothesis says that the function f-
        has the property that f x = negb x.  
*)

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  (* For each case of b, apply H (:= f b = b) twice and verify using reflexivity*)
  destruct b; rewrite -> H; rewrite -> H; reflexivity.
Qed.
  

(******************************)

(*  
    standard, optional (andb_eq_orb)
        Prove the following theorem.
        (Hint: This one can be a bit tricky, depending on how you approach it.
         You will proprobably need both destruct and rewrite, but destructing everything in sight is not the best way.) 
*)

Theorem andb_eq_orb :
  forall (b c : bool), andb b c = orb b c -> b = c.
Proof.
  destruct b,c.
  intro H.
  reflexivity.
  intro H.
  inversion H.
  intro H.
  inversion H.
  intro H.
  reflexivity.
Qed.


(******************************)

(*  
    standard (binary)
        We can generalize our unary representation of natural numbers to the more- 
        efficient binary representation by treating a binary number as a sequence-
        of constructors A and B (representing 0s and 1s), terminated by a Z.
        For comparison, in the unary representation, a number is a sequence of-
        S constructors terminated by an O.
        For example:
        decimal            binary                  unary
           0                 Z                       O
           1                B Z                     S O
           2              A (B Z)                  S (S O)
           3              B (B Z)                 S (S (S O))
           4            A (A (B Z))              S (S (S (S O)))
           5            B (A (B Z))             S (S (S (S (S O))))
           6            A (B (B Z))            S (S (S (S (S (S O)))))
           7            B (B (B Z))           S (S (S (S (S (S (S O))))))
           8           A (A (A (B Z)))       S (S (S (S (S (S (S (S O)))))))

        Note that the low-order bit is on the left and the high-order bit is on-
        the right -- the opposite of the way binary numbers are usually written.
        This choice makes them easier to manipulate.

        Inductive bin : Type :=
                  | Z
                  | A (n : bin)
                  | B (n : bin).

        Complete the definitions below of an increment function incr for-
        binary numbers, and a function bin_to_nat to convert binary numbers-
        to unary numbers.  
*)



Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

(* If a binary ends (at the rightmost bit) with 0, you just need to change that bit to 1.
   Else, if it ends with 1, you change the 1 to 0 and add a 1 to other paart of the number.
*)
Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B (Z)
  | A m' => B (m')
  | B m' => A (incr m')
  end.

(* When you add a 0 in front of a binary number, you're doubling it (remember the case in base 10)
   And when you add a 1 in front of it, you're just basically adding a 0 in fron of-
  it and increamenting the new number by 1 (which is equal to doubling it and then adding it with 1)
*)
Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | A m' => 2 * bin_to_nat(m')
  | B m' => 2 * bin_to_nat(m') + 1
  end.


Example test_bin_incr1 : (incr (B Z)) = A (B Z).
Proof.
  simpl.
  reflexivity.
Qed.
Example test_bin_incr2 : (incr (A (B Z))) = B (B Z).
Proof.
  simpl.
  reflexivity.
Qed.
Example test_bin_incr3 : (incr (B (B Z))) = A (A (B Z)).
Proof.
  simpl.
  reflexivity.
Qed.
Example test_bin_incr4 : bin_to_nat (A (B Z)) = 2.
Proof.
  simpl.
  reflexivity.
Qed.
Example test_bin_incr5 : bin_to_nat (incr (B Z)) = 1 + bin_to_nat (B Z).
Proof.
  simpl.
  reflexivity.
Qed.
Example test_bin_incr6 : bin_to_nat (incr (incr (B Z))) = 2 + bin_to_nat (B Z).
Proof.
  simpl.
  reflexivity.
Qed.
 
























