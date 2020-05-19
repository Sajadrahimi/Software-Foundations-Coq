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





















