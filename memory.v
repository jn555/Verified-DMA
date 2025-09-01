(* 
   Memory.v
   A tiny pure memory model 
   Mem = nat -> Data (using Data := nat for simplicity).
   May swtich data to Z/bytes later.
*)
From Coq Require Import List Arith Bool Lia.
Import ListNotations.

Module Memory.

Definition Addr := nat.
Definition Data := nat.   (* swap to Z/8-bit later; nat keeps proofs light *)
(*
    Entire memory, maps each address to some data
*)
Definition Mem  := Addr -> Data.

(*
    Given a address for that piece of memory, return the data
*)
Definition read  (m:Mem) (a:Addr) : Data := m a.

(*
    For every address in memory, if the address equals that of the 
    inputted one, it sets its data to v (i.e. RHS of implication).
*)

Definition write (m:Mem) (a:Addr) (v:Data) : Mem :=
  fun a' => if Nat.eqb a a' then v else m a'.


(* seq a n = [a; a+1; ...; a+n-1] *)
(* 
    All this does is returns the data for a range starting at
    specified starting address up to n indexes after.

    Given a piece of memory, a starting address, and a number of items:
        1. seq is standard library function which constructs list of 
        sequential nat's starting at a (starting address)
        2. Map applies a function to every element in a list.
        So, here you are doing m num1, m num2, etc. for every element
        of the generated seq list.
        3. Since mem function is defined as Addr -> Data, applying mem 
        to addr returns the associated data. Done for all addresses.
*)
Definition segment (m:Mem) (a n:nat) : list Data :=
  map m (seq a n).

(*
  Lemma: writing at address a does not affect reads at any different address x.

  Intuition:
    - Memory is a pure function Mem := Addr -> Data.
    - write m a v returns a new memory that equals m everywhere except at a.
      So if x <> a, reading at x should give the old value m x.

  Proof outline:
    1) intro Hneq
       Bring the hypothesis Hneq : a <> x into context.

    2) unfold write
       Expand the definition:
         (write m a v) x = if Nat.eqb a x then v else m x

    3) destruct (Nat.eqb a x) eqn:E
       Case-split on the boolean equality test and name it E:
         - Case A: E : Nat.eqb a x = true   (goal: v = m x)
         - Case B: E : Nat.eqb a x = false  (goal: m x = m x)

       The brackets [ ... | ... ] after the semicolon give the scripts for
       Case A and Case B, respectively.

    4) Case A (E = true) contradicts Hneq:
         apply Nat.eqb_eq in E    (* turns E into a propositional equality a = x *)
         subst                     (* replace a by x everywhere *)
         contradiction             (* Hneq became x <> x, impossible *)
       Case B is trivial:
         reflexivity               (* goal is m x = m x *)
*)
Lemma write_preserve (m:Mem) (a:Addr) (v:Data) (x:Addr) :
  a <> x -> (write m a v) x = m x.
Proof.
  intro Hneq. unfold write.
  destruct (Nat.eqb a x) eqn:E; [apply Nat.eqb_eq in E; subst; contradiction|reflexivity].
Qed.


(* Writing at a reads back the written value *)
(*
    Writing to an address then retreiving the value directly
    (through calling mem) returns the correct value

    (write m a v) returns <address->data> function

    Proof:
    1) Unfold write
        if Nat.eqb a a' then v else m a'.

        New goal:
        (fun a; => if Nat.eqb a a' then v else m a') a = v.   

    2) Reduce:
        if Nat.eqb a a then v else m a) = v. 

    3) In Nat.eqb_refl, Nat.eqb a a = true, so v is output

        Then, v = v, which is true.

*)
Lemma write_hit (m:Mem) (a:Addr) (v:Data) :
  (write m a v) a = v.
Proof. 
    unfold write. 
    now rewrite Nat.eqb_refl. 
Qed.

(*
  segment (m:Mem) (a n:nat) : list Data
  Given a piece of mem, a starting address, and num of items,
  returns list of respective data elements
  
  The lemma is stating that the length of this list is the same as the number of items

  Proof:
    1) Unfold segment with the format of its output
       New goal: length (map m (seq a n).) = n
    2) From standard library
        map_length
      : forall (A B : Type) (f : A -> B) (l : list A), length (map f l) = length l

      i.e. length (map f l) = length l

      Thus, since segment := map m (seq a n), length (map m (seq a n)) = length ((seq a n))
      
      Thus, new goal is length ((seq a n)) = n

    3) From standard library
        seq_length
        : forall len start : nat, length (seq start len) = len
      
      Thus, new goal is n = n
      
    4) n = n, reflexivity
*)
Lemma segment_length (m:Mem) a n :
  length (segment m a n) = n.
Proof.
  unfold segment.
  rewrite List.map_length.
  rewrite List.seq_length.
  reflexivity.
Qed.

End Memory.
