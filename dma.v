(* DMA.v
   Abstract, single-channel DMA over pure memory
   
   Copies one element per step.

   Proves correctness under a non-overlap (disjoint ranges) assumption.
*)

From Coq Require Import List Arith Bool Lia.
Import ListNotations.
From VerifiedDMA Require Import memory.
Module Mem := memory.Memory.

Module DMA.

(*
  State is the state of a DMA operation, so how much of the operation is
  complete, and general info about operation (src, dest, etc).

  len is nat, and nat is defined recursively
  i.e.
  Inductive nat :=
  | 0 : nat
  | S : nat -> nat

  1 is S 0
  2 is S (S 0)
  etc.
*)

  Record State := {
    src  : Mem.Addr;
    dst  : Mem.Addr;
    len  : nat;       (* remaining elements to copy *)
    mem  : Mem.Mem
  }.

  (*
    If len = 0, do nothing.
    Else: read mem[src], write it to mem[dst], then bump src, dst, dec len.
  *)
  Definition step (s:State) : State :=
    match s.(len) with
    | 0 => s
    | S _ =>
        let b   := Mem.read s.(mem) s.(src) in
        let mem':= Mem.write s.(mem) s.(dst) b in
        {| src := S s.(src); dst := S s.(dst); len := pred s.(len); mem := mem' |}
    end.

  (*
    Do one step of DMA operation, and calls itself recursively

    Provide n for the number of steps you wanna simulate
  *)
  Fixpoint run (n:nat) (s:State) : State :=
    match n with
    | 0 => s
    | S n' => run n' (step s)
    end.

(*
  Takes 3 inputs
    a: start of first block
    b: start of second block
    n: common length of both blocks

  Checks if the endpoint of a doesnt overlap with start of b
  or if the endpoint of b doesnt overlap with the start of a
*)

Definition disjoint_range (a b n:nat) : Prop :=
  a + n <= b \/ b + n <= a.

(* A simple arithmetic fact: disjoint implies no index in src-range equals an
   index in dst-range. We’ll use this to show source bytes never get clobbered. *)

(*

Pointwise form of two blocks not overlappign

Useful despite us having the range level check between two memory blocks (disjoint_range)
as many lemmas need check for concrete address inequality (i.e. a != x).

To check that one specific address is different than another 
(i.e. index i of mem item a is different than j of mem item b).

Generalized, no element of the src address block equals any element of the dst address block
=
i and j pick particular addresses within the src and dst block, respectively

If the src and dst addresses (nats) are disjoint
then index i of src < n (total length of src)
then index j of dst < n (total length of dst)
then src + i != dst + j

So, if the src and dst ranges are disjoint (which is prereq for this)
then check that the indexed i of src is valid
then check that the indexed j of dst is valid
then check that the addresses plus indexes arent equal

Hdis Hi Hj and Heq are namings you assign to the hypothesis implications
All introduced into context with those names

If you write fewer names than there are arrows, the rest stay in the goal as implications

Since ~x = x -> false
And p -> q = ~p v q

x | ~x v false
1 | 0
0 | 1

(x <> y) is notation for ~ (x = y)
(src + i <> dst + j) is notation for ~ (src + i <> dst + j)
which gets expanded into (src + i = dst + j) -> false 

So, the mapping is:
Hdis : (disjoint_range src dst n)
Hi : (i < n)
Hj : (j < n)
Heq : (src + i = dst + j)

So all these are introduced as assumptions

And what's left is -> false
And that's the new goal

_______
Destruct Hdis as [H | H]
Hdis : (disjoint_range src dst n)

This is case analysis on disjunction

Since disjoint_range is:
    a + n <= b \/ b + n <= a.
It has 2 terms: a \/ b
So H | H

Then there are two branches, one taken for each of the destructed terms

Lia is built in solver to prove this inequality property.

*)
Lemma disjoint_indices_ne (src dst n i j : nat) :
  (disjoint_range src dst n) ->
  (i < n) ->
  (j < n) ->
  (src + i <> dst + j).
Proof.

  intros Hdis Hi Hj Heq. 
  destruct Hdis as [Hleft | Hright];
  lia.
Qed.


End DMA.
