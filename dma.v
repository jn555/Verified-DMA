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

(*
  When you copy one element, both src and dst bump by 1 and the 
  remaining length drops by 1. 
  
  Disjointness should still hold for the tail.

  Lemma:
    Input src index a, dst index b, and mutual length m

    S is the successor constructor for a nat m

    Since nats are defined inductively, so get the next number you do (S n), for nat n

    Thus,
    Given starting mem addresses a and b, 
    If a and b are disjoint over range of mutual mem length of m + 1
    (i.e. a + (m + 1) <= b \/ b + (m + 1) <= a, which are two mutually exclusive conditions)

    then after copying/consuming one element, and thus proceeding/shifting to next to consume,
    the remaining length is still disjoint (so you decement m as well from m + 1 as the total
    mem length has to stay consistent).

  Proof:
    Goal: disjoint_range a b (S m) -> disjoint_range (S a) (S b) m.
    1. Unfolding disjoint_range definition
    Goal: a + (S m) <= b \/ b + (S m) <= a
          -> (S a) + m <= (S b) \/ (S b) + m <= (S a).

    2. Introduce the LHS of the implication as an assumption, and decontruct it into LHS and RHS of OR
    Thus, new goal is the RHS

    So, two branches

    Branch 1:
      a + (S m) <= b
      -> (S a) + m <= (S b) \/ (S b) + m <= (S a).

    Branch 2:
      b + (S m) <= a
      -> (S a) + m <= (S b) \/ (S b) + m <= (S a).

    Both branches proven with lia inequality solver.

    Explanation:

    Branch 1:
    a + (S m) <= b 
    = S (a + m) <= b
    = (S a) + m <= b
    by associative property of addition

    and since b <= S b

    = (S a) + m <= (S b)
*)

Lemma disjoint_shift (a b m : nat) :
  disjoint_range a b (S m) ->
  disjoint_range (S a) (S b) m.
Proof.
  unfold disjoint_range; intros [H|H].
  - left;  lia.   (* a+(S m) <= b  ⇒  (S a)+m <= (S b) *)
  - right; lia.   (* b+(S m) <= a  ⇒  (S b)+m <= (S a) *)
Qed.


(*
  Writing outside segment doesnt change it

  Inputting a memory block m
  and an index w you wanna write to
  And a memory chunk a -> a + m

  mem.segment returns the data starting from a to a+n

  Lemma:
    if the write address w is not within the memory chunk a

    then writing to w with data v (which returns a new memory type), and 
    taking mem.segment of segment a (which returns all the data from a->a+n) 
    equals the same list of data as if you didn't do the write to w.

  Proof:
  1. intro Hout.
    introduce LHS of implication as assumption (rather than prev where whole exp was goal)

    Now, new goal is
    (Mem.segment (Mem.write m w v) a n = Mem.segment m a n)

  2. Unfold Mem.segment
  So new goal is:

  (Mem.segment (Mem.write m w v) a n = Mem.segment m a n).

  Whole exp:
  (w < a) ∨ ((a + n) ≤ w )
  → (Mem.segment (Mem.write m w v) a n = Mem.segment m a n).

  (w < a) ∨ ((a + n) ≤ w )
  → [ (map [ (Mem.write m w v) ] (seq a n)) ] = [ map m (seq a n) ].

      * seq is standard library function which constructs list of 
      sequential nat's starting at a (starting address)
      * map applies a function to every element of a list
      * thus, (seq a n) generated list of sucessive nats from a -> n
      and you're applying a memory type to this list
      * since Mem  := Addr → Data, memory (nat (nat)) = data
      * so you're checking equivilance for the list of data elements of both sides

  3. apply List.map_ext_in
  To transform list equality goal into a pointwise goal (i.e. for each point)

  Lemma map_ext_in :
  ∀ (A B : Type) (f g: A → B) l, 
    (∀ a, In a l → f a = g a) → map f l = map g l.

  Pontwise equality of elements -> equality of mapped lists

  So, turns list equality into “for all x ∈ seq a n, the two functions agree”

  4. Adds LHS of goal implication to assumptions, so new goal is just RHS

  Prev goal: forall a0 : Mem.Addr, In a0 (seq a n) -> Mem.write m w v a0 = m a0

  New assumptions: 
  ...
  x : Mem.Addr
  Hx : In x (seq a n)
  New goal: Mem.write m w v a0 = m a0

  5. apply List.in_seq in Hx as [HxL HxR].

  Lemma in_seq len start n :
  In n (seq start len) ↔ start ≤ n < start+len.

  Tells you if n is within (start) → (start+len)

  Lets you convert between in-set relationship to bounds

  So, prev the assumption was: (Mem.Addr x) ∈ (seq a n)
  Which means x is within the address range list for a

  Now, we express that in terms of bounds:
  L (x >= a) && R (x < a + n)

  6. Assert (P) by T creates a subgoat P; if tactic T solves it, then it adds it to hypothesis
  
  Since (w < a) ∨ (a + n ≤ w)
  and a ≤ x
  and x < a + n

  Then:
  Case 1:
  w < a ≤ x

  Thus W ≠ x

  Case 2:
  x < a + n ≤ w

  Thus W ≠ x

  Proven by lia (inequality solver)

  (x <> w) added to hypotheses

  7. Incorperating existing lemma: Mem.write_preserve

  Lemma: writing at address a does not affect reads at any different address x.

  Since:
  write: (m:Mem) (a:Addr) (v:Data) → Mem

  and
  Mem  := Addr -> Data.

  We are trying to prove that writing data v to address w, which returns a memory type
  And then mem: addr -> data (calling that memory function with address x, arbitrary different address)
  Results in the same data as if we didnt write to v

  Which that previous lemma proved
*)
Lemma segment_write_outside (m:Mem.Mem) (a n w:Mem.Addr) (v:Mem.Data) :
  (* w is outside [a, a+n) *)
  (w < a) \/ ((a + n) <= w )
  -> (Mem.segment (Mem.write m w v) a n = Mem.segment m a n).
Proof.
  intro Hout.
  unfold Mem.segment.  (* map m (seq a n) *)
  apply List.map_ext_in. 
  intros x Hx.
  apply List.in_seq in Hx as [HxL HxR].  (* a <= x < a+n *)
  assert (x <> w) by (intros ->; lia).
  now rewrite (Mem.write_preserve m w v x).
Qed.



End DMA.
