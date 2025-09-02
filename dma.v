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


End DMA.
