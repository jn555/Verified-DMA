(* 
  IO.v
  Small pin and trace model
  
  One sample per pin per tick; if nobody drives a pin this tick, it holds. 
  
  *)

From Coq Require Import List Arith Bool.
Import ListNotations.

Module IO.

(* 
  Identify pins by number for now. 
*)
Definition Pin := nat.

(* 
  Value carried by a pin each tick.
  Using booleans currently, may change
 *)

Definition Val := bool.

(* 
  What a pin reads before it has any samples. 
*)
Definition default : Val := false.


(* 
  Pins history, ordered oldest to newest. 
*)
Definition Trace := list Val.

(* 
  Lookp table for the whole board: for any pin, give me its trace. 
*)
Definition Board := Pin -> Trace.


(* 
  Return the last sample of a trace, or [d] if the trace is empty.
  We reverse to make the last element the head, then pattern match/deconstruct 
*)
Definition last_with (d:Val) (tr:Trace) : Val :=
  match rev tr with
  | [] => d
  | v :: _ => v
  end.

Check last_with.

(* Append one sample to exactly one pin\u2019s trace; other pins are untouched. *)
Definition write_pin (b:Board) (p:Pin) (v:Val) : Board :=
  fun p' =>
    if Nat.eqb p p'
    then b p' ++ [v]
    else b p'.

(* 
  For a single pin: repeat its last value this tick.
  If the trace is empty, we use [default]. 
*)
Definition hold_pin (b:Board) (p:Pin) : Board :=
  write_pin b p (last_with default (b p)).

(* 
  Functions in coq are total, this means they must be defined
   for every antecedent of that type; so, you must be able to call
   it on every pin. 
   
   Thus, it either returns some or none, depending
   on if its being updated in that tick. 
  *)
Definition Update := Pin -> option Val.

(* 
  Apply one tick’s worth of updates:
   For each pin p, append exactly one new sample:
     - if upd p = Some v, append v (component drives p this tick)
     - if upd p = None, append the held value (repeat last; default if empty) 

  given board and update type (mapping every pin to new value
  for that tick, some or none), output a new board with those changes

  since the whole thing has a board type and board maps pin->trace,
  coq infers p is of type pin, and that the consequent must produce a trace.

  b p is function application by juxtaposition, b is applied to p
  and since board is pin -> trace, board->pin->trace (think of it as curried function)

  ++ is concatenation, so to the trace you're adding the result of the
  match expression

  if Val is none, then get the latest value in the trace and append
  that value again to the trace, so for next tick same value repeated
*)
Definition apply_updates (b:Board) (upd:Update) : Board :=
  fun (p : Pin) =>
    (b p : Trace) ++
    [ match (upd p : option Val) with
      | Some v => (v : Val)
      | None   => (last_with default (b p) : Val)
      end ].

(*
  Curried function mapping 
  pin -> board -> board -> prop

  Sees if the same pin on two boards has same value
*)
Definition eq_on_pin (p:Pin) (b1 b2:Board) : Prop :=
  b1 p = b2 p.

End IO.
