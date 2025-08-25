(* IO.v
   Tiny signal/trace model for pins on the board
   One sample per pin per tick; if nobody drives a pin this tick, it holds. *)

From Coq Require Import List Arith Bool.
Import ListNotations.

Module IO.

(* --- Pins & Values --- *)

(* Identify pins by number for now. Easy to change later. *)
Definition Pin := nat.

(* Value carried by a pin each tick. Start with bool; swap to bytes/words later. *)
Definition Val := bool.

(* What a pin reads before it has any samples. *)
Definition default : Val := false.

(* --- Traces & Board --- *)

(* Pins history, ordered oldest to newest. *)
Definition Trace := list Val.

(* Lookp table for the whole board: for any pin, give me its trace. *)
Definition Board := Pin -> Trace.

(* --- Helpers on traces/boards --- *)

(* Return the last sample of a trace, or [d] if the trace is empty.
   We reverse to make the last element the head, then pattern match/deconstruct *)
Definition last_with (d:Val) (tr:Trace) : Val :=
  match rev tr with
  | [] => d
  | v :: _ => v
  end.

(* Append one sample to exactly one pin\u2019s trace; other pins are untouched. *)
Definition write_pin (b:Board) (p:Pin) (v:Val) : Board :=
  fun p' =>
    if Nat.eqb p p'
    then b p' ++ [v]
    else b p'.

(* \u201cHold\u201d semantics for a single pin: repeat its last value this tick.
   If the trace is empty, we use [default]. *)
Definition hold_pin (b:Board) (p:Pin) : Board :=
  write_pin b p (last_with default (b p)).

(* A per-tick proposal: for each pin, either drive [Some v] this tick,
   or [None] meaning \u201cI won\u2019t drive it; let it hold\u201d. *)
Definition Update := Pin -> option Val.

(* Apply one tick\u2019s worth of updates to the whole board.
   Every pin grows by exactly one sample:
     - if [upd p = Some v], append [v]
     - otherwise, append the held value (repeat last; [default] if empty) *)
Definition apply_updates (b:Board) (upd:Update) : Board :=
  fun p =>
    b p ++
    [ match upd p with
      | Some v => v
      | None   => last_with default (b p)
      end ].

(* Equality restricted to one pin\u2019s trace. Handy for non-interference lemmas. *)
Definition eq_on_pin (p:Pin) (b1 b2:Board) : Prop :=
  b1 p = b2 p.

End IO.
