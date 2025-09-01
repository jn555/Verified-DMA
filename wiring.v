(* Wiring.v

Defines minimal component type and mechanism for per-tick updates
  *)

From Coq Require Import List Bool Arith.
Import ListNotations.
From VerifiedDMA Require Import io.
Module IO := io.IO.

Module W.

(* An empty board (all pins have empty traces). *)
Definition empty_board : IO.Board := fun _ => ([] : IO.Trace).

(* 
  One component: declares a set of pins it may write, and a step function
  that proposes an Update given the current board. 

  For each component have a field definining what it MAY drive 
  (i.e. what it's wired to), and a dynamic field for what it is
  driving on that tick.
*)

Record Comp := {
  writes : list IO.Pin;
  step   : IO.Board -> IO.Update
}.

(* 
  Helper: “drive pin p with value v this tick” 
   
  First arg, the board, is ignored, hence _

  The result is an IO.update type, i.e. IO.Pin -> option IO.Value

  For fixed pin p;
  if the queried pin equals the specified pin, through 
  nat.eqb (i.e. equality operation for natural nums),
  then set the outputted consequent, which is of io.update 
  type to p' => (inputted v), or if not then set such the
  to none.

  Basically, given a pin and a value, creates an update type for you, for that board.
  So, you dont have to manually construct the update type for the board.
*)
Definition drive_pin (p : IO.Pin) (v : IO.Val) : IO.Board -> IO.Update :=
  fun _ p' => if Nat.eqb p p' then Some v else None.

Check drive_pin.

(* 
  Merge components’ proposed updates: leftmost writer wins.

  Output type is IO.update, which is pin -> option value, defined for all pins

  So, the body is a function which returns a io.update type

  So, for each pin (LHS), its iterating through the cs list, taking
  the first component of the list and accumulating

  For fixed pin, you want one result each tick.
  so you have to break tie of multiple drivers
  we are taking leftmost as winner

  So, for each pin, we are trying to get one value (or none)

  We iterate through the pins on the board;
  for each pin, we iterate through all the components and see if 
  any are driving it

  If we already found some vaue acc, keep it. if not, step to next component
  and see if it drives that pin on the board, and continue doing this.
  the initial value for acc is none
*)
Definition merge_updates (cs : list Comp) (b : IO.Board) : IO.Update :=
  fun (p : IO.Pin) =>
    fold_left
      (fun (acc : option IO.Val) (c : Comp) =>
         match acc with
         | Some _ => acc
         | None   => c.(step) b p
         end)
      (cs : list Comp)
      (None : option IO.Val).

(* 
  Apply one tick
  Inputs all the components and board and:
    1. Runs merge_updates to get the precedent-adjusted update type for that tick (mapping of each pin to an optional val).
    2. Applies those respective updates to the board by calling IO.apply_updates
 *)
Definition run_once (cs : list Comp) (b : IO.Board) : IO.Board :=
  IO.apply_updates b (merge_updates cs b).

(* 
  Apply n ticks

  Inputs number of ticks, list of components, and the board

  Since nat is defined recursively in coq, i.e.
    Inductive nat :=
    | 0 : nat
    | S : nat -> nat

    When you match with a nonzero, it gets matches with s n', for some n'
    Thus, for example, 8 = S 7, and then it calls run with:
    (7, cs (same component list), board after running one tick) 
    And it repeats this till n = 0, the base case
 *)

Fixpoint run (n : nat) (cs : list Comp) (b : IO.Board) : IO.Board :=
  match n with
  | 0 => b
  | S n' => run n' cs (run_once cs b)
  end.

(* Basic examples *)

(* Defining example component, which drives to one pin (0 and 1 respectively)
a true value.
*)
Definition c0 : Comp := {| writes := [0]; step := drive_pin 0 true |}.
Definition c1 : Comp := {| writes := [1]; step := drive_pin 1 true |}.

(* 
  Proof to ensure that works
   Runs 1 tick for the components list c0 and c1, defined above
   which drive to two nonconflicting pins.

   Run returns an IO.board type, which maps all pins to a trace
   IO.board = pin -> trace
   
   So, you have the (oututted board) (pin) which returns the trace
   And you're ensuring it equals just 1 value, true
  
After one tick, pin 0 and pin 1 have [true]; any other pin holds default. *)
Example run_one_tick_pin0 :
  (run 1 [c0; c1] empty_board) 0 = [true].
Proof. reflexivity. Qed.

Example run_one_tick_pin2_holds_default :
  (run 1 [c0; c1] empty_board) 2 = [IO.default].
Proof. reflexivity. Qed.

(* After two ticks of c0, pin 0 shows two samples [true; true]. *)
Example run_two_ticks_pin0 :
  (run 2 [c0] empty_board) 0 = [true; true].
Proof. reflexivity. Qed.

End W.
