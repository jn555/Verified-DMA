# Verified DMA in Rocq/Coq

This project is a small but complete formal model of a Direct Memory Access (DMA) controller, written in [Rocq/Coq](https://rocq-prover.org/). The goal is to show, end-to-end, how you can model hardware behavior and prove its correctness using theorem proving techniques.

**Status:** This project is still in progress.

---

## What It Does

- **Models a memory system** as a pure function `Addr → Data`.
- **Implements a simple DMA** engine that copies one word per clock tick from a source range to a destination range.
- **Captures wiring and update semantics** for components interacting with a board of pins.
- **Proves correctness theorems** about the DMA, such as:
  - Data is faithfully copied from the source to the destination.
  - Memory outside the destination region is preserved.
  - Disjointness conditions guarantee the source region is never overridden.

---

## Why It Matters

DMA is a classic building block in computer systems, but correctness is easy to get wrong when source and destination ranges overlap. Using Rocq/Coq, we can prove definitively that the model behaves exactly as intended under well-defined conditions.

---

## Project Structure

- `wiring.v`  
  Defines minimal components, pins, and per-tick board updates.

- `memory.v`  
  Models memory as pure functions, with read/write and supporting lemmas.

- `dma.v`  
  The DMA controller itself:
  - State record (source, destination, length, memory).
  - `step` and `run` functions (single-tick and multi-tick).
  - Correctness lemmas and theorems under disjointness assumptions.

---

## Example

One of the key theorems:

```coq
Lemma after_k_copies_segment (s0:State) (k:nat) :
  disjoint_range s0.(src) s0.(dst) s0.(len) ->
  k <= s0.(len) ->
  Mem.segment (run k s0).(mem) s0.(dst) k
  = Mem.segment s0.(mem) s0.(src) k.
```

This states that after k steps, the first k words of the destination equal the original source segment, which is exactly the property a DMA should guarantee.

---

## Inspiration
This project was inspired by [Jeremy Rubin’s Verified DSP](https://css.csail.mit.edu/6.888/2015/papers/jrubin.pdf) paper.