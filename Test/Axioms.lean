/-
Copyright (c) 2026 crdt-lean contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: crdt-lean contributors
-/
import Crdt

/-!
# Axiom footprint gate

Every headline theorem below is pinned to the clean baseline
`{propext, Classical.choice, Quot.sound}` (or fewer) via `#guard_msgs`, which
fails elaboration on ANY drift — a new axiom, `sorry` (`sorryAx`), or
`native_decide` (`Lean.ofReduceBool` / `Lean.trustCompiler`).

This module is a `defaultTarget`, so a plain `lake build` elaborates it and the
gate cannot silently fail to run. Scope: the CvRDT merge algebra core and the
G-Counter convergence headlines. Extending the gate to the OR-Set / Sequence
modules is a follow-up.
-/

-- Merge algebra core (`Crdt.Defs`).

/-- info: 'Crdt.merge_comm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Crdt.merge_comm

/-- info: 'Crdt.merge_assoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Crdt.merge_assoc

/-- info: 'Crdt.merge_idem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Crdt.merge_idem

/-- info: 'Crdt.merge_bot' depends on axioms: [propext] -/
#guard_msgs in #print axioms Crdt.merge_bot

/-- info: 'Crdt.le_merge_left' does not depend on any axioms -/
#guard_msgs in #print axioms Crdt.le_merge_left

/-- info: 'Crdt.le_merge_right' does not depend on any axioms -/
#guard_msgs in #print axioms Crdt.le_merge_right

/-- info: 'Crdt.merge_least' does not depend on any axioms -/
#guard_msgs in #print axioms Crdt.merge_least

-- G-Counter convergence headlines (`Crdt.Instances`).

/-- info: 'Crdt.gcounter_merge_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.gcounter_merge_apply

/-- info: 'Crdt.gcounter_strong_eventual_consistency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.gcounter_strong_eventual_consistency

/-- info: 'Crdt.gcounter_eventual_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.gcounter_eventual_agreement

def main : IO Unit :=
  IO.println "axiom gate passed: all checks pinned by #guard_msgs at compile time"
