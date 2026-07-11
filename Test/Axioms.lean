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

-- Causal-Cut Consumable Authority — the authority frontier, necessity v0
-- (`Crdt.AuthorityFrontier`).

/-- info: 'Crdt.AuthorityFrontier.no_disconnected_double_availability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.no_disconnected_double_availability

/-- info: 'Crdt.AuthorityFrontier.authority_frontier_card_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.authority_frontier_card_le_one

/-- info: 'Crdt.AuthorityFrontier.double_consume_countermodel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.double_consume_countermodel

/-- info: 'Crdt.AuthorityFrontier.copy_frontier_init_card_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.copy_frontier_init_card_two

/-- info: 'Crdt.AuthorityFrontier.ccca_teeth_double_consume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.ccca_teeth_double_consume

/-- info: 'Crdt.AuthorityFrontier.ccca_teeth_both_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.ccca_teeth_both_live

/-- info: 'Crdt.AuthorityFrontier.ccca_edge_only_still_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.ccca_edge_only_still_unsafe

/-- info: 'Crdt.AuthorityFrontier.ccca_safe_world_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.ccca_safe_world_safe

/-- info: 'Crdt.AuthorityFrontier.ccca_safe_world_transfer_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.ccca_safe_world_transfer_live

/--
info: 'Crdt.AuthorityFrontier.ccca_safe_world_no_double_availability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.ccca_safe_world_no_double_availability

-- Sealed-handoff sufficiency (`Crdt.AuthorityFrontier`, third mesh brick).

/-- info: 'Crdt.AuthorityFrontier.sealed_handoff_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.sealed_handoff_safe

/-- info: 'Crdt.AuthorityFrontier.wSafe_sealed_handoff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.wSafe_sealed_handoff

/-- info: 'Crdt.AuthorityFrontier.wEdgeOnly_not_sealed_handoff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.wEdgeOnly_not_sealed_handoff

/-- info: 'Crdt.AuthorityFrontier.wSeq_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.wSeq_safe

/-- info: 'Crdt.AuthorityFrontier.wSeq_not_sealed_handoff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.wSeq_not_sealed_handoff

/-- info: 'Crdt.AuthorityFrontier.gap_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.gap_vacuous

-- Sufficiency lifted to the (generated) abstract system
-- (`Crdt.AuthorityFrontier`, Layer D — fourth mesh brick).

/-- info: 'Crdt.AuthorityFrontier.sufficiency_needs_generation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.sufficiency_needs_generation

/-- info: 'Crdt.AuthorityFrontier.sealed_senders_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.sealed_senders_safe

/-- info: 'Crdt.AuthorityFrontier.copy_not_sealed_senders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.copy_not_sealed_senders

/-- info: 'Crdt.AuthorityFrontier.wSafe_sender_never_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.wSafe_sender_never_live

/-- info: 'Crdt.AuthorityFrontier.seq_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.seq_safe

/-- info: 'Crdt.AuthorityFrontier.seq_both_live_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.seq_both_live_init

/-- info: 'Crdt.AuthorityFrontier.seq_not_sealed_senders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.seq_not_sealed_senders

def main : IO Unit :=
  IO.println "axiom gate passed: all checks pinned by #guard_msgs at compile time"
