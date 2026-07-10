/-
Copyright (c) 2026 crdt-lean contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: crdt-lean contributors
-/
import Mathlib

set_option linter.unusedSectionVars false

/-!
# Causal-Cut Consumable Authority (CCCA) — the authority frontier, necessity v0

A single-use right ("authority") whose bytes replicate freely cannot be
simultaneously LIVE in two disconnected failure domains — unless the system
is willing to double-spend it. Formally, necessity only: **operational
safety (at most one completed consume, judged on receipts alone) plus the
asynchronous consume-diamond implies the live authority frontier has
cardinality ≤ 1** at every reachable configuration whose domains are
pairwise disconnected. Plus a **checked counterexample**: copyable bytes at
two domains, no coordination — both consume, the receipt union carries two
completed consumes, at-most-once is violated.

## The one rule (anti-tautology discipline)

`live` and `frontier` are **derived observers** over freely-replicated
monotone state — copyable bytes plus grow-only receipts — never primitives:

* `Safe` mentions ONLY completed receipts (`receipts`, a `Finset` that only
  grows along steps);
* `live c d` means only that `d` can take a possible LOCAL consume step
  given what has been delivered to it;
* the bridge between them is the operational amalgamation lemma
  (`no_disconnected_double_availability`): two disconnected live domains
  can BOTH fire — `step_live`, then `frozen_live` (a disconnected step
  cannot revoke remote enablement: the asynchrony square), then `step_live`
  again — and the two receipts land, contradicting safety.

There is no owner field, no uniqueness axiom, and no handoff in the
definition of enablement. Concurrent enablement is *not* a contradiction by
definition — the unsafe model below realizes it (and pays for it).

## Named assumptions (each law is one field, so every apparent escape
   traces to exactly one name)

* `step_live` — locally enabled steps can fire (no hidden global lock);
* `step_reachable` — reachability is closed under steps;
* `receipts_step` — a consume step completes: the stepping domain's receipt
  is recorded and receipts only grow;
* `frozen_live` — LOCALITY: a step in a disconnected domain cannot revoke
  another domain's enablement (the async square of the consume-diamond).

Escape hatches, each breaking exactly one named assumption:
* **quorum consensus** — majority quorums intersect, so two
  quorum-satisfying domains are never `disconnected`;
* **epoch / lease expiry** — an external clock edge revoking remote
  enablement violates `frozen_live` (it is an oracle communication);
* **randomized consume** — per-outcome only; the diamond survives, safety
  becomes probabilistic, outside `Safe`'s certainty claim;
* **delayed receipts / reconciliation** — detection, not prevention: `Safe`
  itself fails at the offending cut; the frontier claim is untouched;
* **signatures** — authenticate the bytes but do not allocate the one-shot
  right: `live` has no unforgeability input and the bytes stay copyable.

## Intended interpretation (SealV2, mapping only — the theorem lives here)

Approval bytes → the copyable replicated state; completed consume receipt →
a successful `validateAndConsumeWithStore` write of the nonce into a
domain's replay store; failure domain → a disconnected replica of that
store; `Safe` → at-most-once nonce spend across domains. The concrete
refinement proof is future work, deliberately not claimed here.

## Honest non-claims

Does NOT prove: crash recovery or durability; cryptographic authenticity or
unforgeability (bytes here are abstract and copyable — this models
replication, not forgery-resistance); Byzantine safety; correctness of any
clock, lease, quorum, or epoch scheme; conformance of the deployed SealV2
implementation; liveness during partitions; SUFFICIENCY of any escrow or
handoff protocol; and no novelty beyond invariant confluence / escrow CRDTs
is claimed — this necessity direction is close to a corollary of Bailis
et al.'s invariant confluence (arXiv:1402.2237) and bounded-counter escrow
(arXiv:1503.09052); it is honest repo infrastructure and the mesh spine,
not new distributed-systems theory.

**Unproved conjecture (recorded, deliberately NOT formalized here — no
axiom, no placeholder declaration): the handoff-or-gap normal form.** Every
safe transfer of live authority between disconnected domains factors
through either a causal handoff edge whose past seals the sender's consume
potential, or a cut where the frontier is empty. The finite probe evidence
below (`ccca_edge_only_still_unsafe` vs `ccca_safe_world_*`) is consistent
with it; the general characterization is the next brick.
-/

namespace Crdt.AuthorityFrontier

/-! ## Layer A — the abstract consume system and the theorem -/

/-- A replicated single-use-consume system over failure domains `D`. All
laws are named fields; see the module docstring's escape-hatch table. -/
structure AuthoritySystem (D : Type) [DecidableEq D] where
  /-- Global configurations (the model's cuts). -/
  Config : Type
  /-- Reachable configurations. -/
  reachable : Config → Prop
  /-- `step c d c'`: domain `d` performs its local consume. -/
  step : Config → D → Config → Prop
  /-- Completed consume receipts — grow-only, the ONLY input to safety. -/
  receipts : Config → Finset D
  /-- Derived local enablement: `d` can take a possible local consume step. -/
  live : Config → D → Prop
  /-- `d₁` and `d₂` share no communication at `c`. -/
  disconnected : Config → D → D → Prop
  /-- Locally enabled steps can fire. -/
  step_live : ∀ c d, live c d → ∃ c', step c d c'
  /-- Reachability is closed under steps. -/
  step_reachable : ∀ c d c', reachable c → step c d c' → reachable c'
  /-- A consume completes: the receipt is recorded, receipts only grow. -/
  receipts_step : ∀ c d c', step c d c' → receipts c' = insert d (receipts c)
  /-- LOCALITY (the async square): a step in a disconnected domain cannot
  revoke another domain's enablement. -/
  frozen_live : ∀ c d₁ d₂ c₁, disconnected c d₁ d₂ → step c d₁ c₁ →
    live c d₂ → live c₁ d₂

variable {D : Type} [DecidableEq D]

/-- Operational safety: at most one completed consume, judged on receipts
alone, at every reachable configuration. -/
def Safe (S : AuthoritySystem D) : Prop :=
  ∀ c, S.reachable c → (S.receipts c).card ≤ 1

/-- The live authority frontier — a DERIVED observer: the set of domains
whose local view licenses a consume step. -/
noncomputable def frontier [Fintype D] (S : AuthoritySystem D) (c : S.Config) :
    Finset D :=
  letI := Classical.decPred (S.live c)
  Finset.univ.filter (S.live c)

/-- **The amalgamation lemma (the content).** In a safe system, two
DISTINCT, DISCONNECTED domains are never both live at a reachable
configuration: if they were, `step_live` fires the first consume,
`frozen_live` carries the second domain's enablement across the
disconnected step, `step_live` fires the second consume, and
`receipts_step` (twice) lands two receipts — contradicting safety. -/
theorem no_disconnected_double_availability (S : AuthoritySystem D)
    (hsafe : Safe S) {c : S.Config} (hreach : S.reachable c) {d₁ d₂ : D}
    (hne : d₁ ≠ d₂) (hdis : S.disconnected c d₁ d₂) :
    ¬(S.live c d₁ ∧ S.live c d₂) := by
  rintro ⟨h1, h2⟩
  obtain ⟨c₁, hs1⟩ := S.step_live c d₁ h1
  have hr1 : S.reachable c₁ := S.step_reachable c d₁ c₁ hreach hs1
  have h2' : S.live c₁ d₂ := S.frozen_live c d₁ d₂ c₁ hdis hs1 h2
  obtain ⟨c₂, hs2⟩ := S.step_live c₁ d₂ h2'
  have hr2 : S.reachable c₂ := S.step_reachable c₁ d₂ c₂ hr1 hs2
  have hrec : S.receipts c₂ = insert d₂ (insert d₁ (S.receipts c)) := by
    rw [S.receipts_step c₁ d₂ c₂ hs2, S.receipts_step c d₁ c₁ hs1]
  have hsub : ({d₁, d₂} : Finset D) ⊆ S.receipts c₂ := by
    rw [hrec]
    intro x hx
    rcases Finset.mem_insert.mp hx with hx1 | hx2
    · subst hx1
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · have hx2' := Finset.mem_singleton.mp hx2
      subst hx2'
      exact Finset.mem_insert_self _ _
  have h2le : 2 ≤ (S.receipts c₂).card := by
    calc 2 = ({d₁, d₂} : Finset D).card := (Finset.card_pair hne).symm
      _ ≤ (S.receipts c₂).card := Finset.card_le_card hsub
  have := hsafe c₂ hr2
  omega

/-- **CCCA necessity: the live authority frontier has cardinality ≤ 1.**
At any reachable configuration whose domains are pairwise disconnected, a
safe system's frontier holds at most one domain. -/
theorem authority_frontier_card_le_one [Fintype D] (S : AuthoritySystem D)
    (hsafe : Safe S) {c : S.Config} (hreach : S.reachable c)
    (hdis : ∀ d₁ d₂ : D, d₁ ≠ d₂ → S.disconnected c d₁ d₂) :
    (frontier S c).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra hab
  have hla : S.live c a := by
    have := ha; unfold frontier at this
    exact (Finset.mem_filter.mp this).2
  have hlb : S.live c b := by
    have := hb; unfold frontier at this
    exact (Finset.mem_filter.mp this).2
  exact no_disconnected_double_availability S hsafe hreach hab (hdis a b hab)
    ⟨hla, hlb⟩

/-! ## Layer B — the CopyModel: copyable bytes, no coordination

The teeth of the model, and the checked counterexample. Two domains
(`Bool`: `true` = L, `false` = R), each holding a copy of the approval
bytes from the start (copyability = there is NO possession precondition).
A configuration is the pair of per-domain consume receipts. `live` reads
ONLY the domain's own local component — its delivered view; the domains
never communicate, so any two DISTINCT domains are disconnected. -/

/-- Configurations: (L's receipt flag, R's receipt flag). -/
abbrev CopyConfig := Bool × Bool

/-- Local receipt component of a domain — all `live` ever reads. -/
def copyOwn (c : CopyConfig) (d : Bool) : Bool := if d then c.1 else c.2

/-- Reachability from the empty-receipt initial configuration. -/
inductive CopyReach : CopyConfig → Prop
  | init : CopyReach (false, false)
  | stepL {b : Bool} : CopyReach (false, b) → CopyReach (true, b)
  | stepR {a : Bool} : CopyReach (a, false) → CopyReach (a, true)

/-- The uncoordinated copy system. Every law is PROVED (nothing assumed). -/
def CopySystem : AuthoritySystem Bool where
  Config := CopyConfig
  reachable := CopyReach
  step c d c' := copyOwn c d = false ∧
    c' = (if d then (true, c.2) else (c.1, true))
  receipts c :=
    (if c.1 then {true} else ∅) ∪ (if c.2 then {false} else ∅)
  live c d := copyOwn c d = false
  disconnected _ d₁ d₂ := d₁ ≠ d₂
  step_live c d h := ⟨if d then (true, c.2) else (c.1, true), h, rfl⟩
  step_reachable c d c' hr hs := by
    obtain ⟨hlive, rfl⟩ := hs
    obtain ⟨a, b⟩ := c
    cases d with
    | true =>
        have ha : a = false := by simpa [copyOwn] using hlive
        subst ha
        exact CopyReach.stepL hr
    | false =>
        have hb : b = false := by simpa [copyOwn] using hlive
        subst hb
        exact CopyReach.stepR hr
  receipts_step c d c' hs := by
    obtain ⟨hlive, rfl⟩ := hs
    obtain ⟨a, b⟩ := c
    cases d with
    | true =>
        have ha : a = false := by simpa [copyOwn] using hlive
        subst ha
        cases b <;> decide
    | false =>
        have hb : b = false := by simpa [copyOwn] using hlive
        subst hb
        cases a <;> decide
  frozen_live c d₁ d₂ c₁ hne hs h := by
    obtain ⟨hlive, rfl⟩ := hs
    obtain ⟨a, b⟩ := c
    cases d₁ <;> cases d₂ <;> first
      | exact absurd rfl hne
      | simpa [copyOwn] using h

/-- **The checked double-consume counterexample.** Copyable bytes, two
disconnected domains, both locally live at the start; both consumes fire;
the receipt union carries TWO completed consumes; at-most-once is violated
— the system is not `Safe`, and its initial frontier holds both domains. -/
theorem double_consume_countermodel :
    CopySystem.reachable (true, true) ∧
    CopySystem.receipts (true, true) = {true, false} ∧
    (CopySystem.receipts (true, true)).card = 2 ∧
    ¬ Safe CopySystem ∧
    CopySystem.live (false, false) true ∧
    CopySystem.live (false, false) false ∧
    CopySystem.disconnected (false, false) true false := by
  refine ⟨CopyReach.stepR (CopyReach.stepL CopyReach.init), by decide, by decide,
    ?_, rfl, rfl, fun h => nomatch h⟩
  intro hsafe
  have := hsafe (true, true) (CopyReach.stepR (CopyReach.stepL CopyReach.init))
  revert this
  decide

/-- The countermodel's initial frontier really is BOTH domains (card 2):
concurrent enablement is realizable, not a contradiction by definition —
the anti-tautology witness. -/
theorem copy_frontier_init_card_two :
    (frontier CopySystem (false, false)).card = 2 := by
  classical
  have huniv : frontier CopySystem (false, false) = Finset.univ := by
    unfold frontier
    apply Finset.filter_true_of_mem
    intro d _
    cases d <;> rfl
  rw [huniv]
  simp

/-! ## Layer C — finite causal-cut probe worlds (STEP-0 evidence, landed)

Six events over two domains — `0` enableL · `1` disableL · `2` consumeL ·
`3` enableR · `4` disableR · `5` consumeR — with an explicit strict causal
order per world. Cuts are down-closed event sets; an event's firing
conditions are judged over ITS OWN causal past (what its domain had seen);
`cutLive` is the derived possible-local-step observer. All checks are
kernel-`decide`d (no `native_decide`). Probe verdicts:

* `wUnsafe` (no coordination): double-consume expressible (TEETH) and a
  both-live cut exists;
* `wEdgeOnly` (disable→enable causal edge, sender potential UNSEALED):
  STILL unsafe — the edge alone is insufficient;
* `wSafe` (edge AND the disable seals the sender's consume potential):
  safe, the receiver becomes genuinely live (the transfer works), and no
  cut has both domains live. -/

/-- Probe events. -/
abbrev PE := Fin 6

/-- `true` = the L domain. -/
def peDomL (e : PE) : Bool := e.val < 3

def peEnable (e : PE) : Bool := e.val = 0 || e.val = 3
def peDisable (e : PE) : Bool := e.val = 1 || e.val = 4
def peConsume (e : PE) : Bool := e.val = 2 || e.val = 5

/-- A probe world: an explicit strict causal order on the six events. -/
structure CutWorld where
  lt : PE → PE → Bool

/-- Irreflexive and transitive — checked per world by `decide`. -/
abbrev CutWorld.strict (w : CutWorld) : Prop :=
  (∀ e, w.lt e e = false) ∧
  (∀ a b c, w.lt a b = true → w.lt b c = true → w.lt a c = true)

/-- The world-fixed causal past of an event. -/
abbrev CutWorld.past (w : CutWorld) (e : PE) : Finset PE :=
  Finset.univ.filter (fun f => w.lt f e)

/-- Down-closed cuts: the reachable observations. -/
abbrev CutWorld.closedCut (w : CutWorld) (C : Finset PE) : Prop :=
  ∀ e ∈ C, ∀ f, w.lt f e = true → f ∈ C

/-- Firing conditions of an event over its OWN causal past (its domain's
delivered view at the moment it fired): an enable for the domain, no
disable for the domain, no consume receipt anywhere in view. Derived —
reads only the world order. -/
abbrev CutWorld.fires (w : CutWorld) (e : PE) : Prop :=
  (∃ g ∈ w.past e, peEnable g = true ∧ peDomL g = peDomL e) ∧
  (∀ g ∈ w.past e, ¬(peDisable g = true ∧ peDomL g = peDomL e)) ∧
  (∀ g ∈ w.past e, peConsume g = false)

/-- A cut is valid when every consume it contains fired legitimately. -/
abbrev CutWorld.validCut (w : CutWorld) (C : Finset PE) : Prop :=
  ∀ e ∈ C, peConsume e = true → w.fires e

/-- Derived local enablement at a cut: a fresh consume potential of the
domain whose causal prerequisites are all delivered and whose firing
conditions hold. No owner, no handoff primitive. -/
abbrev CutWorld.cutLive (w : CutWorld) (d : Bool) (C : Finset PE) : Prop :=
  ∃ e : PE, peConsume e = true ∧ peDomL e = d ∧ e ∉ C ∧ w.past e ⊆ C ∧ w.fires e

/-- Completed consume receipts of a cut — grow-only under `⊆`. -/
abbrev CutWorld.cutReceipts (_w : CutWorld) (C : Finset PE) : Finset PE :=
  C.filter (fun e => peConsume e = true)

-- Shallow decidability instances (combined queries otherwise explode
-- instance synthesis).
instance (w : CutWorld) : DecidablePred w.closedCut := fun _ => inferInstance
instance (w : CutWorld) (e : PE) : Decidable (w.fires e) := inferInstance
instance (w : CutWorld) : DecidablePred w.validCut := fun _ => inferInstance
instance (w : CutWorld) (d : Bool) : DecidablePred (w.cutLive d) := fun _ =>
  inferInstance

/-- No coordination: enables precede their domain's disable and consume;
no cross-domain edges at all. -/
def wUnsafe : CutWorld where
  lt a b := (a.val = 0 && b.val = 1) || (a.val = 0 && b.val = 2)
    || (a.val = 3 && b.val = 4) || (a.val = 3 && b.val = 5)

/-- The disable→enable handoff edge is present, but the sender's consume
potential is NOT sealed by the disable. -/
def wEdgeOnly : CutWorld where
  lt a b := (a.val = 0 && (b.val = 1 || b.val = 2 || b.val = 3 || b.val = 4 || b.val = 5))
    || (a.val = 1 && (b.val = 3 || b.val = 4 || b.val = 5))
    || (a.val = 3 && (b.val = 4 || b.val = 5))

/-- The handoff edge AND the disable seals the sender's consume potential
(the disable is in the potential's causal past). -/
def wSafe : CutWorld where
  lt a b := (a.val = 0 && (b.val = 1 || b.val = 2 || b.val = 3 || b.val = 4 || b.val = 5))
    || (a.val = 1 && (b.val = 2 || b.val = 3 || b.val = 4 || b.val = 5))
    || (a.val = 3 && (b.val = 4 || b.val = 5))

theorem wUnsafe_strict : wUnsafe.strict := by decide
theorem wEdgeOnly_strict : wEdgeOnly.strict := by decide
theorem wSafe_strict : wSafe.strict := by decide

/-- TEETH: in the uncoordinated world a valid, down-closed cut with TWO
completed consumes exists — the enumerator expresses double-consume. -/
theorem ccca_teeth_double_consume :
    ∃ C : Finset PE, wUnsafe.closedCut C ∧ wUnsafe.validCut C ∧
      (wUnsafe.cutReceipts C).card = 2 := by decide

/-- And concurrent enablement is realizable: a cut with BOTH domains live. -/
theorem ccca_teeth_both_live :
    ∃ C : Finset PE, wUnsafe.closedCut C ∧ wUnsafe.validCut C ∧
      wUnsafe.cutLive true C ∧ wUnsafe.cutLive false C := by decide

/-- Query (a), the sharp half: the handoff EDGE ALONE is insufficient —
with the sender's potential unsealed, double-consume is still expressible. -/
theorem ccca_edge_only_still_unsafe :
    ∃ C : Finset PE, wEdgeOnly.closedCut C ∧ wEdgeOnly.validCut C ∧
      (wEdgeOnly.cutReceipts C).card = 2 := by decide

/-- Query (a), the safe half: with the edge and the seal, every valid
down-closed cut carries at most one completed consume. -/
theorem ccca_safe_world_safe :
    ∀ C : Finset PE, wSafe.closedCut C → wSafe.validCut C →
      (wSafe.cutReceipts C).card ≤ 1 := by decide

/-- …and the transfer is genuine: the receiving domain becomes live. -/
theorem ccca_safe_world_transfer_live :
    ∃ C : Finset PE, wSafe.closedCut C ∧ wSafe.validCut C ∧
      wSafe.cutLive false C := by decide

/-- Query (b): no valid down-closed cut of the safe world has BOTH domains
live — UNSAT for the operational reason (the seal), not by definition. -/
theorem ccca_safe_world_no_double_availability :
    ¬ ∃ C : Finset PE, wSafe.closedCut C ∧ wSafe.validCut C ∧
      wSafe.cutLive true C ∧ wSafe.cutLive false C := by decide

end Crdt.AuthorityFrontier
