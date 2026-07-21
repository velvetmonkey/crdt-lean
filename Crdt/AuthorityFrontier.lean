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

/-! ## Sealed-handoff SUFFICIENCY (the third mesh brick)

The sufficiency half of the recorded handoff conjecture, discharged:
**a sealed-handoff world is Safe** — every valid closed cut carries at most
one completed consume (`sealed_handoff_safe`, a general `CutWorld` theorem
with a structural proof; `decide` is used only for finite witnesses).

**The seal is ONE causal edge.** Diffing `wEdgeOnly` (unsafe) against
`wSafe` (safe), the only difference is `lt disableL consumeL`: the disable
sits in the causal past of the sender's OWN consume, tripping `fires`'
no-same-domain-disable clause. `SealedHandoff` states exactly that, as a
PURE causal-order predicate over `w.lt` + `peDisable`/`peConsume`/`peDomL`
— it mentions no receipts, no `Safe`, no cardinality, and none of the
necessity theorems (the non-circularity kill line). Its discriminating
fact against `wEdgeOnly` is the order bit `wEdgeOnly.lt 1 2 = false`
(`wEdgeOnly_no_seal_edge`), decided independently of any double-consume
outcome.

**Vacuity discharge (Codex's caveat):** the event vocabulary is fixed —
every `CutWorld` carries both consume events (2 and 5) — so
`SealedHandoff`'s universal ranges over exactly one consume potential per
domain and is never vacuously satisfied; no transfer-classification,
origin, or coverage clauses are needed.

**Why there is no biconditional (the tautology trap, and a discovery):**
the naive gap disjunct "∃ a cut with an empty frontier" is VACUOUSLY true —
at `C = ∅` nobody is live, in every world (`gap_vacuous`), so
`Safe ⟺ handoff ∨ gap` would collapse to `Safe ⟺ True`. Worse, the probe
found a THIRD safe shape: **causal consume-sequencing** (`wSeq`) — the
sender's consume sits in the receiver's causal past (`wSeq.lt 2 5 = true`),
so `fires`' no-consume-in-view clause kills the receiver's potential; the
world is Safe (`wSeq_safe`) with NO sealed handoff
(`wSeq_not_sealed_handoff`) and a genuinely live sender
(`wSeq_sender_live`). The two-disjunct normal form recorded by the v0
conjecture above is therefore INCOMPLETE as stated: any future
characterization must account for at least {sealed handoff, genuine gap,
consume-sequencing}, with "gap" needing a sharper definition than
empty-frontier-somewhere. The conjecture text above is kept verbatim as the
historical record; this paragraph is the refinement.

**Honest scope:** sufficiency only — this does NOT claim the sealed
handoff is the unique safe shape (`wSeq` refutes exactly that), and it is
proven over the finite `CutWorld` probe model, not the abstract
`AuthoritySystem` (which has no causal order to state the pattern over —
lifting sufficiency to an abstract causal setting is a later brick). The
landed novelty disclaimer applies unchanged. -/

/-- The sealed-handoff pattern, as PURE causal order: some domain (the
sender) has every one of its consume potentials sealed — a same-domain
disable in the potential's own causal past. Reads only `w.lt` and the
event vocabulary; no receipts, no safety, no cardinality. -/
abbrev CutWorld.SealedHandoff (w : CutWorld) : Prop :=
  ∃ d : Bool, ∀ e : PE, peConsume e = true → peDomL e = d →
    ∃ g : PE, peDisable g = true ∧ peDomL g = d ∧ w.lt g e = true

/-- A sealed consume can never fire: the sealing disable sits in its causal
past, contradicting `fires`' no-same-domain-disable clause. -/
theorem seal_blocks_fires (w : CutWorld) (e g : PE)
    (hg : peDisable g = true) (hdom : peDomL g = peDomL e)
    (hlt : w.lt g e = true) : ¬ w.fires e := by
  intro hf
  exact hf.2.1 g (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hlt⟩) ⟨hg, hdom⟩

/-- **Sealed-handoff sufficiency (the builder's guarantee).** In any world
whose sender domain is sealed, every valid closed cut carries at most one
completed consume: the sealed domain's consumes can never fire
(`seal_blocks_fires`), so a valid cut's receipts live inside the other
domain's single consume potential. Structural proof — no enumeration. -/
theorem sealed_handoff_safe (w : CutWorld) (h : w.SealedHandoff) :
    ∀ C : Finset PE, w.closedCut C → w.validCut C →
      (w.cutReceipts C).card ≤ 1 := by
  intro C _hclosed hvalid
  obtain ⟨d, hseal⟩ := h
  have hsub : w.cutReceipts C ⊆ {if d then (5 : PE) else 2} := by
    intro e he
    obtain ⟨heC, hcons⟩ := Finset.mem_filter.mp he
    by_cases hd : peDomL e = d
    · -- the sealed domain's consume cannot sit in a valid cut
      obtain ⟨g, hg, hgdom, hlt⟩ := hseal e hcons hd
      exact absurd (hvalid e heC hcons)
        (seal_blocks_fires w e g hg (hgdom.trans hd.symm) hlt)
    · -- the other domain owns exactly one consume potential
      have hval : e.val = 2 ∨ e.val = 5 := by
        simpa [peConsume] using hcons
      rcases hval with h2 | h5
      · have he2 : e = (2 : PE) := Fin.ext h2
        subst he2
        cases d with
        | true => exact absurd rfl hd
        | false => simp
      · have he5 : e = (5 : PE) := Fin.ext h5
        subst he5
        cases d with
        | true => simp
        | false => exact absurd rfl hd
  calc (w.cutReceipts C).card
      ≤ ({if d then (5 : PE) else 2} : Finset PE).card :=
        Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

/-- Kill-line witness: the safe world IS a sealed handoff — decided from
the causal order alone. -/
theorem wSafe_sealed_handoff : wSafe.SealedHandoff := by decide

/-- Kill-line witness: the edge-only world is NOT a sealed handoff —
decided from the causal order alone, independent of its unsafe outcome. -/
theorem wEdgeOnly_not_sealed_handoff : ¬ wEdgeOnly.SealedHandoff := by decide

/-- THE discriminating bit, named: the safe world carries the seal edge. -/
theorem wSafe_seal_edge : wSafe.lt 1 2 = true := rfl

/-- …and the edge-only world does not. This single order fact is what
separates them for `SealedHandoff` — no receipt is consulted. -/
theorem wEdgeOnly_no_seal_edge : wEdgeOnly.lt 1 2 = false := rfl

/-- The third safe shape found by the probe: causal consume-sequencing.
Enables precede their own consumes; the sender's consume sits in the
receiver's causal past; NO disable seals anywhere. -/
def wSeq : CutWorld where
  lt a b := (a.val = 0 && (b.val = 2 || b.val = 5))
    || (a.val = 3 && b.val = 5)
    || (a.val = 2 && b.val = 5)

theorem wSeq_strict : wSeq.strict := by decide

/-- `wSeq` is Safe: the sender's consume poisons the receiver's `fires`
no-consume-in-view clause (`wSeq.lt 2 5 = true`). -/
theorem wSeq_safe :
    ∀ C : Finset PE, wSeq.closedCut C → wSeq.validCut C →
      (wSeq.cutReceipts C).card ≤ 1 := by decide

/-- …with NO sealed handoff: the two-disjunct conjecture is incomplete. -/
theorem wSeq_not_sealed_handoff : ¬ wSeq.SealedHandoff := by decide

/-- …and a genuinely live sender — this is a real authority scenario, not
a world where nobody could ever spend. -/
theorem wSeq_sender_live :
    ∃ C : Finset PE, wSeq.closedCut C ∧ wSeq.validCut C ∧
      wSeq.cutLive true C := by decide

/-- The naive gap disjunct is vacuous: in EVERY world the empty cut is
closed, valid, and has an empty frontier — `fires` demands an enable in
the potential's past, but a potential whose past fits inside `∅` has an
empty past. This is why the biconditional was cut. -/
theorem gap_vacuous (w : CutWorld) :
    ∃ C : Finset PE, w.closedCut C ∧ w.validCut C ∧
      ∀ d : Bool, ¬ w.cutLive d C := by
  refine ⟨∅, ?_, ?_, ?_⟩
  · intro e he
    exact absurd he (Finset.notMem_empty e)
  · intro e he
    exact absurd he (Finset.notMem_empty e)
  · rintro d ⟨e, _, _, _, hpast, hfires⟩
    obtain ⟨g, hgmem, _⟩ := hfires.1
    exact absurd (hpast hgmem) (Finset.notMem_empty g)

/-! ## Layer D — sufficiency at the abstract level: the probe, the no-go, the lift

**Probe verdict (recorded before the lift): the literal lift is REFUTED.**
`CutWorld.SealedHandoff` cannot be stated over the bare `AuthoritySystem`
(no events, no causal order, no disable vocabulary — the boundary already
named in Layer C's honest-scope note), and more fundamentally NO
discriminating predicate over the bare signature can imply `Safe`:

* **The generation gap.** `reachable` is an arbitrary step-closed FIELD
  with no induction principle, and `receipts` at reachable configurations
  are unconstrained except along steps. Sufficiency is an invariant
  argument — base case plus preservation — and the bare structure has no
  base case. `StepFreeSystem` below makes this a kernel-checked no-go: a
  system with NO steps and NO liveness (so every step/live-shaped pattern
  holds vacuously, including the direct analogue of the sealed-handoff
  predicate) whose constant receipts already violate safety
  (`sufficiency_needs_generation`). A predicate that survives this
  countermodel must constrain `receipts` at reachable configurations
  directly — i.e. restate `Safe`, the kill-line violation.

**The lift, at the honest price.** Sufficiency holds one level up, over
`GeneratedAuthoritySystem`: the bare system plus exactly the structure the
`CutWorld` probe model provides for free — an initial configuration with
empty receipts, reachability generated from it (an induction principle),
and steps that fire only when live (`CutWorld`'s `validCut`/`fires`
discipline). Over that structure, `SealedSenders` — every domain except a
designated receiver is never live at any reachable configuration — implies
safety (`sealed_senders_safe`), with a structural proof and no finiteness
assumption on `D`. This is the maximal available generality: the no-go
shows the two added laws cannot be dropped.

**Kill-line discipline (the predicate is discriminating, not Safe
restated).** `SealedSenders` mentions only `live` and `reachable` — no
receipts, no cardinality. `CopySystem` instantiates the generated laws
(`CopyGenerated`) and FAILS the predicate (`copy_not_sealed_senders`) — as
it must, being unsafe. And the correspondence with Layer C is checked, not
asserted: in `wSafe` the sealed sender is never `cutLive` at ANY cut
(`wSafe_sender_never_live`) — `SealedSenders` is exactly that shape, one
level up: the abstract shadow of `CutWorld.SealedHandoff`'s derived effect
(`seal_blocks_fires`), stating the seal's operational content (the sender
is never live) where no causal order exists to state its FORM (the
disable-before-consume edge).

**No biconditional, again.** `SeqSystem` — the abstract mirror of `wSeq`'s
consume-sequencing — is Safe (`seq_safe`) with BOTH domains live at the
initial configuration (`seq_both_live_init`), hence no sealed sender
(`seq_not_sealed_senders`). Sufficiency only, exactly as in Layer C. -/

/-- **The no-go countermodel.** No steps, no liveness, constant two-element
receipts, everything reachable. Every `AuthoritySystem` law holds
(vacuously); every pattern over `step`/`live` holds (vacuously); safety
fails. Sufficiency cannot live at this generality. -/
def StepFreeSystem : AuthoritySystem Bool where
  Config := Unit
  reachable _ := True
  step _ _ _ := False
  receipts _ := {true, false}
  live _ _ := False
  disconnected _ _ _ := True
  step_live _ _ h := absurd h not_false
  step_reachable _ _ _ _ hs := hs.elim
  receipts_step _ _ _ hs := hs.elim
  frozen_live _ _ _ _ _ hs _ := hs.elim

/-- **The generation gap, kernel-checked.** The direct abstract analogue of
the sealed-handoff predicate — some receiver `d₀` such that every other
domain is never live at any reachable configuration — HOLDS in the
step-free system (vacuously: nobody is ever live), yet the system is not
`Safe`. So over the bare `AuthoritySystem` the predicate does not imply
safety; the lift genuinely needs generated reachability. -/
theorem sufficiency_needs_generation :
    (∃ d₀ : Bool, ∀ c, StepFreeSystem.reachable c →
      ∀ d, d ≠ d₀ → ¬ StepFreeSystem.live c d) ∧
    ¬ Safe StepFreeSystem := by
  constructor
  · exact ⟨true, fun _ _ _ _ h => h⟩
  · intro hsafe
    have := hsafe () trivial
    revert this
    decide

/-- The bare system plus exactly what the finite probe model supplied for
free: an initial configuration with empty receipts, reachability GENERATED
from it (the induction principle `CutWorld`'s down-closed cuts carry
intrinsically), and steps that fire only when live (`validCut`/`fires`).
The no-go (`sufficiency_needs_generation`) shows these cannot be dropped. -/
structure GeneratedAuthoritySystem (D : Type) [DecidableEq D] extends
    AuthoritySystem D where
  /-- The initial configuration. -/
  init : Config
  /-- The initial configuration is reachable. -/
  init_reachable : reachable init
  /-- Nothing has been consumed initially. -/
  init_receipts : receipts init = ∅
  /-- Steps fire only from local enablement (the `fires` discipline). -/
  step_requires_live : ∀ c d c', step c d c' → live c d
  /-- Reachability is generated: induction from `init` along steps. -/
  reachable_generated : ∀ (P : Config → Prop), P init →
    (∀ c d c', reachable c → P c → step c d c' → P c') →
    ∀ c, reachable c → P c

/-- **The lifted sealed-handoff predicate.** Some designated receiver `d₀`;
every OTHER domain — every sender — is never live at any reachable
configuration. Pure `live`/`reachable`: no receipts, no cardinality, no
`Safe`. The abstract shadow of `CutWorld.SealedHandoff`: with no causal
order to state the seal's form (disable-before-consume), it states the
seal's checked operational effect (`wSafe_sender_never_live`). -/
def SealedSenders (S : GeneratedAuthoritySystem D) : Prop :=
  ∃ d₀ : D, ∀ c, S.reachable c → ∀ d, d ≠ d₀ → ¬ S.live c d

/-- **Sufficiency, lifted (the fourth mesh brick).** In a generated system
whose senders are all sealed, safety holds: receipts start empty and only
the receiver can ever step, so every reachable configuration's receipts
live inside `{d₀}`. Structural induction along generated reachability — no
finiteness of `D`, no enumeration, no causal order. -/
theorem sealed_senders_safe (S : GeneratedAuthoritySystem D)
    (h : SealedSenders S) : Safe S.toAuthoritySystem := by
  obtain ⟨d₀, hseal⟩ := h
  have hinv : ∀ c, S.reachable c → S.receipts c ⊆ {d₀} := by
    intro c hc
    refine S.reachable_generated (fun c => S.receipts c ⊆ {d₀}) ?_ ?_ c hc
    · show S.receipts S.init ⊆ {d₀}
      rw [S.init_receipts]
      exact Finset.empty_subset _
    · intro c d c' hr hP hs
      show S.receipts c' ⊆ {d₀}
      have hlive := S.step_requires_live c d c' hs
      have hd : d = d₀ := by
        by_contra hne
        exact hseal c hr d hne hlive
      rw [S.receipts_step c d c' hs, hd]
      exact Finset.insert_subset_iff.mpr ⟨Finset.mem_singleton_self d₀, hP⟩
  intro c hc
  calc (S.receipts c).card
      ≤ ({d₀} : Finset D).card := Finset.card_le_card (hinv c hc)
    _ = 1 := Finset.card_singleton d₀

/-- The uncoordinated copy system carries the generated structure: its
reachability is inductively defined, its receipts start empty, and its
steps require local enablement. So the enriched laws do not smuggle in
safety — the unsafe countermodel satisfies all of them. -/
def CopyGenerated : GeneratedAuthoritySystem Bool where
  toAuthoritySystem := CopySystem
  init := (false, false)
  init_reachable := CopyReach.init
  init_receipts := by decide
  step_requires_live _ _ _ hs := hs.1
  reachable_generated P hinit hstep c hc := by
    induction hc with
    | init => exact hinit
    | @stepL b hr ih => exact hstep (false, b) true (true, b) hr ih ⟨rfl, rfl⟩
    | @stepR a hr ih => exact hstep (a, false) false (a, true) hr ih ⟨rfl, rfl⟩

/-- Kill-line witness: the (unsafe) copy system FAILS `SealedSenders` —
both domains are live at the reachable initial configuration. The
predicate discriminates; it is not vacuously available. -/
theorem copy_not_sealed_senders : ¬ SealedSenders CopyGenerated := by
  rintro ⟨d₀, h⟩
  cases d₀ with
  | true => exact h (false, false) CopyReach.init false (by decide) rfl
  | false => exact h (false, false) CopyReach.init true (by decide) rfl

/-- The checked Layer C ↔ Layer D correspondence: in the sealed-handoff
world `wSafe`, the sealed sender is never `cutLive` at ANY cut — the exact
shape `SealedSenders` states abstractly. -/
theorem wSafe_sender_never_live : ∀ C : Finset PE, ¬ wSafe.cutLive true C := by
  decide

/-- The abstract mirror of `wSeq` (consume-sequencing): both domains are
live at the start, whoever consumes first poisons the other's enablement
(here: enablement exists only at the initial configuration), and the
domains coordinate (`disconnected` is empty). Safe, with no sealed
sender. -/
def SeqSystem : GeneratedAuthoritySystem Bool where
  Config := CopyConfig
  reachable c := c = (false, false) ∨ c = (true, false) ∨ c = (false, true)
  step c d c' := c = (false, false) ∧
    c' = (if d then (true, c.2) else (c.1, true))
  receipts c :=
    (if c.1 then {true} else ∅) ∪ (if c.2 then {false} else ∅)
  live c _ := c = (false, false)
  disconnected _ _ _ := False
  step_live c d h := ⟨if d then (true, c.2) else (c.1, true), h, rfl⟩
  step_reachable c d c' _ hs := by
    obtain ⟨hc, rfl⟩ := hs
    subst hc
    cases d
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  receipts_step c d c' hs := by
    obtain ⟨hc, rfl⟩ := hs
    subst hc
    cases d <;> decide
  frozen_live _ _ _ _ hdis _ _ := hdis.elim
  init := (false, false)
  init_reachable := Or.inl rfl
  init_receipts := by decide
  step_requires_live _ _ _ hs := hs.1
  reachable_generated P hinit hstep c hc := by
    rcases hc with rfl | rfl | rfl
    · exact hinit
    · exact hstep (false, false) true (true, false) (Or.inl rfl) hinit ⟨rfl, rfl⟩
    · exact hstep (false, false) false (false, true) (Or.inl rfl) hinit ⟨rfl, rfl⟩

/-- `SeqSystem` is Safe — checked over its three reachable configurations. -/
theorem seq_safe : Safe SeqSystem.toAuthoritySystem := by
  intro c hc
  rcases hc with rfl | rfl | rfl <;> decide

/-- …with both domains genuinely live at the reachable start… -/
theorem seq_both_live_init :
    SeqSystem.live (false, false) true ∧ SeqSystem.live (false, false) false :=
  ⟨rfl, rfl⟩

/-- …hence NO sealed sender: sufficiency, not necessity — the abstract
mirror of `wSeq_safe` + `wSeq_not_sealed_handoff`. -/
theorem seq_not_sealed_senders : ¬ SealedSenders SeqSystem := by
  rintro ⟨d₀, h⟩
  cases d₀ with
  | true => exact h (false, false) (Or.inl rfl) false (by decide) rfl
  | false => exact h (false, false) (Or.inl rfl) true (by decide) rfl

/-! ## Layer E — the normal-form STEP-0 enumerator and the shape observers

STEP 0 of the normal-form brick, same probe-before-proving discipline as
Layer C: before any characterization theorem is attempted, a finite
ENUMERATOR of probe worlds must confirm that a safe-LOOKING trajectory that
is neither a witnessed handoff nor a gap is EXPRESSIBLE — otherwise any
normal form proved over this model would be vacuous (it would "hold" only
because the model cannot write down the alternative).

**The enumerator.** `probeWorld m`, for `m : Fin 256`: the family of causal
orders generated by the 256 subsets of the 8-edge basis `probeEdge`, with
`lt` = path-reachability along the selected edges (fuel 4 = paths of ≤ 5
edges, enough because every basis edge strictly increases the event index,
so no path repeats a node). Irreflexivity is generic and structural
(`probeWorld_irrefl`, via `probeReach_lt`); full strictness (with
transitivity) is discharged per witness world by pointwise identification
with a named world. The family CONTAINS all four landed Layer C worlds
(`probeWorld_99/107/111/82` identify them by index) plus the new gap world
`wGap` (`probeWorld_2`) — the enumerator is a superset of the v0 probe,
not a new model.

**The shape observers — all DERIVED, pure causal order.** They read only
`w.lt` and the fixed event vocabulary; no receipts, no safety, no
liveness, and none of them appears in any firing rule (the kill line:
handoff stays in the CONCLUSION, never in the definition of enablement):

* `Unenabled e` — GAP at the potential: no same-domain enable in `e`'s
  causal past; the domain never acquires the authority at all;
* `SealWitnessed e` — a same-domain disable causally precedes `e` (the
  Layer C seal, stated per potential);
* `SeqWitnessed e` — some consume event causally precedes `e` (the `wSeq`
  shape);
* `RelinquishWitnessed e` = seal ∨ sequencing — the "handoff" disjunct in
  its honest form: a causal witness that a relinquish event precedes the
  dead potential. HONESTY: this is WEAKER than the v0 conjecture's
  informal "the authority moves" — `wSeq` and `wGap` are safe worlds in
  which no authority ever moves, so movement cannot be a necessary
  disjunct. The provable disjunct is a witnessed relinquish, not a
  completed transfer.

**Probe verdicts (the STEP-0 outcome, recorded before the Layer F
proofs):**

* `step0_alternative_expressible` — the GO condition: probe world 107
  (= `wEdgeOnly`) is strict; NEITHER of its consume potentials is
  unenabled, sealed, or sequenced (no gap, no witness of any kind); a
  valid closed cut has BOTH domains simultaneously live (every local rule
  is satisfied — the trajectory looks safe to every local observer); and a
  valid closed cut carries TWO completed consumes. The
  neither-handoff-nor-gap trajectory is expressible, and only the safety
  hypothesis excludes it. The normal form is not vacuous.
* `step0_gap_world_expressible` — probe world 2 (= `wGap`) is strict,
  safe, has a genuinely live sender, NO relinquish witness anywhere, and
  an UNENABLED receiver potential (while the sender's potential is
  enabled): the gap disjunct does real, discriminating work — contrast
  `gap_vacuous`, which killed the naive cut-level "empty frontier
  somewhere" gap.
* `step0_seal_shape` / `step0_seq_shape` — worlds 111 (= `wSafe`) and 82
  (= `wSeq`) realize the seal and sequencing shapes EXCLUSIVELY: each
  satisfies its own witness and provably fails the other two shapes. The
  three shapes are pairwise independent — none subsumes another. -/

/-- GAP shape at a consume potential: no same-domain enable anywhere in its
causal past — the domain never acquires the authority. Pure causal order. -/
abbrev CutWorld.Unenabled (w : CutWorld) (e : PE) : Prop :=
  ∀ g ∈ w.past e, ¬(peEnable g = true ∧ peDomL g = peDomL e)

/-- SEAL witness at a consume potential: a same-domain disable causally
precedes it (the Layer C seal, per potential). Pure causal order. -/
abbrev CutWorld.SealWitnessed (w : CutWorld) (e : PE) : Prop :=
  ∃ g : PE, peDisable g = true ∧ peDomL g = peDomL e ∧ w.lt g e = true

/-- SEQUENCING witness at a consume potential: some consume event causally
precedes it (the `wSeq` shape). Pure causal order. -/
abbrev CutWorld.SeqWitnessed (w : CutWorld) (e : PE) : Prop :=
  ∃ g : PE, peConsume g = true ∧ w.lt g e = true

/-- Witnessed relinquish — the honest "handoff" disjunct: a causal witness
that a relinquish event (a same-domain disable, or any consume) precedes
the potential. NOT a claim that authority moves; see the layer doc. -/
abbrev CutWorld.RelinquishWitnessed (w : CutWorld) (e : PE) : Prop :=
  w.SealWitnessed e ∨ w.SeqWitnessed e

/-- The 8-edge causal basis of the STEP-0 enumerator. Every edge strictly
increases the event index (checked by `probeStep_lt`), so every generated
order is irreflexive and all its paths are simple. -/
def probeEdge : Fin 8 → PE × PE
  | 0 => (0, 1)  -- enableL  < disableL
  | 1 => (0, 2)  -- enableL  < consumeL
  | 2 => (1, 2)  -- disableL < consumeL   (the SEAL edge)
  | 3 => (1, 3)  -- disableL < enableR    (the handoff edge)
  | 4 => (2, 5)  -- consumeL < consumeR   (the SEQUENCING edge)
  | 5 => (3, 4)  -- enableR  < disableR
  | 6 => (3, 5)  -- enableR  < consumeR
  | 7 => (4, 5)  -- disableR < consumeR   (the R-side seal edge)

/-- Basis edges selected by bitmask `m`. -/
def probeStep (m : Fin 256) (a b : PE) : Bool :=
  (List.finRange 8).any fun i => m.val.testBit i.val && decide (probeEdge i = (a, b))

/-- Reachability along selected basis edges: `probeReach m n` witnesses
paths of at most `n + 1` edges. -/
def probeReach (m : Fin 256) : Nat → PE → PE → Bool
  | 0, a, b => probeStep m a b
  | n + 1, a, b =>
      probeStep m a b ||
        (List.finRange 6).any fun c => probeStep m a c && probeReach m n c b

/-- The `m`-th probe world: causal order = ≤5-edge reachability along the
mask's basis edges. -/
def probeWorld (m : Fin 256) : CutWorld where
  lt a b := probeReach m 4 a b

/-- Worlds with pointwise-equal orders are equal. -/
theorem CutWorld.ext' {v w : CutWorld} (h : ∀ a b, v.lt a b = w.lt a b) :
    v = w := by
  cases v with
  | mk vlt =>
    cases w with
    | mk wlt =>
      have hfun : vlt = wlt := funext fun a => funext fun b => h a b
      rw [hfun]

/-- Every basis edge strictly increases the event index. -/
theorem probeStep_lt (m : Fin 256) (a b : PE) (h : probeStep m a b = true) :
    a.val < b.val := by
  simp only [probeStep, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨i, _, _, hedge⟩ := h
  have hall : ∀ i : Fin 8, (probeEdge i).1.val < (probeEdge i).2.val := by decide
  have hlt := hall i
  rw [hedge] at hlt
  exact hlt

/-- Reachability along basis edges strictly increases the event index. -/
theorem probeReach_lt (m : Fin 256) :
    ∀ (n : Nat) (a b : PE), probeReach m n a b = true → a.val < b.val := by
  intro n
  induction n with
  | zero => exact fun a b h => probeStep_lt m a b h
  | succ k ih =>
    intro a b h
    simp only [probeReach, Bool.or_eq_true, List.any_eq_true,
      Bool.and_eq_true] at h
    rcases h with h1 | ⟨c, _, hac, hcb⟩
    · exact probeStep_lt m a b h1
    · exact Nat.lt_trans (probeStep_lt m a c hac) (ih c b hcb)

/-- EVERY probe world is irreflexive — generic, structural, no
enumeration: reachability strictly increases the event index. -/
theorem probeWorld_irrefl (m : Fin 256) (e : PE) :
    (probeWorld m).lt e e = false := by
  cases hval : (probeWorld m).lt e e with
  | false => rfl
  | true => exact absurd (probeReach_lt m 4 e e hval) (Nat.lt_irrefl e.val)

/-- The gap world: only `enableL < consumeL`. R is never enabled — its
consume potential is a genuine GAP, with no relinquish event anywhere. -/
def wGap : CutWorld where
  lt a b := a.val = 0 && b.val = 2

theorem wGap_strict : wGap.strict := by decide

/-- The enumerator contains the uncoordinated world: index 99 is
`wUnsafe`, pointwise. -/
theorem probeWorld_99 : probeWorld 99 = wUnsafe := CutWorld.ext' (by decide)

/-- The enumerator contains the edge-only world: index 107 is
`wEdgeOnly`, pointwise. -/
theorem probeWorld_107 : probeWorld 107 = wEdgeOnly := CutWorld.ext' (by decide)

/-- The enumerator contains the sealed-handoff world: index 111 is
`wSafe`, pointwise. -/
theorem probeWorld_111 : probeWorld 111 = wSafe := CutWorld.ext' (by decide)

/-- The enumerator contains the consume-sequencing world: index 82 is
`wSeq`, pointwise. -/
theorem probeWorld_82 : probeWorld 82 = wSeq := CutWorld.ext' (by decide)

/-- The enumerator contains the gap world: index 2 is `wGap`, pointwise. -/
theorem probeWorld_2 : probeWorld 2 = wGap := CutWorld.ext' (by decide)

/-- **STEP 0, the GO condition.** The enumerator EXPRESSES a safe-looking
trajectory that is neither a witnessed handoff nor a gap: probe world 107
is strict; NO consume potential is unenabled or relinquish-witnessed; a
valid closed cut has BOTH domains simultaneously live (locally lawful
everywhere — safe-looking); and a valid closed cut carries TWO completed
consumes. The alternative to the normal form is expressible, and only
safety excludes it — the characterization is not vacuous. -/
theorem step0_alternative_expressible :
    ∃ m : Fin 256, (probeWorld m).strict ∧
      (∀ e : PE, peConsume e = true →
        ¬(probeWorld m).Unenabled e ∧ ¬(probeWorld m).RelinquishWitnessed e) ∧
      (∃ C : Finset PE, (probeWorld m).closedCut C ∧ (probeWorld m).validCut C ∧
        (probeWorld m).cutLive true C ∧ (probeWorld m).cutLive false C) ∧
      (∃ C : Finset PE, (probeWorld m).closedCut C ∧ (probeWorld m).validCut C ∧
        ((probeWorld m).cutReceipts C).card = 2) := by
  refine ⟨107, ?_⟩
  rw [probeWorld_107]
  exact ⟨wEdgeOnly_strict, by decide, by decide, ccca_edge_only_still_unsafe⟩

/-- **STEP 0, gap non-vacuity.** Probe world 2 is strict and SAFE with a
genuinely live sender, NO relinquish witness on any event, an ENABLED
sender potential — and an UNENABLED receiver potential. The gap disjunct
discriminates (unlike the vacuous cut-level gap of `gap_vacuous`). -/
theorem step0_gap_world_expressible :
    ∃ m : Fin 256, (probeWorld m).strict ∧
      (∀ C : Finset PE, (probeWorld m).closedCut C → (probeWorld m).validCut C →
        ((probeWorld m).cutReceipts C).card ≤ 1) ∧
      (∃ C : Finset PE, (probeWorld m).closedCut C ∧ (probeWorld m).validCut C ∧
        (probeWorld m).cutLive true C) ∧
      (probeWorld m).Unenabled 5 ∧ ¬(probeWorld m).Unenabled 2 ∧
      (∀ e : PE, ¬(probeWorld m).RelinquishWitnessed e) := by
  refine ⟨2, ?_⟩
  rw [probeWorld_2]
  exact ⟨wGap_strict, by decide, by decide, by decide, by decide, by decide⟩

/-- STEP 0, shape independence (seal): `wSafe` (= probe world 111)
realizes EXACTLY the seal shape — seal witness on the sender's potential,
no gap on either potential, no sequencing witness anywhere. -/
theorem step0_seal_shape :
    wSafe.SealWitnessed 2 ∧ ¬wSafe.Unenabled 2 ∧ ¬wSafe.Unenabled 5 ∧
      (∀ e : PE, ¬wSafe.SeqWitnessed e) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- STEP 0, shape independence (sequencing): `wSeq` (= probe world 82)
realizes EXACTLY the sequencing shape — a consume causally precedes the
receiver's potential, no seal witness anywhere, no gap on either
potential. -/
theorem step0_seq_shape :
    wSeq.SeqWitnessed 5 ∧ (∀ e : PE, ¬wSeq.SealWitnessed e) ∧
      ¬wSeq.Unenabled 2 ∧ ¬wSeq.Unenabled 5 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Layer F — the handoff-or-gap NORMAL FORM (the characterization)

The brick: `authority_normal_form` — for every strict probe world,

  `SafeCuts w ↔ ∃ consume potential e, Unenabled e ∨ RelinquishWitnessed e`

every safe world is a GAP or a WITNESSED RELINQUISH on some potential, and
nothing else is safe. Both directions are STRUCTURAL proofs over all
strict `CutWorld`s (an infinite class of orders — `decide` appears only in
finite side conditions like `peConsume 2 = true`), not an enumeration.

Decomposition, each step named:

* `both_fires_unsafe` — the amalgamation: if both consume potentials can
  fire, the glued cut `{2, 5} ∪ past 2 ∪ past 5` is closed (transitivity)
  and valid (`fires`' no-consume-in-view clause makes both pasts
  consume-free) and carries TWO receipts. Safety therefore forces a DEAD
  potential;
* `dead_potential_safe` — the converse: one dead potential confines every
  valid cut's receipts to the other domain's single potential;
* `safeCuts_iff_dead_potential` — safety ⟺ some potential is dead. THIS
  equivalence is the operational content of the normal form;
* `dead_trichotomy` — a dead potential is unenabled ∨ seal-witnessed ∨
  sequencing-witnessed. HONESTY: this decomposition is de Morgan over the
  three clauses of the v0-frozen `fires` predicate — definitional
  bookkeeping, not new content. The content lives in
  `safeCuts_iff_dead_potential`; the trichotomy only NAMES why the dead
  potential is dead, and Layer E shows each name is independently
  realizable;
* `everLive_iff_fires` / `safeCuts_iff_ever_live_unique` — the trajectory
  reading: `fires e` ⟺ its domain is live at SOME valid closed cut, so
  safety ⟺ the two domains are never both ever-live. Cross-CUT mutual
  exclusion — strictly stronger than v0's per-cut frontier bound;
* `safe_cut_dichotomy` — the per-cut statement in the conjectured target
  shape: at every valid closed cut of a safe world the frontier is EMPTY,
  or is EXACTLY the singleton domain opposite a dead potential that
  carries a gap-or-relinquish shape;
* `sealedHandoff_iff_sealWitnessed` — bridge to Layer C: `SealedHandoff`
  is precisely the seal disjunct, stated per potential.

**What this does NOT say (the honest boundary).** The v0 conjecture read
"handoff (the authority MOVES, with a causal witness) or gap". The proved
normal form WEAKENS the handoff disjunct to "witnessed relinquish"
(seal-by-disable or sequencing-by-consume): `wSeq` and `wGap` are safe
worlds in which nothing ever moves, so movement cannot be a necessary
disjunct — the two-disjunct conjecture as originally worded is REFUTED,
and this trichotomy (gap / seal / sequencing, with the latter two folded
into one witnessed-relinquish disjunct) is the correct statement. The gap
disjunct is likewise sharpened from the vacuous cut-level "some cut has an
empty frontier" (killed by `gap_vacuous`) to the potential-level "never
enabled". Scope: the fixed 6-event, one-potential-per-domain vocabulary of
Layer C; with several potentials per domain, "dead" must range over all of
a domain's potentials and the amalgamation must glue the pasts of every
undead pair — that lift is the next brick and is NOT claimed. All Layer
A–D honest non-claims (crash recovery, unforgeability, Byzantine safety,
clock/lease/quorum/epoch correctness, deployed SealV2 conformance,
liveness during partitions) apply unchanged. -/

/-- Membership in the causal past is exactly the order bit. -/
theorem CutWorld.mem_past {w : CutWorld} {g e : PE} :
    g ∈ w.past e ↔ w.lt g e = true :=
  ⟨fun h => (Finset.mem_filter.mp h).2,
   fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ g, h⟩⟩

/-- Operational safety of a probe world, as a named predicate: every valid
down-closed cut carries at most one completed consume. -/
abbrev CutWorld.SafeCuts (w : CutWorld) : Prop :=
  ∀ C : Finset PE, w.closedCut C → w.validCut C → (w.cutReceipts C).card ≤ 1

/-- The event vocabulary carries exactly two consume potentials. -/
theorem consume_eq_two_or_five :
    ∀ e : PE, peConsume e = true → e = 2 ∨ e = 5 := by decide

/-- **The normal-form amalgamation.** If BOTH consume potentials can fire,
the glued cut `{2, 5} ∪ past 2 ∪ past 5` is closed (transitivity of the
causal order) and valid (`fires`' no-consume-in-view clause makes both
pasts consume-free, and both consumes fire by hypothesis) — and it carries
two completed consumes. So the world is not safe. Structural: holds for
every strict world. -/
theorem both_fires_unsafe (w : CutWorld) (hstrict : w.strict)
    (h2 : w.fires 2) (h5 : w.fires 5) : ¬ w.SafeCuts := by
  intro hsafe
  obtain ⟨_hirr, htrans⟩ := hstrict
  set C : Finset PE := insert 2 (insert 5 (w.past 2 ∪ w.past 5)) with hC
  have h2C : (2 : PE) ∈ C := Finset.mem_insert_self _ _
  have h5C : (5 : PE) ∈ C := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hclosed : w.closedCut C := by
    intro e he f hf
    rcases Finset.mem_insert.mp he with rfl | he'
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (CutWorld.mem_past.mpr hf)))
    · rcases Finset.mem_insert.mp he' with rfl | he''
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (CutWorld.mem_past.mpr hf)))
      · rcases Finset.mem_union.mp he'' with hp | hp
        · have hlt : w.lt f 2 = true := htrans f e 2 hf (CutWorld.mem_past.mp hp)
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_union_left _ (CutWorld.mem_past.mpr hlt)))
        · have hlt : w.lt f 5 = true := htrans f e 5 hf (CutWorld.mem_past.mp hp)
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_union_right _ (CutWorld.mem_past.mpr hlt)))
  have hvalid : w.validCut C := by
    intro e _ hcons
    rcases consume_eq_two_or_five e hcons with rfl | rfl
    · exact h2
    · exact h5
  have hsub : ({2, 5} : Finset PE) ⊆ w.cutReceipts C := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact Finset.mem_filter.mpr ⟨h2C, by decide⟩
    · rw [Finset.mem_singleton] at hx'
      subst hx'
      exact Finset.mem_filter.mpr ⟨h5C, by decide⟩
  have h2le : 2 ≤ (w.cutReceipts C).card := by
    calc 2 = ({2, 5} : Finset PE).card := by decide
      _ ≤ (w.cutReceipts C).card := Finset.card_le_card hsub
  have := hsafe C hclosed hvalid
  omega

/-- **The converse: one dead potential is enough.** If some consume
potential can never fire, every valid closed cut's receipts fit inside the
other domain's single potential. Structural; strictness not needed. -/
theorem dead_potential_safe (w : CutWorld)
    (h : ¬ w.fires 2 ∨ ¬ w.fires 5) : w.SafeCuts := by
  intro C _hclosed hvalid
  rcases h with hdead | hdead
  · have hsub : w.cutReceipts C ⊆ {5} := by
      intro e he
      obtain ⟨heC, hcons⟩ := Finset.mem_filter.mp he
      rcases consume_eq_two_or_five e hcons with rfl | rfl
      · exact absurd (hvalid _ heC hcons) hdead
      · exact Finset.mem_singleton_self _
    calc (w.cutReceipts C).card ≤ ({5} : Finset PE).card :=
        Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  · have hsub : w.cutReceipts C ⊆ {2} := by
      intro e he
      obtain ⟨heC, hcons⟩ := Finset.mem_filter.mp he
      rcases consume_eq_two_or_five e hcons with rfl | rfl
      · exact Finset.mem_singleton_self _
      · exact absurd (hvalid _ heC hcons) hdead
    calc (w.cutReceipts C).card ≤ ({2} : Finset PE).card :=
        Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _

/-- **Safety ⟺ a dead potential.** The operational content of the normal
form: a strict world is safe exactly when one of its two consume
potentials can never fire. -/
theorem safeCuts_iff_dead_potential (w : CutWorld) (hstrict : w.strict) :
    w.SafeCuts ↔ (¬ w.fires 2 ∨ ¬ w.fires 5) := by
  constructor
  · intro hsafe
    by_contra h
    rcases not_or.mp h with ⟨h2, h5⟩
    exact both_fires_unsafe w hstrict (not_not.mp h2) (not_not.mp h5) hsafe
  · exact dead_potential_safe w

/-- **Why a potential is dead: the trichotomy.** A consume potential fails
to fire exactly when it is unenabled (gap), seal-witnessed, or
sequencing-witnessed. HONESTY: this is de Morgan over the three clauses of
the v0-frozen `fires` — it names the failure, it does not add content. -/
theorem dead_trichotomy (w : CutWorld) (e : PE) :
    ¬ w.fires e ↔
      (w.Unenabled e ∨ w.SealWitnessed e ∨ w.SeqWitnessed e) := by
  constructor
  · intro hnf
    by_cases hA : ∃ g ∈ w.past e, peEnable g = true ∧ peDomL g = peDomL e
    · by_cases hB : ∀ g ∈ w.past e, ¬(peDisable g = true ∧ peDomL g = peDomL e)
      · by_cases hC : ∀ g ∈ w.past e, peConsume g = false
        · exact absurd ⟨hA, hB, hC⟩ hnf
        · right; right
          push_neg at hC
          obtain ⟨g, hgmem, hg⟩ := hC
          have hg' : peConsume g = true := by simpa using hg
          exact ⟨g, hg', CutWorld.mem_past.mp hgmem⟩
      · right; left
        push_neg at hB
        obtain ⟨g, hgmem, hg1, hg2⟩ := hB
        exact ⟨g, hg1, hg2, CutWorld.mem_past.mp hgmem⟩
    · left
      intro g hgmem hg
      exact hA ⟨g, hgmem, hg⟩
  · rintro (hU | ⟨g, hg1, hg2, hlt⟩ | ⟨g, hg1, hlt⟩) hf
    · obtain ⟨g, hgmem, hg⟩ := hf.1
      exact hU g hgmem hg
    · exact hf.2.1 g (CutWorld.mem_past.mpr hlt) ⟨hg1, hg2⟩
    · have hfalse := hf.2.2 g (CutWorld.mem_past.mpr hlt)
      simp [hg1] at hfalse

/-- **THE NORMAL FORM.** A strict probe world is safe IF AND ONLY IF some
consume potential is a gap (never enabled) or carries a causal relinquish
witness (a same-domain disable or a consume in its past). Every safe
evolution of the single-use authority factors through one of these shapes;
nothing else is safe. Structural in both directions. -/
theorem authority_normal_form (w : CutWorld) (hstrict : w.strict) :
    w.SafeCuts ↔
      ∃ e : PE, peConsume e = true ∧
        (w.Unenabled e ∨ w.RelinquishWitnessed e) := by
  rw [safeCuts_iff_dead_potential w hstrict]
  constructor
  · rintro (h | h)
    · exact ⟨2, by decide, (dead_trichotomy w 2).mp h⟩
    · exact ⟨5, by decide, (dead_trichotomy w 5).mp h⟩
  · rintro ⟨e, hcons, hshape⟩
    rcases consume_eq_two_or_five e hcons with rfl | rfl
    · exact Or.inl ((dead_trichotomy w 2).mpr hshape)
    · exact Or.inr ((dead_trichotomy w 5).mpr hshape)

/-- The unique consume potential of a domain: `2` for L, `5` for R. -/
def potOf : Bool → PE
  | true => 2
  | false => 5

/-- The domain is live at SOME valid closed cut of the world. -/
abbrev CutWorld.EverLive (w : CutWorld) (d : Bool) : Prop :=
  ∃ C : Finset PE, w.closedCut C ∧ w.validCut C ∧ w.cutLive d C

/-- A potential fires exactly when its domain is live SOMEWHERE: the cut
`past e` is closed, valid (fires' no-consume clause), and delivers exactly
the potential's prerequisites. -/
theorem everLive_iff_fires (w : CutWorld) (hstrict : w.strict) (d : Bool) :
    w.EverLive d ↔ w.fires (potOf d) := by
  obtain ⟨hirr, htrans⟩ := hstrict
  constructor
  · rintro ⟨C, _, _, e, hcons, hdom, _, _, hf⟩
    have he : e = potOf d := by
      rcases consume_eq_two_or_five e hcons with rfl | rfl
      · cases d
        · exact absurd hdom (by decide)
        · rfl
      · cases d
        · rfl
        · exact absurd hdom (by decide)
    rwa [he] at hf
  · intro hf
    refine ⟨w.past (potOf d), ?_, ?_, potOf d, ?_, ?_, ?_, ?_, hf⟩
    · intro e he f hfe
      exact CutWorld.mem_past.mpr
        (htrans f e (potOf d) hfe (CutWorld.mem_past.mp he))
    · intro e he hcons
      have hfalse := hf.2.2 e he
      simp [hcons] at hfalse
    · cases d <;> decide
    · cases d <;> decide
    · intro hmem
      have hlt := CutWorld.mem_past.mp hmem
      rw [hirr (potOf d)] at hlt
      exact Bool.false_ne_true hlt
    · exact Finset.Subset.refl _

/-- **Cross-cut mutual exclusion (the trajectory reading).** A strict
world is safe exactly when its two domains are never BOTH ever-live —
across ALL valid closed cuts, not per cut. Strictly stronger than the v0
per-cut frontier bound. -/
theorem safeCuts_iff_ever_live_unique (w : CutWorld) (hstrict : w.strict) :
    w.SafeCuts ↔ ¬(w.EverLive true ∧ w.EverLive false) := by
  rw [safeCuts_iff_dead_potential w hstrict]
  constructor
  · rintro (h | h) ⟨hT, hF⟩
    · exact h ((everLive_iff_fires w hstrict true).mp hT)
    · exact h ((everLive_iff_fires w hstrict false).mp hF)
  · intro h
    by_cases h2 : w.fires 2
    · right
      intro h5
      exact h ⟨(everLive_iff_fires w hstrict true).mpr h2,
               (everLive_iff_fires w hstrict false).mpr h5⟩
    · exact Or.inl h2

/-- The live frontier of a cut — a DERIVED observer over `cutLive`, the
same discipline as Layer A's `frontier`. Never a primitive. -/
noncomputable def CutWorld.frontierAt (w : CutWorld) (C : Finset PE) :
    Finset Bool :=
  letI := Classical.decPred fun d => w.cutLive d C
  Finset.univ.filter fun d => w.cutLive d C

theorem CutWorld.mem_frontierAt {w : CutWorld} {C : Finset PE} {d : Bool} :
    d ∈ w.frontierAt C ↔ w.cutLive d C := by
  classical
  unfold CutWorld.frontierAt
  simp

/-- **The per-cut handoff-or-gap dichotomy (the conjectured target
shape).** In a safe strict world, EVERY valid closed cut has an empty
frontier, or its frontier is EXACTLY the singleton domain opposite a dead
consume potential that carries a gap-or-relinquish shape. The at-most-one
of v0 is now doing something namable. -/
theorem safe_cut_dichotomy (w : CutWorld) (hstrict : w.strict)
    (hsafe : w.SafeCuts) (C : Finset PE) (hclosed : w.closedCut C)
    (hvalid : w.validCut C) :
    w.frontierAt C = ∅ ∨
      ∃ e : PE, peConsume e = true ∧
        (w.Unenabled e ∨ w.RelinquishWitnessed e) ∧
        w.frontierAt C = {!peDomL e} := by
  by_cases hempty : w.frontierAt C = ∅
  · exact Or.inl hempty
  · right
    obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hfire : w.fires (potOf d) :=
      (everLive_iff_fires w hstrict d).mp
        ⟨C, hclosed, hvalid, CutWorld.mem_frontierAt.mp hd⟩
    have hdeadOther : ¬ w.fires (potOf !d) := by
      rcases (safeCuts_iff_dead_potential w hstrict).mp hsafe with h | h
      · cases d
        · exact h
        · exact absurd hfire h
      · cases d
        · exact absurd hfire h
        · exact h
    refine ⟨potOf !d, ?_, (dead_trichotomy w _).mp hdeadOther, ?_⟩
    · cases d <;> decide
    · have hdomeq : (!peDomL (potOf !d)) = d := by cases d <;> decide
      rw [hdomeq]
      apply Finset.ext
      intro d'
      simp only [Finset.mem_singleton]
      constructor
      · intro hd'
        have hfire' : w.fires (potOf d') :=
          (everLive_iff_fires w hstrict d').mp
            ⟨C, hclosed, hvalid, CutWorld.mem_frontierAt.mp hd'⟩
        by_contra hne
        have hflip : d' = !d := by
          cases d <;> cases d' <;> simp_all
        rw [hflip] at hfire'
        exact absurd hfire' hdeadOther
      · rintro rfl
        exact hd

/-- Bridge to Layer C: the sealed-handoff pattern is exactly a seal
witness on one domain's (unique) consume potential. -/
theorem sealedHandoff_iff_sealWitnessed (w : CutWorld) :
    w.SealedHandoff ↔ (w.SealWitnessed 2 ∨ w.SealWitnessed 5) := by
  constructor
  · rintro ⟨d, h⟩
    cases d
    · right
      obtain ⟨g, hg1, hg2, hlt⟩ := h 5 (by decide) (by decide)
      refine ⟨g, hg1, ?_, hlt⟩
      rw [hg2]; decide
    · left
      obtain ⟨g, hg1, hg2, hlt⟩ := h 2 (by decide) (by decide)
      refine ⟨g, hg1, ?_, hlt⟩
      rw [hg2]; decide
  · rintro (⟨g, hg1, hg2, hlt⟩ | ⟨g, hg1, hg2, hlt⟩)
    · refine ⟨true, fun e hcons hdom => ?_⟩
      have he : e = 2 := by
        rcases consume_eq_two_or_five e hcons with rfl | rfl
        · rfl
        · exact absurd hdom (by decide)
      subst he
      refine ⟨g, hg1, ?_, hlt⟩
      rw [hg2]; decide
    · refine ⟨false, fun e hcons hdom => ?_⟩
      have he : e = 5 := by
        rcases consume_eq_two_or_five e hcons with rfl | rfl
        · exact absurd hdom (by decide)
        · rfl
      subst he
      refine ⟨g, hg1, ?_, hlt⟩
      rw [hg2]; decide

/-! ## Layer G — no silent handoff (the abstract fragment)

The abstract `AuthoritySystem` has no causal order, so the Layer F shapes
cannot even be STATED over it (the Layer C/D boundary, unchanged). What
does lift is the normal form's contrapositive punchline: **a handoff needs
a connected moment.** `StepChain` is the derived reflexive-transitive
closure of `step` — no new primitive, no new law. `no_silent_handoff`:
in a Safe system under TOTAL partition (every reachable configuration
pairwise disconnected), the live domain along any chain is CONSTANT —
either the old holder's enablement survives every disconnected step
(`frozen_live`, inductively, via `live_persists`) and v0's amalgamation
fires at the endpoint, or the old holder already consumed and the new
holder's consume lands a second receipt. Contrapositive
(`handoff_needs_connection`): if live authority DID change hands along an
evolution, some reachable configuration had a connected pair of distinct
domains — the abstract shadow of Layer F's causal relinquish witness.

Scope honesty: this is a FRAGMENT, not the characterization. It says
transfer implies connection; it does not classify what the connection must
carry — that classification (`authority_normal_form`) exists only in the
finite causal vocabulary, where a causal order is available to state the
shapes. Lifting the full trichotomy to an abstract causal setting remains
open, exactly as Layer C's honest-scope note anticipated. -/

/-- Multi-step evolution: the reflexive-transitive closure of `step`.
DERIVED from the existing signature — not a new primitive. -/
inductive StepChain (S : AuthoritySystem D) : S.Config → S.Config → Prop
  | refl (c : S.Config) : StepChain S c c
  | tail {c₁ c₂ c₃ : S.Config} {d : D} :
      StepChain S c₁ c₂ → S.step c₂ d c₃ → StepChain S c₁ c₃

/-- Chains preserve reachability. -/
theorem StepChain.reachable_of {S : AuthoritySystem D}
    {c₁ c₂ : S.Config} (h : StepChain S c₁ c₂) (hr : S.reachable c₁) :
    S.reachable c₂ := by
  induction h with
  | refl => exact hr
  | tail _ hs ih => exact S.step_reachable _ _ _ ih hs

/-- Persistence under total partition: along any chain, a live domain
either stays live (each disconnected step is absorbed by `frozen_live`) or
has consumed — its receipt is in the record. -/
theorem live_persists {S : AuthoritySystem D}
    (hdis : ∀ c, S.reachable c → ∀ d₁ d₂ : D, d₁ ≠ d₂ → S.disconnected c d₁ d₂)
    {c₁ c₂ : S.Config} {d₁ : D} (hchain : StepChain S c₁ c₂)
    (hr : S.reachable c₁) (hlive : S.live c₁ d₁) :
    S.live c₂ d₁ ∨ d₁ ∈ S.receipts c₂ := by
  induction hchain with
  | refl => exact Or.inl hlive
  | @tail cb cc d hchain' hs ih =>
    have hrb : S.reachable cb := hchain'.reachable_of hr
    rcases ih with hl | hrcpt
    · by_cases hd : d = d₁
      · subst hd
        right
        rw [S.receipts_step _ _ _ hs]
        exact Finset.mem_insert_self _ _
      · left
        exact S.frozen_live cb d d₁ cc (hdis cb hrb d d₁ hd) hs hl
    · right
      rw [S.receipts_step _ _ _ hs]
      exact Finset.mem_insert_of_mem hrcpt

/-- **No silent handoff (the abstract normal-form fragment).** In a safe
system under total partition, the live domain never changes along any
evolution: live `d₁` at `c₁` and live `d₂` at any chain-successor `c₂`
forces `d₁ = d₂`. Either `d₁`'s enablement persisted (then v0's
amalgamation fires at `c₂`), or `d₁` consumed (then firing `d₂` lands a
second receipt). Authority transfer between permanently disconnected
domains is impossible. -/
theorem no_silent_handoff (S : AuthoritySystem D) (hsafe : Safe S)
    (hdis : ∀ c, S.reachable c → ∀ d₁ d₂ : D, d₁ ≠ d₂ → S.disconnected c d₁ d₂)
    {c₁ c₂ : S.Config} {d₁ d₂ : D} (hr : S.reachable c₁)
    (hchain : StepChain S c₁ c₂) (h₁ : S.live c₁ d₁) (h₂ : S.live c₂ d₂) :
    d₁ = d₂ := by
  by_contra hne
  have hr₂ : S.reachable c₂ := hchain.reachable_of hr
  rcases live_persists hdis hchain hr h₁ with hl | hrcpt
  · exact no_disconnected_double_availability S hsafe hr₂ hne
      (hdis c₂ hr₂ d₁ d₂ hne) ⟨hl, h₂⟩
  · obtain ⟨c₃, hs⟩ := S.step_live c₂ d₂ h₂
    have hr₃ : S.reachable c₃ := S.step_reachable _ _ _ hr₂ hs
    have hrec : S.receipts c₃ = insert d₂ (S.receipts c₂) :=
      S.receipts_step _ _ _ hs
    have hsub : ({d₁, d₂} : Finset D) ⊆ S.receipts c₃ := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · rw [hrec]
        exact Finset.mem_insert_of_mem hrcpt
      · rw [Finset.mem_singleton] at hx'
        subst hx'
        rw [hrec]
        exact Finset.mem_insert_self _ _
    have h2le : 2 ≤ (S.receipts c₃).card := by
      calc 2 = ({d₁, d₂} : Finset D).card := (Finset.card_pair hne).symm
        _ ≤ (S.receipts c₃).card := Finset.card_le_card hsub
    have := hsafe c₃ hr₃
    omega

/-- **A handoff needs a connected moment (contrapositive corollary).** If
live authority DID move across a chain in a safe system, then some
reachable configuration had a connected pair of distinct domains — the
communication that carried the handoff. The abstract shadow of the causal
relinquish witness. -/
theorem handoff_needs_connection (S : AuthoritySystem D) (hsafe : Safe S)
    {c₁ c₂ : S.Config} {d₁ d₂ : D} (hr : S.reachable c₁)
    (hchain : StepChain S c₁ c₂) (h₁ : S.live c₁ d₁) (h₂ : S.live c₂ d₂)
    (hne : d₁ ≠ d₂) :
    ∃ c, S.reachable c ∧ ∃ e₁ e₂ : D, e₁ ≠ e₂ ∧ ¬ S.disconnected c e₁ e₂ := by
  by_contra h
  push_neg at h
  exact hne (no_silent_handoff S hsafe h hr hchain h₁ h₂)

end Crdt.AuthorityFrontier
