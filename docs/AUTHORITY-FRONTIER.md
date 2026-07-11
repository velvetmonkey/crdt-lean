# The Authority Frontier: verified coordination-free authorization

A one-use approval handed to a fleet of agents cannot be spent twice, even across a network partition, without coordination. And any safe transfer of that authority has to go through a sealed handoff (or a genuine availability gap). Machine-checked in Lean 4, `Crdt/AuthorityFrontier.lean`.

## The claim, in one line

**Your one-shot approval provably cannot double-spend across a partition, and we have machine-checked exactly where coordination must live.**

## What is proven

| Result | Theorem | Status |
|---|---|---|
| **Necessity** (the impossibility): safety forces at most one live consumer at any reachable cut, over freely-replicable state (copyable bytes, grow-only receipts) | `authority_frontier_card_le_one` (via `no_disconnected_double_availability`) | Proven, **abstract** `AuthoritySystem`, on `main` |
| **A witnessed double-spend** when coordination is dropped | `double_consume_countermodel` | Proven, on `main` |
| **Sufficiency** (a pattern that works): if the sender seals its own consume before the receiver is enabled, the fleet is safe | `sealed_handoff_safe` | Proven, **finite `CutWorld` model**, branch `feat/sealed-handoff` |
| **A third safe shape**: safety can also come from causally sequencing the consumes (the sender's consume poisons the receiver's) | `wSeq_safe` + `wSeq_not_sealed_handoff` | Proven, same branch |

## The honest boundaries, stated not buried

- **Necessity is general; sufficiency is in-model.** The impossibility is proven for the abstract `AuthoritySystem` (any number of domains). The sufficiency (sealed handoff works) is proven in the finite `CutWorld` probe model, and is **not yet lifted** to the abstract system. Do not round "the pattern is safe in our model" up to "the pattern is safe, full stop."
- **The safe-transfer taxonomy is richer than two shapes.** The original "handoff or gap" conjecture is incomplete: `wSeq` is a third safe shape (consume-sequencing). Recorded, not hidden.
- **The naive "gap" disjunct is vacuous** (`gap_vacuous`): "there exists a cut where nobody is live" is trivially true at the empty cut, so a `Safe ⟺ handoff∨gap` biconditional would collapse to `Safe ⟺ True`. We prove sufficiency of the sealed handoff and make no biconditional claim.
- **This is a result about the model.** Whether it applies to the deployed [[seal]] gate is a separate applicability bridge (in progress): instantiating `AuthoritySystem` with SealV2's real nonce model.
- **No novelty beyond invariant-confluence / escrow-CRDT.** The necessity is a corollary of known distributed-systems theory (Bailis invariant confluence; O'Neil / Balegas escrow), here made machine-checked and given a named abstraction. Not Byzantine, not crash-recovery, not cryptographic.

## Who this is for

Agent fleets, multi-node MCP deployments, offline-first approval flows. The competitor-can't-say claim: a machine-checked boundary on where a distributed approval fabric *must* coordinate to stay single-use, with a witnessed counterexample for what happens when it doesn't.

## Where

`Crdt/AuthorityFrontier.lean`. Axiom footprint `{propext, Classical.choice, Quot.sound}`, zero `sorry`, no `native_decide`, pinned at compile time by the `axiom_check` gate.