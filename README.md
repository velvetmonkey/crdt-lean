# crdt-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](Crdt)

**crdt-lean: Formal Proofs of State-based CRDT Convergence in Lean 4**

Lean 4 formal proofs that state-based CRDTs (CvRDTs) converge: **Strong Eventual Consistency** (replicas that delivered the same set of updates hold equal state, regardless of order or redelivery), **conditional liveness** (under an explicit fairness assumption every replica eventually reaches — and stays at — the join of all updates), and concrete instances (**G-Set**, **G-Counter**, **PN-Counter**) proven to be lawful CvRDT carriers that inherit those guarantees for free.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## Why it matters

A CvRDT is the AP-side answer to replicated state: nodes gossip their full state and merge, and the datatype is designed so that merging always converges without coordination, quorums, or a total order. The convergence guarantee rests on one algebraic fact — the state space is a **join-semilattice** and merge is the **join** — so order, duplication, and concurrency of delivery are quotiented away. This library machine-checks that guarantee and then discharges it for datatypes you would actually ship, so the abstract theorem is anchored to concrete objects rather than left as an assumption.

It is the discrete, asynchronous sibling of the continuous consensus result in [kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean): where Kuramoto certifies phase synchrony of coupled oscillators, this certifies state convergence of gossiping replicas.

## Setting

A state-based CRDT carrier is a `SemilatticeSup S` with `OrderBot S` and `DecidableEq S`: `⊥` is the initial state, `merge a b := a ⊔ b` is the join. A replica's observable state after delivering a finite set `updates : Finset S` is `replicaState updates := updates.sup id`, and a delivery stream is a `List S` folded with `merge` from `⊥`. The bridge lemma collapses any such fold to the join over the *delivered set*, which is what makes SEC immediate.

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `merge_comm` / `merge_assoc` / `merge_idem` | The three Shapiro CvRDT conditions (commutative, associative, idempotent merge) |
| 2 | `merge_bot` | `⊥` is the identity for merge (initial state) |
| 3 | `le_merge_left` / `le_merge_right` | Merge is inflationary: a replica never moves down the lattice |
| 4 | `replicaState_insert` / `replicaState_empty` | Observable state as join over the delivered set |
| 5 | `fold_merge_eq_replicaState` | Any delivery order/multiplicity collapses to the join over the delivered *set* |
| 6 | `strong_eventual_consistency` | Same delivered set ⇒ equal folded state (the headline SEC guarantee) |
| 7 | `replicaState_redeliver` | Redelivering a known update is a no-op (set-level idempotence) |
| 8 | `le_replicaState` / `replicaState_le` | Converged state is the least upper bound of the delivered set |
| 9 | `replicaState_mono` | Delivery is monotone: more updates only move a replica up |
| 10 | `merge_replicaState` | Gossip step: merging two replicas = replica of the union of deliveries |
| 11 | `eventually_covers` | Monotone delivery + each-update-eventually-arrives ⇒ whole finite set eventually present |
| 12 | `DeliverySystem.converges` | Under fairness + quiescence, each replica reaches `allUpdates` and stays |
| 13 | `DeliverySystem.reaches_converged` | Each replica's state eventually equals the join of all updates |
| 14 | `DeliverySystem.eventual_agreement` | Any two replicas eventually hold identical state, forever after some finite T |
| 15 | G-Set / G-Counter / PN-Counter | Each proven a lawful CvRDT carrier, inheriting SEC + eventual agreement; with monotone semantic reads |
| 16 | `ORSet.add_wins` | **Add-wins**: a fresh add merged with a concurrent remove of the same element leaves it present — the defining OR-Set property, and the case a 2P-Set gets wrong |
| 17 | `ORSet.remove_lookup_false` | Absent a concurrent add, remove genuinely removes (every observed token tombstoned) |
| 18 | `ORSet.add_lookup` | A fresh add makes the element present |

## The honest boundary

Liveness is **conditional**, by necessity: you cannot prove a network delivers messages. The `DeliverySystem` structure carries fairness (every generated update eventually reaches every replica) and quiescence (the update set is finite and fixed) as **asserted fields**, not derived facts. That is the line between what Lean certifies (given fair delivery, replicas converge and agree) and what the network layer must guarantee (fair delivery). G-Set/G-Counter/PN-Counter are the *easy* lattices; the **OR-Set** is the genuinely subtle one — its `add_wins` theorem machine-checks the concurrent add-beats-remove behaviour a 2P-Set gets wrong. Sequence CRDTs (RGA) are the next frontier.

CRDT convergence is **not** distributed consensus in the Paxos/Raft sense: CvRDTs converge precisely by *avoiding* consensus (no quorum, no total order, AP not CP). The word "consensus" here is used in the convergence sense, as in the Kuramoto control literature, not the FLP/quorum sense.

## Project structure

```
Crdt/
├── Defs.lean         — merge (= join), the three CvRDT conditions, replicaState
├── Convergence.lean  — fold_merge_eq_replicaState, strong_eventual_consistency (safety half of SEC)
├── Liveness.lean     — eventually_covers, DeliverySystem, eventual_agreement (the "Eventual" half)
├── Instances.lean    — G-Set, G-Counter, PN-Counter as lawful CvRDT carriers
└── ORSet.lean        — Observed-Remove Set: add-wins semantics over a product of grow-only sets
```

## Building

```bash
lake exe cache get   # fetch Mathlib build cache
lake build
```

Requires the Lean toolchain pinned in `lean-toolchain` (v4.28.0) and Mathlib v4.28.0 (pinned in `lakefile.toml`).

## Related

Part of the [velvetmonkey Lean 4 proof corpus](https://velvetmonkey.github.io/lean/). Sibling to [kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean) (continuous consensus) and the [mcp-seal](https://github.com/velvetmonkey/mcp-seal) verified-agent-kernel line.
