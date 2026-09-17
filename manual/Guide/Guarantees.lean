import VersoManual
import Solcore.Core.Safety
import Solcore.Core.Check
import Solcore.Core.FuelResumptionProperties
import Solcore.Resolved.EvaluationProperties
import Solcore.Semantics.WorldStateStorageReadWriteProperties
import Solcore.Semantics.TransactionJournalProperties

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "A map of the proven guarantees" =>
%%%
tag := "guarantees"
file := "guarantees"
%%%

This chapter is a guide to proof families, organized by the question a reader
wants answered. It is not a count of theorem names: ten helper lemmas need not
cover a broader behavior than one carefully stated correspondence theorem.
The detailed implementation ledger remains
[Current status](https://github.com/Y-Nak/solcore-lean/blob/main/docs/CURRENT_STATUS.md).

# Does the checker recognize the typing rules?

*Guarantee:* successful diagnostic checking at the declared result type is
equivalent to declarative program validity in the supplied context.
*Boundary:* the program's data definitions, result type, and body typing.
*Anchor:*
{name Solcore.Core.Program.checkDetailedIn_iff_wellTyped}`Program.checkDetailedIn_iff_wellTyped`.
This does not establish intended business behavior or contract admission.
See {ref "checking-a-program"}[checking].

# Does the machine implement evaluation?

*Guarantee:* a completed initial-state machine run is a declarative evaluation
with the same value and store; any such evaluation has sufficient executable
fuel. *Boundary:* the specified environment and initial local store.
*Anchors:*
{name Solcore.Core.runStateful_evaluation_sound}`runStateful_evaluation_sound`
and
{name Solcore.Core.evaluation_runStateful_complete_with_sufficient_fuel}`evaluation_runStateful_complete_with_sufficient_fuel`.
See {ref "execution"}[execution and fuel].

# Can evaluation disagree with itself?

*Guarantee:* two evaluations from identical inputs agree on both their value
and final store. *Boundary:* this relation and these inputs, rather than two
different machines with an unstated correspondence.
*Anchor:* {name Solcore.Core.evaluation_deterministic}`evaluation_deterministic`.
Machine transition determinism supplies the corresponding stepwise property.

# What failures does typing exclude?

*Guarantee:* typed machine states preserve their typing and cannot produce a
raw machine fault. *Boundary:* matching values, continuation, store, and data
definitions, as required by the particular typing judgment.
*Anchor:*
{name Solcore.Core.well_typed_runStateful_never_faults}`well_typed_runStateful_never_faults`.
The pure closed fragment also has termination and sufficient-fuel results.
Contract reverts, host failures, and budget exhaustion are different outcomes.

# Is pausing and resuming faithful?

*Guarantee:* continuing the actual exhausted state is equal to a single run
with the combined budget. *Boundary:* the checkpoint must be the one the
first run returned. *Anchor:*
{name Solcore.Core.runStateful_resume}`runStateful_resume`.
Exact residual-cost results additionally assume a known path to a final state.
The runtime has corresponding resumption laws for its richer saved contexts.

# Do primitive and derived operations mean what they say?

Word arithmetic families establish modular, signed, bitwise, shift, byte,
comparison, and conversion laws. Evaluation lemmas additionally track operand
order, exactly-once evaluation, faults, and final stores. Renaming and weakening
lemmas establish how builders interact with environments. These are distinct
obligations: a commutativity law on Word values is not permission to reorder
effectful expressions. See {ref "core-language"}[the expression language].

# Does adding or renaming a binding preserve meaning?

Renaming, weakening, insertion, and scope-extension families relate changed
contexts, expressions, runtime values, environments, and stores. Binder handling
and closure environments are part of their premises and conclusions. Exact
value equality is available for selected ground fragments; richer values may
need an explicit relation. See {ref "frontend"}[names and lowering].

# Does lowering preserve a source computation?

*Guarantee:* successful lowering of the local resolved fragment gives
bidirectional evaluation correspondence with positional Core.
*Boundary:* the named scope and value environment correspond, and lowering
exists. *Anchor:*
{name Solcore.Resolved.Lowers.evaluates_iff}`Lowers.evaluates_iff`.
This local theorem must not be reported as general whole-source compiler
correctness. The broader frontend includes executable checked carriers and
restricted linking with a different current proof boundary.

# What is proven directly about source evaluation?

The callback-free source expression and body evaluators have soundness,
eventual completeness given a source evaluation, and determinism results.
Compositional body families additionally connect child contracts to typing,
Core paths, and exact costs. Their scope, owner, fragment, and child-contract
premises matter. See {ref "source-semantics"}[proven source fragments] and
{ref "source-types"}[the executable type-system boundary].

# What do the parser theorems establish?

The syntax proof families cover source ownership and span validity, executable
progress and totality, and correspondence with ordinary grammar relations for
specified Core, Yul, declaration, and file boundaries. AST and endpoint
exactness need not include full diagnostic-trace equality. A recovered output
need not be diagnostic-free. These are parsing guarantees, not typing or
execution guarantees. Follow the {ref "frontend"}[frontend discussion] for the
remaining boundary and reference links.

# Which state changes can be observed?

*Guarantee:* successful storage writes are read back at the selected slot,
and unrelated slots or addresses retain their observations.
*Boundary:* account presence and the required slot/address inequalities.
*Anchor:*
{name Solcore.Semantics.WorldState.readStorage?_writeStorage?_same}`WorldState.readStorage?_writeStorage?_same`
and its isolation companions. Balance, nonce, code, and world-update families
provide their own observation laws; a storage law alone says nothing about
every other account field.

# What survives failure?

Frame and root execution families distinguish working from selected state,
rollback effects from traces, nested outcomes from root disposition, and
preflight rejection from execution. Return selects working state; root revert
and trap select the checkpoint. Journal laws retain order and duplicates:
{name Solcore.Semantics.TransactionJournal.logList_record_two}`TransactionJournal.logList_record_two`.
See {ref "contracts"}[contracts and rollback] for the trap-policy distinction.

# What makes test inputs trustworthy?

Checked generation and shrinking retain typing and fragment admission evidence.
Shrink candidates carry a strict complexity decrease. Wire and protocol
families preserve closed version boundaries and validate their exact envelopes.
These guarantees support reproducible testing; they do not prove an external
compiler or prove that a shrink preserves an arbitrary failure predicate.
See {ref "oracle"}[Oracle experiments].

# What remains outside these guarantees?

The model does not currently establish general end-to-end preservation from
Solcore source through a Rust or Haskell compiler to EVM execution. Broader
source forms, general recursive linking and calls, richer ABI behavior,
physical EVM memory and bytecode refinement, and gas or fork-specific behavior
need their own stated boundaries. An implemented internal feature is also not
automatically part of every published protocol.

Proofs are checked by Lean under its foundations. The repository's source-policy
scan rejects designated escape hatches; compiled theorem dependency reports
answer a different trust question. English explanations and the choice of
specification itself still require human review.
