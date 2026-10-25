# Hull meaning preservation

## Completion rule

A feature is connected when its independent `Semantics` derivation reaches the
actual `compile` / `ScalarExecution.prepare` implementation and the public
`run` / `resume` API. Its theorem must relate the result, language-fault reason
and represented source heap. Compiler output, function installation, argument
initialization and loop closures must come from the implementation, rather than
from an assumed body-preservation premise.

Helper lemmas count as intermediate work. Each implementation step should end
with a public theorem consumer, an executable regression, verification and a
commit.

## Current public theorem

`Correspondence.prepare_recursive_program_resumes` relates every genuine finite
chain of resumptions to an independent finite Hull function evaluation. It
preserves values and language faults, including all allocations and writes made
before failure. Completion occurs exactly when cumulative fuel reaches the
transition count; otherwise the computation remains resumable.

The theorem requires successful preparation, `RecursiveProgram` syntactic
eligibility and a finite independent source evaluation. It accepts any source
result: value representation and exclusion of malformed source observations
follow from the proof. Actual compilation and initialization establish scope
coverage, parameter arity and the typed heap relation. Successful builtin
compilation supplies the required argument constraints. No separate
`SafeResult` premise is required.

Public inputs use the existing scalar parser. The theorem does not assert
termination or specify concrete external effects.

The connected fragment includes structural values, pure builtins, recursive
named calls, local variables, blocks, loops and control transfers, product-path
assignments and pattern alternatives. Language fault propagation is connected
through expressions, argument evaluation, function boundaries and every loop
stage (`2b7a07347`).

## Priorities

| Priority | Theorem / connection | Completion evidence | Status |
| --- | --- | --- | --- |
| 1 | Product-path assignment preserves the result and heap, including failed RHS calls. | The common recursive public theorem covers nested places; source/public/runtime consumers cover successful writes and faults. | Connected |
| 1 | Pattern matching preserves arm selection, binder allocation and control outcomes. | Actual `testPattern` and `lowerAlternatives` feed the mutual derivation proof and public resumptions, including skipped arms and faults. | Connected |
| 2 | Accepted initialization and execution exclude malformed source observations. | Actual globals, parameter binding, locals and match binders supply scope coverage; compiler checks and typed heaps exclude malformed observations. The public theorem has no outcome-safety premise. | Connected |
| 3 | Concrete external state is preserved. | Independent memory, storage, environment and log semantics relate to the emitted Core code and public contract state. | Open |
| 4 | External calls, creation and rollback preserve observable outcomes. | Returned data, balances, storage, receipts and rollback are related through actual execution and resumption. | Open |
| 4 | Assembly preserves its independent meaning. | Yul statement derivations connect to actual lowering and public execution, reusing the concrete effect relations. | Open |
| 5 | Divergence and reverse correspondence. | Relate nontermination and characterize Core outcomes after terminating execution and effects are covered. | Open |

Priorities 1 and 2 close gaps in the existing pure Hull theorem. Priorities 3
and 4 connect the remaining observable runtime behavior. Priority 5 should not
delay those connections.

## Next public milestone

Connect concrete external state to the public theorem. Start with storage and
memory operations, then environment reads and logs. Define their independent
Hull effects and relate them to the actual Core context and returned state.
The proof must include writes before a language fault and state carried across
resumptions. Once these state relations are connected, use them for external
calls, creation, rollback and assembly.

## Verification

- Build the affected theorem modules and the full test executable.
- Run independent-source public consumers and the complete test suite.
- Check the semantic-kernel declaration policy and the public theorem's axioms.
- Record actual ambiguities or upstream bugs in the ignored `questions.md`.
- Delete disposable proof checks and verification logs after use.
