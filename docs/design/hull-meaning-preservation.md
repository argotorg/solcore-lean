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

The theorem currently requires successful preparation, `RecursiveProgram`
syntactic eligibility and `SafeResult` for the source result. `SafeResult`
includes values and `.fault (.language reason)`. Malformed source observations
such as an absent variable are outside that result relation. The theorem does
not assert termination or specify concrete external effects.

The connected fragment includes structural values, pure builtins, recursive
named calls, local variables, blocks, loops and control transfers. Language
fault propagation is connected through expressions, argument evaluation,
function boundaries and every loop stage (`2b7a07347`).

## Priorities

| Priority | Theorem / connection | Completion evidence | Status |
| --- | --- | --- | --- |
| 1 | Product-path assignment preserves the result and heap, including failed RHS calls. | The common recursive public theorem covers nested places; source/public/runtime consumers cover successful writes and faults. | Next |
| 1 | Pattern matching preserves arm selection, binder allocation and control outcomes. | Actual `testPattern` and `lowerAlternatives` feed the mutual derivation proof and public resumptions, including skipped arms and faults. | Next |
| 2 | Accepted initialization and execution exclude malformed source observations. | Derive scope coverage and representation invariants from actual globals, parameters, locals and match binders; remove the public `SafeResult` assumption where justified. | Open |
| 3 | Concrete external state is preserved. | Independent memory, storage, environment and log semantics relate to the emitted Core code and public contract state. | Open |
| 4 | External calls, creation and rollback preserve observable outcomes. | Returned data, balances, storage, receipts and rollback are related through actual execution and resumption. | Open |
| 4 | Assembly preserves its independent meaning. | Yul statement derivations connect to actual lowering and public execution, reusing the concrete effect relations. | Open |
| 5 | Divergence and reverse correspondence. | Relate nontermination and characterize Core outcomes after terminating execution and effects are covered. | Open |

Priorities 1 and 2 close gaps in the existing pure Hull theorem. Priorities 3
and 4 connect the remaining observable runtime behavior. Priority 5 should not
delay those connections.

## Verification

- Build the affected theorem modules and the full test executable.
- Run independent-source public consumers and the complete test suite.
- Check the semantic-kernel declaration policy and the public theorem's axioms.
- Record actual ambiguities or upstream bugs in the ignored `questions.md`.
- Delete disposable proof checks and verification logs after use.
