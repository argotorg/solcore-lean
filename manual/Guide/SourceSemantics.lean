import VersoManual
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.ClosedSourceEvaluatorCompletenessProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Proven source fragments and their boundaries" =>
%%%
tag := "source-semantics"
file := "source-semantics"
%%%

There is more proven source semantics than the local Resolved bridge alone.
The frontend contains families of restricted source-expression and body
relations, executable recognizers and evaluators, lowering results, and exact
cost theorems. Understanding their restrictions is more useful than treating
the entire frontend as either proven or unproven.

# Original syntax can have an independent meaning

{name Solcore.Frontend.ClosedSourceExpressionEvaluates}`ClosedSourceExpressionEvaluates`
and
{name Solcore.Frontend.ClosedSourceBodyEvaluates}`ClosedSourceBodyEvaluates`
relate original source expressions and bodies to values and stores. They retain
ownership, name tables, and ordered captured values. Source closures retain
source bodies and their lexical context, rather than being identified by their
printed lambda text alone.

Here “closed” means that the recursive judgments no longer require external
callbacks. It does not mean the lexical environment must be empty. Confusing
those two meanings would incorrectly strengthen the theorem's assumptions.

# What the executable evaluator guarantees

{name Solcore.Frontend.evaluateClosedSourceExpression?_sound}`evaluateClosedSourceExpression?_sound`
says that a successful bounded evaluation gives the independent source
evaluation relation with the same value and final store. The corresponding
body theorem provides the same direction for a body.

{name Solcore.Frontend.evaluateClosedSourceExpression?_eventually_complete}`evaluateClosedSourceExpression?_eventually_complete`
says that, given a derivation of this source evaluation, all sufficiently large
budgets produce its result. This is conditional on that derivation. It does
not claim that every arbitrary source expression terminates or is supported.

{name Solcore.Frontend.ClosedSourceExpressionEvaluates.deterministic}`ClosedSourceExpressionEvaluates.deterministic`
ensures two such evaluations agree on value and final store. Separate theorem
families address store preservation, environment ownership, and budget
monotonicity. These statements are about the independent source relation, not
merely running a Core evaluator twice.

# Composition requires child guarantees

Many source-body results are deliberately parameterized by the guarantees of
the child expressions they contain. A body with local bindings and terminal
returns can inherit typing, evaluation correspondence, and cost properties
only when its child elaborators and evaluators provide the required contracts.

A representative
[computation return-tree theorem](https://github.com/Y-Nak/solcore-lean/blob/main/Solcore/Frontend/ComputationReturnTreeRuntimeSafetyProperties.lean)
assumes child typing, membership in a suitable Core fragment, behavior under
weakening and insertion, evaluation correspondence, and compatible step costs.
With a matching typed runtime environment and store, its conclusion includes a
typed result, a well-typed final store, source evaluation, a Core path under
any continuation, and exact success/exhaustion thresholds.

That is a strong compositional theorem. The many child assumptions are the
reason it can be reused; they are not obligations that can be omitted when
summarizing it as “source execution is safe.”

# Relating the proof families to the active frontend

Restricted local, conditional, lambda, data, computation-body, and scope/owner
families establish particular bridges and admissibility boundaries. The newer
whole-program checking and specialization path has its own typed occurrences,
selected evidence, checked elaboration carriers, and linking restrictions.

These developments can share definitions and support one another without
already forming a single theorem about every program accepted by the current
whole-program checker. The remaining connection must identify the exact source
relation, admitted syntax, evidence interpretation, and target execution.

Use the detailed
[frontend status](https://github.com/Y-Nak/solcore-lean/blob/main/docs/CURRENT_STATUS.md)
to select the family matching a concrete program. A theorem with a familiar
name is useful only if its owner, scope, fragment, store, and budget assumptions
match that program's path through the model.
