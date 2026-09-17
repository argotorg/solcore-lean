import VersoManual
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.ClosedSourceEvaluatorCompletenessProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Frontend.ComputationReturnTreeRuntimeSafetyProperties

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

{includeDocstring Solcore.Frontend.ClosedSourceExpressionEvaluates}

# What the executable evaluator guarantees

{name Solcore.Frontend.evaluateClosedSourceExpression?_sound}`evaluateClosedSourceExpression?_sound`

{includeDocstring Solcore.Frontend.evaluateClosedSourceExpression?_sound}

{name Solcore.Frontend.evaluateClosedSourceExpression?_eventually_complete}`evaluateClosedSourceExpression?_eventually_complete`

{includeDocstring Solcore.Frontend.evaluateClosedSourceExpression?_eventually_complete}

{name Solcore.Frontend.ClosedSourceExpressionEvaluates.deterministic}`ClosedSourceExpressionEvaluates.deterministic`

{includeDocstring Solcore.Frontend.ClosedSourceExpressionEvaluates.deterministic}

# Composition requires child guarantees

Many source-body results are deliberately parameterized by the guarantees of
the child expressions they contain. A body with local bindings and terminal
returns can inherit typing, evaluation correspondence, and cost properties
only when its child elaborators and evaluators provide the required contracts.

{name Solcore.Frontend.ComputationReturnTreeElaborates.runtime_typed_execution}`ComputationReturnTreeElaborates.runtime_typed_execution`

{includeDocstring Solcore.Frontend.ComputationReturnTreeElaborates.runtime_typed_execution}

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
