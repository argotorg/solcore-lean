import Solcore.Frontend.ClosedSourceShortCircuitProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties

/- Semantic negative consumers. A successful non-Bool left witness
excludes every whole-expression endpoint before soundness is used for all depths.
Right syntax, lexical inputs and complete stores have no additional restrictions.
This includes every non-Bool RuntimeValue, including arbitrary source closures.
No typing, projection, termination, exact-depth or canonical-runtime claim. -/
set_option autoImplicit false
open Solcore Solcore.Frontend

namespace Tests.ClosedShortCircuitNegative

/-- A non-Bool left result excludes every conjunction value and final store. -/
theorem logicalAnd_nonBool_left_has_no_success
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore leftStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {leftValue : RuntimeValue}
    (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
      initialStore left leftValue leftStore)
    (notBool : ∀ b : Bool, leftValue ≠ .bool b) :
    ∀ value finalStore,
      ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ value finalStore := by
  intro value finalStore evaluated
  rcases closedSourceExpressionEvaluates_logicalAnd_iff.mp evaluated with
    ⟨_, forcedLeft⟩ | ⟨middleStore, forcedLeft, _⟩
  · exact notBool false (leftEvaluation.deterministic forcedLeft).1
  · exact notBool true (leftEvaluation.deterministic forcedLeft).1

/-- A non-Bool left result excludes every disjunction value and final store. -/
theorem logicalOr_nonBool_left_has_no_success
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore leftStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {leftValue : RuntimeValue}
    (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
      initialStore left leftValue leftStore)
    (notBool : ∀ b : Bool, leftValue ≠ .bool b) :
    ∀ value finalStore,
      ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ value finalStore := by
  intro value finalStore evaluated
  rcases closedSourceExpressionEvaluates_logicalOr_iff.mp evaluated with
    ⟨_, forcedLeft⟩ | ⟨middleStore, forcedLeft, _⟩
  · exact notBool true (leftEvaluation.deterministic forcedLeft).1
  · exact notBool false (leftEvaluation.deterministic forcedLeft).1

/-- Every-depth rejection follows from semantic impossibility, not one failed run. -/
theorem logicalAnd_nonBool_left_none_at_every_depth
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore leftStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {leftValue : RuntimeValue}
    (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
      initialStore left leftValue leftStore)
    (notBool : ∀ b : Bool, leftValue ≠ .bool b) :
    ∀ budget,
      evaluateClosedSourceExpression? budget owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ = none := by
  intro budget
  cases accepted : evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ with
  | none => rfl
  | some endpoint =>
      rcases endpoint with ⟨value, finalStore⟩
      exact False.elim
        (logicalAnd_nonBool_left_has_no_success leftEvaluation notBool value finalStore
          (evaluateClosedSourceExpression?_sound accepted))

/-- Every-depth disjunction rejection uses the same all-endpoint source argument. -/
theorem logicalOr_nonBool_left_none_at_every_depth
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore leftStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {leftValue : RuntimeValue}
    (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
      initialStore left leftValue leftStore)
    (notBool : ∀ b : Bool, leftValue ≠ .bool b) :
    ∀ budget,
      evaluateClosedSourceExpression? budget owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ = none := by
  intro budget
  cases accepted : evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ with
  | none => rfl
  | some endpoint =>
      rcases endpoint with ⟨value, finalStore⟩
      exact False.elim
        (logicalOr_nonBool_left_has_no_success leftEvaluation notBool value finalStore
          (evaluateClosedSourceExpression?_sound accepted))

end Tests.ClosedShortCircuitNegative
