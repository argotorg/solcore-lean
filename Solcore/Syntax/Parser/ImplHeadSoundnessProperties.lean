import Solcore.Syntax.Parser.DelimitedSoundnessProperties
import Solcore.Syntax.Parser.Impl
import Solcore.Syntax.Parser.SignatureLeafDiagnosticReflectionProperties
import Solcore.Syntax.Parser.TypeDiagnosticReflectionProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-! Parser-independent soundness for implementation declaration head leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ImplInternals

/-- Optional `default` parsing cannot erase an incoming diagnostic. -/
theorem implDefaultMarker_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess implDefaultMarker := by
  unfold implDefaultMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess .defaultKw .topItem)
    intro marker
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/-- Optional `default` success preserves keyword priority and exact state. -/
theorem implDefaultMarker_success_sound {input next : State}
    {marker : Option SourceSpan}
    (result : implDefaultMarker input = .ok marker next) :
    DeclarativeGrammar.OptionalImplDefaultMarkerParses
      input.declarativeRemainder marker next.declarativeRemainder := by
  unfold implDefaultMarker getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    cases markerResult : keyword .defaultKw .topItem input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok token afterMarker =>
        simp only [markerResult, pure] at result
        cases result
        exact .present token.span
          (keyword_success_exactTokenParses .defaultKw .topItem markerResult)
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (keywordAbsentAt_of_isKeyword_eq_false .defaultKw absent)

/-- Requiring head arguments cannot erase diagnostics on a successful branch. -/
theorem requireImplArguments_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList TypeExpr) :
    Parser.ReflectsDiagnosticFreeOnSuccess (requireImplArguments values) := by
  unfold requireImplArguments
  cases values.elements with
  | nil =>
      intro input value next result diagnosticFree
      contradiction
  | cons head tail => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Requiring nonempty head arguments preserves state, span, and source order. -/
theorem requireImplArguments_success_shape
    {values : DelimitedList TypeExpr} {input next : State}
    {arguments : NonemptyDelimitedList TypeExpr}
    (result : requireImplArguments values input = .ok arguments next) :
    next = input ∧ arguments.span = values.span ∧
      arguments.elements.toList = values.elements := by
  unfold requireImplArguments at result
  cases elements : values.elements with
  | nil => rw [elements] at result; contradiction
  | cons head tail =>
      rw [elements] at result
      cases result
      exact ⟨rfl, rfl, by simp [NonemptyList.toList]⟩

/-- The delimited and nonempty stages yield exact implementation arguments. -/
theorem implHeadArguments_success_sound
    {input afterValues next : State} {values : DelimitedList TypeExpr}
    {arguments : NonemptyDelimitedList TypeExpr}
    (valuesResult : delimited .less .greater false typeExpr .typeExpr
      .topLevel input = .ok values afterValues)
    (argumentsResult : requireImplArguments values afterValues =
      .ok arguments next) :
    DeclarativeGrammar.ImplHeadArgumentsParses input.declarativeRemainder
      arguments next.declarativeRemainder := by
  have valuesGrammar := delimited_nonempty_trailing_success_sound
    .less .greater typeExpr DeclarativeGrammar.TypeExprParses
    .typeExpr .topLevel typeExpr_success_sound typeExpr_preservesTokenWindow
    valuesResult
  have shape := requireImplArguments_success_shape argumentsResult
  unfold DeclarativeGrammar.ImplHeadArgumentsParses
  rw [shape.1]
  simpa only [shape.2.1, shape.2.2] using valuesGrammar

end ImplInternals

end Solcore.Syntax.Parser
