import Solcore.Syntax.DeclarativeCoreTypeExactnessProperties
import Solcore.Syntax.DeclarativeFunctionParameterPublicOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionParameterRecoveryExactnessProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact values for recovery-aware named function parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem comptimePrefixAbsent_conflicts_exactValue
    {input afterMarker afterName : Remainder} {markerSpan : SourceSpan}
    {name : Syntax.Identifier}
    (absent : ComptimeParameterPrefixAbsentAt input)
    (markerParsed : ExactTokenParses
      (.identifier ContextualKeyword.comptime.spelling)
      input markerSpan afterMarker)
    (nameParsed : IdentifierParses afterMarker name afterName) : False := by
  apply absent
  refine ⟨markerSpan, name.span, name.value, markerParsed.1, ?_⟩
  simpa [markerParsed.2] using nameParsed.1

/-- With fixed accumulated fields, a parameter tail fixes its AST and final
remainder. -/
theorem FunctionParameterTailOrdinaryParses.result_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {start : SourceSpan} {marker : Option SourceSpan}
    {name : Syntax.Identifier} {errorSpan : SourceSpan}
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterTailOrdinaryParses typeOrdinary start
      marker name errorSpan input left afterLeft)
    (rightParsed : FunctionParameterTailOrdinaryParses typeOrdinary start
      marker name errorSpan input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | typed leftColonSpan leftColon leftType =>
      cases rightParsed with
      | typed rightColonSpan rightColon rightType =>
          rcases leftColon.result_unique rightColon with
            ⟨colonSpanEq, afterColonEq⟩
          subst colonSpanEq
          subst afterColonEq
          rcases typeOutcomes.successResultUnique leftType rightType with
            ⟨typeEq, outputEq⟩
          subst typeEq
          exact ⟨rfl, outputEq⟩
      | typeMissing rightColonAbsent =>
          exact False.elim
            (typeTokenAbsent_conflicts_token rightColonAbsent leftColon.1)
  | typeMissing leftColonAbsent =>
      cases rightParsed with
      | typed rightColonSpan rightColon rightType =>
          exact False.elim
            (typeTokenAbsent_conflicts_token leftColonAbsent rightColon.1)
      | typeMissing => exact ⟨rfl, rfl⟩

/-- With fixed accumulated fields, a parameter tail fixes its AST. -/
theorem FunctionParameterTailOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {start : SourceSpan} {marker : Option SourceSpan}
    {name : Syntax.Identifier} {errorSpan : SourceSpan}
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterTailOrdinaryParses typeOrdinary start
      marker name errorSpan input left afterLeft)
    (rightParsed : FunctionParameterTailOrdinaryParses typeOrdinary start
      marker name errorSpan input right afterRight) : left = right :=
  (leftParsed.result_unique typeOutcomes rightParsed).1

/-- Non-recovering named-parameter success fixes its AST and final
remainder. -/
theorem FunctionParameterCoreOrdinaryParses.result_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterCoreOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : FunctionParameterCoreOrdinaryParses typeOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | ordinary leftAbsent leftName leftTail =>
      cases rightParsed with
      | ordinary rightAbsent rightName rightTail =>
          rcases leftName.result_unique rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          exact leftTail.result_unique typeOutcomes rightTail
      | comptime markerSpan rightMarker rightName rightTail =>
          exact False.elim
            (comptimePrefixAbsent_conflicts_exactValue leftAbsent rightMarker
              rightName)
  | comptime markerSpan leftMarker leftName leftTail =>
      cases rightParsed with
      | ordinary rightAbsent rightName rightTail =>
          exact False.elim
            (comptimePrefixAbsent_conflicts_exactValue rightAbsent leftMarker
              leftName)
      | comptime rightMarkerSpan rightMarker rightName rightTail =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          rcases leftName.result_unique rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          exact leftTail.result_unique typeOutcomes rightTail

/-- Non-recovering named-parameter success fixes its AST. -/
theorem FunctionParameterCoreOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterCoreOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : FunctionParameterCoreOrdinaryParses typeOrdinary input right
      afterRight) : left = right :=
  (leftParsed.result_unique typeOutcomes rightParsed).1

/-- A recovery-aware named parameter fixes its AST and final remainder. -/
theorem FunctionParameterOrdinaryParses.result_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input left afterLeft)
    (rightParsed : FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input right afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact leftCore.result_unique typeOutcomes rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (functionParameterCoreDeterministicOutcomeSpec
              typeOutcomes.toDeterministicOutcomeSpec
              |>.successRejectDisjoint coreRejected ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (functionParameterCoreDeterministicOutcomeSpec
              typeOutcomes.toDeterministicOutcomeSpec
              |>.successRejectDisjoint coreRejected ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.result_unique rightRecovery

/-- A recovery-aware named parameter fixes its AST. -/
theorem FunctionParameterOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input left afterLeft)
    (rightParsed : FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input right afterRight) : left = right :=
  (leftParsed.result_unique typeOutcomes rightParsed).1

/-- Public named-parameter rejection has one nonconsuming endpoint. -/
theorem FunctionParameterRejects.output_unique
    {typeRejects : Remainder → Remainder → Prop}
    {input left right : Remainder}
    (leftRejected : FunctionParameterRejects typeRejects input left)
    (rightRejected : FunctionParameterRejects typeRejects input right) :
    left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Recovery-aware named parameters preserve exact child outcomes. -/
theorem functionParameterExactOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects) :
    ExactDeterministicOutcomeSpec
      (FunctionParameterOrdinaryParses typeOrdinary typeRejects)
      (FunctionParameterRejects typeRejects) where
  toDeterministicOutcomeSpec :=
    functionParameterDeterministicOutcomeSpec
      typeOutcomes.toDeterministicOutcomeSpec
  successValueUnique := FunctionParameterOrdinaryParses.value_unique
    typeOutcomes
  rejectOutputUnique := FunctionParameterRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
