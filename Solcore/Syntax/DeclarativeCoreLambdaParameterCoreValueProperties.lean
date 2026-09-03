import Solcore.Syntax.DeclarativeCoreLambdaParameterOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Successful-value functionality for the ordinary lambda-parameter core. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem lambdaParameter_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- At one fixed name, an inferred or typed suffix fixes its parameter AST. -/
theorem OrdinaryLambdaParameterTailOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {name : Syntax.Identifier} {input : Remainder}
    {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name
      input left afterLeft)
    (rightParsed : OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name
      input right afterRight) : left = right := by
  cases leftParsed with
  | inferred leftAbsent =>
      cases rightParsed with
      | inferred => rfl
      | typed rightSpan rightColon rightType =>
          exact False.elim
            (lambdaParameter_absent_conflicts_exact leftAbsent rightColon)
  | typed leftSpan leftColon leftType =>
      cases rightParsed with
      | inferred rightAbsent =>
          exact False.elim
            (lambdaParameter_absent_conflicts_exact rightAbsent leftColon)
      | typed rightSpan rightColon rightType =>
          have afterColonEq := leftColon.output_unique rightColon
          subst afterColonEq
          have typeEq := typeOutcomes.successValueUnique leftType rightType
          subst typeEq
          rfl

/-- The ordinary-name branch fixes its inferred or typed parameter value. -/
theorem OrdinaryLambdaParameterOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : OrdinaryLambdaParameterOrdinaryParses typeOrdinary input
      left afterLeft)
    (rightParsed : OrdinaryLambdaParameterOrdinaryParses typeOrdinary input
      right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftName leftTail =>
      cases rightParsed with
      | parsed rightName rightTail =>
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          exact leftTail.value_unique typeOutcomes rightTail

/-- The contextual-comptime branch fixes its typed or missing-type AST. -/
theorem ComptimeLambdaParameterOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : ComptimeLambdaParameterOrdinaryParses typeOrdinary input
      left afterLeft)
    (rightParsed : ComptimeLambdaParameterOrdinaryParses typeOrdinary input
      right afterRight) : left = right := by
  cases leftParsed with
  | typed leftMarkerSpan leftColonSpan leftMarker leftName leftColon
      leftType =>
      cases rightParsed with
      | typed rightMarkerSpan rightColonSpan rightMarker rightName
          rightColon rightType =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerEq, afterMarkerEq⟩
          subst markerEq
          subst afterMarkerEq
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          have afterColonEq := leftColon.output_unique rightColon
          subst afterColonEq
          have typeEq := typeOutcomes.successValueUnique leftType rightType
          subst typeEq
          rfl
      | typeMissing rightMarkerSpan rightMarker rightName rightAbsent =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact False.elim
            (lambdaParameter_absent_conflicts_exact rightAbsent leftColon)
  | typeMissing leftMarkerSpan leftMarker leftName leftAbsent =>
      cases rightParsed with
      | typed rightMarkerSpan rightColonSpan rightMarker rightName
          rightColon rightType =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact False.elim
            (lambdaParameter_absent_conflicts_exact leftAbsent rightColon)
      | typeMissing rightMarkerSpan rightMarker rightName rightAbsent =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerEq, afterMarkerEq⟩
          subst markerEq
          subst afterMarkerEq
          have nameEq := identifierExactOutcomeSpec.successValueUnique
            leftName rightName
          subst nameEq
          rfl

/-- Ordered comptime/ordinary dispatch fixes every successful Core value. -/
theorem LambdaParameterCoreOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterCoreOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : LambdaParameterCoreOrdinaryParses typeOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | comptime leftComptime =>
      cases rightParsed with
      | comptime rightComptime =>
          exact leftComptime.value_unique typeOutcomes rightComptime
      | ordinary rightAbsent rightOrdinary =>
          exact False.elim (rightAbsent leftComptime.startsAt)
  | ordinary leftAbsent leftOrdinary =>
      cases rightParsed with
      | comptime rightComptime =>
          exact False.elim (leftAbsent rightComptime.startsAt)
      | ordinary rightAbsent rightOrdinary =>
          exact leftOrdinary.value_unique typeOutcomes rightOrdinary

/-- A non-recovering lambda-parameter success fixes its AST and remainder. -/
theorem LambdaParameterCoreOrdinaryParses.result_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterCoreOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : LambdaParameterCoreOrdinaryParses typeOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique typeOutcomes rightParsed,
    leftParsed.output_unique typeOutcomes.toDeterministicOutcomeSpec
      rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
