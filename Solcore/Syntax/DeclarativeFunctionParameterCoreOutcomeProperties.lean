import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeFunctionParameterOutcomeGrammar

/-! Deterministic ordinary outcomes of non-recovering named parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem comptimePrefixAbsent_conflicts_exact
    {input afterMarker afterName : Remainder} {markerSpan : SourceSpan}
    {name : Syntax.Identifier}
    (absent : ComptimeParameterPrefixAbsentAt input)
    (markerParsed : ExactTokenParses
      (.identifier ContextualKeyword.comptime.spelling)
      input markerSpan afterMarker)
    (nameParsed : IdentifierParses afterMarker name afterName) : False := by
  apply absent
  refine ⟨markerSpan, name.span, name.value, markerParsed.1, ?_⟩
  have nameToken := nameParsed.1
  rw [markerParsed.2] at nameToken
  exact nameToken

/-- A named-parameter tail has one deterministic final remainder. -/
theorem FunctionParameterTailOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {leftStart rightStart : SourceSpan}
    {leftMarker rightMarker : Option SourceSpan}
    {leftName rightName : Syntax.Identifier}
    {leftErrorSpan rightErrorSpan : SourceSpan}
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterTailOrdinaryParses typeOrdinary leftStart
      leftMarker leftName leftErrorSpan input left afterLeft)
    (rightParsed : FunctionParameterTailOrdinaryParses typeOrdinary rightStart
      rightMarker rightName rightErrorSpan input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | typed leftColonSpan leftColon leftType =>
      cases rightParsed with
      | typed rightColonSpan rightColon rightType =>
          have afterColonEq := exactToken_output_unique leftColon rightColon
          subst afterColonEq
          exact typeOutcomes.successOutputUnique leftType rightType
      | typeMissing rightAbsent =>
          exact False.elim
            (absent_conflicts_token rightAbsent leftColon.1)
  | typeMissing leftAbsent =>
      cases rightParsed with
      | typed rightColonSpan rightColon rightType =>
          exact False.elim
            (absent_conflicts_token leftAbsent rightColon.1)
      | typeMissing => rfl

/-- Non-recovering named-parameter success has one final remainder. -/
theorem FunctionParameterCoreOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterCoreOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : FunctionParameterCoreOrdinaryParses typeOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | ordinary leftAbsent leftName leftTail =>
      cases rightParsed with
      | ordinary rightAbsent rightName rightTail =>
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact leftTail.output_unique typeOutcomes rightTail
      | comptime markerSpan rightMarker rightName rightTail =>
          exact False.elim
            (comptimePrefixAbsent_conflicts_exact leftAbsent rightMarker
              rightName)
  | comptime markerSpan leftMarker leftName leftTail =>
      cases rightParsed with
      | ordinary rightAbsent rightName rightTail =>
          exact False.elim
            (comptimePrefixAbsent_conflicts_exact rightAbsent leftMarker
              leftName)
      | comptime markerSpan rightMarker rightName rightTail =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact leftTail.output_unique typeOutcomes rightTail

/-- Non-recovering rejection excludes every ordinary Core success. -/
theorem FunctionParameterCoreRejects.disjointOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input rejected : Remainder}
    (rejection : FunctionParameterCoreRejects typeRejects input rejected) :
    ¬ ∃ parameter output,
      FunctionParameterCoreOrdinaryParses typeOrdinary input parameter
        output := by
  rintro ⟨parameter, output, parsed⟩
  cases rejection with
  | comptimeType markerSpan colonSpan rejectedMarker rejectedName
        rejectedColon typeRejected =>
      cases parsed with
      | ordinary absent nameParsed tail =>
          exact comptimePrefixAbsent_conflicts_exact absent rejectedMarker
            rejectedName
      | comptime successfulMarkerSpan successfulMarker successfulName tail =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          cases tail with
          | typeMissing colonAbsent =>
              exact absent_conflicts_token colonAbsent rejectedColon.1
          | typed successfulColonSpan successfulColon typeParsed =>
              have afterColonEq := exactToken_output_unique rejectedColon
                successfulColon
              subst afterColonEq
              exact typeOutcomes.successRejectDisjoint typeRejected
                ⟨_, _, typeParsed⟩
  | ordinaryName absent nameRejected =>
      cases parsed with
      | comptime markerSpan markerParsed nameParsed tail =>
          exact comptimePrefixAbsent_conflicts_exact absent markerParsed
            nameParsed
      | ordinary otherAbsent nameParsed tail =>
          exact nameRejected.disjoint ⟨_, _, nameParsed⟩
  | ordinaryType colonSpan absent rejectedName rejectedColon typeRejected =>
      cases parsed with
      | comptime markerSpan markerParsed nameParsed tail =>
          exact comptimePrefixAbsent_conflicts_exact absent markerParsed
            nameParsed
      | ordinary otherAbsent successfulName tail =>
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          cases tail with
          | typeMissing colonAbsent =>
              exact absent_conflicts_token colonAbsent rejectedColon.1
          | typed successfulColonSpan successfulColon typeParsed =>
              have afterColonEq := exactToken_output_unique rejectedColon
                successfulColon
              subst afterColonEq
              exact typeOutcomes.successRejectDisjoint typeRejected
                ⟨_, _, typeParsed⟩

/-- Deterministic ordinary outcomes of non-recovering `namedParameterCore`. -/
theorem functionParameterCoreDeterministicOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects) :
    DeterministicOutcomeSpec
      (FunctionParameterCoreOrdinaryParses typeOrdinary)
      (FunctionParameterCoreRejects typeRejects) where
  successOutputUnique := FunctionParameterCoreOrdinaryParses.output_unique
    typeOutcomes
  successRejectDisjoint := FunctionParameterCoreRejects.disjointOrdinary
    typeOutcomes

end Solcore.Syntax.DeclarativeGrammar
