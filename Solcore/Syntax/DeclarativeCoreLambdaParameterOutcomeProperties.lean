import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeCoreLambdaParameterOutcomeGrammar

/-! Deterministic ordinary outcomes of the lambda-parameter core. -/

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

private theorem identifier_value_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierParses input left afterLeft)
    (rightParsed : IdentifierParses input right afterRight) : left = right := by
  have tokenEq : ({ span := left.span, value := .identifier left.value } :
      Token) = { span := right.span, value := .identifier right.value } :=
    Option.some.inj (leftParsed.1.2.symm.trans rightParsed.1.2)
  cases left
  cases right
  simp_all

/-- A comptime-branch outcome proves the positive two-token guard. -/
theorem ComptimeLambdaParameterOrdinaryParses.startsAt
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {input output : Remainder} {parameter : Syntax.LambdaParameter}
    (parsed : ComptimeLambdaParameterOrdinaryParses typeOrdinary input
      parameter output) : ComptimeLambdaParameterStartsAt input := by
  cases parsed with
  | typed markerSpan colonSpan markerParsed nameParsed =>
      have nameToken := nameParsed.1
      rw [markerParsed.2] at nameToken
      exact ⟨markerSpan, _, _, markerParsed.1, nameToken⟩
  | typeMissing markerSpan markerParsed nameParsed =>
      have nameToken := nameParsed.1
      rw [markerParsed.2] at nameToken
      exact ⟨markerSpan, _, _, markerParsed.1, nameToken⟩

/-- The ordinary suffix has one deterministic remainder. -/
theorem OrdinaryLambdaParameterTailOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {name : Syntax.Identifier} {input : Remainder}
    {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name
      input left afterLeft)
    (rightParsed : OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name
      input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | inferred leftAbsent =>
      cases rightParsed with
      | inferred => rfl
      | typed span colonParsed typeParsed =>
          exact False.elim
            (absent_conflicts_token leftAbsent colonParsed.1)
  | typed span leftColon leftType =>
      cases rightParsed with
      | inferred rightAbsent =>
          exact False.elim
            (absent_conflicts_token rightAbsent leftColon.1)
      | typed span rightColon rightType =>
          have afterColonEq := exactToken_output_unique leftColon rightColon
          subst afterColonEq
          exact typeOutcomes.successOutputUnique leftType rightType

/-- Ordinary-name success has one deterministic remainder. -/
theorem OrdinaryLambdaParameterOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : OrdinaryLambdaParameterOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : OrdinaryLambdaParameterOrdinaryParses typeOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftName leftTail =>
      cases rightParsed with
      | parsed rightName rightTail =>
          have nameEq := identifier_value_unique leftName rightName
          subst nameEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact leftTail.output_unique typeOutcomes rightTail

/-- Contextual-comptime success has one deterministic remainder. -/
theorem ComptimeLambdaParameterOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : ComptimeLambdaParameterOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : ComptimeLambdaParameterOrdinaryParses typeOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | typed markerSpan colonSpan leftMarker leftName leftColon leftType =>
      cases rightParsed with
      | typed markerSpan colonSpan rightMarker rightName rightColon rightType =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          have afterColonEq := exactToken_output_unique leftColon rightColon
          subst afterColonEq
          exact typeOutcomes.successOutputUnique leftType rightType
      | typeMissing markerSpan rightMarker rightName rightAbsent =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact False.elim
            (absent_conflicts_token rightAbsent leftColon.1)
  | typeMissing markerSpan leftMarker leftName leftAbsent =>
      cases rightParsed with
      | typed markerSpan colonSpan rightMarker rightName rightColon rightType =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact False.elim
            (absent_conflicts_token leftAbsent rightColon.1)
      | typeMissing markerSpan rightMarker rightName rightAbsent =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          exact leftName.output_unique rightName

/-- Core success has one deterministic remainder. -/
theorem LambdaParameterCoreOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterCoreOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : LambdaParameterCoreOrdinaryParses typeOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | comptime left =>
      cases rightParsed with
      | comptime right => exact left.output_unique typeOutcomes right
      | ordinary absent right => exact False.elim (absent left.startsAt)
  | ordinary absent left =>
      cases rightParsed with
      | comptime right => exact False.elim (absent right.startsAt)
      | ordinary otherAbsent right =>
          exact left.output_unique typeOutcomes right

/-- Core rejection excludes every ordinary Core success. -/
theorem LambdaParameterCoreRejects.disjointOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input rejected : Remainder}
    (rejection : LambdaParameterCoreRejects typeRejects input rejected) :
    ¬ ∃ parameter output,
      LambdaParameterCoreOrdinaryParses typeOrdinary input parameter output := by
  rintro ⟨parameter, output, parsed⟩
  cases rejection with
  | comptimeType markerSpan colonSpan rejectedMarker rejectedName
        rejectedColon typeRejected =>
      cases parsed with
      | ordinary absent ordinaryParsed =>
          have nameToken := rejectedName.1
          rw [rejectedMarker.2] at nameToken
          exact absent ⟨markerSpan, _, _, rejectedMarker.1, nameToken⟩
      | comptime successful =>
          cases successful with
          | typeMissing successMarkerSpan successMarker successName
                colonAbsent =>
              have afterMarkerEq := exactToken_output_unique rejectedMarker
                successMarker
              subst afterMarkerEq
              have afterNameEq := rejectedName.output_unique successName
              subst afterNameEq
              exact absent_conflicts_token colonAbsent rejectedColon.1
          | typed markerSpan colonSpan successMarker successName successColon
                typeParsed =>
              have afterMarkerEq := exactToken_output_unique rejectedMarker
                successMarker
              subst afterMarkerEq
              have afterNameEq := rejectedName.output_unique successName
              subst afterNameEq
              have afterColonEq := exactToken_output_unique rejectedColon
                successColon
              subst afterColonEq
              exact typeOutcomes.successRejectDisjoint typeRejected
                ⟨_, _, typeParsed⟩
  | ordinaryName absent nameRejected =>
      cases parsed with
      | comptime successful => exact absent successful.startsAt
      | ordinary otherAbsent successful =>
          cases successful with
          | parsed nameParsed tail =>
              exact nameRejected.disjoint ⟨_, _, nameParsed⟩
  | ordinaryType colonSpan absent rejectedName rejectedColon typeRejected =>
      cases parsed with
      | comptime successful => exact absent successful.startsAt
      | ordinary otherAbsent successful =>
          cases successful with
          | parsed successName tail =>
              have afterNameEq := rejectedName.output_unique successName
              subst afterNameEq
              cases tail with
              | inferred colonAbsent =>
                  exact absent_conflicts_token colonAbsent rejectedColon.1
              | typed span successColon typeParsed =>
                  have afterColonEq := exactToken_output_unique rejectedColon
                    successColon
                  subst afterColonEq
                  exact typeOutcomes.successRejectDisjoint typeRejected
                    ⟨_, _, typeParsed⟩

/-- Deterministic ordinary outcome contract for `lambdaParameterCore`. -/
theorem lambdaParameterCoreDeterministicOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects) :
    DeterministicOutcomeSpec
      (LambdaParameterCoreOrdinaryParses typeOrdinary)
      (LambdaParameterCoreRejects typeRejects) where
  successOutputUnique := LambdaParameterCoreOrdinaryParses.output_unique
    typeOutcomes
  successRejectDisjoint := LambdaParameterCoreRejects.disjointOrdinary
    typeOutcomes

end Solcore.Syntax.DeclarativeGrammar
