import Solcore.Syntax.DeclarativeCoreStatementSimpleOutcomeProperties

/-! Complete deterministic outcomes of Core `let` and `return` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Ordinary Core `let` success has a unique output remainder. -/
theorem LetStatementOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : LetStatementOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : LetStatementOrdinaryParses expressionOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftSemicolonSpan leftMarker leftName leftType
        leftInitializer leftSemicolon =>
      cases rightParsed with
      | parsed rightMarkerSpan rightSemicolonSpan rightMarker rightName
            rightType rightInitializer rightSemicolon =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          have afterTypeEq := leftType.output_unique typeOutcomes rightType
          subst afterTypeEq
          have afterInitializerEq :=
            OptionalLetInitializerOrdinaryParses.output_unique
              expressionOutcomes leftInitializer rightInitializer
          subst afterInitializerEq
          exact exactToken_output_unique leftSemicolon rightSemicolon

/-- Exact Core `let` rejection excludes ordinary success. -/
theorem LetStatementRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input rejected : Remainder}
    (rejection : LetStatementRejects expressionOrdinary expressionRejects
      typeRejects input rejected) :
    ¬ ∃ statement output,
      LetStatementOrdinaryParses expressionOrdinary input statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulSemicolonSpan successfulMarker
        successfulName successfulType successfulInitializer
        successfulSemicolon =>
      cases rejection with
      | markerRejected markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | nameRejected rejectedMarkerSpan rejectedMarker rejectedName =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact rejectedName.disjoint ⟨_, _, successfulName⟩
      | typeRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedType =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          exact (OptionalLetTypeRejects.disjointOrdinary typeOutcomes
            rejectedType) ⟨_, _, successfulType⟩
      | initializerRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedType rejectedInitializer =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterTypeEq := rejectedType.output_unique typeOutcomes
            successfulType
          subst afterTypeEq
          exact (OptionalLetInitializerRejects.disjointOrdinary
            expressionOutcomes rejectedInitializer)
              ⟨_, _, successfulInitializer⟩
      | semicolonRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedType rejectedInitializer semicolonAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterTypeEq := rejectedType.output_unique typeOutcomes
            successfulType
          subst afterTypeEq
          have afterInitializerEq :=
            OptionalLetInitializerOrdinaryParses.output_unique
              expressionOutcomes rejectedInitializer successfulInitializer
          subst afterInitializerEq
          exact absent_conflicts_exact semicolonAbsent successfulSemicolon

/-- Lift expression and type outcomes through a complete Core `let`. -/
theorem letStatementDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects) :
    DeterministicOutcomeSpec
      (LetStatementOrdinaryParses expressionOrdinary)
      (LetStatementRejects expressionOrdinary expressionRejects typeRejects)
    where
  successOutputUnique := LetStatementOrdinaryParses.output_unique
    expressionOutcomes typeOutcomes
  successRejectDisjoint := LetStatementRejects.disjointOrdinary
    expressionOutcomes typeOutcomes

/-- Ordinary Core `return` success has a unique output remainder. -/
theorem ReturnStatementOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : ReturnStatementOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ReturnStatementOrdinaryParses expressionOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftSemicolonSpan leftMarker leftValue
        leftSemicolon =>
      cases rightParsed with
      | parsed rightMarkerSpan rightSemicolonSpan rightMarker rightValue
            rightSemicolon =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterValueEq :=
            OptionalReturnValueOrdinaryParses.output_unique
              expressionOutcomes leftValue rightValue
          subst afterValueEq
          exact exactToken_output_unique leftSemicolon rightSemicolon

/-- Exact Core `return` rejection excludes ordinary success. -/
theorem ReturnStatementRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : ReturnStatementRejects expressionOrdinary expressionRejects
      input rejected) :
    ¬ ∃ statement output,
      ReturnStatementOrdinaryParses expressionOrdinary input statement
        output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulSemicolonSpan successfulMarker
        successfulValue successfulSemicolon =>
      cases rejection with
      | markerRejected markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | valueRejected rejectedMarkerSpan rejectedMarker rejectedValue =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact (OptionalReturnValueRejects.disjointOrdinary
            expressionOutcomes rejectedValue) ⟨_, _, successfulValue⟩
      | semicolonRejected rejectedMarkerSpan rejectedMarker rejectedValue
            semicolonAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterValueEq :=
            OptionalReturnValueOrdinaryParses.output_unique
              expressionOutcomes rejectedValue successfulValue
          subst afterValueEq
          exact absent_conflicts_exact semicolonAbsent successfulSemicolon

/-- Lift expression outcomes through a complete Core `return`. -/
theorem returnStatementDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (ReturnStatementOrdinaryParses expressionOrdinary)
      (ReturnStatementRejects expressionOrdinary expressionRejects) where
  successOutputUnique := ReturnStatementOrdinaryParses.output_unique
    expressionOutcomes
  successRejectDisjoint := ReturnStatementRejects.disjointOrdinary
    expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
