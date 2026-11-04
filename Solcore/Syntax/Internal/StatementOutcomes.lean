import Solcore.Syntax.Grammar.Statements
import Solcore.Syntax.Internal.SignatureOutcomes
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Internal.TypeOutcomes
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Grammar.Basics

/-!
Properties of the declarative grammar of simple statements, blocks, loops and `match`
cases: outcomes are deterministic, and successful values and rejection points are unique.
Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreAssemblyStatementOutcomeProperties
/-! Deterministic ordinary outcomes for Core `assembly`. -/

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

/-- Ordinary Core assembly success has one final remainder. -/
theorem AssemblyStatementOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssemblyStatementOrdinaryParses input left afterLeft)
    (rightParsed : AssemblyStatementOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          exact leftBody.output_unique
            yulStatementPublicDeterministicOutcomeSpec rightBody

/-- Exact Core assembly rejection excludes ordinary success. -/
theorem AssemblyStatementRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : AssemblyStatementRejects input rejected) :
    ¬ ∃ statement output,
      AssemblyStatementOrdinaryParses input statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact rejectedBody.disjointOrdinary
            yulStatementPublicDeterministicOutcomeSpec
              ⟨_, _, _, successfulBody⟩

/-- Public Yul body outcomes lift through the Core assembly wrapper. -/
theorem assemblyStatementDeterministicOutcomeSpec :
    DeterministicOutcomeSpec AssemblyStatementOrdinaryParses
      AssemblyStatementRejects where
  successOutputUnique := AssemblyStatementOrdinaryParses.output_unique
  successRejectDisjoint := AssemblyStatementRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreAssemblyStatementExactnessProperties
/-! Exact Core assembly statements from unconditional inline-Yul body outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An assembly marker and Yul body fix the full embedded Core statement. -/
theorem AssemblyStatementOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssemblyStatementOrdinaryParses input left afterLeft)
    (rightParsed : AssemblyStatementOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightBody =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          rcases leftBody.result_unique rightBody with ⟨spanEq, bodyEq, outputEq⟩
          subst spanEq
          subst bodyEq
          rfl

/-- Ordinary assembly success fixes its complete AST and final remainder. -/
theorem AssemblyStatementOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssemblyStatementOrdinaryParses input left afterLeft)
    (rightParsed : AssemblyStatementOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Assembly rejection fixes the missing-marker or first Yul-body failure endpoint. -/
theorem AssemblyStatementRejects.output_unique
    {input left right : Remainder}
    (leftRejected : AssemblyStatementRejects input left)
    (rightRejected : AssemblyStatementRejects input right) : left = right := by
  cases leftRejected with
  | markerMissing leftAbsent =>
      cases rightRejected with
      | markerMissing => rfl
      | bodyRejected rightSpan rightMarker rightBody =>
          exact False.elim (leftAbsent ⟨_, rightMarker.1⟩)
  | bodyRejected leftSpan leftMarker leftBody =>
      cases rightRejected with
      | markerMissing rightAbsent =>
          exact False.elim (rightAbsent ⟨_, leftMarker.1⟩)
      | bodyRejected rightSpan rightMarker rightBody =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          exact leftBody.output_unique rightBody

/-- Independent Yul recursion discharges every Core assembly exactness premise. -/
theorem assemblyStatementExactOutcomeSpec :
    ExactDeterministicOutcomeSpec AssemblyStatementOrdinaryParses
      AssemblyStatementRejects where
  toDeterministicOutcomeSpec := assemblyStatementDeterministicOutcomeSpec
  successValueUnique := AssemblyStatementOrdinaryParses.value_unique
  rejectOutputUnique := AssemblyStatementRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementSimpleOutcomeProperties
/-! Deterministic ordinary outcomes of Core `let` and `return` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (token : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, token⟩

/-- Optional let types have functional ordinary success. -/
theorem OptionalLetTypeParses.output_unique
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input : Remainder} {left right : Option Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalLetTypeParses input left afterLeft)
    (rightParsed : OptionalLetTypeParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present span token parsed =>
          exact False.elim (absent_conflicts_exact leftAbsent token)
  | present leftSpan leftToken leftType =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
      | present rightSpan rightToken rightType =>
          have afterTokenEq := exactToken_output_unique leftToken rightToken
          subst afterTokenEq
          exact typeOutcomes.successOutputUnique leftType rightType

/-- Optional let-type rejection excludes ordinary success. -/
theorem OptionalLetTypeRejects.disjointOrdinary
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input rejected : Remainder}
    (rejection : OptionalLetTypeRejects typeRejects input rejected) :
    ¬ ∃ type output, OptionalLetTypeParses input type output := by
  rintro ⟨type, output, successful⟩
  cases rejection with
  | typeRejected rejectedSpan rejectedToken rejectedType =>
      cases successful with
      | absent colonAbsent =>
          exact absent_conflicts_exact colonAbsent rejectedToken
      | present successfulSpan successfulToken successfulType =>
          have afterTokenEq := exactToken_output_unique rejectedToken
            successfulToken
          subst afterTokenEq
          exact typeOutcomes.successRejectDisjoint rejectedType
            ⟨_, _, successfulType⟩

/-- Deterministic outcomes for optional let types. -/
theorem optionalLetTypeDeterministicOutcomeSpec
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects) :
    DeterministicOutcomeSpec OptionalLetTypeParses
      (OptionalLetTypeRejects typeRejects) where
  successOutputUnique := OptionalLetTypeParses.output_unique typeOutcomes
  successRejectDisjoint :=
    OptionalLetTypeRejects.disjointOrdinary typeOutcomes

/-- Optional let initializers have functional ordinary success. -/
theorem OptionalLetInitializerOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalLetInitializerOrdinaryParses expressionOrdinary
      input left afterLeft)
    (rightParsed : OptionalLetInitializerOrdinaryParses expressionOrdinary
      input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present span token parsed =>
          exact False.elim (absent_conflicts_exact leftAbsent token)
  | present leftSpan leftToken leftValue =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
      | present rightSpan rightToken rightValue =>
          have afterTokenEq := exactToken_output_unique leftToken rightToken
          subst afterTokenEq
          exact expressionOutcomes.successOutputUnique leftValue rightValue

/-- Optional initializer rejection excludes ordinary success. -/
theorem OptionalLetInitializerRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : OptionalLetInitializerRejects expressionRejects input
      rejected) :
    ¬ ∃ initializer output,
      OptionalLetInitializerOrdinaryParses expressionOrdinary input
        initializer output := by
  rintro ⟨initializer, output, successful⟩
  cases rejection with
  | expressionRejected rejectedSpan rejectedToken rejectedExpression =>
      cases successful with
      | absent equalAbsent =>
          exact absent_conflicts_exact equalAbsent rejectedToken
      | present successfulSpan successfulToken successfulExpression =>
          have afterTokenEq := exactToken_output_unique rejectedToken
            successfulToken
          subst afterTokenEq
          exact expressionOutcomes.successRejectDisjoint rejectedExpression
            ⟨_, _, successfulExpression⟩

/-- Deterministic outcomes for optional let initializers. -/
theorem optionalLetInitializerDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (OptionalLetInitializerOrdinaryParses expressionOrdinary)
      (OptionalLetInitializerRejects expressionRejects) where
  successOutputUnique :=
    OptionalLetInitializerOrdinaryParses.output_unique expressionOutcomes
  successRejectDisjoint :=
    OptionalLetInitializerRejects.disjointOrdinary expressionOutcomes

/-- Optional return values have functional ordinary success. -/
theorem OptionalReturnValueOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalReturnValueOrdinaryParses expressionOrdinary input
      left afterLeft)
    (rightParsed : OptionalReturnValueOrdinaryParses expressionOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftSpan leftToken =>
      cases rightParsed with
      | absent => rfl
      | present rightAbsent rightValue =>
          exact False.elim
            (absent_conflicts_token rightAbsent leftToken)
  | present leftAbsent leftValue =>
      cases rightParsed with
      | absent rightSpan rightToken =>
          exact False.elim
            (absent_conflicts_token leftAbsent rightToken)
      | present rightAbsent rightValue =>
          exact expressionOutcomes.successOutputUnique leftValue rightValue

/-- Optional return-value rejection excludes ordinary success. -/
theorem OptionalReturnValueRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : OptionalReturnValueRejects expressionRejects input rejected) :
    ¬ ∃ value output,
      OptionalReturnValueOrdinaryParses expressionOrdinary input value
        output := by
  rintro ⟨value, output, successful⟩
  cases rejection with
  | expressionRejected semicolonAbsent rejectedExpression =>
      cases successful with
      | absent span token =>
          exact absent_conflicts_token semicolonAbsent token
      | present successfulAbsent successfulExpression =>
          exact expressionOutcomes.successRejectDisjoint rejectedExpression
            ⟨_, _, successfulExpression⟩

/-- Deterministic outcomes for optional return values. -/
theorem optionalReturnValueDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (OptionalReturnValueOrdinaryParses expressionOrdinary)
      (OptionalReturnValueRejects expressionRejects) where
  successOutputUnique :=
    OptionalReturnValueOrdinaryParses.output_unique expressionOutcomes
  successRejectDisjoint :=
    OptionalReturnValueRejects.disjointOrdinary expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementSimpleCompleteOutcomeProperties
/-! Complete deterministic outcomes of Core `let` and `return` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementLayerPriorityProperties
/-! Exact guard selection for the ordered Core statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An exact current token-kind selected by a Core statement guard. -/
def StatementLayerTokenAt (input : Remainder) (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := kind }

/-- Positive evidence for the executable guard at one dispatcher stage. -/
def StatementLayerGuardAt (input : Remainder) : StatementLayerStage → Prop
  | .letGuard => StatementLayerTokenAt input (.keyword .letKw)
  | .returnGuard => StatementLayerTokenAt input (.keyword .returnKw)
  | .matchGuard => StatementLayerTokenAt input (.keyword .matchKw)
  | .forGuard => StatementLayerTokenAt input (.keyword .forKw)
  | .whileGuard => StatementLayerTokenAt input
      (.identifier ContextualKeyword.while.spelling)
  | .ifGuard => StatementLayerTokenAt input (.keyword .ifKw)
  | .assemblyGuard => StatementLayerTokenAt input (.keyword .assemblyKw)
  | .blockGuard => StatementLayerTokenAt input (.symbol .leftBrace)
  | .breakGuard => StatementLayerTokenAt input (.keyword .breakKw)
  | .continueGuard => StatementLayerTokenAt input (.keyword .continueKw)
  | .fallback => True

/-- Numeric order of the executable Core statement decisions. -/
def StatementLayerStage.rank : StatementLayerStage → Nat
  | .letGuard => 0
  | .returnGuard => 1
  | .matchGuard => 2
  | .forGuard => 3
  | .whileGuard => 4
  | .ifGuard => 5
  | .assemblyGuard => 6
  | .blockGuard => 7
  | .breakGuard => 8
  | .continueGuard => 9
  | .fallback => 10

/-- Exact negative evidence corresponding to one positive guard. -/
def StatementLayerGuardAbsentAt (input : Remainder) :
    StatementLayerStage → Prop
  | .letGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .letKw)
  | .returnGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .returnKw)
  | .matchGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .matchKw)
  | .forGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .forKw)
  | .whileGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.identifier ContextualKeyword.while.spelling)
  | .ifGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .ifKw)
  | .assemblyGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .assemblyKw)
  | .blockGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftBrace)
  | .breakGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .breakKw)
  | .continueGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .continueKw)
  | .fallback => False

/-- A positive guard conflicts with its exact negative evidence. -/
theorem StatementLayerGuardAbsentAt.not_guard
    {input : Remainder} {stage : StatementLayerStage}
    (absent : StatementLayerGuardAbsentAt input stage) :
    ¬ StatementLayerGuardAt input stage := by
  cases stage <;>
    simp only [StatementLayerGuardAbsentAt, StatementLayerGuardAt,
      StatementLayerTokenAt] at absent ⊢
  all_goals exact absent

/-- A priority prefix contains negative evidence for every earlier guard. -/
theorem StatementLayerPrefixAbsent.guardAbsent_of_rank_lt
    {input : Remainder} {stage previous : StatementLayerStage}
    (priority : StatementLayerPrefixAbsent input stage)
    (before : previous.rank < stage.rank) :
    StatementLayerGuardAbsentAt input previous := by
  induction priority with
  | start =>
      cases previous <;> simp [StatementLayerStage.rank] at before
  | afterLet prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterReturn prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterMatch prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterFor prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterWhile prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterIf prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterAssembly prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterBlock prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterBreak prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterContinue prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]

/-- Stage rank exactly reflects the finite dispatcher order. -/
theorem StatementLayerStage.rank_injective :
    Function.Injective StatementLayerStage.rank := by
  intro left right equal
  cases left <;> cases right <;> simp_all [StatementLayerStage.rank]

/-- Exact priority and positive guards select at most one Core stage. -/
theorem statementLayer_selectedStage_unique
    {input : Remainder} {left right : StatementLayerStage}
    (leftPriority : StatementLayerPrefixAbsent input left)
    (leftGuard : StatementLayerGuardAt input left)
    (rightPriority : StatementLayerPrefixAbsent input right)
    (rightGuard : StatementLayerGuardAt input right) :
    left = right := by
  apply StatementLayerStage.rank_injective
  by_cases equal : left.rank = right.rank
  · exact equal
  · rcases Nat.lt_or_gt_of_ne equal with before | after
    · exact False.elim
        ((rightPriority.guardAbsent_of_rank_lt before).not_guard leftGuard)
    · exact False.elim
        ((leftPriority.guardAbsent_of_rank_lt after).not_guard rightGuard)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementLayerSelectionOutcomeProperties
/-!
Generic deterministic outcomes for the selected stage of the ordered Core
statement dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary success at one selected stage.  Every guarded primary is wrapped
in the executable transactional fallback; the final stage runs the fallback
directly. -/
inductive StatementLayerSelectionOrdinaryParsesAt {alpha : Type}
    (primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop)
    (primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop)
    (fallbackParses : Remainder → alpha → Remainder → Prop) :
    StatementLayerStage → Remainder → alpha → Remainder → Prop where
  | guarded {stage input value output}
      (notFallback : stage ≠ .fallback)
      (priority : StatementLayerPrefixAbsent input stage)
      (guard : StatementLayerGuardAt input stage)
      (parsed : TransactionalFallbackOrdinaryParses
        (primaryParses stage) (primaryRejects stage) fallbackParses input
          value output) :
      StatementLayerSelectionOrdinaryParsesAt primaryParses primaryRejects
        fallbackParses stage input value output
  | fallback {input value output}
      (priority : StatementLayerPrefixAbsent input .fallback)
      (parsed : fallbackParses input value output) :
      StatementLayerSelectionOrdinaryParsesAt primaryParses primaryRejects
        fallbackParses .fallback input value output

/-- Ordinary success at the uniquely selected dispatcher stage. -/
def StatementLayerSelectionOrdinaryParses {alpha : Type}
    (primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop)
    (primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop)
    (fallbackParses : Remainder → alpha → Remainder → Prop)
    (input : Remainder) (value : alpha) (output : Remainder) : Prop :=
  ∃ stage, StatementLayerSelectionOrdinaryParsesAt primaryParses
    primaryRejects fallbackParses stage input value output

/-- Exact rejection at one selected stage. -/
inductive StatementLayerSelectionRejectsAt {alpha : Type}
    (primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop)
    (primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop)
    (fallbackRejects : Remainder → Remainder → Prop) :
    StatementLayerStage → Remainder → Remainder → Prop where
  | guarded {stage input rejected}
      (notFallback : stage ≠ .fallback)
      (priority : StatementLayerPrefixAbsent input stage)
      (guard : StatementLayerGuardAt input stage)
      (rejection : TransactionalFallbackRejects (primaryRejects stage)
        fallbackRejects input rejected) :
      StatementLayerSelectionRejectsAt primaryParses primaryRejects
        fallbackRejects stage input rejected
  | fallback {input rejected}
      (priority : StatementLayerPrefixAbsent input .fallback)
      (rejection : fallbackRejects input rejected) :
      StatementLayerSelectionRejectsAt primaryParses primaryRejects
        fallbackRejects .fallback input rejected

/-- Exact rejection at the uniquely selected dispatcher stage. -/
def StatementLayerSelectionRejects {alpha : Type}
    (primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop)
    (primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop)
    (fallbackRejects : Remainder → Remainder → Prop)
    (input rejected : Remainder) : Prop :=
  ∃ stage, StatementLayerSelectionRejectsAt primaryParses primaryRejects
    fallbackRejects stage input rejected

theorem StatementLayerSelectionOrdinaryParsesAt.priority {alpha : Type}
    {primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop}
    {fallbackParses : Remainder → alpha → Remainder → Prop}
    {stage input value output}
    (parsed : StatementLayerSelectionOrdinaryParsesAt primaryParses
      primaryRejects fallbackParses stage input value output) :
    StatementLayerPrefixAbsent input stage := by
  cases parsed <;> assumption

theorem StatementLayerSelectionOrdinaryParsesAt.guard {alpha : Type}
    {primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop}
    {fallbackParses : Remainder → alpha → Remainder → Prop}
    {stage input value output}
    (parsed : StatementLayerSelectionOrdinaryParsesAt primaryParses
      primaryRejects fallbackParses stage input value output) :
    StatementLayerGuardAt input stage := by
  cases parsed <;> simp_all [StatementLayerGuardAt]

theorem StatementLayerSelectionRejectsAt.priority {alpha : Type}
    {primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop}
    {fallbackRejects : Remainder → Remainder → Prop}
    {stage input rejected}
    (rejection : StatementLayerSelectionRejectsAt primaryParses
      primaryRejects fallbackRejects stage input rejected) :
    StatementLayerPrefixAbsent input stage := by
  cases rejection <;> assumption

theorem StatementLayerSelectionRejectsAt.guard {alpha : Type}
    {primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop}
    {fallbackRejects : Remainder → Remainder → Prop}
    {stage input rejected}
    (rejection : StatementLayerSelectionRejectsAt primaryParses
      primaryRejects fallbackRejects stage input rejected) :
    StatementLayerGuardAt input stage := by
  cases rejection <;> simp_all [StatementLayerGuardAt]

/-- Selected-stage success has one output whenever every primary and the
shared fallback have deterministic outcomes. -/
theorem StatementLayerSelectionOrdinaryParses.output_unique {alpha : Type}
    {primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop}
    {fallbackParses : Remainder → alpha → Remainder → Prop}
    {fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : ∀ stage, stage ≠ .fallback →
      DeterministicOutcomeSpec (primaryParses stage)
        (primaryRejects stage))
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses
      fallbackRejects)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : StatementLayerSelectionOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : StatementLayerSelectionOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftStage, leftParsed⟩
  rcases rightParsed with ⟨rightStage, rightParsed⟩
  have selected := statementLayer_selectedStage_unique leftParsed.priority
    leftParsed.guard rightParsed.priority rightParsed.guard
  subst rightStage
  cases leftParsed <;> cases rightParsed
  · exact TransactionalFallbackOrdinaryParses.output_unique
      (primaryOutcomes _ (by assumption)) fallbackOutcomes
        (by assumption) (by assumption)
  · contradiction
  · contradiction
  · exact fallbackOutcomes.successOutputUnique (by assumption)
      (by assumption)

/-- Selected-stage rejection excludes every ordinary success. -/
theorem StatementLayerSelectionRejects.disjointOrdinary {alpha : Type}
    {primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop}
    {fallbackParses : Remainder → alpha → Remainder → Prop}
    {fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : ∀ stage, stage ≠ .fallback →
      DeterministicOutcomeSpec (primaryParses stage)
        (primaryRejects stage))
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses
      fallbackRejects)
    {input rejected : Remainder}
    (rejection : StatementLayerSelectionRejects primaryParses primaryRejects
      fallbackRejects input rejected) :
    ¬ ∃ value output, StatementLayerSelectionOrdinaryParses
      primaryParses primaryRejects fallbackParses input value output := by
  rintro ⟨value, output, successful⟩
  rcases rejection with ⟨rejectedStage, rejection⟩
  rcases successful with ⟨successfulStage, successful⟩
  have selected := statementLayer_selectedStage_unique rejection.priority
    rejection.guard successful.priority successful.guard
  subst successfulStage
  cases rejection <;> cases successful
  · exact TransactionalFallbackRejects.disjointOrdinary
      (primaryOutcomes _ (by assumption)) fallbackOutcomes (by assumption)
        ⟨_, _, by assumption⟩
  · contradiction
  · contradiction
  · exact fallbackOutcomes.successRejectDisjoint (by assumption)
      ⟨_, _, by assumption⟩

/-- Package deterministic outcomes of the generic selected-stage layer. -/
theorem statementLayerSelectionDeterministicOutcomeSpec {alpha : Type}
    (primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop)
    (primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop)
    (fallbackParses : Remainder → alpha → Remainder → Prop)
    (fallbackRejects : Remainder → Remainder → Prop)
    (primaryOutcomes : ∀ stage, stage ≠ .fallback →
      DeterministicOutcomeSpec (primaryParses stage)
        (primaryRejects stage))
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses
      fallbackRejects) :
    DeterministicOutcomeSpec
      (StatementLayerSelectionOrdinaryParses primaryParses primaryRejects
        fallbackParses)
      (StatementLayerSelectionRejects primaryParses primaryRejects
        fallbackRejects) where
  successOutputUnique := StatementLayerSelectionOrdinaryParses.output_unique
    primaryOutcomes fallbackOutcomes
  successRejectDisjoint := StatementLayerSelectionRejects.disjointOrdinary
    primaryOutcomes fallbackOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementLayerSelectionExactnessProperties
/-! Exact selected-stage outcomes without exact raw primary rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The selected stage and unique branch values determine the statement AST. -/
theorem StatementLayerSelectionOrdinaryParses.value_unique {alpha : Type}
    {primaryParses : StatementLayerStage → Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage → Remainder → Remainder → Prop}
    {fallbackParses : Remainder → alpha → Remainder → Prop}
    (primaryOutcomes : ∀ stage, stage ≠ .fallback →
      DeterministicOutcomeSpec (primaryParses stage) (primaryRejects stage))
    (primaryValues : ∀ stage, stage ≠ .fallback →
      ∀ {input left right afterLeft afterRight},
        primaryParses stage input left afterLeft →
        primaryParses stage input right afterRight → left = right)
    (fallbackValues : ∀ {input left right afterLeft afterRight},
      fallbackParses input left afterLeft →
      fallbackParses input right afterRight → left = right)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : StatementLayerSelectionOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : StatementLayerSelectionOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftStage, leftParsed⟩
  rcases rightParsed with ⟨rightStage, rightParsed⟩
  have selected := statementLayer_selectedStage_unique leftParsed.priority
    leftParsed.guard rightParsed.priority rightParsed.guard
  subst rightStage
  cases leftParsed <;> cases rightParsed
  · exact TransactionalFallbackOrdinaryParses.value_unique_of_success
      (fallbackParses := fallbackParses)
      (primaryOutcomes _ (by assumption)) (primaryValues _ (by assumption))
      fallbackValues (by assumption) (by assumption)
  · contradiction
  · contradiction
  · exact fallbackValues (by assumption) (by assumption)

/-- Deterministic stages and unique successful values fix complete results. -/
theorem StatementLayerSelectionOrdinaryParses.result_unique {alpha : Type}
    {primaryParses : StatementLayerStage → Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage → Remainder → Remainder → Prop}
    {fallbackParses : Remainder → alpha → Remainder → Prop}
    {fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : ∀ stage, stage ≠ .fallback →
      DeterministicOutcomeSpec (primaryParses stage) (primaryRejects stage))
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses fallbackRejects)
    (primaryValues : ∀ stage, stage ≠ .fallback →
      ∀ {input left right afterLeft afterRight},
        primaryParses stage input left afterLeft →
        primaryParses stage input right afterRight → left = right)
    (fallbackValues : ∀ {input left right afterLeft afterRight},
      fallbackParses input left afterLeft →
      fallbackParses input right afterRight → left = right)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : StatementLayerSelectionOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : StatementLayerSelectionOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique (fallbackParses := fallbackParses)
      primaryOutcomes primaryValues fallbackValues rightParsed,
    leftParsed.output_unique primaryOutcomes fallbackOutcomes rightParsed⟩

/-- Guarded rejection rewinds; only final-stage rejection needs an endpoint law. -/
theorem StatementLayerSelectionRejects.output_unique {alpha : Type}
    {primaryParses : StatementLayerStage → Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage → Remainder → Remainder → Prop}
    {fallbackRejects : Remainder → Remainder → Prop}
    (fallbackOutputs : ∀ {input left right},
      fallbackRejects input left → fallbackRejects input right → left = right)
    {input left right : Remainder}
    (leftRejects : StatementLayerSelectionRejects primaryParses
      primaryRejects fallbackRejects input left)
    (rightRejects : StatementLayerSelectionRejects primaryParses
      primaryRejects fallbackRejects input right) : left = right := by
  rcases leftRejects with ⟨leftStage, leftRejects⟩
  rcases rightRejects with ⟨rightStage, rightRejects⟩
  have selected := statementLayer_selectedStage_unique leftRejects.priority
    leftRejects.guard rightRejects.priority rightRejects.guard
  subst rightStage
  cases leftRejects <;> cases rightRejects
  · exact TransactionalFallbackRejects.output_unique
      (by assumption) (by assumption)
  · contradiction
  · contradiction
  · exact fallbackOutputs (by assumption) (by assumption)

/-- Priority, successful primary values, and an exact fallback determine every
ordinary result and rejecting endpoint of the complete selected-stage layer. -/
theorem statementLayerSelectionExactOutcomeSpecOfSuccess {alpha : Type}
    (primaryParses : StatementLayerStage → Remainder → alpha → Remainder → Prop)
    (primaryRejects : StatementLayerStage → Remainder → Remainder → Prop)
    (fallbackParses : Remainder → alpha → Remainder → Prop)
    (fallbackRejects : Remainder → Remainder → Prop)
    (primaryOutcomes : ∀ stage, stage ≠ .fallback →
      DeterministicOutcomeSpec (primaryParses stage) (primaryRejects stage))
    (primaryValues : ∀ stage, stage ≠ .fallback →
      ∀ {input left right afterLeft afterRight},
        primaryParses stage input left afterLeft →
        primaryParses stage input right afterRight → left = right)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec fallbackParses fallbackRejects) :
    ExactDeterministicOutcomeSpec
      (StatementLayerSelectionOrdinaryParses primaryParses primaryRejects
        fallbackParses)
      (StatementLayerSelectionRejects primaryParses primaryRejects fallbackRejects) where
  toDeterministicOutcomeSpec :=
    statementLayerSelectionDeterministicOutcomeSpec primaryParses primaryRejects
      fallbackParses fallbackRejects primaryOutcomes
      fallbackOutcomes.toDeterministicOutcomeSpec
  successValueUnique := fun leftParsed rightParsed =>
    leftParsed.value_unique (fallbackParses := fallbackParses) primaryOutcomes
      primaryValues fallbackOutcomes.successValueUnique rightParsed
  rejectOutputUnique := fun leftRejects rightRejects =>
    leftRejects.output_unique (primaryParses := primaryParses)
      (primaryRejects := primaryRejects) (fallbackRejects := fallbackRejects)
      fallbackOutcomes.rejectOutputUnique rightRejects

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreAssignmentStatementOutcomeProperties
/-!
Functionality, rejection exclusivity, and clean embedding for ordinary Core
assignment-or-expression statement outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem valueOperator_output_unique
    {input leftOutput rightOutput : Remainder}
    {leftOperator rightOperator : Located ValueAssignOp}
    (leftParsed : ValueAssignOperatorParses input leftOperator leftOutput)
    (rightParsed : ValueAssignOperatorParses input rightOperator rightOutput) :
    leftOutput = rightOutput :=
  (leftParsed.unique rightParsed).2

/-- A parsed assignment suffix has a unique output remainder. -/
theorem AssignmentTailParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : CoreAssignmentTail}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssignmentTailParses expressionOrdinary input left
      afterLeft)
    (rightParsed : AssignmentTailParses expressionOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | bitNot leftSpan leftToken =>
      cases rightParsed with
      | bitNot rightSpan rightToken => rw [leftToken.2, rightToken.2]
      | value rightAbsent rightOperator rightExpression =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
  | value leftAbsent leftOperator leftExpression =>
      cases rightParsed with
      | bitNot rightSpan rightToken =>
          exact False.elim (absent_conflicts_exact leftAbsent rightToken)
      | value rightAbsent rightOperator rightExpression =>
          have operatorEq := valueOperator_output_unique leftOperator
            rightOperator
          subst operatorEq
          exact outcomes.successOutputUnique leftExpression rightExpression

/-- Maximal optional assignment suffix parsing has a unique remainder. -/
theorem OptionalAssignmentTailParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option CoreAssignmentTail}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalAssignmentTailParses expressionOrdinary input left
      afterLeft)
    (rightParsed : OptionalAssignmentTailParses expressionOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightTail =>
          cases rightTail with
          | bitNot span token =>
              exact False.elim (absent_conflicts_exact leftAbsent.1 token)
          | value tildeAbsent operatorParsed expressionParsed =>
              exact False.elim (operatorParsed.not_absent leftAbsent.2)
  | present leftTail =>
      cases rightParsed with
      | absent rightAbsent =>
          cases leftTail with
          | bitNot span token =>
              exact False.elim (absent_conflicts_exact rightAbsent.1 token)
          | value tildeAbsent operatorParsed expressionParsed =>
              exact False.elim (operatorParsed.not_absent rightAbsent.2)
      | present rightTail =>
          exact leftTail.output_unique outcomes rightTail

/-- Maximal optional statement-semicolon parsing has a unique remainder. -/
theorem OptionalStatementSemicolonParses.output_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalStatementSemicolonParses input left afterLeft)
    (rightParsed : OptionalStatementSemicolonParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightToken =>
          exact False.elim (absent_conflicts_exact leftAbsent rightToken)
  | present leftSpan leftToken =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
      | present rightSpan rightToken => rw [leftToken.2, rightToken.2]

/-- Ordinary Core fallback success has a unique output remainder. -/
theorem AssignmentOrExpressionStatementOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input left afterLeft)
    (rightParsed : AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input right afterRight) : afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftExpression, leftAfterExpression, leftTail, leftAfterTail,
      leftSemicolon, leftExpressionParsed, leftTailParsed,
      leftSemicolonParsed, leftBuild⟩
  rcases rightParsed with
    ⟨rightExpression, rightAfterExpression, rightTail, rightAfterTail,
      rightSemicolon, rightExpressionParsed, rightTailParsed,
      rightSemicolonParsed, rightBuild⟩
  have expressionEq := outcomes.successOutputUnique leftExpressionParsed
    rightExpressionParsed
  subst expressionEq
  have tailEq := leftTailParsed.output_unique outcomes rightTailParsed
  subst tailEq
  exact leftSemicolonParsed.output_unique rightSemicolonParsed

/-- Exact fallback rejection excludes every ordinary fallback success. -/
theorem AssignmentOrExpressionStatementRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : AssignmentOrExpressionStatementRejects expressionOrdinary
      expressionRejects input rejected) :
    ¬ ∃ statement output,
      AssignmentOrExpressionStatementOrdinaryParses expressionOrdinary input
        statement output := by
  rintro ⟨statement, output, left, afterLeft, tail, afterTail, semicolon,
    leftParsed, tailParsed, semicolonParsed, builds⟩
  cases rejection with
  | leftRejected leftRejected =>
      exact outcomes.successRejectDisjoint leftRejected
        ⟨left, afterLeft, leftParsed⟩
  | rightRejected rejectedLeft rejectedTilde rejectedOperator
        rightRejected =>
      have afterLeftEq := outcomes.successOutputUnique rejectedLeft leftParsed
      subst afterLeftEq
      cases tailParsed with
      | absent tailAbsent =>
          exact rejectedOperator.not_absent tailAbsent.2
      | present successfulTail =>
          cases successfulTail with
          | bitNot span token =>
              exact absent_conflicts_exact rejectedTilde token
          | value successfulTilde successfulOperator rightParsed =>
              have afterOperatorEq := valueOperator_output_unique
                rejectedOperator successfulOperator
              subst afterOperatorEq
              exact outcomes.successRejectDisjoint rightRejected
                ⟨_, _, rightParsed⟩

/-- Ordinary assignment/expression outcomes form a deterministic contract. -/
theorem assignmentOrExpressionStatementDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (AssignmentOrExpressionStatementOrdinaryParses expressionOrdinary)
      (AssignmentOrExpressionStatementRejects expressionOrdinary
        expressionRejects) where
  successOutputUnique :=
    AssignmentOrExpressionStatementOrdinaryParses.output_unique outcomes
  successRejectDisjoint :=
    AssignmentOrExpressionStatementRejects.disjointOrdinary outcomes

/-- A clean assignment suffix embeds into its ordinary counterpart. -/
theorem OptionalAssignmentTailParses.toOrdinary
    {cleanExpression ordinaryExpression :
      Remainder → Syntax.Expr → Remainder → Prop}
    (cleanToOrdinary : ∀ {input value output},
      cleanExpression input value output →
        ordinaryExpression input value output)
    {input output : Remainder} {tail : Option CoreAssignmentTail}
    (parsed : OptionalAssignmentTailParses cleanExpression input tail output) :
    OptionalAssignmentTailParses ordinaryExpression input tail output := by
  cases parsed with
  | absent tailAbsent => exact .absent tailAbsent
  | present tailParsed =>
      apply OptionalAssignmentTailParses.present
      cases tailParsed with
      | bitNot operatorSpan operatorParsed =>
          exact .bitNot operatorSpan operatorParsed
      | value tildeAbsent operatorParsed rightParsed =>
          exact .value tildeAbsent operatorParsed
            (cleanToOrdinary rightParsed)

/-- Every clean Core fallback success is the same ordinary success. -/
theorem AssignmentOrExpressionStatementParses.toOrdinary
    {cleanExpression ordinaryExpression :
      Remainder → Syntax.Expr → Remainder → Prop}
    (cleanToOrdinary : ∀ {input value output},
      cleanExpression input value output →
        ordinaryExpression input value output)
    {input output : Remainder} {statement : Syntax.Statement}
    (parsed : AssignmentOrExpressionStatementParses cleanExpression input
      statement output) :
    AssignmentOrExpressionStatementOrdinaryParses ordinaryExpression input
      statement output := by
  rcases parsed with ⟨left, afterLeft, tail, afterTail, semicolon,
    leftParsed, tailParsed, semicolonParsed, builds⟩
  refine ⟨left, afterLeft, tail, afterTail, semicolon,
    cleanToOrdinary leftParsed, tailParsed.toOrdinary cleanToOrdinary,
    semicolonParsed, ?_⟩
  cases builds with
  | expression => exact .expression _ _
  | value => exact .value _ _ _ _
  | bitNot => exact .bitNot _ _ _

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForItemLeafOutcomeProperties
/-! Deterministic ordinary outcomes for the two Core `for` item branches. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary `for let` success has one final remainder. -/
theorem ForLetItemOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForLetItemOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ForLetItemOrdinaryParses expressionOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftType leftInitializer =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightType
            rightInitializer =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          have afterTypeEq := leftType.output_unique typeOutcomes rightType
          subst afterTypeEq
          exact OptionalLetInitializerOrdinaryParses.output_unique
            expressionOutcomes leftInitializer rightInitializer

/-- Exact `for let` rejection excludes ordinary success. -/
theorem ForLetItemRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input rejected : Remainder}
    (rejection : ForLetItemRejects expressionOrdinary expressionRejects
      typeRejects input rejected) :
    ¬ ∃ item output,
      ForLetItemOrdinaryParses expressionOrdinary input item output := by
  rintro ⟨item, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulName
        successfulType successfulInitializer =>
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

/-- Lift expression and type outcomes through one `for let` item. -/
theorem forLetItemDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects) :
    DeterministicOutcomeSpec
      (ForLetItemOrdinaryParses expressionOrdinary)
      (ForLetItemRejects expressionOrdinary expressionRejects typeRejects)
    where
  successOutputUnique := ForLetItemOrdinaryParses.output_unique
    expressionOutcomes typeOutcomes
  successRejectDisjoint := ForLetItemRejects.disjointOrdinary
    expressionOutcomes typeOutcomes

/-- Ordinary non-let `for` item success has one final remainder. -/
theorem ForAssignmentOrExpressionOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForAssignmentOrExpressionOrdinaryParses expressionOrdinary
      input left afterLeft)
    (rightParsed : ForAssignmentOrExpressionOrdinaryParses expressionOrdinary
      input right afterRight) : afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftExpression, leftAfterExpression, leftTail, leftExpressionParsed,
      leftTailParsed, leftBuild⟩
  rcases rightParsed with
    ⟨rightExpression, rightAfterExpression, rightTail,
      rightExpressionParsed, rightTailParsed, rightBuild⟩
  have afterExpressionEq := expressionOutcomes.successOutputUnique
    leftExpressionParsed rightExpressionParsed
  subst afterExpressionEq
  exact leftTailParsed.output_unique expressionOutcomes rightTailParsed

/-- Exact non-let item rejection excludes ordinary success. -/
theorem ForAssignmentOrExpressionRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : ForAssignmentOrExpressionRejects expressionOrdinary
      expressionRejects input rejected) :
    ¬ ∃ item output,
      ForAssignmentOrExpressionOrdinaryParses expressionOrdinary input item
        output := by
  rintro ⟨item, output, left, afterLeft, tail, leftParsed, tailParsed,
    builds⟩
  cases rejection with
  | leftRejected leftRejected =>
      exact expressionOutcomes.successRejectDisjoint leftRejected
        ⟨left, afterLeft, leftParsed⟩
  | rightRejected rejectedLeft rejectedTilde rejectedOperator
        rightRejected =>
      have afterLeftEq := expressionOutcomes.successOutputUnique rejectedLeft
        leftParsed
      subst afterLeftEq
      cases tailParsed with
      | absent tailAbsent =>
          exact rejectedOperator.not_absent tailAbsent.2
      | present successfulTail =>
          cases successfulTail with
          | bitNot span token =>
              exact absent_conflicts_exact rejectedTilde token
          | value successfulTilde successfulOperator rightParsed =>
              have afterOperatorEq := valueOperator_output_unique
                rejectedOperator successfulOperator
              subst afterOperatorEq
              exact expressionOutcomes.successRejectDisjoint rightRejected
                ⟨_, _, rightParsed⟩

/-- Lift expression outcomes through the non-let `for` item branch. -/
theorem forAssignmentOrExpressionDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (ForAssignmentOrExpressionOrdinaryParses expressionOrdinary)
      (ForAssignmentOrExpressionRejects expressionOrdinary
        expressionRejects) where
  successOutputUnique :=
    ForAssignmentOrExpressionOrdinaryParses.output_unique expressionOutcomes
  successRejectDisjoint :=
    ForAssignmentOrExpressionRejects.disjointOrdinary expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForItemOutcomeProperties
/-! Deterministic outcomes for the let-prioritized public Core `for` item. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Public ordinary `for` item success has one final remainder. -/
theorem ForItemOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ForItemOrdinaryParses expressionOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | letItem leftLet =>
      cases rightParsed with
      | letItem rightLet =>
          exact ForLetItemOrdinaryParses.output_unique expressionOutcomes
            typeOutcomes leftLet rightLet
      | assignmentOrExpression letAbsent rightFallback =>
          cases leftLet with
          | parsed markerSpan marker name type initializer =>
              exact False.elim (absent_conflicts_exact letAbsent marker)
  | assignmentOrExpression leftAbsent leftFallback =>
      cases rightParsed with
      | letItem rightLet =>
          cases rightLet with
          | parsed markerSpan marker name type initializer =>
              exact False.elim (absent_conflicts_exact leftAbsent marker)
      | assignmentOrExpression rightAbsent rightFallback =>
          exact ForAssignmentOrExpressionOrdinaryParses.output_unique
            expressionOutcomes leftFallback rightFallback

/-- Exact public `for` item rejection excludes every ordinary success. -/
theorem ForItemRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input rejected : Remainder}
    (rejection : ForItemRejects expressionOrdinary expressionRejects
      typeRejects input rejected) :
    ¬ ∃ item output,
      ForItemOrdinaryParses expressionOrdinary input item output := by
  rintro ⟨item, output, successful⟩
  cases rejection with
  | letItem markerCurrent itemRejected =>
      cases successful with
      | letItem itemParsed =>
          exact itemRejected.disjointOrdinary expressionOutcomes typeOutcomes
            ⟨_, _, itemParsed⟩
      | assignmentOrExpression letAbsent itemParsed =>
          exact letAbsent ⟨_, markerCurrent⟩
  | assignmentOrExpression letAbsent itemRejected =>
      cases successful with
      | letItem itemParsed =>
          cases itemParsed with
          | parsed markerSpan marker name type initializer =>
              exact absent_conflicts_exact letAbsent marker
      | assignmentOrExpression otherAbsent itemParsed =>
          exact itemRejected.disjointOrdinary expressionOutcomes
            ⟨_, _, itemParsed⟩

/-- Lift expression and type outcomes through the prioritized public item. -/
theorem forItemDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects) :
    DeterministicOutcomeSpec
      (ForItemOrdinaryParses expressionOrdinary)
      (ForItemRejects expressionOrdinary expressionRejects typeRejects) where
  successOutputUnique := ForItemOrdinaryParses.output_unique
    expressionOutcomes typeOutcomes
  successRejectDisjoint := ForItemRejects.disjointOrdinary
    expressionOutcomes typeOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForItemsTailOutcomeProperties
/-! Deterministic ordinary outcomes for Core `for` item-list tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An ordinary Core `for` item-list tail has one final remainder. -/
theorem ForItemsTailOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol)
    {input : Remainder} {left right : List Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemsTailOrdinaryParses expressionOrdinary stop input
      left afterLeft)
    (rightParsed : ForItemsTailOrdinaryParses expressionOrdinary stop input
      right afterRight) : afterLeft = afterRight := by
  have itemOutcomes := forItemDeterministicOutcomeSpec expressionOutcomes
    typeExprDeterministicOutcomeSpec
  induction leftParsed generalizing right afterRight with
  | done leftCommaAbsent =>
      cases rightParsed with
      | done => rfl
      | next rightCommaSpan rightComma rightStopAbsent rightItem
            rightProgress rightTail =>
          exact False.elim
            (absent_conflicts_exact leftCommaAbsent rightComma)
  | next leftCommaSpan leftComma leftStopAbsent leftItem leftProgress leftTail
        inductionHypothesis =>
      cases rightParsed with
      | done rightCommaAbsent =>
          exact False.elim
            (absent_conflicts_exact rightCommaAbsent leftComma)
      | next rightCommaSpan rightComma rightStopAbsent rightItem
            rightProgress rightTail =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          cases afterCommaEq
          have afterItemEq := itemOutcomes.successOutputUnique leftItem
            rightItem
          cases afterItemEq
          exact inductionHypothesis rightTail

/-- Exact tail rejection excludes ordinary tail success. -/
theorem ForItemsTailRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) {stop : Symbol} {input rejected : Remainder}
    (rejection : ForItemsTailRejects expressionOrdinary expressionRejects stop
      input rejected) :
    ¬ ∃ items output,
      ForItemsTailOrdinaryParses expressionOrdinary stop input items output := by
  have itemOutcomes := forItemDeterministicOutcomeSpec expressionOutcomes
    typeExprDeterministicOutcomeSpec
  induction rejection with
  | stopAfterComma commaSpan stopSpan commaParsed stopCurrent =>
      rintro ⟨items, output, successful⟩
      cases successful with
      | done commaAbsent =>
          exact absent_conflicts_exact commaAbsent commaParsed
      | next successfulCommaSpan successfulComma stopAbsent itemParsed
            progress tail =>
          have afterCommaEq := exactToken_output_unique commaParsed
            successfulComma
          cases afterCommaEq
          exact stopAbsent ⟨stopSpan, stopCurrent⟩
  | itemRejected commaSpan commaParsed stopAbsent itemRejected =>
      rintro ⟨items, output, successful⟩
      cases successful with
      | done commaAbsent =>
          exact absent_conflicts_exact commaAbsent commaParsed
      | next successfulCommaSpan successfulComma successfulStopAbsent
            itemParsed progress tail =>
          have afterCommaEq := exactToken_output_unique commaParsed
            successfulComma
          cases afterCommaEq
          exact itemOutcomes.successRejectDisjoint itemRejected
            ⟨_, _, itemParsed⟩
  | laterRejected commaSpan commaParsed stopAbsent itemParsed progress
        tailRejected inductionHypothesis =>
      rintro ⟨items, output, successful⟩
      cases successful with
      | done commaAbsent =>
          exact absent_conflicts_exact commaAbsent commaParsed
      | next successfulCommaSpan successfulComma successfulStopAbsent
            successfulItem successfulProgress successfulTail =>
          have afterCommaEq := exactToken_output_unique commaParsed
            successfulComma
          cases afterCommaEq
          have afterItemEq := itemOutcomes.successOutputUnique itemParsed
            successfulItem
          cases afterItemEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩

/-- Lift expression outcomes through a Core `for` item-list tail. -/
theorem forItemsTailDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol) :
    DeterministicOutcomeSpec
      (ForItemsTailOrdinaryParses expressionOrdinary stop)
      (ForItemsTailRejects expressionOrdinary expressionRejects stop) where
  successOutputUnique := ForItemsTailOrdinaryParses.output_unique
    expressionOutcomes stop
  successRejectDisjoint := ForItemsTailRejects.disjointOrdinary
    expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForItemsOutcomeProperties
/-! Deterministic ordinary outcomes for public Core `for` item lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token_variant {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- An ordinary public Core `for` item list has one final remainder. -/
theorem ForItemsOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol)
    {input : Remainder} {left right : List Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemsOrdinaryParses expressionOrdinary stop input left
      afterLeft)
    (rightParsed : ForItemsOrdinaryParses expressionOrdinary stop input right
      afterRight) : afterLeft = afterRight := by
  have itemOutcomes := forItemDeterministicOutcomeSpec expressionOutcomes
    typeExprDeterministicOutcomeSpec
  have tailOutcomes := forItemsTailDeterministicOutcomeSpec
    expressionOutcomes stop
  cases leftParsed with
  | empty leftStopSpan leftStopCurrent =>
      cases rightParsed with
      | empty => rfl
      | nonempty rightStopAbsent rightFirst rightProgress rightTail =>
          exact False.elim
            (absent_conflicts_token_variant rightStopAbsent leftStopCurrent)
  | nonempty leftStopAbsent leftFirst leftProgress leftTail =>
      cases rightParsed with
      | empty rightStopSpan rightStopCurrent =>
          exact False.elim
            (absent_conflicts_token_variant leftStopAbsent rightStopCurrent)
      | nonempty rightStopAbsent rightFirst rightProgress rightTail =>
          have afterFirstEq := itemOutcomes.successOutputUnique leftFirst
            rightFirst
          cases afterFirstEq
          exact tailOutcomes.successOutputUnique leftTail rightTail

/-- Exact public item-list rejection excludes ordinary success. -/
theorem ForItemsRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) {stop : Symbol} {input rejected : Remainder}
    (rejection : ForItemsRejects expressionOrdinary expressionRejects stop
      input rejected) :
    ¬ ∃ items output,
      ForItemsOrdinaryParses expressionOrdinary stop input items output := by
  have itemOutcomes := forItemDeterministicOutcomeSpec expressionOutcomes
    typeExprDeterministicOutcomeSpec
  have tailOutcomes := forItemsTailDeterministicOutcomeSpec
    expressionOutcomes stop
  rintro ⟨items, output, successful⟩
  cases rejection with
  | firstRejected stopAbsent firstRejected =>
      cases successful with
      | empty stopSpan stopCurrent =>
          exact absent_conflicts_token_variant stopAbsent stopCurrent
      | nonempty successfulStopAbsent firstParsed progress tail =>
          exact itemOutcomes.successRejectDisjoint firstRejected
            ⟨_, _, firstParsed⟩
  | tailRejected stopAbsent firstParsed progress tailRejected =>
      cases successful with
      | empty stopSpan stopCurrent =>
          exact absent_conflicts_token_variant stopAbsent stopCurrent
      | nonempty successfulStopAbsent successfulFirst successfulProgress
            successfulTail =>
          have afterFirstEq := itemOutcomes.successOutputUnique firstParsed
            successfulFirst
          cases afterFirstEq
          exact tailOutcomes.successRejectDisjoint tailRejected
            ⟨_, _, successfulTail⟩

/-- Lift expression outcomes through the public Core `for` item list. -/
theorem forItemsDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol) :
    DeterministicOutcomeSpec
      (ForItemsOrdinaryParses expressionOrdinary stop)
      (ForItemsRejects expressionOrdinary expressionRejects stop) where
  successOutputUnique := ForItemsOrdinaryParses.output_unique
    expressionOutcomes stop
  successRejectDisjoint := ForItemsRejects.disjointOrdinary
    expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementSemicolonExactnessProperties
/-! Exact source spans and remainders for optional Core statement semicolons. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Maximal optional semicolon parsing fixes its optional span and remainder. -/
theorem OptionalStatementSemicolonParses.result_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalStatementSemicolonParses input left afterLeft)
    (rightParsed : OptionalStatementSemicolonParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present rightSpan rightToken =>
          exact False.elim (leftAbsent ⟨rightSpan, rightToken.1⟩)
  | present leftSpan leftToken =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (rightAbsent ⟨leftSpan, leftToken.1⟩)
      | present rightSpan rightToken =>
          rcases leftToken.result_unique rightToken with
            ⟨spanEq, outputEq⟩
          exact ⟨congrArg some spanEq, outputEq⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreAssignmentStatementExactnessProperties
/-!
Exact ordinary Core assignment-or-expression statements from exact expression
outcomes. The proofs preserve assignment priority, optional suffixes, source
spans, diagnosed missing-semicolon successes, and rejection endpoints.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem assignment_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A value-assignment token fixes its operator, source span, and remainder. -/
theorem ValueAssignOperatorParses.result_unique
    {input leftOutput rightOutput : Remainder}
    {leftOperator rightOperator : Located ValueAssignOp}
    (leftParsed : ValueAssignOperatorParses input leftOperator leftOutput)
    (rightParsed : ValueAssignOperatorParses input rightOperator rightOutput) :
    leftOperator = rightOperator ∧ leftOutput = rightOutput :=
  leftParsed.unique rightParsed

/-- Exact expression outcomes fix a prioritized assignment suffix and its
final remainder. -/
theorem AssignmentTailParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : CoreAssignmentTail}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssignmentTailParses expressionOrdinary input left
      afterLeft)
    (rightParsed : AssignmentTailParses expressionOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | bitNot leftSpan leftToken =>
      cases rightParsed with
      | bitNot rightSpan rightToken =>
          rcases leftToken.result_unique rightToken with
            ⟨spanEq, outputEq⟩
          exact ⟨congrArg CoreAssignmentTail.bitNot spanEq, outputEq⟩
      | value rightAbsent rightOperator rightExpression =>
          exact False.elim
            (assignment_absent_conflicts_exact rightAbsent leftToken)
  | value leftAbsent leftOperator leftExpression =>
      cases rightParsed with
      | bitNot rightSpan rightToken =>
          exact False.elim
            (assignment_absent_conflicts_exact leftAbsent rightToken)
      | value rightAbsent rightOperator rightExpression =>
          rcases leftOperator.result_unique rightOperator with
            ⟨operatorEq, afterOperatorEq⟩
          subst operatorEq
          subst afterOperatorEq
          rcases outcomes.successResultUnique leftExpression rightExpression
            with ⟨expressionEq, outputEq⟩
          subst expressionEq
          exact ⟨rfl, outputEq⟩

/-- Maximal optional assignment suffixes fix their value and remainder under
exact expression outcomes. -/
theorem OptionalAssignmentTailParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option CoreAssignmentTail}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalAssignmentTailParses expressionOrdinary input left
      afterLeft)
    (rightParsed : OptionalAssignmentTailParses expressionOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present rightTail =>
          cases rightTail with
          | bitNot span token =>
              exact False.elim
                (assignment_absent_conflicts_exact leftAbsent.1 token)
          | value tildeAbsent operator expression =>
              exact False.elim (operator.not_absent leftAbsent.2)
  | present leftTail =>
      cases rightParsed with
      | absent rightAbsent =>
          cases leftTail with
          | bitNot span token =>
              exact False.elim
                (assignment_absent_conflicts_exact rightAbsent.1 token)
          | value tildeAbsent operator expression =>
              exact False.elim (operator.not_absent rightAbsent.2)
      | present rightTail =>
          rcases leftTail.result_unique outcomes rightTail with
            ⟨tailEq, outputEq⟩
          exact ⟨congrArg some tailEq, outputEq⟩

/-- Ordinary fallback success fixes the complete statement AST, including
assignments whose missing semicolon is diagnosed. -/
theorem AssignmentOrExpressionStatementOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input left afterLeft)
    (rightParsed : AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input right afterRight) : left = right := by
  rcases leftParsed with
    ⟨leftExpression, leftAfterExpression, leftTail, leftAfterTail,
      leftSemicolon, leftExpressionParsed, leftTailParsed,
      leftSemicolonParsed, leftBuild⟩
  rcases rightParsed with
    ⟨rightExpression, rightAfterExpression, rightTail, rightAfterTail,
      rightSemicolon, rightExpressionParsed, rightTailParsed,
      rightSemicolonParsed, rightBuild⟩
  rcases outcomes.successResultUnique leftExpressionParsed
      rightExpressionParsed with ⟨expressionEq, afterExpressionEq⟩
  subst expressionEq
  subst afterExpressionEq
  rcases leftTailParsed.result_unique outcomes rightTailParsed with
    ⟨tailEq, afterTailEq⟩
  subst tailEq
  subst afterTailEq
  rcases leftSemicolonParsed.result_unique rightSemicolonParsed with
    ⟨semicolonEq, outputEq⟩
  subst semicolonEq
  cases leftBuild <;> cases rightBuild <;> rfl

/-- Ordinary fallback success fixes both its statement AST and remainder. -/
theorem AssignmentOrExpressionStatementOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input left afterLeft)
    (rightParsed : AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- Exact expression outcomes fix the initial-expression or committed
right-operand rejection endpoint of an ordinary fallback statement. -/
theorem AssignmentOrExpressionStatementRejects.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input left right : Remainder}
    (leftRejects : AssignmentOrExpressionStatementRejects expressionOrdinary
      expressionRejects input left)
    (rightRejects : AssignmentOrExpressionStatementRejects expressionOrdinary
      expressionRejects input right) : left = right := by
  cases leftRejects with
  | leftRejected leftExpression =>
      cases rightRejects with
      | leftRejected rightExpression =>
          exact outcomes.rejectOutputUnique leftExpression rightExpression
      | rightRejected rightLeft rightTilde rightOperator rightExpression =>
          exact False.elim
            (outcomes.successRejectDisjoint leftExpression
              ⟨_, _, rightLeft⟩)
  | rightRejected leftLeft leftTilde leftOperator leftExpression =>
      cases rightRejects with
      | leftRejected rightExpression =>
          exact False.elim
            (outcomes.successRejectDisjoint rightExpression
              ⟨_, _, leftLeft⟩)
      | rightRejected rightLeft rightTilde rightOperator rightExpression =>
          have afterLeftEq := outcomes.successOutputUnique leftLeft rightLeft
          subst afterLeftEq
          have afterOperatorEq :=
            (leftOperator.result_unique rightOperator).2
          subst afterOperatorEq
          exact outcomes.rejectOutputUnique leftExpression rightExpression

/-- Exact expression outcomes lift to exact ordinary assignment and
expression-statement fallback outcomes. -/
theorem assignmentOrExpressionStatementExactOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    ExactDeterministicOutcomeSpec
      (AssignmentOrExpressionStatementOrdinaryParses expressionOrdinary)
      (AssignmentOrExpressionStatementRejects expressionOrdinary
        expressionRejects) where
  toDeterministicOutcomeSpec :=
    assignmentOrExpressionStatementDeterministicOutcomeSpec
      outcomes.toDeterministicOutcomeSpec
  successValueUnique :=
    AssignmentOrExpressionStatementOrdinaryParses.value_unique outcomes
  rejectOutputUnique :=
    AssignmentOrExpressionStatementRejects.output_unique outcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockIsolationOutcomeProperties
/-!
Capture functionality and deterministic outcomes for balanced Core block
isolation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- A balanced tail scan selects one closing span and endpoint. -/
theorem BalancedBlockTailScans.output_unique
    {input : Remainder} {depth offset : Nat}
    {leftClosing rightClosing : SourceSpan} {leftEnd rightEnd : Nat}
    (leftScan : BalancedBlockTailScans input depth offset leftClosing leftEnd)
    (rightScan : BalancedBlockTailScans input depth offset rightClosing
      rightEnd) : leftClosing = rightClosing ∧ leftEnd = rightEnd := by
  induction leftScan generalizing rightClosing rightEnd with
  | close leftToken =>
      cases rightScan with
      | close rightToken =>
          have tokenEq := tokenAt_unique leftToken rightToken
          cases tokenEq
          exact ⟨rfl, rfl⟩
      | opening rightToken rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          cases tokenEq
      | other rightToken rightNotOpening rightNotClosing rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          have kindEq := congrArg (fun token => token.value) tokenEq
          exact False.elim (rightNotClosing kindEq.symm)
  | opening leftToken leftTail inductionHypothesis =>
      cases rightScan with
      | close rightToken =>
          have tokenEq := tokenAt_unique leftToken rightToken
          cases tokenEq
      | opening rightToken rightTail =>
          exact inductionHypothesis rightTail
      | nestedClosing rightToken rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          cases tokenEq
      | other rightToken rightNotOpening rightNotClosing rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          have kindEq := congrArg (fun token => token.value) tokenEq
          exact False.elim (rightNotOpening kindEq.symm)
  | nestedClosing leftToken leftTail inductionHypothesis =>
      cases rightScan with
      | opening rightToken rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          cases tokenEq
      | nestedClosing rightToken rightTail =>
          exact inductionHypothesis rightTail
      | other rightToken rightNotOpening rightNotClosing rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          have kindEq := congrArg (fun token => token.value) tokenEq
          exact False.elim (rightNotClosing kindEq.symm)
  | other leftToken leftNotOpening leftNotClosing leftTail
        inductionHypothesis =>
      cases rightScan with
      | close rightToken =>
          have tokenEq := tokenAt_unique leftToken rightToken
          have kindEq := congrArg (fun token => token.value) tokenEq
          exact False.elim (leftNotClosing kindEq)
      | opening rightToken rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          have kindEq := congrArg (fun token => token.value) tokenEq
          exact False.elim (leftNotOpening kindEq)
      | nestedClosing rightToken rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          have kindEq := congrArg (fun token => token.value) tokenEq
          exact False.elim (leftNotClosing kindEq)
      | other rightToken rightNotOpening rightNotClosing rightTail =>
          exact inductionHypothesis rightTail

/-- A balanced capture at one input has one exact span and endpoint. -/
theorem BalancedBlockCaptures.output_unique {input : Remainder}
    {left right : BalancedBlockCapture}
    (leftParsed : BalancedBlockCaptures input left)
    (rightParsed : BalancedBlockCaptures input right) : left = right := by
  cases leftParsed with
  | captured leftOpening leftTail =>
      cases rightParsed with
      | captured rightOpening rightTail =>
          have openingEq := tokenAt_unique leftOpening rightOpening
          rcases leftTail.output_unique rightTail with
            ⟨closingEq, endEq⟩
          cases openingEq
          cases closingEq
          cases endEq
          rfl

/-- Ordinary isolated-block success has one final parent remainder. -/
theorem IsolatedCoreBlockOrdinaryParses.output_unique
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects
      input left afterLeft)
    (rightParsed : IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects
      input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | direct leftAbsent leftBody =>
      cases rightParsed with
      | direct rightAbsent rightBody =>
          exact blockOutcomes.successOutputUnique leftBody rightBody
      | captured rightCapture rightBody =>
          exact False.elim (leftAbsent ⟨_, rightCapture⟩)
      | recovered rightCapture rightRejected =>
          exact False.elim (leftAbsent ⟨_, rightCapture⟩)
  | captured leftCapture leftBody =>
      cases rightParsed with
      | direct rightAbsent rightBody =>
          exact False.elim (rightAbsent ⟨_, leftCapture⟩)
      | captured rightCapture rightBody =>
          have captureEq := leftCapture.output_unique rightCapture
          cases captureEq
          rfl
      | recovered rightCapture rightRejected =>
          have captureEq := leftCapture.output_unique rightCapture
          cases captureEq
          rfl
  | recovered leftCapture leftRejected =>
      cases rightParsed with
      | direct rightAbsent rightBody =>
          exact False.elim (rightAbsent ⟨_, leftCapture⟩)
      | captured rightCapture rightBody =>
          have captureEq := leftCapture.output_unique rightCapture
          cases captureEq
          rfl
      | recovered rightCapture rightRejected =>
          have captureEq := leftCapture.output_unique rightCapture
          cases captureEq
          rfl

/-- An externally visible isolation rejection excludes every ordinary
isolated-block success. -/
theorem IsolatedCoreBlockRejects.disjointOrdinary
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects)
    {input rejected : Remainder}
    (rejection : IsolatedCoreBlockRejects blockRejects input rejected) :
    ¬ ∃ body output,
      IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects input body
        output := by
  rintro ⟨body, output, successful⟩
  cases rejection with
  | direct captureAbsent bodyRejected =>
      cases successful with
      | direct otherAbsent bodyParsed =>
          exact blockOutcomes.successRejectDisjoint bodyRejected
            ⟨_, _, bodyParsed⟩
      | captured captureParsed bodyParsed =>
          exact captureAbsent ⟨_, captureParsed⟩
      | recovered captureParsed otherRejected =>
          exact captureAbsent ⟨_, captureParsed⟩

/-- Lift deterministic raw-block outcomes through balanced isolation and
captured child-rejection recovery. -/
theorem isolatedCoreBlockDeterministicOutcomeSpec
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects) :
    DeterministicOutcomeSpec
      (IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects)
      (IsolatedCoreBlockRejects blockRejects) where
  successOutputUnique :=
    IsolatedCoreBlockOrdinaryParses.output_unique blockOutcomes
  successRejectDisjoint :=
    IsolatedCoreBlockRejects.disjointOrdinary blockOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockOutcomeProperties
/-!
Functionality, rejection exclusivity, and clean embedding for ordinary raw
Core-block outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary block-item success has one final remainder. -/
theorem CoreBlockItemsParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {leftBody rightBody : List Syntax.Statement}
    {leftClosing rightClosing : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : CoreBlockItemsParses statementOrdinary input leftBody
      leftClosing afterLeft)
    (rightParsed : CoreBlockItemsParses statementOrdinary input rightBody
      rightClosing afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightBody rightClosing afterRight with
  | close leftClosing leftToken =>
      cases rightParsed with
      | close rightClosing rightToken =>
          exact exactToken_output_unique leftToken rightToken
      | next notAtEnd closingAbsent statementParsed progress tail =>
          exact False.elim (absent_conflicts_exact closingAbsent leftToken)
  | next notAtEnd closingAbsent statementParsed progress tail
        inductionHypothesis =>
      cases rightParsed with
      | close rightClosing rightToken =>
          exact False.elim (absent_conflicts_exact closingAbsent rightToken)
      | next otherNotAtEnd otherClosingAbsent otherStatementParsed
            otherProgress otherTail =>
          have afterStatementEq := outcomes.successOutputUnique statementParsed
            otherStatementParsed
          subst afterStatementEq
          exact inductionHypothesis otherTail

/-- Diagnostic-inclusive complete Core-block success has one final remainder. -/
theorem CoreBlockOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {policy : CoreBlockTailPolicy}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : CoreBlockOrdinaryParses statementOrdinary policy input left
      afterLeft)
    (rightParsed : CoreBlockOrdinaryParses statementOrdinary policy input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpening leftClosing leftToken leftBody =>
      cases rightParsed with
      | parsed rightOpening rightClosing rightToken rightBody =>
          have afterOpeningEq := exactToken_output_unique leftToken rightToken
          subst afterOpeningEq
          exact leftBody.output_unique outcomes rightBody

/-- Ordinary block success preserves the carrier and active window whenever
ordinary statements do. -/
theorem CoreBlockOrdinaryParses.output_window
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {policy : CoreBlockTailPolicy}
    (statementWindow : ∀ {input statement output},
      statementOrdinary input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {block : Syntax.Block}
    (parsed : CoreBlockOrdinaryParses statementOrdinary policy input block
      output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed openingSpan closingSpan openingToken bodyParsed =>
      rcases openingToken with ⟨openingAt, rfl⟩
      exact bodyParsed.output_window statementWindow

/-- An exact item rejection excludes every ordinary item success. -/
theorem CoreBlockItemsRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input rejected : Remainder}
    (rejection : CoreBlockItemsRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ body closingSpan output,
      CoreBlockItemsParses statementOrdinary input body closingSpan output := by
  induction rejection with
  | missingClose closingAbsent atEnd =>
      rintro ⟨body, closingSpan, output, parsed⟩
      cases parsed with
      | close span closingParsed =>
          exact absent_conflicts_exact closingAbsent closingParsed
      | next notAtEnd otherAbsent statementParsed progress tail =>
          exact (Nat.not_lt_of_ge atEnd) notAtEnd
  | statementRejected notAtEnd closingAbsent statementRejected =>
      rintro ⟨body, closingSpan, output, parsed⟩
      cases parsed with
      | close span closingParsed =>
          exact absent_conflicts_exact closingAbsent closingParsed
      | next otherNotAtEnd otherAbsent statementParsed progress tail =>
          exact outcomes.successRejectDisjoint statementRejected
            ⟨_, _, statementParsed⟩
  | laterRejected notAtEnd closingAbsent statementParsed progress tailRejected
        inductionHypothesis =>
      rintro ⟨body, closingSpan, output, parsed⟩
      cases parsed with
      | close span closingParsed =>
          exact absent_conflicts_exact closingAbsent closingParsed
      | next otherNotAtEnd otherAbsent otherStatementParsed otherProgress
            otherTail =>
          have afterStatementEq := outcomes.successOutputUnique statementParsed
            otherStatementParsed
          subst afterStatementEq
          exact inductionHypothesis ⟨_, _, _, otherTail⟩

/-- Exact complete-block rejection excludes ordinary complete-block success. -/
theorem CoreBlockRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {policy : CoreBlockTailPolicy}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input rejected : Remainder}
    (rejection : CoreBlockRejects statementOrdinary statementRejects policy
      input rejected) :
    ¬ ∃ block output,
      CoreBlockOrdinaryParses statementOrdinary policy input block output := by
  rintro ⟨block, output, parsed⟩
  cases rejection with
  | openingMissing openingAbsent =>
      cases parsed with
      | parsed openingSpan closingSpan openingParsed bodyParsed =>
          exact absent_conflicts_exact openingAbsent openingParsed
  | itemsRejected rejectedSpan rejectedOpening itemsRejected =>
      cases parsed with
      | parsed openingSpan closingSpan openingParsed bodyParsed =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            openingParsed
          subst afterOpeningEq
          exact itemsRejected.disjointOrdinary outcomes
            ⟨_, _, _, bodyParsed⟩

/-- Raw Core-block ordinary outcomes are deterministic and exclusive. -/
theorem coreBlockDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (policy : CoreBlockTailPolicy)
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects) :
    DeterministicOutcomeSpec
      (CoreBlockOrdinaryParses statementOrdinary policy)
      (CoreBlockRejects statementOrdinary statementRejects policy) where
  successOutputUnique := CoreBlockOrdinaryParses.output_unique outcomes
  successRejectDisjoint := CoreBlockRejects.disjointOrdinary outcomes

/-- Clean block items embed when clean statement success embeds. -/
theorem CoreBlockItemsParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {body : List Syntax.Statement}
    {closingSpan : SourceSpan}
    (parsed : CoreBlockItemsParses statementClean input body closingSpan
      output) :
    CoreBlockItemsParses statementOrdinary input body closingSpan output := by
  induction parsed with
  | close span closing => exact .close span closing
  | next notAtEnd closingAbsent statementParsed progress tail
        inductionHypothesis =>
      exact .next notAtEnd closingAbsent (cleanToOrdinary statementParsed)
        progress inductionHypothesis

/-- Diagnostic-free Core-block grammar embeds into ordinary success. -/
theorem CoreBlockParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {policy : CoreBlockTailPolicy} {input output : Remainder}
    {block : Syntax.Block}
    (parsed : CoreBlockParses statementClean policy input block output) :
    CoreBlockOrdinaryParses statementOrdinary policy input block output := by
  cases parsed with
  | parsed openingSpan closingSpan openingParsed bodyParsed tailsValid =>
      exact .parsed openingSpan closingSpan openingParsed
        (bodyParsed.toOrdinary cleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchDefaultOutcomeProperties
/-! Deterministic diagnostic-inclusive outcomes for optional Core default. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Optional default success has one output remainder. -/
theorem OptionalDefaultBodyOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Option Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary input
      left afterLeft)
    (rightParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent rightAbsent => rfl
      | present rightMarkerSpan rightMarker rightBody =>
          exact False.elim (absent_conflicts_exact leftAbsent rightMarker)
  | present leftMarkerSpan leftMarker leftBody =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftMarker)
      | present rightMarkerSpan rightMarker rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          cases afterMarkerEq
          exact leftBody.output_unique statementOutcomes rightBody

/-- Exact optional-default rejection excludes ordinary success. -/
theorem OptionalDefaultBodyRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : OptionalDefaultBodyRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ body output,
      OptionalDefaultBodyOrdinaryParses statementOrdinary input body output := by
  rintro ⟨body, output, successful⟩
  cases rejection with
  | bodyRejected rejectedMarkerSpan rejectedMarker rejectedBody =>
      cases successful with
      | absent defaultAbsent =>
          exact absent_conflicts_exact defaultAbsent rejectedMarker
      | present successfulMarkerSpan successfulMarker successfulBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          exact rejectedBody.disjointOrdinary statementOutcomes
            ⟨_, _, successfulBody⟩

/-- Lift recursive statement outcomes through prioritized optional default. -/
theorem optionalDefaultBodyDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (OptionalDefaultBodyOrdinaryParses statementOrdinary)
      (OptionalDefaultBodyRejects statementOrdinary statementRejects) where
  successOutputUnique := OptionalDefaultBodyOrdinaryParses.output_unique
    statementOutcomes
  successRejectDisjoint := OptionalDefaultBodyRejects.disjointOrdinary
    statementOutcomes

/-- Every clean optional-default derivation embeds into the ordinary
relation. -/
theorem OptionalDefaultBodyParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    (statementToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {body : Option Syntax.Block}
    (parsed : OptionalDefaultBodyParses statementClean input body output) :
    OptionalDefaultBodyOrdinaryParses statementOrdinary input body output := by
  cases parsed with
  | absent defaultAbsent => exact .absent defaultAbsent
  | present markerSpan markerParsed bodyParsed =>
      exact .present markerSpan markerParsed
        (bodyParsed.toOrdinary statementToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchCaseOutcomeProperties
/-! Deterministic diagnostic-inclusive outcomes for one Core match case. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary match-case success has one final remainder. -/
theorem MatchCaseOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : Syntax.MatchCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
      input left afterLeft)
    (rightParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
      input right afterRight) : afterLeft = afterRight := by
  have blockOutcomes := coreBlockDeterministicOutcomeSpec .require
    statementOutcomes
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftPattern leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightPattern rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          cases afterMarkerEq
          have afterPatternEq := patternOutcomes.successOutputUnique
            leftPattern rightPattern
          cases afterPatternEq
          exact blockOutcomes.successOutputUnique leftBody rightBody

/-- Exact match-case rejection excludes ordinary success. -/
theorem MatchCaseRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input rejected : Remainder}
    (rejection : MatchCaseRejects statementOrdinary statementRejects
      patternOrdinary patternRejects input rejected) :
    ¬ ∃ arm output,
      MatchCaseOrdinaryParses statementOrdinary patternOrdinary input arm
        output := by
  rintro ⟨arm, output, successful⟩
  have blockOutcomes := coreBlockDeterministicOutcomeSpec .require
    statementOutcomes
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulPattern
        successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | patternRejected rejectedMarkerSpan rejectedMarker rejectedPattern =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          exact patternOutcomes.successRejectDisjoint rejectedPattern
            ⟨_, _, successfulPattern⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedPattern
            rejectedBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterPatternEq := patternOutcomes.successOutputUnique
            rejectedPattern successfulPattern
          cases afterPatternEq
          exact blockOutcomes.successRejectDisjoint rejectedBody
            ⟨_, _, successfulBody⟩

/-- Lift statement and pattern outcomes through one Core match case. -/
theorem matchCaseDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects) :
    DeterministicOutcomeSpec
      (MatchCaseOrdinaryParses statementOrdinary patternOrdinary)
      (MatchCaseRejects statementOrdinary statementRejects patternOrdinary
        patternRejects) where
  successOutputUnique := MatchCaseOrdinaryParses.output_unique
    statementOutcomes patternOutcomes
  successRejectDisjoint := MatchCaseRejects.disjointOrdinary
    statementOutcomes patternOutcomes

/-- Every clean match-case derivation embeds into the ordinary relation. -/
theorem MatchCaseParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {patternClean patternOrdinary :
      Remainder → Syntax.Pattern → Remainder → Prop}
    (statementToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    (patternToOrdinary : ∀ {input pattern output},
      patternClean input pattern output →
        patternOrdinary input pattern output)
    {input output : Remainder} {arm : Syntax.MatchCase}
    (parsed : MatchCaseParses statementClean patternClean input arm output) :
    MatchCaseOrdinaryParses statementOrdinary patternOrdinary input arm
      output := by
  cases parsed with
  | parsed markerSpan markerParsed patternParsed bodyParsed =>
      exact .parsed markerSpan markerParsed
        (patternToOrdinary patternParsed)
        (bodyParsed.toOrdinary statementToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchCasesOutcomeProperties
/-! Deterministic outcomes for the maximal Core match-case sequence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every ordinary case starts at an exact `case` token. -/
theorem MatchCaseOrdinaryParses.startsAt
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {input output : Remainder} {arm : Syntax.MatchCase}
    (parsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary input
      arm output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .keyword .caseKw
    } := by
  cases parsed with
  | parsed markerSpan markerParsed patternParsed bodyParsed =>
      exact ⟨markerSpan, markerParsed.1⟩

/-- Ordinary maximal case-list success has one final remainder. -/
theorem MatchCasesOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : List Syntax.MatchCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
      input left afterLeft)
    (rightParsed : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
      input right afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done rightAbsent => rfl
      | next rightArm rightProgress rightTail =>
          exact False.elim (leftAbsent rightArm.startsAt)
  | next leftArm leftProgress leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent leftArm.startsAt)
      | next rightArm rightProgress rightTail =>
          have afterArmEq := MatchCaseOrdinaryParses.output_unique
            statementOutcomes patternOutcomes leftArm rightArm
          subst afterArmEq
          exact inductionHypothesis rightTail

/-- Guarded exact case-list rejection excludes maximal ordinary success. -/
theorem MatchCasesRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input rejected : Remainder}
    (rejection : MatchCasesRejects statementOrdinary statementRejects
      patternOrdinary patternRejects input rejected) :
    ¬ ∃ arms output,
      MatchCasesOrdinaryParses statementOrdinary patternOrdinary input arms
        output := by
  induction rejection with
  | firstRejected casePresent armRejected =>
      rintro ⟨arms, output, successful⟩
      cases successful with
      | done caseAbsent => exact caseAbsent casePresent
      | next armParsed progress tail =>
          exact MatchCaseRejects.disjointOrdinary statementOutcomes
            patternOutcomes armRejected ⟨_, _, armParsed⟩
  | laterRejected rejectedArm progress tailRejected inductionHypothesis =>
      rintro ⟨arms, output, successful⟩
      cases successful with
      | done caseAbsent => exact caseAbsent rejectedArm.startsAt
      | next successfulArm otherProgress successfulTail =>
          have afterArmEq := MatchCaseOrdinaryParses.output_unique
            statementOutcomes patternOutcomes rejectedArm successfulArm
          subst afterArmEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩

/-- Lift supplied statement and pattern outcomes through the case sequence. -/
theorem matchCasesDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects) :
    DeterministicOutcomeSpec
      (MatchCasesOrdinaryParses statementOrdinary patternOrdinary)
      (MatchCasesRejects statementOrdinary statementRejects patternOrdinary
        patternRejects) where
  successOutputUnique := MatchCasesOrdinaryParses.output_unique
    statementOutcomes patternOutcomes
  successRejectDisjoint := MatchCasesRejects.disjointOrdinary
    statementOutcomes patternOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementWhileOutcomeProperties
/-! Deterministic ordinary outcomes for canonical Core `while`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary Core `while` success has one final remainder. -/
theorem WhileStatementOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input left afterLeft)
    (rightParsed : WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input right afterRight) : afterLeft = afterRight := by
  have blockOutcomes := coreBlockDeterministicOutcomeSpec .require
    statementOutcomes
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftClosingSpan leftMarker
        leftOpening leftCondition leftClosing leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightClosingSpan rightMarker
            rightOpening rightCondition rightClosing rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          cases afterMarkerEq
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          cases afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            leftCondition rightCondition
          cases afterConditionEq
          have afterClosingEq := exactToken_output_unique leftClosing
            rightClosing
          cases afterClosingEq
          exact blockOutcomes.successOutputUnique leftBody rightBody

/-- Exact Core `while` rejection excludes ordinary success. -/
theorem WhileStatementRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : WhileStatementRejects expressionOrdinary expressionRejects
      statementOrdinary statementRejects input rejected) :
    ¬ ∃ statement output,
      WhileStatementOrdinaryParses expressionOrdinary statementOrdinary input
        statement output := by
  rintro ⟨statement, output, successful⟩
  have blockOutcomes := coreBlockDeterministicOutcomeSpec .require
    statementOutcomes
  cases successful with
  | parsed successfulMarkerSpan successfulOpeningSpan successfulClosingSpan
        successfulMarker successfulOpening successfulCondition
        successfulClosing successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | openingMissing rejectedMarkerSpan rejectedMarker openingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          exact absent_conflicts_exact openingAbsent successfulOpening
      | conditionRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedMarker rejectedOpening rejectedCondition =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          cases afterOpeningEq
          exact expressionOutcomes.successRejectDisjoint rejectedCondition
            ⟨_, _, successfulCondition⟩
      | closingMissing rejectedMarkerSpan rejectedOpeningSpan rejectedMarker
            rejectedOpening rejectedCondition closingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          cases afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          cases afterConditionEq
          exact absent_conflicts_exact closingAbsent successfulClosing
      | bodyRejected rejectedMarkerSpan rejectedOpeningSpan rejectedClosingSpan
            rejectedMarker rejectedOpening rejectedCondition rejectedClosing
            rejectedBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          cases afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          cases afterConditionEq
          have afterClosingEq := exactToken_output_unique rejectedClosing
            successfulClosing
          cases afterClosingEq
          exact blockOutcomes.successRejectDisjoint rejectedBody
            ⟨_, _, successfulBody⟩

/-- Lift expression and recursive-statement outcomes through one Core
`while` statement. -/
theorem whileStatementDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (WhileStatementOrdinaryParses expressionOrdinary statementOrdinary)
      (WhileStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects) where
  successOutputUnique := WhileStatementOrdinaryParses.output_unique
    expressionOutcomes statementOutcomes
  successRejectDisjoint := WhileStatementRejects.disjointOrdinary
    expressionOutcomes statementOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementControlLeafOutcomeProperties
/-! Deterministic outcomes for Core block and terminated-control statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Keyword-plus-semicolon control success has a unique remainder. -/
theorem TerminatedControlStatementOrdinaryParses.output_unique
    {keyword : HardKeyword} {statementValue : Syntax.StatementValue}
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : TerminatedControlStatementOrdinaryParses keyword
      statementValue input left afterLeft)
    (rightParsed : TerminatedControlStatementOrdinaryParses keyword
      statementValue input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftSemicolonSpan leftMarker leftSemicolon =>
      cases rightParsed with
      | parsed rightMarkerSpan rightSemicolonSpan rightMarker
            rightSemicolon =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          exact exactToken_output_unique leftSemicolon rightSemicolon

/-- Exact terminated-control rejection excludes success. -/
theorem TerminatedControlStatementRejects.disjointOrdinary
    {keyword : HardKeyword} {statementValue : Syntax.StatementValue}
    {input rejected : Remainder}
    (rejection : TerminatedControlStatementRejects keyword input rejected) :
    ¬ ∃ statement output,
      TerminatedControlStatementOrdinaryParses keyword statementValue input
        statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulSemicolonSpan successfulMarker
        successfulSemicolon =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | semicolonMissing rejectedMarkerSpan rejectedMarker
            semicolonAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact absent_conflicts_exact semicolonAbsent successfulSemicolon

/-- Deterministic outcome of one fixed terminated-control statement. -/
theorem terminatedControlStatementDeterministicOutcomeSpec
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue) :
    DeterministicOutcomeSpec
      (TerminatedControlStatementOrdinaryParses keyword statementValue)
      (TerminatedControlStatementRejects keyword) where
  successOutputUnique :=
    TerminatedControlStatementOrdinaryParses.output_unique
  successRejectDisjoint :=
    TerminatedControlStatementRejects.disjointOrdinary

/-- Diagnostic-inclusive block statements have a unique remainder. -/
theorem BlockStatementOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : BlockStatementOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : BlockStatementOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftBody =>
      cases rightParsed with
      | parsed rightBody =>
          exact (coreBlockDeterministicOutcomeSpec .require
            statementOutcomes).successOutputUnique leftBody rightBody

/-- Raw block rejection excludes a block-statement success. -/
theorem BlockStatementRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : BlockStatementRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ statement output,
      BlockStatementOrdinaryParses statementOrdinary input statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed bodyParsed =>
      exact (coreBlockDeterministicOutcomeSpec .require
        statementOutcomes).successRejectDisjoint rejection
          ⟨_, _, bodyParsed⟩

/-- Lift recursive statement outcomes through `blockStatement`. -/
theorem blockStatementDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (BlockStatementOrdinaryParses statementOrdinary)
      (BlockStatementRejects statementOrdinary statementRejects) where
  successOutputUnique := BlockStatementOrdinaryParses.output_unique
    statementOutcomes
  successRejectDisjoint := BlockStatementRejects.disjointOrdinary
    statementOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForStatementSuccessOutcomeProperties
/-! Functional ordinary success for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary Core `for` success has one final remainder. -/
theorem ForStatementOrdinaryParses.output_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input left afterLeft)
    (rightParsed : ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input right afterRight) : afterLeft = afterRight := by
  have initializerOutcomes := forItemsDeterministicOutcomeSpec
    expressionOutcomes .semicolon
  have postOutcomes := forItemsDeterministicOutcomeSpec expressionOutcomes
    .rightParen
  have blockOutcomes := coreBlockDeterministicOutcomeSpec .require
    statementOutcomes
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftFirstSemicolonSpan
        leftSecondSemicolonSpan leftClosingSpan leftMarker leftOpening
        leftInitializer leftFirstSemicolon leftCondition leftSecondSemicolon
        leftPost leftClosing leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightFirstSemicolonSpan
            rightSecondSemicolonSpan rightClosingSpan rightMarker rightOpening
            rightInitializer rightFirstSemicolon rightCondition
            rightSecondSemicolon rightPost rightClosing rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            leftInitializer rightInitializer
          subst afterInitializerEq
          have afterFirstSemicolonEq := exactToken_output_unique
            leftFirstSemicolon rightFirstSemicolon
          subst afterFirstSemicolonEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            leftCondition rightCondition
          subst afterConditionEq
          have afterSecondSemicolonEq := exactToken_output_unique
            leftSecondSemicolon rightSecondSemicolon
          subst afterSecondSemicolonEq
          have afterPostEq := postOutcomes.successOutputUnique leftPost
            rightPost
          subst afterPostEq
          have afterClosingEq := exactToken_output_unique leftClosing
            rightClosing
          subst afterClosingEq
          exact blockOutcomes.successOutputUnique leftBody rightBody

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForStatementRejectionOutcomeProperties
/-! Rejection disjointness for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact Core `for` rejection excludes ordinary success. -/
theorem ForStatementRejects.disjointOrdinary
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : ForStatementRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects input rejected) :
    ¬ ∃ statement output, ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input statement output := by
  rintro ⟨statement, output, successful⟩
  have initializerOutcomes := forItemsDeterministicOutcomeSpec
    expressionOutcomes .semicolon
  have postOutcomes := forItemsDeterministicOutcomeSpec expressionOutcomes
    .rightParen
  have blockOutcomes := coreBlockDeterministicOutcomeSpec .require
    statementOutcomes
  cases successful with
  | parsed successfulMarkerSpan successfulOpeningSpan
        successfulFirstSemicolonSpan successfulSecondSemicolonSpan
        successfulClosingSpan successfulMarker successfulOpening
        successfulInitializer successfulFirstSemicolon successfulCondition
        successfulSecondSemicolon successfulPost successfulClosing
        successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | openingMissing rejectedMarkerSpan rejectedMarker openingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact absent_conflicts_exact openingAbsent successfulOpening
      | initializerRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedMarker rejectedOpening rejectedInitializer =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact initializerOutcomes.successRejectDisjoint
            rejectedInitializer ⟨_, _, successfulInitializer⟩
      | firstSemicolonMissing rejectedMarkerSpan rejectedOpeningSpan
            rejectedMarker rejectedOpening rejectedInitializer
            semicolonAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            rejectedInitializer successfulInitializer
          subst afterInitializerEq
          exact absent_conflicts_exact semicolonAbsent
            successfulFirstSemicolon
      | conditionRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedSemicolonSpan rejectedMarker rejectedOpening
            rejectedInitializer rejectedSemicolon rejectedCondition =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            rejectedInitializer successfulInitializer
          subst afterInitializerEq
          have afterSemicolonEq := exactToken_output_unique rejectedSemicolon
            successfulFirstSemicolon
          subst afterSemicolonEq
          exact expressionOutcomes.successRejectDisjoint rejectedCondition
            ⟨_, _, successfulCondition⟩
      | secondSemicolonMissing rejectedMarkerSpan rejectedOpeningSpan
            rejectedFirstSemicolonSpan rejectedMarker rejectedOpening
            rejectedInitializer rejectedFirstSemicolon rejectedCondition
            semicolonAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            rejectedInitializer successfulInitializer
          subst afterInitializerEq
          have afterFirstSemicolonEq := exactToken_output_unique
            rejectedFirstSemicolon successfulFirstSemicolon
          subst afterFirstSemicolonEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          exact absent_conflicts_exact semicolonAbsent
            successfulSecondSemicolon
      | postRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedFirstSemicolonSpan rejectedSecondSemicolonSpan
            rejectedMarker rejectedOpening rejectedInitializer
            rejectedFirstSemicolon rejectedCondition rejectedSecondSemicolon
            rejectedPost =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            rejectedInitializer successfulInitializer
          subst afterInitializerEq
          have afterFirstSemicolonEq := exactToken_output_unique
            rejectedFirstSemicolon successfulFirstSemicolon
          subst afterFirstSemicolonEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          have afterSecondSemicolonEq := exactToken_output_unique
            rejectedSecondSemicolon successfulSecondSemicolon
          subst afterSecondSemicolonEq
          exact postOutcomes.successRejectDisjoint rejectedPost
            ⟨_, _, successfulPost⟩
      | closingMissing rejectedMarkerSpan rejectedOpeningSpan
            rejectedFirstSemicolonSpan rejectedSecondSemicolonSpan
            rejectedMarker rejectedOpening rejectedInitializer
            rejectedFirstSemicolon rejectedCondition rejectedSecondSemicolon
            rejectedPost closingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            rejectedInitializer successfulInitializer
          subst afterInitializerEq
          have afterFirstSemicolonEq := exactToken_output_unique
            rejectedFirstSemicolon successfulFirstSemicolon
          subst afterFirstSemicolonEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          have afterSecondSemicolonEq := exactToken_output_unique
            rejectedSecondSemicolon successfulSecondSemicolon
          subst afterSecondSemicolonEq
          have afterPostEq := postOutcomes.successOutputUnique rejectedPost
            successfulPost
          subst afterPostEq
          exact absent_conflicts_exact closingAbsent successfulClosing
      | bodyRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedFirstSemicolonSpan rejectedSecondSemicolonSpan
            rejectedClosingSpan rejectedMarker rejectedOpening
            rejectedInitializer rejectedFirstSemicolon rejectedCondition
            rejectedSecondSemicolon rejectedPost rejectedClosing
            rejectedBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            rejectedInitializer successfulInitializer
          subst afterInitializerEq
          have afterFirstSemicolonEq := exactToken_output_unique
            rejectedFirstSemicolon successfulFirstSemicolon
          subst afterFirstSemicolonEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          have afterSecondSemicolonEq := exactToken_output_unique
            rejectedSecondSemicolon successfulSecondSemicolon
          subst afterSecondSemicolonEq
          have afterPostEq := postOutcomes.successOutputUnique rejectedPost
            successfulPost
          subst afterPostEq
          have afterClosingEq := exactToken_output_unique rejectedClosing
            successfulClosing
          subst afterClosingEq
          exact blockOutcomes.successRejectDisjoint rejectedBody
            ⟨_, _, successfulBody⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForStatementOutcomeProperties
/-! Deterministic ordinary outcomes for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Lift recursive statement and expression outcomes through Core `for`. -/
theorem forStatementDeterministicOutcomeSpec
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (ForStatementOrdinaryParses statementOrdinary expressionOrdinary)
      (ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects) where
  successOutputUnique := ForStatementOrdinaryParses.output_unique
    statementOutcomes expressionOutcomes
  successRejectDisjoint := ForStatementRejects.disjointOrdinary
    statementOutcomes expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementOptionalElseOutcomeProperties
/-! Deterministic diagnostic-inclusive outcomes for optional Core `else`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Optional `else` success has one output remainder. -/
theorem OptionalElseBodyOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Option Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalElseBodyOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : OptionalElseBodyOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent rightAbsent => rfl
      | present rightMarkerSpan rightMarker rightBody =>
          exact False.elim (absent_conflicts_exact leftAbsent rightMarker)
  | present leftMarkerSpan leftMarker leftBody =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftMarker)
      | present rightMarkerSpan rightMarker rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          exact leftBody.output_unique statementOutcomes rightBody

/-- Exact optional `else` rejection excludes success. -/
theorem OptionalElseBodyRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : OptionalElseBodyRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ body output,
      OptionalElseBodyOrdinaryParses statementOrdinary input body output := by
  rintro ⟨body, output, successful⟩
  cases rejection with
  | bodyRejected rejectedMarkerSpan rejectedMarker rejectedBody =>
      cases successful with
      | absent elseAbsent =>
          exact absent_conflicts_exact elseAbsent rejectedMarker
      | present successfulMarkerSpan successfulMarker successfulBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact rejectedBody.disjointOrdinary statementOutcomes
            ⟨_, _, successfulBody⟩

/-- Lift recursive statement outcomes through prioritized optional `else`. -/
theorem optionalElseBodyDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (OptionalElseBodyOrdinaryParses statementOrdinary)
      (OptionalElseBodyRejects statementOrdinary statementRejects) where
  successOutputUnique := OptionalElseBodyOrdinaryParses.output_unique
    statementOutcomes
  successRejectDisjoint := OptionalElseBodyRejects.disjointOrdinary
    statementOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementIfOutcomeProperties
/-! Deterministic diagnostic-inclusive outcomes for canonical Core `if`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary Core `if` success has one final remainder. -/
theorem IfStatementOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input left afterLeft)
    (rightParsed : IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftClosingSpan leftMarker
        leftOpening leftCondition leftClosing leftThen leftElse =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightClosingSpan rightMarker
            rightOpening rightCondition rightClosing rightThen rightElse =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            leftCondition rightCondition
          subst afterConditionEq
          have afterClosingEq := exactToken_output_unique leftClosing
            rightClosing
          subst afterClosingEq
          have afterThenEq := leftThen.output_unique statementOutcomes
            rightThen
          subst afterThenEq
          exact OptionalElseBodyOrdinaryParses.output_unique statementOutcomes
            leftElse rightElse

/-- Exact Core `if` rejection excludes ordinary success. -/
theorem IfStatementRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : IfStatementRejects expressionOrdinary expressionRejects
      statementOrdinary statementRejects input rejected) :
    ¬ ∃ statement output,
      IfStatementOrdinaryParses expressionOrdinary statementOrdinary input
        statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulOpeningSpan successfulClosingSpan
        successfulMarker successfulOpening successfulCondition
        successfulClosing successfulThen successfulElse =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | openingMissing rejectedMarkerSpan rejectedMarker openingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact absent_conflicts_exact openingAbsent successfulOpening
      | conditionRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedMarker rejectedOpening rejectedCondition =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact expressionOutcomes.successRejectDisjoint rejectedCondition
            ⟨_, _, successfulCondition⟩
      | closingMissing rejectedMarkerSpan rejectedOpeningSpan rejectedMarker
            rejectedOpening rejectedCondition closingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          exact absent_conflicts_exact closingAbsent successfulClosing
      | thenRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedClosingSpan rejectedMarker rejectedOpening
            rejectedCondition rejectedClosing rejectedThen =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          have afterClosingEq := exactToken_output_unique rejectedClosing
            successfulClosing
          subst afterClosingEq
          exact rejectedThen.disjointOrdinary statementOutcomes
            ⟨_, _, successfulThen⟩
      | elseRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedClosingSpan rejectedMarker rejectedOpening
            rejectedCondition rejectedClosing rejectedThen rejectedElse =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          have afterClosingEq := exactToken_output_unique rejectedClosing
            successfulClosing
          subst afterClosingEq
          have afterThenEq := rejectedThen.output_unique statementOutcomes
            successfulThen
          subst afterThenEq
          exact (OptionalElseBodyRejects.disjointOrdinary statementOutcomes
            rejectedElse) ⟨_, _, successfulElse⟩

/-- Lift expression and recursive statement outcomes through Core `if`. -/
theorem ifStatementDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (IfStatementOrdinaryParses expressionOrdinary statementOrdinary)
      (IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects) where
  successOutputUnique := IfStatementOrdinaryParses.output_unique
    expressionOutcomes statementOutcomes
  successRejectDisjoint := IfStatementRejects.disjointOrdinary
    expressionOutcomes statementOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchScrutineesOutcomeProperties
/-! Deterministic outcomes for requiring nonempty Core match scrutinees. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev RequireScrutineesOrdinaryParses := RequireScrutineesParses

/-- Empty parsed scrutinees reject without consuming any further token. -/
inductive RequireScrutineesRejects (values : DelimitedList Syntax.Expr) :
    Remainder → Remainder → Prop where
  | empty {input : Remainder} (emptyValues : values.elements = []) :
      RequireScrutineesRejects values input input

/-- Nonempty scrutinee conversion has one output remainder. -/
theorem RequireScrutineesOrdinaryParses.output_unique
    {values : DelimitedList Syntax.Expr} {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : RequireScrutineesOrdinaryParses values input left afterLeft)
    (rightParsed : RequireScrutineesOrdinaryParses values input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed
  cases rightParsed
  rfl

/-- Empty scrutinee rejection excludes nonempty conversion. -/
theorem RequireScrutineesRejects.disjointOrdinary
    {values : DelimitedList Syntax.Expr} {input rejected : Remainder}
    (rejection : RequireScrutineesRejects values input rejected) :
    ¬ ∃ scrutinees output,
      RequireScrutineesOrdinaryParses values input scrutinees output := by
  rintro ⟨scrutinees, output, successful⟩
  cases rejection with
  | empty emptyValues =>
      cases successful
      contradiction

/-- Requiring nonempty scrutinees is a deterministic pure outcome. -/
theorem requireScrutineesDeterministicOutcomeSpec
    (values : DelimitedList Syntax.Expr) :
    DeterministicOutcomeSpec
      (RequireScrutineesOrdinaryParses values)
      (RequireScrutineesRejects values) where
  successOutputUnique := RequireScrutineesOrdinaryParses.output_unique
  successRejectDisjoint := RequireScrutineesRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchScrutineeListOutcomeProperties
/-!
Diagnostic-inclusive deterministic outcomes for the parenthesized,
nonempty, trailing-comma Core match scrutinee list.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary success of the exact Core match scrutinee list parser. -/
abbrev MatchScrutineeListOrdinaryParses
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop) :=
  NonemptyTrailingDelimitedListParses .leftParen .rightParen
    expressionOrdinary

/-- Exact rejection of the required, allow-trailing scrutinee list. -/
abbrev MatchScrutineeListRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :=
  DelimitedListRejects .leftParen .rightParen false true
    expressionOrdinary expressionRejects

/-- Ordinary Core match scrutinee-list success has one final remainder. -/
theorem MatchScrutineeListOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : DelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      left afterLeft)
    (rightParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      right afterRight) : afterLeft = afterRight :=
  NonemptyTrailingDelimitedListParses.output_unique
    (opening := .leftParen) (closing := .rightParen)
    (elementParses := expressionOrdinary)
    expressionOutcomes.successOutputUnique leftParsed rightParsed

/-- Exact scrutinee-list rejection excludes ordinary success. -/
theorem MatchScrutineeListRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : MatchScrutineeListRejects expressionOrdinary
      expressionRejects input rejected) :
    ¬ ∃ values output,
      MatchScrutineeListOrdinaryParses expressionOrdinary input values
        output :=
  rejection.disjointNonemptyTrailing expressionOutcomes
    (fun parsed => parsed)

/-- Lift expression outcomes through the Core match scrutinee list. -/
theorem matchScrutineeListDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (MatchScrutineeListOrdinaryParses expressionOrdinary)
      (MatchScrutineeListRejects expressionOrdinary expressionRejects) where
  successOutputUnique := MatchScrutineeListOrdinaryParses.output_unique
    expressionOutcomes
  successRejectDisjoint := MatchScrutineeListRejects.disjointOrdinary
    expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
end
