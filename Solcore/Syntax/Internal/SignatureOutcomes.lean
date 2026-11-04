import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Internal.ParameterOutcomes
import Solcore.Syntax.Internal.TypeOutcomes
import Solcore.Syntax.Grammar.Signatures
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Grammar.YulFuel
import Solcore.Syntax.Internal.YulStatementOutcomes

/-!
Properties of the declarative grammar of function signatures, generic parameters and
modifiers: outcomes are deterministic, and successful values and rejection points are
unique. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeGenericParametersExactnessProperties
/-! Full value and rejection-endpoint functionality for generic parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem generic_absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem genericParameterListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (NonemptyTrailingDelimitedListParses .less .greater IdentifierParses)
      (DelimitedListRejects .less .greater false true IdentifierParses
        IdentifierRejects) :=
  nonemptyTrailingDelimitedListExactOutcomeSpec .less .greater
    identifierExactOutcomeSpec

/-- A required generic-parameter list fixes its nonempty AST value. -/
theorem GenericParametersParses.value_unique
    {input : Remainder} {left right : Syntax.GenericParameters}
    {afterLeft afterRight : Remainder}
    (leftParsed : GenericParametersParses input left afterLeft)
    (rightParsed : GenericParametersParses input right afterRight) :
    left = right := by
  have encodedEq := genericParameterListExactOutcomeSpec.successValueUnique
    leftParsed rightParsed
  cases left with
  | mk leftSpan leftElements =>
      cases leftElements with
      | mk leftHead leftTail =>
          cases right with
          | mk rightSpan rightElements =>
              cases rightElements with
              | mk rightHead rightTail =>
                  simp [Syntax.NonemptyList.toList] at encodedEq
                  simp_all

/-- A required generic-parameter list fixes its value and final remainder. -/
theorem GenericParametersParses.result_unique
    {input : Remainder} {left right : Syntax.GenericParameters}
    {afterLeft afterRight : Remainder}
    (leftParsed : GenericParametersParses input left afterLeft)
    (rightParsed : GenericParametersParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A required generic-parameter rejection has one failing endpoint. -/
theorem GenericParametersRejects.output_unique
    {input left right : Remainder}
    (leftRejected : GenericParametersRejects input left)
    (rightRejected : GenericParametersRejects input right) : left = right :=
  genericParameterListExactOutcomeSpec.rejectOutputUnique leftRejected
    rightRejected

/-- Required generic parameters have fully exact ordinary outcomes. -/
theorem genericParametersExactOutcomeSpec :
    ExactDeterministicOutcomeSpec GenericParametersParses
      GenericParametersRejects where
  toDeterministicOutcomeSpec := genericParametersDeterministicOutcomeSpec
  successValueUnique := GenericParametersParses.value_unique
  rejectOutputUnique := GenericParametersRejects.output_unique

private theorem genericParameters_opening_present
    {input output : Remainder} {parameters : Syntax.GenericParameters}
    (parsed : GenericParametersParses input parameters output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .less } := by
  unfold GenericParametersParses at parsed
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact ⟨openingSpan, openingToken⟩

/-- Optional generic parameters fix their absent or present AST value. -/
theorem OptionalGenericParametersParses.value_unique
    {input : Remainder} {left right : Option Syntax.GenericParameters}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalGenericParametersParses input left afterLeft)
    (rightParsed : OptionalGenericParametersParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightParameters =>
          rcases genericParameters_opening_present rightParameters with
            ⟨span, openingToken⟩
          exact False.elim
            (generic_absent_conflicts_token leftAbsent openingToken)
  | present leftParameters =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases genericParameters_opening_present leftParameters with
            ⟨span, openingToken⟩
          exact False.elim
            (generic_absent_conflicts_token rightAbsent openingToken)
      | present rightParameters =>
          rw [leftParameters.value_unique rightParameters]

/-- Optional generic parameters fix their value and final remainder. -/
theorem OptionalGenericParametersParses.result_unique
    {input : Remainder} {left right : Option Syntax.GenericParameters}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalGenericParametersParses input left afterLeft)
    (rightParsed : OptionalGenericParametersParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A committed optional-generic rejection has one failing endpoint. -/
theorem OptionalGenericParametersRejects.output_unique
    {input left right : Remainder}
    (leftRejected : OptionalGenericParametersRejects input left)
    (rightRejected : OptionalGenericParametersRejects input right) :
    left = right := by
  cases leftRejected with
  | present _ leftParameters =>
      cases rightRejected with
      | present _ rightParameters =>
          exact leftParameters.output_unique rightParameters

/-- Optional generic parameters have fully exact ordinary outcomes. -/
theorem optionalGenericParametersExactOutcomeSpec :
    ExactDeterministicOutcomeSpec OptionalGenericParametersParses
      OptionalGenericParametersRejects where
  toDeterministicOutcomeSpec :=
    optionalGenericParametersDeterministicOutcomeSpec
  successValueUnique := OptionalGenericParametersParses.value_unique
  rejectOutputUnique := OptionalGenericParametersRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeReturnClauseOutcomeProperties
/-! Deterministic exact outcomes for optional canonical `returns` clauses. -/

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

private theorem returnTypeListDeterministicOutcomeSpec :
    DeterministicOutcomeSpec
      (TrailingDelimitedListParses .leftParen .rightParen
        TypeExprOrdinaryParses)
      (DelimitedListRejects .leftParen .rightParen true true
        TypeExprOrdinaryParses TypeExprRejects) :=
  trailingDelimitedListDeterministicOutcomeSpec .leftParen .rightParen
    typeExprDeterministicOutcomeSpec

/-- Optional `returns` success has one final remainder. -/
theorem OptionalReturnClauseParses.output_unique
    {input : Remainder} {left right : Option Syntax.ReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalReturnClauseParses input left afterLeft)
    (rightParsed : OptionalReturnClauseParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightMarkerSpan rightMarker rightTypes =>
          exact False.elim (absent_conflicts_exact leftAbsent rightMarker)
  | present leftMarkerSpan leftMarker leftTypes =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftMarker)
      | present rightMarkerSpan rightMarker rightTypes =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          exact returnTypeListDeterministicOutcomeSpec.successOutputUnique
            leftTypes rightTypes

/-- Exact optional-`returns` rejection excludes every successful branch. -/
theorem OptionalReturnClauseRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalReturnClauseRejects input rejected) :
    ¬ ∃ clause output, OptionalReturnClauseParses input clause output := by
  rintro ⟨clause, output, successful⟩
  cases rejection with
  | typesRejected rejectedMarkerSpan rejectedMarker typesRejected =>
      cases successful with
      | absent markerAbsent =>
          exact absent_conflicts_exact markerAbsent rejectedMarker
      | present successfulMarkerSpan successfulMarker typesParsed =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact returnTypeListDeterministicOutcomeSpec.successRejectDisjoint
            typesRejected ⟨_, _, typesParsed⟩

/-- Optional canonical `returns` has deterministic and exclusive outcomes. -/
theorem optionalReturnClauseDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalReturnClauseParses
      OptionalReturnClauseRejects where
  successOutputUnique := OptionalReturnClauseParses.output_unique
  successRejectDisjoint := OptionalReturnClauseRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionParametersOutcomeProperties
/-! Deterministic exact outcomes for recovery-aware function parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A successful function-parameter list has one final remainder. -/
theorem FunctionParametersOrdinaryParses.output_unique
    {input : Remainder}
    {left right : DelimitedList Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParametersOrdinaryParses input left afterLeft)
    (rightParsed : FunctionParametersOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  unfold FunctionParametersOrdinaryParses at leftParsed rightParsed
  exact TrailingDelimitedListParses.output_unique
    (opening := .leftParen) (closing := .rightParen)
    (elementParses := FunctionParameterOrdinaryParses
      TypeExprOrdinaryParses TypeExprRejects)
    (FunctionParameterOrdinaryParses.output_unique
      typeExprDeterministicOutcomeSpec) leftParsed rightParsed

/-- Exact list rejection excludes every ordinary list success. -/
theorem FunctionParametersRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : FunctionParametersRejects input rejected) :
    ¬ ∃ parameters output,
      FunctionParametersOrdinaryParses input parameters output := by
  unfold FunctionParametersOrdinaryParses
  exact rejection.disjointAllowEmptyTrailing
    (functionParameterDeterministicOutcomeSpec
      typeExprDeterministicOutcomeSpec) (fun parsed => parsed)

/-- Recovery-aware function-parameter lists have deterministic and exclusive
ordinary outcomes. -/
theorem functionParametersDeterministicOutcomeSpec :
    DeterministicOutcomeSpec FunctionParametersOrdinaryParses
      FunctionParametersRejects where
  successOutputUnique := FunctionParametersOrdinaryParses.output_unique
  successRejectDisjoint := FunctionParametersRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionSignatureOutcomeProperties
/-!
Functionality and rejection exclusivity for ordinary named-function signature
outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One prioritized optional modifier has one final remainder. -/
theorem OptionalFunctionModifierParses.output_unique
    {keyword : HardKeyword} {input : Remainder}
    {left right : Option SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : OptionalFunctionModifierParses keyword input left afterLeft)
    (rightParsed : OptionalFunctionModifierParses keyword input right
      afterRight) : afterLeft = afterRight := by
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
      | present rightSpan rightToken =>
          exact exactToken_output_unique leftToken rightToken

/-- Fixed-order optional function modifiers have one final remainder. -/
theorem FunctionModifiersParses.output_unique
    {input : Remainder} {left right : Syntax.FunctionModifiers}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionModifiersParses input left afterLeft)
    (rightParsed : FunctionModifiersParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftAfterPublic, leftPublic, leftPayable⟩
  rcases rightParsed with
    ⟨rightAfterPublic, rightPublic, rightPayable⟩
  have afterPublicEq := leftPublic.output_unique rightPublic
  subst afterPublicEq
  exact leftPayable.output_unique rightPayable

/-- Ordinary function-signature success has one final remainder. -/
theorem FunctionSignatureOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.FunctionSignature}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionSignatureOrdinaryParses input left afterLeft)
    (rightParsed : FunctionSignatureOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftKeywordSpan leftKeyword leftName leftGenerics leftParameters
        leftModifiers leftReturns leftWhere =>
      cases rightParsed with
      | parsed rightKeywordSpan rightKeyword rightName rightGenerics
            rightParameters rightModifiers rightReturns rightWhere =>
          have afterKeywordEq := exactToken_output_unique leftKeyword
            rightKeyword
          subst afterKeywordEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          have afterGenericsEq := leftGenerics.output_unique rightGenerics
          subst afterGenericsEq
          have afterParametersEq := leftParameters.output_unique
            rightParameters
          subst afterParametersEq
          have afterModifiersEq := leftModifiers.output_unique rightModifiers
          subst afterModifiersEq
          have afterReturnsEq := leftReturns.output_unique rightReturns
          subst afterReturnsEq
          exact leftWhere.output_unique rightWhere

/-- Exact first-stage signature rejection excludes every ordinary success. -/
theorem FunctionSignatureRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : FunctionSignatureRejects input rejected) :
    ¬ ∃ signature output,
      FunctionSignatureOrdinaryParses input signature output := by
  rintro ⟨signature, output, successful⟩
  cases successful with
  | parsed successfulKeywordSpan successfulKeyword successfulName
        successfulGenerics successfulParameters successfulModifiers
        successfulReturns successfulWhere =>
      cases rejection with
      | keywordMissing keywordAbsent =>
          exact absent_conflicts_exact keywordAbsent successfulKeyword
      | nameRejected rejectedKeywordSpan rejectedKeyword nameRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | genericsRejected rejectedKeywordSpan rejectedKeyword rejectedName
            genericsRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          exact optionalGenericParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint genericsRejected
              ⟨_, _, successfulGenerics⟩
      | parametersRejected rejectedKeywordSpan rejectedKeyword rejectedName
            rejectedGenerics parametersRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          exact functionParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint parametersRejected
              ⟨_, _, successfulParameters⟩
      | returnsRejected rejectedKeywordSpan rejectedKeyword rejectedName
            rejectedGenerics rejectedParameters rejectedModifiers
            returnsRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterModifiersEq := rejectedModifiers.output_unique
            successfulModifiers
          subst afterModifiersEq
          exact optionalReturnClauseDeterministicOutcomeSpec
            |>.successRejectDisjoint returnsRejected
              ⟨_, _, successfulReturns⟩
      | whereRejected rejectedKeywordSpan rejectedKeyword rejectedName
            rejectedGenerics rejectedParameters rejectedModifiers
            rejectedReturns whereRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterModifiersEq := rejectedModifiers.output_unique
            successfulModifiers
          subst afterModifiersEq
          have afterReturnsEq := rejectedReturns.output_unique
            successfulReturns
          subst afterReturnsEq
          exact optionalWhereClauseDeterministicOutcomeSpec
            |>.successRejectDisjoint whereRejected ⟨_, _, successfulWhere⟩

/-- Complete named-function signatures have deterministic and exclusive
ordinary outcomes. -/
theorem functionSignatureDeterministicOutcomeSpec :
    DeterministicOutcomeSpec FunctionSignatureOrdinaryParses
      FunctionSignatureRejects where
  successOutputUnique := FunctionSignatureOrdinaryParses.output_unique
  successRejectDisjoint := FunctionSignatureRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionModifierExactnessProperties
/-! Shared exact values for optional hard-keyword function modifiers. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem modifier_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- One optional function modifier fixes its absent or present span. -/
theorem OptionalFunctionModifierParses.value_unique
    {keyword : HardKeyword} {input : Remainder}
    {left right : Option SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : OptionalFunctionModifierParses keyword input left afterLeft)
    (rightParsed : OptionalFunctionModifierParses keyword input right
      afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightToken =>
          exact False.elim
            (modifier_absent_conflicts_exact leftAbsent rightToken)
  | present leftSpan leftToken =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (modifier_absent_conflicts_exact rightAbsent leftToken)
      | present rightSpan rightToken =>
          rw [leftToken.span_unique rightToken]

/-- One optional function modifier fixes its value and final remainder. -/
theorem OptionalFunctionModifierParses.result_unique
    {keyword : HardKeyword} {input : Remainder}
    {left right : Option SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : OptionalFunctionModifierParses keyword input left afterLeft)
    (rightParsed : OptionalFunctionModifierParses keyword input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementExactnessProperties
/-! Exact recursive fixed-fuel and public inline-Yul statement outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every recursive statement fuel fixes successful ASTs and rejecting endpoints. -/
theorem yulStatementExactOutcomeSpecWithFuel (fuel : Nat) :
    ExactDeterministicOutcomeSpec (YulStatementOrdinaryParsesWithFuel fuel)
      (YulStatementRejectsWithFuel fuel) := by
  induction fuel with
  | zero =>
      exact {
        toDeterministicOutcomeSpec := yulStatementOutcomeSpecWithFuel 0
        successValueUnique := by
          intro input left right afterLeft afterRight leftParsed
          exact False.elim (YulStatementOrdinaryParsesWithFuel.zero leftParsed)
        rejectOutputUnique := by
          intro input left right leftRejected
          exact False.elim (YulStatementRejectsWithFuel.zero leftRejected)
      }
  | succ fuel ih =>
      exact yulStatementLayerExactOutcomeSpec
        (yulStatementTerminatedExactOutcomeSpec (yulStatementCoreExactOutcomeSpec ih))
        (YulStatementRejects.disjointTerminatedOrdinary
          (YulStatementRejects.disjointCoreOrdinary ih.toDeterministicOutcomeSpec))

/-- Fixed-fuel ordinary statements fix their complete AST and remainder. -/
theorem YulStatementOrdinaryParsesWithFuel.result_unique {fuel : Nat}
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementOrdinaryParsesWithFuel fuel input left afterLeft)
    (rightParsed : YulStatementOrdinaryParsesWithFuel fuel input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  (yulStatementExactOutcomeSpecWithFuel fuel).successResultUnique leftParsed rightParsed

/-- Fixed-fuel ordinary statement rejection fixes the complete endpoint. -/
theorem YulStatementRejectsWithFuel.output_unique {fuel : Nat}
    {input left right : Remainder}
    (leftRejected : YulStatementRejectsWithFuel fuel input left)
    (rightRejected : YulStatementRejectsWithFuel fuel input right) : left = right :=
  (yulStatementExactOutcomeSpecWithFuel fuel).rejectOutputUnique leftRejected rightRejected

/-- Input-selected public fuel preserves fully exact ordinary statement outcomes. -/
theorem yulStatementPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulStatementOrdinaryParses
      YulStatementPublicRejects where
  toDeterministicOutcomeSpec := yulStatementPublicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (yulStatementExactOutcomeSpecWithFuel (yulStatementPublicFuel input)).successValueUnique
      leftParsed rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact (yulStatementExactOutcomeSpecWithFuel (yulStatementPublicFuel input)).rejectOutputUnique
      leftRejected rightRejected

/-- Exact public statement outcomes with the concrete recovery-boundary rejection. -/
theorem yulStatementExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulStatementOrdinaryParses YulStatementRejects where
  toDeterministicOutcomeSpec := yulStatementPublicDeterministicOutcomeSpec
  successValueUnique := yulStatementPublicExactOutcomeSpec.successValueUnique
  rejectOutputUnique := YulStatementRejects.output_unique

/-- Public ordinary statements fix their complete AST and final remainder. -/
theorem YulStatementOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementOrdinaryParses input left afterLeft)
    (rightParsed : YulStatementOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  yulStatementExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Public fuel-indexed statement rejection fixes its complete endpoint. -/
theorem YulStatementPublicRejects.output_unique {input left right : Remainder}
    (leftRejected : YulStatementPublicRejects input left)
    (rightRejected : YulStatementPublicRejects input right) : left = right :=
  yulStatementPublicExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulBodyExactnessProperties
/-! Fully exact public inline-Yul body ASTs, source spans, and endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Public Yul bodies have exact successful block values and rejecting endpoints. -/
theorem yulBodyExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulBodyOutcomeParses YulBodyRejects :=
  yulBlockExactOutcomeSpec yulStatementExactOutcomeSpec

/-- Public Yul bodies fix their span, source-order statements, and complete remainder. -/
theorem YulBodyOrdinaryParses.result_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftBody rightBody : List Syntax.YulStmt} {afterLeft afterRight : Remainder}
    (leftParsed : YulBodyOrdinaryParses input leftSpan leftBody afterLeft)
    (rightParsed : YulBodyOrdinaryParses input rightSpan rightBody afterRight) :
    leftSpan = rightSpan ∧ leftBody = rightBody ∧ afterLeft = afterRight :=
  YulBlockParses.result_unique yulStatementExactOutcomeSpec leftParsed rightParsed

/-- Public Yul body rejection fixes the complete first-failure endpoint. -/
theorem YulBodyRejects.output_unique {input left right : Remainder}
    (leftRejected : YulBodyRejects input left)
    (rightRejected : YulBodyRejects input right) : left = right :=
  yulBodyExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

end Solcore.Syntax.DeclarativeGrammar
end
