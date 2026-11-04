import Solcore.Syntax.Grammar.Declarations
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Internal.TypeOutcomes
import Solcore.Syntax.Internal.SignatureOutcomes
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Internal.DelimitedExactness

/-!
Properties of the declarative grammar of derive attributes, type aliases and contract
entries: outcomes are deterministic, and successful values and rejection points are
unique. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractFieldOutcomeProperties
/-! Deterministic exact ordinary outcomes for contract storage fields. -/

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

/-- Optional field initializers have one final remainder. -/
theorem OptionalContractFieldInitializerOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input left afterLeft)
    (rightParsed : OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightEqual rightExpression =>
          exact False.elim (absent_conflicts_exact leftAbsent rightEqual)
  | present leftSpan leftEqual leftExpression =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftEqual)
      | present rightSpan rightEqual rightExpression =>
          have afterEqualEq := exactToken_output_unique leftEqual rightEqual
          subst afterEqualEq
          exact expressionOutcomes.successOutputUnique leftExpression
            rightExpression

/-- Optional field-initializer rejection excludes ordinary success. -/
theorem OptionalContractFieldInitializerRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : OptionalContractFieldInitializerRejects expressionRejects
      input rejected) :
    ¬ ∃ initializer output,
      OptionalContractFieldInitializerOrdinaryParses expressionOrdinary input
        initializer output := by
  rintro ⟨initializer, output, successful⟩
  cases rejection with
  | expressionRejected rejectedSpan rejectedEqual rejectedExpression =>
      cases successful with
      | absent equalAbsent =>
          exact absent_conflicts_exact equalAbsent rejectedEqual
      | present successfulSpan successfulEqual successfulExpression =>
          have afterEqualEq := exactToken_output_unique rejectedEqual
            successfulEqual
          subst afterEqualEq
          exact expressionOutcomes.successRejectDisjoint rejectedExpression
            ⟨_, _, successfulExpression⟩

/-- Optional contract-field initializers have deterministic ordinary outcomes. -/
theorem optionalContractFieldInitializerDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (OptionalContractFieldInitializerOrdinaryParses expressionOrdinary)
      (OptionalContractFieldInitializerRejects expressionRejects) where
  successOutputUnique :=
    OptionalContractFieldInitializerOrdinaryParses.output_unique
      expressionOutcomes
  successRejectDisjoint :=
    OptionalContractFieldInitializerRejects.disjointOrdinary
      expressionOutcomes

/-- Ordinary contract-field success has one final remainder. -/
theorem ContractFieldOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ContractField}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractFieldOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ContractFieldOrdinaryParses expressionOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftColonSpan leftSemicolonSpan leftName leftColon leftType
        leftInitializer leftSemicolon =>
      cases rightParsed with
      | parsed rightColonSpan rightSemicolonSpan rightName rightColon rightType
            rightInitializer rightSemicolon =>
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          have afterColonEq := exactToken_output_unique leftColon rightColon
          subst afterColonEq
          have afterTypeEq := typeExprDeterministicOutcomeSpec
            |>.successOutputUnique leftType rightType
          subst afterTypeEq
          have afterInitializerEq :=
            OptionalContractFieldInitializerOrdinaryParses.output_unique
              expressionOutcomes leftInitializer rightInitializer
          subst afterInitializerEq
          exact exactToken_output_unique leftSemicolon rightSemicolon

/-- Exact contract-field rejection excludes every ordinary success. -/
theorem ContractFieldRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : ContractFieldRejects expressionOrdinary expressionRejects
      input rejected) :
    ¬ ∃ field output,
      ContractFieldOrdinaryParses expressionOrdinary input field output := by
  rintro ⟨field, output, successful⟩
  cases successful with
  | parsed successfulColonSpan successfulSemicolonSpan successfulName
        successfulColon successfulType successfulInitializer
        successfulSemicolon =>
      cases rejection with
      | nameRejected nameRejected =>
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | colonMissing rejectedName colonAbsent =>
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact absent_conflicts_exact colonAbsent successfulColon
      | typeRejected rejectedColonSpan rejectedName rejectedColon
            typeRejected =>
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterColonEq := exactToken_output_unique rejectedColon
            successfulColon
          subst afterColonEq
          exact typeExprDeterministicOutcomeSpec.successRejectDisjoint
            typeRejected ⟨_, _, successfulType⟩
      | initializerRejected rejectedColonSpan rejectedName rejectedColon
            rejectedType initializerRejected =>
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterColonEq := exactToken_output_unique rejectedColon
            successfulColon
          subst afterColonEq
          have afterTypeEq := typeExprDeterministicOutcomeSpec
            |>.successOutputUnique rejectedType successfulType
          subst afterTypeEq
          exact (optionalContractFieldInitializerDeterministicOutcomeSpec
            expressionOutcomes).successRejectDisjoint initializerRejected
              ⟨_, _, successfulInitializer⟩
      | semicolonMissing rejectedColonSpan rejectedName rejectedColon
            rejectedType rejectedInitializer semicolonAbsent =>
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterColonEq := exactToken_output_unique rejectedColon
            successfulColon
          subst afterColonEq
          have afterTypeEq := typeExprDeterministicOutcomeSpec
            |>.successOutputUnique rejectedType successfulType
          subst afterTypeEq
          have afterInitializerEq :=
            OptionalContractFieldInitializerOrdinaryParses.output_unique
              expressionOutcomes rejectedInitializer successfulInitializer
          subst afterInitializerEq
          exact absent_conflicts_exact semicolonAbsent successfulSemicolon

/-- Contract storage fields have deterministic and exclusive ordinary
outcomes. -/
theorem contractFieldDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (ContractFieldOrdinaryParses expressionOrdinary)
      (ContractFieldRejects expressionOrdinary expressionRejects) where
  successOutputUnique := ContractFieldOrdinaryParses.output_unique
    expressionOutcomes
  successRejectDisjoint := ContractFieldRejects.disjointOrdinary
    expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeProperties
/-! Deterministic exact ordinary outcomes for canonical constructors. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Fixed-order ordinary entry modifiers have one final remainder. -/
theorem ContractEntryModifiersOrdinaryParses.output_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractEntryModifiersOrdinaryParses input left afterLeft)
    (rightParsed : ContractEntryModifiersOrdinaryParses input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftPublic leftPayable =>
      cases rightParsed with
      | parsed rightPublic rightPayable =>
          have afterPublicEq := leftPublic.output_unique rightPublic
          subst afterPublicEq
          exact leftPayable.output_unique rightPayable

/-- Ordinary constructor success has one final remainder. -/
theorem ConstructorDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ConstructorDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorDeclOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftParameters leftModifiers leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightParameters rightModifiers
            rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterParametersEq := leftParameters.output_unique
            rightParameters
          subst afterParametersEq
          have afterModifiersEq := leftModifiers.output_unique rightModifiers
          subst afterModifiersEq
          exact (isolatedCoreBlockPublicOutcomeSpec .require)
            |>.successOutputUnique leftBody rightBody

/-- Exact constructor rejection excludes every ordinary constructor success. -/
theorem ConstructorDeclRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ConstructorDeclRejects input rejected) :
    ¬ ∃ declaration output,
      ConstructorDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulParameters
        successfulModifiers successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | parametersRejected rejectedMarkerSpan rejectedMarker
            parametersRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact functionParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint parametersRejected
              ⟨_, _, successfulParameters⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedParameters
            rejectedModifiers bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterModifiersEq := rejectedModifiers.output_unique
            successfulModifiers
          subst afterModifiersEq
          exact (isolatedCoreBlockPublicOutcomeSpec .require)
            |>.successRejectDisjoint bodyRejected ⟨_, _, successfulBody⟩

/-- Canonical constructors have deterministic and exclusive ordinary
outcomes. -/
theorem constructorDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ConstructorDeclOrdinaryParses
      ConstructorDeclRejects where
  successOutputUnique := ConstructorDeclOrdinaryParses.output_unique
  successRejectDisjoint := ConstructorDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFallbackDeclarationOutcomeProperties
/-! Deterministic exact ordinary outcomes for canonical fallback declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Pure fallback-parameter validation has one final remainder. -/
theorem FallbackParameterValidationOrdinaryParses.output_unique
    {parameters : DelimitedList Syntax.FunctionParameter}
    {input afterLeft afterRight : Remainder}
    (leftParsed : FallbackParameterValidationOrdinaryParses parameters input
      afterLeft)
    (rightParsed : FallbackParameterValidationOrdinaryParses parameters input
      afterRight) : afterLeft = afterRight := by
  cases leftParsed <;> cases rightParsed <;> rfl

/-- Pure fallback-parameter validation leaves its input remainder unchanged. -/
theorem FallbackParameterValidationOrdinaryParses.output_eq_input
    {parameters : DelimitedList Syntax.FunctionParameter}
    {input output : Remainder}
    (parsed : FallbackParameterValidationOrdinaryParses parameters input
      output) : output = input := by
  cases parsed <;> rfl

/-- Ordinary fallback success has one final remainder. -/
theorem FallbackDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.FallbackDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FallbackDeclOrdinaryParses input left afterLeft)
    (rightParsed : FallbackDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftParameters leftValidation
        leftModifiers leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightParameters rightValidation
            rightModifiers rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterParametersEq := leftParameters.output_unique
            rightParameters
          subst afterParametersEq
          have afterValidationEq : _ := leftValidation.output_eq_input.trans
            rightValidation.output_eq_input.symm
          subst afterValidationEq
          have afterModifiersEq := leftModifiers.output_unique rightModifiers
          subst afterModifiersEq
          exact (isolatedCoreBlockPublicOutcomeSpec .require)
            |>.successOutputUnique leftBody rightBody

/-- Exact fallback rejection excludes every ordinary fallback success. -/
theorem FallbackDeclRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : FallbackDeclRejects input rejected) :
    ¬ ∃ declaration output,
      FallbackDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulParameters
        successfulValidation successfulModifiers successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | parametersRejected rejectedMarkerSpan rejectedMarker
            parametersRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact functionParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint parametersRejected
              ⟨_, _, successfulParameters⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedParameters
            rejectedValidation rejectedModifiers bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterValidationEq : _ := rejectedValidation.output_eq_input.trans
            successfulValidation.output_eq_input.symm
          subst afterValidationEq
          have afterModifiersEq := rejectedModifiers.output_unique
            successfulModifiers
          subst afterModifiersEq
          exact (isolatedCoreBlockPublicOutcomeSpec .require)
            |>.successRejectDisjoint bodyRejected ⟨_, _, successfulBody⟩

/-- Canonical fallback declarations have deterministic and exclusive ordinary
outcomes. -/
theorem fallbackDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec FallbackDeclOrdinaryParses
      FallbackDeclRejects where
  successOutputUnique := FallbackDeclOrdinaryParses.output_unique
  successRejectDisjoint := FallbackDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractEntryModifierExactnessProperties
/-! Exact values for fixed-order public/payable contract-entry modifiers. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Fixed public-then-payable modifiers have one exact payable marker value. -/
theorem ContractEntryModifiersOrdinaryParses.value_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractEntryModifiersOrdinaryParses input left afterLeft)
    (rightParsed : ContractEntryModifiersOrdinaryParses input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftPublic leftPayable =>
      cases rightParsed with
      | parsed rightPublic rightPayable =>
          have afterPublicEq := leftPublic.output_unique rightPublic
          cases afterPublicEq
          exact leftPayable.value_unique rightPayable

/-- Fixed public-then-payable modifiers fix their value and remainder. -/
theorem ContractEntryModifiersOrdinaryParses.result_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractEntryModifiersOrdinaryParses input left afterLeft)
    (rightParsed : ContractEntryModifiersOrdinaryParses input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractMemberRecoveryOutcomeProperties
/-! Functionality and outcome exclusion for contract-member recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- A contract-member recovery scan has one final remainder. -/
theorem ContractMemberRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.ContractMember} {afterLeft afterRight : Remainder},
      ContractMemberRecoveryScanParses first leftLast input left afterLeft →
      ContractMemberRecoveryScanParses first rightLast input right afterRight →
      afterLeft = afterRight := by
  intro first leftLast rightLast input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing rightLast right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- Complete ordinary contract-member recovery has one final remainder. -/
theorem ContractMemberRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberRecoveryParses input left afterLeft)
    (rightParsed : ContractMemberRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Every contract-member recovery rejection is non-consuming. -/
theorem ContractMemberRecoveryRejects.output_eq
    {input rejected : Remainder}
    (rejection : ContractMemberRecoveryRejects input rejected) :
    rejected = input := by
  cases rejection <;> rfl

/-- An unavailable mandatory first token excludes every recovery success. -/
theorem ContractMemberRecoveryRejects.disjointParses
    {input rejected : Remainder}
    (rejection : ContractMemberRecoveryRejects input rejected) :
    ¬ ∃ member output, ContractMemberRecoveryParses input member output := by
  rintro ⟨member, output, parsed⟩
  cases parsed with
  | recovered current scan =>
      cases rejection with
      | windowEnd atEnd =>
          exact Nat.not_lt_of_ge atEnd current.1
      | missingToken inside missing =>
          rw [current.2] at missing
          contradiction

/-- Deterministic ordinary outcome contract for contract-member recovery. -/
theorem contractMemberRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ContractMemberRecoveryParses
      ContractMemberRecoveryRejects where
  successOutputUnique := ContractMemberRecoveryParses.output_unique
  successRejectDisjoint := ContractMemberRecoveryRejects.disjointParses

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractMemberRecoveryExactnessProperties
/-! Full functionality of contract-member recovery outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A recovery scan with fixed first and last retained spans has one exact
error-member AST. -/
theorem ContractMemberRecoveryScanParses.value_unique :
    ∀ {first last : SourceSpan} {input : Remainder}
      {left right : Syntax.ContractMember}
      {afterLeft afterRight : Remainder},
      ContractMemberRecoveryScanParses first last input left afterLeft →
      ContractMemberRecoveryScanParses first last input right afterRight →
      left = right := by
  intro first last input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops =>
          exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- A recovery scan with fixed retained spans determines its AST and final
remainder. -/
theorem ContractMemberRecoveryScanParses.result_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberRecoveryScanParses first last input left
      afterLeft)
    (rightParsed : ContractMemberRecoveryScanParses first last input right
      afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Complete contract-member recovery has one exact error-member AST. -/
theorem ContractMemberRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberRecoveryParses input left afterLeft)
    (rightParsed : ContractMemberRecoveryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact leftScan.value_unique rightScan

/-- Complete contract-member recovery fixes its AST and final remainder. -/
theorem ContractMemberRecoveryParses.result_unique
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberRecoveryParses input left afterLeft)
    (rightParsed : ContractMemberRecoveryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- An unavailable mandatory token fixes the exact nonconsuming endpoint. -/
theorem ContractMemberRecoveryRejects.output_unique
    {input left right : Remainder}
    (leftRejects : ContractMemberRecoveryRejects input left)
    (rightRejects : ContractMemberRecoveryRejects input right) :
    left = right :=
  leftRejects.output_eq.trans rightRejects.output_eq.symm

/-- Contract-member recovery has fully functional success and rejection
outcomes. -/
theorem contractMemberRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ContractMemberRecoveryParses
      ContractMemberRecoveryRejects where
  toDeterministicOutcomeSpec := contractMemberRecoveryDeterministicOutcomeSpec
  successValueUnique := ContractMemberRecoveryParses.value_unique
  rejectOutputUnique := ContractMemberRecoveryRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDeriveAttributeRecoveryOutcomeProperties
/-! Deterministic ordinary outcomes for derive-attribute recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- The priority-ordered recovery tail has one final remainder. -/
theorem DeriveAttributeRecoveryTailParses.output_unique :
    ∀ {hash leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.DeriveAttribute}
      {afterLeft afterRight : Remainder},
      DeriveAttributeRecoveryTailParses hash leftLast input left afterLeft →
      DeriveAttributeRecoveryTailParses hash rightLast input right afterRight →
      afterLeft = afterRight := by
  intro hash leftLast rightLast input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing rightLast right afterRight with
  | malformed leftClosingSpan leftClosing =>
      intro rightParsed
      cases rightParsed with
      | malformed rightClosingSpan rightClosing =>
          rw [leftClosing.2, rightClosing.2]
      | unclosed rightClosingAbsent rightStops =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosing.1)
      | next rightClosingAbsent rightContinues rightCurrent rightTail =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosing.1)
  | unclosed leftClosingAbsent leftStops =>
      intro rightParsed
      cases rightParsed with
      | malformed rightClosingSpan rightClosing =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosing.1)
      | unclosed => rfl
      | next rightClosingAbsent rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftClosingAbsent leftContinues leftCurrent leftTail
      inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | malformed rightClosingSpan rightClosing =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosing.1)
      | unclosed rightClosingAbsent rightStops =>
          exact False.elim (leftContinues rightStops)
      | next rightClosingAbsent rightContinues rightCurrent rightTail =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- The complete recovered path has one final remainder. -/
theorem DeriveAttributeRecoveredParses.output_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeRecoveredParses input left afterLeft)
    (rightParsed : DeriveAttributeRecoveredParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftHashSpan leftOpeningSpan leftHash leftOpening leftTail =>
      cases rightParsed with
      | recovered rightHashSpan rightOpeningSpan rightHash rightOpening
          rightTail =>
          have hashTokenEq := tokenAt_unique leftHash.1 rightHash.1
          have hashSpanEq : leftHashSpan = rightHashSpan :=
            congrArg (fun token : Token => token.span) hashTokenEq
          have afterHashEq := leftHash.2.trans rightHash.2.symm
          subst rightHashSpan
          subst afterHashEq
          have openingTokenEq := tokenAt_unique leftOpening.1 rightOpening.1
          have openingSpanEq : leftOpeningSpan = rightOpeningSpan :=
            congrArg (fun token : Token => token.span) openingTokenEq
          have afterOpeningEq := leftOpening.2.trans rightOpening.2.symm
          subst rightOpeningSpan
          subst afterOpeningEq
          exact leftTail.output_unique rightTail

/-- A recovered-prefix rejection excludes every recovered success. -/
theorem DeriveAttributeRecoveredRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : DeriveAttributeRecoveredRejects input rejected) :
    ¬ ∃ value output, DeriveAttributeRecoveredParses input value output := by
  rintro ⟨value, output, successful⟩
  cases successful with
  | recovered successfulHashSpan successfulOpeningSpan successfulHash
      successfulOpening successfulTail =>
      cases rejection with
      | hashMissing hashAbsent =>
          exact absent_conflicts_token hashAbsent successfulHash.1
      | openingMissing rejectedHashSpan rejectedHash openingAbsent =>
          have afterHashEq := rejectedHash.2.trans successfulHash.2.symm
          subst afterHashEq
          exact absent_conflicts_token openingAbsent successfulOpening.1

/-- Recovered derive attributes form a deterministic ordinary outcome. -/
theorem deriveAttributeRecoveredDeterministicOutcomeSpec :
    DeterministicOutcomeSpec DeriveAttributeRecoveredParses
      DeriveAttributeRecoveredRejects where
  successOutputUnique := DeriveAttributeRecoveredParses.output_unique
  successRejectDisjoint := DeriveAttributeRecoveredRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDeriveAttributeRecoveryExactnessProperties
/-! Full functionality of recovered derive-attribute outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- For one fixed last retained span, the priority-ordered recovery tail has
one exact recovered AST value. -/
theorem DeriveAttributeRecoveryTailParses.value_unique :
    ∀ {hash last : SourceSpan} {input : Remainder}
      {left right : Syntax.DeriveAttribute}
      {afterLeft afterRight : Remainder},
      DeriveAttributeRecoveryTailParses hash last input left afterLeft →
      DeriveAttributeRecoveryTailParses hash last input right afterRight →
      left = right := by
  intro hash last input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing right afterRight with
  | malformed leftClosingSpan leftClosing =>
      intro rightParsed
      cases rightParsed with
      | malformed rightClosingSpan rightClosing =>
          have closingSpanEq := leftClosing.span_unique rightClosing
          cases closingSpanEq
          rfl
      | unclosed rightClosingAbsent rightStops =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosing.1)
      | next rightClosingAbsent rightContinues rightCurrent rightTail =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosing.1)
  | unclosed leftClosingAbsent leftStops =>
      intro rightParsed
      cases rightParsed with
      | malformed rightClosingSpan rightClosing =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosing.1)
      | unclosed => rfl
      | next rightClosingAbsent rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftClosingAbsent leftContinues leftCurrent leftTail
      inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | malformed rightClosingSpan rightClosing =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosing.1)
      | unclosed rightClosingAbsent rightStops =>
          exact False.elim (leftContinues rightStops)
      | next rightClosingAbsent rightContinues rightCurrent rightTail =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- A recovery tail with one fixed retained span fixes its AST and final
remainder. -/
theorem DeriveAttributeRecoveryTailParses.result_unique
    {hash last : SourceSpan} {input : Remainder}
    {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeRecoveryTailParses hash last input left
      afterLeft)
    (rightParsed : DeriveAttributeRecoveryTailParses hash last input right
      afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The complete recovered path has one exact AST value. -/
theorem DeriveAttributeRecoveredParses.value_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeRecoveredParses input left afterLeft)
    (rightParsed : DeriveAttributeRecoveredParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | recovered leftHashSpan leftOpeningSpan leftHash leftOpening leftTail =>
      cases rightParsed with
      | recovered rightHashSpan rightOpeningSpan rightHash rightOpening
          rightTail =>
          rcases leftHash.result_unique rightHash with
            ⟨hashSpanEq, afterHashEq⟩
          cases hashSpanEq
          cases afterHashEq
          rcases leftOpening.result_unique rightOpening with
            ⟨openingSpanEq, afterOpeningEq⟩
          cases openingSpanEq
          cases afterOpeningEq
          exact leftTail.value_unique rightTail

/-- The complete recovered path fixes its AST and final remainder. -/
theorem DeriveAttributeRecoveredParses.result_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeRecoveredParses input left afterLeft)
    (rightParsed : DeriveAttributeRecoveredParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A recovered-prefix rejection has one exact failing endpoint. -/
theorem DeriveAttributeRecoveredRejects.output_unique
    {input left right : Remainder}
    (leftRejects : DeriveAttributeRecoveredRejects input left)
    (rightRejects : DeriveAttributeRecoveredRejects input right) :
    left = right := by
  cases leftRejects with
  | hashMissing leftHashAbsent =>
      cases rightRejects with
      | hashMissing => rfl
      | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
          exact False.elim
            (absent_conflicts_token leftHashAbsent rightHash.1)
  | openingMissing leftHashSpan leftHash leftOpeningAbsent =>
      cases rightRejects with
      | hashMissing rightHashAbsent =>
          exact False.elim
            (absent_conflicts_token rightHashAbsent leftHash.1)
      | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
          exact leftHash.output_unique rightHash

/-- Recovered derive attributes have fully functional ordinary and rejection
outcomes. -/
theorem deriveAttributeRecoveredExactOutcomeSpec :
    ExactDeterministicOutcomeSpec DeriveAttributeRecoveredParses
      DeriveAttributeRecoveredRejects where
  toDeterministicOutcomeSpec :=
    deriveAttributeRecoveredDeterministicOutcomeSpec
  successValueUnique := DeriveAttributeRecoveredParses.value_unique
  rejectOutputUnique := DeriveAttributeRecoveredRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDeriveTargetOutcomeProperties
/-! Deterministic and exclusive ordinary outcomes for dotted derive targets. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One ordinary or diagnosed derive component has one final remainder. -/
theorem DeriveComponentParses.output_unique
    {input : Remainder} {left right : Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveComponentParses input left afterLeft)
    (rightParsed : DeriveComponentParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | identifier leftIdentifier =>
      cases rightParsed with
      | identifier rightIdentifier =>
          exact IdentifierParses.output_unique leftIdentifier rightIdentifier
      | reserved keyword allowed span token =>
          have impossible := tokenAt_unique leftIdentifier.1 token
          cases impossible
  | reserved keyword allowed span token =>
      cases rightParsed with
      | identifier rightIdentifier =>
          have impossible := tokenAt_unique token rightIdentifier.1
          cases impossible
      | reserved => rfl

/-- Exact derive-component rejection excludes every component success. -/
theorem DeriveComponentRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : DeriveComponentRejects input rejected) :
    ¬ ∃ component output, DeriveComponentParses input component output := by
  rintro ⟨component, output, successful⟩
  cases rejection with
  | unavailable reservedAbsent identifierRejected =>
      cases successful with
      | identifier identifierParsed =>
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            identifierRejected ⟨_, _, identifierParsed⟩
      | reserved keyword allowed span token =>
          exact absent_conflicts_token (reservedAbsent keyword allowed) token

/-- Derive components form a deterministic broad ordinary outcome. -/
theorem deriveComponentDeterministicOutcomeSpec :
    DeterministicOutcomeSpec DeriveComponentParses DeriveComponentRejects where
  successOutputUnique := DeriveComponentParses.output_unique
  successRejectDisjoint := DeriveComponentRejects.disjointOrdinary

/-- A maximal dotted derive-target tail has one final remainder. -/
theorem DeriveTargetTailParses.output_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveTargetTailParses input left afterLeft)
    (rightParsed : DeriveTargetTailParses input right afterRight) :
    afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftDotAbsent =>
      cases rightParsed with
      | done => rfl
      | next rightDotSpan rightDot _ _ =>
          exact False.elim
            (absent_conflicts_token leftDotAbsent rightDot)
  | next leftDotSpan leftDot leftComponent leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightDotAbsent =>
          exact False.elim
            (absent_conflicts_token rightDotAbsent leftDot)
      | next rightDotSpan rightDot rightComponent rightTail =>
          have afterComponentEq :=
            DeriveComponentParses.output_unique leftComponent rightComponent
          subst afterComponentEq
          exact inductionHypothesis rightTail

/-- Exact dotted-tail rejection excludes every maximal tail success. -/
theorem DeriveTargetTailRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : DeriveTargetTailRejects input rejected) :
    ¬ ∃ components output,
      DeriveTargetTailParses input components output := by
  induction rejection with
  | componentRejected dotSpan dotParsed componentRejected =>
      rintro ⟨components, output, successful⟩
      cases successful with
      | done dotAbsent =>
          exact absent_conflicts_token dotAbsent dotParsed.1
      | next successfulDotSpan successfulDot componentParsed tail =>
          have afterDotEq := dotParsed.2
          subst afterDotEq
          exact deriveComponentDeterministicOutcomeSpec.successRejectDisjoint
            componentRejected ⟨_, _, componentParsed⟩
  | laterRejected dotSpan dotParsed rejectedComponent tailRejected
      inductionHypothesis =>
      rintro ⟨components, output, successful⟩
      cases successful with
      | done dotAbsent =>
          exact absent_conflicts_token dotAbsent dotParsed.1
      | next successfulDotSpan successfulDot successfulComponent
          successfulTail =>
          have afterDotEq := dotParsed.2
          subst afterDotEq
          have afterComponentEq := DeriveComponentParses.output_unique
            rejectedComponent successfulComponent
          subst afterComponentEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩

/-- Dotted derive-target tails form a deterministic broad ordinary outcome. -/
theorem deriveTargetTailDeterministicOutcomeSpec :
    DeterministicOutcomeSpec DeriveTargetTailParses
      DeriveTargetTailRejects where
  successOutputUnique := DeriveTargetTailParses.output_unique
  successRejectDisjoint := DeriveTargetTailRejects.disjointOrdinary

/-- A complete dotted derive target has one final remainder. -/
theorem DeriveTargetParses.output_unique
    {input : Remainder} {left right : Syntax.DeriveTarget}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveTargetParses input left afterLeft)
    (rightParsed : DeriveTargetParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftFirst, leftAfterFirst, leftComponents, leftFirstParsed,
      leftTail, leftShape⟩
  rcases rightParsed with
    ⟨rightFirst, rightAfterFirst, rightComponents, rightFirstParsed,
      rightTail, rightShape⟩
  have afterFirstEq := DeriveComponentParses.output_unique leftFirstParsed
    rightFirstParsed
  subst afterFirstEq
  exact DeriveTargetTailParses.output_unique leftTail rightTail

/-- Exact derive-target rejection excludes every complete target success. -/
theorem DeriveTargetRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : DeriveTargetRejects input rejected) :
    ¬ ∃ target output, DeriveTargetParses input target output := by
  rintro ⟨target, output, successful⟩
  rcases successful with
    ⟨first, afterFirst, components, firstParsed, tail, shape⟩
  cases rejection with
  | firstRejected componentRejected =>
      exact deriveComponentDeterministicOutcomeSpec.successRejectDisjoint
        componentRejected ⟨_, _, firstParsed⟩
  | tailRejected rejectedFirst tailRejected =>
      have afterFirstEq := DeriveComponentParses.output_unique rejectedFirst
        firstParsed
      subst afterFirstEq
      exact deriveTargetTailDeterministicOutcomeSpec.successRejectDisjoint
        tailRejected ⟨_, _, tail⟩

/-- Complete derive targets form a deterministic broad ordinary outcome. -/
theorem deriveTargetDeterministicOutcomeSpec :
    DeterministicOutcomeSpec DeriveTargetParses DeriveTargetRejects where
  successOutputUnique := DeriveTargetParses.output_unique
  successRejectDisjoint := DeriveTargetRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDeriveTargetExactnessProperties
/-! Full value and rejection-endpoint functionality for derive targets. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One ordinary or diagnosed derive component has one exact value. -/
theorem DeriveComponentParses.value_unique
    {input : Remainder} {left right : Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveComponentParses input left afterLeft)
    (rightParsed : DeriveComponentParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | identifier leftIdentifier =>
      cases rightParsed with
      | identifier rightIdentifier =>
          exact leftIdentifier.value_unique rightIdentifier
      | reserved keyword allowed span token =>
          have impossible := leftIdentifier.1.token_unique token
          cases impossible
  | reserved leftKeyword leftAllowed leftSpan leftToken =>
      cases rightParsed with
      | identifier rightIdentifier =>
          have impossible := leftToken.token_unique rightIdentifier.1
          cases impossible
      | reserved rightKeyword rightAllowed rightSpan rightToken =>
          have tokenEq := leftToken.token_unique rightToken
          have spanEq : leftSpan = rightSpan :=
            congrArg (fun token : Token => token.span) tokenEq
          have kindEq : leftKeyword = rightKeyword :=
            TokenKind.keyword.inj
              (congrArg (fun token : Token => token.value) tokenEq)
          subst spanEq
          subst kindEq
          rfl

/-- One derive component fixes both its exact value and final remainder. -/
theorem DeriveComponentParses.result_unique
    {input : Remainder} {left right : Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveComponentParses input left afterLeft)
    (rightParsed : DeriveComponentParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A rejected derive component has one exact nonconsuming endpoint. -/
theorem DeriveComponentRejects.output_unique
    {input left right : Remainder}
    (leftRejects : DeriveComponentRejects input left)
    (rightRejects : DeriveComponentRejects input right) : left = right := by
  cases leftRejects
  cases rightRejects
  rfl

/-- Derive components have fully functional success and rejection outcomes. -/
theorem deriveComponentExactOutcomeSpec :
    ExactDeterministicOutcomeSpec DeriveComponentParses
      DeriveComponentRejects where
  toDeterministicOutcomeSpec := deriveComponentDeterministicOutcomeSpec
  successValueUnique := DeriveComponentParses.value_unique
  rejectOutputUnique := DeriveComponentRejects.output_unique

/-- A maximal dotted derive tail has one exact component list. -/
theorem DeriveTargetTailParses.value_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveTargetTailParses input left afterLeft)
    (rightParsed : DeriveTargetTailParses input right afterRight) :
    left = right := by
  induction leftParsed generalizing right afterRight with
  | done leftDotAbsent =>
      cases rightParsed with
      | done => rfl
      | next rightDotSpan rightDot _ _ =>
          exact False.elim
            (absent_conflicts_token leftDotAbsent rightDot)
  | next leftDotSpan leftDot leftComponent leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightDotAbsent =>
          exact False.elim
            (absent_conflicts_token rightDotAbsent leftDot)
      | next rightDotSpan rightDot rightComponent rightTail =>
          have componentEq :=
            leftComponent.value_unique rightComponent
          have afterComponentEq :=
            leftComponent.output_unique rightComponent
          subst componentEq
          subst afterComponentEq
          have tailEq := inductionHypothesis rightTail
          subst tailEq
          rfl

/-- A maximal dotted tail fixes its component list and final remainder. -/
theorem DeriveTargetTailParses.result_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveTargetTailParses input left afterLeft)
    (rightParsed : DeriveTargetTailParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A dotted-tail rejection has one exact first failing endpoint. -/
theorem DeriveTargetTailRejects.output_unique
    {input left right : Remainder}
    (leftRejects : DeriveTargetTailRejects input left)
    (rightRejects : DeriveTargetTailRejects input right) : left = right := by
  induction leftRejects generalizing right with
  | componentRejected leftDotSpan leftDot leftComponentRejects =>
      cases rightRejects with
      | componentRejected rightDotSpan rightDot rightComponentRejects =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          exact leftComponentRejects.output_unique rightComponentRejects
      | laterRejected rightDotSpan rightDot rightComponent
            rightTailRejects =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          exact False.elim
            (deriveComponentDeterministicOutcomeSpec.successRejectDisjoint
              leftComponentRejects ⟨_, _, rightComponent⟩)
  | laterRejected leftDotSpan leftDot leftComponent leftTailRejects
        inductionHypothesis =>
      cases rightRejects with
      | componentRejected rightDotSpan rightDot rightComponentRejects =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          exact False.elim
            (deriveComponentDeterministicOutcomeSpec.successRejectDisjoint
              rightComponentRejects ⟨_, _, leftComponent⟩)
      | laterRejected rightDotSpan rightDot rightComponent
            rightTailRejects =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          rcases leftComponent.result_unique rightComponent with
            ⟨componentEq, afterComponentEq⟩
          subst componentEq
          subst afterComponentEq
          exact inductionHypothesis rightTailRejects

/-- Dotted tails have fully functional success and rejection outcomes. -/
theorem deriveTargetTailExactOutcomeSpec :
    ExactDeterministicOutcomeSpec DeriveTargetTailParses
      DeriveTargetTailRejects where
  toDeterministicOutcomeSpec := deriveTargetTailDeterministicOutcomeSpec
  successValueUnique := DeriveTargetTailParses.value_unique
  rejectOutputUnique := DeriveTargetTailRejects.output_unique

/-- A complete dotted derive target has one exact AST value. -/
theorem DeriveTargetParses.value_unique
    {input : Remainder} {left right : Syntax.DeriveTarget}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveTargetParses input left afterLeft)
    (rightParsed : DeriveTargetParses input right afterRight) :
    left = right := by
  rcases leftParsed with
    ⟨leftFirst, leftAfterFirst, leftComponents, leftFirstParsed,
      leftTail, leftShape⟩
  rcases rightParsed with
    ⟨rightFirst, rightAfterFirst, rightComponents, rightFirstParsed,
      rightTail, rightShape⟩
  rcases leftFirstParsed.result_unique rightFirstParsed with
    ⟨firstEq, afterFirstEq⟩
  subst firstEq
  subst afterFirstEq
  have componentsEq := leftTail.value_unique rightTail
  subst componentsEq
  exact leftShape.trans rightShape.symm

/-- A complete target fixes its exact AST value and final remainder. -/
theorem DeriveTargetParses.result_unique
    {input : Remainder} {left right : Syntax.DeriveTarget}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveTargetParses input left afterLeft)
    (rightParsed : DeriveTargetParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A complete derive-target rejection has one exact failing endpoint. -/
theorem DeriveTargetRejects.output_unique
    {input left right : Remainder}
    (leftRejects : DeriveTargetRejects input left)
    (rightRejects : DeriveTargetRejects input right) : left = right := by
  cases leftRejects with
  | firstRejected leftComponentRejects =>
      cases rightRejects with
      | firstRejected rightComponentRejects =>
          exact leftComponentRejects.output_unique rightComponentRejects
      | tailRejected rightFirst rightTailRejects =>
          exact False.elim
            (deriveComponentDeterministicOutcomeSpec.successRejectDisjoint
              leftComponentRejects ⟨_, _, rightFirst⟩)
  | tailRejected leftFirst leftTailRejects =>
      cases rightRejects with
      | firstRejected rightComponentRejects =>
          exact False.elim
            (deriveComponentDeterministicOutcomeSpec.successRejectDisjoint
              rightComponentRejects ⟨_, _, leftFirst⟩)
      | tailRejected rightFirst rightTailRejects =>
          rcases leftFirst.result_unique rightFirst with
            ⟨firstEq, afterFirstEq⟩
          subst firstEq
          subst afterFirstEq
          exact leftTailRejects.output_unique rightTailRejects

/-- Complete derive targets have exact deterministic ordinary outcomes. -/
theorem deriveTargetExactOutcomeSpec :
    ExactDeterministicOutcomeSpec DeriveTargetParses DeriveTargetRejects where
  toDeterministicOutcomeSpec := deriveTargetDeterministicOutcomeSpec
  successValueUnique := DeriveTargetParses.value_unique
  rejectOutputUnique := DeriveTargetRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDeriveAttributeValidOutcomeProperties
/-! Deterministic exact outcomes for the normal derive-attribute path. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token_variant {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem deriveTargetListDeterministicOutcomeSpec :
    DeterministicOutcomeSpec
      (NoTrailingDelimitedListParses .leftParen .rightParen
        DeriveTargetParses)
      (DelimitedListRejects .leftParen .rightParen true false
        DeriveTargetParses DeriveTargetRejects) :=
  noTrailingDelimitedListDeterministicOutcomeSpec .leftParen .rightParen
    deriveTargetDeterministicOutcomeSpec

/-- A successful normal derive attribute has one final remainder. -/
theorem DeriveAttributeParses.output_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeParses input left afterLeft)
    (rightParsed : DeriveAttributeParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftHashSpan, leftOpeningSpan, leftMarkerSpan, leftTargets,
      leftAfterTargets, leftClosingSpan, leftHash, leftOpening, leftMarker,
      leftTargetsParsed, leftClosing, leftOutput, leftShape⟩
  rcases rightParsed with
    ⟨rightHashSpan, rightOpeningSpan, rightMarkerSpan, rightTargets,
      rightAfterTargets, rightClosingSpan, rightHash, rightOpening,
      rightMarker, rightTargetsParsed, rightClosing, rightOutput,
      rightShape⟩
  have afterTargetsEq :=
    deriveTargetListDeterministicOutcomeSpec.successOutputUnique
      leftTargetsParsed rightTargetsParsed
  subst afterTargetsEq
  rw [leftOutput, rightOutput]

/-- Exact normal-path rejection excludes every normal derive-attribute
success. -/
theorem DeriveAttributeValidRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : DeriveAttributeValidRejects input rejected) :
    ¬ ∃ value output, DeriveAttributeParses input value output := by
  rintro ⟨value, output, successful⟩
  rcases successful with
    ⟨successfulHashSpan, successfulOpeningSpan, successfulMarkerSpan,
      targets, afterTargets, successfulClosingSpan, successfulHash,
      successfulOpening, successfulMarker, targetsParsed,
      successfulClosing, outputShape, attributeShape⟩
  cases rejection with
  | hashMissing hashAbsent =>
      exact absent_conflicts_token_variant hashAbsent successfulHash
  | openingMissing hashSpan hashParsed openingAbsent =>
      rw [hashParsed.2] at openingAbsent
      exact absent_conflicts_token_variant openingAbsent (by
        simpa only using successfulOpening)
  | markerMissing hashSpan openingSpan hashParsed openingParsed
      markerAbsent =>
      rw [hashParsed.2] at openingParsed
      rw [openingParsed.2] at markerAbsent
      exact absent_conflicts_token_variant markerAbsent (by
        simpa only [Nat.add_assoc] using successfulMarker)
  | targetsRejected hashSpan openingSpan markerSpan hashParsed openingParsed
      markerParsed targetsRejected =>
      rw [hashParsed.2] at openingParsed
      rw [openingParsed.2] at markerParsed
      rw [markerParsed.2] at targetsRejected
      have normalizedRejection :
          DelimitedListRejects .leftParen .rightParen true false
            DeriveTargetParses DeriveTargetRejects
            { input with cursor := input.cursor + 3 } rejected := by
        simpa only [Nat.add_assoc] using targetsRejected
      exact deriveTargetListDeterministicOutcomeSpec.successRejectDisjoint
        normalizedRejection ⟨_, _, targetsParsed⟩
  | closingMissing hashSpan openingSpan markerSpan hashParsed openingParsed
      markerParsed rejectedTargets closingAbsent =>
      rw [hashParsed.2] at openingParsed
      rw [openingParsed.2] at markerParsed
      rw [markerParsed.2] at rejectedTargets
      have normalizedTargets := rejectedTargets
      simp only [Nat.add_assoc] at normalizedTargets
      have afterTargetsEq :=
        deriveTargetListDeterministicOutcomeSpec.successOutputUnique
          normalizedTargets targetsParsed
      subst afterTargetsEq
      exact absent_conflicts_token_variant closingAbsent successfulClosing

/-- The normal derive-attribute path has deterministic and exclusive ordinary
outcomes. -/
theorem deriveAttributeValidDeterministicOutcomeSpec :
    DeterministicOutcomeSpec DeriveAttributeParses
      DeriveAttributeValidRejects where
  successOutputUnique := DeriveAttributeParses.output_unique
  successRejectDisjoint := DeriveAttributeValidRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDeriveAttributeOutcomeProperties
/-! Deterministic broad ordinary outcomes for public derive attributes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Prioritized normal-or-recovered derive success has one final remainder. -/
theorem DeriveAttributeOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeOrdinaryParses input left afterLeft)
    (rightParsed : DeriveAttributeOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | normal leftNormal =>
      cases rightParsed with
      | normal rightNormal =>
          exact deriveAttributeValidDeterministicOutcomeSpec.successOutputUnique
            leftNormal rightNormal
      | recovered rightValidRejection rightRecovered =>
          exact False.elim
            (deriveAttributeValidDeterministicOutcomeSpec.successRejectDisjoint
              rightValidRejection ⟨_, _, leftNormal⟩)
  | recovered leftValidRejection leftRecovered =>
      cases rightParsed with
      | normal rightNormal =>
          exact False.elim
            (deriveAttributeValidDeterministicOutcomeSpec.successRejectDisjoint
              leftValidRejection ⟨_, _, rightNormal⟩)
      | recovered rightValidRejection rightRecovered =>
          exact
            deriveAttributeRecoveredDeterministicOutcomeSpec.successOutputUnique
              leftRecovered rightRecovered

/-- Exact rejection of both branches excludes normal and recovered public
success alike. -/
theorem DeriveAttributeRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : DeriveAttributeRejects input rejected) :
    ¬ ∃ value output, DeriveAttributeOrdinaryParses input value output := by
  rintro ⟨value, output, successful⟩
  cases rejection with
  | both validRejection recoveredRejection =>
      cases successful with
      | normal normalParsed =>
          exact
            deriveAttributeValidDeterministicOutcomeSpec.successRejectDisjoint
              validRejection ⟨_, _, normalParsed⟩
      | recovered otherValidRejection recoveredParsed =>
          exact
            deriveAttributeRecoveredDeterministicOutcomeSpec.successRejectDisjoint
              recoveredRejection ⟨_, _, recoveredParsed⟩

/-- Public derive attributes have deterministic and exclusive ordinary
outcomes without claiming value or rejection-endpoint uniqueness. -/
theorem deriveAttributeDeterministicOutcomeSpec :
    DeterministicOutcomeSpec DeriveAttributeOrdinaryParses
      DeriveAttributeRejects where
  successOutputUnique := DeriveAttributeOrdinaryParses.output_unique
  successRejectDisjoint := DeriveAttributeRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDeriveAttributeValidExactnessProperties
/-! Full functionality of the normal derive-attribute outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem deriveTargetListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (NoTrailingDelimitedListParses .leftParen .rightParen
        DeriveTargetParses)
      (DelimitedListRejects .leftParen .rightParen true false
        DeriveTargetParses DeriveTargetRejects) :=
  noTrailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    deriveTargetExactOutcomeSpec

/-- A successful normal derive attribute has one exact AST value. -/
theorem DeriveAttributeParses.value_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeParses input left afterLeft)
    (rightParsed : DeriveAttributeParses input right afterRight) :
    left = right := by
  rcases leftParsed with
    ⟨leftHashSpan, leftOpeningSpan, leftMarkerSpan, leftTargets,
      leftAfterTargets, leftClosingSpan, leftHash, leftOpening, leftMarker,
      leftTargetsParsed, leftClosing, leftOutput, leftShape⟩
  rcases rightParsed with
    ⟨rightHashSpan, rightOpeningSpan, rightMarkerSpan, rightTargets,
      rightAfterTargets, rightClosingSpan, rightHash, rightOpening,
      rightMarker, rightTargetsParsed, rightClosing, rightOutput,
      rightShape⟩
  have hashTokenEq := leftHash.token_unique rightHash
  have hashSpanEq : leftHashSpan = rightHashSpan :=
    congrArg (fun token : Token => token.span) hashTokenEq
  rcases deriveTargetListExactOutcomeSpec.successResultUnique
      leftTargetsParsed rightTargetsParsed with
    ⟨targetsEq, afterTargetsEq⟩
  subst targetsEq
  subst afterTargetsEq
  have closingTokenEq := leftClosing.token_unique rightClosing
  have closingSpanEq : leftClosingSpan = rightClosingSpan :=
    congrArg (fun token : Token => token.span) closingTokenEq
  subst hashSpanEq
  subst closingSpanEq
  exact leftShape.trans rightShape.symm

/-- A successful normal derive attribute fixes its AST and final remainder. -/
theorem DeriveAttributeParses.result_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeParses input left afterLeft)
    (rightParsed : DeriveAttributeParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A normal-path rejection has one exact first failing endpoint. -/
theorem DeriveAttributeValidRejects.output_unique
    {input left right : Remainder}
    (leftRejects : DeriveAttributeValidRejects input left)
    (rightRejects : DeriveAttributeValidRejects input right) : left = right :=
  by
    cases leftRejects with
    | hashMissing leftHashAbsent =>
        cases rightRejects with
        | hashMissing => rfl
        | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
            exact False.elim
              (absent_conflicts_token_variant leftHashAbsent rightHash.1)
        | markerMissing rightHashSpan rightOpeningSpan rightHash rightOpening
              rightMarkerAbsent =>
            exact False.elim
              (absent_conflicts_token_variant leftHashAbsent rightHash.1)
        | targetsRejected rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargetsRejects =>
            exact False.elim
              (absent_conflicts_token_variant leftHashAbsent rightHash.1)
        | closingMissing rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargets
              rightClosingAbsent =>
            exact False.elim
              (absent_conflicts_token_variant leftHashAbsent rightHash.1)
    | openingMissing leftHashSpan leftHash leftOpeningAbsent =>
        cases rightRejects with
        | hashMissing rightHashAbsent =>
            exact False.elim
              (absent_conflicts_token_variant rightHashAbsent leftHash.1)
        | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
            exact leftHash.output_unique rightHash
        | markerMissing rightHashSpan rightOpeningSpan rightHash rightOpening
              rightMarkerAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact False.elim
              (absent_conflicts_token_variant leftOpeningAbsent rightOpening.1)
        | targetsRejected rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargetsRejects =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact False.elim
              (absent_conflicts_token_variant leftOpeningAbsent rightOpening.1)
        | closingMissing rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargets
              rightClosingAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact False.elim
              (absent_conflicts_token_variant leftOpeningAbsent rightOpening.1)
    | markerMissing leftHashSpan leftOpeningSpan leftHash leftOpening
          leftMarkerAbsent =>
        cases rightRejects with
        | hashMissing rightHashAbsent =>
            exact False.elim
              (absent_conflicts_token_variant rightHashAbsent leftHash.1)
        | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact False.elim
              (absent_conflicts_token_variant rightOpeningAbsent leftOpening.1)
        | markerMissing rightHashSpan rightOpeningSpan rightHash rightOpening
              rightMarkerAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact leftOpening.output_unique rightOpening
        | targetsRejected rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargetsRejects =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            exact False.elim
              (absent_conflicts_token_variant leftMarkerAbsent rightMarker.1)
        | closingMissing rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargets
              rightClosingAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            exact False.elim
              (absent_conflicts_token_variant leftMarkerAbsent rightMarker.1)
    | targetsRejected leftHashSpan leftOpeningSpan leftMarkerSpan leftHash
          leftOpening leftMarker leftTargetsRejects =>
        cases rightRejects with
        | hashMissing rightHashAbsent =>
            exact False.elim
              (absent_conflicts_token_variant rightHashAbsent leftHash.1)
        | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact False.elim
              (absent_conflicts_token_variant rightOpeningAbsent leftOpening.1)
        | markerMissing rightHashSpan rightOpeningSpan rightHash rightOpening
              rightMarkerAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            exact False.elim
              (absent_conflicts_token_variant rightMarkerAbsent leftMarker.1)
        | targetsRejected rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargetsRejects =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            have afterMarkerEq := leftMarker.output_unique rightMarker
            subst afterMarkerEq
            exact deriveTargetListExactOutcomeSpec.rejectOutputUnique
              leftTargetsRejects rightTargetsRejects
        | closingMissing rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargets
              rightClosingAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            have afterMarkerEq := leftMarker.output_unique rightMarker
            subst afterMarkerEq
            exact False.elim
              (deriveTargetListExactOutcomeSpec.successRejectDisjoint
                leftTargetsRejects ⟨_, _, rightTargets⟩)
    | closingMissing leftHashSpan leftOpeningSpan leftMarkerSpan leftHash
          leftOpening leftMarker leftTargets leftClosingAbsent =>
        cases rightRejects with
        | hashMissing rightHashAbsent =>
            exact False.elim
              (absent_conflicts_token_variant rightHashAbsent leftHash.1)
        | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact False.elim
              (absent_conflicts_token_variant rightOpeningAbsent leftOpening.1)
        | markerMissing rightHashSpan rightOpeningSpan rightHash rightOpening
              rightMarkerAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            exact False.elim
              (absent_conflicts_token_variant rightMarkerAbsent leftMarker.1)
        | targetsRejected rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargetsRejects =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            have afterMarkerEq := leftMarker.output_unique rightMarker
            subst afterMarkerEq
            exact False.elim
              (deriveTargetListExactOutcomeSpec.successRejectDisjoint
                rightTargetsRejects ⟨_, _, leftTargets⟩)
        | closingMissing rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargets
              rightClosingAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            have afterMarkerEq := leftMarker.output_unique rightMarker
            subst afterMarkerEq
            exact deriveTargetListExactOutcomeSpec.successOutputUnique
              leftTargets rightTargets

/-- The normal derive-attribute path has fully functional ordinary and
rejection outcomes. -/
theorem deriveAttributeValidExactOutcomeSpec :
    ExactDeterministicOutcomeSpec DeriveAttributeParses
      DeriveAttributeValidRejects where
  toDeterministicOutcomeSpec := deriveAttributeValidDeterministicOutcomeSpec
  successValueUnique := DeriveAttributeParses.value_unique
  rejectOutputUnique := DeriveAttributeValidRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDeriveAttributeExactnessProperties
/-! Full functionality of public prioritized derive-attribute outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Prioritized normal-or-recovered success has one exact AST value. -/
theorem DeriveAttributeOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeOrdinaryParses input left afterLeft)
    (rightParsed : DeriveAttributeOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | normal leftNormal =>
      cases rightParsed with
      | normal rightNormal =>
          exact deriveAttributeValidExactOutcomeSpec.successValueUnique
            leftNormal rightNormal
      | recovered rightValidRejects rightRecovered =>
          exact False.elim
            (deriveAttributeValidExactOutcomeSpec.successRejectDisjoint
              rightValidRejects ⟨_, _, leftNormal⟩)
  | recovered leftValidRejects leftRecovered =>
      cases rightParsed with
      | normal rightNormal =>
          exact False.elim
            (deriveAttributeValidExactOutcomeSpec.successRejectDisjoint
              leftValidRejects ⟨_, _, rightNormal⟩)
      | recovered rightValidRejects rightRecovered =>
          exact deriveAttributeRecoveredExactOutcomeSpec.successValueUnique
            leftRecovered rightRecovered

/-- Prioritized normal-or-recovered success fixes its AST and final
remainder. -/
theorem DeriveAttributeOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeOrdinaryParses input left afterLeft)
    (rightParsed : DeriveAttributeOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Public rejection has one exact endpoint, namely recovery's first failing
endpoint after both branches reject. -/
theorem DeriveAttributeRejects.output_unique
    {input left right : Remainder}
    (leftRejects : DeriveAttributeRejects input left)
    (rightRejects : DeriveAttributeRejects input right) : left = right := by
  cases leftRejects with
  | both leftValidRejects leftRecoveredRejects =>
      cases rightRejects with
      | both rightValidRejects rightRecoveredRejects =>
          exact
            deriveAttributeRecoveredExactOutcomeSpec.rejectOutputUnique
              leftRecoveredRejects rightRecoveredRejects

/-- Public derive attributes have fully functional prioritized success and
rejection outcomes. -/
theorem deriveAttributeExactOutcomeSpec :
    ExactDeterministicOutcomeSpec DeriveAttributeOrdinaryParses
      DeriveAttributeRejects where
  toDeterministicOutcomeSpec := deriveAttributeDeterministicOutcomeSpec
  successValueUnique := DeriveAttributeOrdinaryParses.value_unique
  rejectOutputUnique := DeriveAttributeRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractDeriveAttachmentProperties
/-! Functional and total laws for pure contract-member derive attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Attaching one derive attribute to one contract member has one exact AST
result. -/
theorem ContractDeriveAttaches.output_unique
    {derive : Syntax.DeriveAttribute} {member left right : Syntax.ContractMember}
    (leftAttached : ContractDeriveAttaches derive member left)
    (rightAttached : ContractDeriveAttaches derive member right) :
    left = right := by
  cases leftAttached <;> cases rightAttached <;> rfl

/-- Every contract-member variant has an exact derive-attachment result. -/
theorem ContractDeriveAttaches.exists
    (derive : Syntax.DeriveAttribute) (member : Syntax.ContractMember) :
    ∃ output, ContractDeriveAttaches derive member output := by
  rcases member with ⟨memberSpan, leadingComments, value⟩
  cases value with
  | field declaration =>
      exact ⟨_, .field⟩
  | function declaration =>
      exact ⟨_, .function⟩
  | constructor declaration =>
      exact ⟨_, .constructor⟩
  | fallback declaration =>
      exact ⟨_, .fallback⟩
  | typeAlias declaration =>
      exact ⟨_, .typeAlias⟩
  | enum declaration =>
      exact ⟨_, .enum⟩
  | error =>
      exact ⟨_, .error⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeAliasValueOutcomeProperties
/-! Deterministic ordinary outcomes for recovery-aware type-alias values. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every pre-recovery boundary is also a stop of the recovery scan. -/
theorem TypeAliasValueBoundaryStops.toRecoveryStop
    {input : Remainder} (stops : TypeAliasValueBoundaryStops input) :
    TypeAliasValueRecoveryStops input := by
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | semicolon token => exact .semicolon token

/-- The recursive malformed-value scan has one final remainder. -/
theorem TypeAliasValueRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.TypeExpr} {afterLeft afterRight : Remainder},
      TypeAliasValueRecoveryScanParses first leftLast input left afterLeft →
      TypeAliasValueRecoveryScanParses first rightLast input right afterRight →
      afterLeft = afterRight := by
  intro first leftLast rightLast input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing rightLast right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- Complete malformed-value recovery has one final remainder. -/
theorem TypeAliasValueRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueRecoveryParses input left afterLeft)
    (rightParsed : TypeAliasValueRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftContinues leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightContinues rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Every recovery rejection retains its complete input remainder. -/
theorem TypeAliasValueRecoveryRejects.output_eq
    {input rejected : Remainder}
    (rejection : TypeAliasValueRecoveryRejects input rejected) :
    rejected = input := by
  cases rejection <;> rfl

/-- An unavailable recovery first token excludes every recovery success. -/
theorem TypeAliasValueRecoveryRejects.disjointParses
    {input rejected : Remainder}
    (rejection : TypeAliasValueRecoveryRejects input rejected) :
    ¬ ∃ value output, TypeAliasValueRecoveryParses input value output := by
  rintro ⟨value, output, parsed⟩
  cases parsed with
  | recovered continues current scan =>
      cases rejection with
      | boundary stops => exact continues stops
      | missingToken inside missing =>
          rw [current.2] at missing
          contradiction

/-- Standalone malformed-value recovery has deterministic ordinary outcomes. -/
theorem typeAliasValueRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TypeAliasValueRecoveryParses
      TypeAliasValueRecoveryRejects where
  successOutputUnique := TypeAliasValueRecoveryParses.output_unique
  successRejectDisjoint := TypeAliasValueRecoveryRejects.disjointParses

/-- Preserved carrier and window evidence makes cursor-only rewind exact. -/
theorem TypeAliasValueCoreRejectsWithPreservedWindow.exists_rewind_eq
    {input : Remainder}
    (rejected : TypeAliasValueCoreRejectsWithPreservedWindow input) :
    ∃ failed, TypeExprRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- A preserved Core rejection excludes strict Core type success. -/
theorem TypeAliasValueCoreRejectsWithPreservedWindow.disjointOrdinary
    {input : Remainder}
    (rejected : TypeAliasValueCoreRejectsWithPreservedWindow input) :
    ¬ ∃ value output, TypeExprOrdinaryParses input value output := by
  rintro ⟨value, output, parsed⟩
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  exact typeExprDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨_, _, parsed⟩

/-- Recovery-aware alias-value success has one final remainder. -/
theorem TypeAliasValueOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasValueOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact typeExprDeterministicOutcomeSpec.successOutputUnique leftCore
            rightCore
      | recovered rightRejected rightRecovery =>
          exact False.elim
            (rightRejected.disjointOrdinary ⟨_, _, leftCore⟩)
  | recovered leftRejected leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          exact False.elim
            (leftRejected.disjointOrdinary ⟨_, _, rightCore⟩)
      | recovered rightRejected rightRecovery =>
          exact leftRecovery.output_unique rightRecovery

/-- Exact alias-value rejection excludes strict and recovered success. -/
theorem TypeAliasValueRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : TypeAliasValueRejects input rejected) :
    ¬ ∃ value output, TypeAliasValueOrdinaryParses input value output := by
  rintro ⟨value, output, successful⟩
  cases rejection with
  | boundary coreRejected stops =>
      cases successful with
      | core coreParsed =>
          exact coreRejected.disjointOrdinary ⟨_, _, coreParsed⟩
      | recovered otherRejected recovered =>
          cases recovered with
          | recovered continues current scan => exact continues stops
  | recovery coreRejected continues recoveryRejected =>
      cases successful with
      | core coreParsed =>
          exact coreRejected.disjointOrdinary ⟨_, _, coreParsed⟩
      | recovered otherRejected recovered =>
          exact typeAliasValueRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint recoveryRejected ⟨_, _, recovered⟩

/-- Every alias-value rejection returns the rewound input remainder. -/
theorem TypeAliasValueRejects.output_eq
    {input rejected : Remainder}
    (rejection : TypeAliasValueRejects input rejected) : rejected = input := by
  cases rejection with
  | boundary => rfl
  | recovery coreRejected continues recoveryRejected =>
      exact recoveryRejected.output_eq

/-- Recovery-aware alias values have deterministic and exclusive outcomes. -/
theorem typeAliasValueDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TypeAliasValueOrdinaryParses
      TypeAliasValueRejects where
  successOutputUnique := TypeAliasValueOrdinaryParses.output_unique
  successRejectDisjoint := TypeAliasValueRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeAliasValueRecoveryExactnessProperties
/-!
Exact malformed type-alias value recovery and its conditional lift through
the remaining Core type-expression frontier.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exact_tokenAt_unique {tokens : Array Token}
    {endIndex index : Nat} {left right : Token}
    (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- With the same retained first and last spans, a recovery scan constructs
one exact error type value. -/
theorem TypeAliasValueRecoveryScanParses.value_unique :
    ∀ {first last : SourceSpan} {input : Remainder}
      {left right : Syntax.TypeExpr} {afterLeft afterRight : Remainder},
      TypeAliasValueRecoveryScanParses first last input left afterLeft →
      TypeAliasValueRecoveryScanParses first last input right afterRight →
      left = right := by
  intro first last input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing right with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops =>
          exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := exact_tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- A recovery scan fixes both its error type value and final remainder. -/
theorem TypeAliasValueRecoveryScanParses.result_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.TypeExpr} {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueRecoveryScanParses first last input left
      afterLeft)
    (rightParsed : TypeAliasValueRecoveryScanParses first last input right
      afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Complete malformed-value recovery constructs one exact error type. -/
theorem TypeAliasValueRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueRecoveryParses input left afterLeft)
    (rightParsed : TypeAliasValueRecoveryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | recovered leftContinues leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightContinues rightCurrent rightScan =>
          have currentEq := exact_tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.value_unique rightScan

/-- Complete malformed-value recovery fixes its value and remainder. -/
theorem TypeAliasValueRecoveryParses.result_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueRecoveryParses input left afterLeft)
    (rightParsed : TypeAliasValueRecoveryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Every unavailable-first-token recovery rejection has one endpoint. -/
theorem TypeAliasValueRecoveryRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TypeAliasValueRecoveryRejects input left)
    (rightRejected : TypeAliasValueRecoveryRejects input right) :
    left = right :=
  leftRejected.output_eq.trans rightRejected.output_eq.symm

/-- Standalone malformed-value recovery has fully exact outcomes. -/
theorem typeAliasValueRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TypeAliasValueRecoveryParses
      TypeAliasValueRecoveryRejects where
  toDeterministicOutcomeSpec :=
    typeAliasValueRecoveryDeterministicOutcomeSpec
  successValueUnique := TypeAliasValueRecoveryParses.value_unique
  rejectOutputUnique := TypeAliasValueRecoveryRejects.output_unique

/-- Exact Core type outcomes make recovery-aware alias values exact. -/
theorem TypeAliasValueOrdinaryParses.value_unique_of_typeExpr
    (typeOutcomes : ExactDeterministicOutcomeSpec
      TypeExprOrdinaryParses TypeExprRejects)
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasValueOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact typeOutcomes.successValueUnique leftCore rightCore
      | recovered rightCoreRejected rightRecovery =>
          exact False.elim
            (rightCoreRejected.disjointOrdinary ⟨_, _, leftCore⟩)
  | recovered leftCoreRejected leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          exact False.elim
            (leftCoreRejected.disjointOrdinary ⟨_, _, rightCore⟩)
      | recovered rightCoreRejected rightRecovery =>
          exact typeAliasValueRecoveryExactOutcomeSpec.successValueUnique
            leftRecovery rightRecovery

/-- Under exact Core type outcomes, alias values fix both their value and
final remainder. -/
theorem TypeAliasValueOrdinaryParses.result_unique_of_typeExpr
    (typeOutcomes : ExactDeterministicOutcomeSpec
      TypeExprOrdinaryParses TypeExprRejects)
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasValueOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_typeExpr typeOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Public alias-value rejection always has the rewound input endpoint. -/
theorem TypeAliasValueRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TypeAliasValueRejects input left)
    (rightRejected : TypeAliasValueRejects input right) :
    left = right :=
  leftRejected.output_eq.trans rightRejected.output_eq.symm

/-- Exact Core type outcomes lift through alias-value recovery without any
further prerequisite. -/
theorem typeAliasValueExactOutcomeSpecOfTypeExpr
    (typeOutcomes : ExactDeterministicOutcomeSpec
      TypeExprOrdinaryParses TypeExprRejects) :
    ExactDeterministicOutcomeSpec TypeAliasValueOrdinaryParses
      TypeAliasValueRejects where
  toDeterministicOutcomeSpec := typeAliasValueDeterministicOutcomeSpec
  successValueUnique :=
    TypeAliasValueOrdinaryParses.value_unique_of_typeExpr typeOutcomes
  rejectOutputUnique := TypeAliasValueRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeAliasParametersOutcomeProperties
/-! Deterministic exact outcomes for optional type-alias parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem typeAliasParameters_opening_present
    {input output : Remainder} {parameters : DelimitedList Syntax.Identifier}
    (parsed : TypeAliasParametersOrdinaryParses input parameters output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftParen } := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

/-- The exact allow-empty, allow-trailing alias parameter list has deterministic
and exclusive identifier outcomes. -/
theorem typeAliasParametersDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TypeAliasParametersOrdinaryParses
      TypeAliasParametersRejects :=
  trailingDelimitedListDeterministicOutcomeSpec .leftParen .rightParen
    identifierDeterministicOutcomeSpec

/-- Optional type-alias parameter success has one final remainder. -/
theorem OptionalTypeAliasParametersOrdinaryParses.output_unique
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.Identifier)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalTypeAliasParametersOrdinaryParses input left
      afterLeft)
    (rightParsed : OptionalTypeAliasParametersOrdinaryParses input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightParsed =>
          rcases typeAliasParameters_opening_present rightParsed with
            ⟨span, openingPresent⟩
          exact False.elim
            (absent_conflicts_token_variant leftAbsent openingPresent)
  | present leftParsed =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases typeAliasParameters_opening_present leftParsed with
            ⟨span, openingPresent⟩
          exact False.elim
            (absent_conflicts_token_variant rightAbsent openingPresent)
      | present rightParsed =>
          exact typeAliasParametersDeterministicOutcomeSpec
            |>.successOutputUnique leftParsed rightParsed

/-- Exact optional alias-parameter rejection excludes absent and present
success. -/
theorem OptionalTypeAliasParametersRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalTypeAliasParametersRejects input rejected) :
    ¬ ∃ parameters output,
      OptionalTypeAliasParametersOrdinaryParses input parameters output := by
  rintro ⟨parameters, output, successful⟩
  cases rejection with
  | present openingPresent parametersRejected =>
      cases successful with
      | absent openingAbsent =>
          rcases openingPresent with ⟨span, openingToken⟩
          exact absent_conflicts_token_variant openingAbsent openingToken
      | present parametersParsed =>
          exact typeAliasParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint parametersRejected
              ⟨_, _, parametersParsed⟩

/-- Optional type-alias parameters have deterministic and exclusive ordinary
outcomes. -/
theorem optionalTypeAliasParametersDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalTypeAliasParametersOrdinaryParses
      OptionalTypeAliasParametersRejects where
  successOutputUnique :=
    OptionalTypeAliasParametersOrdinaryParses.output_unique
  successRejectDisjoint :=
    OptionalTypeAliasParametersRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeAliasOutcomeProperties
/-! Deterministic exact ordinary outcomes for complete type-alias declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary complete type-alias success has one final remainder. -/
theorem TypeAliasDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.TypeAliasDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasDeclOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftKeywordSpan leftEqualSpan leftSemicolonSpan leftKeyword leftName
        leftParameters leftEqual leftValue leftSemicolon =>
      cases rightParsed with
      | parsed rightKeywordSpan rightEqualSpan rightSemicolonSpan rightKeyword
            rightName rightParameters rightEqual rightValue rightSemicolon =>
          have afterKeywordEq := exactToken_output_unique leftKeyword
            rightKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          have afterParametersEq := leftParameters.output_unique rightParameters
          subst afterParametersEq
          have afterEqualEq := exactToken_output_unique leftEqual rightEqual
          subst afterEqualEq
          have afterValueEq := leftValue.output_unique rightValue
          subst afterValueEq
          exact exactToken_output_unique leftSemicolon rightSemicolon

/-- Exact complete type-alias rejection excludes every ordinary success. -/
theorem TypeAliasDeclRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : TypeAliasDeclRejects input rejected) :
    ¬ ∃ declaration output,
      TypeAliasDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulKeywordSpan successfulEqualSpan successfulSemicolonSpan
        successfulKeyword successfulName successfulParameters successfulEqual
        successfulValue successfulSemicolon =>
      cases rejection with
      | keywordMissing keywordAbsent =>
          exact absent_conflicts_exact keywordAbsent successfulKeyword
      | nameRejected rejectedKeywordSpan rejectedKeyword nameRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | parametersRejected rejectedKeywordSpan rejectedKeyword rejectedName
            parametersRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact optionalTypeAliasParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint parametersRejected
              ⟨_, _, successfulParameters⟩
      | equalMissing rejectedKeywordSpan rejectedKeyword rejectedName
            rejectedParameters equalAbsent =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          exact absent_conflicts_exact equalAbsent successfulEqual
      | valueRejected rejectedKeywordSpan rejectedEqualSpan rejectedKeyword
            rejectedName rejectedParameters rejectedEqual valueRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterEqualEq := exactToken_output_unique rejectedEqual
            successfulEqual
          subst afterEqualEq
          exact typeAliasValueDeterministicOutcomeSpec
            |>.successRejectDisjoint valueRejected ⟨_, _, successfulValue⟩
      | semicolonMissing rejectedKeywordSpan rejectedEqualSpan rejectedKeyword
            rejectedName rejectedParameters rejectedEqual rejectedValue
            semicolonAbsent =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterEqualEq := exactToken_output_unique rejectedEqual
            successfulEqual
          subst afterEqualEq
          have afterValueEq := rejectedValue.output_unique successfulValue
          subst afterValueEq
          exact absent_conflicts_exact semicolonAbsent successfulSemicolon

/-- Complete broad type aliases have deterministic and exclusive ordinary
outcomes. -/
theorem typeAliasDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TypeAliasDeclOrdinaryParses
      TypeAliasDeclRejects where
  successOutputUnique := TypeAliasDeclOrdinaryParses.output_unique
  successRejectDisjoint := TypeAliasDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeAliasParametersExactnessProperties
/-! Exact values and rejection endpoints for optional type-alias parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exact_absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem exact_typeAliasParameters_opening_present
    {input output : Remainder} {parameters : DelimitedList Syntax.Identifier}
    (parsed : TypeAliasParametersOrdinaryParses input parameters output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftParen } := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

/-- The allow-empty, allow-trailing alias parameter list has one exact value,
final remainder, and rejecting endpoint. -/
theorem typeAliasParametersExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TypeAliasParametersOrdinaryParses
      TypeAliasParametersRejects :=
  trailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    identifierExactOutcomeSpec

/-- Optional alias parameters have one exact optional list value. -/
theorem OptionalTypeAliasParametersOrdinaryParses.value_unique
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.Identifier)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalTypeAliasParametersOrdinaryParses input left
      afterLeft)
    (rightParsed : OptionalTypeAliasParametersOrdinaryParses input right
      afterRight) :
    left = right := by
  cases leftParsed with
  | absent leftOpeningAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightParameters =>
          rcases exact_typeAliasParameters_opening_present rightParameters with
            ⟨span, openingToken⟩
          exact False.elim
            (exact_absent_conflicts_token leftOpeningAbsent openingToken)
  | present leftParameters =>
      cases rightParsed with
      | absent rightOpeningAbsent =>
          rcases exact_typeAliasParameters_opening_present leftParameters with
            ⟨span, openingToken⟩
          exact False.elim
            (exact_absent_conflicts_token rightOpeningAbsent openingToken)
      | present rightParameters =>
          have parametersEq :=
            typeAliasParametersExactOutcomeSpec.successValueUnique
              leftParameters rightParameters
          subst parametersEq
          rfl

/-- Optional alias parameters fix both their value and final remainder. -/
theorem OptionalTypeAliasParametersOrdinaryParses.result_unique
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.Identifier)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalTypeAliasParametersOrdinaryParses input left
      afterLeft)
    (rightParsed : OptionalTypeAliasParametersOrdinaryParses input right
      afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- A committed optional-parameter rejection has one failing endpoint. -/
theorem OptionalTypeAliasParametersRejects.output_unique
    {input left right : Remainder}
    (leftRejected : OptionalTypeAliasParametersRejects input left)
    (rightRejected : OptionalTypeAliasParametersRejects input right) :
    left = right := by
  cases leftRejected with
  | present leftOpening leftParameters =>
      cases rightRejected with
      | present rightOpening rightParameters =>
          exact typeAliasParametersExactOutcomeSpec.rejectOutputUnique
            leftParameters rightParameters

/-- Optional type-alias parameters have exact ordinary outcomes. -/
theorem optionalTypeAliasParametersExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      OptionalTypeAliasParametersOrdinaryParses
      OptionalTypeAliasParametersRejects where
  toDeterministicOutcomeSpec :=
    optionalTypeAliasParametersDeterministicOutcomeSpec
  successValueUnique :=
    OptionalTypeAliasParametersOrdinaryParses.value_unique
  rejectOutputUnique :=
    OptionalTypeAliasParametersRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end
