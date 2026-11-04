import Solcore.Syntax.CallableDeclarationValidity
import Solcore.Syntax.ContractDeclarationValidity
import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.Parser.ConstructorSelectionSoundnessProperties
import Solcore.Syntax.Parser.ContractBodyCompletenessProperties
import Solcore.Syntax.Parser.ContractBodyProperties
import Solcore.Syntax.Parser.ContractBodyStateProperties
import Solcore.Syntax.Parser.ContractBodyTotalityProperties
import Solcore.Syntax.Parser.ContractCanonicalProperties
import Solcore.Syntax.Parser.ContractDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberCoreOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberWithAttributeOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractDeclarationProperties
import Solcore.Syntax.Parser.ContractDeclarationTotalityProperties
import Solcore.Syntax.Parser.ContractFieldOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractFieldTotalityProperties
import Solcore.Syntax.Parser.ContractMemberCompletenessProperties
import Solcore.Syntax.Parser.ContractMemberRecoveryCompletenessProperties
import Solcore.Syntax.Parser.ContractMemberStrictProperties
import Solcore.Syntax.Parser.ContractMemberTotalityProperties
import Solcore.Syntax.Parser.ContractProperties
import Solcore.Syntax.Parser.ContractRecoveryProperties
import Solcore.Syntax.Parser.ContractRecoveryTotalityProperties
import Solcore.Syntax.Parser.ConstructorDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractDeclSoundnessProperties
import Solcore.Syntax.Parser.CoreTermPublicOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FallbackDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser
import Solcore.Syntax.Parser.DeclarationCanonicalProperties
import Solcore.Syntax.Parser.FunctionDeclarationCompletenessProperties
import Solcore.Syntax.Parser.ImplementationDeclarationCompletenessProperties
import Solcore.Syntax.Parser.ContractDeclarationCompletenessProperties
import Solcore.Syntax.Parser.DeriveCarrierProperties
import Solcore.Syntax.Parser.DeriveAttributeOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DeriveAttributeTotalityProperties
import Solcore.Syntax.Parser.DeriveCompletenessProperties
import Solcore.Syntax.Parser.DeriveRecoveryTotalityProperties
import Solcore.Syntax.Parser.Derive
import Solcore.Syntax.Parser.DeriveTargetOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DeriveTargetTotalityProperties
import Solcore.Syntax.Parser.Enum
import Solcore.Syntax.Parser.FunctionDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionDeclSoundnessProperties
import Solcore.Syntax.Parser.FunctionDeclarationTotalityProperties
import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionParametersExactnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionParameterOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionParametersOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionParametersSoundnessProperties
import Solcore.Syntax.Parser.FunctionProperties
import Solcore.Syntax.Parser.FunctionSignatureLeafTotalityProperties
import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.Parser.FunctionSignatureOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionSignatureSoundnessProperties
import Solcore.Syntax.Parser.FunctionSignatureTotalityProperties
import Solcore.Syntax.Parser.Impl
import Solcore.Syntax.Parser.LocalExportItemOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SelectorNameOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SimpleDeclarationCompletenessProperties
import Solcore.Syntax.Parser.Trait
import Solcore.Syntax.Parser.TypeAlias
import Solcore.Syntax.Parser.PredicateSequenceOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseTotalityProperties
import Solcore.Syntax.SignatureValidity

/-!
# Declaration syntax tests

Contracts and their members, enums, traits, implementations, functions and signatures, type
aliases, `derive`, and the `where` and return clauses.
-/

section
-- leanmerge: from Solcore.Test.SyntaxCallableDeclarationValidity
/-! External consumers for callable declaration validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @FunctionDecl.ValidFor
example := @TraitMethod.ValidFor
example := @TraitDecl.ValidFor
example := @ImplMethod.ValidFor
example := @ImplDecl.ValidFor

example (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (declaration : FunctionDecl)
    (valid : FunctionDecl.ValidFor statementValid file declaration)
    (statement : Statement)
    (member : statement ∈ declaration.value.body.value) :
    declaration.value.signature.ValidFor file ∧
      statementValid file statement :=
  ⟨valid.2.1, valid.2.2.2 statement member⟩

example (file : SourceFile) (declaration : TraitDecl)
    (valid : TraitDecl.ValidFor file declaration)
    (method : TraitMethod) (member : method ∈ declaration.value.methods) :
    declaration.value.bodySpan.ValidFor file ∧
      TraitMethod.ValidFor file method :=
  ⟨valid.2.2.2.2.2.1, valid.2.2.2.2.2.2 method member⟩

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxContractDeclarationValidity
/-! External consumers for canonical contract declaration validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @ContractField.ValidFor
example := @ConstructorDecl.ValidFor
example := @FallbackDecl.ValidFor
example := @ContractMember.ValidFor
example := @ContractDecl.ValidFor

example := @namedParameter_preservesTokenWindow
example := @namedParameter_preservesTokensOnSuccess
example := @namedParameter_validFor
example := @FunctionParameterInternals.ordinaryNamedParameter_validFor
example := @FunctionParameterInternals.comptimeNamedParameter_validFor
example := @FunctionParameterInternals.namedParameterCore_validFor
example := @FunctionParameterInternals.finishRecoveredParameter_validFor
example := @FunctionParameterInternals.recoverParameterAux_validFor
example := @FunctionParameterInternals.recoverParameter_validFor
example := @FunctionParameterInternals.namedParameterTail_validFor
example := @LambdaParameterInternals.ofFunctionParameter_validFor
example := @LambdaParameterInternals.ordinaryLambdaParameterTail_validFor
example := @LambdaParameterInternals.comptimeLambdaParameterTail_validFor
example := @LambdaParameterInternals.ordinaryLambdaParameter_validFor
example := @LambdaParameterInternals.comptimeLambdaParameter_validFor
example := @LambdaParameterInternals.lambdaParameterCore_validFor
example := @LambdaParameterInternals.recoverLambdaParameter_validFor
example := @LambdaParameterInternals.lambdaParameterCore_preservesTokenWindow
example := @LambdaParameterInternals.recoverLambdaParameter_preservesTokenWindow
example := @lambdaParameter_validFor
example := @lambdaParameter_preservesTokenWindow
example := @lambdaParameter_preservesTokensOnSuccess
example := @lambdaParameter_ok_state_shape
example := @lambdaParameter_cursorMonotoneOnSuccess
example := @lambdaParameter_startsAtCurrentTokenOnSuccess
example := @ContractEntryInternals.entryParameters_validFor_of_namedParameter
example := @ContractEntryInternals.entryParameters_validFor
example := @ContractEntryInternals.entryParameters_preservesTokenWindow
example := @ContractEntryInternals.entryParameters_preservesTokensOnSuccess
example :=
  @ContractEntryInternals.entryParameters_cursorMonotoneOnSuccess
example :=
  @ContractEntryInternals.entryParameters_startsAtCurrentTokenOnSuccess
example := @ContractEntryInternals.optionalModifier_validFor
example := @ContractEntryInternals.optionalModifier_preservesTokenWindow
example := @ContractEntryInternals.optionalModifier_preservesTokensOnSuccess
example :=
  @ContractEntryInternals.optionalModifier_cursorMonotoneOnSuccess
example :=
  @ContractEntryInternals.optionalModifier_some_startsAtCurrentTokenOnSuccess
example := @ContractEntryInternals.implicitPublicModifiers_validFor
example :=
  @ContractEntryInternals.implicitPublicModifiers_preservesTokenWindow
example :=
  @ContractEntryInternals.implicitPublicModifiers_preservesTokensOnSuccess
example :=
  @ContractEntryInternals.implicitPublicModifiers_cursorMonotoneOnSuccess
example := @constructorDecl_preservesTokenWindow
example := @constructorDecl_preservesTokensOnSuccess
example := @constructorDecl_cursorMonotoneOnSuccess
example := @constructorDecl_startsAtCurrentTokenOnSuccess
example := @ContractEntryInternals.requiredBlock_startsAtCurrentTokenOnSuccess
example := @constructorDecl_span_validOnSuccess
example := @constructorDecl_validFor_of_span
example := @constructorDecl_validFor
example := @fallbackDecl_span_validOnSuccess
example := @fallbackDecl_validFor_of_span
example := @fallbackDecl_validFor
example := @fallbackDecl_preservesTokenWindow
example := @fallbackDecl_preservesTokensOnSuccess
example := @fallbackDecl_cursorMonotoneOnSuccess
example := @fallbackDecl_startsAtCurrentTokenOnSuccess

example (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (declaration : ContractDecl)
    (valid : ContractDecl.ValidFor statementValid expressionValid
      file declaration)
    (member : ContractMember)
    (retained : member ∈ declaration.value.members) :
    declaration.value.bodySpan.ValidFor file ∧
      ContractMember.ValidFor statementValid expressionValid file member :=
  ⟨valid.2.2.2.2.1, valid.2.2.2.2.2 member retained⟩

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserConstructorSelectionSoundnessProperties
/-! External consumers for constructor-selection grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserConstructorSelectionSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @IdentifierParses
example := @ConstructorNamesParses
example := @ConstructorSelectionParses
example := @identifier_success_sound
example := @requireConstructorNames_success_shape
example := @constructorSelection_success_sound
example := @constructorSelection_success_sound_and_validFor

example {input next : State} {selection : ConstructorSelection}
    (inputValid : input.ValidFor)
    (result : ExportInternals.constructorSelection input =
      .ok selection next) :
    ConstructorSelectionParses input.declarativeRemainder selection
        next.declarativeRemainder ∧
      selection.ValidFor input.file :=
  constructorSelection_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserConstructorSelectionSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractBodyCompletenessProperties
/-! Contract-body completeness consumers keep independent grammar spans and
forward member lists distinct from the executable body structure. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractBodyCompletenessProperties

open Solcore
open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example {input : State} (inputValid : input.ValidFor)
    {span : SourceSpan} {members : List ContractMember}
    {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ContractBodyOrdinaryParses
      input.declarativeRemainder span members remainder) :
    ∃ output, contractBody input = .ok ⟨span, members⟩ output ∧
      output.declarativeRemainder = remainder :=
  (contractBody_ordinary_success_iff inputValid
    (body := ⟨span, members⟩)).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {body : ContractBody} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : contractBody input = .ok body output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ContractBodyOrdinaryParses
      input.declarativeRemainder body.span body.members remainder :=
  (contractBody_ordinary_success_iff inputValid).mpr
    ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ContractBodyRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, contractBody input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (contractBody_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : contractBody input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ContractBodyRejects
      input.declarativeRemainder rejected :=
  (contractBody_ordinary_reject_iff inputValid).mpr
    ⟨failure, output, result, remainderEq⟩

end Solcore.Test.SyntaxParserContractBodyCompletenessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractBodyProperties
set_option autoImplicit false

namespace Tests
open Solcore.Syntax.Parser

example := @ContractInternals.ContractBody
example := @ContractInternals.ContractBody.ValidFor
example := @ContractInternals.closeContractBody_validFor
example := @ContractInternals.contractMembers_validFor
example := @ContractInternals.contractBody_validFor

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractBodyStateProperties
set_option autoImplicit false

namespace Tests
open Solcore.Syntax.Parser

example := @ContractInternals.closeContractBody_preservesTokenWindow
example := @ContractInternals.contractMembers_preservesTokenWindow
example := @ContractInternals.contractMembers_ok_state_shape
example := @ContractInternals.contractBody_preservesTokenWindow
example := @ContractInternals.contractBody_preservesTokensOnSuccess
example := @ContractInternals.contractBody_ok_state_shape
example := @ContractInternals.contractBody_cursor_lt_onSuccess
example := @ContractInternals.contractBody_cursorMonotoneOnSuccess
example := @ContractInternals.contractBody_startsAtCurrentTokenOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractBodyTotalityProperties
/-! External consumers for conditional contract-body totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractBodyTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example := @ContractMemberInvariantFreeOnValid
example := @contractMembers_ordinary_of_remainingCount_lt
example := @contractMembers_production_ordinary
example := @contractBody_ordinary
example := @contractBody_ne_invariant

example (ordinary : ContractMemberInvariantFreeOnValid)
    (input : State) (valid : input.ValidFor)
    (error : ParserInvariantError) :
    contractBody input ≠ .invariant error :=
  contractBody_ne_invariant ordinary input valid error

end Solcore.Test.SyntaxParserContractBodyTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractCanonicalProperties
namespace Tests
open Solcore.Syntax.Parser
example := @contractBody_canonical_inputs
example := @contractDecl_canonical_contract
example := @contractDecl_canonical_validFor
example := @contractDecl_canonical_preservesTokenWindow
example := @contractDecl_canonical_preservesTokensOnSuccess
example := @contractDecl_canonical_cursorMonotoneOnSuccess
example := @contractDecl_canonical_startsAtCurrentTokenOnSuccess
example := @contractDecl_canonical_cursor_lt_onSuccess
end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractDeclarationExactnessProperties
/-! Compile-time consumers for conditional exact contract declarations. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractDeclarationExactnessProperties

open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ContractMemberCoreOrdinaryParses.value_unique_of_exact_children
example := @ContractMemberCoreOrdinaryParses.result_unique_of_exact_children
example := @ContractMemberCoreRejects.output_unique_of_exact_children
example := @contractMemberCoreExactOutcomeSpecOfChildren
example := @contractMemberCoreExactOutcomeSpecOfLeaves
example := @contractMemberCoreExactOutcomeSpecOfTermFuel
example := @ContractMemberTailOrdinaryParses.result_unique_of_member
example := @ContractMemberTailRejects.output_unique_of_member
example := @contractMemberTailExactOutcomeSpecOfMember
example := @contractBodyExactOutcomeSpecOfMember
example := @contractBodyExactOutcomeSpecOfCore
example := @ContractDeclOrdinaryParses.value_unique_of_body
example := @ContractDeclOrdinaryParses.result_unique_of_body
example := @ContractDeclRejects.output_unique_of_body
example := @contractDeclExactOutcomeSpecOfBody
example := @contractDeclExactOutcomeSpecOfCore
example := @contractMemberCoreExactOutcomeSpecOfCoreTerms
example := @contractMemberCoreExactOutcomeSpecOfCoreTermFuel
example := @contractMemberExactOutcomeSpecOfCoreTermFuel
example := @contractBodyExactOutcomeSpecOfCoreTermFuel
example := @contractDeclExactOutcomeSpecOfCoreTermFuel

example := @ContractInternals.contractMemberCore_exactOutcomeSpec_of_leaves
example := @ContractInternals.contractMemberCore_exactOutcomeSpec_of_termFuel
example := @ContractInternals.contractMemberCore_success_result_unique
example := @ContractInternals.contractMemberCore_reject_output_unique
example := @ContractInternals.contractMemberWithAttribute_exactOutcomeSpec_of_core
example := @ContractInternals.contractBody_exactOutcomeSpec_of_member
example := @ContractInternals.contractBody_exactOutcomeSpec_of_core
example := @ContractInternals.contractBody_success_result_unique_of_member
example := @ContractInternals.contractBody_reject_output_unique_of_member
example := @contractDecl_exactOutcomeSpec_of_body
example := @contractDecl_exactOutcomeSpec_of_core
example := @contractDecl_success_result_unique_of_body
example := @contractDecl_reject_output_unique_of_body
example := @ContractInternals.contractMemberCore_exactOutcomeSpec_of_coreTermFuel
example := @ContractInternals.contractMemberWithAttribute_exactOutcomeSpec_of_coreTermFuel
example := @ContractInternals.contractBody_exactOutcomeSpec_of_coreTermFuel
example := @contractDecl_exactOutcomeSpec_of_coreTermFuel

end Solcore.Test.SyntaxParserContractDeclarationExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractDeclarationProperties
namespace Tests
open Solcore.Syntax.Parser
example := @ContractInternals.ContractBodyParserInputs
example := @ContractInternals.ContractDeclParserContract
example := @ContractInternals.contractDecl_contract
example (inputs : ContractInternals.ContractBodyParserInputs) :
    Parser.PreservesTokensOnSuccess contractDecl :=
  (ContractInternals.contractDecl_contract inputs).preservesTokensOnSuccess
end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractDeclarationTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @ContractInternals.productionContractMemberTotalityContract
example := @ContractInternals.productionContractMemberCore_invariantFreeOnValid
example :=
  @ContractInternals.productionContractMemberWithAttribute_invariantFreeOnValid
example := @ContractInternals.productionContractMemberInvariantFreeOnValid
example := @ContractInternals.productionContractBody_ordinary
example := @ContractInternals.contractBody_invariantFreeOnValid
example := @contractDecl_invariantFreeOnValid
example := @contractDecl_ordinary
example := @contractDecl_ne_invariant

end Solcore.Test.SyntaxParserContractDeclarationTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractEntryDeclarationTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractEntryDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @constructorDecl_ordinary
example := @constructorDecl_invariantFreeOnValid
example := @constructorDecl_ne_invariant
example := @fallbackDecl_ordinary
example := @fallbackDecl_invariantFreeOnValid
example := @fallbackDecl_ne_invariant

end Solcore.Test.SyntaxParserContractEntryDeclarationTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractEntryHelperTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractEntryHelperTotalityProperties

open Solcore.Syntax.Parser

example := @ContractEntryInternals.entryParameters_invariantFreeOnValid
example := @ContractEntryInternals.optionalModifier_invariantFreeOnValid
example := @ContractEntryInternals.implicitPublicModifiers_invariantFreeOnValid

end Solcore.Test.SyntaxParserContractEntryHelperTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractFieldExactnessProperties
/-! Compile-time consumers for exact contract-field outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractFieldExactnessProperties

open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalContractFieldInitializerOrdinaryParses.value_unique
example := @OptionalContractFieldInitializerOrdinaryParses.result_unique
example := @OptionalContractFieldInitializerRejects.output_unique
example := @optionalContractFieldInitializerExactOutcomeSpec
example := @ContractFieldOrdinaryParses.value_unique
example := @ContractFieldOrdinaryParses.result_unique
example := @ContractFieldRejects.output_unique
example := @contractFieldExactOutcomeSpec

example := @ContractInternals.optionalFieldInitializer_exactOutcomeSpec
example := @ContractInternals.optionalFieldInitializer_success_result_unique
example := @ContractInternals.optionalFieldInitializer_reject_output_unique
example := @ContractInternals.contractField_exactOutcomeSpec
example := @ContractInternals.contractField_success_result_unique
example := @ContractInternals.contractField_reject_output_unique

end Solcore.Test.SyntaxParserContractFieldExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractFieldTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractFieldTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example (expressionParser : Parser Expr)
    (expressionFree : Parser.InvariantFreeOnValid expressionParser) :
    Parser.InvariantFreeOnValid
      (optionalFieldInitializer expressionParser) :=
  optionalFieldInitializer_invariantFreeOnValid expressionParser expressionFree

example (expressionParser : Parser Expr)
    (expressionFree : Parser.InvariantFreeOnValid expressionParser)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractField expressionParser input ≠ .invariant error :=
  contractField_ne_invariant expressionParser expressionFree input inputValid
    error

end Solcore.Test.SyntaxParserContractFieldTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractMemberCompletenessProperties
/-! External consumers of both directions of contract-internal completeness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractMemberCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example {input : State} (inputValid : input.ValidFor)
    {value : ContractField} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ContractFieldOrdinaryParses
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, contractField expression input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (contractFieldPublic_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : ContractField} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : contractField expression input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ContractFieldOrdinaryParses
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder value remainder :=
  (contractFieldPublic_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ContractFieldRejects
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, contractField expression input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (contractFieldPublic_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : contractField expression input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ContractFieldRejects
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects
      input.declarativeRemainder rejected :=
  (contractFieldPublic_ordinary_reject_iff inputValid).mpr
    ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, contractMemberCore input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (contractMemberCore_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : contractMemberCore input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      input.declarativeRemainder value remainder :=
  (contractMemberCore_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ContractMemberCoreRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, contractMemberCore input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (contractMemberCore_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : contractMemberCore input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ContractMemberCoreRejects
      input.declarativeRemainder rejected :=
  (contractMemberCore_ordinary_reject_iff inputValid).mpr
    ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ContractMemberOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, contractMemberWithAttribute input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (contractMemberWithAttribute_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : contractMemberWithAttribute input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ContractMemberOrdinaryParses
      input.declarativeRemainder value remainder :=
  (contractMemberWithAttribute_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ContractMemberRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, contractMemberWithAttribute input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (contractMemberWithAttribute_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : contractMemberWithAttribute input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ContractMemberRejects
      input.declarativeRemainder rejected :=
  (contractMemberWithAttribute_ordinary_reject_iff inputValid).mpr
    ⟨failure, output, result, remainderEq⟩

end Solcore.Test.SyntaxParserContractMemberCompletenessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractMemberRecoveryCompletenessProperties
/-! External consumers of both directions of contract-internal completeness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractMemberRecoveryCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example {input : State}
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ContractMemberRecoveryParses
      input.declarativeRemainder value remainder) :
    ∃ output, recoverContractMember input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (recoverContractMember_ordinary_success_iff).mp parsed

example {input : State}
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : recoverContractMember input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ContractMemberRecoveryParses
      input.declarativeRemainder value remainder :=
  (recoverContractMember_ordinary_success_iff).mpr ⟨output, result, remainderEq⟩

example {input : State}
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ContractMemberRecoveryRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, recoverContractMember input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (recoverContractMember_ordinary_reject_iff).mp rejection

example {input : State}
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : recoverContractMember input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ContractMemberRecoveryRejects
      input.declarativeRemainder rejected :=
  (recoverContractMember_ordinary_reject_iff).mpr
    ⟨failure, output, result, remainderEq⟩

end Solcore.Test.SyntaxParserContractMemberRecoveryCompletenessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractMemberStrictProperties
/-! External consumers for strict contract-member cursor progress. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractMemberStrictProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example := @contractFieldMember_cursor_lt_onSuccess
example := @contractFunctionMember_cursor_lt_onSuccess
example := @contractConstructorMember_cursor_lt_onSuccess
example := @contractFallbackMember_cursor_lt_onSuccess
example := @contractTypeAliasMember_cursor_lt_onSuccess
example := @contractEnumMember_cursor_lt_onSuccess
example := @contractMemberCore_cursor_lt_onSuccess
example := @contractMemberWithAttribute_cursor_lt_onSuccess

example {input final : State} {member : ContractMember}
    (parsed : contractMemberWithAttribute input = .ok member final) :
    input.cursor < final.cursor :=
  contractMemberWithAttribute_cursor_lt_onSuccess parsed

end Solcore.Test.SyntaxParserContractMemberStrictProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractMemberTotalityProperties
/-! External consumers for conditional contract-member totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractMemberTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example := @mapMember_invariantFreeOnValid
example := @ContractMemberTotalityContract
example := @contractMemberParser_invariantFreeOnValid
example := @contractMemberCore_invariantFreeOnValid
example := @attachContractDerive_invariantFreeOnValid
example := @contractMemberWithAttribute_invariantFreeOnValid
example := @contractMemberWithAttribute_ne_invariant
example := @contractMemberInvariantFree_of_totalityContract
example := @contractBody_ordinary_of_memberTotalityContract
example := @contractBody_ne_invariant_of_memberTotalityContract

example (contract : ContractMemberTotalityContract) :
    ContractMemberInvariantFreeOnValid :=
  contractMemberInvariantFree_of_totalityContract contract

end Solcore.Test.SyntaxParserContractMemberTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractProperties
set_option autoImplicit false

namespace Tests
open Solcore.Syntax.Parser

example := @ContractInternals.contractField_validFor
example := @ContractInternals.contractField_preservesTokenWindow
example := @ContractInternals.contractField_preservesTokensOnSuccess
example := @ContractInternals.contractField_cursorMonotoneOnSuccess
example := @ContractInternals.contractField_startsAtCurrentTokenOnSuccess
example := @ContractInternals.ContractMemberParserContract
example := @ContractInternals.ContractMemberParserContract.preservesTokensOnSuccess
example := @ContractInternals.CanonicalContractMemberContract
example := @ContractInternals.extendContractMemberStart_contract
example := @ContractInternals.attachContractDerive_reply_validFor
example := @ContractInternals.attachContractDerive_preservesTokenWindow
example := @ContractInternals.attachContractDerive_preservesTokensOnSuccess
example := @ContractInternals.attachContractDerive_cursorMonotoneOnSuccess
example := @ContractInternals.attachContractDerive_preservesDeriveStartOnSuccess
example := @ContractInternals.attachContractDerive_spanAlignedOnSuccess
example := @ContractInternals.mapMember_contract
example := @ContractInternals.contractField_canonical_contract
example := @ContractInternals.contractFunction_canonical_contract
example := @ContractInternals.contractConstructor_canonical_contract
example := @ContractInternals.contractFallback_canonical_contract
example := @ContractInternals.contractTypeAlias_canonical_contract
example := @ContractInternals.contractEnum_canonical_contract
example := @ContractInternals.contractMemberParser_canonical_contract
example := @ContractInternals.contractMemberCore_canonical_contract
example := @ContractInternals.contractMemberWithAttribute_canonical_contract
end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractRecoveryProperties
set_option autoImplicit false

namespace Tests
open Solcore.Syntax.Parser

example := @ContractInternals.RecoveredContractMemberValid
example := @ContractInternals.finishRecoveredMember_validFor
example := @ContractInternals.recoverContractMemberAux_validFor
example := @ContractInternals.recoverContractMember_validFor
example := @ContractInternals.finishRecoveredMember_preservesTokenWindow
example := @ContractInternals.recoverContractMemberAux_preservesTokenWindow
example := @ContractInternals.recoverContractMemberAux_preservesTokensOnSuccess
example := @ContractInternals.recoverContractMemberAux_ok_state_shape
example := @ContractInternals.recoverContractMemberAux_cursorMonotoneOnSuccess
example := @ContractInternals.recoverContractMember_preservesTokenWindow
example := @ContractInternals.recoverContractMember_preservesTokensOnSuccess
example := @ContractInternals.recoverContractMember_ok_state_shape
example := @ContractInternals.recoverContractMember_cursor_lt_onSuccess
example := @ContractInternals.recoverContractMember_cursorMonotoneOnSuccess
example := @ContractInternals.recoverContractMember_startsAtCurrentTokenOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractRecoveryTotalityProperties
/-! External consumers for contract-member recovery totality laws. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractRecoveryTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example := @recoverContractMemberAux_ok_of_remainingCount_lt
example := @recoverContractMemberAux_production_ok
example := @recoverContractMember_total
example := @recoverContractMember_ne_invariant
example := @recoverContractMember_reject_of_atEnd
example := @recoverContractMember_ok_of_valid_not_atEnd

example (state : State) (error : ParserInvariantError) :
    recoverContractMember state ≠ .invariant error :=
  recoverContractMember_ne_invariant state error

example (state : State) (atEnd : state.atEnd = true) :
    ∃ failure, recoverContractMember state = .reject failure state :=
  recoverContractMember_reject_of_atEnd state atEnd

example (state : State) (valid : state.ValidFor)
    (notEnd : state.atEnd = false) :
    ∃ member final, recoverContractMember state = .ok member final :=
  recoverContractMember_ok_of_valid_not_atEnd state valid notEnd

end Solcore.Test.SyntaxParserContractRecoveryTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContractSoundnessProperties
/-! External consumers for strict and broad contract-declaration components. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ContractEntryModifiersParses
example := @ContractEntryModifiersOrdinaryParses
example := @OptionalFunctionModifierParses.value_unique
example := @OptionalFunctionModifierParses.result_unique
example := @ContractEntryModifiersOrdinaryParses.value_unique
example := @ContractEntryModifiersOrdinaryParses.result_unique
example := @ConstructorDeclParses
example := @ConstructorDeclOrdinaryParses
example := @ConstructorDeclRejects
example := @constructorDeclDeterministicOutcomeSpec
example := @ConstructorDeclOrdinaryParses.value_unique_of_exact_children
example := @ConstructorDeclOrdinaryParses.result_unique_of_exact_children
example := @ConstructorDeclRejects.output_unique_of_exact_children
example := @constructorDeclExactOutcomeSpecOfChildren
example := @constructorDeclExactOutcomeSpecOfBody
example := @constructorDeclExactOutcomeSpecOfStatementFuel
example := @ConstructorDeclOrdinaryParses.result_unique_of_exact_body
example := @ConstructorDeclRejects.output_unique_of_exact_body
example := @FallbackDeclParses
example := @FallbackParameterValidationOrdinaryParses
example := @FallbackDeclOrdinaryParses
example := @FallbackDeclRejects
example := @fallbackDeclDeterministicOutcomeSpec
example := @OptionalContractFieldInitializerParses
example := @OptionalContractFieldInitializerOrdinaryParses
example := @OptionalContractFieldInitializerRejects
example := @optionalContractFieldInitializerDeterministicOutcomeSpec
example := @ContractFieldParses
example := @ContractFieldOrdinaryParses
example := @ContractFieldRejects
example := @contractFieldDeterministicOutcomeSpec
example := @ContractMemberCoreTokenPresentAt
example := @ContractMemberCoreOrdinaryParses
example := @ContractMemberCoreRejects
example := @contractMemberCoreDeterministicOutcomeSpec
example := @ContractDeriveAttaches
example := @ContractMemberOrdinaryParses
example := @ContractMemberRejects
example := @contractMemberDeterministicOutcomeSpec
example := @ContractMemberOrdinaryParses.value_unique_of_core
example := @ContractMemberOrdinaryParses.result_unique_of_core
example := @ContractMemberRejects.output_unique_of_core
example := @contractMemberExactOutcomeSpecOfCore
example := @ContractMemberRecoveryBoundaryStartsAt
example := @ContractMemberRecoveryStops
example := @ContractMemberRecoveryScanParses
example := @ContractMemberRecoveryParses
example := @ContractMemberRecoveryRejects
example := @contractMemberRecoveryDeterministicOutcomeSpec
example := @ContractMemberRecoveryScanParses.value_unique
example := @ContractMemberRecoveryScanParses.result_unique
example := @ContractMemberRecoveryParses.value_unique
example := @ContractMemberRecoveryParses.result_unique
example := @ContractMemberRecoveryRejects.output_unique
example := @contractMemberRecoveryExactOutcomeSpec
example := @ContractMemberRejectsWithPreservedWindow
example := @ContractMemberTailOrdinaryParses
example := @ContractMemberTailOrdinaryOutcomeParses
example := @ContractMemberTailRejects
example := @contractMemberTailDeterministicOutcomeSpec
example := @ContractBodyOrdinaryParses
example := @ContractBodyOrdinaryOutcomeParses
example := @ContractBodyRejects
example := @contractBodyDeterministicOutcomeSpec
example := @ContractDeclOrdinaryParses
example := @ContractDeclRejects
example := @contractDeclDeterministicOutcomeSpec
example := @ContractMemberCoreParses
example := @ContractMemberParses
example := @ContractMemberTailParses
example := @ContractBodyParses
example := @ContractDeclParses

example := @ContractInternals.contractMemberCore_reflectsDiagnosticFreeOnSuccess
example := @ContractInternals.contractMemberCore_success_sound
example := @ContractInternals.contractMemberCore_success_ordinaryOutcome_sound
example := @ContractInternals.contractMemberCore_reject_ordinaryOutcome_sound
example := @ContractInternals.contractMemberCore_ordinaryOutcome_sound
example := @ContractInternals.contractMemberCore_ordinaryOutcomeSpec
example := @ContractInternals.attachContractDerive_success_ordinaryOutcome_sound
example := @ContractInternals.attachContractDerive_total_success
example := @ContractInternals.contractMemberWithAttribute_success_ordinaryOutcome_sound
example := @ContractInternals.contractMemberWithAttribute_reject_ordinaryOutcome_sound
example := @ContractInternals.contractMemberWithAttribute_ordinaryOutcome_sound
example := @ContractInternals.contractMemberWithAttribute_ordinaryOutcomeSpec
example := @ContractInternals.contractMemberWithAttribute_exactOutcomeSpec_of_core
example := @ContractInternals.contractMemberWithAttribute_success_result_unique_of_core
example := @ContractInternals.contractMemberWithAttribute_reject_output_unique_of_core
example := @ContractInternals.recoveryBoundaryStartsAt_of_atContractRecoveryBoundary_eq_true
example := @ContractInternals.atContractRecoveryBoundary_eq_true_of_recoveryBoundaryStartsAt
example := @ContractInternals.contractMemberRecoveryStops_of_guard_eq_true
example := @ContractInternals.contractMemberRecoveryStops_of_advance?_eq_none
example := @ContractInternals.no_contractMemberRecoveryStops_of_nonBoundary_token
example := @ContractInternals.recoverContractMemberAux_success_ordinaryOutcome_sound
example := @ContractInternals.recoverContractMember_success_ordinaryOutcome_sound
example := @ContractInternals.recoverContractMember_reject_ordinaryOutcome_sound
example := @ContractInternals.recoverContractMember_ordinaryOutcome_sound
example := @ContractInternals.recoverContractMember_ordinaryOutcomeSpec
example := @ContractInternals.recoverContractMember_exactOutcomeSpec
example := @ContractInternals.recoverContractMember_success_result_unique
example := @ContractInternals.recoverContractMember_reject_output_unique
example := @ContractInternals.contractMemberRejectsWithPreservedWindow_of_result
example := @ContractInternals.rewoundContractMember_declarativeRemainder_eq
example := @ContractInternals.cursor_lt_endIndex_of_atEnd_eq_false
example := @ContractInternals.contractMemberRecoveryBoundaryStartsAt_of_guard_eq_true
example := @ContractInternals.no_contractMemberRecoveryBoundaryStartsAt_of_guard_eq_false
example := @ContractInternals.closeContractBody_success_exact
example := @ContractInternals.closeContractBody_success_of_rightBrace_guard
example := @ContractInternals.contractMembers_success_ordinaryOutcome_sound_strong
example := @ContractInternals.contractMembers_reject_ordinaryOutcome_sound
example := @ContractInternals.contractBody_success_ordinaryOutcome_sound
example := @ContractInternals.contractBody_reject_ordinaryOutcome_sound
example := @ContractInternals.contractBody_ordinaryOutcome_sound
example := @ContractInternals.contractBody_ordinaryOutcomeSpec
example := @contractDecl_success_ordinaryOutcome_sound
example := @contractDecl_reject_ordinaryOutcome_sound
example := @contractDecl_ordinaryOutcome_sound
example := @contractDecl_ordinaryOutcomeSpec
example := @ContractInternals.contractMemberWithAttribute_reflectsDiagnosticFreeOnSuccess
example := @ContractInternals.contractMemberWithAttribute_success_sound

example := @ContractEntryInternals.entryParameters_success_ordinaryOutcome_sound
example := @ContractEntryInternals.entryParameters_reject_ordinaryOutcome_sound
example := @ContractEntryInternals.implicitPublicModifiers_success_ordinaryOutcome_sound
example := @ContractEntryInternals.implicitPublicModifiers_ne_reject
example := @constructorDecl_success_ordinaryOutcome_sound
example := @constructorDecl_reject_ordinaryOutcome_sound
example := @constructorDecl_ordinaryOutcome_sound
example := @constructorDecl_ordinaryOutcomeSpec
example := @constructorDecl_exactOutcomeSpec_of_body
example := @constructorDecl_exactOutcomeSpec_of_statementFuel
example := @constructorDecl_success_result_unique_of_body
example := @constructorDecl_reject_output_unique_of_body
example := @constructorDecl_exactOutcomeSpec_of_children
example := @constructorDecl_success_result_unique_of_children
example := @constructorDecl_reject_output_unique_of_children
example := @fallbackDecl_success_ordinaryOutcome_sound
example := @fallbackDecl_reject_ordinaryOutcome_sound
example := @fallbackDecl_ordinaryOutcome_sound
example := @fallbackDecl_ordinaryOutcomeSpec
example := @fallbackDeclExactOutcomeSpecOfBody
example := @fallbackDeclExactOutcomeSpecOfStatementFuel
example := @fallbackDecl_exactOutcomeSpec_of_body
example := @fallbackDecl_exactOutcomeSpec_of_statementFuel
example := @fallbackDecl_success_result_unique_of_body
example := @fallbackDecl_reject_output_unique_of_body
example := @ContractInternals.optionalFieldInitializer_success_ordinaryOutcome_sound
example := @ContractInternals.optionalFieldInitializer_reject_ordinaryOutcome_sound
example := @ContractInternals.optionalFieldInitializer_ordinaryOutcome_sound
example := @ContractInternals.optionalFieldInitializer_ordinaryOutcomeSpec
example := @ContractInternals.contractField_success_ordinaryOutcome_sound
example := @ContractInternals.contractField_reject_ordinaryOutcome_sound
example := @ContractInternals.contractField_ordinaryOutcome_sound
example := @ContractInternals.contractField_ordinaryOutcomeSpec

example := @ContractInternals.contractBody_reflectsDiagnosticFreeOnSuccess
example := @ContractInternals.contractBody_success_sound
example := @ContractInternals.contractBody_success_sound_and_validFor

example := @ContractInternals.contractDecl_reflectsDiagnosticFreeOnSuccess
example := @ContractInternals.contractDecl_success_sound
example := @ContractInternals.contractDecl_success_sound_and_validFor

example
    (expressionParses : Remainder → Expr → Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      Remainder → Block → Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ContractDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractDecl input = .ok declaration next) :
    ContractDeclParses expressionParses allowBodyParses requiredBodyParses
          input.declarativeRemainder declaration next.declarativeRemainder ∧
      ContractDecl.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor input.file
        declaration :=
  ContractInternals.contractDecl_success_sound_and_validFor expressionParses
    allowBodyParses requiredBodyParses expressionReflects expressionSound
    allowBodyReflects allowBodySound requiredBodyReflects requiredBodySound
    inputValid diagnosticFree result

example {input next : State} {declaration : ConstructorDecl}
    (result : constructorDecl input = .ok declaration next) :
    ConstructorDeclOrdinaryParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  constructorDecl_success_ordinaryOutcome_sound result

example {input next : State} {member : ContractMember}
    (result : ContractInternals.contractMemberCore input = .ok member next) :
    ContractMemberCoreOrdinaryParses input.declarativeRemainder member
      next.declarativeRemainder :=
  ContractInternals.contractMemberCore_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : ContractInternals.contractMemberCore input =
      .reject failure rejected) :
    ContractMemberCoreRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  ContractInternals.contractMemberCore_reject_ordinaryOutcome_sound result

example {derive : DeriveAttribute} {coreMember attached : ContractMember}
    {input output : State}
    (result : ContractInternals.attachContractDerive derive coreMember input =
      .ok attached output) :
    ContractDeriveAttaches derive coreMember attached ∧
      output.declarativeRemainder = input.declarativeRemainder :=
  ContractInternals.attachContractDerive_success_ordinaryOutcome_sound result

example {input output : State} {member : ContractMember}
    (result : ContractInternals.contractMemberWithAttribute input = .ok member output) :
    ContractMemberOrdinaryParses input.declarativeRemainder member output.declarativeRemainder :=
  ContractInternals.contractMemberWithAttribute_success_ordinaryOutcome_sound result
example {input rejected : State} {failure : Failure}
    (result : ContractInternals.contractMemberWithAttribute input = .reject failure rejected) :
    ContractMemberRejects input.declarativeRemainder rejected.declarativeRemainder :=
  ContractInternals.contractMemberWithAttribute_reject_ordinaryOutcome_sound result
example {input output : State} {member : ContractMember}
    (result : ContractInternals.recoverContractMember input = .ok member output) :
    ContractMemberRecoveryParses input.declarativeRemainder member output.declarativeRemainder :=
  ContractInternals.recoverContractMember_success_ordinaryOutcome_sound result
example {input rejected : State} {failure : Failure}
    (result : ContractInternals.recoverContractMember input = .reject failure rejected) :
    ContractMemberRecoveryRejects input.declarativeRemainder rejected.declarativeRemainder :=
  ContractInternals.recoverContractMember_reject_ordinaryOutcome_sound result
example {input output : State} {body : ContractInternals.ContractBody}
    (result : ContractInternals.contractBody input = .ok body output) :
    ContractBodyOrdinaryParses input.declarativeRemainder body.span body.members
      output.declarativeRemainder :=
  ContractInternals.contractBody_success_ordinaryOutcome_sound result
example {input rejected : State} {failure : Failure}
    (result : ContractInternals.contractBody input = .reject failure rejected) :
    ContractBodyRejects input.declarativeRemainder rejected.declarativeRemainder :=
  ContractInternals.contractBody_reject_ordinaryOutcome_sound result

example {input output : State} {declaration : ContractDecl}
    (result : contractDecl input = .ok declaration output) :
    ContractDeclOrdinaryParses input.declarativeRemainder declaration
      output.declarativeRemainder :=
  contractDecl_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : contractDecl input = .reject failure rejected) :
    ContractDeclRejects input.declarativeRemainder rejected.declarativeRemainder :=
  contractDecl_reject_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : constructorDecl input = .reject failure rejected) :
    ConstructorDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  constructorDecl_reject_ordinaryOutcome_sound result

example {input next : State} {declaration : FallbackDecl}
    (result : fallbackDecl input = .ok declaration next) :
    FallbackDeclOrdinaryParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  fallbackDecl_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : fallbackDecl input = .reject failure rejected) :
    FallbackDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  fallbackDecl_reject_ordinaryOutcome_sound result

example {input next : State} {initializer : Option Expr}
    (result : ContractInternals.optionalFieldInitializer expression input =
      .ok initializer next) :
    OptionalContractFieldInitializerOrdinaryParses
      CoreExpressionOrdinaryParses input.declarativeRemainder initializer
        next.declarativeRemainder :=
  ContractInternals.optionalFieldInitializer_success_ordinaryOutcome_sound
    expression CoreExpressionOrdinaryParses expression_success_ordinary_sound
      result

example {input rejected : State} {failure : Failure}
    (result : ContractInternals.optionalFieldInitializer expression input =
      .reject failure rejected) :
    OptionalContractFieldInitializerRejects CoreExpressionPublicRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  ContractInternals.optionalFieldInitializer_reject_ordinaryOutcome_sound
    expression CoreExpressionPublicRejects expression_reject_ordinary_sound
      result

example {input next : State} {field : ContractField}
    (result : ContractInternals.contractField expression input =
      .ok field next) :
    ContractFieldOrdinaryParses CoreExpressionOrdinaryParses
      input.declarativeRemainder field next.declarativeRemainder :=
  ContractInternals.contractField_success_ordinaryOutcome_sound expression
    CoreExpressionOrdinaryParses expression_success_ordinary_sound result

example {input rejected : State} {failure : Failure}
    (result : ContractInternals.contractField expression input =
      .reject failure rejected) :
    ContractFieldRejects CoreExpressionOrdinaryParses
      CoreExpressionPublicRejects input.declarativeRemainder
        rejected.declarativeRemainder :=
  ContractInternals.contractField_reject_ordinaryOutcome_sound expression
    CoreExpressionOrdinaryParses CoreExpressionPublicRejects
      expression_success_ordinary_sound expression_reject_ordinary_sound result

end Solcore.Test.SyntaxParserContractSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserContracts
/-! Executable canonical contract declaration and entry-point regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def contractSource : SourceId := {
  origin := .main
  path := "parser-contracts.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := contractSource, content }
  match Parser.parse file with
  | .error error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual output.lexicalDiagnostics [] s!"{label} lexical diagnostics"
      unless output.parsed.items.all (fun item => item.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid item span")
      unless output.parseDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid diagnostic span")
      pure output

private def qualifiedText (name : QualifiedName) : String :=
  String.intercalate "."
    (name.value.components.toList.map (fun item => item.value))

private def typeName? (type : TypeExpr) : Option String :=
  match type.value with
  | .named name none => some (qualifiedText name)
  | _ => none

private def genericNames (parameters : GenericParameters) : List String :=
  parameters.elements.toList.map (fun name => name.value)

private def parameterNames
    (parameters : DelimitedList FunctionParameter) : List String :=
  parameters.elements.filterMap fun parameter => match parameter.value with
    | .typed _ name _ => some name.value
    | .error => none

private def tailName? (body : Block) : Option String :=
  match body.value with
  | [{ value := .expression expression false, .. }] =>
      match expression.value with
      | .identifier name => some name.value
      | _ => none
  | _ => none

private def testDeriveContractFieldBoundary : IO Unit := do
  let output ← checkedParse "derive contract-field boundary"
    "contract C { #[derive(Eq)\nvalue: word; }"
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
    (byteRange diagnostic.span, diagnostic.kind)) [
      ((13, 25), .constraintViolation .unclosedDeriveAttribute),
      ((13, 25), .constraintViolation .deriveOnlyEnum)
    ] "contract-field boundary diagnostics"
  match output.parsed.items with
  | [{ value := .contract declaration, .. }] =>
      match declaration.value.members with
      | [{ span := memberSpan, value := .field field, .. }] =>
          assertEqual (byteRange memberSpan) (13, 38)
            "derived field member span"
          assertEqual (byteRange field.span) (13, 38)
            "derived field declaration span"
          assertEqual field.value.name.value "value"
            "field after unclosed derive"
      | members => throw (IO.userError
          s!"derive field boundary changed: {reprStr members}")
  | items => throw (IO.userError
      s!"derive field contract changed: {reprStr items}")

private def testMalformedFieldRecovery : IO Unit := do
  let output ← checkedParse "malformed contract field"
    "contract C { broken: ; function good() {} } function after() {}"
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
    (byteRange diagnostic.span, diagnostic.kind)) [
      ((13, 22), .recovered .contractMember)
    ] "malformed field diagnostics"
  match output.parsed.items with
  | [
      { span := contractSpan, value := .contract declaration, .. },
      { span := afterSpan, value := .function after, .. }
    ] =>
      assertEqual (byteRange contractSpan) (0, 43)
        "recovered contract span"
      assertEqual (byteRange afterSpan) (44, 63)
        "top item after recovered contract"
      assertEqual after.value.signature.name.value "after"
        "function after recovered contract"
      match declaration.value.members with
      | [errorMember, goodMember] =>
          assertEqual (byteRange errorMember.span) (13, 22)
            "malformed field recovery span"
          assertEqual errorMember.value .error
            "malformed field recovery node"
          match goodMember.value with
          | .function good =>
              assertEqual good.value.signature.name.value "good"
                "member after malformed field"
          | value => throw (IO.userError
              s!"member after malformed field changed: {reprStr value}")
      | members => throw (IO.userError
          s!"malformed field members changed: {reprStr members}")
  | items => throw (IO.userError
      s!"malformed field items changed: {reprStr items}")

private def testContractDeclaration : IO Unit := do
  let source := String.intercalate "\n" [
    "contract Vault<t,> {",
    "  balance: word = 0;",
    "  function get() public returns (word) { balance }",
    "  constructor(seed: word,) public payable { balance = seed; }",
    "  fallback(arg: word) public payable { return; }",
    "  type Local = word;",
    "  #[derive(Eq)] enum Flag { Off, On(word), }",
    "}"
  ]
  let output ← checkedParse "contract declaration" source
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
    (byteRange diagnostic.span, diagnostic.kind)) [
      ((120, 126), .constraintViolation
        (.implicitPublicModifier .constructorKw)),
      ((165, 176), .constraintViolation .fallbackRequiresNoParameters),
      ((177, 183), .constraintViolation
        (.implicitPublicModifier .fallbackKw))
    ] "contract entry diagnostics"
  match output.parsed.items with
  | [{ value := .contract declaration, .. }] =>
      assertEqual (byteRange declaration.span) (0, 271) "contract span"
      assertEqual declaration.value.name.value "Vault" "contract name"
      assertEqual (declaration.value.genericParameters.map genericNames)
        (some ["t"]) "contract generic parameters"
      assertEqual (byteRange declaration.value.bodySpan) (19, 271)
        "contract body span"
      match declaration.value.members with
      | [field, function, constructor, fallback, alias, enum] =>
          assertEqual [byteRange field.span, byteRange function.span,
              byteRange constructor.span, byteRange fallback.span,
              byteRange alias.span, byteRange enum.span]
            [(23, 41), (44, 92), (95, 154), (157, 203),
              (206, 224), (227, 269)] "contract member order and spans"
          match field.value with
          | .field declaration =>
              assertEqual declaration.value.name.value "balance" "field name"
              assertEqual (typeName? declaration.value.type) (some "word")
                "field type"
              match declaration.value.initializer with
              | some { value := .literal { value := .decimal "0", .. }, .. } =>
                  pure ()
              | initializer => throw (IO.userError
                  s!"field initializer changed: {reprStr initializer}")
          | value => throw (IO.userError s!"field member changed: {reprStr value}")
          match function.value with
          | .function declaration =>
              assertEqual declaration.value.signature.name.value "get"
                "contract function name"
              assertEqual (declaration.value.signature.modifiers.publicMarker.map
                byteRange) (some (59, 65)) "contract public marker"
              assertEqual (tailName? declaration.value.body) (some "balance")
                "contract function tail"
          | value => throw (IO.userError
              s!"function member changed: {reprStr value}")
          match constructor.value with
          | .constructor declaration =>
              assertEqual (parameterNames declaration.value.parameters) ["seed"]
                "constructor parameters"
              assertEqual (declaration.value.payableMarker.map byteRange)
                (some (127, 134)) "constructor payable marker"
          | value => throw (IO.userError
              s!"constructor member changed: {reprStr value}")
          match fallback.value with
          | .fallback declaration =>
              assertEqual (parameterNames declaration.value.parameters) ["arg"]
                "invalid fallback parameter retained"
              assertEqual (declaration.value.payableMarker.map byteRange)
                (some (184, 191)) "fallback payable marker"
          | value => throw (IO.userError
              s!"fallback member changed: {reprStr value}")
          match alias.value with
          | .typeAlias declaration =>
              assertEqual declaration.value.name.value "Local"
                "contract type alias"
          | value => throw (IO.userError s!"alias member changed: {reprStr value}")
          match enum.value with
          | .enum declaration =>
              assertEqual declaration.value.name.value "Flag" "contract enum name"
              assertEqual (declaration.value.deriveAttribute.map fun derive =>
                derive.value.targets.elements.map qualifiedText)
                (some ["Eq"]) "contract enum derive"
              assertEqual (declaration.value.constructors.map fun constructor =>
                constructor.value.name.value) ["Off", "On"]
                "contract enum constructors"
          | value => throw (IO.userError s!"enum member changed: {reprStr value}")
      | members => throw (IO.userError
          s!"contract members changed: {reprStr members}")
  | items => throw (IO.userError s!"contract item changed: {reprStr items}")

/-- Run canonical contract declaration and entry-point parser regressions. -/
def testSyntaxParserContracts : IO Unit := do
  testDeriveContractFieldBoundary
  testMalformedFieldRecovery
  testContractDeclaration

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDeclarationCanonicalProperties
/-! External consumers for canonical body-bearing declaration validity. -/

namespace Tests

open Solcore.Syntax.Parser

example := @functionDecl_canonical_validFor
example := @constructorDecl_canonical_validFor
example := @fallbackDecl_canonical_validFor
example := @implDecl_canonical_validFor

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDeclarationCompletenessProperties
/-! Compile-time consumers of declaration grammar completeness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeclarationCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @functionDecl_ordinary_success_iff
example := @functionDecl_ordinary_reject_iff
example := @constructorDecl_ordinary_success_iff
example := @constructorDecl_ordinary_reject_iff
example := @fallbackDecl_ordinary_success_iff
example := @fallbackDecl_ordinary_reject_iff
example := @implDecl_ordinary_success_iff
example := @implDecl_ordinary_reject_iff
example := @contractDecl_ordinary_success_iff
example := @contractDecl_ordinary_reject_iff

example (location : FunctionLocation)
    {input : State} (inputValid : input.ValidFor)
    {value : FunctionDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.FunctionDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, functionDecl location input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (functionDecl_ordinary_success_iff location inputValid).mp parsed

example (location : FunctionLocation)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.FunctionDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, functionDecl location input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (functionDecl_ordinary_reject_iff location inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : ConstructorDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ConstructorDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, constructorDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (constructorDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ConstructorDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, constructorDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (constructorDecl_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : FallbackDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.FallbackDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, fallbackDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (fallbackDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.FallbackDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, fallbackDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (fallbackDecl_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : ImplDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ImplDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, implDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (implDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ImplDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, implDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (implDecl_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : ContractDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ContractDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, contractDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (contractDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ContractDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, contractDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (contractDecl_ordinary_reject_iff inputValid).mp rejection

end Solcore.Test.SyntaxParserDeclarationCompletenessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDeriveAttributeProperties
/-! External compile consumers for canonical derive-attribute contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DeriveAttribute.ValidFor

example (file : SourceFile) (value : DeriveAttribute)
    (valid : DeriveAttribute.ValidFor file value) :
    value.span.ValidFor file ∧
      value.value.targets.ValidFor QualifiedName.ValidFor file :=
  valid

example : deriveAttribute.ValidFor DeriveAttribute.ValidFor :=
  deriveAttribute_validFor

example : Parser.PreservesTokenWindow deriveAttribute :=
  deriveAttribute_preservesTokenWindow

example : Parser.PreservesTokensOnSuccess deriveAttribute :=
  deriveAttribute_preservesTokensOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess deriveAttribute (·.span) :=
  deriveAttribute_startsAtCurrentTokenOnSuccess

example {input next : State} {value : DeriveAttribute}
    (parsed : deriveAttribute input = .ok value next) :
    input.cursor < next.cursor :=
  deriveAttribute_cursor_lt_onSuccess parsed

example : Parser.CursorMonotoneOnSuccess deriveAttribute :=
  deriveAttribute_cursorMonotoneOnSuccess

example :
    deriveAttribute.ValidFor DeriveAttribute.ValidFor ∧
      Parser.PreservesTokenWindow deriveAttribute ∧
      Parser.PreservesTokensOnSuccess deriveAttribute ∧
      Parser.CursorMonotoneOnSuccess deriveAttribute ∧
      Parser.StartsAtCurrentTokenOnSuccess deriveAttribute (·.span) :=
  ⟨deriveAttribute_validFor, deriveAttribute_preservesTokenWindow,
    deriveAttribute_preservesTokensOnSuccess,
    deriveAttribute_cursorMonotoneOnSuccess,
    deriveAttribute_startsAtCurrentTokenOnSuccess⟩

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDeriveAttributeSoundnessProperties
/-! External consumers for derive-attribute grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveAttributeSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @DeriveAttributeParses
example := @DeriveAttributeValidRejects
example := @deriveAttributeValidDeterministicOutcomeSpec
example := @DeriveAttributeRecoveryDeclarationStartsAt
example := @DeriveAttributeRecoveryStops
example := @DeriveAttributeRecoveryTailParses
example := @DeriveAttributeRecoveredParses
example := @DeriveAttributeRecoveredRejects
example := @deriveAttributeRecoveredDeterministicOutcomeSpec
example := @DeriveAttributeOrdinaryParses
example := @DeriveAttributeRejects
example := @deriveAttributeDeterministicOutcomeSpec
example := @DeriveAttributeParses.value_unique
example := @DeriveAttributeParses.result_unique
example := @DeriveAttributeValidRejects.output_unique
example := @deriveAttributeValidExactOutcomeSpec
example := @DeriveAttributeRecoveryTailParses.value_unique
example := @DeriveAttributeRecoveryTailParses.result_unique
example := @DeriveAttributeRecoveredParses.value_unique
example := @DeriveAttributeRecoveredParses.result_unique
example := @DeriveAttributeRecoveredRejects.output_unique
example := @deriveAttributeRecoveredExactOutcomeSpec
example := @DeriveAttributeOrdinaryParses.value_unique
example := @DeriveAttributeOrdinaryParses.result_unique
example := @DeriveAttributeRejects.output_unique
example := @deriveAttributeExactOutcomeSpec
example := @deriveAttributeValid_success_sound
example := @DeriveAttributeInternals.valid_reject_ordinaryOutcome_sound
example := @deriveAttributeValid_success_ordinaryOutcome_sound
example := @deriveAttributeValid_reject_ordinaryOutcome_sound
example := @deriveAttributeValid_ordinaryOutcome_sound
example := @deriveAttributeValid_ordinaryOutcomeSpec
example := @deriveAttributeValid_exactOutcomeSpec
example := @deriveAttributeValid_success_result_unique
example := @deriveAttributeValid_reject_output_unique
example :=
  @DeriveAttributeInternals.recoveryDeclarationStartsAt_of_atDeriveDeclarationBoundary_eq_true
example :=
  @DeriveAttributeInternals.atDeriveDeclarationBoundary_eq_true_of_recoveryDeclarationStartsAt
example := @DeriveAttributeInternals.recoveryStops_of_unclosedGuard_eq_true
example := @DeriveAttributeInternals.recoveryStops_of_advance?_eq_none
example := @DeriveAttributeInternals.no_recoveryStops_of_nonBoundary_token
example := @DeriveAttributeInternals.recoverTail_success_ordinaryOutcome_sound
example :=
  @DeriveAttributeInternals.recoverTail_production_success_ordinaryOutcome_sound
example := @deriveAttributeRecovered_success_ordinaryOutcome_sound
example := @deriveAttributeRecovered_reject_ordinaryOutcome_sound
example := @deriveAttributeRecovered_ordinaryOutcome_sound
example := @deriveAttributeRecovered_ordinaryOutcomeSpec
example := @deriveAttributeRecovered_exactOutcomeSpec
example := @deriveAttributeRecovered_success_result_unique
example := @deriveAttributeRecovered_reject_output_unique
example := @deriveAttribute_success_ordinaryOutcome_sound
example := @deriveAttribute_reject_ordinaryOutcome_sound
example := @deriveAttribute_ordinaryOutcome_sound
example := @deriveAttribute_ordinaryOutcomeSpec
example := @deriveAttribute_exactOutcomeSpec
example := @deriveAttribute_success_result_unique
example := @deriveAttribute_reject_output_unique
example := @deriveAttribute_success_sound
example := @deriveAttribute_success_sound_and_validFor

example {input next : State} {value : DeriveAttribute}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : deriveAttribute input = .ok value next) :
    DeriveAttributeParses input.declarativeRemainder value
      next.declarativeRemainder :=
  deriveAttribute_success_sound diagnosticFree result

example {input next : State} {value : DeriveAttribute}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (result : deriveAttribute input = .ok value next) :
    DeriveAttributeParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      value.ValidFor input.file :=
  deriveAttribute_success_sound_and_validFor inputValid diagnosticFree result

example {input rejected : State} {failure : Failure}
    (result : DeriveAttributeInternals.valid input =
      .reject failure rejected) :
    DeriveAttributeValidRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  deriveAttributeValid_reject_ordinaryOutcome_sound result

example {input next : State} {value : DeriveAttribute}
    (result : DeriveAttributeInternals.recovered input = .ok value next) :
    DeriveAttributeRecoveredParses input.declarativeRemainder value
      next.declarativeRemainder :=
  deriveAttributeRecovered_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : DeriveAttributeInternals.recovered input =
      .reject failure rejected) :
    DeriveAttributeRecoveredRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  deriveAttributeRecovered_reject_ordinaryOutcome_sound result

example {input next : State} {value : DeriveAttribute}
    (result : deriveAttribute input = .ok value next) :
    DeriveAttributeOrdinaryParses input.declarativeRemainder value
      next.declarativeRemainder :=
  deriveAttribute_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : deriveAttribute input = .reject failure rejected) :
    DeriveAttributeRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  deriveAttribute_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserDeriveAttributeSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDeriveAttributeTotalityProperties
/-! External consumers for canonical derive-attribute totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveAttributeTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DeriveAttributeInternals.valid_ordinary
example := @DeriveAttributeInternals.valid_ne_invariant
example := @deriveAttribute_ordinary
example := @deriveAttribute_ne_invariant
example := @deriveAttribute_elementTotalityContract

example : ElementTotalityContract deriveAttribute :=
  deriveAttribute_elementTotalityContract

example (input : State) (valid : input.ValidFor)
    (error : ParserInvariantError) :
    deriveAttribute input ≠ .invariant error :=
  deriveAttribute_ne_invariant input valid error

end Solcore.Test.SyntaxParserDeriveAttributeTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDeriveCompletenessProperties
/-! External consumers of both directions of exact ordinary completeness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example {input : State}
    {value : DeriveTarget} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.DeriveTargetParses
      input.declarativeRemainder value remainder) :
    ∃ output, deriveTarget input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (deriveTarget_ordinary_success_iff).mp parsed

example {input : State}
    {value : DeriveTarget} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : deriveTarget input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.DeriveTargetParses
      input.declarativeRemainder value remainder :=
  (deriveTarget_ordinary_success_iff).mpr ⟨output, result, remainderEq⟩

example {input : State}
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.DeriveTargetRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, deriveTarget input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (deriveTarget_ordinary_reject_iff).mp rejection

example {input : State}
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : deriveTarget input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.DeriveTargetRejects input.declarativeRemainder rejected :=
  (deriveTarget_ordinary_reject_iff).mpr ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.DeriveAttributeParses
      input.declarativeRemainder value remainder) :
    ∃ output, DeriveAttributeInternals.valid input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (deriveAttributeValid_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : DeriveAttributeInternals.valid input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.DeriveAttributeParses
      input.declarativeRemainder value remainder :=
  (deriveAttributeValid_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.DeriveAttributeValidRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, DeriveAttributeInternals.valid input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (deriveAttributeValid_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : DeriveAttributeInternals.valid input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.DeriveAttributeValidRejects input.declarativeRemainder rejected :=
  (deriveAttributeValid_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example {input : State}
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.DeriveAttributeRecoveredParses
      input.declarativeRemainder value remainder) :
    ∃ output, DeriveAttributeInternals.recovered input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (deriveAttributeRecovered_ordinary_success_iff).mp parsed

example {input : State}
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : DeriveAttributeInternals.recovered input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.DeriveAttributeRecoveredParses
      input.declarativeRemainder value remainder :=
  (deriveAttributeRecovered_ordinary_success_iff).mpr ⟨output, result, remainderEq⟩

example {input : State}
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.DeriveAttributeRecoveredRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, DeriveAttributeInternals.recovered input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (deriveAttributeRecovered_ordinary_reject_iff).mp rejection

example {input : State}
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : DeriveAttributeInternals.recovered input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.DeriveAttributeRecoveredRejects input.declarativeRemainder rejected :=
  (deriveAttributeRecovered_ordinary_reject_iff).mpr ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.DeriveAttributeOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, deriveAttribute input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (deriveAttribute_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : deriveAttribute input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.DeriveAttributeOrdinaryParses
      input.declarativeRemainder value remainder :=
  (deriveAttribute_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.DeriveAttributeRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, deriveAttribute input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (deriveAttribute_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : deriveAttribute input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.DeriveAttributeRejects input.declarativeRemainder rejected :=
  (deriveAttribute_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

end Solcore.Test.SyntaxParserDeriveCompletenessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDeriveRecoveryTotalityProperties
/-! External consumers for derive recovery totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @DeriveAttributeInternals.startsDeriveContractField
example := @DeriveAttributeInternals.atDeriveDeclarationBoundary
example :=
  @DeriveAttributeInternals.recoverTail_ordinary_of_remainingCount_lt
example :=
  @DeriveAttributeInternals.recoverTail_ne_invariant_of_remainingCount_lt
example := @DeriveAttributeInternals.recoverTail_production_ordinary
example := @DeriveAttributeInternals.recovered_ordinary
example := @DeriveAttributeInternals.recovered_ne_invariant

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDeriveTargetInternals
/-! External compile consumers for proof-visible derive-target internals. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveTargetInternals

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.DeriveTargetInternals

example : reservedDeriveKeyword? (.keyword .contractKw) =
    some .contractKw := rfl

example : reservedDeriveKeyword? (.keyword .returnKw) = none := rfl

example : reservedDeriveKeyword? (.identifier "Trait") = none := rfl

example : Parser Identifier := deriveComponent

example (first last : Identifier) (tailRev : List Identifier) :
    Parser DeriveTarget := finishDeriveTarget first last tailRev

example (first : Identifier) :
    Nat → Identifier → List Identifier → State → Reply DeriveTarget :=
  deriveTargetTail first

example (first last : Identifier) (tailRev : List Identifier)
    (state : State) :
    finishDeriveTarget first last tailRev state = .ok {
      span := SourceSpan.cover first.span last.span
      value := {
        components := {
          head := first
          tail := tailRev.reverse
        }
      }
    } state := rfl

end Solcore.Test.SyntaxParserDeriveTargetInternals
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDeriveTargetProperties
/-! External compile consumers for canonical derive-target contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example : deriveTarget.ValidFor QualifiedName.ValidFor :=
  deriveTarget_validFor

example : Parser.PreservesTokenWindow deriveTarget :=
  deriveTarget_preservesTokenWindow

example : Parser.PreservesTokensOnSuccess deriveTarget :=
  deriveTarget_preservesTokensOnSuccess

example : Parser.CursorMonotoneOnSuccess deriveTarget :=
  deriveTarget_cursorMonotoneOnSuccess

example {input next : State} {target : DeriveTarget}
    (parsed : deriveTarget input = .ok target next) :
    ∃ firstToken, input.peek? = some firstToken ∧
      firstToken.span.startByte = target.span.startByte ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor :=
  deriveTarget_ok_state_shape parsed

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDeriveTargetSoundnessProperties
/-! External consumers for derive-target grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveTargetSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ReservedDeriveTargetKeyword
example := @DeriveComponentParses
example := @DeriveTargetTailParses
example := @DeriveTargetParses
example := @ExactDeterministicOutcomeSpec
example := @ExactDeterministicOutcomeSpec.successResultUnique
example := @TokenAt.token_unique
example := @ExactTokenParses.result_unique
example := @IdentifierParses.result_unique
example := @IdentifierRejects.output_unique
example := @identifierExactOutcomeSpec
example := @DeriveReservedComponentAbsentAt
example := @DeriveComponentRejects
example := @deriveComponentDeterministicOutcomeSpec
example := @DeriveComponentParses.result_unique
example := @DeriveComponentRejects.output_unique
example := @deriveComponentExactOutcomeSpec
example := @DeriveTargetTailRejects
example := @deriveTargetTailDeterministicOutcomeSpec
example := @DeriveTargetTailParses.result_unique
example := @DeriveTargetTailRejects.output_unique
example := @deriveTargetTailExactOutcomeSpec
example := @DeriveTargetRejects
example := @deriveTargetDeterministicOutcomeSpec
example := @DeriveTargetParses.result_unique
example := @DeriveTargetRejects.output_unique
example := @deriveTargetExactOutcomeSpec
example := @deriveComponent_success_sound
example := @deriveComponent_reject_ordinaryOutcome_sound
example :=
  @DeriveTargetInternals.deriveTargetTail_production_reject_ordinaryOutcome_sound
example := @deriveTarget_success_sound
example := @deriveTarget_success_sound_and_validFor
example := @deriveTarget_success_ordinaryOutcome_sound
example := @deriveTarget_reject_ordinaryOutcome_sound
example := @deriveTarget_ordinaryOutcome_sound
example := @deriveTarget_ordinaryOutcomeSpec
example := @deriveTarget_exactOutcomeSpec
example := @deriveTarget_success_result_unique
example := @deriveTarget_reject_output_unique

example {input next : State} {target : DeriveTarget}
    (result : deriveTarget input = .ok target next) :
    DeriveTargetParses input.declarativeRemainder target
      next.declarativeRemainder :=
  deriveTarget_success_sound result

example {input next : State} {target : DeriveTarget}
    (inputValid : input.ValidFor)
    (result : deriveTarget input = .ok target next) :
    DeriveTargetParses input.declarativeRemainder target
        next.declarativeRemainder ∧
      target.ValidFor input.file :=
  deriveTarget_success_sound_and_validFor inputValid result

example {input rejected : State} {failure : Failure}
    (result : deriveTarget input = .reject failure rejected) :
    DeriveTargetRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  deriveTarget_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserDeriveTargetSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDeriveTargetTotalityProperties
/-! External consumers for canonical derive-target totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveTargetTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.DeriveTargetInternals

example := @deriveComponent_ordinary
example := @deriveComponent_ne_invariant
example := @deriveComponent_ok_cursor_window
example := @deriveTargetTail_ordinary_of_remainingCount_lt
example := @deriveTargetTail_production_ordinary
example := @deriveTargetTail_ne_invariant_of_remainingCount_lt
example := @deriveTarget_ordinary
example := @deriveTarget_ne_invariant
example := @deriveTarget_elementTotalityContract

example : ElementTotalityContract deriveTarget :=
  deriveTarget_elementTotalityContract

example (state : State) (error : ParserInvariantError) :
    deriveTarget state ≠ .invariant error :=
  deriveTarget_ne_invariant state error

end Solcore.Test.SyntaxParserDeriveTargetTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserEnumBodyTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserEnumBodyTotalityProperties

open Solcore.Syntax.Parser

example := @EnumInternals.enumConstructors_ordinary
example := @EnumInternals.enumConstructors_ne_invariant
example := @EnumInternals.enumBody_ordinary
example := @EnumInternals.enumBody_invariantFreeOnValid
example := @EnumInternals.enumBody_ne_invariant

end Solcore.Test.SyntaxParserEnumBodyTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserEnumDeclarationTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserEnumDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @enumDecl_ordinary
example := @enumDecl_invariantFreeOnValid
example := @enumDecl_ne_invariant

end Solcore.Test.SyntaxParserEnumDeclarationTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserEnumElementTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserEnumElementTotalityProperties

open Solcore.Syntax.Parser

example := @EnumInternals.enumConstructorFields_ordinary
example := @EnumInternals.enumConstructorFields_invariantFreeOnValid
example := @EnumInternals.enumConstructor_ordinary
example := @EnumInternals.enumConstructor_invariantFreeOnValid
example := @EnumInternals.enumConstructor_cursor_lt_onSuccess
example := @EnumInternals.enumConstructor_elementTotalityContract

end Solcore.Test.SyntaxParserEnumElementTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserEnumSoundnessProperties
/-! External consumers for algebraic-enum grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserEnumSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalEnumConstructorFieldsParses
example := @EnumConstructorParses
example := @EnumBodyParses
example := @EnumDeclParses
example := @OptionalEnumConstructorFieldsOrdinaryParses
example := @OptionalEnumConstructorFieldsRejects
example := @optionalEnumConstructorFieldsDeterministicOutcomeSpec
example := @EnumConstructorOrdinaryParses
example := @EnumConstructorRejects
example := @enumConstructorDeterministicOutcomeSpec
example := @EnumBodyOrdinaryParses
example := @EnumBodyOrdinaryOutcomeParses
example := @EnumBodyRejects
example := @enumBodyDeterministicOutcomeSpec
example := @EnumDeclOrdinaryParses
example := @EnumDeclRejects
example := @enumDeclDeterministicOutcomeSpec
example := @enumConstructorFieldListExactOutcomeSpec
example := @optionalEnumConstructorFieldsExactOutcomeSpec
example := @enumConstructorExactOutcomeSpec
example := @enumBodyExactOutcomeSpec
example := @enumDeclExactOutcomeSpec
example := @EnumInternals.enumConstructorFields_success_sound
example := @EnumInternals.enumConstructor_success_sound
example := @EnumInternals.enumBody_success_sound
example := @enumDecl_success_sound
example := @enumDecl_success_sound_and_validFor
example := @enumDecl_none_success_sound_and_validFor
example := @EnumInternals.enumConstructorFields_success_ordinaryOutcome_sound
example := @EnumInternals.enumConstructorFields_reject_ordinaryOutcome_sound
example := @EnumInternals.enumConstructorFields_ordinaryOutcome_sound
example := @EnumInternals.enumConstructorFields_ordinaryOutcomeSpec
example := @EnumInternals.enumConstructor_success_ordinaryOutcome_sound
example := @EnumInternals.enumConstructor_reject_ordinaryOutcome_sound
example := @EnumInternals.enumConstructor_ordinaryOutcome_sound
example := @EnumInternals.enumConstructor_ordinaryOutcomeSpec
example := @EnumInternals.enumBody_success_ordinaryOutcome_sound
example := @EnumInternals.enumBody_reject_ordinaryOutcome_sound
example := @EnumInternals.enumBody_ordinaryOutcome_sound
example := @EnumInternals.enumBody_ordinaryOutcomeSpec
example := @enumDecl_success_ordinaryOutcome_sound
example := @enumDecl_reject_ordinaryOutcome_sound
example := @enumDecl_ordinaryOutcome_sound
example := @enumDecl_ordinaryOutcomeSpec
example := @EnumInternals.enumConstructorFields_exactOutcomeSpec
example := @EnumInternals.enumConstructorFields_success_result_unique
example := @EnumInternals.enumConstructorFields_reject_output_unique
example := @EnumInternals.enumConstructor_exactOutcomeSpec
example := @EnumInternals.enumConstructor_success_result_unique
example := @EnumInternals.enumConstructor_reject_output_unique
example := @EnumInternals.enumBody_exactOutcomeSpec
example := @EnumInternals.enumBody_success_result_unique
example := @EnumInternals.enumBody_reject_output_unique
example := @enumDecl_exactOutcomeSpec
example := @enumDecl_success_result_unique
example := @enumDecl_reject_output_unique

example {input next : State} {declaration : EnumDecl}
    (result : enumDecl none input = .ok declaration next) :
    EnumDeclParses none input.declarativeRemainder declaration
      next.declarativeRemainder :=
  enumDecl_success_sound none result

example {input next : State} {declaration : EnumDecl}
    (inputValid : input.ValidFor)
    (result : enumDecl none input = .ok declaration next) :
    EnumDeclParses none input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  enumDecl_none_success_sound_and_validFor inputValid result

example {input rejected : State} {failure : Failure}
    (result : enumDecl none input = .reject failure rejected) :
    EnumDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  enumDecl_reject_ordinaryOutcome_sound none result

example (deriveAttribute : Option DeriveAttribute)
    {input leftOutput rightOutput : State} {left right : EnumDecl}
    (leftResult : enumDecl deriveAttribute input = .ok left leftOutput)
    (rightResult : enumDecl deriveAttribute input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  enumDecl_success_result_unique deriveAttribute leftResult rightResult

example (deriveAttribute : Option DeriveAttribute)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : enumDecl deriveAttribute input = .reject leftFailure leftOutput)
    (rightResult : enumDecl deriveAttribute input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  enumDecl_reject_output_unique deriveAttribute leftResult rightResult

end Solcore.Test.SyntaxParserEnumSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserEnumTraitImpl
/-! Executable canonical enum, derive, trait, and impl regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def declarationSource : SourceId := {
  origin := .main
  path := "parser-enum-trait-impl.sol"
}

private def checkedParse_variant (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := declarationSource, content }
  match Parser.parse file with
  | .error error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual output.lexicalDiagnostics [] s!"{label} lexical diagnostics"
      unless output.parsed.items.all (fun item => item.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid item span")
      unless output.parseDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid diagnostic span")
      pure output

private def enumFieldNames
    (fields : Option (DelimitedList TypeExpr)) : Option (List String) :=
  fields.map fun values => values.elements.map fun type =>
    (typeName? type).getD "<non-name>"

private def testEnumAndDerive : IO Unit := do
  let source :=
    "#[derive(pkg.Eq, Ord)] enum Option<a,> { None, Some(a), Pair(a, word), }"
  let output ← checkedParse_variant "enum and derive" source
  assertEqual output.parseDiagnostics [] "enum diagnostics"
  match output.parsed.items with
  | [{ span := itemSpan, value := .enum declaration, .. }] =>
      assertEqual (byteRange itemSpan) (0, 72) "derived enum item span"
      assertEqual declaration.value.name.value "Option" "enum name"
      assertEqual (declaration.value.parameters.map genericNames)
        (some ["a"]) "enum generic trailing comma"
      assertEqual (declaration.value.parameters.map
        (fun values => byteRange values.span)) (some (34, 38))
        "enum generic span"
      assertEqual (byteRange declaration.value.bodySpan) (39, 72)
        "enum body span"
      match declaration.value.deriveAttribute with
      | some derive =>
          assertEqual (byteRange derive.span) (0, 22) "derive attribute span"
          assertEqual (derive.value.targets.elements.map qualifiedText)
            ["pkg.Eq", "Ord"] "derive target paths"
      | none => throw (IO.userError "enum derive attribute was lost")
      match declaration.value.constructors with
      | [nullaryCtor, unaryCtor, pairCtor] =>
          assertEqual (nullaryCtor.value.name.value,
              enumFieldNames nullaryCtor.value.fields)
            ("None", none) "nullary enum constructor"
          assertEqual (unaryCtor.value.name.value,
              enumFieldNames unaryCtor.value.fields)
            ("Some", some ["a"]) "unary enum constructor"
          assertEqual (pairCtor.value.name.value,
              enumFieldNames pairCtor.value.fields)
            ("Pair", some ["a", "word"]) "product enum constructor"
          assertEqual [byteRange nullaryCtor.span, byteRange unaryCtor.span,
              byteRange pairCtor.span]
            [(41, 45), (47, 54), (56, 69)] "constructor spans"
      | constructors => throw (IO.userError
          s!"enum constructors changed: {reprStr constructors}")
  | items => throw (IO.userError s!"enum item changed: {reprStr items}")

private def testDeriveDiagnostics : IO Unit := do
  let empty ← checkedParse_variant "empty derive" "#[derive()] enum Empty {}"
  match empty.parsed.items, empty.parseDiagnostics with
  | [{ value := .enum declaration, .. }],
      [{ span, kind := .constraintViolation .deriveRequiresTarget }] =>
      assertEqual (byteRange span) (0, 11) "empty derive diagnostic span"
      assertEqual (declaration.value.deriveAttribute.map fun derive =>
        derive.value.targets.elements) (some []) "empty derive retained"
  | items, diagnostics => throw (IO.userError
      s!"empty derive changed: {reprStr items}; {reprStr diagnostics}")

  let reserved ← checkedParse_variant "reserved derive target"
    "#[derive(contract)] enum Reserved { Only }"
  match reserved.parsed.items, reserved.parseDiagnostics with
  | [{ value := .enum declaration, .. }],
      [{ span, kind := .constraintViolation
          (.reservedDeriveTarget .contractKw) }] =>
      assertEqual (byteRange span) (9, 17) "reserved target span"
      assertEqual (declaration.value.deriveAttribute.map fun derive =>
        derive.value.targets.elements.map qualifiedText)
        (some ["contract"]) "reserved target source text"
  | items, diagnostics => throw (IO.userError
      s!"reserved derive changed: {reprStr items}; {reprStr diagnostics}")

  let misplaced ← checkedParse_variant "misplaced derive"
    "#[derive(Eq)] type Alias = word;"
  match misplaced.parsed.items, misplaced.parseDiagnostics with
  | [{ span := itemSpan, value := .typeAlias alias, .. }],
      [{ span, kind := .constraintViolation .deriveOnlyEnum }] =>
      assertEqual (byteRange span) (0, 13) "misplaced derive diagnostic span"
      assertEqual (byteRange itemSpan) (0, 32) "misplaced derive item span"
      assertEqual (byteRange alias.span) (0, 32)
        "misplaced derive declaration span"
      assertEqual alias.value.name.value "Alias" "following declaration retained"
  | items, diagnostics => throw (IO.userError
      s!"misplaced derive changed: {reprStr items}; {reprStr diagnostics}")

private def testDeriveRecovery : IO Unit := do
  let malformed ← checkedParse_variant "closed malformed derive"
    "#[derive(Eq,)] enum Closed { One }"
  match malformed.parsed.items, malformed.parseDiagnostics with
  | [{ span := itemSpan, value := .enum declaration, .. }],
      [{ span, kind := .constraintViolation .malformedDeriveAttribute }] =>
      assertEqual (byteRange span) (0, 14) "malformed derive span"
      assertEqual (byteRange itemSpan) (0, 34) "malformed enum item span"
      assertEqual declaration.value.name.value "Closed"
        "declaration after malformed derive"
      assertEqual (declaration.value.deriveAttribute.map fun derive =>
        derive.value.targets.elements) (some []) "recovered malformed attribute"
  | items, diagnostics => throw (IO.userError
      s!"malformed derive changed: {reprStr items}; {reprStr diagnostics}")

  let unclosed ← checkedParse_variant "unclosed top-level derive"
    "#[derive(Eq)\nenum Open { One }"
  match unclosed.parsed.items, unclosed.parseDiagnostics with
  | [{ span := itemSpan, value := .enum declaration, .. }],
      [{ span, kind := .constraintViolation .unclosedDeriveAttribute }] =>
      assertEqual (byteRange span) (0, 12) "unclosed derive span"
      assertEqual (byteRange itemSpan) (0, 30) "unclosed enum item span"
      assertEqual declaration.value.name.value "Open"
        "declaration after unclosed derive"
  | items, diagnostics => throw (IO.userError
      s!"unclosed derive changed: {reprStr items}; {reprStr diagnostics}")

  let content := "#[derive(Eq) }"
  let file : SourceFile := { id := declarationSource, content }
  let lexed ← match Lexer.lex file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"derive right-brace lexer invariant: {reprStr error}")
  match Parser.deriveAttribute (Parser.State.initial file lexed) with
  | .ok derive state =>
      assertEqual (byteRange derive.span) (0, 12)
        "right-brace recovered derive span"
      assertEqual state.peekKind? (some (.symbol .rightBrace))
        "right brace remains unconsumed"
      assertEqual (state.diagnostics.map fun diagnostic => diagnostic.kind)
        [.constraintViolation .unclosedDeriveAttribute]
        "right-brace derive diagnostic"
  | .reject failure _ => throw (IO.userError
      s!"right-brace derive rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"right-brace derive invariant: {reprStr error}")

private def testTraitDeclaration : IO Unit := do
  let source :=
    "trait Convert<a, b,> where a: Eq, { function convert(value: a) returns (b,); }"
  let output ← checkedParse_variant "trait declaration" source
  assertEqual output.parseDiagnostics [] "trait diagnostics"
  match output.parsed.items with
  | [{ value := .trait declaration, .. }] =>
      assertEqual (byteRange declaration.span) (0, 78) "trait span"
      assertEqual declaration.value.name.value "Convert" "trait name"
      assertEqual (genericNames declaration.value.genericParameters)
        ["a", "b"] "trait generic parameters"
      assertEqual (byteRange declaration.value.genericParameters.span)
        (13, 20) "trait generic span"
      assertEqual (declaration.value.whereClause.map fun clause =>
        clause.predicates.toList.length) (some 1) "trait predicate count"
      assertEqual (byteRange declaration.value.bodySpan) (34, 78)
        "trait body span"
      match declaration.value.methods with
      | [method] =>
          assertEqual (byteRange method.span) (36, 76) "trait method span"
          assertEqual method.value.signature.name.value "convert"
            "trait method name"
          assertEqual (parameterNames method.value.signature.parameters)
            ["value"] "trait method parameters"
          assertEqual (method.value.signature.returnsClause.map fun returns =>
            returns.types.elements.map typeName?)
            (some [some "b"]) "trait method return type"
          assertEqual (byteRange method.value.semicolon) (75, 76)
            "trait method semicolon span"
      | methods => throw (IO.userError
          s!"trait methods changed: {reprStr methods}")
  | items => throw (IO.userError s!"trait item changed: {reprStr items}")

private def testImplDeclaration : IO Unit := do
  let source :=
    "default impl<t,> Convert<t, word,> where t: Eq, { function convert(value: t) returns (word) { value } }"
  let output ← checkedParse_variant "impl declaration" source
  assertEqual output.parseDiagnostics [] "impl diagnostics"
  match output.parsed.items with
  | [{ value := .impl declaration, .. }] =>
      assertEqual (byteRange declaration.span) (0, 103) "impl span"
      assertEqual (declaration.value.defaultMarker.map byteRange)
        (some (0, 7)) "default marker span"
      assertEqual (declaration.value.genericParameters.map genericNames)
        (some ["t"]) "impl generic parameters"
      assertEqual declaration.value.traitName.value "Convert" "impl trait name"
      assertEqual (declaration.value.headArguments.elements.toList.map typeName?)
        [some "t", some "word"] "impl head arguments"
      assertEqual (byteRange declaration.value.headArguments.span) (24, 34)
        "impl head span"
      assertEqual (declaration.value.whereClause.map fun clause =>
        clause.predicates.toList.length) (some 1) "impl predicate count"
      assertEqual (byteRange declaration.value.bodySpan) (48, 103)
        "impl body span"
      match declaration.value.methods with
      | [method] =>
          assertEqual (byteRange method.span) (50, 101) "impl method span"
          assertEqual method.value.declaration.value.signature.name.value
            "convert" "impl method name"
          assertEqual (tailName? method.value.declaration.value.body)
            (some "value") "impl method tail expression"
      | methods => throw (IO.userError
          s!"impl methods changed: {reprStr methods}")
  | items => throw (IO.userError s!"impl item changed: {reprStr items}")

/-- Run canonical enum, derive, trait, and impl parser regressions. -/
def testSyntaxParserEnumTraitImpl : IO Unit := do
  testEnumAndDerive
  testDeriveDiagnostics
  testDeriveRecovery
  testTraitDeclaration
  testImplDeclaration

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFunctionDeclSoundnessProperties
/-! External consumers for strict and broad function-declaration outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionDeclSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @FunctionDeclParses
example := @FunctionDeclOrdinaryParses
example := @FunctionDeclRejects
example := @functionDeclDeterministicOutcomeSpec

example := @functionDecl_reflectsDiagnosticFreeOnSuccess
example := @functionDecl_success_sound
example := @functionDecl_success_sound_and_validFor
example := @functionDecl_success_ordinaryOutcome_sound
example := @functionDecl_reject_ordinaryOutcome_sound
example := @functionDecl_ordinaryOutcome_sound
example := @functionDecl_ordinaryOutcomeSpec
example := @functionDeclExactOutcomeSpecOfBody
example := @functionDeclExactOutcomeSpecOfStatementFuel
example := @functionDecl_exactOutcomeSpec_of_body
example := @functionDecl_exactOutcomeSpec_of_statementFuel
example := @functionDecl_success_result_unique_of_body
example := @functionDecl_reject_output_unique_of_body

example
    (bodyParses : Remainder → Block → Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : FunctionDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionDecl .module input = .ok declaration next) :
    FunctionDeclParses bodyParses ModuleFunctionModifiersAllowed
      input.declarativeRemainder declaration next.declarativeRemainder :=
  functionDecl_success_sound .module bodyParses bodyReflects bodySound
    diagnosticFree result

example
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : Remainder → Block → Remainder → Prop)
    (bodyValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : FunctionDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionDecl .contract input = .ok declaration next) :
    FunctionDeclParses bodyParses ContractFunctionModifiersAllowed
          input.declarativeRemainder declaration next.declarativeRemainder ∧
      FunctionDecl.ValidFor statementValid input.file declaration :=
  functionDecl_success_sound_and_validFor statementValid .contract bodyParses
    bodyValid bodyReflects bodySound inputValid diagnosticFree result

example {input next : State} {declaration : FunctionDecl}
    (result : functionDecl .module input = .ok declaration next) :
    FunctionDeclOrdinaryParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  functionDecl_success_ordinaryOutcome_sound .module result

example {input rejected : State} {failure : Failure}
    (result : functionDecl .contract input = .reject failure rejected) :
    FunctionDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  functionDecl_reject_ordinaryOutcome_sound .contract result

end Solcore.Test.SyntaxParserFunctionDeclSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFunctionDeclarationTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @functionDecl_ordinary
example := @functionDecl_invariantFreeOnValid
example := @functionDecl_ne_invariant

end Solcore.Test.SyntaxParserFunctionDeclarationTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFunctionParameterSoundnessProperties
/-! External consumers for strict and recovery-aware function parameters. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionParameterSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @FunctionParameterParses
example := @FunctionParametersParses
example := @FunctionParameterTailOrdinaryParses
example := @FunctionParameterCoreOrdinaryParses
example := @FunctionParameterCoreRejects
example := @FunctionParameterBoundaryStops
example := @FunctionParameterOrdinaryParses
example := @FunctionParameterRejects
example := @functionParameterCoreDeterministicOutcomeSpec
example := @functionParameterDeterministicOutcomeSpec
example := @functionParameterRecoveryExactOutcomeSpec
example := @functionParameterExactOutcomeSpec
example := @FunctionParametersOrdinaryParses
example := @FunctionParametersRejects
example := @functionParametersDeterministicOutcomeSpec
example := @functionParametersExactOutcomeSpec

example := @Parser.ReflectsDiagnosticFreeOnSuccess
example := @Parser.pure_reflectsDiagnosticFreeOnSuccess
example := @Parser.bind_reflectsDiagnosticFreeOnSuccess
example := @Parser.orElse_reflectsDiagnosticFreeOnSuccess
example := @delimited_reflectsDiagnosticFreeOnSuccess
example := @delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess
example := @typeExprWithFuel_reflectsDiagnosticFreeOnSuccess
example := @typeExpr_reflectsDiagnosticFreeOnSuccess
example := @namedParameter_reflectsDiagnosticFreeOnSuccess

example := @namedParameter_success_sound
example := @namedParameter_success_sound_and_validFor
example := @functionParameters_success_sound
example := @functionParameters_success_sound_and_validFor
example := @FunctionParameterInternals.namedParameterCore_ordinaryOutcome_sound
example := @FunctionParameterInternals.namedParameterCore_ordinaryOutcomeSpec
example := @namedParameter_success_ordinaryOutcome_sound
example := @namedParameter_reject_ordinaryOutcome_sound
example := @namedParameter_ordinaryOutcome_sound
example := @namedParameter_ordinaryOutcomeSpec
example := @namedParameter_exactOutcomeSpec
example := @namedParameter_success_result_unique
example := @namedParameter_reject_output_unique
example := @functionParameters_success_ordinaryOutcome_sound
example := @functionParameters_reject_ordinaryOutcome_sound
example := @functionParameters_ordinaryOutcome_sound
example := @functionParameters_ordinaryOutcomeSpec
example := @functionParameters_exactOutcomeSpec
example := @functionParameters_success_result_unique
example := @functionParameters_reject_output_unique

example :
    DeterministicOutcomeSpec
      (FunctionParameterOrdinaryParses TypeExprOrdinaryParses TypeExprRejects)
      (FunctionParameterRejects TypeExprRejects) :=
  functionParameterDeterministicOutcomeSpec typeExprDeterministicOutcomeSpec

example :
    ExactDeterministicOutcomeSpec
      (FunctionParameterOrdinaryParses TypeExprOrdinaryParses TypeExprRejects)
      (FunctionParameterRejects TypeExprRejects) :=
  functionParameterExactOutcomeSpec typeExprExactOutcomeSpec

example {input next : State} {parameter : FunctionParameter}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (result : namedParameter input = .ok parameter next) :
    FunctionParameterParses input.declarativeRemainder parameter
        next.declarativeRemainder ∧
      parameter.ValidFor input.file :=
  namedParameter_success_sound_and_validFor inputValid diagnosticFree result

example {input next : State} {parameter : FunctionParameter}
    (result : namedParameter input = .ok parameter next) :
    FunctionParameterOrdinaryParses TypeExprOrdinaryParses TypeExprRejects
      input.declarativeRemainder parameter next.declarativeRemainder :=
  namedParameter_success_ordinaryOutcome_sound TypeExprOrdinaryParses
    TypeExprRejects typeExpr_success_sound typeExpr_reject_sound result

example {input rejected : State} {failure : Failure}
    (result : namedParameter input = .reject failure rejected) :
    FunctionParameterRejects TypeExprRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  namedParameter_reject_ordinaryOutcome_sound TypeExprRejects
    typeExpr_reject_sound result

example {input next : State}
    {parameters : DelimitedList FunctionParameter}
    (result : functionParameters input = .ok parameters next) :
    FunctionParametersOrdinaryParses input.declarativeRemainder parameters
      next.declarativeRemainder :=
  functionParameters_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : functionParameters input = .reject failure rejected) :
    FunctionParametersRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  functionParameters_reject_ordinaryOutcome_sound result

example {input next : State}
    {parameters : DelimitedList FunctionParameter}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (result : functionParameters input = .ok parameters next) :
    FunctionParametersParses input.declarativeRemainder parameters
        next.declarativeRemainder ∧
      DelimitedList.ValidFor FunctionParameter.ValidFor input.file
        parameters :=
  functionParameters_success_sound_and_validFor inputValid diagnosticFree
    result

end Solcore.Test.SyntaxParserFunctionParameterSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFunctionProperties
/-! External compile consumers for complete-function state contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @FunctionInternals.block_startsAtCurrentTokenOnSuccess
example := @FunctionInternals.functionSignature_cursor_lt_onSuccess
example := @functionDecl_span_validOnSuccess
example := @functionDecl_validFor_of_span
example := @functionDecl_validFor
example := @functionDecl_preservesTokenWindow_of_block
example := @functionDecl_preservesTokensOnSuccess_of_block
example := @functionDecl_cursorMonotoneOnSuccess_of_block
example := @functionDecl_startsAtCurrentTokenOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFunctionSignatureLeafTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionSignatureLeafTotalityProperties

open Solcore.Syntax.Parser

example := @functionParameters_invariantFreeOnValid
example := @optionalFunctionModifier_invariantFreeOnValid
example := @functionModifiers_invariantFreeOnValid
example := @returnClause_invariantFreeOnValid

end Solcore.Test.SyntaxParserFunctionSignatureLeafTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFunctionSignatureProperties
/-! External compile consumers for function-signature prerequisites. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := functionParameters_validFor
example := functionParameters_preservesTokenWindow
example := functionParameters_preservesTokensOnSuccess
example := functionParameters_cursorMonotoneOnSuccess
example := functionParameters_startsAtCurrentTokenOnSuccess
example := @optionalFunctionModifier_some_startsAtCurrentTokenOnSuccess
example := @functionSignature_validFor_of_span
example := @functionSignature_span_validOnSuccess
example := @functionSignature_validFor
example := @functionSignature_preservesTokenWindow_of_where
example := @functionSignature_preservesTokensOnSuccess_of_where
example := @functionSignature_cursorMonotoneOnSuccess_of_where
example := @functionSignature_preservesTokenWindow
example := @functionSignature_preservesTokensOnSuccess
example := @functionSignature_cursorMonotoneOnSuccess
example := @functionSignature_startsAtCurrentTokenOnSuccess
example := @SignatureInternals.signatureEnd_where
example := @SignatureInternals.signatureEnd_returns
example := @SignatureInternals.signatureEnd_payable
example := @SignatureInternals.signatureEnd_public
example := @SignatureInternals.signatureEnd_parameters
example := @SignatureInternals.signatureEnd_validFor
example := @functionSignature_keyword_start_le_endOnSuccess
example := returnClause_validFor
example := returnClause_preservesTokenWindow
example := returnClause_preservesTokensOnSuccess
example := returnClause_cursorMonotoneOnSuccess
example := @returnClause_some_startsAtCurrentTokenOnSuccess
example := functionModifiers_validFor
example := functionModifiers_preservesTokenWindow
example := functionModifiers_preservesTokensOnSuccess
example := functionModifiers_cursorMonotoneOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFunctionSignatureSoundnessProperties
/-! External consumers for strict and broad function-signature outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionSignatureSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalFunctionModifierParses
example := @FunctionModifiersParses
example := @ModuleFunctionModifiersAllowed
example := @ContractFunctionModifiersAllowed
example := @functionSignatureEnd
example := @FunctionSignatureParses
example := @FunctionSignatureOrdinaryParses
example := @FunctionSignatureRejects
example := @functionSignatureDeterministicOutcomeSpec
example := @genericParametersExactOutcomeSpec
example := @optionalGenericParametersExactOutcomeSpec
example := @optionalReturnClauseExactOutcomeSpec
example := @predicateExactOutcomeSpec
example := @groupedPredicateSequenceExactOutcomeSpec
example := @barePredicateSequenceExactOutcomeSpec
example := @predicateSequenceExactOutcomeSpec
example := @optionalWhereClauseExactOutcomeSpec
example := @functionSignatureExactOutcomeSpec

example := @optionalFunctionModifier_success_sound
example := @optionalFunctionModifier_success_sound_and_validFor
example := @functionModifiers_success_sound
example := @functionModifiers_success_sound_and_validFor
example := @functionModifiers_module_success_allowed
example := @functionModifiers_contract_success_allowed

example := @genericParameters_reflectsDiagnosticFreeOnSuccess
example := @optionalGenericParameters_reflectsDiagnosticFreeOnSuccess
example := @functionParameters_reflectsDiagnosticFreeOnSuccess
example := @optionalFunctionModifier_reflectsDiagnosticFreeOnSuccess
example := @functionModifiers_reflectsDiagnosticFreeOnSuccess
example := @returnClause_reflectsDiagnosticFreeOnSuccess
example := @predicate_reflectsDiagnosticFreeOnSuccess
example := @PredicateInternals.groupedPredicates_reflectsDiagnosticFreeOnSuccess
example := @PredicateInternals.barePredicates_reflectsDiagnosticFreeOnSuccess
example := @PredicateInternals.predicateSequence_reflectsDiagnosticFreeOnSuccess
example := @whereClause_reflectsDiagnosticFreeOnSuccess

example := @functionSignature_success_sound
example := @functionSignature_success_sound_and_validFor
example := @functionSignature_module_success_sound
example := @functionSignature_contract_success_sound
example := @functionSignature_success_ordinaryOutcome_sound
example := @functionSignature_reject_ordinaryOutcome_sound
example := @functionSignature_ordinaryOutcome_sound
example := @functionSignature_ordinaryOutcomeSpec
example := @functionSignature_exactOutcomeSpec
example := @functionSignature_success_result_unique
example := @functionSignature_reject_output_unique

example {input next : State} {signature : FunctionSignature}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (result : functionSignature .module input = .ok signature next) :
    FunctionSignatureParses ModuleFunctionModifiersAllowed
          input.declarativeRemainder signature next.declarativeRemainder ∧
      FunctionSignature.ValidFor input.file signature :=
  functionSignature_success_sound_and_validFor .module inputValid
    diagnosticFree result

example {input next : State} {signature : FunctionSignature}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (result : functionSignature .contract input = .ok signature next) :
    FunctionSignatureParses ContractFunctionModifiersAllowed
          input.declarativeRemainder signature next.declarativeRemainder ∧
      FunctionSignature.ValidFor input.file signature :=
  functionSignature_success_sound_and_validFor .contract inputValid
    diagnosticFree result

example {input next : State} {signature : FunctionSignature}
    (result : functionSignature .module input = .ok signature next) :
    FunctionSignatureOrdinaryParses input.declarativeRemainder signature
      next.declarativeRemainder :=
  functionSignature_success_ordinaryOutcome_sound .module result

example {input rejected : State} {failure : Failure}
    (result : functionSignature .contract input = .reject failure rejected) :
    FunctionSignatureRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  functionSignature_reject_ordinaryOutcome_sound .contract result

end Solcore.Test.SyntaxParserFunctionSignatureSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserFunctionSignatureTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionSignatureTotalityProperties

open Solcore.Syntax.Parser

example := @functionSignature_ordinary
example := @functionSignature_invariantFreeOnValid
example := @functionSignature_ne_invariant
example := @functionSignature_elementTotalityContract

end Solcore.Test.SyntaxParserFunctionSignatureTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserImplBodyTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImplBodyTotalityProperties

open Solcore.Syntax.Parser

example := @ImplInternals.implMethod_ordinary
example := @ImplInternals.implMethod_invariantFreeOnValid
example := @ImplInternals.implMethod_ne_invariant
example := @ImplInternals.implMethod_cursor_lt_onSuccess
example := @ImplInternals.implMethods_ordinary_of_remainingCount_lt
example := @ImplInternals.implMethods_production_ordinary
example := @ImplInternals.implMethods_production_invariantFreeOnValid
example := @ImplInternals.implMethods_production_ne_invariant
example := @ImplInternals.implMethods_ne_invariant_of_remainingCount_lt
example := @ImplInternals.implBody_ordinary
example := @ImplInternals.implBody_invariantFreeOnValid
example := @ImplInternals.implBody_ne_invariant

end Solcore.Test.SyntaxParserImplBodyTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserImplDeclarationTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImplDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @ImplInternals.implDeclAfterDefault_ordinary
example := @ImplInternals.implDeclAfterDefault_invariantFreeOnValid
example := @ImplInternals.implDeclAfterDefault_ne_invariant
example := @implDecl_ordinary
example := @implDecl_invariantFreeOnValid
example := @implDecl_ne_invariant

end Solcore.Test.SyntaxParserImplDeclarationTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserImplHeadTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImplHeadTotalityProperties

open Solcore.Syntax.Parser

example := @ImplInternals.requireImplArguments_ok_of_delimited_false_ok
example := @ImplInternals.implDefaultMarker_invariantFreeOnValid
example := @ImplInternals.implDefaultMarker_ne_invariant

end Solcore.Test.SyntaxParserImplHeadTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserImplProperties
/-! External compile consumers for implementation parser state contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @ImplInternals.requireImplArguments_preservesTokenWindow
example := @ImplInternals.implMethod_preservesTokenWindow_of_block
example := @ImplInternals.implMethods_preservesTokenWindow_of_block
example := @ImplInternals.implBody_preservesTokenWindow_of_block
example := @ImplInternals.implMethods_cursorMonotoneOnSuccess
example := @ImplInternals.implBody_cursorMonotoneOnSuccess
example := @ImplInternals.implDefaultMarker_preservesTokenWindow
example := @ImplInternals.implDefaultMarker_preservesTokensOnSuccess
example := @ImplInternals.implDefaultMarker_some_startsAtCurrentTokenOnSuccess
example := @ImplInternals.implDeclAfterDefault_preservesTokenWindow_of_block
example := @ImplInternals.implDeclAfterDefault_preservesTokensOnSuccess_of_block
example := @ImplInternals.implDeclAfterDefault_cursor_lt_onSuccess
example := @ImplInternals.implDeclAfterDefault_startOnSuccess
example := @implDecl_preservesTokenWindow_of_block
example := @implDecl_preservesTokensOnSuccess_of_block
example := @implDecl_cursor_lt_onSuccess
example := @implDecl_cursorMonotoneOnSuccess
example := @implDecl_startsAtCurrentTokenOnSuccess
example := @ImplInternals.ImplBody.ValidFor
example := @ImplInternals.requireImplArguments_reply_validFor
example := @ImplInternals.implMethod_validFor
example := @ImplInternals.implMethods_validFor
example := @ImplInternals.implBody_validFor
example := @ImplInternals.implBody_startsAtCurrentTokenOnSuccess
example := @ImplInternals.implDefaultMarker_validFor
example := @implDecl_validFor

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserImplSoundnessProperties
/-! External consumers for strict and broad implementation soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImplSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalImplDefaultMarkerParses
example := @OptionalImplDefaultMarkerOrdinaryParses
example := @OptionalImplDefaultMarkerRejects
example := @optionalImplDefaultMarkerDeterministicOutcomeSpec
example := @OptionalImplDefaultMarkerOrdinaryParses.value_unique
example := @OptionalImplDefaultMarkerOrdinaryParses.result_unique
example := @OptionalImplDefaultMarkerRejects.output_unique
example := @optionalImplDefaultMarkerExactOutcomeSpec
example := @ImplHeadArgumentsParses
example := @ImplHeadArgumentsOrdinaryParses
example := @ImplHeadArgumentsRejects
example := @implHeadArgumentsDeterministicOutcomeSpec
example := @ImplHeadArgumentsOrdinaryParses.value_unique
example := @ImplHeadArgumentsOrdinaryParses.result_unique
example := @ImplHeadArgumentsRejects.output_unique
example := @implHeadArgumentsExactOutcomeSpec
example := @ImplMethodParses
example := @ImplMethodOrdinaryParses
example := @ImplMethodRejects
example := @implMethodDeterministicOutcomeSpec
example := @ImplMethodTailParses
example := @ImplMethodStartAt
example := @ImplMethodTailOrdinaryParses
example := @ImplMethodTailOrdinaryOutcomeParses
example := @ImplMethodTailRejects
example := @implMethodTailDeterministicOutcomeSpec
example := @ImplMethodTailOrdinaryParses.result_unique
example := @ImplMethodTailOrdinaryOutcomeParses.value_unique
example := @ImplMethodTailRejects.output_unique
example := @implMethodTailExactOutcomeSpecOfMethod
example := @ImplBodyParses
example := @ImplBodyOrdinaryParses
example := @ImplBodyOrdinaryOutcomeParses
example := @ImplBodyRejects
example := @implBodyDeterministicOutcomeSpec
example := @ImplBodyOrdinaryParses.result_unique
example := @ImplBodyOrdinaryOutcomeParses.value_unique
example := @ImplBodyRejects.output_unique
example := @implBodyExactOutcomeSpecOfMethod
example := @implBodyExactOutcomeSpecOfBody
example := @implBodyExactOutcomeSpecOfStatementFuel
example := @ImplDeclParses
example := @ImplDeclOrdinaryParses
example := @ImplDeclRejects
example := @implDeclDeterministicOutcomeSpec
example := @ImplDeclOrdinaryParses.value_unique_of_impl_body
example := @ImplDeclOrdinaryParses.result_unique_of_impl_body
example := @ImplDeclRejects.output_unique_of_impl_body
example := @implDeclExactOutcomeSpecOfImplBody
example := @implDeclExactOutcomeSpecOfBody
example := @implDeclExactOutcomeSpecOfStatementFuel

example := @ImplInternals.implDefaultMarker_reflectsDiagnosticFreeOnSuccess
example := @ImplInternals.implDefaultMarker_success_sound
example := @ImplInternals.implDefaultMarker_validFor
example := @ImplInternals.requireImplArguments_reflectsDiagnosticFreeOnSuccess
example := @ImplInternals.requireImplArguments_success_shape
example := @ImplInternals.requireImplArguments_reply_validFor
example := @ImplInternals.implHeadArguments_success_sound
example := @ImplInternals.implDefaultMarker_success_ordinaryOutcome_sound
example := @ImplInternals.implDefaultMarker_reject_ordinaryOutcome_sound
example := @ImplInternals.implDefaultMarker_ordinaryOutcome_sound
example := @ImplInternals.implDefaultMarker_ordinaryOutcomeSpec
example := @ImplInternals.implDefaultMarker_exactOutcomeSpec
example := @ImplInternals.implDefaultMarker_success_result_unique
example := @ImplInternals.implDefaultMarker_reject_output_unique
example := @ImplInternals.implHeadArguments_success_ordinaryOutcome_sound
example := @ImplInternals.implHeadArguments_reject_ordinaryOutcome_sound
example := @ImplInternals.implHeadArguments_ordinaryOutcome_sound
example := @ImplInternals.implHeadArguments_ordinaryOutcomeSpec
example := @ImplInternals.implHeadArguments_exactOutcomeSpec
example := @ImplInternals.implHeadArguments_success_result_unique
example := @ImplInternals.implHeadArguments_reject_output_unique

example := @ImplInternals.implMethod_reflectsDiagnosticFreeOnSuccess
example := @ImplInternals.implMethod_success_sound
example := @ImplInternals.implMethod_success_sound_and_validFor
example := @ImplInternals.implMethod_validFor
example := @ImplInternals.implMethod_success_ordinaryOutcome_sound
example := @ImplInternals.implMethod_reject_ordinaryOutcome_sound
example := @ImplInternals.implMethod_ordinaryOutcome_sound
example := @ImplInternals.implMethod_ordinaryOutcomeSpec
example := @implMethodExactOutcomeSpecOfBody
example := @implMethodExactOutcomeSpecOfStatementFuel
example := @ImplInternals.implMethod_exactOutcomeSpec_of_body
example := @ImplInternals.implMethod_exactOutcomeSpec_of_statementFuel
example := @ImplInternals.implMethod_success_result_unique_of_body
example := @ImplInternals.implMethod_reject_output_unique_of_body

example := @ImplInternals.implBody_reflectsDiagnosticFreeOnSuccess
example := @ImplInternals.implBody_success_sound
example := @ImplInternals.implBody_success_sound_and_validFor
example := @ImplInternals.implBody_validFor
example := @ImplInternals.implBody_success_ordinaryOutcome_sound
example := @ImplInternals.implBody_reject_ordinaryOutcome_sound
example := @ImplInternals.implBody_ordinaryOutcome_sound
example := @ImplInternals.implBody_ordinaryOutcomeSpec
example := @ImplInternals.implBody_exactOutcomeSpec_of_method
example := @ImplInternals.implBody_exactOutcomeSpec_of_body
example := @ImplInternals.implBody_exactOutcomeSpec_of_statementFuel
example := @ImplInternals.implBody_success_result_unique_of_method
example := @ImplInternals.implBody_reject_output_unique_of_method
example := @ImplInternals.implBody_success_result_unique_of_body
example := @ImplInternals.implBody_reject_output_unique_of_body
example := @ImplInternals.implBody_success_result_unique_of_statementFuel
example := @ImplInternals.implBody_reject_output_unique_of_statementFuel

example := @implDecl_reflectsDiagnosticFreeOnSuccess
example := @implDecl_success_sound
example := @implDecl_success_sound_and_validFor
example := @implDecl_validFor
example := @implDecl_success_ordinaryOutcome_sound
example := @implDecl_reject_ordinaryOutcome_sound
example := @implDecl_ordinaryOutcome_sound
example := @implDecl_ordinaryOutcomeSpec
example := @implDecl_exactOutcomeSpec_of_implBody
example := @implDecl_exactOutcomeSpec_of_body
example := @implDecl_exactOutcomeSpec_of_statementFuel
example := @implDecl_success_result_unique_of_implBody
example := @implDecl_reject_output_unique_of_implBody
example := @implDecl_success_result_unique_of_body
example := @implDecl_reject_output_unique_of_body
example := @implDecl_success_result_unique_of_statementFuel
example := @implDecl_reject_output_unique_of_statementFuel

example
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : Remainder → Block → Remainder → Prop)
    (bodyValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ImplDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implDecl input = .ok declaration next) :
    ImplDeclParses bodyParses input.declarativeRemainder declaration
          next.declarativeRemainder ∧
      ImplDecl.ValidFor statementValid input.file declaration :=
  implDecl_success_sound_and_validFor statementValid bodyParses bodyValid
    bodyWindow bodyReflects bodySound inputValid diagnosticFree result

example {input next : State} {method : ImplMethod}
    (result : ImplInternals.implMethod input = .ok method next) :
    ImplMethodOrdinaryParses input.declarativeRemainder method
      next.declarativeRemainder :=
  ImplInternals.implMethod_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : ImplInternals.implMethod input = .reject failure rejected) :
    ImplMethodRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  ImplInternals.implMethod_reject_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : implDecl input = .reject failure rejected) :
    ImplDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  implDecl_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserImplSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserLocalExportItemSoundnessProperties
/-! External consumers for local export-item grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserLocalExportItemSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @IdentifierDotAbsentAt
example := @LocalExportItemParses
example := @LocalExportItemQualifiedStartAt
example := @LocalExportItemOrdinaryParses
example := @LocalExportItemRejects
example := @localExportItemDeterministicOutcomeSpec
example := @localExportItem_success_sound
example := @localExportItem_success_sound_and_validFor
example := @localExportItem_success_ordinaryOutcome_sound
example := @localExportItem_reject_ordinaryOutcome_sound
example := @localExportItem_ordinaryOutcome_sound
example := @localExportItem_ordinaryOutcomeSpec

example {input next : State} {item : LocalExportItem}
    (inputValid : input.ValidFor)
    (result : ExportInternals.localExportItem input = .ok item next) :
    LocalExportItemParses input.declarativeRemainder item
        next.declarativeRemainder ∧
      item.ValidFor input.file :=
  localExportItem_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserLocalExportItemSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserSelectorNameSoundnessProperties
/-! External consumers for selector-name grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSelectorNameSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @SelectorOperatorSymbol
example := @SelectorOperatorPartsParses
example := @SelectorOperatorPartAbsentAt
example := @MaximalSelectorOperatorPartsParses
example := @OperatorSelectorParses
example := @SelectorNameParses
example := @SelectorNameOrdinaryParses
example := @SelectorNameRejects
example := @selectorNameDeterministicOutcomeSpec
example := @operatorPart?_eq_some_iff
example := @operatorSelector_success_sound
example := @selectorName_success_sound
example := @selectorName_success_sound_and_validFor
example := @selectorName_success_ordinaryOutcome_sound
example := @selectorName_reject_ordinaryOutcome_sound
example := @selectorName_ordinaryOutcome_sound
example := @selectorName_ordinaryOutcomeSpec

example {kind : TokenKind} {spelling : String} :
    operatorPart? kind = some spelling ↔
      ∃ symbol,
        kind = .symbol symbol ∧
        SelectorOperatorSymbol symbol ∧
        spelling = symbol.spelling :=
  operatorPart?_eq_some_iff

example (context : ParseContext) {input next : State}
    {selector : SelectorName}
    (result : selectorName context input = .ok selector next) :
    SelectorNameParses input.declarativeRemainder selector
      next.declarativeRemainder :=
  selectorName_success_sound context result

example (context : ParseContext) {input next : State}
    {selector : SelectorName} (inputValid : input.ValidFor)
    (result : selectorName context input = .ok selector next) :
    SelectorNameParses input.declarativeRemainder selector
        next.declarativeRemainder ∧
      selector.ValidFor input.file :=
  selectorName_success_sound_and_validFor context inputValid result

end Solcore.Test.SyntaxParserSelectorNameSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserSignatures
/-! Direct executable regressions for canonical function signatures. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @Parser.genericParameters_validFor
example := @Parser.genericParameters_preservesTokenWindow
example := @Parser.genericParameters_preservesTokensOnSuccess
example := @Parser.genericParameters_cursorMonotoneOnSuccess
example := @Parser.genericParameters_startsAtCurrentTokenOnSuccess
example := @Parser.optionalGenericParameters_validFor
example := @Parser.optionalGenericParameters_preservesTokenWindow
example := @Parser.optionalGenericParameters_preservesTokensOnSuccess
example := @Parser.optionalGenericParameters_cursorMonotoneOnSuccess

private def parserSource : SourceId := {
  origin := .main
  path := "parser-signatures.sol"
}

private structure SignatureRun where
  signature : FunctionSignature
  diagnostics : List ParseDiagnostic

private def runSignature (label content : String)
    (location : Parser.FunctionLocation) : IO SignatureRun := do
  let file : SourceFile := { id := parserSource, content }
  let lexed ← match Lexer.lex file with
    | .error error => throw (IO.userError
        s!"{label}: lexer invariant failed: {reprStr error}")
    | .ok value => pure value
  assertEqual lexed.diagnostics [] s!"{label} lexical diagnostics"
  match Parser.functionSignature location (Parser.State.initial file lexed) with
  | .ok signature state =>
      unless state.atEnd do
        throw (IO.userError
          s!"{label}: left {state.remainingCount} token(s) unconsumed")
      unless signature.span.isValidFor file do
        throw (IO.userError s!"{label}: invalid signature span")
      unless state.diagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid diagnostic span")
      pure { signature, diagnostics := state.diagnostics }
  | .reject failure _ => throw (IO.userError
      s!"{label}: parser rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")

private inductive SignatureTypeShape where
  | named (path : List String) (arguments : Option (List SignatureTypeShape))
  | tuple (elements : List SignatureTypeShape)
  | comptime (inner : SignatureTypeShape)
  | other
  | error
  deriving Repr, BEq, Inhabited

private partial def typeShape (type : TypeExpr) : SignatureTypeShape :=
  match type.value with
  | .named name arguments => .named
      (name.value.components.toList.map (fun item => item.value))
      (arguments.map fun items => items.elements.toList.map typeShape)
  | .tuple elements => .tuple (elements.map typeShape)
  | .comptime _ _ inner => .comptime (typeShape inner)
  | .error => .error
  | _ => .other

private inductive SignatureParameterShape where
  | typed (comptime : Bool) (name : String) (type : SignatureTypeShape)
  | error
  deriving Repr, BEq

private def parameterShape (parameter : FunctionParameter) : SignatureParameterShape :=
  match parameter.value with
  | .typed marker name type =>
      .typed marker.isSome name.value (typeShape type)
  | .error => .error

private structure SignaturePredicateShape where
  subject : SignatureTypeShape
  traitName : String
  arguments : Option (List SignatureTypeShape)
  deriving Repr, BEq

private def predicateShape (predicate : Predicate) : SignaturePredicateShape := {
  subject := typeShape predicate.subject
  traitName := predicate.traitName.value
  arguments := predicate.arguments.map fun values =>
    values.elements.toList.map typeShape
}

private def names (values : GenericParameters) : List String :=
  values.elements.toList.map (fun name => name.value)

private def named (name : String) : SignatureTypeShape := .named [name] none

private def testCanonicalContractSignature : IO Unit := do
  let source :=
    "function combine<a, b,>(left: pkg.Box<a>, comptime right: b,) public payable returns (pkg.Pair<a, b>,) where (a: Eq, pkg.Box<b>: Convert<a, b>,)"
  let run ← runSignature "canonical contract signature" source .contract
  let signature := run.signature
  assertEqual run.diagnostics [] "canonical signature diagnostics"
  assertEqual signature.name.value "combine" "canonical signature name"
  assertEqual (signature.genericParameters.map names)
    (some ["a", "b"]) "generic trailing comma"
  assertEqual (signature.parameters.elements.map parameterShape) [
    .typed false "left" (.named ["pkg", "Box"] (some [named "a"])),
    .typed true "right" (named "b")
  ] "typed and comptime parameters"
  assertEqual (signature.modifiers.publicMarker.map byteRange) (some (62, 68))
    "public marker span"
  assertEqual (signature.modifiers.payableMarker.map byteRange) (some (69, 76))
    "payable marker span"
  assertEqual (signature.returnsClause.map fun clause =>
      clause.types.elements.map typeShape)
    (some [.named ["pkg", "Pair"] (some [named "a", named "b"])])
    "trailing return list"
  assertEqual (signature.whereClause.map fun clause =>
      clause.predicates.toList.map predicateShape) (some [
    ⟨named "a", "Eq", none⟩,
    ⟨.named ["pkg", "Box"] (some [named "b"]), "Convert",
      some [named "a", named "b"]⟩
  ]) "grouped predicates and trait arguments"
  assertEqual (byteRange signature.span) (0, 144) "signature span"
  assertEqual (signature.genericParameters.map
    (fun values => byteRange values.span)) (some (16, 23)) "generic span"
  assertEqual (byteRange signature.parameters.span) (23, 61) "parameter span"
  assertEqual (signature.parameters.elements.map
    (fun parameter => byteRange parameter.span)) [(24, 40), (42, 59)]
    "individual parameter spans"
  assertEqual (signature.returnsClause.map
    (fun clause => byteRange clause.span)) (some (77, 102)) "returns span"
  assertEqual (signature.whereClause.map
    (fun clause => byteRange clause.span)) (some (103, 144)) "where span"

private def testEmptyAndTrailingLists : IO Unit := do
  let implicit ← runSignature "implicit unit" "function implicit()" .module
  assertEqual implicit.diagnostics [] "implicit-unit diagnostics"
  assertEqual implicit.signature.parameters.elements [] "empty parameters"
  assertEqual implicit.signature.returnsClause none "absent returns clause"

  let explicit ← runSignature "explicit unit"
    "function explicit() returns ()" .module
  assertEqual explicit.diagnostics [] "explicit-unit diagnostics"
  assertEqual (explicit.signature.returnsClause.map
    (fun clause => clause.types.elements)) (some []) "empty return list"

  let trailing ← runSignature "trailing lists"
    "function trailing<t,>(value: t,) returns (t,)" .module
  assertEqual trailing.diagnostics [] "trailing-list diagnostics"
  assertEqual (trailing.signature.genericParameters.map names) (some ["t"])
    "trailing generic list"
  assertEqual (trailing.signature.parameters.elements.map parameterShape)
    [.typed false "value" (named "t")] "trailing parameter list"
  assertEqual (trailing.signature.returnsClause.map fun clause =>
    clause.types.elements.map typeShape) (some [named "t"])
    "trailing returns list"

private def testModifierLocations : IO Unit := do
  let source := "function exposed() public payable"
  let moduleRun ← runSignature "module modifiers" source .module
  assertEqual (moduleRun.signature.modifiers.publicMarker.map byteRange)
    (some (19, 25)) "module public marker retained"
  assertEqual (moduleRun.signature.modifiers.payableMarker.map byteRange)
    (some (26, 33)) "module payable marker retained"
  assertEqual (moduleRun.diagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((19, 25), .constraintViolation
      (.modifierOutsideContract .publicKw)),
    ((26, 33), .constraintViolation
      (.modifierOutsideContract .payableKw))
  ] "module modifier diagnostics"
  let contractRun ← runSignature "contract modifiers" source .contract
  assertEqual contractRun.diagnostics [] "contract modifier allowance"
  assertEqual contractRun.signature.modifiers moduleRun.signature.modifiers
    "modifier source shape independent of location"

private def testBareWhereClause : IO Unit := do
  let run ← runSignature "bare where clause"
    "function constrained<t>() where t: Eq, pkg.Box<t>: Convert<word, t,>,"
    .module
  assertEqual run.diagnostics [] "bare where diagnostics"
  assertEqual (run.signature.whereClause.map fun clause =>
      clause.predicates.toList.map predicateShape) (some [
    ⟨named "t", "Eq", none⟩,
    ⟨.named ["pkg", "Box"] (some [named "t"]), "Convert",
      some [named "word", named "t"]⟩
  ]) "bare predicates and trailing trait arguments"
  match run.signature.whereClause with
  | some clause =>
      assertEqual clause.predicates.toList.length 2 "bare predicate count"
      assertEqual clause.span.endByte
        "function constrained<t>() where t: Eq, pkg.Box<t>: Convert<word, t,>,".utf8ByteSize
        "bare trailing comma included in span"
  | none => throw (IO.userError "bare where clause was lost")

private def testParameterDiagnostics : IO Unit := do
  let untyped ← runSignature "untyped parameter"
    "function missing(value)" .module
  assertEqual (untyped.signature.parameters.elements.map parameterShape)
    [.error] "untyped parameter recovery shape"
  assertEqual (untyped.diagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((17, 22), .constraintViolation .namedParameterRequiresType)
  ] "untyped parameter diagnostic"

  let comptimeType ← runSignature "comptime parameter type"
    "function invalid(value: comptime<word>)" .module
  assertEqual (comptimeType.signature.parameters.elements.map parameterShape)
    [.typed false "value" (.comptime (named "word"))]
    "comptime type source shape"
  match comptimeType.diagnostics with
  | [{ span, kind := .constraintViolation .comptimeTypeInParameter }] =>
      assertEqual (byteRange span) (24, 38) "comptime-type diagnostic span"
  | diagnostics => throw (IO.userError
      s!"comptime parameter type: unexpected diagnostics {reprStr diagnostics}")

  let recovered ← runSignature "parameter recovery"
    "function recover(+ -, good: word)" .module
  assertEqual (recovered.signature.parameters.elements.map parameterShape)
    [.error, .typed false "good" (named "word")]
    "recovered parameter and following parameter"
  match recovered.diagnostics with
  | [{ span := first, kind := firstKind },
      { span := consumed, kind := secondKind }] =>
      assertEqual firstKind (.unexpected (some (.symbol .plus))
        { head := .identifier, tail := [] } .parameter)
        "parameter failure diagnostic"
      assertEqual secondKind (.recovered .functionParameter)
        "parameter recovery diagnostic"
      assertEqual (byteRange first) (17, 18) "parameter failure span"
      assertEqual (byteRange consumed) (17, 20) "parameter recovery span"
  | diagnostics => throw (IO.userError
      s!"parameter recovery: unexpected diagnostics {reprStr diagnostics}")

/-- Run direct canonical function-signature parser regressions. -/
def testSyntaxParserSignatures : IO Unit := do
  testCanonicalContractSignature
  testEmptyAndTrailingLists
  testModifierLocations
  testBareWhereClause
  testParameterDiagnostics

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserSimpleDeclarationCompletenessProperties
/-! External consumers of both directions of exact ordinary completeness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSimpleDeclarationCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example {input : State} (inputValid : input.ValidFor)
    {value : TypeAliasDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, typeAlias input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (typeAlias_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : TypeAliasDecl} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : typeAlias input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      input.declarativeRemainder value remainder :=
  (typeAlias_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.TypeAliasDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, typeAlias input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (typeAlias_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : typeAlias input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.TypeAliasDeclRejects input.declarativeRemainder rejected :=
  (typeAlias_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example (deriveAttribute : Option DeriveAttribute) {input : State} (inputValid : input.ValidFor)
    {value : EnumDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute
      input.declarativeRemainder value remainder) :
    ∃ output, enumDecl deriveAttribute input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (enumDecl_ordinary_success_iff deriveAttribute inputValid).mp parsed

example (deriveAttribute : Option DeriveAttribute) {input : State} (inputValid : input.ValidFor)
    {value : EnumDecl} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : enumDecl deriveAttribute input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute
      input.declarativeRemainder value remainder :=
  (enumDecl_ordinary_success_iff deriveAttribute inputValid).mpr ⟨output, result, remainderEq⟩

example (deriveAttribute : Option DeriveAttribute) {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.EnumDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, enumDecl deriveAttribute input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (enumDecl_ordinary_reject_iff deriveAttribute inputValid).mp rejection

example (deriveAttribute : Option DeriveAttribute) {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : enumDecl deriveAttribute input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.EnumDeclRejects input.declarativeRemainder rejected :=
  (enumDecl_ordinary_reject_iff deriveAttribute inputValid).mpr ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : TraitDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.TraitDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, traitDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (traitDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : TraitDecl} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : traitDecl input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.TraitDeclOrdinaryParses
      input.declarativeRemainder value remainder :=
  (traitDecl_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.TraitDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, traitDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (traitDecl_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : traitDecl input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.TraitDeclRejects input.declarativeRemainder rejected :=
  (traitDecl_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

end Solcore.Test.SyntaxParserSimpleDeclarationCompletenessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTraitBodyTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTraitBodyTotalityProperties

open Solcore.Syntax.Parser

example := @TraitInternals.traitMethod_ordinary
example := @TraitInternals.traitMethod_invariantFreeOnValid
example := @TraitInternals.traitMethod_ne_invariant
example := @TraitInternals.traitMethod_elementTotalityContract
example := @TraitInternals.traitMethods_ordinary_of_remainingCount_lt
example := @TraitInternals.traitMethods_production_ordinary
example := @TraitInternals.traitMethods_production_invariantFreeOnValid
example := @TraitInternals.traitMethods_production_ne_invariant
example := @TraitInternals.traitMethods_ne_invariant_of_remainingCount_lt
example := @TraitInternals.traitBody_ordinary
example := @TraitInternals.traitBody_invariantFreeOnValid
example := @TraitInternals.traitBody_ne_invariant

end Solcore.Test.SyntaxParserTraitBodyTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTraitDeclarationTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTraitDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @traitDecl_ordinary
example := @traitDecl_invariantFreeOnValid
example := @traitDecl_ne_invariant

end Solcore.Test.SyntaxParserTraitDeclarationTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTraitProperties
/-! External compile consumers for canonical trait parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @TraitInternals.traitMethod_validFor
example := @TraitInternals.TraitBody.ValidFor
example := @TraitInternals.traitMethods_validFor
example := @TraitInternals.traitBody_validFor
example := @TraitInternals.traitBody_startsAtCurrentTokenOnSuccess
example := @TraitInternals.traitMethod_cursor_lt_onSuccess
example := @TraitInternals.traitBody_cursor_lt_onSuccess
example := @TraitInternals.traitMethod_preservesTokenWindow
example := @TraitInternals.traitMethods_preservesTokenWindow
example := @TraitInternals.traitMethods_cursorMonotoneOnSuccess
example := @TraitInternals.traitBody_preservesTokenWindow
example := @TraitInternals.traitBody_cursorMonotoneOnSuccess
example := @traitDecl_preservesTokenWindow
example := @traitDecl_validFor
example := @traitDecl_preservesTokensOnSuccess
example := @traitDecl_cursorMonotoneOnSuccess
example := @traitDecl_startsAtCurrentTokenOnSuccess
example := @traitDecl_cursor_lt_onSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTraitSoundnessProperties
/-! External consumers for diagnostic-free trait grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTraitSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TraitMethodParses
example := @TraitMethodTailParses
example := @TraitBodyParses
example := @TraitDeclParses
example := @TraitMethodOrdinaryParses
example := @TraitMethodRejects
example := @traitMethodDeterministicOutcomeSpec
example := @TraitMethodStartAt
example := @TraitMethodTailOrdinaryParses
example := @TraitMethodTailOrdinaryOutcomeParses
example := @TraitMethodTailRejects
example := @traitMethodTailDeterministicOutcomeSpec
example := @TraitMethodTailOrdinaryParses.result_unique
example := @TraitMethodTailRejects.output_unique
example := @traitMethodTailExactOutcomeSpec
example := @TraitBodyOrdinaryParses
example := @TraitBodyOrdinaryOutcomeParses
example := @TraitBodyRejects
example := @traitBodyDeterministicOutcomeSpec
example := @TraitBodyOrdinaryParses.result_unique
example := @TraitBodyRejects.output_unique
example := @traitBodyExactOutcomeSpec
example := @TraitDeclOrdinaryParses
example := @TraitDeclRejects
example := @traitDeclDeterministicOutcomeSpec
example := @TraitDeclOrdinaryParses.result_unique
example := @TraitDeclRejects.output_unique
example := @traitDeclExactOutcomeSpec

example := @TraitInternals.traitMethod_reflectsDiagnosticFreeOnSuccess
example := @TraitInternals.traitMethod_success_sound
example := @TraitInternals.traitMethod_success_sound_and_validFor

example := @TraitInternals.traitBody_reflectsDiagnosticFreeOnSuccess
example := @TraitInternals.traitBody_success_sound
example := @TraitInternals.traitBody_success_sound_and_validFor

example := @traitDecl_reflectsDiagnosticFreeOnSuccess
example := @traitDecl_success_sound
example := @traitDecl_success_sound_and_validFor
example := @TraitInternals.traitMethod_success_ordinaryOutcome_sound
example := @TraitInternals.traitMethod_reject_ordinaryOutcome_sound
example := @TraitInternals.traitMethod_ordinaryOutcome_sound
example := @TraitInternals.traitMethod_ordinaryOutcomeSpec
example := @traitMethodExactOutcomeSpec
example := @TraitInternals.traitMethod_exactOutcomeSpec
example := @TraitInternals.traitMethod_success_result_unique
example := @TraitInternals.traitMethod_reject_output_unique
example := @TraitInternals.traitBody_success_ordinaryOutcome_sound
example := @TraitInternals.traitBody_reject_ordinaryOutcome_sound
example := @TraitInternals.traitBody_ordinaryOutcome_sound
example := @TraitInternals.traitBody_ordinaryOutcomeSpec
example := @TraitInternals.traitBody_exactOutcomeSpec
example := @TraitInternals.traitBody_success_result_unique
example := @TraitInternals.traitBody_reject_output_unique
example := @traitDecl_success_ordinaryOutcome_sound
example := @traitDecl_reject_ordinaryOutcome_sound
example := @traitDecl_ordinaryOutcome_sound
example := @traitDecl_ordinaryOutcomeSpec
example := @traitDecl_exactOutcomeSpec
example := @traitDecl_success_result_unique
example := @traitDecl_reject_output_unique

example {input next : State} {method : TraitMethod}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : TraitInternals.traitMethod input = .ok method next) :
    TraitMethodParses input.declarativeRemainder method
      next.declarativeRemainder :=
  TraitInternals.traitMethod_success_sound diagnosticFree result

example {input next : State} {body : TraitInternals.TraitBody}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : TraitInternals.traitBody input = .ok body next) :
    TraitBodyParses input.declarativeRemainder body.span body.methods
          next.declarativeRemainder ∧
      TraitInternals.TraitBody.ValidFor input.file body :=
  TraitInternals.traitBody_success_sound_and_validFor inputValid
    diagnosticFree result

example {input next : State} {declaration : TraitDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitDecl input = .ok declaration next) :
    TraitDeclParses input.declarativeRemainder declaration
          next.declarativeRemainder ∧
      TraitDecl.ValidFor input.file declaration :=
  traitDecl_success_sound_and_validFor inputValid diagnosticFree result

example {input rejected : State} {failure : Failure}
    (result : traitDecl input = .reject failure rejected) :
    TraitDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  traitDecl_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserTraitSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeAliasRecoveryTotalityProperties
/-! External consumers for type-alias recovery totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeAliasRecoveryTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.TypeAliasInternals

example := @recoverTypeAliasValueAux_exists_ok_of_remainingCount_lt
example := @recoverTypeAliasValueAux_production_exists_ok
example := @recoverTypeAliasValueAux_ordinary_of_remainingCount_lt
example := @recoverTypeAliasValueAux_ne_invariant_of_remainingCount_lt
example := @recoverTypeAliasValueAux_production_ordinary
example := @recoverTypeAliasValueAux_production_ne_invariant
example := @recoverTypeAliasValue_ordinary
example := @recoverTypeAliasValue_ne_invariant

example (state : State) (error : ParserInvariantError) :
    recoverTypeAliasValue state ≠ .invariant error :=
  recoverTypeAliasValue_ne_invariant state error

example : Parser.PreservesTokenWindow recoverTypeAliasValue :=
  recoverTypeAliasValue_preservesTokenWindow

end Solcore.Test.SyntaxParserTypeAliasRecoveryTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeAliasSoundnessProperties
/-! External consumers for transparent type-alias grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeAliasSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalTypeAliasParametersParses
example := @TypeAliasDeclParses
example := @TypeAliasParametersOrdinaryParses
example := @TypeAliasParametersRejects
example := @typeAliasParametersDeterministicOutcomeSpec
example := @typeAliasParametersExactOutcomeSpec
example := @OptionalTypeAliasParametersOrdinaryParses
example := @OptionalTypeAliasParametersRejects
example := @optionalTypeAliasParametersDeterministicOutcomeSpec
example := @OptionalTypeAliasParametersOrdinaryParses.value_unique
example := @OptionalTypeAliasParametersOrdinaryParses.result_unique
example := @OptionalTypeAliasParametersRejects.output_unique
example := @optionalTypeAliasParametersExactOutcomeSpec
example := @TypeAliasValueBoundaryStops
example := @TypeAliasValueRecoveryStops
example := @TypeAliasValueRecoveryScanParses
example := @TypeAliasValueRecoveryParses
example := @TypeAliasValueRecoveryRejects
example := @typeAliasValueRecoveryDeterministicOutcomeSpec
example := @TypeAliasValueRecoveryScanParses.value_unique
example := @TypeAliasValueRecoveryScanParses.result_unique
example := @TypeAliasValueRecoveryParses.value_unique
example := @TypeAliasValueRecoveryParses.result_unique
example := @TypeAliasValueRecoveryRejects.output_unique
example := @typeAliasValueRecoveryExactOutcomeSpec
example := @TypeAliasValueCoreRejectsWithPreservedWindow
example := @TypeAliasValueOrdinaryParses
example := @TypeAliasValueRejects
example := @typeAliasValueDeterministicOutcomeSpec
example := @TypeAliasValueOrdinaryParses.value_unique_of_typeExpr
example := @TypeAliasValueOrdinaryParses.result_unique_of_typeExpr
example := @TypeAliasValueRejects.output_unique
example := @typeAliasValueExactOutcomeSpecOfTypeExpr
example := @TypeAliasValueOrdinaryParses.value_unique
example := @TypeAliasValueOrdinaryParses.result_unique
example := @typeAliasValueExactOutcomeSpec
example := @TypeAliasDeclOrdinaryParses
example := @TypeAliasDeclRejects
example := @typeAliasDeclDeterministicOutcomeSpec
example := @TypeAliasDeclOrdinaryParses.value_unique
example := @TypeAliasDeclOrdinaryParses.result_unique
example := @TypeAliasDeclRejects.output_unique
example := @typeAliasDeclExactOutcomeSpec
example := @parseTypeAliasParameters_success_sound
example := @TypeAliasInternals.parseAliasValue_success_sound_of_diagnosticFree
example := @typeAlias_success_sound
example := @typeAlias_success_sound_and_validFor

example := @TypeAliasInternals.recoverTypeAliasValue_success_ordinary_sound
example := @TypeAliasInternals.recoverTypeAliasValue_reject_ordinary_sound
example := @TypeAliasInternals.recoverTypeAliasValue_ordinaryOutcome_sound
example := @TypeAliasInternals.recoverTypeAliasValue_ordinaryOutcomeSpec
example := @TypeAliasInternals.recoverTypeAliasValue_exactOutcomeSpec
example := @TypeAliasInternals.recoverTypeAliasValue_success_result_unique
example := @TypeAliasInternals.recoverTypeAliasValue_reject_output_unique
example := @parseTypeAliasParameters_success_ordinaryOutcome_sound
example := @parseTypeAliasParameters_reject_ordinaryOutcome_sound
example := @parseTypeAliasParameters_ordinaryOutcome_sound
example := @parseTypeAliasParameters_ordinaryOutcomeSpec
example := @parseTypeAliasParameters_exactOutcomeSpec
example := @parseTypeAliasParameters_success_result_unique
example := @parseTypeAliasParameters_reject_output_unique
example := @TypeAliasInternals.parseAliasValue_success_ordinaryOutcome_sound
example := @TypeAliasInternals.parseAliasValue_reject_ordinaryOutcome_sound
example := @TypeAliasInternals.parseAliasValue_ordinaryOutcome_sound
example := @TypeAliasInternals.parseAliasValue_ordinaryOutcomeSpec
example := @TypeAliasInternals.parseAliasValue_exactOutcomeSpec_of_typeExpr
example := @TypeAliasInternals.parseAliasValue_success_result_unique_of_typeExpr
example := @TypeAliasInternals.parseAliasValue_reject_output_unique
example := @TypeAliasInternals.parseAliasValue_exactOutcomeSpec
example := @TypeAliasInternals.parseAliasValue_success_result_unique
example := @typeAlias_success_ordinaryOutcome_sound
example := @typeAlias_reject_ordinaryOutcome_sound
example := @typeAlias_ordinaryOutcome_sound
example := @typeAlias_ordinaryOutcomeSpec
example := @typeAlias_exactOutcomeSpec
example := @typeAlias_success_result_unique
example := @typeAlias_reject_output_unique

example {input next : State} {declaration : TypeAliasDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : typeAlias input = .ok declaration next) :
    TypeAliasDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  typeAlias_success_sound diagnosticFree result

example {input next : State} {declaration : TypeAliasDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : typeAlias input = .ok declaration next) :
    TypeAliasDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  typeAlias_success_sound_and_validFor inputValid diagnosticFree result

example {input next : State} {value : TypeExpr}
    (result : TypeAliasInternals.parseAliasValue input = .ok value next) :
    TypeAliasValueOrdinaryParses input.declarativeRemainder value
      next.declarativeRemainder :=
  TypeAliasInternals.parseAliasValue_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : TypeAliasInternals.parseAliasValue input =
      .reject failure rejected) :
    TypeAliasValueRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  TypeAliasInternals.parseAliasValue_reject_ordinaryOutcome_sound result

example {input next : State} {declaration : TypeAliasDecl}
    (result : typeAlias input = .ok declaration next) :
    TypeAliasDeclOrdinaryParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  typeAlias_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : typeAlias input = .reject failure rejected) :
    TypeAliasDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  typeAlias_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserTypeAliasSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeAliasTotalityProperties
/-! External consumers for complete type-alias totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @parseTypeAliasParameters_invariantFreeOnValid
example := @parseTypeAliasParameters_ne_invariant
example := @TypeAliasInternals.parseAliasValue_invariantFreeOnValid
example := @TypeAliasInternals.parseAliasValue_ne_invariant
example := @typeAlias_invariantFreeOnValid_of_type
example := @typeAlias_ne_invariant_of_type
example : Parser.InvariantFreeOnValid typeAlias :=
  typeAlias_invariantFreeOnValid
example := @typeAlias_ne_invariant

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserWhereClauseSoundnessProperties
/-! External consumers for exact predicate-sequence and optional-where outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserWhereClauseSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TypeExprStartToken
example := @TypeExprStartsAt
example := @TypeExprAbsentAt
example := @BarePredicateTailParses
example := @BarePredicateTailRejects
example := @BarePredicateSequenceParses
example := @BarePredicateSequenceRejects
example := @barePredicateSequenceDeterministicOutcomeSpec
example := @barePredicateSequenceExactOutcomeSpec
example := @GroupedPredicateSequenceParses
example := @GroupedPredicateSequenceUnavailable
example := @GroupedPredicateSequenceRejects
example := @groupedPredicateSequenceDeterministicOutcomeSpec
example := @groupedPredicateSequenceExactOutcomeSpec
example := @GroupedPredicateSequenceRejects.no_parse
example := @PredicateSequenceParses
example := @PredicateSequenceRejects
example := @predicateSequenceDeterministicOutcomeSpec
example := @predicateSequenceExactOutcomeSpec
example := @OptionalWhereClauseParses
example := @OptionalWhereClauseRejects
example := @optionalWhereClauseDeterministicOutcomeSpec
example := @optionalWhereClauseExactOutcomeSpec

example := @PredicateInternals.barePredicates_success_sound
example := @PredicateInternals.barePredicates_success_sound_and_validFor
example := @PredicateInternals.barePredicates_reject_sound
example := @PredicateInternals.barePredicates_ordinaryOutcome_sound
example := @PredicateInternals.barePredicates_exactOutcomeSpec
example := @PredicateInternals.barePredicates_success_result_unique
example := @PredicateInternals.barePredicates_reject_output_unique
example := @PredicateInternals.groupedPredicates_success_sound
example := @PredicateInternals.groupedPredicates_success_sound_and_validFor
example := @PredicateInternals.groupedPredicates_reject_sound
example := @PredicateInternals.groupedPredicates_ordinaryOutcome_sound
example := @PredicateInternals.groupedPredicates_exactOutcomeSpec
example := @PredicateInternals.groupedPredicates_success_result_unique
example := @PredicateInternals.groupedPredicates_reject_output_unique
example := @PredicateInternals.predicateSequence_success_sound
example := @PredicateInternals.predicateSequence_success_sound_and_validFor
example := @PredicateInternals.predicateSequence_reject_sound
example := @PredicateInternals.predicateSequence_ordinaryOutcome_sound
example := @PredicateInternals.predicateSequence_exactOutcomeSpec
example := @PredicateInternals.predicateSequence_success_result_unique
example := @PredicateInternals.predicateSequence_reject_output_unique
example := @whereClause_success_sound
example := @whereClause_success_sound_and_validFor
example := @whereClause_reject_sound
example := @whereClause_ordinaryOutcome_sound
example := @whereClause_exactOutcomeSpec
example := @whereClause_success_result_unique
example := @whereClause_reject_output_unique

example {input next : State}
    {predicates : NonemptyDelimitedList Predicate}
    (result : PredicateInternals.predicateSequence input =
      .ok predicates next) :
    PredicateSequenceParses input.declarativeRemainder predicates
      next.declarativeRemainder :=
  PredicateInternals.predicateSequence_success_sound result

example {input next : State}
    {predicates : NonemptyDelimitedList Predicate}
    (inputValid : input.ValidFor)
    (result : PredicateInternals.predicateSequence input =
      .ok predicates next) :
    PredicateSequenceParses input.declarativeRemainder predicates
        next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor Predicate.ValidFor input.file
        predicates :=
  PredicateInternals.predicateSequence_success_sound_and_validFor inputValid
    result

example {input rejected : State} {failure : Failure}
    (result : PredicateInternals.groupedPredicates input =
      .reject failure rejected) :
    GroupedPredicateSequenceRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  PredicateInternals.groupedPredicates_reject_sound result

example {input rejected : State} {failure : Failure}
    (result : PredicateInternals.barePredicates input =
      .reject failure rejected) :
    BarePredicateSequenceRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  PredicateInternals.barePredicates_reject_sound result

example {input rejected : State} {failure : Failure}
    (result : PredicateInternals.predicateSequence input =
      .reject failure rejected) :
    PredicateSequenceRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  PredicateInternals.predicateSequence_reject_sound result

example {input rejected : Remainder}
    (rejection : GroupedPredicateSequenceRejects input rejected) :
    GroupedPredicateSequenceUnavailable input :=
  rejection.no_parse

example :
    DeterministicOutcomeSpec GroupedPredicateSequenceParses
      GroupedPredicateSequenceRejects :=
  groupedPredicateSequenceDeterministicOutcomeSpec

example {input next : State} {clause : Option WhereClause}
    (result : whereClause input = .ok clause next) :
    OptionalWhereClauseParses input.declarativeRemainder clause
      next.declarativeRemainder :=
  whereClause_success_sound result

example {input next : State} {clause : Option WhereClause}
    (inputValid : input.ValidFor)
    (result : whereClause input = .ok clause next) :
    OptionalWhereClauseParses input.declarativeRemainder clause
        next.declarativeRemainder ∧
      Option.ValidFor WhereClause.ValidFor input.file clause :=
  whereClause_success_sound_and_validFor inputValid result

example {input rejected : State} {failure : Failure}
    (result : whereClause input = .reject failure rejected) :
    OptionalWhereClauseRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  whereClause_reject_sound result

end Solcore.Test.SyntaxParserWhereClauseSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserWhereClauseTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserWhereClauseTotalityProperties

open Solcore.Syntax.Parser

example := @whereClause_invariantFreeOnValid
example := @whereClause_ordinary
example := @whereClause_ne_invariant

end Solcore.Test.SyntaxParserWhereClauseTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxSignatureValidity
/-! External consumers for canonical signature source validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @Predicate.ValidFor
example := @WhereClause.ValidFor
example := @FunctionModifiers.ValidFor
example := @ReturnClause.ValidFor
example := @FunctionSignature.ValidFor

example (file : SourceFile) (signature : FunctionSignature)
    (valid : FunctionSignature.ValidFor file signature) :
    signature.span.ValidFor file ∧
      signature.name.span.ValidFor file ∧
      signature.parameters.span.ValidFor file :=
  ⟨valid.1, valid.2.1, valid.2.2.2.2.1⟩

example (file : SourceFile) (clause : ReturnClause)
    (valid : ReturnClause.ValidFor file clause)
    (type : TypeExpr) (member : type ∈ clause.types.elements) :
    clause.span.ValidFor file ∧ TypeExpr.ValidFor file type :=
  ⟨valid.1, valid.2.2 type member⟩

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxTypeDeclarationValidity
/-! External consumers for type and enum declaration validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @TypeAliasDecl.ValidFor
example := @TypeAliasInternals.finishRecoveredType_validFor
example := @TypeAliasInternals.recoverTypeAliasValueAux_validFor
example := @TypeAliasInternals.parseAliasValue_validFor
example := @TypeAliasInternals.parseAliasValue_preservesTokenWindow
example := @TypeAliasInternals.parseAliasValue_preservesTokensOnSuccess
example := @TypeAliasInternals.parseAliasValue_cursorMonotoneOnSuccess
example := @parseTypeAliasParameters_validFor
example := @typeAlias_validFor
example := @typeAlias_preservesTokenWindow
example := @typeAlias_preservesTokensOnSuccess
example := @typeAlias_cursorMonotoneOnSuccess
example := @typeAlias_startsAtCurrentTokenOnSuccess
example := @EnumConstructor.ValidFor
example := @EnumDecl.ValidFor
example := @EnumInternals.enumConstructorFields_validFor
example := @EnumInternals.enumConstructorFields_preservesTokenWindow
example := @EnumInternals.enumConstructorFields_cursorMonotoneOnSuccess
example := @EnumInternals.enumConstructor_validFor
example := @EnumInternals.enumConstructor_preservesTokenWindow
example := @EnumInternals.enumConstructor_preservesTokensOnSuccess
example := @EnumInternals.enumConstructor_cursorMonotoneOnSuccess
example := @EnumInternals.enumConstructor_startsAtCurrentTokenOnSuccess
example := @EnumInternals.closeEnumBody_validFor
example := @EnumInternals.closeEnumBody_preservesTokenWindow
example := @EnumInternals.closeEnumBody_cursorMonotoneOnSuccess
example := @EnumInternals.closeEnumBody_preservesOpeningStartOnSuccess
example := @EnumInternals.enumConstructors_validFor
example := @EnumInternals.enumConstructors_preservesTokenWindow
example := @EnumInternals.enumConstructors_cursorMonotoneOnSuccess
example := @EnumInternals.enumConstructors_preservesOpeningStartOnSuccess
example := @EnumInternals.enumBody_validFor
example := @EnumInternals.enumBody_preservesTokenWindow
example := @EnumInternals.enumBody_preservesTokensOnSuccess
example := @EnumInternals.enumBody_cursorMonotoneOnSuccess
example := @EnumInternals.enumBody_startsAtCurrentTokenOnSuccess
example := @enumDecl_validFor
example := @enumDecl_none_validFor
example := @enumDecl_preservesTokenWindow
example := @enumDecl_preservesTokensOnSuccess
example := @enumDecl_cursorMonotoneOnSuccess
example := @enumDecl_none_startsAtCurrentTokenOnSuccess
example := @enumDecl_some_preservesDerivedStartOnSuccess

example (file : SourceFile) (declaration : TypeAliasDecl)
    (valid : TypeAliasDecl.ValidFor file declaration) :
    declaration.span.ValidFor file ∧
      declaration.value.name.span.ValidFor file ∧
      TypeExpr.ValidFor file declaration.value.value :=
  ⟨valid.1, valid.2.1, valid.2.2.2.2⟩

example (file : SourceFile) (declaration : EnumDecl)
    (valid : EnumDecl.ValidFor file declaration)
    (constructor : EnumConstructor)
    (member : constructor ∈ declaration.value.constructors) :
    declaration.value.bodySpan.ValidFor file ∧
      EnumConstructor.ValidFor file constructor :=
  ⟨valid.2.2.2.2.2.1, valid.2.2.2.2.2.2 constructor member⟩

end Tests
end
