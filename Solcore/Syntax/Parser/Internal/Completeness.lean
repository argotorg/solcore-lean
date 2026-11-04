import Solcore.Syntax.Parser.Internal.DeclarationTotality
import Solcore.Syntax.Parser.Internal.ContractOutcomeSoundness
import Solcore.Syntax.Parser.Internal.OutcomeCompleteness
import Solcore.Syntax.Parser.Internal.ContractBodySoundness
import Solcore.Syntax.Parser.Internal.DeriveSoundness
import Solcore.Syntax.Parser.Internal.ContractEntryProofs
import Solcore.Syntax.Parser.Internal.ImplProofs
import Solcore.Syntax.Parser.Internal.EnumProofs
import Solcore.Syntax.Parser.Internal.TraitProofs
import Solcore.Syntax.Parser.Internal.TypeAliasProofs
import Solcore.Syntax.Parser.Internal.SignatureSoundness
import Solcore.Syntax.Parser.Internal.TypeTotality
import Solcore.Syntax.Parser.Internal.ModuleTotality
import Solcore.Syntax.Parser.Internal.ExportSoundness
import Solcore.Syntax.Parser.Internal.ImportSoundness
import Solcore.Syntax.Parser.Internal.YulTotality
import Solcore.Syntax.Parser.Internal.YulPublicSoundness
import Solcore.Syntax.Parser.Internal.YulAssignmentSoundness

/-!
Completeness of the parsers of declarations: declarative success and rejection are matched
by execution.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberCompletenessProperties
/-! Complete ordinary grammar correspondence for production contract fields
and attribute-free or derive-aware members. Only input validity is required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Independent production-field success is exactly execution with the same
AST and declarative remainder on a valid input. -/
theorem contractFieldPublic_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ContractField} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractFieldOrdinaryParses
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, contractField expression input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (contractField expression)
    contractFieldPublic_exactOutcomeSpec
    (Solcore.Syntax.Parser.contractField_ne_invariant input inputValid)
    (contractField_success_ordinaryOutcome_sound expression
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      expression_success_ordinary_sound)
    (contractField_reject_ordinaryOutcome_sound expression
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects
      expression_success_ordinary_sound expression_reject_ordinary_sound)

/-- Independent production-field rejection is exactly execution at the same
declarative endpoint; failure diagnostics remain existential. -/
theorem contractFieldPublic_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractFieldRejects
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, contractField expression input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject (contractField expression)
    contractFieldPublic_exactOutcomeSpec
    (Solcore.Syntax.Parser.contractField_ne_invariant input inputValid)
    (contractField_success_ordinaryOutcome_sound expression
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      expression_success_ordinary_sound)
    (contractField_reject_ordinaryOutcome_sound expression
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects
      expression_success_ordinary_sound expression_reject_ordinary_sound)

/-- Attribute-free member grammar success is exactly execution with the same
member AST and declarative remainder. -/
theorem contractMemberCore_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, contractMemberCore input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok contractMemberCore
    contractMemberCore_exactOutcomeSpec
    (productionContractMemberCore_invariantFreeOnValid.ne_invariant
      input inputValid)
    contractMemberCore_success_ordinaryOutcome_sound
    contractMemberCore_reject_ordinaryOutcome_sound

/-- Attribute-free member grammar rejection is exactly execution at the same
declarative endpoint, without fixing failure diagnostics. -/
theorem contractMemberCore_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractMemberCoreRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, contractMemberCore input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject contractMemberCore
    contractMemberCore_exactOutcomeSpec
    (productionContractMemberCore_invariantFreeOnValid.ne_invariant
      input inputValid)
    contractMemberCore_success_ordinaryOutcome_sound
    contractMemberCore_reject_ordinaryOutcome_sound

/-- Derive-aware member grammar success is exactly execution with the same
member AST, including any attached attribute, and declarative remainder. -/
theorem contractMemberWithAttribute_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractMemberOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, contractMemberWithAttribute input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok contractMemberWithAttribute
    contractMemberWithAttribute_exactOutcomeSpec
    (productionContractMemberWithAttribute_ne_invariant input inputValid)
    contractMemberWithAttribute_success_ordinaryOutcome_sound
    contractMemberWithAttribute_reject_ordinaryOutcome_sound

/-- Derive-aware member grammar rejection is exactly execution at the same
declarative endpoint, without fixing failure diagnostics. -/
theorem contractMemberWithAttribute_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractMemberRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, contractMemberWithAttribute input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject contractMemberWithAttribute
    contractMemberWithAttribute_exactOutcomeSpec
    (productionContractMemberWithAttribute_ne_invariant input inputValid)
    contractMemberWithAttribute_success_ordinaryOutcome_sound
    contractMemberWithAttribute_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractBodyCompletenessProperties
/-! Complete contract-body correspondence, preserving the grammar's covered
span and forward member list in the executable body structure. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem contractBody_parserValue_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (fun input (body : ContractBody) output =>
        DeclarativeGrammar.ContractBodyOrdinaryParses
          input body.span body.members output)
      DeclarativeGrammar.ContractBodyRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact contractBody_exactOutcomeSpec.successOutputUnique
      (show DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
        input (left.span, left.members) afterLeft from leftParsed)
      (show DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
        input (right.span, right.members) afterRight from rightParsed)
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨body, output, parsed⟩
    exact contractBody_exactOutcomeSpec.successRejectDisjoint rejection
      ⟨(body.span, body.members), output, parsed⟩
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    have bodyEq := contractBody_exactOutcomeSpec.successValueUnique
      (show DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
        input (left.span, left.members) afterLeft from leftParsed)
      (show DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
        input (right.span, right.members) afterRight from rightParsed)
    cases left
    cases right
    simp_all
  rejectOutputUnique := contractBody_exactOutcomeSpec.rejectOutputUnique

/-- Independent body success corresponds exactly to execution with the same
covered span, source-order members, and declarative remainder. -/
theorem contractBody_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {body : ContractBody} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractBodyOrdinaryParses
      input.declarativeRemainder body.span body.members remainder ↔
      ∃ output, contractBody input = .ok body output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok contractBody
    contractBody_parserValue_exactOutcomeSpec
    (productionContractBody_ne_invariant input inputValid)
    contractBody_success_ordinaryOutcome_sound
    contractBody_reject_ordinaryOutcome_sound

/-- Independent body rejection corresponds exactly to execution at the same
declarative endpoint, without identifying diagnostics or complete states. -/
theorem contractBody_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractBodyRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, contractBody input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject contractBody
    contractBody_parserValue_exactOutcomeSpec
    (productionContractBody_ne_invariant input inputValid)
    contractBody_success_ordinaryOutcome_sound
    contractBody_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractDeclarationCompletenessProperties
/-! Complete ordinary grammar correspondence for contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Contract grammar success is exactly execution with the same AST and
declarative remainder on a valid input. -/
theorem contractDecl_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ContractDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, contractDecl input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok contractDecl contractDecl_exactOutcomeSpec
    (contractDecl_invariantFreeOnValid.ne_invariant input inputValid)
    contractDecl_success_ordinaryOutcome_sound contractDecl_reject_ordinaryOutcome_sound

/-- Contract grammar rejection is exactly execution at the same
declarative endpoint on a valid input. -/
theorem contractDecl_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractDeclRejects input.declarativeRemainder rejected ↔
      ∃ failure output, contractDecl input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject contractDecl contractDecl_exactOutcomeSpec
    (contractDecl_invariantFreeOnValid.ne_invariant input inputValid)
    contractDecl_success_ordinaryOutcome_sound contractDecl_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberRecoveryCompletenessProperties
/-! Complete standalone contract-member recovery correspondence for arbitrary
input states; recovery's production fuel needs no validity premise. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Independent recovery success is exactly execution with the same recovered
member AST and declarative remainder, even without input validity. -/
theorem recoverContractMember_ordinary_success_iff
    {input : State} {value : ContractMember}
    {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractMemberRecoveryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, recoverContractMember input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok recoverContractMember
    recoverContractMember_exactOutcomeSpec
    (recoverContractMember_ne_invariant input)
    recoverContractMember_success_ordinaryOutcome_sound
    recoverContractMember_reject_ordinaryOutcome_sound

/-- Independent recovery rejection is exactly execution at the same
declarative endpoint, leaving diagnostics existential. -/
theorem recoverContractMember_ordinary_reject_iff
    {input : State} {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractMemberRecoveryRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, recoverContractMember input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject recoverContractMember
    recoverContractMember_exactOutcomeSpec
    (recoverContractMember_ne_invariant input)
    recoverContractMember_success_ordinaryOutcome_sound
    recoverContractMember_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveCompletenessProperties
/-! Complete derive-target and normal, recovered, and public attribute outcomes.
Target and recovery correspondence needs no state-validity assumption. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Independent deriveTarget success corresponds exactly to execution with the
same AST and declarative remainder on every input. -/
theorem deriveTarget_ordinary_success_iff
    {input : State}
    {value : DeriveTarget} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveTargetParses
      input.declarativeRemainder value remainder ↔
      ∃ output, deriveTarget input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok deriveTarget deriveTarget_exactOutcomeSpec
    (deriveTarget_ne_invariant input)
    deriveTarget_success_ordinaryOutcome_sound deriveTarget_reject_ordinaryOutcome_sound

/-- Independent deriveTarget rejection corresponds exactly to execution at the
same declarative endpoint on every input, leaving diagnostics existential. -/
theorem deriveTarget_ordinary_reject_iff
    {input : State}
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveTargetRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, deriveTarget input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject deriveTarget deriveTarget_exactOutcomeSpec
    (deriveTarget_ne_invariant input)
    deriveTarget_success_ordinaryOutcome_sound deriveTarget_reject_ordinaryOutcome_sound

/-- Independent deriveAttributeValid success corresponds exactly to execution with the
same AST and declarative remainder on a valid input. -/
theorem deriveAttributeValid_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveAttributeParses
      input.declarativeRemainder value remainder ↔
      ∃ output, DeriveAttributeInternals.valid input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok DeriveAttributeInternals.valid deriveAttributeValid_exactOutcomeSpec
    (DeriveAttributeInternals.valid_ne_invariant input inputValid)
    deriveAttributeValid_success_ordinaryOutcome_sound deriveAttributeValid_reject_ordinaryOutcome_sound

/-- Independent deriveAttributeValid rejection corresponds exactly to execution at the
same declarative endpoint on a valid input, leaving diagnostics existential. -/
theorem deriveAttributeValid_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveAttributeValidRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, DeriveAttributeInternals.valid input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject DeriveAttributeInternals.valid deriveAttributeValid_exactOutcomeSpec
    (DeriveAttributeInternals.valid_ne_invariant input inputValid)
    deriveAttributeValid_success_ordinaryOutcome_sound deriveAttributeValid_reject_ordinaryOutcome_sound

/-- Independent deriveAttributeRecovered success corresponds exactly to execution with the
same AST and declarative remainder on every input. -/
theorem deriveAttributeRecovered_ordinary_success_iff
    {input : State}
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveAttributeRecoveredParses
      input.declarativeRemainder value remainder ↔
      ∃ output, DeriveAttributeInternals.recovered input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok DeriveAttributeInternals.recovered deriveAttributeRecovered_exactOutcomeSpec
    (DeriveAttributeInternals.recovered_ne_invariant input)
    deriveAttributeRecovered_success_ordinaryOutcome_sound deriveAttributeRecovered_reject_ordinaryOutcome_sound

/-- Independent deriveAttributeRecovered rejection corresponds exactly to execution at the
same declarative endpoint on every input, leaving diagnostics existential. -/
theorem deriveAttributeRecovered_ordinary_reject_iff
    {input : State}
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveAttributeRecoveredRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, DeriveAttributeInternals.recovered input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject DeriveAttributeInternals.recovered deriveAttributeRecovered_exactOutcomeSpec
    (DeriveAttributeInternals.recovered_ne_invariant input)
    deriveAttributeRecovered_success_ordinaryOutcome_sound deriveAttributeRecovered_reject_ordinaryOutcome_sound

/-- Independent deriveAttribute success corresponds exactly to execution with the
same AST and declarative remainder on a valid input. -/
theorem deriveAttribute_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveAttributeOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, deriveAttribute input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok deriveAttribute deriveAttribute_exactOutcomeSpec
    (deriveAttribute_ne_invariant input inputValid)
    deriveAttribute_success_ordinaryOutcome_sound deriveAttribute_reject_ordinaryOutcome_sound

/-- Independent deriveAttribute rejection corresponds exactly to execution at the
same declarative endpoint on a valid input, leaving diagnostics existential. -/
theorem deriveAttribute_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveAttributeRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, deriveAttribute input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject deriveAttribute deriveAttribute_exactOutcomeSpec
    (deriveAttribute_ne_invariant input inputValid)
    deriveAttribute_success_ordinaryOutcome_sound deriveAttribute_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionDeclarationCompletenessProperties
/-! Complete ordinary grammar correspondence for named functions and
contract entry declarations on valid parser states. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- At either function location, grammar success is exactly execution with
the same function AST and declarative remainder on a valid input. -/
theorem functionDecl_ordinary_success_iff (location : FunctionLocation)
    {input : State} (inputValid : input.ValidFor)
    {value : FunctionDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.FunctionDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, functionDecl location input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (functionDecl location) functionDecl_exactOutcomeSpec
    ((functionDecl_invariantFreeOnValid location).ne_invariant input inputValid)
    (functionDecl_success_ordinaryOutcome_sound location)
    (functionDecl_reject_ordinaryOutcome_sound location)

/-- At either function location, grammar rejection is exactly execution at
the same declarative endpoint on a valid input. -/
theorem functionDecl_ordinary_reject_iff (location : FunctionLocation)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.FunctionDeclRejects input.declarativeRemainder rejected ↔
      ∃ failure output, functionDecl location input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject (functionDecl location) functionDecl_exactOutcomeSpec
    ((functionDecl_invariantFreeOnValid location).ne_invariant input inputValid)
    (functionDecl_success_ordinaryOutcome_sound location)
    (functionDecl_reject_ordinaryOutcome_sound location)

/-- Constructor grammar success is exactly execution with the same AST and
declarative remainder on a valid input. -/
theorem constructorDecl_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ConstructorDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ConstructorDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, constructorDecl input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok constructorDecl constructorDecl_exactOutcomeSpec
    (constructorDecl_invariantFreeOnValid.ne_invariant input inputValid)
    constructorDecl_success_ordinaryOutcome_sound constructorDecl_reject_ordinaryOutcome_sound

/-- Constructor grammar rejection is exactly execution at the same
declarative endpoint on a valid input. -/
theorem constructorDecl_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ConstructorDeclRejects input.declarativeRemainder rejected ↔
      ∃ failure output, constructorDecl input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject constructorDecl constructorDecl_exactOutcomeSpec
    (constructorDecl_invariantFreeOnValid.ne_invariant input inputValid)
    constructorDecl_success_ordinaryOutcome_sound constructorDecl_reject_ordinaryOutcome_sound

/-- Fallback grammar success is exactly execution with the same AST and
declarative remainder on a valid input. -/
theorem fallbackDecl_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : FallbackDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.FallbackDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, fallbackDecl input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok fallbackDecl fallbackDecl_exactOutcomeSpec
    (fallbackDecl_invariantFreeOnValid.ne_invariant input inputValid)
    fallbackDecl_success_ordinaryOutcome_sound fallbackDecl_reject_ordinaryOutcome_sound

/-- Fallback grammar rejection is exactly execution at the same
declarative endpoint on a valid input. -/
theorem fallbackDecl_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.FallbackDeclRejects input.declarativeRemainder rejected ↔
      ∃ failure output, fallbackDecl input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject fallbackDecl fallbackDecl_exactOutcomeSpec
    (fallbackDecl_invariantFreeOnValid.ne_invariant input inputValid)
    fallbackDecl_success_ordinaryOutcome_sound fallbackDecl_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImplementationDeclarationCompletenessProperties
/-! Complete ordinary grammar correspondence for implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Implementation grammar success is exactly execution with the same AST
and declarative remainder on a valid input. -/
theorem implDecl_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ImplDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ImplDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, implDecl input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok implDecl implDecl_exactOutcomeSpec
    (implDecl_invariantFreeOnValid.ne_invariant input inputValid)
    implDecl_success_ordinaryOutcome_sound implDecl_reject_ordinaryOutcome_sound

/-- Implementation grammar rejection is exactly execution at the same
declarative endpoint on a valid input. -/
theorem implDecl_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ImplDeclRejects input.declarativeRemainder rejected ↔
      ∃ failure output, implDecl input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject implDecl implDecl_exactOutcomeSpec
    (implDecl_invariantFreeOnValid.ne_invariant input inputValid)
    implDecl_success_ordinaryOutcome_sound implDecl_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SimpleDeclarationCompletenessProperties
/-! Complete syntax-only correspondence for type aliases, enums, and traits.
The supplied enum derive attribute is fixed but needs no provenance premise. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Independent typeAlias success corresponds exactly to execution with the
same AST and declarative remainder on a valid input. -/
theorem typeAlias_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : TypeAliasDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, typeAlias input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok typeAlias typeAlias_exactOutcomeSpec
    (typeAlias_ne_invariant input inputValid)
    typeAlias_success_ordinaryOutcome_sound typeAlias_reject_ordinaryOutcome_sound

/-- Independent typeAlias rejection corresponds exactly to execution at the
same declarative endpoint on a valid input, leaving diagnostics existential. -/
theorem typeAlias_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TypeAliasDeclRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, typeAlias input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject typeAlias typeAlias_exactOutcomeSpec
    (typeAlias_ne_invariant input inputValid)
    typeAlias_success_ordinaryOutcome_sound typeAlias_reject_ordinaryOutcome_sound

/-- Independent enumDecl success corresponds exactly to execution with the
same AST and declarative remainder on a valid input. -/
theorem enumDecl_ordinary_success_iff (deriveAttribute : Option DeriveAttribute)
    {input : State} (inputValid : input.ValidFor)
    {value : EnumDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute
      input.declarativeRemainder value remainder ↔
      ∃ output, enumDecl deriveAttribute input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (enumDecl deriveAttribute) (enumDecl_exactOutcomeSpec deriveAttribute)
    (enumDecl_ne_invariant deriveAttribute input inputValid)
    (enumDecl_success_ordinaryOutcome_sound deriveAttribute) (enumDecl_reject_ordinaryOutcome_sound deriveAttribute)

/-- Independent enumDecl rejection corresponds exactly to execution at the
same declarative endpoint on a valid input, leaving diagnostics existential. -/
theorem enumDecl_ordinary_reject_iff (deriveAttribute : Option DeriveAttribute)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.EnumDeclRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, enumDecl deriveAttribute input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject (enumDecl deriveAttribute) (enumDecl_exactOutcomeSpec deriveAttribute)
    (enumDecl_ne_invariant deriveAttribute input inputValid)
    (enumDecl_success_ordinaryOutcome_sound deriveAttribute) (enumDecl_reject_ordinaryOutcome_sound deriveAttribute)

/-- Independent traitDecl success corresponds exactly to execution with the
same AST and declarative remainder on a valid input. -/
theorem traitDecl_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : TraitDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TraitDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, traitDecl input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok traitDecl traitDecl_exactOutcomeSpec
    (traitDecl_ne_invariant input inputValid)
    traitDecl_success_ordinaryOutcome_sound traitDecl_reject_ordinaryOutcome_sound

/-- Independent traitDecl rejection corresponds exactly to execution at the
same declarative endpoint on a valid input, leaving diagnostics existential. -/
theorem traitDecl_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TraitDeclRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, traitDecl input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject traitDecl traitDecl_exactOutcomeSpec
    (traitDecl_ne_invariant input inputValid)
    traitDecl_success_ordinaryOutcome_sound traitDecl_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTypeCompletenessProperties
/-! Complete ordinary grammar correspondence for public Core types. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public type grammar success is exactly execution with the same type AST
and declarative remainder on a valid input. -/
theorem typeExpr_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : TypeExpr} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TypeExprOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, typeExpr input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok typeExpr typeExpr_exactOutcomeSpec
    (typeExpr_invariantFreeOnValid.ne_invariant input inputValid)
    typeExpr_success_sound typeExpr_reject_sound

/-- Public type grammar rejection is exactly execution at the same
declarative endpoint on a valid input. -/
theorem typeExpr_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TypeExprRejects input.declarativeRemainder rejected ↔
      ∃ failure output, typeExpr input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject typeExpr typeExpr_exactOutcomeSpec
    (typeExpr_invariantFreeOnValid.ne_invariant input inputValid)
    typeExpr_success_sound typeExpr_reject_sound

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ModuleDeclarationCompletenessProperties
/-! Complete ordinary grammar correspondence for module declarations.
Only import and export need valid-state totality; pragmas are invariant-free
on every state. Results identify ASTs and remainders, not diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Independent importDecl success agrees with execution on valid inputs,
preserving the complete AST and declarative remainder. -/
theorem importDecl_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ImportDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ImportDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, importDecl input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok importDecl importDecl_exactOutcomeSpec
    (importDecl_ne_invariant input inputValid)
    importDecl_success_ordinaryOutcome_sound importDecl_reject_ordinaryOutcome_sound

/-- Independent importDecl rejection agrees with execution on valid inputs
at the declarative endpoint, without identifying failure payloads. -/
theorem importDecl_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ImportDeclRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, importDecl input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject importDecl importDecl_exactOutcomeSpec
    (importDecl_ne_invariant input inputValid)
    importDecl_success_ordinaryOutcome_sound importDecl_reject_ordinaryOutcome_sound

/-- Independent exportDecl success agrees with execution on valid inputs,
preserving the complete AST and declarative remainder. -/
theorem exportDecl_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ExportDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ExportDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, exportDecl input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok exportDecl exportDecl_exactOutcomeSpec
    (exportDecl_ne_invariant input inputValid)
    exportDecl_success_ordinaryOutcome_sound exportDecl_reject_ordinaryOutcome_sound

/-- Independent exportDecl rejection agrees with execution on valid inputs
at the declarative endpoint, without identifying failure payloads. -/
theorem exportDecl_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ExportDeclRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, exportDecl input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject exportDecl exportDecl_exactOutcomeSpec
    (exportDecl_ne_invariant input inputValid)
    exportDecl_success_ordinaryOutcome_sound exportDecl_reject_ordinaryOutcome_sound

/-- Independent pragmaDecl success agrees with execution without a state-validity premise,
preserving the complete AST and declarative remainder. -/
theorem pragmaDecl_ordinary_success_iff
    {input : State}
    {value : PragmaDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.PragmaDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, pragmaDecl input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok pragmaDecl pragmaDecl_exactOutcomeSpec
    (pragmaDecl_ne_invariant input)
    pragmaDecl_success_ordinaryOutcome_sound pragmaDecl_reject_ordinaryOutcome_sound

/-- Independent pragmaDecl rejection agrees with execution without a state-validity premise
at the declarative endpoint, without identifying failure payloads. -/
theorem pragmaDecl_ordinary_reject_iff
    {input : State}
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.PragmaDeclRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, pragmaDecl input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject pragmaDecl pragmaDecl_exactOutcomeSpec
    (pragmaDecl_ne_invariant input)
    pragmaDecl_success_ordinaryOutcome_sound pragmaDecl_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulPublicCompletenessProperties
/-! Complete public Yul grammar correspondence on valid parser states. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public Yul expression grammar success is exactly execution with the same
AST and declarative remainder, including diagnosed recovery. -/
theorem yulExpression_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : YulExpr} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulExpressionOrdinaryParses
        input.declarativeRemainder value remainder ↔
      ∃ output, yulExpression input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok yulExpression yulExpression_publicExactOutcomeSpec
    (yulExpression_ne_invariant input inputValid)
    yulExpression_success_ordinary_sound yulExpression_reject_public_sound

/-- Public Yul expression rejection is exactly execution at the same declarative
endpoint, without fixing the failure payload or diagnostic accumulator. -/
theorem yulExpression_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulExpressionPublicRejects input.declarativeRemainder rejected ↔
      ∃ failure output, yulExpression input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject yulExpression yulExpression_publicExactOutcomeSpec
    (yulExpression_ne_invariant input inputValid)
    yulExpression_success_ordinary_sound yulExpression_reject_public_sound

/-- The equivalent concrete expression boundary has the same rejection completeness. -/
theorem yulExpression_boundary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder rejected ↔
      ∃ failure output, yulExpression input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  DeclarativeGrammar.yulExpressionPublicRejects_iff.symm.trans
    (yulExpression_ordinary_reject_iff inputValid)

/-- Public Yul statement grammar success is exactly execution with the same
located statement and complete declarative remainder. -/
theorem yulStatement_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : YulStmt} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulStatementOrdinaryParses
        input.declarativeRemainder value remainder ↔
      ∃ output, yulStatement input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok yulStatement yulStatement_publicExactOutcomeSpec
    (yulStatement_ne_invariant input inputValid)
    yulStatement_success_ordinary_sound yulStatement_reject_ordinary_sound

/-- Public Yul statement rejection is exactly execution at its declarative endpoint. -/
theorem yulStatement_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulStatementPublicRejects input.declarativeRemainder rejected ↔
      ∃ failure output, yulStatement input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject yulStatement yulStatement_publicExactOutcomeSpec
    (yulStatement_ne_invariant input inputValid)
    yulStatement_success_ordinary_sound yulStatement_reject_ordinary_sound

/-- The equivalent concrete statement boundary has the same rejection completeness. -/
theorem yulStatement_boundary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulStatementRejects input.declarativeRemainder rejected ↔
      ∃ failure output, yulStatement input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  DeclarativeGrammar.yulStatementPublicRejects_iff.symm.trans
    (yulStatement_ordinary_reject_iff inputValid)

private theorem yulBody_parsedBlock_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (fun input (value : YulParsedBlock) output =>
        DeclarativeGrammar.YulBodyOrdinaryParses input value.span value.body output)
      DeclarativeGrammar.YulBodyRejects where
  successOutputUnique := fun left right =>
    (DeclarativeGrammar.YulBodyOrdinaryParses.result_unique left right).2.2
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨body, output, parsed⟩
    exact yulBody_exactOutcomeSpec.successRejectDisjoint rejection
      ⟨{ span := body.span, body := body.body }, output, parsed⟩
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    have resultEq := DeclarativeGrammar.YulBodyOrdinaryParses.result_unique
      leftParsed rightParsed
    cases left
    cases right
    simp_all
  rejectOutputUnique := yulBody_exactOutcomeSpec.rejectOutputUnique

/-- The public braced Yul block grammar is exactly execution with the same
span, forward statement list, and complete declarative remainder. -/
theorem yulBody_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : YulParsedBlock} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulBodyOrdinaryParses
        input.declarativeRemainder value.span value.body remainder ↔
      ∃ output, yulBody input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok yulBody yulBody_parsedBlock_exactOutcomeSpec
    (yulBody_ne_invariant input inputValid)
    yulBody_success_ordinary_sound yulBody_reject_ordinary_sound

/-- Public Yul block rejection is exactly execution at the grammar's first-failure
endpoint; no equality of failure contents or whole states is claimed. -/
theorem yulBody_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulBodyRejects input.declarativeRemainder rejected ↔
      ∃ failure output, yulBody input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject yulBody yulBody_parsedBlock_exactOutcomeSpec
    (yulBody_ne_invariant input inputValid)
    yulBody_success_ordinary_sound yulBody_reject_ordinary_sound

end Solcore.Syntax.Parser
end
