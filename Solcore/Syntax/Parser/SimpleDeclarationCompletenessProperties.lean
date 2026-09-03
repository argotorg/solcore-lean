import Solcore.Syntax.Parser.EnumDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.EnumDeclarationTotalityProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties
import Solcore.Syntax.Parser.TraitDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TraitDeclarationTotalityProperties
import Solcore.Syntax.Parser.TypeAliasDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TypeAliasTotalityProperties

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
