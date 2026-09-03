import Solcore.Syntax.Parser.ExportCanonicalTotalityProperties
import Solcore.Syntax.Parser.ExportDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ImportExactnessProperties
import Solcore.Syntax.Parser.ImportTotalityProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties
import Solcore.Syntax.Parser.PragmaDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PragmaTotalityProperties

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
