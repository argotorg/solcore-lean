import Solcore.Syntax.DeclarativeImportDeclExactnessProperties
import Solcore.Syntax.Parser.ImportSelectionExactnessProperties
import Solcore.Syntax.Parser.PlainImportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.NamespaceImportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.WildcardImportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SelectiveImportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ImportDeclarationOrdinaryOutcomeSoundnessProperties

/-! Unconditional exact executable outcomes for every complete import form. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export full exactness of plainImport outcomes at the fixed outer start. -/
theorem plainImport_exactOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.PlainImportOrdinaryParses start)
      DeclarativeGrammar.PlainImportRejects :=
  DeclarativeGrammar.plainImportExactOutcomeSpec start

/-- Successful plainImport results agree on their complete AST and remainder. -/
theorem plainImport_success_result_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {left right : ImportDecl}
    (leftResult : ImportInternals.plainImport start input = .ok left leftOutput)
    (rightResult : ImportInternals.plainImport start input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (plainImport_exactOutcomeSpec start).successResultUnique
    (plainImport_success_ordinaryOutcome_sound start leftResult)
    (plainImport_success_ordinaryOutcome_sound start rightResult)

/-- Rejected plainImport results agree on their complete declarative endpoint. -/
theorem plainImport_reject_output_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.plainImport start input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.plainImport start input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (plainImport_exactOutcomeSpec start).rejectOutputUnique
    (plainImport_reject_ordinaryOutcome_sound start leftResult)
    (plainImport_reject_ordinaryOutcome_sound start rightResult)

/-- Re-export full exactness of namespaceImport outcomes at the fixed outer start. -/
theorem namespaceImport_exactOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.NamespaceImportOrdinaryParses start)
      DeclarativeGrammar.NamespaceImportRejects :=
  DeclarativeGrammar.namespaceImportExactOutcomeSpec start

/-- Successful namespaceImport results agree on their complete AST and remainder. -/
theorem namespaceImport_success_result_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {left right : ImportDecl}
    (leftResult : ImportInternals.namespaceImport start input = .ok left leftOutput)
    (rightResult : ImportInternals.namespaceImport start input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (namespaceImport_exactOutcomeSpec start).successResultUnique
    (namespaceImport_success_ordinaryOutcome_sound start leftResult)
    (namespaceImport_success_ordinaryOutcome_sound start rightResult)

/-- Rejected namespaceImport results agree on their complete declarative endpoint. -/
theorem namespaceImport_reject_output_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.namespaceImport start input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.namespaceImport start input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (namespaceImport_exactOutcomeSpec start).rejectOutputUnique
    (namespaceImport_reject_ordinaryOutcome_sound start leftResult)
    (namespaceImport_reject_ordinaryOutcome_sound start rightResult)

/-- Re-export full exactness of wildcardImport outcomes at the fixed outer start. -/
theorem wildcardImport_exactOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.WildcardImportOrdinaryParses start)
      DeclarativeGrammar.WildcardImportRejects :=
  DeclarativeGrammar.wildcardImportExactOutcomeSpec start

/-- Successful wildcardImport results agree on their complete AST and remainder. -/
theorem wildcardImport_success_result_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {left right : ImportDecl}
    (leftResult : ImportInternals.wildcardImport start input = .ok left leftOutput)
    (rightResult : ImportInternals.wildcardImport start input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (wildcardImport_exactOutcomeSpec start).successResultUnique
    (wildcardImport_success_ordinaryOutcome_sound start leftResult)
    (wildcardImport_success_ordinaryOutcome_sound start rightResult)

/-- Rejected wildcardImport results agree on their complete declarative endpoint. -/
theorem wildcardImport_reject_output_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.wildcardImport start input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.wildcardImport start input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (wildcardImport_exactOutcomeSpec start).rejectOutputUnique
    (wildcardImport_reject_ordinaryOutcome_sound start leftResult)
    (wildcardImport_reject_ordinaryOutcome_sound start rightResult)

/-- Re-export full exactness of selectiveImport outcomes at the fixed outer start. -/
theorem selectiveImport_exactOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.SelectiveImportOrdinaryParses start)
      DeclarativeGrammar.SelectiveImportRejects :=
  DeclarativeGrammar.selectiveImportExactOutcomeSpec start

/-- Successful selectiveImport results agree on their complete AST and remainder. -/
theorem selectiveImport_success_result_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {left right : ImportDecl}
    (leftResult : ImportInternals.selectiveImport start input = .ok left leftOutput)
    (rightResult : ImportInternals.selectiveImport start input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectiveImport_exactOutcomeSpec start).successResultUnique
    (selectiveImport_success_ordinaryOutcome_sound start leftResult)
    (selectiveImport_success_ordinaryOutcome_sound start rightResult)

/-- Rejected selectiveImport results agree on their complete declarative endpoint. -/
theorem selectiveImport_reject_output_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.selectiveImport start input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.selectiveImport start input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectiveImport_exactOutcomeSpec start).rejectOutputUnique
    (selectiveImport_reject_ordinaryOutcome_sound start leftResult)
    (selectiveImport_reject_ordinaryOutcome_sound start rightResult)

/-- Re-export full exactness of importDecl outcomes. -/
theorem importDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImportDeclOrdinaryParses
      DeclarativeGrammar.ImportDeclRejects :=
  DeclarativeGrammar.importDeclExactOutcomeSpec

/-- Successful importDecl results agree on their complete AST and remainder. -/
theorem importDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : ImportDecl}
    (leftResult : importDecl input = .ok left leftOutput)
    (rightResult : importDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (importDecl_exactOutcomeSpec).successResultUnique
    (importDecl_success_ordinaryOutcome_sound leftResult)
    (importDecl_success_ordinaryOutcome_sound rightResult)

/-- Rejected importDecl results agree on their complete declarative endpoint. -/
theorem importDecl_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : importDecl input = .reject leftFailure leftOutput)
    (rightResult : importDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (importDecl_exactOutcomeSpec).rejectOutputUnique
    (importDecl_reject_ordinaryOutcome_sound leftResult)
    (importDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
