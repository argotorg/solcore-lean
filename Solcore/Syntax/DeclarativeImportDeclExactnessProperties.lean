import Solcore.Syntax.DeclarativeImportDeclOutcomeProperties
import Solcore.Syntax.DeclarativePlainImportExactnessProperties
import Solcore.Syntax.DeclarativeNamespaceImportExactnessProperties
import Solcore.Syntax.DeclarativeWildcardImportExactnessProperties
import Solcore.Syntax.DeclarativeSelectiveImportExactnessProperties

/-! Exact prioritized import declarations over arbitrary token remainders. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem dispatch_present_conflicts_absent
    {input : Remainder} {offset : Nat} {kind : TokenKind}
    (present : ImportDispatchTokenPresentAt input offset kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex
      (input.cursor + offset) kind) : False :=
  absent present

/-- Import priority, keyword span, and exact payloads determine one located AST. -/
theorem ImportDeclOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : ImportDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImportDeclOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind (ematch := 12) [ExactTokenParses.result_unique,
      dispatch_present_conflicts_absent,
      PlainImportOrdinaryParses.value_unique,
      NamespaceImportOrdinaryParses.value_unique,
      WildcardImportOrdinaryParses.value_unique,
      SelectiveImportOrdinaryParses.value_unique]

/-- Complete import success fixes its exact AST and full remainder. -/
theorem ImportDeclOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : ImportDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImportDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Import dispatch and the selected first failing stage fix one rejection endpoint. -/
theorem ImportDeclRejects.output_unique {input left right : Remainder}
    (leftRejected : ImportDeclRejects input left)
    (rightRejected : ImportDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 12) [absent_conflicts_exact, ExactTokenParses.output_unique,
      dispatch_present_conflicts_absent, PlainImportRejects.output_unique,
      NamespaceImportRejects.output_unique, WildcardImportRejects.output_unique,
      SelectiveImportRejects.output_unique]

/-- Prioritized broad import declarations have fully exact success and rejection. -/
theorem importDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ImportDeclOrdinaryParses ImportDeclRejects where
  toDeterministicOutcomeSpec := importDeclDeterministicOutcomeSpec
  successValueUnique := ImportDeclOrdinaryParses.value_unique
  rejectOutputUnique := ImportDeclRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
