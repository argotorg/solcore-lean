import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativePragmaItemsOutcomeProperties
import Solcore.Syntax.DeclarativePragmaOutcomeGrammar

/-! Deterministic and exclusive broad outcomes for complete pragmas. -/

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

/-- Ordinary complete pragma success has one final remainder. -/
theorem PragmaDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.PragmaDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaDeclOrdinaryParses input left afterLeft)
    (rightParsed : PragmaDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftKeywordSpan leftSemicolonSpan leftKeyword leftName leftItems
      leftSemicolon =>
      cases rightParsed with
      | parsed rightKeywordSpan rightSemicolonSpan rightKeyword rightName
          rightItems rightSemicolon =>
          have afterKeywordEq := exactToken_output_unique leftKeyword
            rightKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          have afterItemsEq := leftItems.output_unique rightItems
          subst afterItemsEq
          exact exactToken_output_unique leftSemicolon rightSemicolon

/-- Exact complete pragma rejection excludes every ordinary success. -/
theorem PragmaDeclRejects.disjointOrdinary {input rejected : Remainder}
    (rejection : PragmaDeclRejects input rejected) :
    ¬ ∃ declaration output,
      PragmaDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulKeywordSpan successfulSemicolonSpan successfulKeyword
      successfulName successfulItems successfulSemicolon =>
      cases rejection with
      | keywordMissing keywordAbsent =>
          exact absent_conflicts_exact keywordAbsent successfulKeyword
      | nameRejected rejectedKeywordSpan rejectedKeyword nameRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | itemsRejected rejectedKeywordSpan rejectedKeyword rejectedName
          itemsRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact pragmaItemsDeterministicOutcomeSpec.successRejectDisjoint
            itemsRejected ⟨_, _, successfulItems⟩
      | semicolonMissing rejectedKeywordSpan rejectedKeyword rejectedName
          rejectedItems semicolonAbsent =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterItemsEq := rejectedItems.output_unique successfulItems
          subst afterItemsEq
          exact absent_conflicts_exact semicolonAbsent successfulSemicolon

/-- Complete broad pragmas have deterministic and exclusive ordinary
outcomes. -/
theorem pragmaDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PragmaDeclOrdinaryParses PragmaDeclRejects where
  successOutputUnique := PragmaDeclOrdinaryParses.output_unique
  successRejectDisjoint := PragmaDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
