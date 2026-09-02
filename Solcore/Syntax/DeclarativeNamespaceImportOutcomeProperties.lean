import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeImportTerminatorOutcomeProperties
import Solcore.Syntax.DeclarativeModulePathOutcomeProperties
import Solcore.Syntax.DeclarativeNamespaceImportOutcomeGrammar

/-! Deterministic and exclusive broad namespace-import helper outcomes. -/

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

private theorem importTerminator_cross_output_unique
    {leftLast rightLast : SourceSpan} {input : Remainder}
    {leftSpan rightSpan : SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : ImportTerminatorOrdinaryParses leftLast input leftSpan
      afterLeft)
    (rightParsed : ImportTerminatorOrdinaryParses rightLast input rightSpan
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | semicolon leftSemicolonSpan leftSemicolon =>
      cases rightParsed with
      | semicolon rightSemicolonSpan rightSemicolon =>
          exact exactToken_output_unique leftSemicolon rightSemicolon
      | recovered rightAbsent rightStarts =>
          exact False.elim
            (absent_conflicts_exact rightAbsent leftSemicolon)
  | recovered leftAbsent leftStarts =>
      cases rightParsed with
      | semicolon rightSemicolonSpan rightSemicolon =>
          exact False.elim
            (absent_conflicts_exact leftAbsent rightSemicolon)
      | recovered rightAbsent rightStarts => rfl

/-- Ordinary namespace-import helper success has one final remainder. -/
theorem NamespaceImportOrdinaryParses.output_unique (start : SourceSpan)
    {input : Remainder} {left right : Syntax.ImportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : NamespaceImportOrdinaryParses start input left afterLeft)
    (rightParsed : NamespaceImportOrdinaryParses start input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftStarSpan leftAsSpan leftFromSpan leftEndSpan leftStar leftAs
        leftAlias leftFrom leftPath leftTerminator =>
      cases rightParsed with
      | parsed rightStarSpan rightAsSpan rightFromSpan rightEndSpan rightStar
            rightAs rightAlias rightFrom rightPath rightTerminator =>
          have afterStarEq := exactToken_output_unique leftStar rightStar
          subst afterStarEq
          have afterAsEq := exactToken_output_unique leftAs rightAs
          subst afterAsEq
          have afterAliasEq := IdentifierParses.output_unique leftAlias
            rightAlias
          subst afterAliasEq
          have afterFromEq := exactToken_output_unique leftFrom rightFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique leftPath
            rightPath
          subst afterPathEq
          exact importTerminator_cross_output_unique leftTerminator
            rightTerminator

/-- Exact namespace-import rejection excludes every broad ordinary success. -/
theorem NamespaceImportRejects.disjointOrdinary (start : SourceSpan)
    {input rejected : Remainder}
    (rejection : NamespaceImportRejects input rejected) :
    ¬ ∃ declaration output,
      NamespaceImportOrdinaryParses start input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulStarSpan successfulAsSpan successfulFromSpan
        successfulEndSpan successfulStar successfulAs successfulAlias
        successfulFrom successfulPath successfulTerminator =>
      cases rejection with
      | starMissing starAbsent =>
          exact absent_conflicts_exact starAbsent successfulStar
      | asMissing rejectedStarSpan rejectedStar asAbsent =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          exact absent_conflicts_exact asAbsent successfulAs
      | aliasRejected rejectedStarSpan rejectedAsSpan rejectedStar rejectedAs
            aliasRejected =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterAsEq := exactToken_output_unique rejectedAs successfulAs
          subst afterAsEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            aliasRejected ⟨_, _, successfulAlias⟩
      | fromMissing rejectedStarSpan rejectedAsSpan rejectedStar rejectedAs
            rejectedAlias fromAbsent =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterAsEq := exactToken_output_unique rejectedAs successfulAs
          subst afterAsEq
          have afterAliasEq := IdentifierParses.output_unique rejectedAlias
            successfulAlias
          subst afterAliasEq
          exact absent_conflicts_exact fromAbsent successfulFrom
      | pathRejected rejectedStarSpan rejectedAsSpan rejectedFromSpan
            rejectedStar rejectedAs rejectedAlias rejectedFrom pathRejected =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterAsEq := exactToken_output_unique rejectedAs successfulAs
          subst afterAsEq
          have afterAliasEq := IdentifierParses.output_unique rejectedAlias
            successfulAlias
          subst afterAliasEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          exact modulePathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, successfulPath⟩
      | terminatorRejected rejectedStarSpan rejectedAsSpan rejectedFromSpan
            rejectedStar rejectedAs rejectedAlias rejectedFrom rejectedPath
            terminatorRejected =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterAsEq := exactToken_output_unique rejectedAs successfulAs
          subst afterAsEq
          have afterAliasEq := IdentifierParses.output_unique rejectedAlias
            successfulAlias
          subst afterAliasEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique
            rejectedPath successfulPath
          subst afterPathEq
          exact ImportTerminatorRejects.disjointOrdinary _
            terminatorRejected ⟨_, _, successfulTerminator⟩

/-- Namespace-import helpers have deterministic and exclusive broad ordinary
outcomes for each fixed declaration start span. -/
theorem namespaceImportDeterministicOutcomeSpec (start : SourceSpan) :
    DeterministicOutcomeSpec (NamespaceImportOrdinaryParses start)
      NamespaceImportRejects where
  successOutputUnique := NamespaceImportOrdinaryParses.output_unique start
  successRejectDisjoint := NamespaceImportRejects.disjointOrdinary start

end Solcore.Syntax.DeclarativeGrammar
