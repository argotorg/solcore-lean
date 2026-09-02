import Solcore.Syntax.DeclarativeExportDeclOutcomeGrammar
import Solcore.Syntax.DeclarativeLocalExportOutcomeProperties
import Solcore.Syntax.DeclarativePathExportOutcomeProperties

/-! Deterministic and exclusive broad outcomes for complete exports. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem exactToken_span_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftSpan = rightSpan := by
  have tokenEq :
      ({ span := leftSpan, value := kind } : Token) =
        { span := rightSpan, value := kind } :=
    Option.some.inj (leftParsed.1.2.symm.trans rightParsed.1.2)
  exact congrArg (fun token : Token => token.span) tokenEq

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem localExport_leftBrace_present {start : SourceSpan}
    {input : Remainder} {declaration : Syntax.ExportDecl}
    {output : Remainder}
    (parsed : LocalExportOrdinaryParses start input declaration output) :
    ExportDeclLeftBracePresentAt input := by
  rcases parsed with ⟨items, afterItems, itemsParsed, finishParsed⟩
  cases itemsParsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

private theorem ExportDeclOrdinaryParses.to_dispatch
    {input : Remainder} {declaration : Syntax.ExportDecl}
    {output : Remainder}
    (parsed : ExportDeclOrdinaryParses input declaration output) :
    ∃ keywordSpan afterKeyword,
      ExactTokenParses (.keyword .exportKw) input keywordSpan afterKeyword ∧
      ((ExportDeclLeftBracePresentAt afterKeyword ∧
          LocalExportOrdinaryParses keywordSpan afterKeyword declaration
            output) ∨
        (TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
            afterKeyword.cursor (.symbol .leftBrace) ∧
          PathExportOrdinaryParses keywordSpan afterKeyword declaration
            output)) := by
  cases parsed with
  | ofLocal parsed =>
      unfold LocalExportDeclParses at parsed
      rcases parsed with ⟨keywordSpan, keywordToken, payloadParsed⟩
      refine ⟨keywordSpan, { input with cursor := input.cursor + 1 },
        ⟨keywordToken, rfl⟩, Or.inl ⟨?_, payloadParsed⟩⟩
      exact localExport_leftBrace_present payloadParsed
  | ofModule parsed =>
      unfold ModuleExportDeclParses at parsed
      rcases parsed with
        ⟨keywordSpan, keywordToken, leftBraceAbsent, payloadParsed⟩
      exact ⟨keywordSpan, { input with cursor := input.cursor + 1 },
        ⟨keywordToken, rfl⟩,
        Or.inr ⟨leftBraceAbsent, .module payloadParsed⟩⟩
  | ofModuleAs parsed =>
      unfold ModuleAsExportDeclParses at parsed
      rcases parsed with
        ⟨keywordSpan, keywordToken, leftBraceAbsent, payloadParsed⟩
      exact ⟨keywordSpan, { input with cursor := input.cursor + 1 },
        ⟨keywordToken, rfl⟩,
        Or.inr ⟨leftBraceAbsent, .moduleAs payloadParsed⟩⟩
  | ofItemsFrom parsed =>
      unfold ItemsFromExportDeclParses at parsed
      rcases parsed with
        ⟨keywordSpan, keywordToken, leftBraceAbsent, payloadParsed⟩
      exact ⟨keywordSpan, { input with cursor := input.cursor + 1 },
        ⟨keywordToken, rfl⟩,
        Or.inr ⟨leftBraceAbsent, .itemsFrom payloadParsed⟩⟩

private theorem leftBrace_conflict_after_keyword
    {input leftAfter rightAfter : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftKeyword : ExactTokenParses (.keyword .exportKw) input leftSpan
      leftAfter)
    (rightKeyword : ExactTokenParses (.keyword .exportKw) input rightSpan
      rightAfter)
    (present : ExportDeclLeftBracePresentAt leftAfter)
    (absent : TokenKindAbsentAt rightAfter.tokens rightAfter.endIndex
      rightAfter.cursor (.symbol .leftBrace)) : False := by
  have afterKeywordEq := exactToken_output_unique leftKeyword rightKeyword
  subst afterKeywordEq
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩

private theorem payload_output_unique_after_keyword
    {payload : SourceSpan → Remainder → Syntax.ExportDecl →
      Remainder → Prop}
    {payloadRejects : Remainder → Remainder → Prop}
    (outcomes : ∀ start,
      DeterministicOutcomeSpec (payload start) payloadRejects)
    {input leftAfter rightAfter leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan} {left right : Syntax.ExportDecl}
    (leftKeyword : ExactTokenParses (.keyword .exportKw) input leftSpan
      leftAfter)
    (rightKeyword : ExactTokenParses (.keyword .exportKw) input rightSpan
      rightAfter)
    (leftPayload : payload leftSpan leftAfter left leftOutput)
    (rightPayload : payload rightSpan rightAfter right rightOutput) :
    leftOutput = rightOutput := by
  have afterKeywordEq := exactToken_output_unique leftKeyword rightKeyword
  subst afterKeywordEq
  have keywordSpanEq := exactToken_span_unique leftKeyword rightKeyword
  subst keywordSpanEq
  exact (outcomes leftSpan).successOutputUnique leftPayload rightPayload

private theorem payload_reject_disjoint_after_keyword
    {payload : SourceSpan → Remainder → Syntax.ExportDecl →
      Remainder → Prop}
    {payloadRejects : Remainder → Remainder → Prop}
    (outcomes : ∀ start,
      DeterministicOutcomeSpec (payload start) payloadRejects)
    {input rejectedAfter successfulAfter rejected output : Remainder}
    {rejectedSpan successfulSpan : SourceSpan}
    {declaration : Syntax.ExportDecl}
    (rejectedKeyword : ExactTokenParses (.keyword .exportKw) input
      rejectedSpan rejectedAfter)
    (successfulKeyword : ExactTokenParses (.keyword .exportKw) input
      successfulSpan successfulAfter)
    (payloadRejected : payloadRejects rejectedAfter rejected)
    (payloadParsed : payload successfulSpan successfulAfter declaration
      output) : False := by
  have afterKeywordEq := exactToken_output_unique rejectedKeyword
    successfulKeyword
  subst afterKeywordEq
  have keywordSpanEq := exactToken_span_unique rejectedKeyword
    successfulKeyword
  subst keywordSpanEq
  exact (outcomes rejectedSpan).successRejectDisjoint payloadRejected
    ⟨_, _, payloadParsed⟩

/-- Complete broad export success has one final remainder. -/
theorem ExportDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportDeclOrdinaryParses input left afterLeft)
    (rightParsed : ExportDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed.to_dispatch with
    ⟨leftSpan, leftAfterKeyword, leftKeyword, leftBranch⟩
  rcases rightParsed.to_dispatch with
    ⟨rightSpan, rightAfterKeyword, rightKeyword, rightBranch⟩
  cases leftBranch with
  | inl leftLocal =>
      cases rightBranch with
      | inl rightLocal =>
          exact payload_output_unique_after_keyword
            localExportDeterministicOutcomeSpec leftKeyword rightKeyword
              leftLocal.2 rightLocal.2
      | inr rightPath =>
          exact False.elim (leftBrace_conflict_after_keyword leftKeyword
            rightKeyword leftLocal.1 rightPath.1)
  | inr leftPath =>
      cases rightBranch with
      | inl rightLocal =>
          exact False.elim (leftBrace_conflict_after_keyword rightKeyword
            leftKeyword rightLocal.1 leftPath.1)
      | inr rightPath =>
          exact payload_output_unique_after_keyword
            pathExportDeterministicOutcomeSpec leftKeyword rightKeyword
              leftPath.2 rightPath.2

/-- Exact complete-export rejection excludes every broad ordinary success. -/
theorem ExportDeclRejects.disjointOrdinary {input rejected : Remainder}
    (rejection : ExportDeclRejects input rejected) :
    ¬ ∃ declaration output,
      ExportDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  rcases successful.to_dispatch with
    ⟨successfulSpan, successfulAfterKeyword, successfulKeyword,
      successfulBranch⟩
  cases rejection with
  | keywordMissing keywordAbsent =>
      exact absent_conflicts_exact keywordAbsent successfulKeyword
  | localRejected rejectedSpan rejectedKeyword leftBracePresent
        payloadRejected =>
      cases successfulBranch with
      | inl successfulLocal =>
          exact payload_reject_disjoint_after_keyword
            localExportDeterministicOutcomeSpec rejectedKeyword
              successfulKeyword payloadRejected successfulLocal.2
      | inr successfulPath =>
          exact leftBrace_conflict_after_keyword rejectedKeyword
            successfulKeyword leftBracePresent successfulPath.1
  | pathRejected rejectedSpan rejectedKeyword leftBraceAbsent
        payloadRejected =>
      cases successfulBranch with
      | inl successfulLocal =>
          exact leftBrace_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulLocal.1 leftBraceAbsent
      | inr successfulPath =>
          exact payload_reject_disjoint_after_keyword
            pathExportDeterministicOutcomeSpec rejectedKeyword
              successfulKeyword payloadRejected successfulPath.2

/-- Complete exports have deterministic and exclusive broad outcomes. -/
theorem exportDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ExportDeclOrdinaryParses ExportDeclRejects where
  successOutputUnique := ExportDeclOrdinaryParses.output_unique
  successRejectDisjoint := ExportDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
