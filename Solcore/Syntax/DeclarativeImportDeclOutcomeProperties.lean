import Solcore.Syntax.DeclarativeImportDeclOutcomeGrammar
import Solcore.Syntax.DeclarativeNamespaceImportOutcomeProperties
import Solcore.Syntax.DeclarativePlainImportOutcomeProperties
import Solcore.Syntax.DeclarativeSelectiveImportOutcomeProperties
import Solcore.Syntax.DeclarativeWildcardImportOutcomeProperties

/-! Deterministic exact broad outcomes for complete import declarations. -/

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
      (input.cursor + offset) kind) : False := by
  rcases present with ⟨span, tokenAt⟩
  exact absent ⟨span, tokenAt⟩

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

private theorem dispatch_conflict_after_keyword
    {input leftAfter rightAfter : Remainder}
    {leftSpan rightSpan : SourceSpan} {offset : Nat} {kind : TokenKind}
    (leftKeyword : ExactTokenParses (.keyword .importKw) input leftSpan
      leftAfter)
    (rightKeyword : ExactTokenParses (.keyword .importKw) input rightSpan
      rightAfter)
    (present : ImportDispatchTokenPresentAt leftAfter offset kind)
    (absent : TokenKindAbsentAt rightAfter.tokens rightAfter.endIndex
      (rightAfter.cursor + offset) kind) : False := by
  have afterKeywordEq := exactToken_output_unique leftKeyword rightKeyword
  subst afterKeywordEq
  exact dispatch_present_conflicts_absent present absent

private theorem payload_output_unique_after_keyword
    {payload : SourceSpan → Remainder → Syntax.ImportDecl →
      Remainder → Prop}
    {payloadRejects : Remainder → Remainder → Prop}
    (outcomes : ∀ start,
      DeterministicOutcomeSpec (payload start) payloadRejects)
    {input leftAfter rightAfter leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    {left right : Syntax.ImportDecl}
    (leftKeyword : ExactTokenParses (.keyword .importKw) input leftSpan
      leftAfter)
    (rightKeyword : ExactTokenParses (.keyword .importKw) input rightSpan
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
    {payload : SourceSpan → Remainder → Syntax.ImportDecl →
      Remainder → Prop}
    {payloadRejects : Remainder → Remainder → Prop}
    (outcomes : ∀ start,
      DeterministicOutcomeSpec (payload start) payloadRejects)
    {input rejectedAfter successfulAfter rejected output : Remainder}
    {rejectedSpan successfulSpan : SourceSpan}
    {declaration : Syntax.ImportDecl}
    (rejectedKeyword : ExactTokenParses (.keyword .importKw) input
      rejectedSpan rejectedAfter)
    (successfulKeyword : ExactTokenParses (.keyword .importKw) input
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

/-- Complete broad import success has one final remainder. -/
theorem ImportDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ImportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImportDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImportDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | namespaceImport leftSpan leftKeyword leftStar leftAs leftPayload =>
      cases rightParsed with
      | namespaceImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact payload_output_unique_after_keyword
            namespaceImportDeterministicOutcomeSpec leftKeyword rightKeyword
              leftPayload rightPayload
      | wildcardImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword leftKeyword
            rightKeyword leftAs rightAs)
      | selectiveImport rightSpan rightKeyword rightStar rightBrace
            rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword leftKeyword
            rightKeyword leftStar rightStar)
      | plainImport rightSpan rightKeyword rightStar rightBrace rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword leftKeyword
            rightKeyword leftStar rightStar)
  | wildcardImport leftSpan leftKeyword leftStar leftAs leftPayload =>
      cases rightParsed with
      | namespaceImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword rightKeyword
            leftKeyword rightAs leftAs)
      | wildcardImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact payload_output_unique_after_keyword
            wildcardImportDeterministicOutcomeSpec leftKeyword rightKeyword
              leftPayload rightPayload
      | selectiveImport rightSpan rightKeyword rightStar rightBrace
            rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword leftKeyword
            rightKeyword leftStar rightStar)
      | plainImport rightSpan rightKeyword rightStar rightBrace rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword leftKeyword
            rightKeyword leftStar rightStar)
  | selectiveImport leftSpan leftKeyword leftStar leftBrace leftPayload =>
      cases rightParsed with
      | namespaceImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword rightKeyword
            leftKeyword rightStar leftStar)
      | wildcardImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword rightKeyword
            leftKeyword rightStar leftStar)
      | selectiveImport rightSpan rightKeyword rightStar rightBrace
            rightPayload =>
          exact payload_output_unique_after_keyword
            selectiveImportDeterministicOutcomeSpec leftKeyword rightKeyword
              leftPayload rightPayload
      | plainImport rightSpan rightKeyword rightStar rightBrace rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword leftKeyword
            rightKeyword leftBrace rightBrace)
  | plainImport leftSpan leftKeyword leftStar leftBrace leftPayload =>
      cases rightParsed with
      | namespaceImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword rightKeyword
            leftKeyword rightStar leftStar)
      | wildcardImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword rightKeyword
            leftKeyword rightStar leftStar)
      | selectiveImport rightSpan rightKeyword rightStar rightBrace
            rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword rightKeyword
            leftKeyword rightBrace leftBrace)
      | plainImport rightSpan rightKeyword rightStar rightBrace rightPayload =>
          exact payload_output_unique_after_keyword
            plainImportDeterministicOutcomeSpec leftKeyword rightKeyword
              leftPayload rightPayload

/-- Exact complete-import rejection excludes every broad ordinary success. -/
theorem ImportDeclRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : ImportDeclRejects input rejected) :
    ¬ ∃ declaration output,
      ImportDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases rejection with
  | keywordMissing keywordAbsent =>
      cases successful <;> exact absent_conflicts_exact keywordAbsent (by assumption)
  | namespaceImportRejected rejectedSpan rejectedKeyword rejectedStar
        rejectedAs payloadRejected =>
      cases successful with
      | namespaceImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact payload_reject_disjoint_after_keyword
            namespaceImportDeterministicOutcomeSpec rejectedKeyword
              successfulKeyword payloadRejected payloadParsed
      | wildcardImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact dispatch_conflict_after_keyword rejectedKeyword
            successfulKeyword rejectedAs successfulAs
      | selectiveImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact dispatch_conflict_after_keyword rejectedKeyword
            successfulKeyword rejectedStar successfulStar
      | plainImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact dispatch_conflict_after_keyword rejectedKeyword
            successfulKeyword rejectedStar successfulStar
  | wildcardImportRejected rejectedSpan rejectedKeyword rejectedStar
        rejectedAs payloadRejected =>
      cases successful with
      | namespaceImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact dispatch_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulAs rejectedAs
      | wildcardImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact payload_reject_disjoint_after_keyword
            wildcardImportDeterministicOutcomeSpec rejectedKeyword
              successfulKeyword payloadRejected payloadParsed
      | selectiveImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact dispatch_conflict_after_keyword rejectedKeyword
            successfulKeyword rejectedStar successfulStar
      | plainImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact dispatch_conflict_after_keyword rejectedKeyword
            successfulKeyword rejectedStar successfulStar
  | selectiveImportRejected rejectedSpan rejectedKeyword rejectedStar
        rejectedBrace payloadRejected =>
      cases successful with
      | namespaceImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact dispatch_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulStar rejectedStar
      | wildcardImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact dispatch_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulStar rejectedStar
      | selectiveImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact payload_reject_disjoint_after_keyword
            selectiveImportDeterministicOutcomeSpec rejectedKeyword
              successfulKeyword payloadRejected payloadParsed
      | plainImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact dispatch_conflict_after_keyword rejectedKeyword
            successfulKeyword rejectedBrace successfulBrace
  | plainImportRejected rejectedSpan rejectedKeyword rejectedStar
        rejectedBrace payloadRejected =>
      cases successful with
      | namespaceImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact dispatch_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulStar rejectedStar
      | wildcardImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact dispatch_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulStar rejectedStar
      | selectiveImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact dispatch_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulBrace rejectedBrace
      | plainImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact payload_reject_disjoint_after_keyword
            plainImportDeterministicOutcomeSpec rejectedKeyword
              successfulKeyword payloadRejected payloadParsed

/-- Complete imports have deterministic and exclusive broad outcomes. -/
theorem importDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ImportDeclOrdinaryParses ImportDeclRejects where
  successOutputUnique := ImportDeclOrdinaryParses.output_unique
  successRejectDisjoint := ImportDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
