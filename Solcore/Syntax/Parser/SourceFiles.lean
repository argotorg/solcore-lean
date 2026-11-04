import Solcore.Syntax.Trivia
import Solcore.Syntax.Declaration
import Solcore.Syntax.Source
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Foundation
import Solcore.Syntax.Token
import Solcore.Syntax.Lexer.Result
import Solcore.Syntax.DeclarativeDiagnosticCascadeGrammar
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeGrammar
import Solcore.Syntax.DeclarativeNestingOutcomeGrammar
import Solcore.Syntax.SpanSequence
import Solcore.Syntax.DeclarativeLexedValidationOutcomeGrammar
import Solcore.Syntax.Parser.State
import Solcore.Syntax.Module
import Solcore.Syntax.Parser.Modules
import Solcore.Syntax.Parser.Declarations
import Solcore.Syntax.Parser.Primitive
import Solcore.Syntax.Parser.Signatures
import Solcore.Syntax.Parser.Tokens

/-!
From tokens to a parsed source file.

Main declarations: `sourceFile`, `topItem`, `parseItems`, the nesting preflight
`checkNesting`, the carrier check `validateLexed`, the Rust-compatible diagnostic filter
`filterParseDiagnostics`, and comment attachment. `parse` and `parseLexed` build on these
in `Parser.lean`.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Trivia
/-!
Compatibility façade for the pure syntax-level trivia implementation.

The established parser namespace remains available to existing consumers,
while declarative grammar can depend directly on `Solcore.Syntax.Trivia`
without importing parser state or replies.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

abbrev isRustWhitespace := Solcore.Syntax.Trivia.isRustWhitespace

abbrev utf8Slice? := Solcore.Syntax.Trivia.utf8Slice?

abbrev lineBreakCount := Solcore.Syntax.Trivia.lineBreakCount

abbrev commentsDirectlyBefore :=
  Solcore.Syntax.Trivia.commentsDirectlyBefore

namespace TriviaInternals

abbrev attachEnumConstructorComments :=
  Solcore.Syntax.Trivia.Internals.attachEnumConstructorComments

abbrev attachEnumConstructors :=
  Solcore.Syntax.Trivia.Internals.attachEnumConstructors

abbrev attachEnumComments :=
  Solcore.Syntax.Trivia.Internals.attachEnumComments

abbrev attachTraitMethodComments :=
  Solcore.Syntax.Trivia.Internals.attachTraitMethodComments

abbrev attachTraitComments :=
  Solcore.Syntax.Trivia.Internals.attachTraitComments

abbrev attachImplMethodComments :=
  Solcore.Syntax.Trivia.Internals.attachImplMethodComments

abbrev attachImplComments :=
  Solcore.Syntax.Trivia.Internals.attachImplComments

abbrev attachContractMemberComments :=
  Solcore.Syntax.Trivia.Internals.attachContractMemberComments

abbrev attachContractComments :=
  Solcore.Syntax.Trivia.Internals.attachContractComments

end TriviaInternals

abbrev attachTopItemComments :=
  Solcore.Syntax.Trivia.attachTopItemComments

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.DiagnosticFilter
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Number of LF bytes preceding a validated UTF-8 source offset. -/
private def lineIndex (source : String) (offset : Nat) : Nat :=
  match utf8Slice? source 0 offset with
  | some text => text.toList.count '\n'
  | none => 0

private def spansOverlap (left right : SourceSpan) : Bool :=
  left.source == right.source &&
    left.startByte < right.endByte && right.startByte < left.endByte

private def whitespaceAdjacent (source : String)
    (lexical parsed : SourceSpan) : Bool :=
  if lexical.endByte > parsed.startByte then
    false
  else
    match utf8Slice? source lexical.endByte parsed.startByte with
    | some gap => gap.toList.all fun character =>
        isRustWhitespace character && character != '\n' && character != '\r'
    | none => false

/--
The pinned Rust parser treats a parser error on the affected source line as a
cascade of an invalid lexical token. The overlap and horizontal-whitespace
cases are retained explicitly to keep the byte-span policy evident.
-/
private def lexicalSpanSuppresses (source : String)
    (lexical parsed : SourceSpan) : Bool :=
  lexical.source == parsed.source &&
    (lineIndex source lexical.startByte == lineIndex source parsed.startByte ||
      spansOverlap lexical parsed ||
      (lexical.startByte ≤ parsed.startByte &&
        parsed.startByte ≤ lexical.endByte) ||
      whitespaceAdjacent source lexical parsed)

/--
Only parser failures and explicit recovery markers are known lexical cascades.
Semantic grammar constraints and nesting guards have no origin metadata and
are deliberately preserved.
-/
private def isLexicalCascadeCandidate : ParseDiagnosticKind → Bool
  | .unexpected .. | .recovered .. => true
  | _ => false

private def suppressLexicalCascades (source : String)
    (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic) : List ParseDiagnostic :=
  parsed.filter fun diagnostic =>
    !isLexicalCascadeCandidate diagnostic.kind ||
      !lexical.any fun lexError =>
        lexicalSpanSuppresses source lexError.span diagnostic.span

private theorem whitespaceAdjacent_eq_true_iff (source : String)
    (lexical parsed : SourceSpan) :
    whitespaceAdjacent source lexical parsed = true ↔
      DeclarativeGrammar.HorizontalWhitespaceGap source lexical parsed := by
  unfold whitespaceAdjacent DeclarativeGrammar.HorizontalWhitespaceGap
  split
  · rename_i reversed
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨ordered, _⟩
    omega
  · rename_i ordered
    have bound : lexical.endByte ≤ parsed.startByte := by omega
    cases gap : utf8Slice? source lexical.endByte parsed.startByte with
    | none => simp [bound, gap]
    | some text => simp [bound, gap]

private theorem sourceId_beq_true_iff (left right : SourceId) :
    (left == right) = true ↔ left = right := by
  cases left with
  | mk leftOrigin leftPath =>
      cases right with
      | mk rightOrigin rightPath =>
          cases leftOrigin <;> cases rightOrigin <;>
            simp [BEq.beq, instBEqSourceId.beq, instBEqSourceOrigin.beq]

private theorem lexicalSpanSuppresses_eq_true_iff (source : String)
    (lexical parsed : SourceSpan) :
    lexicalSpanSuppresses source lexical parsed = true ↔
      DeclarativeGrammar.LexicalSpanSuppresses source lexical parsed := by
  by_cases owners : lexical.source = parsed.source
  all_goals simp [lexicalSpanSuppresses, spansOverlap, lineIndex, utf8Slice?,
    DeclarativeGrammar.LexicalSpanSuppresses, DeclarativeGrammar.cascadeLineIndex,
    whitespaceAdjacent_eq_true_iff, sourceId_beq_true_iff, owners, or_assoc] <;> rfl

/-- Normalize ordinary diagnostics without consulting display prose. -/
def filterParseDiagnostics (file : SourceFile)
    (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic) : List ParseDiagnostic :=
  suppressLexicalCascades file.content lexical parsed

private theorem lexicalAnySuppresses_eq_true_iff (source : String)
    (lexical : List LexicalDiagnostic) (span : SourceSpan) :
    (lexical.any fun diagnostic => lexicalSpanSuppresses source diagnostic.span span) = true ↔
      DeclarativeGrammar.LexicalCascadeSuppresses source (lexical.map (·.span)) span := by
  constructor
  · intro suppressed
    rcases List.any_eq_true.mp suppressed with ⟨diagnostic, member, spanMatches⟩
    exact ⟨diagnostic.span, List.mem_map.mpr ⟨diagnostic, member, rfl⟩,
      (lexicalSpanSuppresses_eq_true_iff source diagnostic.span span).mp spanMatches⟩
  · rintro ⟨lexicalSpan, member, spanMatches⟩
    rcases List.mem_map.mp member with ⟨diagnostic, diagnosticMember, rfl⟩
    exact List.any_eq_true.mpr ⟨diagnostic, diagnosticMember,
      (lexicalSpanSuppresses_eq_true_iff source diagnostic.span span).mpr spanMatches⟩

/-- An independently suppressed recovery event is removed at its exact list position. -/
theorem filterParseDiagnostics_cons_recovered_of_suppressed
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (span : SourceSpan) (site : RecoverySite) (parsed : List ParseDiagnostic)
    (suppressed : DeclarativeGrammar.LexicalCascadeSuppresses
      file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical ({ span, kind := .recovered site } :: parsed) =
      filterParseDiagnostics file lexical parsed := by
  have anyEq := (lexicalAnySuppresses_eq_true_iff file.content lexical span).mpr suppressed
  simp [filterParseDiagnostics, suppressLexicalCascades, isLexicalCascadeCandidate, anyEq]

/-- Without an independent suppression witness, a recovery event is retained in order. -/
theorem filterParseDiagnostics_cons_recovered_of_retained
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (span : SourceSpan) (site : RecoverySite) (parsed : List ParseDiagnostic)
    (retained : ¬ DeclarativeGrammar.LexicalCascadeSuppresses
      file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical ({ span, kind := .recovered site } :: parsed) =
      { span, kind := .recovered site } :: filterParseDiagnostics file lexical parsed := by
  cases anyEq : lexical.any (fun diagnostic =>
      lexicalSpanSuppresses file.content diagnostic.span span) with
  | false =>
      simp [filterParseDiagnostics, suppressLexicalCascades, isLexicalCascadeCandidate, anyEq]
  | true =>
      exact False.elim (retained
        ((lexicalAnySuppresses_eq_true_iff file.content lexical span).mp anyEq))

/-- An independently suppressed expectation failure is removed without changing
its surrounding trace. The found token, expectations, and context stay explicit. -/
theorem filterParseDiagnostics_cons_unexpected_of_suppressed
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (span : SourceSpan) (found : Option TokenKind)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (parsed : List ParseDiagnostic)
    (suppressed : DeclarativeGrammar.LexicalCascadeSuppresses
      file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical
      ({ span, kind := .unexpected found expected context } :: parsed) =
      filterParseDiagnostics file lexical parsed := by
  have anyEq := (lexicalAnySuppresses_eq_true_iff file.content lexical span).mpr suppressed
  simp [filterParseDiagnostics, suppressLexicalCascades, isLexicalCascadeCandidate, anyEq]

/-- A retained expectation failure preserves its complete metadata and position. -/
theorem filterParseDiagnostics_cons_unexpected_of_retained
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (span : SourceSpan) (found : Option TokenKind)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (parsed : List ParseDiagnostic)
    (retained : ¬ DeclarativeGrammar.LexicalCascadeSuppresses
      file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical
      ({ span, kind := .unexpected found expected context } :: parsed) =
      { span, kind := .unexpected found expected context } ::
        filterParseDiagnostics file lexical parsed := by
  cases anyEq : lexical.any (fun diagnostic =>
      lexicalSpanSuppresses file.content diagnostic.span span) with
  | false =>
      simp [filterParseDiagnostics, suppressLexicalCascades, isLexicalCascadeCandidate, anyEq]
  | true =>
      exact False.elim (retained
        ((lexicalAnySuppresses_eq_true_iff file.content lexical span).mp anyEq))

/-- Every retained report keeps all metadata, including protected report kinds. -/
theorem filterParseDiagnostics_cons_of_retained
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (diagnostic : ParseDiagnostic) (parsed : List ParseDiagnostic)
    (retained : ¬ DeclarativeGrammar.ParseDiagnosticCascadeSuppresses
      file.content (lexical.map (·.span)) diagnostic) :
    filterParseDiagnostics file lexical (diagnostic :: parsed) =
      diagnostic :: filterParseDiagnostics file lexical parsed := by
  rcases diagnostic with ⟨span, kind⟩
  cases kind with
  | unexpected found expected context =>
      exact filterParseDiagnostics_cons_unexpected_of_retained
        file lexical span found expected context parsed (fun h => retained ⟨trivial, h⟩)
  | recovered site =>
      exact filterParseDiagnostics_cons_recovered_of_retained
        file lexical span site parsed (fun h => retained ⟨trivial, h⟩)
  | invalidIdentifierHyphen text | constraintViolation constraint | nestingExceeded kind limit =>
      simp [filterParseDiagnostics, suppressLexicalCascades, isLexicalCascadeCandidate]

/-- Filtering an empty parser trace cannot introduce a diagnostic. -/
@[simp] theorem filterParseDiagnostics_nil_parsed
    (file : SourceFile) (lexical : List LexicalDiagnostic) :
    filterParseDiagnostics file lexical [] = [] := by
  simp [filterParseDiagnostics, suppressLexicalCascades]

/-- With no lexical errors, diagnostic normalization retains every parser
diagnostic exactly. -/
@[simp] theorem filterParseDiagnostics_nil_lexical
    (file : SourceFile) (parsed : List ParseDiagnostic) :
    filterParseDiagnostics file [] parsed = parsed := by
  simp [filterParseDiagnostics, suppressLexicalCascades]

/-- A nesting overflow has no lexical-cascade origin and is retained even
when ordinary lexical diagnostics occur at the same source location. -/
@[simp] theorem filterParseDiagnostics_single_nestingExceeded
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (span : SourceSpan) (kind : NestingKind) (limit : Nat) :
    filterParseDiagnostics file lexical [{
      span
      kind := .nestingExceeded kind limit
    }] = [{
      span
      kind := .nestingExceeded kind limit
    }] := by
  simp [filterParseDiagnostics, suppressLexicalCascades,
    isLexicalCascadeCandidate]

/-- Diagnostic normalization can only remove parser diagnostics. -/
theorem mem_of_mem_filterParseDiagnostics
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic) (diagnostic : ParseDiagnostic)
    (member : diagnostic ∈ filterParseDiagnostics file lexical parsed) :
    diagnostic ∈ parsed := by
  unfold filterParseDiagnostics suppressLexicalCascades at member
  exact (List.mem_filter.mp member).1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Nesting
/-! Bounded nesting preflight for the canonical syntax parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Canonical parser guard applied before recursive token grammar. -/
def maxSyntaxNesting : Nat :=
  DeclarativeGrammar.canonicalNestingLimit

private abbrev NestingState := DeclarativeGrammar.NestingContext

private def nestingError (kind : NestingKind)
    (token : Token) : ParseDiagnostic := {
  span := token.span
  kind := .nestingExceeded kind maxSyntaxNesting
}

private def checkNestingAux :
    NestingState → List Token → Option ParseDiagnostic
  | _, [] => none
  | state, token :: rest =>
      match DeclarativeGrammar.nestingAction token.value with
      | .conditional =>
          let depth := state.conditionalDepth + 1
          if depth > maxSyntaxNesting then
            some (nestingError .conditional token)
          else
            checkNestingAux { state with conditionalDepth := depth } rest
      | .groupOpen =>
          let depth := state.delimiterDepth + 1
          if depth > maxSyntaxNesting then
            some (nestingError .delimiter token)
          else
            checkNestingAux {
              delimiterDepth := depth
              conditionalDepth := state.conditionalDepth
              conditionalBases := state.conditionalDepth ::
                state.conditionalBases
            } rest
      | .blockOpen =>
          let depth := state.delimiterDepth + 1
          if depth > maxSyntaxNesting then
            some (nestingError .delimiter token)
          else
            checkNestingAux {
              delimiterDepth := depth
              conditionalDepth := 0
              conditionalBases := 0 :: state.conditionalBases
            } rest
      | .close => checkNestingAux state.closeDelimiter rest
      | .reset => checkNestingAux state.resetConditional rest
      | .preserve => checkNestingAux state rest

/-- First delimiter or conditional nesting violation, if one exists. -/
def checkNesting (tokens : List Token) : Option ParseDiagnostic :=
  checkNestingAux {} tokens

/-- Convert a parser-independent nesting overflow to its public diagnostic. -/
def nestingOverflowDiagnostic
    (overflow : DeclarativeGrammar.NestingOverflow) : ParseDiagnostic := {
  span := overflow.span
  kind := .nestingExceeded
    (match overflow.dimension with
      | .delimiter => .delimiter
      | .conditional => .conditional)
    overflow.limit
}

private theorem checkNestingAux_eq_map_of_scan
    {context : DeclarativeGrammar.NestingContext} {tokens : List Token}
    {result : Option DeclarativeGrammar.NestingOverflow}
    (scan : DeclarativeGrammar.NestingScans maxSyntaxNesting
      context tokens result) :
    checkNestingAux context tokens = result.map nestingOverflowDiagnostic := by
  induction scan with
  | done => rfl
  | conditionalExceeded action exceeds =>
      simp [checkNestingAux, action, if_pos exceeds, nestingError,
        nestingOverflowDiagnostic, DeclarativeGrammar.nestingOverflow]
  | conditionalContinues action within tail inductionHypothesis =>
      have notExceeded :
          ¬ maxSyntaxNesting < _ + 1 := Nat.not_lt_of_ge within
      simp [checkNestingAux, action, if_neg notExceeded,
        inductionHypothesis]
  | groupExceeded action exceeds =>
      simp [checkNestingAux, action, if_pos exceeds, nestingError,
        nestingOverflowDiagnostic, DeclarativeGrammar.nestingOverflow]
  | groupContinues action within tail inductionHypothesis =>
      have notExceeded :
          ¬ maxSyntaxNesting < _ + 1 := Nat.not_lt_of_ge within
      simp [checkNestingAux, action, if_neg notExceeded,
        inductionHypothesis]
  | blockExceeded action exceeds =>
      simp [checkNestingAux, action, if_pos exceeds, nestingError,
        nestingOverflowDiagnostic, DeclarativeGrammar.nestingOverflow]
  | blockContinues action within tail inductionHypothesis =>
      have notExceeded :
          ¬ maxSyntaxNesting < _ + 1 := Nat.not_lt_of_ge within
      simp [checkNestingAux, action, if_neg notExceeded,
        inductionHypothesis]
  | close action tail inductionHypothesis =>
      simp [checkNestingAux, action, inductionHypothesis]
  | reset action tail inductionHypothesis =>
      simp [checkNestingAux, action, inductionHypothesis]
  | preserve action tail inductionHypothesis =>
      simp [checkNestingAux, action, inductionHypothesis]

/-- Every declarative root scan computes the identical executable result. -/
theorem checkNesting_eq_map_of_outcome
    {tokens : List Token}
    {result : Option DeclarativeGrammar.NestingOverflow}
    (outcome : DeclarativeGrammar.NestingOutcome tokens result) :
    checkNesting tokens = result.map nestingOverflowDiagnostic := by
  exact checkNestingAux_eq_map_of_scan outcome

private theorem checkNestingAux_some_span_validFor
    (file : SourceFile) (state : NestingState) (tokens : List Token)
    (tokensValid : ∀ token ∈ tokens, token.span.ValidFor file)
    {diagnostic : ParseDiagnostic}
    (result : checkNestingAux state tokens = some diagnostic) :
    diagnostic.span.ValidFor file := by
  induction tokens generalizing state with
  | nil => simp [checkNestingAux] at result
  | cons token rest inductionHypothesis =>
      have tokenValid : token.span.ValidFor file :=
        tokensValid token (by simp)
      have restValid : ∀ retained ∈ rest,
          retained.span.ValidFor file := by
        intro retained member
        exact tokensValid retained (by simp [member])
      cases action : DeclarativeGrammar.nestingAction token.value <;>
          simp only [checkNestingAux, action] at result
      all_goals first
        | (split at result
           · cases result
             exact tokenValid
           · exact inductionHypothesis _ restValid result)
        | exact inductionHypothesis _ restValid result

/-- A reported nesting violation always points into the validated token file. -/
theorem checkNesting_some_span_validFor
    (file : SourceFile) (tokens : List Token)
    (tokensValid : SpanSequence.ValidFor file
      (fun token : Token => token.span) 0 tokens)
    {diagnostic : ParseDiagnostic}
    (result : checkNesting tokens = some diagnostic) :
    diagnostic.span.ValidFor file := by
  exact checkNestingAux_some_span_validFor file {} tokens
    (fun _ member => tokensValid.span_valid member) result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.LexedValidation
/-! Executable provenance validation for already-tokenized syntax input. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace LexedValidation

/-- Validate token spans in source order, returning the first bad index. -/
def tokens (file : SourceFile) :
    Nat → Nat → List Token → Except ParserInvariantError Unit
  | _, _, [] => .ok ()
  | index, previousEnd, token :: rest =>
      if token.span.isValidFor file &&
          previousEnd ≤ token.span.startByte &&
          token.span.startByte < token.span.endByte then
        tokens file (index + 1) token.span.endByte rest
      else
        .error (.invalidTokenSpan index token.span)

/-- Validate comment spans in source order, returning the first bad index. -/
def comments (file : SourceFile) :
    Nat → Nat → List Comment → Except ParserInvariantError Unit
  | _, _, [] => .ok ()
  | index, previousEnd, comment :: rest =>
      if comment.span.isValidFor file &&
          previousEnd ≤ comment.span.startByte &&
          comment.span.startByte < comment.span.endByte then
        comments file (index + 1) comment.span.endByte rest
      else
        .error (.invalidCommentSpan index comment.span)

/-- Validate lexical-diagnostic ownership and UTF-8 boundaries in order. -/
def lexicalDiagnostics (file : SourceFile) :
    Nat → List LexicalDiagnostic → Except ParserInvariantError Unit
  | _, [] => .ok ()
  | index, diagnostic :: rest =>
      if diagnostic.span.isValidFor file then
        lexicalDiagnostics file (index + 1) rest
      else
        .error (.invalidLexicalDiagnosticSpan index diagnostic.span)

end LexedValidation

/-- Validate all provenance consumed or retained by `parseLexed`. -/
def validateLexed (file : SourceFile)
    (lexed : LexedFile) : Except ParserInvariantError Unit := do
  if lexed.source ≠ file.id then
    throw (.invalidLexedSource file.id lexed.source)
  LexedValidation.tokens file 0 0 lexed.tokens
  LexedValidation.comments file 0 0 lexed.comments
  LexedValidation.lexicalDiagnostics file 0 lexed.diagnostics

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.LexedValidationOutcomeSoundnessProperties`
-/

/-! Exact correspondence between executable and declarative lexed validation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

/-- Translate a parser-neutral validation failure to its public invariant error. -/
def lexedValidationInvariantError :
    LexedValidationFailure → ParserInvariantError
  | .sourceMismatch expected actual =>
      .invalidLexedSource expected actual
  | .invalidTokenSpan index span => .invalidTokenSpan index span
  | .invalidCommentSpan index span => .invalidCommentSpan index span
  | .invalidLexicalDiagnosticSpan index span =>
      .invalidLexicalDiagnosticSpan index span

/-- Executable result represented by one declarative whole-file outcome. -/
def lexedValidationResult :
    Option LexedValidationFailure → Except ParserInvariantError Unit
  | none => .ok ()
  | some failure => .error (lexedValidationInvariantError failure)

/-- Executable result represented by one declarative indexed-span scan. -/
def indexedSpanValidationResult
    (failure : Nat → SourceSpan → ParserInvariantError) :
    Option IndexedSpan → Except ParserInvariantError Unit
  | none => .ok ()
  | some invalid => .error (failure invalid.index invalid.span)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.File
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FileInternals

def wrapTypeAlias (declaration : TypeAliasDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .typeAlias declaration
}

def wrapImport (declaration : ImportDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .importDecl declaration
}

def wrapExport (declaration : ExportDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .exportDecl declaration
}

def wrapPragma (declaration : PragmaDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .pragmaDecl declaration
}

def wrapFunction (declaration : FunctionDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .function declaration
}

def wrapEnum (declaration : EnumDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .enum declaration
}

def wrapTrait (declaration : TraitDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .trait declaration
}

def wrapImpl (declaration : ImplDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .impl declaration
}

def wrapContract (declaration : ContractDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .contract declaration
}

def extendTopItemStart (prefixSpan : SourceSpan)
    (item : TopItem) : TopItem :=
  let span := SourceSpan.cover prefixSpan item.span
  let value := match item.value with
    | .importDecl declaration => .importDecl { declaration with span }
    | .exportDecl declaration => .exportDecl { declaration with span }
    | .pragmaDecl declaration => .pragmaDecl { declaration with span }
    | .typeAlias declaration => .typeAlias { declaration with span }
    | .enum declaration => .enum { declaration with span }
    | .trait declaration => .trait { declaration with span }
    | .impl declaration => .impl { declaration with span }
    | .contract declaration => .contract { declaration with span }
    | .function declaration => .function { declaration with span }
    | .error => .error
  { item with span, value }

end FileInternals

namespace FileInternals

def mapTopItem {alpha : Type} (parser : Parser alpha)
    (wrap : alpha → TopItem) : Parser TopItem := fun state =>
  match parser state with
  | .ok value next => .ok (wrap value) next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

def plainTopItem : Parser TopItem := fun state =>
  if isKeyword state .importKw then
    mapTopItem importDecl wrapImport state
  else if isKeyword state .exportKw then
    mapTopItem exportDecl wrapExport state
  else if isKeyword state .pragmaKw then
    mapTopItem pragmaDecl wrapPragma state
  else if isKeyword state .typeKw then
    mapTopItem typeAlias wrapTypeAlias state
  else if isKeyword state .functionKw then
    mapTopItem (functionDecl .module) wrapFunction state
  else if isContextual state .enum then
    mapTopItem (enumDecl none) wrapEnum state
  else if isContextual state .trait then
    mapTopItem traitDecl wrapTrait state
  else if isContextual state .impl || isKeyword state .defaultKw then
    mapTopItem implDecl wrapImpl state
  else if isKeyword state .contractKw then
    mapTopItem contractDecl wrapContract state
  else
    rejectAt state { head := .topItem, tail := [] } .topItem

end FileInternals

namespace FileInternals

def attachDeriveAttribute (derive : DeriveAttribute)
    (item : TopItem) : Parser TopItem :=
  match item.value with
  | .enum declaration =>
      let span := SourceSpan.cover derive.span declaration.span
      pure {
        item with
        span
        value := .enum {
          declaration with
          span
          value := { declaration.value with
            deriveAttribute := some derive
          }
        }
      }
  | _ => do
      let _ ← emitDiagnostic {
        span := derive.span
        kind := .constraintViolation .deriveOnlyEnum
      }
      pure (extendTopItemStart derive.span item)

end FileInternals

namespace FileInternals

/-- Parse one top-level form, including an optional derive attribute. -/
def topItem : Parser TopItem := fun state =>
  if isSymbol state .hash then
    match deriveAttribute state with
    | .ok derive afterDerive =>
        match FileInternals.plainTopItem afterDerive with
        | .ok item next => FileInternals.attachDeriveAttribute derive item next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    FileInternals.plainTopItem state

end FileInternals

namespace FileInternals

def finishRecoveredTopItem (first last : SourceSpan)
    (state : State) : Reply TopItem :=
  let span := SourceSpan.cover first last
  .ok {
    span
    leadingComments := []
    value := .error
  } (state.emit {
    span
    kind := .recovered .topItem
  })

def recoverTopItemAux (first last : SourceSpan) :
    Nat → State → Reply TopItem
  | 0, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, state =>
      if state.atEnd || atTopItemStart state then
        finishRecoveredTopItem first last state
      else
        match state.advance? with
        | some (token, next) =>
            recoverTopItemAux first token.span fuel next
        | none => finishRecoveredTopItem first last state

def recoverTopItem (state : State) : Reply TopItem :=
  match state.advance? with
  | some (token, next) =>
      recoverTopItemAux token.span token.span
        (next.remainingCount + 1) next
  | none => rejectAt state { head := .topItem, tail := [] } .topItem

end FileInternals

namespace FileInternals

/-- Proof boundary for the complete derive-aware item parser. -/
def parseItemsItem : Parser TopItem := topItem

def parseItems :
    Nat → List TopItem → State → Reply (List TopItem)
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, itemsRev, state =>
      if state.atEnd then
        .ok itemsRev.reverse state
      else
        match parseItemsItem state with
        | .ok item next =>
            if next.cursor > state.cursor then
              parseItems fuel (item :: itemsRev) next
            else
              .invariant (.noProgress .topLevel next.currentSpan)
        | .reject failure failedState =>
            let rewound := {
              failedState with
              cursor := state.cursor
            }
            if atTopItemStart state then
              -- Rust recovery also refuses to consume a recognized item start.
              .ok itemsRev.reverse (rewound.emit failure.toDiagnostic)
            else
              -- The enclosing recovery diagnostic replaces its inner failure.
              match FileInternals.recoverTopItem rewound with
              | .ok item next =>
                  parseItems fuel (item :: itemsRev) next
              | .reject recoveryFailure next =>
                  .reject recoveryFailure next
              | .invariant error => .invariant error
        | .invariant error => .invariant error

end FileInternals

/-- Parse a complete token window into a source-owned syntax file. -/
def sourceFile (comments : List Comment) : Parser ParsedFile := fun state =>
  match FileInternals.parseItems (state.remainingCount + 1) [] state with
  | .ok items next => .ok {
      source := state.file.id
      span := SourceSpan.fullFile state.file
      items := items.map (attachTopItemComments state.file comments)
      comments
    } next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end Solcore.Syntax.Parser
end
