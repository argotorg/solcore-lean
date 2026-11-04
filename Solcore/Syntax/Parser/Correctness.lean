import Solcore.Syntax.Parser.Internal.DeclarationTotality
import Solcore.Syntax.Parser.Internal.EnumProofs
import Solcore.Syntax.Parser.Internal.FileTotality
import Solcore.Syntax.Parser.Internal.ImplProofs
import Solcore.Syntax.Parser.Internal.TraitProofs
import Solcore.Syntax.Parser.Internal.SourceFileSoundness
import Solcore.Syntax.Internal.DeclarationExactness
import Solcore.Syntax.Internal.SourceFileOutcomes
import Solcore.Syntax.Parser.Internal.FileProofs
import Solcore.Syntax.Parser.Internal.OutcomeCompleteness
import Solcore.Syntax.Parser.Internal.Completeness
import Solcore.Syntax.Parser.Internal.TermSoundness
import Solcore.Syntax.Parser.Internal.SignatureSoundness

/-!
The parser's main theorems.

The parser against the independent grammar, at the public boundary:
- totality: `productionParse_exists_ok`, `productionParseLexed_exists_ok`;
- soundness: `parse_ok_publicSourceFileOrdinary_sound`;
- completeness: `parse_exists_ok_iff_publicSourceFileOrdinary`;
- uniqueness: `parse_ok_parsed_value_unique`,
  `publicSourceFileOrdinary_exists_unique_of_validation`;
- provenance: `parse_ok_completeOutput_validFor`,
  `PublicSourceFileOrdinaryParses.validFor_of_lexing`;
- one certified branch for every input: `productionParseLexed_certifiedOutcome`.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.CanonicalParserTotalityProperties
/-! Unconditional totality from canonical top-item dispatch to public parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every production declaration branch is invariant-free on valid input. -/
theorem productionPlainTopItemTotalityContract :
    PlainTopItemTotalityContract := {
  moduleFunction := functionDecl_invariantFreeOnValid .module
  enumDecl := enumDecl_invariantFreeOnValid none
  traitDecl := traitDecl_invariantFreeOnValid
  implDecl := implDecl_invariantFreeOnValid
  contractDecl := contractDecl_invariantFreeOnValid
}

/-- Plain canonical top-item dispatch has only ordinary outcomes. -/
theorem productionPlainTopItem_invariantFreeOnValid :
    Parser.InvariantFreeOnValid plainTopItem :=
  plainTopItem_invariantFreeOnValid productionPlainTopItemTotalityContract

theorem productionPlainTopItem_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ item next, plainTopItem input = .ok item next) ∨
      (∃ failure next, plainTopItem input = .reject failure next) :=
  productionPlainTopItem_invariantFreeOnValid input inputValid

theorem productionPlainTopItem_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    plainTopItem input ≠ .invariant error :=
  productionPlainTopItem_invariantFreeOnValid.ne_invariant
    input inputValid error

/-- Derive-aware canonical top-item dispatch has only ordinary outcomes. -/
theorem productionTopItem_invariantFreeOnValid :
    Parser.InvariantFreeOnValid topItem :=
  topItem_invariantFreeOnValid productionPlainTopItemTotalityContract

theorem productionTopItem_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ item next, topItem input = .ok item next) ∨
      (∃ failure next, topItem input = .reject failure next) :=
  productionTopItem_invariantFreeOnValid input inputValid

theorem productionTopItem_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    topItem input ≠ .invariant error :=
  productionTopItem_invariantFreeOnValid.ne_invariant
    input inputValid error

/-- The concrete file-loop item parser is invariant-free on valid input. -/
theorem productionParseItemsItem_invariantFreeOnValid :
    Parser.InvariantFreeOnValid parseItemsItem :=
  parseItemsItem_invariantFreeOnValid productionPlainTopItemTotalityContract

theorem productionParseItemsItem_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ item next, parseItemsItem input = .ok item next) ∨
      (∃ failure next, parseItemsItem input = .reject failure next) :=
  productionParseItemsItem_invariantFreeOnValid input inputValid

theorem productionParseItemsItem_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseItemsItem input ≠ .invariant error :=
  productionParseItemsItem_invariantFreeOnValid.ne_invariant
    input inputValid error

/-- The concrete item theorem discharges the complete-file loop premise. -/
theorem productionParseItemsItemInvariantFree :
    ParseItemsItemInvariantFree :=
  parseItemsItemInvariantFree_of_plainTopItemContract
    productionPlainTopItemTotalityContract

/-- A complete canonical source-file parser always succeeds on valid state. -/
theorem productionSourceFile_exists_ok
    (comments : List Comment) (input : State) (inputValid : input.ValidFor) :
    ∃ parsed final, sourceFile comments input = .ok parsed final :=
  sourceFile_exists_ok_of_plainTopItemContract
    productionPlainTopItemTotalityContract comments input inputValid

theorem productionSourceFile_invariantFreeOnValid
    (comments : List Comment) :
    Parser.InvariantFreeOnValid (sourceFile comments) := by
  intro input inputValid
  exact Or.inl
    (productionSourceFile_exists_ok comments input inputValid)

theorem productionSourceFile_ordinary
    (comments : List Comment) (input : State) (inputValid : input.ValidFor) :
    (∃ parsed final, sourceFile comments input = .ok parsed final) ∨
      (∃ failure final,
        sourceFile comments input = .reject failure final) :=
  productionSourceFile_invariantFreeOnValid comments input inputValid

theorem productionSourceFile_ne_invariant
    (comments : List Comment) (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    sourceFile comments input ≠ .invariant error :=
  (productionSourceFile_invariantFreeOnValid comments).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser.FileInternals

namespace Solcore.Syntax.Parser

/-- Valid already-tokenized input always produces a parse output. -/
theorem productionParseLexed_exists_ok
    (file : SourceFile) (lexed : LexedFile) (lexedValid : lexed.ValidFor file) :
    ∃ output, parseLexed file lexed = .ok output :=
  parseLexed_exists_ok_of_plainTopItemContract
    FileInternals.productionPlainTopItemTotalityContract
    file lexed lexedValid

/-- No parser invariant escapes valid already-tokenized input. -/
theorem productionParseLexed_ne_error
    (file : SourceFile) (lexed : LexedFile) (lexedValid : lexed.ValidFor file)
    (error : ParserInvariantError) :
    parseLexed file lexed ≠ .error error :=
  parseLexed_ne_error_of_plainTopItemContract
    FileInternals.productionPlainTopItemTotalityContract
    file lexed lexedValid error

/-- Public parsing returns a parse output for every source file. -/
theorem productionParse_exists_ok (file : SourceFile) :
    ∃ output, parse file = .ok output :=
  parse_exists_ok_of_plainTopItemContract
    FileInternals.productionPlainTopItemTotalityContract file

/-- Public parsing cannot expose an internal syntax invariant error. -/
theorem productionParse_ne_error
    (file : SourceFile) (error : SyntaxInvariantError) :
    parse file ≠ .error error :=
  parse_ne_error_of_plainTopItemContract
    FileInternals.productionPlainTopItemTotalityContract file error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ParseLexedErrorProperties
/-! Exact origin of exceptional results at the public token-to-file boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- An exceptional token-to-file result is exactly its preflight validation
failure. Once validation succeeds, production parsing is total. -/
theorem productionParseLexed_error_iff_validateLexed_error
    (file : SourceFile) (lexed : LexedFile) (error : ParserInvariantError) :
    parseLexed file lexed = .error error ↔
      validateLexed file lexed = .error error := by
  constructor
  · intro failed
    cases validation : validateLexed file lexed with
    | error validationError =>
        unfold parseLexed at failed
        rw [validation] at failed
        change Except.error validationError = Except.error error at failed
        cases failed
        rfl
    | ok witness =>
        cases witness
        have valid := validateLexed_ok_validFor file lexed validation
        exact (productionParseLexed_ne_error file lexed valid error failed).elim
  · intro failed
    unfold parseLexed
    rw [failed]
    simp only [bind, Except.bind]

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SourceFileCompletenessProperties
/-! Complete source-file AST and remainder correspondence on valid parser states. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every independent source-file derivation is the executable result, and every
executable result has that derivation. Supplied comments need no validity premise
for this syntax-only correspondence. -/
theorem sourceFile_ordinary_iff_exists_ok_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (comments : List Comment) {input : State} (inputValid : input.ValidFor)
    {parsed : ParsedFile} {afterParsed : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
        input.declarativeRemainder parsed afterParsed ↔
      ∃ output, sourceFile comments input = .ok parsed output ∧
        output.declarativeRemainder = afterParsed := by
  constructor
  · intro expected
    rcases productionSourceFile_exists_ok comments input inputValid with
      ⟨actual, output, result⟩
    rcases (sourceFile_exactOutcomeSpec_of_topItem itemOutcomes input.file comments)
        |>.successResultUnique (sourceFile_success_ordinaryOutcome_sound result) expected with
      ⟨valueEq, remainderEq⟩
    exact ⟨output, by simpa only [valueEq] using result, remainderEq⟩
  · rintro ⟨output, result, remainderEq⟩
    simpa only [remainderEq] using sourceFile_success_ordinaryOutcome_sound result

/-- Canonical complete-file syntax and execution agree without a recursive
exactness premise; only the input state's existing validity contract is required. -/
theorem sourceFile_ordinary_iff_exists_ok
    (comments : List Comment) {input : State} (inputValid : input.ValidFor)
    {parsed : ParsedFile} {afterParsed : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
        input.declarativeRemainder parsed afterParsed ↔
      ∃ output, sourceFile comments input = .ok parsed output ∧
        output.declarativeRemainder = afterParsed :=
  sourceFile_ordinary_iff_exists_ok_of_topItem
    DeclarativeGrammar.topItemExactOutcomeSpec comments inputValid

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePublicParseOrdinarySoundnessProperties
/-! Concrete ordinary grammar soundness at both public parser boundaries. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A diagnostic-free successful token-to-syntax parse follows the concrete
ordinary Core grammar from the root token window. -/
theorem parseLexed_ok_coreOrdinary_sound
    {file : SourceFile} {lexed : LexedFile} {output : ParseOutput}
    (diagnosticFree : output.DiagnosticFree)
    (result : parseLexed file lexed = .ok output) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParsesFromStart file
      lexed.tokens lexed.comments output.parsed := by
  have lexedValid := parseLexed_ok_input_validFor file lexed output result
  unfold parseLexed at result
  rw [validateLexed_validFor_ok file lexed lexedValid] at result
  change (match checkNesting lexed.tokens with
    | some diagnostic => Except.ok ({
        parsed := {
          source := file.id
          span := SourceSpan.fullFile file
          items := []
          comments := lexed.comments
        }
        tokens := lexed.tokens
        lexicalDiagnostics := lexed.diagnostics
        parseDiagnostics :=
          filterParseDiagnostics file lexed.diagnostics [diagnostic]
      } : ParseOutput)
    | none =>
        match sourceFile lexed.comments (State.initial file lexed) with
        | .ok parsed finalState => Except.ok ({
            parsed
            tokens := lexed.tokens
            lexicalDiagnostics := lexed.diagnostics
            parseDiagnostics := filterParseDiagnostics file
              lexed.diagnostics finalState.diagnostics
          } : ParseOutput)
        | .reject failure _ =>
            Except.error (ParserInvariantError.noProgress
              .topLevel failure.span)
        | .invariant error => Except.error error) = .ok output at result
  cases nesting : checkNesting lexed.tokens with
  | some nestingDiagnostic =>
      simp only [nesting] at result
      cases result
      rcases diagnosticFree with ⟨lexicalFree, parseFree⟩
      change lexed.diagnostics = [] at lexicalFree
      change filterParseDiagnostics file lexed.diagnostics
        [nestingDiagnostic] = [] at parseFree
      rw [lexicalFree, filterParseDiagnostics_nil_lexical] at parseFree
      contradiction
  | none =>
      simp only [nesting] at result
      cases grammar : sourceFile lexed.comments
          (State.initial file lexed) with
      | ok parsed finalState =>
          simp only [grammar] at result
          cases result
          rcases diagnosticFree with ⟨lexicalFree, parseFree⟩
          change lexed.diagnostics = [] at lexicalFree
          change filterParseDiagnostics file lexed.diagnostics
            finalState.diagnostics = [] at parseFree
          rw [lexicalFree, filterParseDiagnostics_nil_lexical] at parseFree
          have finalDiagnosticFree : finalState.diagnosticsRev = [] := by
            simpa [State.diagnostics] using parseFree
          have parsedByCore :=
            FileInternals.sourceFile_success_coreOrdinary_sound_toEnd
              (comments := lexed.comments) (input := State.initial file lexed)
              (next := finalState) (parsedFile := parsed)
              (State.initial_validFor lexedValid)
              (fun comment member => lexedValid.comment_span member)
              finalDiagnosticFree grammar
          simpa [DeclarativeGrammar.CoreSourceFileOrdinaryParsesFromStart,
            State.initial, State.declarativeRemainder] using parsedByCore
      | reject failure rejected =>
          simp only [grammar] at result
          contradiction
      | invariant error =>
          simp only [grammar] at result
          contradiction

/-- Token-to-syntax ordinary soundness paired with canonical parsed-file
validity. -/
theorem parseLexed_ok_coreOrdinary_sound_and_validFor
    {file : SourceFile} {lexed : LexedFile} {output : ParseOutput}
    (diagnosticFree : output.DiagnosticFree)
    (result : parseLexed file lexed = .ok output) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParsesFromStart file
        lexed.tokens lexed.comments output.parsed ∧
      CanonicalParsedFileValid file output.parsed := by
  exact ⟨parseLexed_ok_coreOrdinary_sound diagnosticFree result,
    parseLexed_ok_complete_validFor file lexed output
      (parseLexed_ok_input_validFor file lexed output result) result⟩

/-- A diagnostic-free successful source parse follows the concrete ordinary
Core grammar over the exact carriers retained in its public output. -/
theorem parse_ok_coreOrdinary_sound
    {file : SourceFile} {output : ParseOutput}
    (diagnosticFree : output.DiagnosticFree)
    (result : parse file = .ok output) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParsesFromStart file
      output.tokens output.parsed.comments output.parsed := by
  rcases parse_ok_lexed_provenance file output result with
    ⟨lexed, _lexing, parsing, tokens, _diagnostics, comments⟩
  simpa only [tokens, comments] using
    parseLexed_ok_coreOrdinary_sound diagnosticFree parsing

/-- Public source ordinary soundness paired with canonical parsed-file
validity. -/
theorem parse_ok_coreOrdinary_sound_and_validFor
    {file : SourceFile} {output : ParseOutput}
    (diagnosticFree : output.DiagnosticFree)
    (result : parse file = .ok output) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParsesFromStart file
        output.tokens output.parsed.comments output.parsed ∧
      CanonicalParsedFileValid file output.parsed := by
  rcases parse_ok_lexed_provenance file output result with
    ⟨lexed, _lexing, parsing, tokens, _diagnostics, comments⟩
  have paired := parseLexed_ok_coreOrdinary_sound_and_validFor
    diagnosticFree parsing
  exact ⟨by simpa only [tokens, comments] using paired.1, paired.2⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CompleteOutputProperties
/-! Complete provenance contract for successful public parser output. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace ParseOutput

/-- Canonical syntax and every retained diagnostic carrier belong to one file. -/
structure CanonicalValidFor (output : ParseOutput) (file : SourceFile) : Prop where
  parsed : Parser.CanonicalParsedFileValid file output.parsed
  tokens : ∀ token ∈ output.tokens, token.span.ValidFor file
  lexicalDiagnostics : ∀ diagnostic ∈ output.lexicalDiagnostics,
    diagnostic.span.ValidFor file
  parseDiagnostics : ∀ diagnostic ∈ output.parseDiagnostics,
    diagnostic.span.ValidFor file

end ParseOutput

namespace Parser

/-- Successful token-to-syntax parsing satisfies the complete output contract. -/
theorem parseLexed_ok_completeOutput_validFor
    (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (result : parseLexed file lexed = .ok output) :
    output.CanonicalValidFor file := by
  have lexedValid := parseLexed_ok_input_validFor file lexed output result
  have retained := parseLexed_ok_retention file lexed output result
  exact {
    parsed := parseLexed_ok_complete_validFor file lexed output lexedValid result
    tokens := by
      intro token member
      exact lexedValid.token_span (by
        simpa only [retained.1] using member)
    lexicalDiagnostics := by
      intro diagnostic member
      exact lexedValid.diagnostic_span (by
        simpa only [retained.2.1] using member)
    parseDiagnostics :=
      parseLexed_ok_parseDiagnostics_validFor
        FileInternals.contractDecl_canonical_inputs file lexed output result
  }

/-- Successful public source parsing satisfies the complete output contract. -/
theorem parse_ok_completeOutput_validFor
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    output.CanonicalValidFor file := by
  unfold parse at result
  cases lexing : Lexer.lex file with
  | error diagnostic => simp [lexing] at result
  | ok lexed =>
      cases parsing : parseLexed file lexed with
      | error error => simp [lexing, parsing] at result
      | ok parsedOutput =>
          have outputEq : parsedOutput = output := by
            simpa [lexing, parsing] using result
          subst output
          exact parseLexed_ok_completeOutput_validFor file lexed parsedOutput
            parsing

end Parser

end Solcore.Syntax
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicSourceFileOrdinaryOutcomeSoundnessProperties
/-! Broad syntax outcomes at both public canonical parser boundaries. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful token-to-file parse has the exact public syntax shape:
either the canonical empty file after nesting overflow, or the recovery-aware
source-file grammar from the root token window. -/
theorem parseLexed_ok_publicSourceFileOrdinary_sound
    {file : SourceFile} {lexed : LexedFile} {output : ParseOutput}
    (result : parseLexed file lexed = .ok output) :
    DeclarativeGrammar.PublicSourceFileOrdinaryParses file
      lexed.tokens lexed.comments output.parsed := by
  have lexedValid := parseLexed_ok_input_validFor file lexed output result
  unfold parseLexed at result
  rw [validateLexed_validFor_ok file lexed lexedValid] at result
  change (match checkNesting lexed.tokens with
    | some diagnostic => Except.ok ({
        parsed := {
          source := file.id
          span := SourceSpan.fullFile file
          items := []
          comments := lexed.comments
        }
        tokens := lexed.tokens
        lexicalDiagnostics := lexed.diagnostics
        parseDiagnostics :=
          filterParseDiagnostics file lexed.diagnostics [diagnostic]
      } : ParseOutput)
    | none =>
        match sourceFile lexed.comments
            (State.initial file lexed) with
        | .ok parsed finalState => Except.ok ({
            parsed
            tokens := lexed.tokens
            lexicalDiagnostics := lexed.diagnostics
            parseDiagnostics := filterParseDiagnostics file
              lexed.diagnostics finalState.diagnostics
          } : ParseOutput)
        | .reject failure _ => Except.error
            (ParserInvariantError.noProgress .topLevel failure.span)
        | .invariant error => Except.error error) = .ok output at result
  cases nesting : checkNesting lexed.tokens with
  | some diagnostic =>
      have exceeds :=
        (checkNesting_some_iff_nestingExceeds
          lexed.tokens diagnostic).mp nesting
      rcases exceeds with ⟨overflow, overflowScan, _diagnosticEq⟩
      simp only [nesting] at result
      cases result
      exact .nestingExceeded overflowScan
  | none =>
      have clears :=
        (checkNesting_none_iff_nestingClears lexed.tokens).mp nesting
      simp only [nesting] at result
      cases grammar : sourceFile lexed.comments
          (State.initial file lexed) with
      | ok parsed finalState =>
          simp only [grammar] at result
          cases result
          have sourceParsed :=
            FileInternals.sourceFile_success_ordinaryOutcome_sound grammar
          apply DeclarativeGrammar.PublicSourceFileOrdinaryParses.sourceFile
            clears
          simpa [DeclarativeGrammar.sourceFileRootRemainder,
            State.initial, State.declarativeRemainder] using sourceParsed
      | reject failure rejected =>
          simp only [grammar] at result
          contradiction
      | invariant error =>
          simp only [grammar] at result
          contradiction

/-- Broad token-to-file syntax soundness paired with the complete canonical
validity contract for every retained public carrier. -/
theorem parseLexed_ok_publicSourceFileOrdinary_sound_and_validFor
    {file : SourceFile} {lexed : LexedFile} {output : ParseOutput}
    (result : parseLexed file lexed = .ok output) :
    DeclarativeGrammar.PublicSourceFileOrdinaryParses file
        lexed.tokens lexed.comments output.parsed ∧
      output.CanonicalValidFor file :=
  ⟨parseLexed_ok_publicSourceFileOrdinary_sound result,
    parseLexed_ok_completeOutput_validFor file lexed output result⟩

/-- Every successful source parse has the broad syntax outcome over the exact
tokens and comments retained by its public output. -/
theorem parse_ok_publicSourceFileOrdinary_sound
    {file : SourceFile} {output : ParseOutput}
    (result : parse file = .ok output) :
    DeclarativeGrammar.PublicSourceFileOrdinaryParses file
      output.tokens output.parsed.comments output.parsed := by
  rcases parse_ok_lexed_provenance file output result with
    ⟨lexed, _lexing, parsing, tokens, _diagnostics, comments⟩
  simpa only [tokens, comments] using
    parseLexed_ok_publicSourceFileOrdinary_sound parsing

/-- Broad source parsing soundness paired with the complete canonical output
validity contract. -/
theorem parse_ok_publicSourceFileOrdinary_sound_and_validFor
    {file : SourceFile} {output : ParseOutput}
    (result : parse file = .ok output) :
    DeclarativeGrammar.PublicSourceFileOrdinaryParses file
        output.tokens output.parsed.comments output.parsed ∧
      output.CanonicalValidFor file :=
  ⟨parse_ok_publicSourceFileOrdinary_sound result,
    parse_ok_completeOutput_validFor file output result⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CertifiedParseProperties
/-! Total public parsing with complete provenance for the returned output. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Valid tokenized input produces an output whose complete provenance belongs
to the source file. -/
theorem productionParseLexed_exists_ok_completeOutput_validFor
    (file : SourceFile) (lexed : LexedFile) (lexedValid : lexed.ValidFor file) :
    ∃ output,
      parseLexed file lexed = .ok output ∧ output.CanonicalValidFor file := by
  rcases productionParseLexed_exists_ok file lexed lexedValid with
    ⟨output, parsed⟩
  exact ⟨output, parsed,
    parseLexed_ok_completeOutput_validFor file lexed output parsed⟩

/-- Every source file produces an output whose complete provenance belongs to
that source file. -/
theorem productionParse_exists_ok_completeOutput_validFor
    (file : SourceFile) :
    ∃ output, parse file = .ok output ∧ output.CanonicalValidFor file := by
  rcases productionParse_exists_ok file with ⟨output, parsed⟩
  exact ⟨output, parsed, parse_ok_completeOutput_validFor file output parsed⟩

/-- Valid tokenized input produces a broad public syntax derivation together
with the complete canonical output contract. -/
theorem productionParseLexed_exists_ok_publicSourceFileOrdinary
    (file : SourceFile) (lexed : LexedFile) (lexedValid : lexed.ValidFor file) :
    ∃ output,
      parseLexed file lexed = .ok output ∧
        DeclarativeGrammar.PublicSourceFileOrdinaryParses file
          lexed.tokens lexed.comments output.parsed ∧
        output.CanonicalValidFor file := by
  rcases productionParseLexed_exists_ok file lexed lexedValid with
    ⟨output, parsed⟩
  exact ⟨output, parsed,
    parseLexed_ok_publicSourceFileOrdinary_sound_and_validFor parsed⟩

/-- Every source file produces a broad public syntax derivation over its exact
retained carriers together with the complete canonical output contract. -/
theorem productionParse_exists_ok_publicSourceFileOrdinary
    (file : SourceFile) :
    ∃ output,
      parse file = .ok output ∧
        DeclarativeGrammar.PublicSourceFileOrdinaryParses file
          output.tokens output.parsed.comments output.parsed ∧
        output.CanonicalValidFor file := by
  rcases productionParse_exists_ok file with ⟨output, parsed⟩
  exact ⟨output, parsed,
    parse_ok_publicSourceFileOrdinary_sound_and_validFor parsed⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CertifiedLexedParseOutcomeProperties
/-! Branch-complete certification of the public token-to-file boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

/-- A public token-to-file error is exactly the mapped first declarative
validation rejection. No later parser invariant can escape. -/
theorem productionParseLexed_error_iff_validationRejects
    (file : SourceFile) (lexed : LexedFile)
    (error : ParserInvariantError) :
    parseLexed file lexed = .error error ↔
      ∃ failure,
        LexedFileValidationRejects file lexed failure ∧
          error = lexedValidationInvariantError failure := by
  rw [productionParseLexed_error_iff_validateLexed_error]
  exact validateLexed_error_iff_validationRejects file lexed error

/--
Every tokenized source has one certified outer public branch. Rejection exposes
the exact first validation failure. Acceptance exposes an actual output, broad
public syntax, exact retained lexical carriers, and complete canonical
validity. The theorem deliberately does not claim an independent exact trace
for normal-branch parse diagnostics.
-/
theorem productionParseLexed_certifiedOutcome
    (file : SourceFile) (lexed : LexedFile) :
    (∃ failure,
      LexedFileValidationRejects file lexed failure ∧
        parseLexed file lexed =
          .error (lexedValidationInvariantError failure)) ∨
    (∃ output,
      LexedFileValidationAccepts file lexed ∧
        parseLexed file lexed = .ok output ∧
        PublicSourceFileOrdinaryParses file
          lexed.tokens lexed.comments output.parsed ∧
        output.tokens = lexed.tokens ∧
        output.lexicalDiagnostics = lexed.diagnostics ∧
        output.parsed.comments = lexed.comments ∧
        output.CanonicalValidFor file) := by
  rcases lexedFileValidationOutcome_total file lexed with
    accepts | ⟨failure, rejects⟩
  · have valid :=
      (lexedFileValidationAccepts_iff_validFor file lexed).mp accepts
    rcases productionParseLexed_exists_ok_publicSourceFileOrdinary
        file lexed valid with
      ⟨output, parsed, syntaxOutcome, canonical⟩
    rcases parseLexed_ok_retention file lexed output parsed with
      ⟨tokens, diagnostics, comments⟩
    exact Or.inr ⟨output, accepts, parsed, syntaxOutcome, tokens, diagnostics,
      comments, canonical⟩
  · apply Or.inl
    refine ⟨failure, rejects, ?_⟩
    exact (productionParseLexed_error_iff_validationRejects file lexed
      (lexedValidationInvariantError failure)).mpr ⟨failure, rejects, rfl⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicSourceFileValueProperties
/-! Public parsed-file value uniqueness; no public remainder or rejection is invented. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- At the same supplied file and lexed carrier, including its source, span,
tokens, and comments, successful public parses agree on their syntax AST. -/
theorem parseLexed_ok_parsed_value_unique_of_topItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      DeclarativeGrammar.TopItemOrdinaryParses input left afterLeft →
      DeclarativeGrammar.TopItemOrdinaryParses input right afterRight → left = right)
    {file : SourceFile} {lexed : LexedFile} {left right : ParseOutput}
    (leftResult : parseLexed file lexed = .ok left)
    (rightResult : parseLexed file lexed = .ok right) :
    left.parsed = right.parsed :=
  DeclarativeGrammar.PublicSourceFileOrdinaryParses.value_unique_of_topItem
    itemValues (parseLexed_ok_publicSourceFileOrdinary_sound leftResult)
    (parseLexed_ok_publicSourceFileOrdinary_sound rightResult)

/-- Exact top-item outcomes fix public syntax at one supplied lexed carrier. -/
theorem parseLexed_ok_parsed_value_unique_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    {file : SourceFile} {lexed : LexedFile} {left right : ParseOutput}
    (leftResult : parseLexed file lexed = .ok left)
    (rightResult : parseLexed file lexed = .ok right) :
    left.parsed = right.parsed :=
  parseLexed_ok_parsed_value_unique_of_topItemValues itemOutcomes.successValueUnique
    leftResult rightResult

/-- Two successful parses of the same source file share one lexical result;
top-item value uniqueness therefore fixes their complete public syntax AST. -/
theorem parse_ok_parsed_value_unique_of_topItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      DeclarativeGrammar.TopItemOrdinaryParses input left afterLeft →
      DeclarativeGrammar.TopItemOrdinaryParses input right afterRight → left = right)
    {file : SourceFile} {left right : ParseOutput}
    (leftResult : parse file = .ok left)
    (rightResult : parse file = .ok right) : left.parsed = right.parsed := by
  rcases parse_ok_lexed_provenance file left leftResult with
    ⟨leftLexed, leftLexing, leftParsing, leftTokens, leftDiagnostics, leftComments⟩
  rcases parse_ok_lexed_provenance file right rightResult with
    ⟨rightLexed, rightLexing, rightParsing, rightTokens, rightDiagnostics,
      rightComments⟩
  have lexedEq : leftLexed = rightLexed :=
    Except.ok.inj (leftLexing.symm.trans rightLexing)
  subst lexedEq
  exact parseLexed_ok_parsed_value_unique_of_topItemValues itemValues
    leftParsing rightParsing

/-- Exact top-item outcomes fix public syntax at one supplied source file. -/
theorem parse_ok_parsed_value_unique_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    {file : SourceFile} {left right : ParseOutput}
    (leftResult : parse file = .ok left)
    (rightResult : parse file = .ok right) : left.parsed = right.parsed :=
  parse_ok_parsed_value_unique_of_topItemValues itemOutcomes.successValueUnique
    leftResult rightResult

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SyntaxExactnessProperties
/-! Unconditional complete-file syntax exactness at the executable boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace FileInternals

/-- All declaration branches supply an exact recovery-aware file loop. -/
theorem parseItems_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FileItemsOrdinaryParses DeclarativeGrammar.FileItemsRejects :=
  DeclarativeGrammar.fileItemsExactOutcomeSpec

/-- At shared fuel and reverse prefix, file loops fix their complete forward result. -/
theorem parseItems_success_result_unique (fuel : Nat) (itemsRev : List TopItem)
    {input leftOutput rightOutput : State} {left right : List TopItem}
    (leftResult : parseItems fuel itemsRev input = .ok left leftOutput)
    (rightResult : parseItems fuel itemsRev input = .ok right rightOutput) :
    left = right ∧ leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  parseItems_success_result_unique_of_topItem DeclarativeGrammar.topItemExactOutcomeSpec
    fuel itemsRev leftResult rightResult

/-- Fixed file provenance and comments give exact source-file outcomes. -/
theorem sourceFile_exactOutcomeSpec (file : SourceFile) (comments : List Comment) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.SourceFileOrdinaryParses file comments)
      DeclarativeGrammar.SourceFileRejects :=
  DeclarativeGrammar.sourceFileExactOutcomeSpec file comments

/-- Complete source-file successes agree on their attached AST and remainder. -/
theorem sourceFile_success_result_unique (comments : List Comment)
    {input leftOutput rightOutput : State} {left right : ParsedFile}
    (leftResult : sourceFile comments input = .ok left leftOutput)
    (rightResult : sourceFile comments input = .ok right rightOutput) :
    left = right ∧ leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  sourceFile_success_result_unique_of_topItem DeclarativeGrammar.topItemExactOutcomeSpec
    comments leftResult rightResult

end FileInternals

/-- At fixed source and lexical carriers, successful public parses have one syntax AST. -/
theorem parseLexed_ok_parsed_value_unique
    {file : SourceFile} {lexed : LexedFile} {left right : ParseOutput}
    (leftResult : parseLexed file lexed = .ok left)
    (rightResult : parseLexed file lexed = .ok right) : left.parsed = right.parsed :=
  parseLexed_ok_parsed_value_unique_of_topItem DeclarativeGrammar.topItemExactOutcomeSpec
    leftResult rightResult

/-- Successful parses of one source file have one complete public syntax AST. -/
theorem parse_ok_parsed_value_unique
    {file : SourceFile} {left right : ParseOutput}
    (leftResult : parse file = .ok left)
    (rightResult : parse file = .ok right) : left.parsed = right.parsed :=
  parse_ok_parsed_value_unique_of_topItem DeclarativeGrammar.topItemExactOutcomeSpec
    leftResult rightResult

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicParseCompletenessProperties
/-! Exact public AST correspondence with validation and lexical provenance. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A token-to-file result with the specified AST exists exactly when the supplied
carrier passes validation and the independent public grammar derives that AST.
Both nesting branches are included, without a diagnostic-free premise. -/
theorem parseLexed_exists_ok_iff_publicSourceFileOrdinary_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (file : SourceFile) (lexed : LexedFile) (parsed : ParsedFile) :
    (∃ output, parseLexed file lexed = .ok output ∧ output.parsed = parsed) ↔
      DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧
        DeclarativeGrammar.PublicSourceFileOrdinaryParses file
          lexed.tokens lexed.comments parsed := by
  constructor
  · rintro ⟨output, result, rfl⟩
    exact ⟨(DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
      (parseLexed_ok_input_validFor file lexed output result),
      parseLexed_ok_publicSourceFileOrdinary_sound result⟩
  · rintro ⟨accepted, expected⟩
    have valid :=
      (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mp accepted
    rcases productionParseLexed_exists_ok file lexed valid with ⟨output, result⟩
    exact ⟨output, result,
      DeclarativeGrammar.PublicSourceFileOrdinaryParses.value_unique_of_exact_topItem
        itemOutcomes (parseLexed_ok_publicSourceFileOrdinary_sound result) expected⟩

/-- A source-to-file result with the specified AST exists exactly when canonical
lexing supplies carriers on which the independent public grammar derives that AST.
The lexical witness supplies all required carrier validity. -/
theorem parse_exists_ok_iff_publicSourceFileOrdinary_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (file : SourceFile) (parsed : ParsedFile) :
    (∃ output, parse file = .ok output ∧ output.parsed = parsed) ↔
      ∃ lexed, Lexer.lex file = .ok lexed ∧
        DeclarativeGrammar.PublicSourceFileOrdinaryParses file
          lexed.tokens lexed.comments parsed := by
  constructor
  · rintro ⟨output, result, rfl⟩
    rcases parse_ok_lexed_provenance file output result with
      ⟨lexed, lexing, parsing, _⟩
    exact ⟨lexed, lexing, parseLexed_ok_publicSourceFileOrdinary_sound parsing⟩
  · rintro ⟨lexed, lexing, expected⟩
    have accepted :=
      (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
        (Lexer.lex_ok_validFor file lexed lexing)
    rcases (parseLexed_exists_ok_iff_publicSourceFileOrdinary_of_topItem
        itemOutcomes file lexed parsed).mpr ⟨accepted, expected⟩ with
      ⟨output, parsing, valueEq⟩
    exact ⟨output, by simp only [parse, lexing, parsing], valueEq⟩

/-- Public token-to-file AST correspondence has no recursive exactness premise.
Validation remains explicit because the syntax relation does not certify carriers. -/
theorem parseLexed_exists_ok_iff_publicSourceFileOrdinary
    (file : SourceFile) (lexed : LexedFile) (parsed : ParsedFile) :
    (∃ output, parseLexed file lexed = .ok output ∧ output.parsed = parsed) ↔
      DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧
        DeclarativeGrammar.PublicSourceFileOrdinaryParses file
          lexed.tokens lexed.comments parsed :=
  parseLexed_exists_ok_iff_publicSourceFileOrdinary_of_topItem
    DeclarativeGrammar.topItemExactOutcomeSpec file lexed parsed

/-- Public source-to-file AST correspondence has no validity or recursive
exactness premise: canonical lexical provenance supplies the input certificate. -/
theorem parse_exists_ok_iff_publicSourceFileOrdinary
    (file : SourceFile) (parsed : ParsedFile) :
    (∃ output, parse file = .ok output ∧ output.parsed = parsed) ↔
      ∃ lexed, Lexer.lex file = .ok lexed ∧
        DeclarativeGrammar.PublicSourceFileOrdinaryParses file
          lexed.tokens lexed.comments parsed :=
  parse_exists_ok_iff_publicSourceFileOrdinary_of_topItem
    DeclarativeGrammar.topItemExactOutcomeSpec file parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicSourceFileGrammarProperties
/-! Consequences for independent public syntax, with no executable parser
reply in the hypotheses: validated carriers determine one AST, and every such
derivation satisfies the complete recursive source-provenance contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An independently derived public AST over validated carriers has valid
recursive source spans, including recovered and nesting-overflow syntax. -/
theorem PublicSourceFileOrdinaryParses.validFor_of_validation
    {file : SourceFile} {lexed : LexedFile} {parsed : ParsedFile}
    (accepted : LexedFileValidationAccepts file lexed)
    (derivation : PublicSourceFileOrdinaryParses file
      lexed.tokens lexed.comments parsed) :
    ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor file parsed := by
  rcases (Parser.parseLexed_exists_ok_iff_publicSourceFileOrdinary
      file lexed parsed).mpr ⟨accepted, derivation⟩ with
    ⟨output, result, valueEq⟩
  have valid := (Parser.parseLexed_ok_completeOutput_validFor
    file lexed output result).parsed
  simpa only [valueEq] using valid

/-- Validated token carriers have exactly one independently derived public
AST. No diagnostic-free or nesting-clearance hypothesis is required. -/
theorem publicSourceFileOrdinary_exists_unique_of_validation
    (file : SourceFile) (lexed : LexedFile)
    (accepted : LexedFileValidationAccepts file lexed) :
    ∃ parsed,
      PublicSourceFileOrdinaryParses file lexed.tokens lexed.comments parsed ∧
      ∀ other, PublicSourceFileOrdinaryParses file
        lexed.tokens lexed.comments other → other = parsed := by
  have valid := (lexedFileValidationAccepts_iff_validFor file lexed).mp accepted
  rcases Parser.productionParseLexed_exists_ok_publicSourceFileOrdinary
      file lexed valid with ⟨output, _, derivation, _⟩
  exact ⟨output.parsed, derivation, fun _ other =>
    PublicSourceFileOrdinaryParses.value_unique other derivation⟩

/-- Canonical lexical provenance supplies validation for any independently
derived public AST; no executable parser result is assumed. -/
theorem PublicSourceFileOrdinaryParses.validFor_of_lexing
    {file : SourceFile} {lexed : LexedFile} {parsed : ParsedFile}
    (lexing : Lexer.lex file = .ok lexed)
    (derivation : PublicSourceFileOrdinaryParses file
      lexed.tokens lexed.comments parsed) :
    ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor file parsed :=
  derivation.validFor_of_validation
    ((lexedFileValidationAccepts_iff_validFor file lexed).mpr
      (Lexer.lex_ok_validFor file lexed lexing))

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemsCompletenessProperties
/-! Complete ordinary file-item grammar correspondence at sufficient fuel.
The fixed reverse accumulator stays outside the declarative grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- At sufficient fuel, grammar success for a fresh suffix is exactly loop
execution returning the fixed accumulated prefix followed by that suffix. -/
theorem parseItems_ordinary_success_iff_of_remainingCount_lt
    (fuel : Nat) (itemsRev : List TopItem)
    {input : State} (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    {suffix : List TopItem} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.FileItemsOrdinaryParses
      input.declarativeRemainder suffix remainder ↔
      ∃ output, parseItems fuel itemsRev input =
        .ok (itemsRev.reverse ++ suffix) output ∧
        output.declarativeRemainder = remainder := by
  constructor
  · intro parsed
    rcases parseItems_exists_ok_of_remainingCount_lt
        productionParseItemsItemInvariantFree fuel itemsRev input inputValid
          adequate with ⟨items, output, result⟩
    rcases parseItems_success_ordinaryOutcome_sound_strong fuel itemsRev input
        items output result with ⟨actual, itemsEq, actualParsed⟩
    rcases parseItems_exactOutcomeSpec.successResultUnique actualParsed parsed with
      ⟨suffixEq, remainderEq⟩
    refine ⟨output, ?_, remainderEq⟩
    simpa only [itemsEq, suffixEq] using result
  · rintro ⟨output, result, remainderEq⟩
    rcases parseItems_success_ordinaryOutcome_sound_strong fuel itemsRev input
        (itemsRev.reverse ++ suffix) output result with
      ⟨actual, itemsEq, actualParsed⟩
    have suffixEq : suffix = actual := List.append_cancel_left itemsEq
    cases suffixEq
    exact remainderEq ▸ actualParsed

/-- The production fuel discharges adequacy while retaining the exact
forward prefix and fresh suffix in the executable result. -/
theorem parseItems_production_ordinary_success_iff (itemsRev : List TopItem)
    {input : State} (inputValid : input.ValidFor)
    {suffix : List TopItem} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.FileItemsOrdinaryParses
      input.declarativeRemainder suffix remainder ↔
      ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ suffix) output ∧
        output.declarativeRemainder = remainder :=
  parseItems_ordinary_success_iff_of_remainingCount_lt
    (input.remainingCount + 1) itemsRev inputValid (by omega)

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemCompletenessProperties
/-! Complete plain and derive-aware top-item grammar correspondence on valid
states, retaining complete ASTs and declarative success or rejection endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Independent plainTopItem success is exactly executable success with the same
AST and declarative remainder on a valid input. -/
theorem plainTopItem_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : TopItem} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.PlainTopItemOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, plainTopItem input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok plainTopItem plainTopItem_exactOutcomeSpec
    (productionPlainTopItem_ne_invariant input inputValid)
    plainTopItem_success_ordinaryOutcome_sound plainTopItem_reject_ordinaryOutcome_sound

/-- Independent plainTopItem rejection is exactly executable rejection at the
same declarative endpoint; failure diagnostics remain existential. -/
theorem plainTopItem_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.PlainTopItemRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, plainTopItem input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject plainTopItem plainTopItem_exactOutcomeSpec
    (productionPlainTopItem_ne_invariant input inputValid)
    plainTopItem_success_ordinaryOutcome_sound plainTopItem_reject_ordinaryOutcome_sound

/-- Independent topItem success is exactly executable success with the same
AST and declarative remainder on a valid input. -/
theorem topItem_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : TopItem} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TopItemOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, topItem input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok topItem topItem_exactOutcomeSpec
    (productionTopItem_ne_invariant input inputValid)
    topItem_success_ordinaryOutcome_sound topItem_reject_ordinaryOutcome_sound

/-- Independent topItem rejection is exactly executable rejection at the
same declarative endpoint; failure diagnostics remain existential. -/
theorem topItem_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TopItemRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, topItem input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject topItem topItem_exactOutcomeSpec
    (productionTopItem_ne_invariant input inputValid)
    topItem_success_ordinaryOutcome_sound topItem_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.SyntaxCompletenessProperties
/-! Public correspondence between independent ordinary syntax and execution.
Success identifies full ASTs and declarative remainders; rejection identifies
its declarative endpoint, not failure payloads or complete parser states. -/
end
