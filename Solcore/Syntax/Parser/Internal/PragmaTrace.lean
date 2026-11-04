import Solcore.Syntax.Internal.PragmaTrace
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.Internal.TypeTrace
import Solcore.Syntax.Parser.Internal.ExportSoundness
import Solcore.Syntax.Parser.Internal.ParseProperties
import Solcore.Syntax.Parser.Internal.BlockTrace
import Solcore.Syntax.Grammar.Modules
import Solcore.Syntax.Parser.Internal.DelimitedSoundness

/-!
Parser side of the traces of pragmas: the parsers produce exactly the events of the trace
grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaItemsTraceProperties
/-! Exact forward diagnostic suffixes from successful pragma item scans. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

/-- Any successful tail adds precisely the events of its new suffix, never
re-emitting diagnostics for identifiers already in the reverse accumulator. -/
theorem pragmaItemsTail_success_diagnosticTrace :
    ∀ fuel itemsRev input items output,
      pragmaItemsTail fuel itemsRev input = .ok items output →
      ∃ suffix trace,
        items = itemsRev.reverse ++ suffix ∧
        DeclarativeGrammar.IdentifierListDiagnosticTrace suffix trace ∧
        output.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items output result
      simp [pragmaItemsTail] at result
  | succ fuel ih =>
      intro itemsRev input items output result
      unfold pragmaItemsTail at result
      split at result
      · cases commaResult : symbol .comma .pragmaDecl input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            have commaSilent := acceptToken_success_diagnostics_eq
              (.symbol .comma) .pragmaDecl (· == .symbol .comma) commaResult
            simp only [commaResult] at result
            split at result
            · cases result
              exact ⟨[], [], by simp, .nil,
                by simpa only [List.append_nil] using commaSilent⟩
            · cases itemResult : identifier .pragmaDecl afterComma with
              | invariant error => simp [itemResult] at result
              | reject failure rejected => simp [itemResult] at result
              | ok item afterItem =>
                  simp only [itemResult] at result
                  rcases ih (item :: itemsRev) afterItem items output result with
                    ⟨suffix, tailTrace, itemsEq, tailDiagnostics, tailEq⟩
                  rcases identifier_success_diagnosticTrace .pragmaDecl itemResult with
                    ⟨headTrace, headDiagnostics, headEq⟩
                  refine ⟨item :: suffix, headTrace ++ tailTrace, ?_,
                    .cons headDiagnostics tailDiagnostics, ?_⟩
                  · simpa only [List.reverse_cons, List.append_assoc,
                      List.singleton_append] using itemsEq
                  · rw [tailEq, headEq, commaSilent, List.append_assoc]
      · cases result
        exact ⟨[], [], by simp, .nil, by simp⟩

/-- Production tail success combines the independent suffix grammar with
exact new events while leaving the pre-existing accumulator prefix outside it. -/
theorem pragmaItemsTail_production_success_trace_sound
    (itemsRev : List Identifier) {input output : State} {items : List Identifier}
    (result : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .ok items output) :
    ∃ suffix trace,
      items = itemsRev.reverse ++ suffix ∧
      DeclarativeGrammar.PragmaItemsTailTraceParses input.declarativeRemainder
        suffix output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaItemsTail_production_success_ordinaryOutcome_sound itemsRev result with
    ⟨suffix, itemsEq, ordinary⟩
  rcases pragmaItemsTail_success_diagnosticTrace (input.remainingCount + 1)
      itemsRev input items output result with
    ⟨tracedSuffix, trace, tracedItemsEq, diagnostics, diagnosticEq⟩
  have suffixEq : tracedSuffix = suffix :=
    List.append_cancel_left (tracedItemsEq.symm.trans itemsEq)
  subst tracedSuffix
  exact ⟨suffix, trace, itemsEq, ⟨ordinary, diagnostics⟩, diagnosticEq⟩

/-- Complete item scanning emits only the ordered per-name diagnostic events. -/
theorem pragmaItems_success_diagnosticTrace
    {input output : State} {items : List Identifier}
    (result : pragmaItems input = .ok items output) :
    ∃ trace, DeclarativeGrammar.IdentifierListDiagnosticTrace items trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  unfold pragmaItems at result
  split at result
  · cases result
    exact ⟨[], .nil, by simp⟩
  · cases firstResult : identifier .pragmaDecl input with
    | invariant error => simp [firstResult] at result
    | reject failure rejected => simp [firstResult] at result
    | ok first afterFirst =>
        simp only [firstResult] at result
        rcases pragmaItemsTail_success_diagnosticTrace (afterFirst.remainingCount + 1)
            [first] afterFirst items output result with
          ⟨suffix, tailTrace, itemsEq, tailDiagnostics, tailEq⟩
        have itemsForm : items = first :: suffix := by simpa using itemsEq
        subst items
        rcases identifier_success_diagnosticTrace .pragmaDecl firstResult with
          ⟨headTrace, headDiagnostics, headEq⟩
        exact ⟨headTrace ++ tailTrace, .cons headDiagnostics tailDiagnostics,
          by rw [tailEq, headEq, List.append_assoc]⟩

/-- Independent item events fix the exact added diagnostic sequence. -/
theorem pragmaItems_success_diagnostics_eq_of_trace
    {input output : State} {items : List Identifier} {trace : List ParseDiagnostic}
    (result : pragmaItems input = .ok items output)
    (diagnostics : DeclarativeGrammar.IdentifierListDiagnosticTrace items trace) :
    output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaItems_success_diagnosticTrace result with
    ⟨actual, actualTrace, actualEq⟩
  simpa only [actualTrace.trace_unique diagnostics] using actualEq

/-- Executable item success derives the full independent AST, remainder,
and trace relation without assuming the input diagnostics are empty. -/
theorem pragmaItems_success_trace_sound
    {input output : State} {items : List Identifier}
    (result : pragmaItems input = .ok items output) :
    ∃ trace, DeclarativeGrammar.PragmaItemsTraceParses input.declarativeRemainder
        items output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaItems_success_diagnosticTrace result with ⟨trace, diagnostics, diagnosticEq⟩
  exact ⟨trace, ⟨pragmaItems_success_ordinaryOutcome_sound result, diagnostics⟩,
    diagnosticEq⟩

end Solcore.Syntax.Parser.PragmaInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaItemsTraceCompletenessProperties
/-! Complete independent success traces for pragma suffixes and item lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

private theorem pragmaItemsTail_production_success_ordinary_iff
    (itemsRev : List Identifier) {input : State} {suffix : List Identifier}
    {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.PragmaItemsTailOrdinaryParses
      input.declarativeRemainder suffix remainder ↔
      ∃ output, pragmaItemsTail (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ suffix) output ∧
        output.declarativeRemainder = remainder := by
  constructor
  · intro ordinary
    cases result : pragmaItemsTail (input.remainingCount + 1) itemsRev input with
    | ok items output =>
        rcases pragmaItemsTail_production_success_ordinaryOutcome_sound itemsRev result with
          ⟨actual, itemsEq, parsed⟩
        rcases pragmaItemsTail_exactOutcomeSpec.successResultUnique parsed ordinary with
          ⟨suffixEq, after⟩
        exact ⟨output, by simp only [itemsEq, suffixEq], after⟩
    | reject failure rejected =>
        exact False.elim (pragmaItemsTail_exactOutcomeSpec.successRejectDisjoint
          (pragmaItemsTail_production_reject_ordinaryOutcome_sound itemsRev result)
          ⟨suffix, remainder, ordinary⟩)
    | invariant error =>
        exact False.elim (pragmaItemsTail_production_ne_invariant itemsRev input error result)
  · rintro ⟨output, result, after⟩
    rcases pragmaItemsTail_production_success_ordinaryOutcome_sound itemsRev result with
      ⟨actual, itemsEq, parsed⟩
    have suffixEq : suffix = actual := List.append_cancel_left itemsEq
    simpa only [← suffixEq, after] using parsed

/-- With a fixed accumulated prefix, only independently traced suffix items
contribute new diagnostics to a successful production-tail execution. -/
theorem pragmaItemsTail_production_success_diagnostics_eq_of_trace
    (itemsRev : List Identifier) {input output : State}
    {suffix : List Identifier} {trace : List ParseDiagnostic}
    (result : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .ok (itemsRev.reverse ++ suffix) output)
    (diagnostics : DeclarativeGrammar.IdentifierListDiagnosticTrace suffix trace) :
    output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaItemsTail_production_success_trace_sound itemsRev result with
    ⟨actual, actualTrace, itemsEq, parsed, actualEq⟩
  have suffixEq : suffix = actual := List.append_cancel_left itemsEq
  subst actual
  simpa only [parsed.2.trace_unique diagnostics] using actualEq

/-- Independent suffix AST, remainder, and trace correspond exactly to
production-tail success, with the fixed prefix outside the new event sequence. -/
theorem pragmaItemsTail_production_trace_success_iff
    (itemsRev : List Identifier) {input : State} {suffix : List Identifier}
    {remainder : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaItemsTailTraceParses
      input.declarativeRemainder suffix remainder trace ↔
      ∃ output, pragmaItemsTail (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ suffix) output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨ordinary, diagnostics⟩
    rcases (pragmaItemsTail_production_success_ordinary_iff itemsRev).mp ordinary with
      ⟨output, result, after⟩
    exact ⟨output, result, after,
      pragmaItemsTail_production_success_diagnostics_eq_of_trace itemsRev result diagnostics⟩
  · rintro ⟨output, result, after, diagnosticEq⟩
    refine ⟨(pragmaItemsTail_production_success_ordinary_iff itemsRev).mpr
      ⟨output, result, after⟩, ?_⟩
    rcases DeclarativeGrammar.identifierListDiagnosticTrace_total suffix with
      ⟨actual, diagnostics⟩
    have actualEq := pragmaItemsTail_production_success_diagnostics_eq_of_trace
      itemsRev result diagnostics
    have traceEq : actual = trace := List.append_cancel_left
      (actualEq.symm.trans diagnosticEq)
    simpa only [traceEq] using diagnostics

private theorem pragmaItems_success_ordinary_iff
    {input : State} {items : List Identifier} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.PragmaItemsOrdinaryParses input.declarativeRemainder items remainder ↔
      ∃ output, pragmaItems input = .ok items output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok pragmaItems pragmaItems_exactOutcomeSpec
    (pragmaItems_ne_invariant input)
    pragmaItems_success_ordinaryOutcome_sound pragmaItems_reject_ordinaryOutcome_sound

/-- Complete item grammar and diagnostic order correspond exactly to execution,
including empty lists and silent trailing commas. -/
theorem pragmaItems_trace_success_iff
    {input : State} {items : List Identifier} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaItemsTraceParses input.declarativeRemainder items remainder trace ↔
      ∃ output, pragmaItems input = .ok items output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨ordinary, diagnostics⟩
    rcases pragmaItems_success_ordinary_iff.mp ordinary with ⟨output, result, after⟩
    exact ⟨output, result, after, pragmaItems_success_diagnostics_eq_of_trace result diagnostics⟩
  · rintro ⟨output, result, after, diagnosticEq⟩
    refine ⟨pragmaItems_success_ordinary_iff.mpr ⟨output, result, after⟩, ?_⟩
    rcases pragmaItems_success_diagnosticTrace result with ⟨actual, diagnostics, actualEq⟩
    have traceEq : actual = trace := List.append_cancel_left
      (actualEq.symm.trans diagnosticEq)
    simpa only [traceEq] using diagnostics

end Solcore.Syntax.Parser.PragmaInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaDeclarationTraceProperties
/-! Complete pragma success traces: raw names and punctuation remain silent. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Only the checked item identifiers emit events during a successful pragma.
The raw pragma name contributes none, even when its spelling has a hyphen. -/
theorem pragmaDecl_success_diagnosticTrace
    {input output : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration output) :
    ∃ trace, DeclarativeGrammar.IdentifierListDiagnosticTrace
        declaration.value.items trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  unfold pragmaDecl at result
  rcases bind_ok_components result with
    ⟨pragmaKeyword, afterKeyword, keywordResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, itemsStage⟩
  rcases bind_ok_components itemsStage with
    ⟨items, afterItems, itemsResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  have keywordSilent := acceptToken_success_diagnostics_eq
    (.keyword .pragmaKw) .pragmaDecl (· == .keyword .pragmaKw) keywordResult
  have nameSilent := rawIdentifier_success_diagnostics_eq .pragmaDecl nameResult
  have semicolonSilent := acceptToken_success_diagnostics_eq
    (.symbol .semicolon) .pragmaDecl (· == .symbol .semicolon) semicolonResult
  rcases PragmaInternals.pragmaItems_success_diagnosticTrace itemsResult with
    ⟨trace, diagnostics, diagnosticEq⟩
  exact ⟨trace, diagnostics,
    by rw [semicolonSilent, diagnosticEq, nameSilent, keywordSilent]⟩

/-- An independent item trace determines the complete added pragma diagnostics. -/
theorem pragmaDecl_success_diagnostics_eq_of_trace
    {input output : State} {declaration : PragmaDecl} {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .ok declaration output)
    (diagnostics : DeclarativeGrammar.IdentifierListDiagnosticTrace
      declaration.value.items trace) :
    output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaDecl_success_diagnosticTrace result with ⟨actual, actualTrace, actualEq⟩
  simpa only [actualTrace.trace_unique diagnostics] using actualEq

/-- Every successful pragma derives the complete independent traced grammar. -/
theorem pragmaDecl_success_trace_sound
    {input output : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration output) :
    ∃ trace, DeclarativeGrammar.PragmaDeclTraceParses input.declarativeRemainder
        declaration output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaDecl_success_diagnosticTrace result with ⟨trace, diagnostics, diagnosticEq⟩
  exact ⟨trace, ⟨pragmaDecl_success_ordinaryOutcome_sound result, diagnostics⟩,
    diagnosticEq⟩

private theorem pragmaDecl_success_ordinary_iff
    {input : State} {declaration : PragmaDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.PragmaDeclOrdinaryParses input.declarativeRemainder
        declaration remainder ↔
      ∃ output, pragmaDecl input = .ok declaration output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok pragmaDecl pragmaDecl_exactOutcomeSpec
    (pragmaDecl_ne_invariant input)
    pragmaDecl_success_ordinaryOutcome_sound pragmaDecl_reject_ordinaryOutcome_sound

/-- Independent pragma AST, remainder, and ordered diagnostic trace are
equivalent to exact executable success, preserving every prior diagnostic. -/
theorem pragmaDecl_trace_success_iff
    {input : State} {declaration : PragmaDecl} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaDeclTraceParses input.declarativeRemainder
        declaration remainder trace ↔
      ∃ output, pragmaDecl input = .ok declaration output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨ordinary, diagnostics⟩
    rcases pragmaDecl_success_ordinary_iff.mp ordinary with ⟨output, result, after⟩
    exact ⟨output, result, after, pragmaDecl_success_diagnostics_eq_of_trace result diagnostics⟩
  · rintro ⟨output, result, after, diagnosticEq⟩
    refine ⟨pragmaDecl_success_ordinary_iff.mpr ⟨output, result, after⟩, ?_⟩
    rcases pragmaDecl_success_diagnosticTrace result with ⟨actual, diagnostics, actualEq⟩
    have traceEq : actual = trace := List.append_cancel_left
      (actualEq.symm.trans diagnosticEq)
    simpa only [traceEq] using diagnostics

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaSequenceTraceProperties
/-! Independent successful pragma sequences determine complete raw file-loop
traces. Existing reverse prefixes are returned but never parsed or diagnosed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- A pragma-only sequence executes at any fuel larger than its declaration
count. Its exact suffix follows the existing prefix without rediagnosing it. -/
theorem parseItems_pragmaSequence_trace_of_length_lt
    (fuel : Nat) (itemsRev : List TopItem)
    {input : State} {declarations : List PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.PragmaSequenceTraceParses
      input.declarativeRemainder declarations after trace)
    (adequate : declarations.length < fuel) :
    ∃ output, parseItems fuel itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing itemsRev input declarations after trace with
  | zero => omega
  | succ fuel ih =>
      cases parsed with
      | done atEnd =>
          have ended : input.atEnd = true := by
            exact decide_eq_true atEnd
          refine ⟨input, ?_, rfl, by simp⟩
          simp only [parseItems, ended, if_true, List.map_nil, List.append_nil]
      | cons headParsed tailParsed =>
          rename_i afterHead head tail headTrace tailTrace
          rcases (pragmaDecl_trace_success_iff (input := input)).mp headParsed with
            ⟨next, declarationResult, nextRemainder, nextTrace⟩
          have marker : ∃ span afterKeyword,
              DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
                input.declarativeRemainder span afterKeyword := by
            cases headParsed.1 with
            | parsed span _ keywordParsed _ _ _ => exact ⟨span, _, keywordParsed⟩
          rcases marker with ⟨span, afterKeyword, keywordParsed⟩
          have itemResult : parseItemsItem input = .ok (wrapPragma head) next := by
            unfold parseItemsItem
            rw [topItem_eq_pragma_of_exactTokenParses keywordParsed]
            simp only [mapTopItem, declarationResult]
          have progress := pragmaDecl_cursor_lt_onSuccess declarationResult
          have inside := headParsed.1.startsInside
          have notEnded : input.atEnd = false := by
            exact decide_eq_false (Nat.not_le_of_gt inside)
          rw [← nextRemainder] at tailParsed
          rcases ih (wrapPragma head :: itemsRev) tailParsed (by
              simp only [List.length_cons] at adequate; omega) with
            ⟨output, result, remainderEq, traceEq⟩
          refine ⟨output, ?_, remainderEq, ?_⟩
          · simp only [parseItems, notEnded, Bool.false_eq_true, if_false,
              itemResult, progress, if_true]
            simpa only [List.reverse_cons, List.append_assoc,
              List.singleton_append, List.map_cons] using result
          · rw [traceEq, nextTrace, List.append_assoc]

/-- Remaining-token adequacy is a sufficient, declaration-count-independent
bound. Neither valid input nor initially empty diagnostics is required. -/
theorem parseItems_pragmaSequence_trace_of_remainingCount_lt
    (fuel : Nat) (itemsRev : List TopItem)
    {input : State} {declarations : List PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.PragmaSequenceTraceParses
      input.declarativeRemainder declarations after trace)
    (adequate : input.remainingCount < fuel) :
    ∃ output, parseItems fuel itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace := by
  apply parseItems_pragmaSequence_trace_of_length_lt fuel itemsRev parsed
  have bound : declarations.length ≤ input.remainingCount := parsed.length_le_remaining
  omega

/-- The production fuel always suffices for an independently derived complete
pragma sequence, retaining the precise fresh ASTs, endpoint, and raw trace. -/
theorem parseItems_production_pragmaSequence_trace
    (itemsRev : List TopItem) {input : State} {declarations : List PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.PragmaSequenceTraceParses
      input.declarativeRemainder declarations after trace) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace :=
  parseItems_pragmaSequence_trace_of_remainingCount_lt
    (input.remainingCount + 1) itemsRev parsed (by omega)

/-- The complete pragma-only window produces the exact comment-attached file.
File wrapping emits no event and does not reorder declarations or diagnostics. -/
theorem sourceFile_pragmaSequence_trace (comments : List Comment)
    {input : State} {declarations : List PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.PragmaSequenceTraceParses
      input.declarativeRemainder declarations after trace) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := (declarations.map wrapPragma).map (attachTopItemComments input.file comments)
        comments
      } output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases parseItems_production_pragmaSequence_trace [] parsed with
    ⟨output, result, remainderEq, traceEq⟩
  refine ⟨output, ?_, remainderEq, traceEq⟩
  simp only [sourceFile, List.reverse_nil, List.nil_append, result]

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaItemsRejectionTraceProperties
/-! Exact uncommitted reports and committed prefix events for item rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

private theorem identifier_success_context_eq (context : ParseContext)
    {input output : State} {name : Identifier}
    (result : identifier context input = .ok name output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold identifier at result
  cases raw : rawIdentifier context input with
  | reject failure rejected => simp [raw] at result
  | invariant error => simp [raw] at result
  | ok parsed afterName =>
      rcases rawIdentifier_ok_tokenAt context raw with ⟨_, rfl⟩
      simp only [raw] at result
      split at result <;> cases result <;> exact ⟨rfl, rfl⟩

private theorem identifier_rejected_report
    {input rejected : State} {failure : Failure}
    (result : identifier .pragmaDecl input = .reject failure rejected) :
    DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
      { head := .identifier, tail := [] } .pragmaDecl
      rejected.declarativeRemainder failure.toDiagnostic := by
  have stateEq := identifier_reject_state_eq .pragmaDecl result
  subst rejected
  exact ((identifier_reject_reports_iff .pragmaDecl).mpr ⟨failure, result, rfl⟩).2

/-- Rejection at any fuel retains exactly the events of newly checked names.
The accumulator never contributes events, and the final failure is not emitted. -/
theorem pragmaItemsTail_reject_trace_sound :
    ∀ fuel itemsRev input failure rejected,
      pragmaItemsTail fuel itemsRev input = .reject failure rejected →
      ∃ trace,
        DeclarativeGrammar.PragmaItemsTailTraceRejects input.file.id input.window.endByte
          input.declarativeRemainder rejected.declarativeRemainder
          failure.toDiagnostic trace ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input failure rejected result
      simp [pragmaItemsTail] at result
  | succ fuel ih =>
      intro itemsRev input failure rejected result
      unfold pragmaItemsTail at result
      cases commaPresent : isSymbol input .comma with
      | false => simp [commaPresent] at result
      | true =>
          rcases symbol_eq_ok_of_isSymbol_eq_true .comma .pragmaDecl commaPresent with
            ⟨comma, commaResult⟩
          simp only [commaPresent, if_true, commaResult] at result
          split at result
          · contradiction
          · rename_i semicolonAbsent
            cases itemResult : identifier .pragmaDecl
                { input with cursor := input.cursor + 1 } with
            | invariant error => simp [itemResult] at result
            | reject itemFailure itemRejected =>
                simp only [itemResult] at result
                cases result
                refine ⟨[], ⟨[], .identifierRejected comma.span
                  (symbol_success_exactTokenParses .comma .pragmaDecl commaResult)
                  (symbolAbsentAt_of_isSymbol_eq_false .semicolon
                    (by simpa using semicolonAbsent))
                  (identifier_reject_sound .pragmaDecl itemResult), .nil,
                  identifier_rejected_report
                    (input := { input with cursor := input.cursor + 1 }) itemResult⟩, ?_⟩
                simpa only [List.append_nil, State.diagnostics] using
                  identifier_reject_diagnostics_eq .pragmaDecl itemResult
            | ok item afterItem =>
                simp only [itemResult] at result
                rcases ih (item :: itemsRev) afterItem failure rejected result with
                  ⟨tailTrace, ⟨consumed, tailParsed, tailEvents, report⟩, tailEq⟩
                rcases identifier_success_diagnosticTrace .pragmaDecl itemResult with
                  ⟨headTrace, headEvents, headEq⟩
                rcases identifier_success_context_eq .pragmaDecl itemResult with
                  ⟨fileEq, windowEq⟩
                refine ⟨headTrace ++ tailTrace,
                  ⟨item :: consumed, .laterRejected comma.span
                    (symbol_success_exactTokenParses .comma .pragmaDecl commaResult)
                    (symbolAbsentAt_of_isSymbol_eq_false .semicolon
                      (by simpa using semicolonAbsent))
                    (identifier_success_sound .pragmaDecl itemResult) tailParsed,
                    .cons headEvents tailEvents, ?_⟩, ?_⟩
                · simpa only [fileEq, windowEq] using report
                · rw [tailEq, headEq, List.append_assoc]
                  rfl

/-- Full item rejection includes the first successful checked name and every
later successful item in order, with no event for the rejected identifier. -/
theorem pragmaItems_reject_trace_sound
    {input rejected : State} {failure : Failure}
    (result : pragmaItems input = .reject failure rejected) :
    ∃ trace,
      DeclarativeGrammar.PragmaItemsTraceRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected.declarativeRemainder
        failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  unfold pragmaItems at result
  split at result
  · contradiction
  · rename_i semicolonAbsent
    cases firstResult : identifier .pragmaDecl input with
    | invariant error => simp [firstResult] at result
    | reject firstFailure firstRejected =>
        simp only [firstResult] at result
        cases result
        refine ⟨[], ⟨[], .firstIdentifierRejected
          (symbolAbsentAt_of_isSymbol_eq_false .semicolon
            (by simpa using semicolonAbsent))
          (identifier_reject_sound .pragmaDecl firstResult), .nil,
          identifier_rejected_report firstResult⟩, ?_⟩
        simpa only [List.append_nil] using
          identifier_reject_diagnostics_eq .pragmaDecl firstResult
    | ok first afterFirst =>
        simp only [firstResult] at result
        rcases pragmaItemsTail_reject_trace_sound (afterFirst.remainingCount + 1)
            [first] afterFirst failure rejected result with
          ⟨tailTrace, ⟨consumed, tailParsed, tailEvents, report⟩, tailEq⟩
        rcases identifier_success_diagnosticTrace .pragmaDecl firstResult with
          ⟨headTrace, headEvents, headEq⟩
        rcases identifier_success_context_eq .pragmaDecl firstResult with
          ⟨fileEq, windowEq⟩
        refine ⟨headTrace ++ tailTrace,
          ⟨first :: consumed, .tailRejected
            (symbolAbsentAt_of_isSymbol_eq_false .semicolon
              (by simpa using semicolonAbsent))
            (identifier_success_sound .pragmaDecl firstResult) tailParsed,
            .cons headEvents tailEvents, ?_⟩, ?_⟩
        · simpa only [fileEq, windowEq] using report
        · rw [tailEq, headEq, List.append_assoc]

end Solcore.Syntax.Parser.PragmaInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaItemsRejectionTraceCompletenessProperties
/-! Complete rejecting pragma-item traces without state-validity assumptions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

/-- Fixed accumulated names do not alter the new trace or the uncommitted
report. Production-tail rejection is exactly the independent trace relation. -/
theorem pragmaItemsTail_production_trace_reject_iff
    (itemsRev : List Identifier) {input : State}
    {remainder : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaItemsTailTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace ↔
      ∃ failure output,
        pragmaItemsTail (input.remainingCount + 1) itemsRev input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        failure.toDiagnostic = diagnostic ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    cases result : pragmaItemsTail (input.remainingCount + 1) itemsRev input with
    | ok items output =>
        rcases traced with ⟨consumed, rejected, _, _⟩
        rcases pragmaItemsTail_production_success_ordinaryOutcome_sound itemsRev result with
          ⟨suffix, _, ordinary⟩
        exact False.elim (pragmaItemsTail_exactOutcomeSpec.successRejectDisjoint
          rejected.ordinary ⟨suffix, output.declarativeRemainder, ordinary⟩)
    | invariant error =>
        exact False.elim (pragmaItemsTail_production_ne_invariant itemsRev input error result)
    | reject failure output =>
        rcases pragmaItemsTail_reject_trace_sound (input.remainingCount + 1)
            itemsRev input failure output result with
          ⟨actualTrace, actual, diagnostics⟩
        rcases actual.result_unique traced with ⟨after, report, events⟩
        exact ⟨failure, output, rfl, after, report, events ▸ diagnostics⟩
  · rintro ⟨failure, output, result, after, report, diagnostics⟩
    rcases pragmaItemsTail_reject_trace_sound (input.remainingCount + 1)
        itemsRev input failure output result with
      ⟨actualTrace, actual, actualDiagnostics⟩
    have events : actualTrace = trace :=
      List.append_cancel_left (actualDiagnostics.symm.trans diagnostics)
    simpa only [after, report, events] using actual

/-- Complete item rejection fixes the endpoint, exact failure report, and
ordered committed events, independently of all pre-existing diagnostics. -/
theorem pragmaItems_trace_reject_iff
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaItemsTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace ↔
      ∃ failure output, pragmaItems input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        failure.toDiagnostic = diagnostic ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    cases result : pragmaItems input with
    | ok items output =>
        rcases traced with ⟨consumed, rejected, _, _⟩
        exact False.elim (pragmaItems_exactOutcomeSpec.successRejectDisjoint
          rejected.ordinary ⟨items, output.declarativeRemainder,
            pragmaItems_success_ordinaryOutcome_sound result⟩)
    | invariant error =>
        exact False.elim (pragmaItems_ne_invariant input error result)
    | reject failure output =>
        rcases pragmaItems_reject_trace_sound result with
          ⟨actualTrace, actual, diagnostics⟩
        rcases actual.result_unique traced with ⟨after, report, events⟩
        exact ⟨failure, output, rfl, after, report, events ▸ diagnostics⟩
  · rintro ⟨failure, output, result, after, report, diagnostics⟩
    rcases pragmaItems_reject_trace_sound result with
      ⟨actualTrace, actual, actualDiagnostics⟩
    have events : actualTrace = trace :=
      List.append_cancel_left (actualDiagnostics.symm.trans diagnostics)
    simpa only [after, report, events] using actual

/-- Report conversion loses no information: tail traces fix every field of
the uncommitted failure itself, not only its eventual diagnostic projection. -/
theorem pragmaItemsTail_production_trace_reject_failure_iff
    (itemsRev : List Identifier) {input : State} {failure : Failure}
    {remainder : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaItemsTailTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace ↔
      ∃ output,
        pragmaItemsTail (input.remainingCount + 1) itemsRev input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    rcases (pragmaItemsTail_production_trace_reject_iff itemsRev).mp traced with
      ⟨actual, output, result, after, report, diagnostics⟩
    have failureEq := Failure.toDiagnostic_injective report
    subst actual
    exact ⟨output, result, after, diagnostics⟩
  · rintro ⟨output, result, after, diagnostics⟩
    exact (pragmaItemsTail_production_trace_reject_iff itemsRev).mpr
      ⟨failure, output, result, after, rfl, diagnostics⟩

/-- Independent complete item traces likewise fix the entire failure payload. -/
theorem pragmaItems_trace_reject_failure_iff
    {input : State} {failure : Failure} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaItemsTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace ↔
      ∃ output, pragmaItems input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    rcases pragmaItems_trace_reject_iff.mp traced with
      ⟨actual, output, result, after, report, diagnostics⟩
    have failureEq := Failure.toDiagnostic_injective report
    subst actual
    exact ⟨output, result, after, diagnostics⟩
  · rintro ⟨output, result, after, diagnostics⟩
    exact pragmaItems_trace_reject_iff.mpr
      ⟨failure, output, result, after, rfl, diagnostics⟩

end Solcore.Syntax.Parser.PragmaInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaDeclarationRejectionTraceProperties
/-! Exact uncommitted failures and retained events for complete pragma rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every rejected declaration realizes exactly one independent failing stage.
Only completed checked items have emitted events; the failure remains uncommitted. -/
theorem pragmaDecl_reject_trace_sound
    {input rejected : State} {failure : Failure}
    (result : pragmaDecl input = .reject failure rejected) :
    ∃ trace,
      DeclarativeGrammar.PragmaDeclTraceRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected.declarativeRemainder
        failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  unfold pragmaDecl at result
  cases keywordResult : keyword .pragmaKw .pragmaDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      have rejectedEq := keyword_reject_state_eq .pragmaKw .pragmaDecl keywordResult
      subst keywordRejected
      simp only [bind, keywordResult] at result
      cases result
      refine ⟨[], .keywordMissing
        (keyword_reject_tokenKindAbsentAt .pragmaKw .pragmaDecl keywordResult)
        (acceptToken_reject_reports (.keyword .pragmaKw) .pragmaDecl
          (· == .keyword .pragmaKw) keywordResult).1, ?_⟩
      simp only [List.append_nil]
  | ok pragmaKeyword afterKeyword =>
      simp only [bind, keywordResult] at result
      have keywordParsed := keyword_success_exactTokenParses .pragmaKw .pragmaDecl keywordResult
      have keywordShape := (keyword_ok_tokenAt .pragmaKw .pragmaDecl keywordResult).2
      have keywordSilent := acceptToken_success_diagnostics_eq
        (.keyword .pragmaKw) .pragmaDecl (· == .keyword .pragmaKw) keywordResult
      cases nameResult : rawIdentifier .pragmaDecl afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          have checked : identifier .pragmaDecl afterKeyword =
              .reject nameFailure nameRejected := by simp only [identifier, nameResult]
          have rejectedEq := identifier_reject_state_eq .pragmaDecl checked
          subst nameRejected
          simp only [nameResult] at result
          cases result
          refine ⟨[], .nameRejected pragmaKeyword.span keywordParsed
            (rawIdentifier_reject_ordinaryOutcome_sound .pragmaDecl nameResult) ?_, ?_⟩
          · have report := ((rawIdentifier_reject_reports_iff .pragmaDecl).mpr
              ⟨failure, nameResult, rfl⟩).2
            simpa only [keywordShape] using report
          · simpa only [List.append_nil] using keywordSilent
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := rawIdentifier_success_ordinaryOutcome_sound .pragmaDecl nameResult
          have nameShape := (rawIdentifier_ok_tokenAt .pragmaDecl nameResult).2
          have nameSilent := rawIdentifier_success_diagnostics_eq .pragmaDecl nameResult
          cases itemsResult : PragmaInternals.pragmaItems afterName with
          | invariant error => simp [itemsResult] at result
          | reject itemsFailure itemsRejected =>
              simp only [itemsResult] at result
              cases result
              rcases PragmaInternals.pragmaItems_reject_trace_sound itemsResult with
                ⟨trace, traced, diagnostics⟩
              refine ⟨trace, .itemsRejected pragmaKeyword.span keywordParsed nameParsed ?_, ?_⟩
              · simpa only [nameShape, keywordShape] using traced
              · rw [diagnostics, nameSilent, keywordSilent]
          | ok items afterItems =>
              simp only [itemsResult] at result
              rcases PragmaInternals.pragmaItems_success_trace_sound itemsResult with
                ⟨trace, itemsParsed, diagnostics⟩
              have itemsContext := PragmaInternals.pragmaItems_success_context_eq itemsResult
              cases semicolonResult : symbol .semicolon .pragmaDecl afterItems with
              | invariant error => simp [semicolonResult] at result
              | ok semicolon output => simp [semicolonResult, pure] at result
              | reject semicolonFailure semicolonRejected =>
                  have rejectedEq := symbol_reject_state_eq .semicolon .pragmaDecl semicolonResult
                  subst semicolonRejected
                  simp only [semicolonResult] at result
                  cases result
                  refine ⟨trace, .semicolonMissing pragmaKeyword.span keywordParsed nameParsed
                    itemsParsed (symbol_reject_tokenKindAbsentAt .semicolon .pragmaDecl
                      semicolonResult) ?_, ?_⟩
                  · have report := (acceptToken_reject_reports (.symbol .semicolon) .pragmaDecl
                      (· == .symbol .semicolon) semicolonResult).1
                    simpa only [itemsContext.1, itemsContext.2, nameShape, keywordShape] using report
                  · rw [diagnostics, nameSilent, keywordSilent]

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaDeclarationRejectionTraceCompletenessProperties
/-! Complete independent pragma rejection, including every failure field. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- An independently derived rejecting trace fixes an existing execution's
endpoint, uncommitted report, and exact retained diagnostic sequence. -/
theorem pragmaDecl_reject_exact_of_trace
    {input output : State} {failure : Failure} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .reject failure output)
    (traced : DeclarativeGrammar.PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace) :
    output.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaDecl_reject_trace_sound result with ⟨actualTrace, actual, diagnostics⟩
  rcases actual.result_unique traced with ⟨after, report, events⟩
  exact ⟨after, report, events ▸ diagnostics⟩

/-- Independent first-failure grammar and exact execution are equivalent.
No input-validity or empty-prior-diagnostics premise is required. -/
theorem pragmaDecl_trace_reject_iff
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace ↔
      ∃ failure output, pragmaDecl input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    cases result : pragmaDecl input with
    | ok declaration output =>
        exact False.elim (pragmaDecl_exactOutcomeSpec.successRejectDisjoint traced.ordinary
          ⟨declaration, output.declarativeRemainder,
            pragmaDecl_success_ordinaryOutcome_sound result⟩)
    | invariant error =>
        exact False.elim (pragmaDecl_ne_invariant input error result)
    | reject failure output =>
        exact ⟨failure, output, rfl, pragmaDecl_reject_exact_of_trace result traced⟩
  · rintro ⟨failure, output, result, after, report, diagnostics⟩
    rcases pragmaDecl_reject_trace_sound result with
      ⟨actualTrace, actual, actualDiagnostics⟩
    have events : actualTrace = trace :=
      List.append_cancel_left (actualDiagnostics.symm.trans diagnostics)
    simpa only [after, report, events] using actual

/-- Diagnostic projection is injective on failures, so the relation can fix
the complete uncommitted failure, not just its later diagnostic rendering. -/
theorem pragmaDecl_trace_reject_failure_iff
    {input : State} {failure : Failure} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace ↔
      ∃ output, pragmaDecl input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    rcases pragmaDecl_trace_reject_iff.mp traced with
      ⟨actual, output, result, after, report, diagnostics⟩
    have failureEq := Failure.toDiagnostic_injective report
    subst actual
    exact ⟨output, result, after, diagnostics⟩
  · rintro ⟨output, result, after, diagnostics⟩
    exact pragmaDecl_trace_reject_iff.mpr
      ⟨failure, output, result, after, rfl, diagnostics⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaNameRejectionTraceProperties
/-! An independently observed missing pragma name fixes the complete
uncommitted failure and preserves the existing raw diagnostic sequence. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- After the exact pragma marker, an unavailable raw name fails at the
independently observed span/token. Only the marker cursor step is retained. -/
theorem pragmaDecl_nameMissing_exact
    {input : State} {marker span : SourceSpan} {found : Option TokenKind}
    {after : DeclarativeGrammar.Remainder}
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after)
    (nameAbsent : DeclarativeGrammar.IdentifierAbsentAt after)
    (current : DeclarativeGrammar.CurrentInputAt input.file.id input.window.endByte
      after span found) :
    pragmaDecl input = .reject {
        span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { input with cursor := input.cursor + 1 } ∧
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder = after ∧
      ({ input with cursor := input.cursor + 1 } : State).diagnostics = input.diagnostics := by
  let advanced : State := { input with cursor := input.cursor + 1 }
  have advancedEq : advanced.declarativeRemainder = after := keywordParsed.2.symm
  have absent : DeclarativeGrammar.IdentifierAbsentAt advanced.declarativeRemainder := by
    simpa only [advancedEq] using nameAbsent
  have observed : DeclarativeGrammar.CurrentInputAt advanced.file.id advanced.window.endByte
      advanced.declarativeRemainder span found := by
    simpa only [advancedEq] using current
  rcases currentInputAt_iff_currentSpan_peekKind.mp observed with ⟨spanEq, foundEq⟩
  have nameResult := rawIdentifier_eq_rejectAt_of_identifierAbsent .pragmaDecl absent
  simp only [rejectAt, spanEq, foundEq] at nameResult
  refine ⟨?_, advancedEq, rfl⟩
  simp only [pragmaDecl, bind, pragmaKeyword_eq_ok_of_exactTokenParses keywordParsed]
  rw [nameResult]

/-- The packaged independent missing-name judgment yields the same exact
failure without any executable success or rejection premise. -/
theorem pragmaDecl_nameMissingAt_exact
    {input : State} {span : SourceSpan} {found : Option TokenKind}
    {after : DeclarativeGrammar.Remainder}
    (missing : DeclarativeGrammar.PragmaNameMissingAt input.file.id input.window.endByte
      input.declarativeRemainder after span found) :
    pragmaDecl input = .reject {
        span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { input with cursor := input.cursor + 1 } ∧
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder = after ∧
      ({ input with cursor := input.cursor + 1 } : State).diagnostics = input.diagnostics := by
  cases missing with
  | missing keywordParsed nameAbsent current =>
      exact pragmaDecl_nameMissing_exact keywordParsed nameAbsent current

namespace FileInternals

/-- Attribute-free pragma dispatch preserves the exact leaf failure and its
silent raw diagnostic trace. -/
theorem plainTopItem_pragmaNameMissing_exact
    {input : State} {marker span : SourceSpan} {found : Option TokenKind}
    {after : DeclarativeGrammar.Remainder}
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after)
    (nameAbsent : DeclarativeGrammar.IdentifierAbsentAt after)
    (current : DeclarativeGrammar.CurrentInputAt input.file.id input.window.endByte
      after span found) :
    plainTopItem input = .reject {
        span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { input with cursor := input.cursor + 1 } ∧
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder = after ∧
      ({ input with cursor := input.cursor + 1 } : State).diagnostics = input.diagnostics := by
  rcases pragmaDecl_nameMissing_exact keywordParsed nameAbsent current with
    ⟨rejected, afterEq, diagnosticsEq⟩
  refine ⟨?_, afterEq, diagnosticsEq⟩
  rw [plainTopItem_eq_pragma_of_exactTokenParses keywordParsed]
  simp only [mapTopItem, rejected]

/-- A leading pragma cannot enter derive parsing; its exact name failure is
returned unchanged through the derive-aware dispatcher. -/
theorem topItem_pragmaNameMissing_exact
    {input : State} {marker span : SourceSpan} {found : Option TokenKind}
    {after : DeclarativeGrammar.Remainder}
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after)
    (nameAbsent : DeclarativeGrammar.IdentifierAbsentAt after)
    (current : DeclarativeGrammar.CurrentInputAt input.file.id input.window.endByte
      after span found) :
    topItem input = .reject {
        span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { input with cursor := input.cursor + 1 } ∧
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder = after ∧
      ({ input with cursor := input.cursor + 1 } : State).diagnostics = input.diagnostics := by
  rcases pragmaDecl_nameMissing_exact keywordParsed nameAbsent current with
    ⟨rejected, afterEq, diagnosticsEq⟩
  refine ⟨?_, afterEq, diagnosticsEq⟩
  rw [topItem_eq_pragma_of_exactTokenParses keywordParsed]
  simp only [mapTopItem, rejected]

/-- The file-loop item boundary has the identical failure and no emitted event. -/
theorem parseItemsItem_pragmaNameMissing_exact
    {input : State} {marker span : SourceSpan} {found : Option TokenKind}
    {after : DeclarativeGrammar.Remainder}
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after)
    (nameAbsent : DeclarativeGrammar.IdentifierAbsentAt after)
    (current : DeclarativeGrammar.CurrentInputAt input.file.id input.window.endByte
      after span found) :
    parseItemsItem input = .reject {
        span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { input with cursor := input.cursor + 1 } ∧
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder = after ∧
      ({ input with cursor := input.cursor + 1 } : State).diagnostics = input.diagnostics :=
  topItem_pragmaNameMissing_exact keywordParsed nameAbsent current

/-- The packaged independent report also crosses the loop-item boundary. -/
theorem parseItemsItem_pragmaNameMissingAt_exact
    {input : State} {span : SourceSpan} {found : Option TokenKind}
    {after : DeclarativeGrammar.Remainder}
    (missing : DeclarativeGrammar.PragmaNameMissingAt input.file.id input.window.endByte
      input.declarativeRemainder after span found) :
    parseItemsItem input = .reject {
        span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { input with cursor := input.cursor + 1 } ∧
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder = after ∧
      ({ input with cursor := input.cursor + 1 } : State).diagnostics = input.diagnostics := by
  cases missing with
  | missing keywordParsed nameAbsent current =>
      exact parseItemsItem_pragmaNameMissing_exact keywordParsed nameAbsent current

end FileInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaDeclarationContextProperties
/-! Unconditional file and complete-window frame laws for pragma declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Successful declarations retain the source file and the full report window,
including its end byte, independently of emitted events and input validity. -/
theorem pragmaDecl_success_context_eq
    {input output : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold pragmaDecl at result
  cases keywordResult : keyword .pragmaKw .pragmaDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject failure rejected => simp [bind, keywordResult] at result
  | ok marker afterKeyword =>
      simp only [bind, keywordResult] at result
      have keywordShape := (keyword_ok_tokenAt .pragmaKw .pragmaDecl keywordResult).2
      cases nameResult : rawIdentifier .pragmaDecl afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          have nameShape := (rawIdentifier_ok_tokenAt .pragmaDecl nameResult).2
          cases itemsResult : PragmaInternals.pragmaItems afterName with
          | invariant error => simp [itemsResult] at result
          | reject failure rejected => simp [itemsResult] at result
          | ok items afterItems =>
              simp only [itemsResult] at result
              have frame := PragmaInternals.pragmaItems_success_context_eq itemsResult
              cases semicolonResult : symbol .semicolon .pragmaDecl afterItems with
              | invariant error => simp [semicolonResult] at result
              | reject failure rejected => simp [semicolonResult] at result
              | ok semicolon afterSemicolon =>
                  simp only [semicolonResult] at result
                  cases result
                  have shape := (symbol_ok_tokenAt .semicolon .pragmaDecl semicolonResult).2
                  simp only [shape, frame.1, frame.2, nameShape, keywordShape, and_self]

/-- All rejecting stages retain the original source and complete window even
when earlier successful checked items have emitted diagnostics. -/
theorem pragmaDecl_reject_context_eq
    {input rejected : State} {failure : Failure}
    (result : pragmaDecl input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  unfold pragmaDecl at result
  cases keywordResult : keyword .pragmaKw .pragmaDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      simp only [bind, keywordResult] at result
      cases result
      rw [keyword_reject_state_eq .pragmaKw .pragmaDecl keywordResult]
      exact ⟨rfl, rfl⟩
  | ok marker afterKeyword =>
      simp only [bind, keywordResult] at result
      have keywordShape := (keyword_ok_tokenAt .pragmaKw .pragmaDecl keywordResult).2
      cases nameResult : rawIdentifier .pragmaDecl afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          have checked : identifier .pragmaDecl afterKeyword = .reject failure rejected := by
            simp only [identifier, nameResult]
          rw [identifier_reject_state_eq .pragmaDecl checked, keywordShape]
          exact ⟨rfl, rfl⟩
      | ok name afterName =>
          simp only [nameResult] at result
          have nameShape := (rawIdentifier_ok_tokenAt .pragmaDecl nameResult).2
          cases itemsResult : PragmaInternals.pragmaItems afterName with
          | invariant error => simp [itemsResult] at result
          | reject itemsFailure itemsRejected =>
              simp only [itemsResult] at result
              cases result
              have frame := PragmaInternals.pragmaItems_reject_context_eq itemsResult
              simp only [frame.1, frame.2, nameShape, keywordShape, and_self]
          | ok items afterItems =>
              simp only [itemsResult] at result
              have frame := PragmaInternals.pragmaItems_success_context_eq itemsResult
              cases semicolonResult : symbol .semicolon .pragmaDecl afterItems with
              | invariant error => simp [semicolonResult] at result
              | ok semicolon output => simp [semicolonResult, pure] at result
              | reject semicolonFailure semicolonRejected =>
                  simp only [semicolonResult] at result
                  cases result
                  rw [symbol_reject_state_eq .semicolon .pragmaDecl semicolonResult]
                  simp only [frame.1, frame.2, nameShape, keywordShape, and_self]

end Solcore.Syntax.Parser
end
