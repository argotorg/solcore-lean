import Solcore.Syntax.Parser.Internal.PragmaTrace
import Solcore.Syntax.Parser.Internal.ExportSoundness
import Solcore.Syntax.Parser.Internal.BlockTrace
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Parser.Internal.SourceFileTrace
import Solcore.Syntax.Parser.Internal.ExportProofs
import Solcore.Syntax.Internal.PragmaTrace
import Solcore.Syntax.Parser.Internal.ModuleTotality
import Solcore.Syntax.Parser.PublicOutputs
import Solcore.Syntax.Internal.TraceBasics

/-!
# Pragma tests

The pragma grammar, its rejection traces and prefix boundaries, and the public examples and
output properties of pragma sequences.
-/

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaDeclarationRejectionTraceProperties
/-! Independent four-stage rejection consumers, without whole-state claims. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaDeclarationRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @pragmaDecl_reject_trace_sound

example {input : State} {remainder : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace) :
    ∃ failure output, pragmaDecl input = .reject failure output ∧
      output.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaDecl_trace_reject_iff.mp traced

example {input output : State} {failure : Failure} {remainder : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .reject failure output)
    (after : output.declarativeRemainder = remainder)
    (report : failure.toDiagnostic = diagnostic)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace :=
  pragmaDecl_trace_reject_iff.mpr ⟨failure, output, result, after, report, diagnostics⟩

example {input : State} {failure : Failure} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace) :
    ∃ output, pragmaDecl input = .reject failure output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaDecl_trace_reject_failure_iff.mp traced

example {input output : State} {failure : Failure} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .reject failure output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace :=
  pragmaDecl_trace_reject_failure_iff.mpr ⟨output, result, after, diagnostics⟩

example {input output : State} {failure : Failure} {remainder : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .reject failure output)
    (traced : PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace) :
    output.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaDecl_reject_exact_of_trace result traced

example {input : State} {span : SourceSpan} {found : Option TokenKind}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.keyword .pragmaKw))
    (current : CurrentInputAt input.file.id input.window.endByte
      input.declarativeRemainder span found) :
    ∃ output, pragmaDecl input = .reject
        { span, found, expected := { head := .keyword .pragmaKw, tail := [] }, context := .pragmaDecl }
        output ∧ output.declarativeRemainder = input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using
    (pragmaDecl_trace_reject_failure_iff (trace := [])).mp
      (.keywordMissing absent (.reported current))

example {input : State} {afterKeyword rejected : Remainder}
    {marker span : SourceSpan} {found : Option TokenKind}
    (keywordParsed : ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker afterKeyword)
    (nameRejected : IdentifierRejects afterKeyword rejected)
    (current : CurrentInputAt input.file.id input.window.endByte rejected span found) :
    ∃ output, pragmaDecl input = .reject
        { span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl }
        output ∧ output.declarativeRemainder = rejected ∧
      output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using
    (pragmaDecl_trace_reject_failure_iff (trace := [])).mp
      (.nameRejected marker keywordParsed nameRejected (.reported current))

example {input : State} {afterKeyword afterName rejected : Remainder}
    {marker nameSpan : SourceSpan} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (keywordParsed : ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker afterKeyword)
    (rawName : IdentifierParses afterKeyword { span := nameSpan, value := "raw-name" } afterName)
    (itemsRejected : PragmaItemsTraceRejects input.file.id input.window.endByte
      afterName rejected diagnostic trace) :
    ∃ failure output, pragmaDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaDecl_trace_reject_iff.mp (.itemsRejected marker keywordParsed rawName itemsRejected)

example {input : State} {afterKeyword afterName afterItems : Remainder}
    {marker span : SourceSpan} {found : Option TokenKind}
    {name : Identifier} {items : List Identifier} {trace : List ParseDiagnostic}
    (keywordParsed : ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker afterKeyword)
    (rawName : IdentifierParses afterKeyword name afterName)
    (itemsParsed : PragmaItemsTraceParses afterName items afterItems trace)
    (absent : TokenKindAbsentAt afterItems.tokens afterItems.endIndex
      afterItems.cursor (.symbol .semicolon))
    (current : CurrentInputAt input.file.id input.window.endByte afterItems span found) :
    ∃ output, pragmaDecl input = .reject
        { span, found, expected := { head := .symbol .semicolon, tail := [] }, context := .pragmaDecl }
        output ∧ output.declarativeRemainder = afterItems ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaDecl_trace_reject_failure_iff.mp
    (.semicolonMissing marker keywordParsed rawName itemsParsed absent (.reported current))

end Solcore.Test.SyntaxParserPragmaDeclarationRejectionTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaExactnessProperties
/-! External consumers of exact pragma items and complete declarations. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.PragmaItemsTailOrdinaryParses
    DeclarativeGrammar.PragmaItemsTailRejects :=
  PragmaInternals.pragmaItemsTail_exactOutcomeSpec

-- The executable reverse prefix is shared; the grammar retains a forward suffix.
example (itemsRev : List Identifier)
    {input output : State} {actual suffix : List Identifier}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : PragmaInternals.pragmaItemsTail (input.remainingCount + 1)
      itemsRev input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.PragmaItemsTailOrdinaryParses
      input.declarativeRemainder suffix afterExpected) :
    actual = itemsRev.reverse ++ suffix ∧
      output.declarativeRemainder = afterExpected := by
  rcases PragmaInternals.pragmaItemsTail_production_success_ordinaryOutcome_sound
    itemsRev result with ⟨actualSuffix, actualEq, actualParsed⟩
  rcases PragmaInternals.pragmaItemsTail_exactOutcomeSpec.successResultUnique
    actualParsed expectedParsed with ⟨suffixEq, afterEq⟩
  exact ⟨actualEq.trans (congrArg (itemsRev.reverse ++ ·) suffixEq), afterEq⟩

example (itemsRev : List Identifier)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : PragmaInternals.pragmaItemsTail (input.remainingCount + 1)
      itemsRev input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.PragmaItemsTailRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  PragmaInternals.pragmaItemsTail_exactOutcomeSpec.rejectOutputUnique
    (PragmaInternals.pragmaItemsTail_production_reject_ordinaryOutcome_sound
      itemsRev result) expectedRejected

example := @PragmaInternals.pragmaItemsTail_production_success_result_unique
example := @PragmaInternals.pragmaItemsTail_production_reject_output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.PragmaItemsOrdinaryParses
    DeclarativeGrammar.PragmaItemsRejects :=
  PragmaInternals.pragmaItems_exactOutcomeSpec

example {input output : State} {actual expected : List Identifier}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : PragmaInternals.pragmaItems input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.PragmaItemsOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  PragmaInternals.pragmaItems_exactOutcomeSpec.successResultUnique
    (PragmaInternals.pragmaItems_success_ordinaryOutcome_sound result)
    expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : PragmaInternals.pragmaItems input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.PragmaItemsRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  PragmaInternals.pragmaItems_exactOutcomeSpec.rejectOutputUnique
    (PragmaInternals.pragmaItems_reject_ordinaryOutcome_sound result)
    expectedRejected

example := @PragmaInternals.pragmaItems_success_result_unique
example := @PragmaInternals.pragmaItems_reject_output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.PragmaDeclOrdinaryParses
    DeclarativeGrammar.PragmaDeclRejects :=
  pragmaDecl_exactOutcomeSpec

example {input output : State} {actual expected : PragmaDecl}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : pragmaDecl input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.PragmaDeclOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  pragmaDecl_exactOutcomeSpec.successResultUnique
    (pragmaDecl_success_ordinaryOutcome_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : pragmaDecl input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.PragmaDeclRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  pragmaDecl_exactOutcomeSpec.rejectOutputUnique
    (pragmaDecl_reject_ordinaryOutcome_sound result) expectedRejected

example := @pragmaDecl_success_result_unique
example := @pragmaDecl_reject_output_unique

end Solcore.Test.SyntaxParserPragmaExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaItemsContextProperties
/-! Context-frame consumers include invalid windows, arbitrary accumulated
diagnostics, emitted hyphen events, and reports after ordinary rejection. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaItemsContextProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PragmaInternals
open Solcore.Syntax.DeclarativeGrammar

example := @identifier_success_context_eq
example := @identifier_reject_context_eq
example := @pragmaItemsTail_success_context_eq
example := @pragmaItemsTail_reject_context_eq
example := @pragmaItems_success_context_eq
example := @pragmaItems_reject_context_eq

/-- A later semicolon rejection can report under the original source/end-byte
context after any successful item scan. -/
theorem successfulItems_transport_report
    {input output : State} {items : List Identifier} {remainder : Remainder}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    {diagnostic : ParseDiagnostic}
    (result : pragmaItems input = .ok items output)
    (report : RejectAtReports output.file.id output.window.endByte
      expected context remainder diagnostic) :
    RejectAtReports input.file.id input.window.endByte
      expected context remainder diagnostic := by
  rcases pragmaItems_success_context_eq result with ⟨fileEq, windowEq⟩
  simpa only [fileEq, windowEq] using report

/-- A rejected suffix transports its uncommitted payload under the same
original source context, for arbitrary fuel and existing reverse items. -/
theorem rejectedTail_transport_report (fuel : Nat) (itemsRev : List Identifier)
    {input rejected : State} {failure : Failure} {diagnostic : ParseDiagnostic}
    (result : pragmaItemsTail fuel itemsRev input = .reject failure rejected)
    (report : RejectAtReports rejected.file.id rejected.window.endByte
      { head := .identifier, tail := [] } .pragmaDecl
      rejected.declarativeRemainder diagnostic) :
    RejectAtReports input.file.id input.window.endByte
      { head := .identifier, tail := [] } .pragmaDecl
      rejected.declarativeRemainder diagnostic := by
  rcases pragmaItemsTail_reject_context_eq fuel itemsRev result with ⟨fileEq, windowEq⟩
  simpa only [fileEq, windowEq] using report

private def exampleFile : SourceFile := {
  id := { origin := .main, path := "pragma-context-frame.sol" }, content := ""
}

private def exampleSpan (startByte endByte : Nat) : SourceSpan := {
  source := exampleFile.id, startByte, endByte
}

private def hyphenName : Identifier := { span := exampleSpan 0 3, value := "a-b" }

private def hyphenEvent : ParseDiagnostic := {
  span := hyphenName.span, kind := .invalidIdentifierHyphen hyphenName.value
}

private def exampleInput (last : Symbol) (priorRev : List ParseDiagnostic) : State := {
  file := exampleFile
  tokens := #[{ span := hyphenName.span, value := .identifier hyphenName.value },
    { span := exampleSpan 3 4, value := .symbol .comma },
    { span := exampleSpan 4 5, value := .symbol last }]
  cursor := 0
  window := { endIndex := 3, endByte := 999 }
  diagnosticsRev := priorRev
}

/-- This fixture really is invalid: context preservation does not silently
depend on validated source bounds or earlier diagnostic provenance. -/
theorem exampleFrame_invalid (last : Symbol) (priorRev : List ParseDiagnostic) :
    ¬ (exampleInput last priorRev).ValidFor := by
  intro valid
  have bound := valid.endByte_le_source
  change 999 ≤ 0 at bound
  omega

/-- A trailing comma succeeds after emitting a hyphen diagnostic while
retaining even the deliberately invalid full file/window context. -/
theorem success_keeps_invalid_frame (priorRev : List ParseDiagnostic) :
    ∃ output, pragmaItems (exampleInput .semicolon priorRev) = .ok [hyphenName] output ∧
      output.file = exampleFile ∧ output.window = { endIndex := 3, endByte := 999 } ∧
      output.diagnostics = priorRev.reverse ++ [hyphenEvent] := by
  let output : State := { (exampleInput .semicolon priorRev).emit hyphenEvent with cursor := 2 }
  have result : pragmaItems (exampleInput .semicolon priorRev) = .ok [hyphenName] output := rfl
  rcases pragmaItems_success_context_eq result with ⟨fileEq, windowEq⟩
  refine ⟨output, result, fileEq, windowEq, ?_⟩
  simp only [output, State.diagnostics, State.emit, exampleInput, List.reverse_cons]

/-- A later missing item rejects after the same emission and retains the
original context, including the unvalidated end byte and complete source file. -/
theorem rejection_keeps_invalid_frame (priorRev : List ParseDiagnostic) :
    ∃ rejected, pragmaItems (exampleInput .plus priorRev) = .reject {
        span := exampleSpan 4 5
        found := some (.symbol .plus)
        expected := { head := .identifier, tail := [] }
        context := .pragmaDecl
      } rejected ∧
      rejected.file = exampleFile ∧ rejected.window = { endIndex := 3, endByte := 999 } ∧
      rejected.diagnostics = priorRev.reverse ++ [hyphenEvent] := by
  let rejected : State := { (exampleInput .plus priorRev).emit hyphenEvent with cursor := 2 }
  have result : pragmaItems (exampleInput .plus priorRev) = .reject {
      span := exampleSpan 4 5, found := some (.symbol .plus),
      expected := { head := .identifier, tail := [] }, context := .pragmaDecl
    } rejected := rfl
  rcases pragmaItems_reject_context_eq result with ⟨fileEq, windowEq⟩
  refine ⟨rejected, result, fileEq, windowEq, ?_⟩
  simp only [rejected, State.diagnostics, State.emit, exampleInput, List.reverse_cons]

end Solcore.Test.SyntaxParserPragmaItemsContextProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaItemsRejectionTraceProperties
/-! Consumers of exact item-rejection payloads and retained prefix events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaItemsRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PragmaInternals
open Solcore.Syntax.DeclarativeGrammar

example := @PragmaItemsTailRejectedPrefix.ordinary
example := @PragmaItemsTailRejects.exists_prefix
example := @PragmaItemsRejectedPrefix.ordinary
example := @PragmaItemsRejects.exists_prefix
example := @PragmaItemsTailRejectedPrefix.result_unique
example := @PragmaItemsRejectedPrefix.result_unique
example := @PragmaItemsTailTraceRejects.result_unique
example := @PragmaItemsTraceRejects.result_unique
example := @pragmaItemsTail_reject_trace_sound
example := @pragmaItems_reject_trace_sound

example (itemsRev : List Identifier) {input : State} {remainder : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaItemsTailTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace) :
    ∃ failure output,
      pragmaItemsTail (input.remainingCount + 1) itemsRev input = .reject failure output ∧
      output.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace :=
  (pragmaItemsTail_production_trace_reject_iff itemsRev).mp traced

example (itemsRev : List Identifier) {input output : State} {failure : Failure}
    {remainder : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (result : pragmaItemsTail (input.remainingCount + 1) itemsRev input = .reject failure output)
    (after : output.declarativeRemainder = remainder)
    (report : failure.toDiagnostic = diagnostic)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaItemsTailTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace :=
  (pragmaItemsTail_production_trace_reject_iff itemsRev).mpr
    ⟨failure, output, result, after, report, diagnostics⟩

example {input : State} {remainder : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaItemsTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace) :
    ∃ failure output, pragmaItems input = .reject failure output ∧
      output.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaItems_trace_reject_iff.mp traced

example {input output : State} {failure : Failure} {remainder : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (result : pragmaItems input = .reject failure output)
    (after : output.declarativeRemainder = remainder)
    (report : failure.toDiagnostic = diagnostic)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaItemsTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace :=
  pragmaItems_trace_reject_iff.mpr ⟨failure, output, result, after, report, diagnostics⟩

example (itemsRev : List Identifier) {input : State} {failure : Failure}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (traced : PragmaItemsTailTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace) :
    ∃ output,
      pragmaItemsTail (input.remainingCount + 1) itemsRev input = .reject failure output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  (pragmaItemsTail_production_trace_reject_failure_iff itemsRev).mp traced

example {input output : State} {failure : Failure} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (result : pragmaItems input = .reject failure output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaItemsTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace :=
  pragmaItems_trace_reject_failure_iff.mpr ⟨output, result, after, diagnostics⟩

example {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {span : SourceSpan} {found : Option TokenKind}
    (noSemicolon : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .semicolon))
    (noIdentifier : IdentifierRejects input rejected)
    (current : CurrentInputAt source endByte rejected span found) :
    PragmaItemsTraceRejects source endByte input rejected
      { span, kind := .unexpected found { head := .identifier, tail := [] } .pragmaDecl } [] :=
  ⟨[], .firstIdentifierRejected noSemicolon noIdentifier, .nil, .reported current⟩

example {source : SourceId} {endByte : Nat} {input afterFirst rejected : Remainder}
    (first second failureSpan : SourceSpan) (found : Option TokenKind)
    (noSemicolon : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .semicolon))
    (firstParsed : IdentifierParses input { span := first, value := "a-b" } afterFirst)
    (laterRejected : PragmaItemsTailRejectedPrefix afterFirst
      [{ span := second, value := "c--d" }] rejected)
    (current : CurrentInputAt source endByte rejected failureSpan found) :
    PragmaItemsTraceRejects source endByte input rejected
      { span := failureSpan,
        kind := .unexpected found { head := .identifier, tail := [] } .pragmaDecl }
      [{ span := first, kind := .invalidIdentifierHyphen "a-b" },
        { span := second, kind := .invalidIdentifierHyphen "c--d" }] :=
  ⟨_, .tailRejected noSemicolon firstParsed laterRejected,
    .cons (.hyphen (by change '-' ∈ "a-b".toList; decide))
      (.cons (.hyphen (by change '-' ∈ "c--d".toList; decide)) .nil),
    .reported current⟩

example {source : SourceId} {endByte : Nat} {input afterComma rejected : Remainder}
    {commaSpan : SourceSpan} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (comma : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
    (semicolon : PragmaItemsTokenPresentAt afterComma (.symbol .semicolon)) :
    ¬ PragmaItemsTailTraceRejects source endByte input rejected diagnostic trace := by
  rintro ⟨consumed, rejectedPrefix, _, _⟩
  exact pragmaItemsTailExactOutcomeSpec.successRejectDisjoint rejectedPrefix.ordinary
    ⟨[], afterComma, .trailing commaSpan ⟨commaSpan, comma.1⟩ comma semicolon⟩

example {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (semicolon : PragmaItemsTokenPresentAt input (.symbol .semicolon)) :
    ¬ PragmaItemsTraceRejects source endByte input rejected diagnostic trace := by
  rintro ⟨consumed, rejectedPrefix, _, _⟩
  exact pragmaItemsExactOutcomeSpec.successRejectDisjoint rejectedPrefix.ordinary
    ⟨[], input, .empty semicolon⟩

end Solcore.Test.SyntaxParserPragmaItemsRejectionTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaNameRejectionTraceProperties
/-! Independent missing-name witnesses, including window-end, wrong-token,
and unavailable-carrier branches, determine exact silent pragma rejection. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaNameRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals
open Solcore.Syntax.DeclarativeGrammar

example := @PragmaNameMissingAt.rejects
example := @peekKind_eq_pragma_of_exactTokenParses
example := @pragmaKeyword_eq_ok_of_exactTokenParses
example := @atTopItemStart_eq_true_of_pragmaToken
example := @plainTopItem_eq_pragma_of_exactTokenParses
example := @topItem_eq_pragma_of_exactTokenParses
example := @pragmaDecl_nameMissing_exact
example := @pragmaDecl_nameMissingAt_exact
example := @plainTopItem_pragmaNameMissing_exact
example := @topItem_pragmaNameMissing_exact
example := @parseItemsItem_pragmaNameMissing_exact
example := @parseItemsItem_pragmaNameMissingAt_exact

private def pragmaFile : SourceFile := {
  id := { origin := .main, path := "missing-pragma-name.sol" }
  content := "pragma"
}

private def markerSpan : SourceSpan := SourceSpan.fullFile pragmaFile

private def endSpan : SourceSpan := {
  source := pragmaFile.id, startByte := 6, endByte := 6
}

private def eofInput (priorRev : List ParseDiagnostic) : State := {
  file := pragmaFile
  tokens := #[{ span := markerSpan, value := .keyword .pragmaKw }]
  cursor := 0
  window := { endIndex := 1, endByte := 6 }
  diagnosticsRev := priorRev
}

private theorem eofMissing (priorRev : List ParseDiagnostic) :
    PragmaNameMissingAt pragmaFile.id 6 (eofInput priorRev).declarativeRemainder
      { (eofInput priorRev).declarativeRemainder with cursor := 1 } endSpan none := by
  apply PragmaNameMissingAt.missing (marker := markerSpan)
  · simp [ExactTokenParses, TokenAt, State.declarativeRemainder, eofInput]
  · simp [IdentifierAbsentAt, TokenAt, State.declarativeRemainder, eofInput]
  · exact .windowEnd (by simp [State.declarativeRemainder, eofInput])

/-- End-of-window uses the supplied end byte, retains only the marker step,
and does not commit its unexpected report into the raw diagnostic sequence. -/
theorem eof_exact (priorRev : List ParseDiagnostic) :
    parseItemsItem (eofInput priorRev) = .reject {
        span := endSpan, found := none,
        expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { eofInput priorRev with cursor := 1 } ∧
      ({ eofInput priorRev with cursor := 1 } : State).diagnostics = priorRev.reverse := by
  have result := parseItemsItem_pragmaNameMissingAt_exact (input := eofInput priorRev)
    (eofMissing priorRev)
  exact ⟨result.1, result.2.2⟩

private def wrongSpan : SourceSpan := {
  source := pragmaFile.id, startByte := 7, endByte := 8
}

private def wrongInput (priorRev : List ParseDiagnostic) : State := {
  eofInput priorRev with
  file := { pragmaFile with content := "pragma ;" }
  tokens := #[{ span := markerSpan, value := .keyword .pragmaKw },
    { span := wrongSpan, value := .symbol .semicolon }]
  window := { endIndex := 2, endByte := 8 }
}

private theorem wrongMissing (priorRev : List ParseDiagnostic) :
    PragmaNameMissingAt pragmaFile.id 8 (wrongInput priorRev).declarativeRemainder
      { (wrongInput priorRev).declarativeRemainder with cursor := 1 }
      wrongSpan (some (.symbol .semicolon)) := by
  apply PragmaNameMissingAt.missing (marker := markerSpan)
  · simp [ExactTokenParses, TokenAt, State.declarativeRemainder, wrongInput, eofInput]
  · simp [IdentifierAbsentAt, TokenAt, State.declarativeRemainder, wrongInput, eofInput]
  · apply CurrentInputAt.token (current := { span := wrongSpan, value := .symbol .semicolon })
    simp [TokenAt, State.declarativeRemainder, wrongInput, eofInput]

/-- A present non-identifier keeps its own exact span and found kind; it is
not replaced by the enclosing source's end-of-input report. -/
theorem semicolon_exact (priorRev : List ParseDiagnostic) :
    pragmaDecl (wrongInput priorRev) = .reject {
        span := wrongSpan, found := some (.symbol .semicolon),
        expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { wrongInput priorRev with cursor := 1 } ∧
      ({ wrongInput priorRev with cursor := 1 } : State).diagnostics = priorRev.reverse := by
  have result := pragmaDecl_nameMissingAt_exact (input := wrongInput priorRev)
    (wrongMissing priorRev)
  exact ⟨result.1, result.2.2⟩

private def unavailableInput (priorRev : List ParseDiagnostic) : State := {
  eofInput priorRev with window := { endIndex := 2, endByte := 6 }
}

private theorem unavailableMissing (priorRev : List ParseDiagnostic) :
    PragmaNameMissingAt pragmaFile.id 6 (unavailableInput priorRev).declarativeRemainder
      { (unavailableInput priorRev).declarativeRemainder with cursor := 1 }
      endSpan none := by
  apply PragmaNameMissingAt.missing (marker := markerSpan)
  · simp [ExactTokenParses, TokenAt, State.declarativeRemainder, unavailableInput, eofInput]
  · simp [IdentifierAbsentAt, TokenAt, State.declarativeRemainder, unavailableInput, eofInput]
  · apply CurrentInputAt.missingToken
    · simp [State.declarativeRemainder, unavailableInput, eofInput]
    · simp [State.declarativeRemainder, unavailableInput, eofInput]

/-- No validity assumption is silently introduced: an unavailable carrier
inside the supplied window has the exact same empty end-byte observation. -/
theorem unavailableCarrier_exact (priorRev : List ParseDiagnostic) :
    parseItemsItem (unavailableInput priorRev) = .reject {
        span := endSpan, found := none,
        expected := { head := .identifier, tail := [] }, context := .pragmaDecl
      } { unavailableInput priorRev with cursor := 1 } ∧
      ({ unavailableInput priorRev with cursor := 1 } : State).diagnostics = priorRev.reverse := by
  have result := parseItemsItem_pragmaNameMissingAt_exact (input := unavailableInput priorRev)
    (unavailableMissing priorRev)
  exact ⟨result.1, result.2.2⟩

end Solcore.Test.SyntaxParserPragmaNameRejectionTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaPrefixBoundaryTraceProperties
/-! Independent prefix order, cursor rewind, and single final-report consumers. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaPrefixBoundaryTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals
open Solcore.Syntax.DeclarativeGrammar

example := @PragmaPrefixBoundaryTraceParses.carrier_stop
example := @PragmaPrefixBoundaryTraceParses.length_lt_remaining
example := @PragmaPrefixBoundaryTraceParses.result_unique
example := @PragmaPrefixBoundaryTraceParses.cascadeFilters
example := @pragmaDecl_success_context_eq
example := @pragmaDecl_reject_context_eq
example := @parseItems_pragmaPrefixBoundary_trace_of_remainingCount_lt

example (fuel : Nat) (itemsRev : List TopItem) {input : State}
    {declarations : List PragmaDecl} {stopped : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder declarations stopped diagnostic trace)
    (adequate : declarations.length < fuel) :
    ∃ output, parseItems fuel itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = stopped ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) :=
  parseItems_pragmaPrefixBoundary_trace_of_length_lt fuel itemsRev parsed adequate

example (itemsRev : List TopItem) {input : State}
    {declarations : List PragmaDecl} {stopped : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder declarations stopped diagnostic trace) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = stopped ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) :=
  parseItems_production_pragmaPrefixBoundary_trace itemsRev parsed

example (comments : List Comment) {input : State}
    {declarations : List PragmaDecl} {stopped : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder declarations stopped diagnostic trace) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := (declarations.map wrapPragma).map (attachTopItemComments input.file comments)
        comments
      } output ∧
      output.declarativeRemainder = stopped ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) :=
  sourceFile_pragmaPrefixBoundary_trace comments parsed

example (prior : TopItem) {input : State}
    {first second : PragmaDecl} {afterFirst afterSecond afterKeyword rejected : Remainder}
    {firstTrace secondTrace rejectedTrace : List ParseDiagnostic}
    {marker : SourceSpan} {diagnostic : ParseDiagnostic}
    (firstParsed : PragmaDeclTraceParses input.declarativeRemainder first afterFirst firstTrace)
    (secondParsed : PragmaDeclTraceParses afterFirst second afterSecond secondTrace)
    (recognized : ExactTokenParses (.keyword .pragmaKw) afterSecond marker afterKeyword)
    (lastRejected : PragmaDeclTraceRejects input.file.id input.window.endByte
      afterSecond rejected diagnostic rejectedTrace) :
    ∃ output, parseItems (input.remainingCount + 1) [prior] input =
        .ok [prior, wrapPragma first, wrapPragma second] output ∧
      output.declarativeRemainder = afterSecond ∧
      output.diagnostics = input.diagnostics ++
        (firstTrace ++ secondTrace ++ rejectedTrace ++ [diagnostic]) := by
  have parsed := PragmaPrefixBoundaryTraceParses.cons firstParsed
    (.cons secondParsed (.stopped marker recognized lastRejected))
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.map_cons, List.map_nil, List.singleton_append, List.append_assoc] using
      parseItems_production_pragmaPrefixBoundary_trace [prior] parsed

example (itemsRev : List TopItem) {input : State}
    {afterKeyword rejected : Remainder} {marker : SourceSpan}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (recognized : ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker afterKeyword)
    (lastRejected : PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder rejected diagnostic trace) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok itemsRev.reverse output ∧
      output.declarativeRemainder = input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) := by
  simpa only [List.map_nil, List.append_nil] using
    parseItems_production_pragmaPrefixBoundary_trace itemsRev
      (.stopped marker recognized lastRejected)

example {source : SourceId} {endByte : Nat} {input stopped : Remainder}
    {declarations : List PragmaDecl} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses source endByte input
      declarations stopped diagnostic trace) :
    input.cursor ≤ stopped.cursor ∧ stopped.cursor < input.endIndex :=
  parsed.carrier_stop.2.2

example {input afterKeyword : Remainder} {marker : SourceSpan}
    (recognized : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .pragmaKw)) :
    False :=
  absent ⟨marker, recognized.1⟩

end Solcore.Test.SyntaxParserPragmaPrefixBoundaryTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaProperties
/-! External consumers for provisional pragma provenance contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @PragmaDecl.ValidFor
example := @pragmaDecl_validFor
example := @pragmaDecl_preservesTokenWindow
example := @pragmaDecl_preservesTokensOnSuccess
example := @pragmaDecl_startsAtCurrentTokenOnSuccess
example := @pragmaDecl_cursor_lt_onSuccess
example := @pragmaDecl_cursorMonotoneOnSuccess

example :
    pragmaDecl.ValidFor PragmaDecl.ValidFor ∧
      Parser.PreservesTokenWindow pragmaDecl ∧
      Parser.PreservesTokensOnSuccess pragmaDecl ∧
      Parser.CursorMonotoneOnSuccess pragmaDecl ∧
      Parser.StartsAtCurrentTokenOnSuccess pragmaDecl (·.span) :=
  ⟨pragmaDecl_validFor, pragmaDecl_preservesTokenWindow,
    pragmaDecl_preservesTokensOnSuccess,
    pragmaDecl_cursorMonotoneOnSuccess,
    pragmaDecl_startsAtCurrentTokenOnSuccess⟩

example (file : SourceFile) (declaration : PragmaDecl)
    (valid : PragmaDecl.ValidFor file declaration) :
    declaration.span.ValidFor file ∧
      declaration.value.name.span.ValidFor file :=
  ⟨valid.1, valid.2.1⟩

example (file : SourceFile) (declaration : PragmaDecl)
    (valid : PragmaDecl.ValidFor file declaration)
    (item : Identifier) (member : item ∈ declaration.value.items) :
    item.span.ValidFor file :=
  valid.2.2 item member

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaRejectionCascadeProperties
/-! Independent consumers distinguish the raw prefix from a committed failure.
Whole-list equalities preserve repeated reports, their order, and all payloads. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaRejectionCascadeProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat} {input rejected : Remainder}
  {diagnostic : ParseDiagnostic} {trace kept : List ParseDiagnostic}
  (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace)
  (text : String) (lexical : List SourceSpan)

example (filtered : ParseDiagnosticCascadeFilters text lexical
    (trace ++ [diagnostic]) kept) :
    (¬ ParseDiagnosticCascadeSuppresses text lexical diagnostic ∧
      kept = trace ++ [diagnostic]) ∨
      (ParseDiagnosticCascadeSuppresses text lexical diagnostic ∧ kept = trace) :=
  (traced.committedCascadeFilters_iff text lexical).mp filtered

example (choice :
    (¬ ParseDiagnosticCascadeSuppresses text lexical diagnostic ∧
      kept = trace ++ [diagnostic]) ∨
      (ParseDiagnosticCascadeSuppresses text lexical diagnostic ∧ kept = trace)) :
    ParseDiagnosticCascadeFilters text lexical (trace ++ [diagnostic]) kept :=
  (traced.committedCascadeFilters_iff text lexical).mpr choice

/-- Dropping the committed report preserves all three earlier occurrences,
including an identical repeated event after a different event. -/
theorem repeated_prefix_survives_suppression
    {first second : ParseDiagnostic}
    (prefixTraced : PragmaDeclTraceRejects source endByte input rejected diagnostic
      [first, second, first])
    (suppressed : ParseDiagnosticCascadeSuppresses text lexical diagnostic) :
    ParseDiagnosticCascadeFilters text lexical
      [first, second, first, diagnostic] [first, second, first] :=
  prefixTraced.committedCascadeFilters_of_suppressed text lexical suppressed

/-- Keeping the committed report leaves it last; the protected prefix's order
and duplicates remain unchanged instead of becoming a set of spans. -/
theorem repeated_prefix_precedes_retained_failure
    {first second : ParseDiagnostic}
    (prefixTraced : PragmaDeclTraceRejects source endByte input rejected diagnostic
      [first, second, first])
    (retained : ¬ ParseDiagnosticCascadeSuppresses text lexical diagnostic) :
    ParseDiagnosticCascadeFilters text lexical
      [first, second, first, diagnostic] [first, second, first, diagnostic] :=
  prefixTraced.committedCascadeFilters_of_retained text lexical retained

include traced in
/-- Filtering cannot introduce a third possibility or silently remove a
protected occurrence from the rejecting declaration's earlier trace. -/
theorem committed_output_has_only_two_shapes
    (filtered : ParseDiagnosticCascadeFilters text lexical (trace ++ [diagnostic]) kept) :
    kept = trace ++ [diagnostic] ∨ kept = trace := by
  rcases (traced.committedCascadeFilters_iff text lexical).mp filtered with
    ⟨_, same⟩ | ⟨_, same⟩
  · exact Or.inl same
  · exact Or.inr same

/-- Before the caller commits its failure, only the raw prefix is filtered;
no failure event is invented by the rejecting grammar or its protection law. -/
example : ParseDiagnosticCascadeFilters text lexical trace trace :=
  traced.cascadeFilters text lexical

end Solcore.Test.SyntaxParserPragmaRejectionCascadeProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaRejectionTraceGrammarProperties
/-! Independent first-failure reports and protected prior pragma events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaRejectionTraceGrammarProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

example (source : SourceId) (endByte : Nat) {input rejected : Remainder}
    (ordinary : PragmaDeclRejects input rejected) :
    ∃ diagnostic trace, PragmaDeclTraceRejects source endByte input rejected diagnostic trace :=
  ordinary.exists_trace source endByte

example {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace) :
    PragmaDeclRejects input rejected := traced.ordinary

example {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {leftDiagnostic rightDiagnostic : ParseDiagnostic} {leftTrace rightTrace : List ParseDiagnostic}
    (left : PragmaDeclTraceRejects source endByte input afterLeft leftDiagnostic leftTrace)
    (right : PragmaDeclTraceRejects source endByte input afterRight rightDiagnostic rightTrace) :
    afterLeft = afterRight ∧ leftDiagnostic = rightDiagnostic ∧ leftTrace = rightTrace :=
  left.result_unique right

example {source : SourceId} {endByte : Nat} {input : Remainder} {diagnostic : ParseDiagnostic}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .pragmaKw))
    (reported : RejectAtReports source endByte { head := .keyword .pragmaKw, tail := [] }
      .pragmaDecl input diagnostic) :
    PragmaDeclTraceRejects source endByte input input diagnostic [] :=
  .keywordMissing absent reported

example {source : SourceId} {endByte : Nat} {input afterKeyword : Remainder}
    {marker : SourceSpan} {diagnostic : ParseDiagnostic}
    (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
    (absent : IdentifierAbsentAt afterKeyword)
    (reported : RejectAtReports source endByte { head := .identifier, tail := [] }
      .pragmaDecl afterKeyword diagnostic) :
    PragmaDeclTraceRejects source endByte input afterKeyword diagnostic [] :=
  .nameRejected marker keywordParsed (.absent absent) reported

example {source : SourceId} {endByte : Nat} {input afterKeyword afterName rejected : Remainder}
    {marker : SourceSpan} {name : Identifier} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
    (nameParsed : IdentifierParses afterKeyword name afterName)
    (itemsRejected : PragmaItemsTraceRejects source endByte afterName rejected diagnostic trace) :
    PragmaDeclTraceRejects source endByte input rejected diagnostic trace :=
  .itemsRejected marker keywordParsed nameParsed itemsRejected

example {source : SourceId} {endByte : Nat} {input afterKeyword afterName afterItems : Remainder}
    {marker : SourceSpan} {name : Identifier} {items : List Identifier}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
    (nameParsed : IdentifierParses afterKeyword name afterName)
    (itemsParsed : PragmaItemsTraceParses afterName items afterItems trace)
    (absent : TokenKindAbsentAt afterItems.tokens afterItems.endIndex afterItems.cursor (.symbol .semicolon))
    (reported : RejectAtReports source endByte { head := .symbol .semicolon, tail := [] }
      .pragmaDecl afterItems diagnostic) :
    PragmaDeclTraceRejects source endByte input afterItems diagnostic trace :=
  .semicolonMissing marker keywordParsed nameParsed itemsParsed absent reported

/-- A rejected declaration's already emitted names stay protected; its distinct
uncommitted report is deliberately not inserted into this raw filtering claim. -/
example {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  traced.cascadeFilters text lexical

end Solcore.Test.SyntaxParserPragmaRejectionTraceGrammarProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaSoundnessProperties
/-! External consumers for strict and exact ordinary pragma outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TokenAt
example := @PragmaItemsTailParses
example := @PragmaItemsParses
example := @PragmaDeclParses
example := @PragmaItemsTokenPresentAt
example := @PragmaItemsTailOrdinaryParses
example := @PragmaItemsTailRejects
example := @pragmaItemsTailDeterministicOutcomeSpec
example := @PragmaItemsOrdinaryParses
example := @PragmaItemsRejects
example := @pragmaItemsDeterministicOutcomeSpec
example := @PragmaDeclOrdinaryParses
example := @PragmaDeclRejects
example := @pragmaDeclDeterministicOutcomeSpec
example := @State.declarativeRemainder
example := @rawIdentifier_success_ordinaryOutcome_sound
example := @rawIdentifier_reject_ordinaryOutcome_sound
example := @rawIdentifier_ordinaryOutcome_sound
example := @rawIdentifier_ordinaryOutcomeSpec
example := @PragmaInternals.pragmaItemsTail_production_ordinaryOutcome_sound
example := @PragmaInternals.pragmaItems_ordinaryOutcome_sound
example := @PragmaInternals.pragmaItemsTail_ordinaryOutcomeSpec
example := @PragmaInternals.pragmaItems_ordinaryOutcomeSpec
example := @pragmaDecl_success_ordinaryOutcome_sound
example := @pragmaDecl_reject_ordinaryOutcome_sound
example := @pragmaDecl_ordinaryOutcome_sound
example := @pragmaDecl_ordinaryOutcomeSpec
example := @pragmaDecl_success_sound
example := @pragmaDecl_success_sound_and_validFor

example {input next : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration next) :
    PragmaDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  pragmaDecl_success_sound result

example {input next : State} {declaration : PragmaDecl}
    (inputValid : input.ValidFor)
    (result : pragmaDecl input = .ok declaration next) :
    PragmaDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  pragmaDecl_success_sound_and_validFor inputValid result

example {input next : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration next) :
    PragmaDeclOrdinaryParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  pragmaDecl_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : pragmaDecl input = .reject failure rejected) :
    PragmaDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  pragmaDecl_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserPragmaSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaTotalityProperties
/-! External consumers for pragma-parser totality laws. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PragmaInternals

example := @pragmaItemsTail_ordinary_of_remainingCount_lt
example := @pragmaItemsTail_production_ordinary
example := @pragmaItemsTail_production_ne_invariant
example := @pragmaItems_ordinary
example := @pragmaItems_ne_invariant
example := @pragmaDecl_ordinary
example := @pragmaDecl_ne_invariant

example (state : State) (error : ParserInvariantError) :
    pragmaDecl state ≠ .invariant error :=
  pragmaDecl_ne_invariant state error

end Solcore.Test.SyntaxParserPragmaTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaTraceProperties
/-! Consumers of ordered pragma success traces, including silent raw names. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PragmaInternals
open Solcore.Syntax.DeclarativeGrammar

example := @identifierListDiagnosticTrace_total
example := @IdentifierListDiagnosticTrace.trace_unique
example := @IdentifierListDiagnosticTrace.append
example := @PragmaItemsTailTraceParses.result_unique
example := @PragmaItemsTraceParses.result_unique
example := @PragmaDeclTraceParses.result_unique
example := @pragmaItemsTail_success_diagnosticTrace
example := @pragmaItemsTail_production_success_trace_sound
example := @pragmaItems_success_diagnosticTrace
example := @pragmaItems_success_diagnostics_eq_of_trace
example := @pragmaItems_success_trace_sound
example := @pragmaItemsTail_production_success_diagnostics_eq_of_trace
example := @pragmaDecl_success_diagnosticTrace
example := @pragmaDecl_success_diagnostics_eq_of_trace

example (first middle last : SourceSpan) :
    IdentifierListDiagnosticTrace
      [{ span := first, value := "a-b" }, { span := middle, value := "clean" },
        { span := last, value := "c--d" }]
      [{ span := first, kind := .invalidIdentifierHyphen "a-b" },
        { span := last, kind := .invalidIdentifierHyphen "c--d" }] :=
  .cons (.hyphen (by change '-' ∈ "a-b".toList; decide))
    (.cons (.clean (by change ¬ '-' ∈ "clean".toList; decide))
      (.cons (.hyphen (by change '-' ∈ "c--d".toList; decide)) .nil))

example (itemsRev : List Identifier) {input : State} {suffix : List Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (parsed : PragmaItemsTailTraceParses input.declarativeRemainder suffix remainder trace) :
    ∃ output, pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .ok (itemsRev.reverse ++ suffix) output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  (pragmaItemsTail_production_trace_success_iff itemsRev).mp parsed

example (itemsRev : List Identifier) {input output : State} {suffix : List Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (result : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .ok (itemsRev.reverse ++ suffix) output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaItemsTailTraceParses input.declarativeRemainder suffix remainder trace :=
  (pragmaItemsTail_production_trace_success_iff itemsRev).mpr
    ⟨output, result, after, diagnostics⟩

example {input : State} {items : List Identifier} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (parsed : PragmaItemsTraceParses input.declarativeRemainder items remainder trace) :
    ∃ output, pragmaItems input = .ok items output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaItems_trace_success_iff.mp parsed

example {input output : State} {items : List Identifier} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (result : pragmaItems input = .ok items output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaItemsTraceParses input.declarativeRemainder items remainder trace :=
  pragmaItems_trace_success_iff.mpr ⟨output, result, after, diagnostics⟩

example {input : State} {declaration : PragmaDecl} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (parsed : PragmaDeclTraceParses input.declarativeRemainder declaration remainder trace) :
    ∃ output, pragmaDecl input = .ok declaration output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaDecl_trace_success_iff.mp parsed

example {input output : State} {declaration : PragmaDecl} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .ok declaration output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaDeclTraceParses input.declarativeRemainder declaration remainder trace :=
  pragmaDecl_trace_success_iff.mpr ⟨output, result, after, diagnostics⟩

example {input : State} {declaration : PragmaDecl} {remainder : Remainder}
    (parsed : PragmaDeclOrdinaryParses input.declarativeRemainder declaration remainder)
    (noItems : declaration.value.items = []) :
    ∃ output, pragmaDecl input = .ok declaration output ∧
      output.declarativeRemainder = remainder ∧ output.diagnostics = input.diagnostics := by
  have diagnostics : IdentifierListDiagnosticTrace declaration.value.items [] := by
    rw [noItems]
    exact .nil
  simpa only [List.append_nil] using pragmaDecl_trace_success_iff.mp ⟨parsed, diagnostics⟩

example {input output : State} {actual expected : PragmaDecl} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .ok actual output)
    (parsed : PragmaDeclTraceParses input.declarativeRemainder expected remainder trace) :
    actual = expected ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaDecl_success_trace_sound result with ⟨actualTrace, actualParsed, actualEq⟩
  rcases actualParsed.result_unique parsed with ⟨rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, actualEq⟩

end Solcore.Test.SyntaxParserPragmaTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
/-! Ground pragma-name failures determine complete public outputs through
independent grammar. Only lexical fixtures are reduced by the kernel. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals
open Solcore.Syntax.DeclarativeGrammar

def exampleSource : SourceId := { origin := .main, path := "pragma-name-examples.sol" }

def exampleFile (content : String) : SourceFile := { id := exampleSource, content }

def byteSpan (startByte endByte : Nat) : SourceSpan := {
  source := exampleSource, startByte, endByte
}

def pragmaToken (offset : Nat) : Token := {
  span := byteSpan offset (offset + 6), value := .keyword .pragmaKw
}

def semicolonToken (offset : Nat) : Token := {
  span := byteSpan offset (offset + 1), value := .symbol .semicolon
}

def pragmaTokens (offset : Nat) (rest : List Token) : List Token :=
  pragmaToken offset :: semicolonToken (offset + 7) :: rest

def lexicalCarrier (tokens : List Token) (diagnostics : List LexicalDiagnostic) : LexedFile := {
  source := exampleSource, tokens, comments := [], diagnostics
}

def expectedOutput (content : String) (tokens : List Token)
    (lexical : List LexicalDiagnostic) (parsed : List ParseDiagnostic) : ParseOutput := {
  parsed := {
    source := exampleSource
    span := SourceSpan.fullFile (exampleFile content)
    items := []
    comments := []
  }
  tokens
  lexicalDiagnostics := lexical
  parseDiagnostics := parsed
}

/-- An actual lexical fixture supplies exactly the carrier used by the grammar. -/
theorem lex_ok_of_toOption {file : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex file).toOption = some lexed) : Lexer.lex file = .ok lexed := by
  cases result : Lexer.lex file with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

/-- The semicolon is an independently observed non-name after the marker. -/
theorem pragmaSemicolonMissing (content : String) (offset : Nat) (rest : List Token) :
    PragmaNameMissingAt (exampleFile content).id (exampleFile content).content.utf8ByteSize
      (sourceFileRootRemainder (pragmaTokens offset rest))
      { sourceFileRootRemainder (pragmaTokens offset rest) with cursor := 1 }
      (byteSpan (offset + 7) (offset + 7 + 1)) (some (.symbol .semicolon)) := by
  apply PragmaNameMissingAt.missing (marker := (pragmaToken offset).span)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, pragmaTokens, pragmaToken]
  · simp [IdentifierAbsentAt, TokenAt, sourceFileRootRemainder, pragmaTokens, semicolonToken]
  · apply CurrentInputAt.token (current := semicolonToken (offset + 7))
    simp [TokenAt, sourceFileRootRemainder, pragmaTokens]

/-- The marker preserves nesting and the semicolon resets it before the tail. -/
theorem pragmaTokensClear (offset : Nat) (rest : List Token) (clears : NestingClears rest) :
    NestingClears (pragmaTokens offset rest) :=
  .preserve rfl (.reset rfl clears)

/-- Grammar, canonical lexical validation, and independent filtering compute
both public entry points, including all lexical and diagnostic fields. -/
theorem completeOutputs {content : String} {tokens : List Token}
    {lexical : List LexicalDiagnostic} {after : Remainder}
    {span : SourceSpan} {found : Option TokenKind} {kept : List SourceSpan}
    (lexing : Lexer.lex (exampleFile content) = .ok (lexicalCarrier tokens lexical))
    (clears : NestingClears tokens)
    (missing : PragmaNameMissingAt (exampleFile content).id
      (exampleFile content).content.utf8ByteSize (sourceFileRootRemainder tokens)
      after span found)
    (filtered : LexicalCascadeFilters content (lexical.map (·.span)) [span] kept) :
    parseLexed (exampleFile content) (lexicalCarrier tokens lexical) =
        .ok (expectedOutput content tokens lexical
          (unexpectedDiagnostics found { head := .identifier, tail := [] } .pragmaDecl kept)) ∧
      parse (exampleFile content) = .ok (expectedOutput content tokens lexical
        (unexpectedDiagnostics found { head := .identifier, tail := [] } .pragmaDecl kept)) := by
  have accepted : LexedFileValidationAccepts (exampleFile content)
      (lexicalCarrier tokens lexical) :=
    (lexedFileValidationAccepts_iff_validFor _ _).mpr (Lexer.lex_ok_validFor _ _ lexing)
  exact ⟨parseLexed_eq_ok_of_pragmaNameMissing accepted clears missing filtered,
    parse_eq_ok_of_pragmaNameMissing lexing clears missing filtered⟩

set_option maxRecDepth 4096 in
private theorem eofLexes :
    Lexer.lex (exampleFile "pragma") = .ok (lexicalCarrier [pragmaToken 0] []) := by
  apply lex_ok_of_toOption
  decide +kernel

private theorem eofMissing :
    PragmaNameMissingAt exampleSource 6 (sourceFileRootRemainder [pragmaToken 0])
      { sourceFileRootRemainder [pragmaToken 0] with cursor := 1 } (byteSpan 6 6) none := by
  apply PragmaNameMissingAt.missing (marker := byteSpan 0 6)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, pragmaToken]
  · simp [IdentifierAbsentAt, TokenAt, sourceFileRootRemainder]
  · exact .windowEnd (by decide)

/-- EOF reports no found token at the exact zero-width byte-6 endpoint. -/
theorem eof_parse_eq_output :
    parse (exampleFile "pragma") = .ok (expectedOutput "pragma" [pragmaToken 0] []
      [{
        span := byteSpan 6 6
        kind := .unexpected none { head := .identifier, tail := [] } .pragmaDecl
      }]) :=
  (completeOutputs eofLexes (.preserve rfl .done) eofMissing
    (lexicalCascadeFilters_nil_lexical "pragma" [byteSpan 6 6])).2

set_option maxRecDepth 4096 in
private theorem semicolonLexes :
    Lexer.lex (exampleFile "pragma ;") = .ok (lexicalCarrier (pragmaTokens 0 []) []) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- The failure records the actual semicolon at bytes 7..8, not the marker. -/
theorem semicolon_parse_eq_output :
    parse (exampleFile "pragma ;") = .ok (expectedOutput "pragma ;" (pragmaTokens 0 []) []
      [{
        span := byteSpan 7 8
        kind := .unexpected (some (.symbol .semicolon))
          { head := .identifier, tail := [] } .pragmaDecl
      }]) :=
  (completeOutputs semicolonLexes (pragmaTokensClear 0 [] .done)
    (pragmaSemicolonMissing "pragma ;" 0 [])
    (lexicalCascadeFilters_nil_lexical "pragma ;" [byteSpan 7 8])).2

private def laterTokens : List Token := [
  { span := byteSpan 9 13, value := .keyword .typeKw },
  { span := byteSpan 14 19, value := .identifier "Later" },
  { span := byteSpan 20 21, value := .symbol .equal },
  { span := byteSpan 22 26, value := .identifier "word" },
  semicolonToken 26
]

set_option maxRecDepth 4096 in
private theorem laterLexes :
    Lexer.lex (exampleFile "pragma ; type Later = word;") =
      .ok (lexicalCarrier (pragmaTokens 0 laterTokens) []) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- Even a valid following declaration is retained only as tokens: recognized
start rejection commits one report and returns an empty item list. -/
theorem laterTokens_parse_eq_output :
    parse (exampleFile "pragma ; type Later = word;") =
      .ok (expectedOutput "pragma ; type Later = word;" (pragmaTokens 0 laterTokens) []
        [{
          span := byteSpan 7 8
          kind := .unexpected (some (.symbol .semicolon))
            { head := .identifier, tail := [] } .pragmaDecl
        }]) :=
  (completeOutputs laterLexes
    (pragmaTokensClear 0 laterTokens
      (.preserve rfl (.preserve rfl (.preserve rfl (.preserve rfl (.reset rfl .done))))))
    (pragmaSemicolonMissing "pragma ; type Later = word;" 0 laterTokens)
    (lexicalCascadeFilters_nil_lexical "pragma ; type Later = word;" [byteSpan 7 8])).2

/-- The internal root remainder is rewound unchanged, proving that the later
tokens really remain unconsumed; this endpoint is hidden by public ParseOutput. -/
theorem laterTokens_sourceFile_remainsAtRoot :
    ∃ output, sourceFile [] (State.initial (exampleFile "pragma ; type Later = word;")
        (lexicalCarrier (pragmaTokens 0 laterTokens) [])) = .ok {
          source := exampleSource
          span := SourceSpan.fullFile (exampleFile "pragma ; type Later = word;")
          items := []
          comments := []
        } output ∧
      output.declarativeRemainder = sourceFileRootRemainder (pragmaTokens 0 laterTokens) := by
  have missing := pragmaSemicolonMissing "pragma ; type Later = word;" 0 laterTokens
  cases missing with
  | missing keywordParsed absent current =>
      rcases parseItemsItem_pragmaNameMissing_exact
          (input := State.initial (exampleFile "pragma ; type Later = word;")
            (lexicalCarrier (pragmaTokens 0 laterTokens) []))
          keywordParsed absent current with ⟨rejected, _after, _prior⟩
      rcases sourceFile_boundaryStop_trace_exact [] keywordParsed.1.1
          (atTopItemStart_eq_true_of_pragmaToken
            (input := State.initial (exampleFile "pragma ; type Later = word;")
              (lexicalCarrier (pragmaTokens 0 laterTokens) [])) keywordParsed) rejected with
        ⟨output, result, remainderEq, _trace⟩
      exact ⟨output, result, remainderEq⟩

end Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPublicPragmaNameCascadeExamples
/-! Real lexical errors suppress a same-line pragma expectation report but
retain one after LF. Complete outputs share the same lexical byte ranges. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaNameCascadeExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples

private def invalidToken : LexicalDiagnostic := {
  span := byteSpan 0 2
  kind := .invalidToken
}

set_option maxRecDepth 4096 in
private theorem sameLineLexes :
    Lexer.lex (exampleFile "§ pragma ;") =
      .ok (lexicalCarrier (pragmaTokens 3 []) [invalidToken]) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 4096 in
private theorem nextLineLexes :
    Lexer.lex (exampleFile "§\npragma ;") =
      .ok (lexicalCarrier (pragmaTokens 3 []) [invalidToken]) := by
  apply lex_ok_of_toOption
  decide +kernel

private theorem sameLineSuppressed :
    LexicalCascadeSuppresses "§ pragma ;" [invalidToken.span] (byteSpan 10 11) := by
  refine ⟨invalidToken.span, by simp, rfl, Or.inl ?_⟩
  decide

/-- The invalid character remains in lexicalDiagnostics at bytes 0..2;
the same-line unexpected-semicolon report at 10..11 is removed completely. -/
theorem sameLine_parse_eq_output :
    parse (exampleFile "§ pragma ;") =
      .ok (expectedOutput "§ pragma ;" (pragmaTokens 3 []) [invalidToken] []) :=
  (completeOutputs sameLineLexes (pragmaTokensClear 3 [] .done)
    (pragmaSemicolonMissing "§ pragma ;" 3 []) (.drop sameLineSuppressed .nil)).2

private theorem nextLineRetained :
    ¬ LexicalCascadeSuppresses "§\npragma ;" [invalidToken.span] (byteSpan 10 11) := by
  rintro ⟨span, member, _sourceEq, suppressed⟩
  have spanEq : span = invalidToken.span := by simpa using member
  subst span
  rcases suppressed with sameLine | overlap | covered | adjacent
  · exact (by decide : cascadeLineIndex "§\npragma ;" invalidToken.span.startByte ≠
      cascadeLineIndex "§\npragma ;" (byteSpan 10 11).startByte) sameLine
  · exact (by decide : ¬ (byteSpan 10 11).startByte < invalidToken.span.endByte) overlap.2
  · exact (by decide : ¬ (byteSpan 10 11).startByte ≤ invalidToken.span.endByte) covered.2
  · rcases adjacent with ⟨_ordered, gap, sliced, whitespace⟩
    have exactGap : Trivia.utf8Slice? "§\npragma ;" invalidToken.span.endByte
        (byteSpan 10 11).startByte = some "\npragma " := by decide
    have gapEq : gap = "\npragma " := Option.some.inj (sliced.symm.trans exactGap)
    subst gap
    contradiction

/-- On the next LF line both diagnostics remain, with the actual found token,
identifier expectation, pragma context, and exact two independent byte spans. -/
theorem nextLine_parse_eq_output :
    parse (exampleFile "§\npragma ;") =
      .ok (expectedOutput "§\npragma ;" (pragmaTokens 3 []) [invalidToken]
        [{
          span := byteSpan 10 11
          kind := .unexpected (some (.symbol .semicolon))
            { head := .identifier, tail := [] } .pragmaDecl
        }]) :=
  (completeOutputs nextLineLexes (pragmaTokensClear 3 [] .done)
    (pragmaSemicolonMissing "§\npragma ;" 3 []) (.keep nextLineRetained .nil)).2

/-- Already-tokenized parsing uses validation from the same canonical lexical
fixture and returns the identical full suppressed output. -/
theorem sameLine_parseLexed_eq_output :
    parseLexed (exampleFile "§ pragma ;")
        (lexicalCarrier (pragmaTokens 3 []) [invalidToken]) =
      .ok (expectedOutput "§ pragma ;" (pragmaTokens 3 []) [invalidToken] []) :=
  (completeOutputs sameLineLexes (pragmaTokensClear 3 [] .done)
    (pragmaSemicolonMissing "§ pragma ;" 3 []) (.drop sameLineSuppressed .nil)).1

end Solcore.Test.SyntaxParserPublicPragmaNameCascadeExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPublicPragmaNameRejectionOutputProperties
/-! Consumers of complete public outputs from an independent missing pragma
name, preserving source context and exact expectation-report metadata. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaNameRejectionOutputProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {file : SourceFile} {lexed : LexedFile} {after : Remainder}
  {span : SourceSpan} {found : Option TokenKind} {kept : List SourceSpan}
  (accepted : LexedFileValidationAccepts file lexed)
  (clears : NestingClears lexed.tokens)
  (missing : PragmaNameMissingAt file.id file.content.utf8ByteSize
    (sourceFileRootRemainder lexed.tokens) after span found)

example (filtered : LexicalCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) [span] kept) :
    parseLexed file lexed = .ok {
      parsed := {
        source := file.id
        span := SourceSpan.fullFile file
        items := []
        comments := lexed.comments
      }
      tokens := lexed.tokens
      lexicalDiagnostics := lexed.diagnostics
      parseDiagnostics := unexpectedDiagnostics found
        { head := .identifier, tail := [] } .pragmaDecl kept
    } :=
  parseLexed_eq_ok_of_pragmaNameMissing accepted clears missing filtered

example (result : parseLexed file lexed =
    .ok (pragmaNameMissingParseOutput file lexed found kept)) :
    LexedFileValidationAccepts file lexed ∧
      LexicalCascadeFilters file.content (lexed.diagnostics.map (·.span)) [span] kept :=
  (parseLexed_eq_ok_pragmaNameMissing_iff clears missing).mp result

example (suppressed : LexicalCascadeSuppresses file.content
    (lexed.diagnostics.map (·.span)) span) :
    parseLexed file lexed = .ok (pragmaNameMissingParseOutput file lexed found []) :=
  parseLexed_eq_ok_of_pragmaNameMissing accepted clears missing (.drop suppressed .nil)

example (retained : ¬ LexicalCascadeSuppresses file.content
    (lexed.diagnostics.map (·.span)) span) :
    parseLexed file lexed = .ok (pragmaNameMissingParseOutput file lexed found [span]) :=
  parseLexed_eq_ok_of_pragmaNameMissing accepted clears missing (.keep retained .nil)

example (lexing : Lexer.lex file = .ok lexed)
    (filtered : LexicalCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) [span] kept) :
    parse file = .ok (pragmaNameMissingParseOutput file lexed found kept) :=
  parse_eq_ok_of_pragmaNameMissing lexing clears missing filtered

example (lexing : Lexer.lex file = .ok lexed)
    (result : parse file = .ok (pragmaNameMissingParseOutput file lexed found kept)) :
    LexicalCascadeFilters file.content (lexed.diagnostics.map (·.span)) [span] kept :=
  (parse_eq_ok_pragmaNameMissing_iff lexing clears missing).mp result

end Solcore.Test.SyntaxParserPublicPragmaNameRejectionOutputProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPublicPragmaPrefixBoundaryOutputProperties
/-! Public successful-prefix boundary consumers. Complete output construction
uses independent syntax and filtering, never an executable declaration reply. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaPrefixBoundaryOutputProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
  {stopped : Remainder} {diagnostic : ParseDiagnostic} {trace kept : List ParseDiagnostic}
  (accepted : LexedFileValidationAccepts file lexed)
  (clears : NestingClears lexed.tokens)
  (parsed : PragmaPrefixBoundaryTraceParses file.id file.content.utf8ByteSize
    (sourceFileRootRemainder lexed.tokens) declarations stopped diagnostic trace)
  (filtered : ParseDiagnosticCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept)

example : parseLexed file lexed = .ok {
    parsed := {
      source := file.id
      span := SourceSpan.fullFile file
      items := (declarations.map FileInternals.wrapPragma).map
        (Trivia.attachTopItemComments file lexed.comments)
      comments := lexed.comments
    }
    tokens := lexed.tokens
    lexicalDiagnostics := lexed.diagnostics
    parseDiagnostics := kept
  } :=
  parseLexed_eq_ok_of_pragmaPrefixBoundary accepted clears parsed filtered

example (result : parseLexed file lexed =
    .ok (pragmaSequenceParseOutput file lexed declarations kept)) :
    LexedFileValidationAccepts file lexed ∧
      ParseDiagnosticCascadeFilters file.content
        (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept :=
  (parseLexed_eq_ok_pragmaPrefixBoundary_iff clears parsed).mp result

example : parseLexed file lexed =
    .ok (pragmaSequenceParseOutput file lexed declarations kept) :=
  (parseLexed_eq_ok_pragmaPrefixBoundary_iff clears parsed).mpr ⟨accepted, filtered⟩

example (lexing : Lexer.lex file = .ok lexed) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept) :=
  parse_eq_ok_of_pragmaPrefixBoundary lexing clears parsed filtered

example (lexing : Lexer.lex file = .ok lexed)
    (result : parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept)) :
    ParseDiagnosticCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept :=
  (parse_eq_ok_pragmaPrefixBoundary_iff lexing clears parsed).mp result

example (lexing : Lexer.lex file = .ok lexed) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept) :=
  (parse_eq_ok_pragmaPrefixBoundary_iff lexing clears parsed).mpr filtered

include clears parsed in
/-- Suppressing the final report leaves all earlier events, including those
emitted inside the rejected pragma, and all successful prefix items intact. -/
theorem suppressed_report_keeps_prefix_and_events
    (lexing : Lexer.lex file = .ok lexed)
    (suppressed : ParseDiagnosticCascadeSuppresses file.content
      (lexed.diagnostics.map (·.span)) diagnostic) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations trace) := by
  apply parse_eq_ok_of_pragmaPrefixBoundary lexing clears parsed
  simpa only [List.append_nil] using
    (parsed.cascadeFilters file.content (lexed.diagnostics.map (·.span))).append
      (.drop suppressed .nil)

include clears parsed in
/-- A retained final report occurs once after the complete ordered preceding
trace. It neither replaces prior reports nor contributes a rejected AST item. -/
theorem retained_report_follows_prefix_events
    (lexing : Lexer.lex file = .ok lexed)
    (retained : ¬ ParseDiagnosticCascadeSuppresses file.content
      (lexed.diagnostics.map (·.span)) diagnostic) :
    parse file = .ok
      (pragmaSequenceParseOutput file lexed declarations (trace ++ [diagnostic])) := by
  apply parse_eq_ok_of_pragmaPrefixBoundary lexing clears parsed
  exact (parsed.cascadeFilters file.content (lexed.diagnostics.map (·.span))).append
    (.keep retained .nil)

include clears parsed in
/-- Without lexical diagnostics, the full trace and final report survive,
regardless of the number of successful declarations or duplicate events. -/
theorem no_lexical_errors_keeps_prefix_and_committed_trace
    (lexing : Lexer.lex file = .ok lexed) (noErrors : lexed.diagnostics = []) :
    parse file = .ok
      (pragmaSequenceParseOutput file lexed declarations (trace ++ [diagnostic])) := by
  apply parse_eq_ok_of_pragmaPrefixBoundary lexing clears parsed
  rw [noErrors, List.map_nil]
  exact parseDiagnosticCascadeFilters_nil_lexical file.content (trace ++ [diagnostic])

include clears filtered in
/-- The zero-successful-prefix constructor recovers the initial-pragma stop
case, with comments and lexical fields retained and no fabricated AST item. -/
theorem stopped_initial_pragma_has_no_items
    {marker : SourceSpan} {afterKeyword rejected : Remainder}
    (lexing : Lexer.lex file = .ok lexed)
    (recognized : ExactTokenParses (.keyword .pragmaKw)
      (sourceFileRootRemainder lexed.tokens) marker afterKeyword)
    (rejected : PragmaDeclTraceRejects file.id file.content.utf8ByteSize
      (sourceFileRootRemainder lexed.tokens) rejected diagnostic trace) :
    parse file = .ok (pragmaSequenceParseOutput file lexed [] kept) :=
  parse_eq_ok_of_pragmaPrefixBoundary lexing clears (.stopped marker recognized rejected) filtered

end Solcore.Test.SyntaxParserPublicPragmaPrefixBoundaryOutputProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPublicPragmaRejectionOutputProperties
/-! Complete public rejection consumers. Every premise describes independent
input, grammar, or filtering; none assumes a declaration or file parser reply. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaRejectionOutputProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {file : SourceFile} {lexed : LexedFile}
  {marker : SourceSpan} {afterKeyword rejected : Remainder}
  {diagnostic : ParseDiagnostic} {trace kept : List ParseDiagnostic}
  (accepted : LexedFileValidationAccepts file lexed)
  (clears : NestingClears lexed.tokens)
  (keywordParsed : ExactTokenParses (.keyword .pragmaKw)
    (sourceFileRootRemainder lexed.tokens) marker afterKeyword)
  (traced : PragmaDeclTraceRejects file.id file.content.utf8ByteSize
    (sourceFileRootRemainder lexed.tokens) rejected diagnostic trace)
  (filtered : ParseDiagnosticCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept)

example : parseLexed file lexed = .ok {
    parsed := {
      source := file.id
      span := SourceSpan.fullFile file
      items := []
      comments := lexed.comments
    }
    tokens := lexed.tokens
    lexicalDiagnostics := lexed.diagnostics
    parseDiagnostics := kept
  } :=
  parseLexed_eq_ok_of_pragmaRejection accepted clears keywordParsed traced filtered

example (result : parseLexed file lexed = .ok (pragmaRejectionParseOutput file lexed kept)) :
    LexedFileValidationAccepts file lexed ∧
      ParseDiagnosticCascadeFilters file.content
        (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept :=
  (parseLexed_eq_ok_pragmaRejection_iff clears keywordParsed traced).mp result

example : parseLexed file lexed = .ok (pragmaRejectionParseOutput file lexed kept) :=
  (parseLexed_eq_ok_pragmaRejection_iff clears keywordParsed traced).mpr ⟨accepted, filtered⟩

example (lexing : Lexer.lex file = .ok lexed) :
    parse file = .ok (pragmaRejectionParseOutput file lexed kept) :=
  parse_eq_ok_of_pragmaRejection lexing clears keywordParsed traced filtered

example (lexing : Lexer.lex file = .ok lexed)
    (result : parse file = .ok (pragmaRejectionParseOutput file lexed kept)) :
    ParseDiagnosticCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept :=
  (parse_eq_ok_pragmaRejection_iff lexing clears keywordParsed traced).mp result

example (lexing : Lexer.lex file = .ok lexed) :
    parse file = .ok (pragmaRejectionParseOutput file lexed kept) :=
  (parse_eq_ok_pragmaRejection_iff lexing clears keywordParsed traced).mpr filtered

include traced in
/-- Already emitted item diagnostics are protected even though the declaration
ultimately rejects; lexical cascade suppression cannot erase these events. -/
theorem rejected_item_events_retained :
    ParseDiagnosticCascadeFilters file.content (lexed.diagnostics.map (·.span)) trace trace :=
  traced.cascadeFilters file.content (lexed.diagnostics.map (·.span))

include clears keywordParsed traced in
/-- If no lexical errors occur, every prior event and the final report survive
in exactly that order. This is a complete output computation from grammar. -/
theorem no_lexical_errors_keeps_committed_trace
    (lexing : Lexer.lex file = .ok lexed) (noErrors : lexed.diagnostics = []) :
    parse file = .ok (pragmaRejectionParseOutput file lexed (trace ++ [diagnostic])) := by
  apply parse_eq_ok_of_pragmaRejection lexing clears keywordParsed traced
  rw [noErrors]
  apply parseDiagnosticCascadeFilters_of_retained file.content ([] : List SourceSpan)
  intro event _member suppressed
  rcases suppressed.2 with ⟨span, membership, _⟩
  simp only [List.not_mem_nil] at membership

end Solcore.Test.SyntaxParserPublicPragmaRejectionOutputProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPublicPragmaSequenceOutputProperties
/-! Complete public pragma-sequence consumers, including empty token carriers.
No example assumes an executable item or source-file reply. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaSequenceOutputProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
  {after : Remainder} {trace kept : List ParseDiagnostic}
  (accepted : LexedFileValidationAccepts file lexed)
  (clears : NestingClears lexed.tokens)
  (parsed : PragmaSequenceTraceParses (sourceFileRootRemainder lexed.tokens)
    declarations after trace)

example : parseLexed file lexed = .ok {
    parsed := {
      source := file.id
      span := SourceSpan.fullFile file
      items := (declarations.map FileInternals.wrapPragma).map
        (Trivia.attachTopItemComments file lexed.comments)
      comments := lexed.comments
    }
    tokens := lexed.tokens
    lexicalDiagnostics := lexed.diagnostics
    parseDiagnostics := trace
  } :=
  parseLexed_eq_ok_of_pragmaSequence accepted clears parsed

example (result : parseLexed file lexed =
    .ok (pragmaSequenceParseOutput file lexed declarations kept)) :
    LexedFileValidationAccepts file lexed ∧ kept = trace :=
  (parseLexed_eq_ok_pragmaSequence_iff clears parsed).mp result

example (same : kept = trace) :
    parseLexed file lexed = .ok (pragmaSequenceParseOutput file lexed declarations kept) :=
  (parseLexed_eq_ok_pragmaSequence_iff clears parsed).mpr ⟨accepted, same⟩

example (lexing : Lexer.lex file = .ok lexed) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations trace) :=
  parse_eq_ok_of_pragmaSequence lexing clears parsed

example (lexing : Lexer.lex file = .ok lexed)
    (result : parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept)) :
    kept = trace := (parse_eq_ok_pragmaSequence_iff lexing clears parsed).mp result

example (lexing : Lexer.lex file = .ok lexed) (same : kept = trace) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept) :=
  (parse_eq_ok_pragmaSequence_iff lexing clears parsed).mpr same

example (filtered : ParseDiagnosticCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) trace kept) : kept = trace :=
  (parsed.cascadeFilters_iff file.content (lexed.diagnostics.map (·.span))).mp filtered

/-- The empty grammar case retains arbitrary lexical diagnostics and comments;
neither clear nesting nor an executable parser result needs to be assumed. -/
theorem empty_sequence_parse_eq_output
    (lexing : Lexer.lex file = .ok lexed) (empty : lexed.tokens = []) :
    parse file = .ok {
      parsed := {
        source := file.id
        span := SourceSpan.fullFile file
        items := []
        comments := lexed.comments
      }
      tokens := lexed.tokens
      lexicalDiagnostics := lexed.diagnostics
      parseDiagnostics := []
    } := by
  have emptyGrammar : PragmaSequenceTraceParses (sourceFileRootRemainder lexed.tokens)
      [] (sourceFileRootRemainder lexed.tokens) [] :=
    .done (by simp [sourceFileRootRemainder, empty])
  have emptyClears : NestingClears lexed.tokens := by
    rw [empty]
    exact .done
  exact parse_eq_ok_of_pragmaSequence lexing emptyClears emptyGrammar

end Solcore.Test.SyntaxParserPublicPragmaSequenceOutputProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPublicPragmaSuccessExamples
/-! Ground complete pragma outputs derived from independent grammar and traces.
Only canonical lexical fixtures are evaluated by kernel-backed decision. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples

def atCursor (tokens : List Token) (cursor : Nat) : Remainder := {
  sourceFileRootRemainder tokens with cursor
}

def identifierToken (startByte endByte : Nat) (text : String) : Token := {
  span := byteSpan startByte endByte, value := .identifier text
}

def commaToken (offset : Nat) : Token := {
  span := byteSpan offset (offset + 1), value := .symbol .comma
}

/-- Every output field is explicit, including attached comments and diagnostics. -/
def pragmaOutput (content : String) (lexed : LexedFile) (declaration : PragmaDecl)
    (leading : List Comment) (trace : List ParseDiagnostic) : ParseOutput := {
  parsed := {
    source := exampleSource
    span := SourceSpan.fullFile (exampleFile content)
    items := [{
      span := declaration.span
      leadingComments := leading
      value := .pragmaDecl declaration }]
    comments := lexed.comments
  }
  tokens := lexed.tokens
  lexicalDiagnostics := lexed.diagnostics
  parseDiagnostics := trace
}

def rawTokens (offset : Nat) : List Token := [pragmaToken offset,
  identifierToken (offset + 7) (offset + 14) "foo-bar", semicolonToken (offset + 14)]

def rawDeclaration (offset : Nat) : PragmaDecl := {
  span := SourceSpan.cover (pragmaToken offset).span (semicolonToken (offset + 14)).span
  value := {
    name := { span := byteSpan (offset + 7) (offset + 14), value := "foo-bar" }
    items := [] }
}

/-- The raw name is parsed exactly but contributes no checked-name event. -/
theorem rawParsed (offset : Nat) :
    PragmaDeclTraceParses (sourceFileRootRemainder (rawTokens offset))
      (rawDeclaration offset) (atCursor (rawTokens offset) 3) [] := by
  refine ⟨?_, .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor (rawTokens offset) 1)
    (afterName := atCursor (rawTokens offset) 2)
    (afterItems := atCursor (rawTokens offset) 2)
    (pragmaToken offset).span (semicolonToken (offset + 14)).span
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, rawTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, rawTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.empty
    exact ⟨(semicolonToken (offset + 14)).span, by
      simp [TokenAt, sourceFileRootRemainder, atCursor, rawTokens, semicolonToken]⟩
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, rawTokens, semicolonToken]

theorem rawClears (offset : Nat) : NestingClears (rawTokens offset) :=
  .preserve rfl (.preserve rfl (.reset rfl .done))

set_option maxRecDepth 4096 in
private theorem rawLexes : Lexer.lex (exampleFile "pragma foo-bar;") =
    .ok (lexicalCarrier (rawTokens 0) []) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- A hyphenated raw pragma name has a complete successful, diagnostic-free
public result; it is not checked like a pragma item. -/
theorem rawNameHyphen_parse_eq_output :
    parse (exampleFile "pragma foo-bar;") =
      .ok (pragmaOutput "pragma foo-bar;" (lexicalCarrier (rawTokens 0) [])
        (rawDeclaration 0) [] []) :=
  parse_eq_ok_of_singlePragmaTrace rawLexes (rawClears 0) (rawParsed 0) rfl

def multipleTokens : List Token := [pragmaToken 0, identifierToken 7 8 "p",
  identifierToken 9 20 "foo-bar-baz", commaToken 20,
  identifierToken 21 29 "qux-quux", commaToken 29, semicolonToken 30]

def multipleDeclaration : PragmaDecl := {
  span := byteSpan 0 31
  value := {
    name := { span := byteSpan 7 8, value := "p" }
    items := [{ span := byteSpan 9 20, value := "foo-bar-baz" },
      { span := byteSpan 21 29, value := "qux-quux" }]
  }
}

def multipleTrace : List ParseDiagnostic := [
  { span := byteSpan 9 20, kind := .invalidIdentifierHyphen "foo-bar-baz" },
  { span := byteSpan 21 29, kind := .invalidIdentifierHyphen "qux-quux" }]

private theorem multipleParsed :
    PragmaDeclTraceParses (sourceFileRootRemainder multipleTokens) multipleDeclaration
      (atCursor multipleTokens 7) multipleTrace := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "foo-bar-baz".toList; decide))
    (.cons (.hyphen (by change '-' ∈ "qux-quux".toList; decide)) .nil)⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor multipleTokens 1)
    (afterName := atCursor multipleTokens 2)
    (afterItems := atCursor multipleTokens 6) (byteSpan 0 6) (byteSpan 30 31)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, multipleTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, multipleTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor multipleTokens 3)
    · simp [TokenKindAbsentAt, TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.next
        (afterComma := atCursor multipleTokens 4) (afterItem := atCursor multipleTokens 5)
        (byteSpan 20 21)
      · exact ⟨byteSpan 20 21, by
          simp [TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, commaToken]⟩
      · simp [ExactTokenParses, TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, commaToken]
      · simp [TokenKindAbsentAt, TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, identifierToken]
      · simp [IdentifierParses, TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, identifierToken]
      · apply PragmaItemsTailOrdinaryParses.trailing (byteSpan 29 30)
        · exact ⟨byteSpan 29 30, by
            simp [TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, commaToken]⟩
        · simp [ExactTokenParses, TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, commaToken]
        · exact ⟨byteSpan 30 31, by
            simp [TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, semicolonToken]⟩
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, multipleTokens, semicolonToken]

set_option maxRecDepth 8192 in
private theorem multipleLexes : Lexer.lex (exampleFile "pragma p foo-bar-baz,qux-quux,;") =
    .ok (lexicalCarrier multipleTokens []) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- Multiple checked items emit once per item, not once per hyphen. The
trailing comma is accepted and emits no additional event. -/
theorem multipleItemsTrailingComma_parse_eq_output :
    parse (exampleFile "pragma p foo-bar-baz,qux-quux,;") =
      .ok (pragmaOutput "pragma p foo-bar-baz,qux-quux,;" (lexicalCarrier multipleTokens [])
        multipleDeclaration [] multipleTrace) :=
  parse_eq_ok_of_singlePragmaTrace multipleLexes
    (.preserve rfl (.preserve rfl (.preserve rfl (.reset rfl
      (.preserve rfl (.reset rfl (.reset rfl .done))))))) multipleParsed rfl

end Solcore.Test.SyntaxParserPublicPragmaSuccessExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures
/-! Canonical carriers and independent exact later-stage pragma rejection.
Only lexical fixtures are evaluated; parser replies are never assumed here. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

def prefixTokens (offset : Nat) : List Token := [pragmaToken offset,
  identifierToken (offset + 7) (offset + 8) "p",
  identifierToken (offset + 9) (offset + 12) "a-b"]

def missingItemTokens (offset : Nat) : List Token :=
  prefixTokens offset ++ [commaToken (offset + 12)]

def rawName (offset : Nat) : Identifier := {
  span := byteSpan (offset + 7) (offset + 8), value := "p"
}

def checkedItem (offset : Nat) : Identifier := {
  span := byteSpan (offset + 9) (offset + 12), value := "a-b"
}

def hyphenEvent (offset : Nat) : ParseDiagnostic := {
  span := (checkedItem offset).span, kind := .invalidIdentifierHyphen "a-b"
}

def eofUnexpected (endByte : Nat) (expected : ParseExpectation) : ParseDiagnostic := {
  span := byteSpan endByte endByte
  kind := .unexpected none { head := expected, tail := [] } .pragmaDecl
}

def lexicalInvalid : LexicalDiagnostic := { span := byteSpan 0 2, kind := .invalidToken }

theorem prefixKeyword (offset : Nat) (rest : List Token) :
    ExactTokenParses (.keyword .pragmaKw) (sourceFileRootRemainder (prefixTokens offset ++ rest))
      (pragmaToken offset).span (atCursor (prefixTokens offset ++ rest) 1) := by
  simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, prefixTokens, pragmaToken]

theorem prefixClears (offset : Nat) (rest : List Token) (clears : NestingClears rest) :
    NestingClears (prefixTokens offset ++ rest) :=
  .preserve rfl (.preserve rfl (.preserve rfl clears))

/-- The first item succeeds and emits once; the comma then requires a new
identifier, so EOF reports an identifier expectation at the exact byte end. -/
theorem missingItemDeclRejects (offset : Nat) :
    PragmaDeclTraceRejects exampleSource (offset + 13)
      (sourceFileRootRemainder (missingItemTokens offset))
      (atCursor (missingItemTokens offset) 4)
      (eofUnexpected (offset + 13) .identifier) [hyphenEvent offset] := by
  apply PragmaDeclTraceRejects.itemsRejected
    (afterKeyword := atCursor (missingItemTokens offset) 1)
    (afterName := atCursor (missingItemTokens offset) 2)
    (name := rawName offset) (pragmaToken offset).span
  · exact prefixKeyword offset [commaToken (offset + 12)]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor,
      missingItemTokens, prefixTokens, rawName, identifierToken]
  · refine ⟨[checkedItem offset], ?_,
      .cons (.hyphen (by change '-' ∈ "a-b".toList; decide)) .nil, ?_⟩
    · apply PragmaItemsRejectedPrefix.tailRejected
        (afterFirst := atCursor (missingItemTokens offset) 3)
      · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor,
          missingItemTokens, prefixTokens, identifierToken]
      · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor,
          missingItemTokens, prefixTokens, checkedItem, identifierToken]
      · apply PragmaItemsTailRejectedPrefix.identifierRejected
          (afterComma := atCursor (missingItemTokens offset) 4)
          (byteSpan (offset + 12) (offset + 13))
        · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor,
            missingItemTokens, prefixTokens, commaToken, Nat.add_assoc]
        · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor,
            missingItemTokens, prefixTokens]
        · apply IdentifierRejects.absent
          simp [IdentifierAbsentAt, TokenAt, sourceFileRootRemainder, atCursor,
            missingItemTokens, prefixTokens]
    · apply RejectAtReports.reported
      exact .windowEnd (by simp [sourceFileRootRemainder, atCursor, missingItemTokens, prefixTokens])

/-- Without a comma the item scan succeeds; only the final semicolon is
missing, and the already emitted hyphen event still precedes its report. -/
theorem missingSemicolonDeclRejects (offset : Nat) :
    PragmaDeclTraceRejects exampleSource (offset + 12)
      (sourceFileRootRemainder (prefixTokens offset)) (atCursor (prefixTokens offset) 3)
      (eofUnexpected (offset + 12) (.symbol .semicolon)) [hyphenEvent offset] := by
  apply PragmaDeclTraceRejects.semicolonMissing
    (afterKeyword := atCursor (prefixTokens offset) 1)
    (afterName := atCursor (prefixTokens offset) 2)
    (name := rawName offset) (items := [checkedItem offset]) (pragmaToken offset).span
  · exact prefixKeyword offset []
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor,
      prefixTokens, rawName, identifierToken]
  · refine ⟨?_, .cons (.hyphen (by change '-' ∈ "a-b".toList; decide)) .nil⟩
    apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor (prefixTokens offset) 3)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, prefixTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, prefixTokens,
        checkedItem, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, prefixTokens]
  · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, prefixTokens]
  · apply RejectAtReports.reported
    exact .windowEnd (by simp [sourceFileRootRemainder, atCursor, prefixTokens])

set_option maxRecDepth 8192 in
theorem missingItemLexes : Lexer.lex (exampleFile "pragma p a-b,") =
    .ok (lexicalCarrier (missingItemTokens 0) []) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 8192 in
theorem missingSemicolonLexes : Lexer.lex (exampleFile "pragma p a-b") =
    .ok (lexicalCarrier (prefixTokens 0) []) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 8192 in
theorem sameLineLexes : Lexer.lex (exampleFile "§ pragma p a-b,") =
    .ok (lexicalCarrier (missingItemTokens 3) [lexicalInvalid]) := by
  apply lex_ok_of_toOption
  decide +kernel

end Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaPrefixBoundaryFixtures
/-! Canonical successful-then-rejected pragma carriers. Independent grammar
fixes the successful AST, rewound second marker, and two prior identifier events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaPrefixBoundaryFixtures

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples
open Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures (eofUnexpected)

def boundaryTokens (secondOffset : Nat) : List Token := [
  pragmaToken 0, identifierToken 7 8 "p", identifierToken 9 12 "a-b", semicolonToken 12,
  pragmaToken secondOffset, identifierToken (secondOffset + 7) (secondOffset + 8) "q",
  identifierToken (secondOffset + 9) (secondOffset + 12) "c-d",
  commaToken (secondOffset + 12)]

def keptDeclaration : PragmaDecl := {
  span := byteSpan 0 13
  value := {
    name := { span := byteSpan 7 8, value := "p" }
    items := [{ span := byteSpan 9 12, value := "a-b" }]
  }
}

def firstEvent : ParseDiagnostic := {
  span := byteSpan 9 12, kind := .invalidIdentifierHyphen "a-b"
}

def failedItem (offset : Nat) : Identifier := {
  span := byteSpan (offset + 9) (offset + 12), value := "c-d"
}

def secondEvent (offset : Nat) : ParseDiagnostic := {
  span := (failedItem offset).span, kind := .invalidIdentifierHyphen "c-d"
}

private theorem firstParsed (offset : Nat) :
    PragmaDeclTraceParses (sourceFileRootRemainder (boundaryTokens offset)) keptDeclaration
      (atCursor (boundaryTokens offset) 4) [firstEvent] := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "a-b".toList; decide)) .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor (boundaryTokens offset) 1)
    (afterName := atCursor (boundaryTokens offset) 2)
    (afterItems := atCursor (boundaryTokens offset) 3) (byteSpan 0 6) (byteSpan 12 13)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor (boundaryTokens offset) 3)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, semicolonToken]
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, semicolonToken]

private theorem secondKeyword (offset : Nat) :
    ExactTokenParses (.keyword .pragmaKw) (atCursor (boundaryTokens offset) 4)
      (pragmaToken offset).span (atCursor (boundaryTokens offset) 5) := by
  simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, pragmaToken]

private theorem secondRejected (offset : Nat) :
    PragmaDeclTraceRejects exampleSource (offset + 13) (atCursor (boundaryTokens offset) 4)
      (atCursor (boundaryTokens offset) 8) (eofUnexpected (offset + 13) .identifier)
      [secondEvent offset] := by
  apply PragmaDeclTraceRejects.itemsRejected
    (afterKeyword := atCursor (boundaryTokens offset) 5)
    (afterName := atCursor (boundaryTokens offset) 6)
    (name := { span := byteSpan (offset + 7) (offset + 8), value := "q" })
    (pragmaToken offset).span
  · exact secondKeyword offset
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, identifierToken]
  · refine ⟨[failedItem offset], ?_,
      .cons (.hyphen (by change '-' ∈ "c-d".toList; decide)) .nil, ?_⟩
    · apply PragmaItemsRejectedPrefix.tailRejected
        (afterFirst := atCursor (boundaryTokens offset) 7)
      · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, identifierToken]
      · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor,
          boundaryTokens, failedItem, identifierToken]
      · apply PragmaItemsTailRejectedPrefix.identifierRejected
          (afterComma := atCursor (boundaryTokens offset) 8)
          (byteSpan (offset + 12) (offset + 13))
        · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor,
            boundaryTokens, commaToken, Nat.add_assoc]
        · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens]
        · apply IdentifierRejects.absent
          simp [IdentifierAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens]
    · apply RejectAtReports.reported
      exact .windowEnd (by simp [sourceFileRootRemainder, atCursor, boundaryTokens])

/-- The failed declaration emits its checked-name event, but yields no AST;
its cursor is rewound to token four while the exact EOF report stays separate. -/
theorem boundaryParsed (offset : Nat) :
    PragmaPrefixBoundaryTraceParses exampleSource (offset + 13)
      (sourceFileRootRemainder (boundaryTokens offset)) [keptDeclaration]
      (atCursor (boundaryTokens offset) 4) (eofUnexpected (offset + 13) .identifier)
      [firstEvent, secondEvent offset] :=
  .cons (firstParsed offset)
    (.stopped (pragmaToken offset).span (secondKeyword offset) (secondRejected offset))

theorem boundaryClears (offset : Nat) : NestingClears (boundaryTokens offset) :=
  .preserve rfl (.preserve rfl (.preserve rfl (.reset rfl
    (.preserve rfl (.preserve rfl (.preserve rfl (.reset rfl .done)))))))

def lexicalBetween : LexicalDiagnostic := {
  span := byteSpan 14 16, kind := .invalidToken
}

set_option maxRecDepth 8192 in
theorem cleanBoundaryLexes : Lexer.lex (exampleFile "pragma p a-b; pragma q c-d,") =
    .ok (lexicalCarrier (boundaryTokens 14) []) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 8192 in
theorem sameLineBoundaryLexes : Lexer.lex (exampleFile "pragma p a-b; § pragma q c-d,") =
    .ok (lexicalCarrier (boundaryTokens 17) [lexicalBetween]) := by
  apply lex_ok_of_toOption
  decide +kernel

end Solcore.Test.SyntaxParserPragmaPrefixBoundaryFixtures
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPragmaSequenceTraceProperties
/-! Independent pragma-sequence consumers preserve old item prefixes, exact
fresh declaration/diagnostic order, carrier endpoints, and supplied comments. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaSequenceTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

example := @PragmaDeclOrdinaryParses.startsInside
example := @PragmaDeclOrdinaryParses.carrier_progress
example := @PragmaDeclOrdinaryParses.toTopItem
example := @PragmaSequenceTraceParses.carrier_atEnd
example := @PragmaSequenceTraceParses.length_le_remaining
example := @PragmaSequenceTraceParses.toFileItems
example := @PragmaSequenceTraceParses.result_unique
example := @parseItems_pragmaSequence_trace_of_length_lt
example := @parseItems_pragmaSequence_trace_of_remainingCount_lt
example := @parseItems_production_pragmaSequence_trace
example := @sourceFile_pragmaSequence_trace

/-- Empty grammar requires the active end, not an empty token array, and
preserves all existing items and raw diagnostics without a validity premise. -/
theorem emptySequence_retains_prefix (itemsRev : List TopItem) (input : State)
    (atEnd : input.window.endIndex ≤ input.cursor) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok itemsRev.reverse output ∧
      output.declarativeRemainder = input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics := by
  simpa only [List.map_nil, List.append_nil] using
    parseItems_production_pragmaSequence_trace itemsRev
      (input := input) (PragmaSequenceTraceParses.done atEnd)

/-- An already reversed two-item prefix is restored once, before every fresh
pragma; only the independent fresh sequence contributes additional diagnostics. -/
theorem reversePrefix_order (first second : TopItem)
    {input : State} {declarations : List PragmaDecl} {after : Remainder}
    {trace : List ParseDiagnostic}
    (parsed : PragmaSequenceTraceParses input.declarativeRemainder declarations after trace) :
    ∃ output, parseItems (input.remainingCount + 1) [second, first] input =
        .ok ([first, second] ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] using parseItems_production_pragmaSequence_trace [second, first] parsed

private def pairTokens : List Token := [pragmaToken 0, identifierToken 7 8 "a",
  identifierToken 9 12 "x-y", semicolonToken 12, pragmaToken 14,
  identifierToken 21 22 "b", identifierToken 23 26 "z-w", semicolonToken 26]

private def firstDeclaration : PragmaDecl := {
  span := byteSpan 0 13
  value := {
    name := { span := byteSpan 7 8, value := "a" }
    items := [{ span := byteSpan 9 12, value := "x-y" }] }
}

private def secondDeclaration : PragmaDecl := {
  span := byteSpan 14 27
  value := {
    name := { span := byteSpan 21 22, value := "b" }
    items := [{ span := byteSpan 23 26, value := "z-w" }] }
}

private def firstDiagnostic : ParseDiagnostic := {
  span := byteSpan 9 12, kind := .invalidIdentifierHyphen "x-y"
}

private def secondDiagnostic : ParseDiagnostic := {
  span := byteSpan 23 26, kind := .invalidIdentifierHyphen "z-w"
}

private theorem firstParsed :
    PragmaDeclTraceParses (sourceFileRootRemainder pairTokens) firstDeclaration
      (atCursor pairTokens 4) [firstDiagnostic] := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "x-y".toList; decide)) .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor pairTokens 1) (afterName := atCursor pairTokens 2)
    (afterItems := atCursor pairTokens 3) (byteSpan 0 6) (byteSpan 12 13)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor pairTokens 3)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, semicolonToken]
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, semicolonToken]

private theorem secondParsed :
    PragmaDeclTraceParses (atCursor pairTokens 4) secondDeclaration
      (atCursor pairTokens 8) [secondDiagnostic] := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "z-w".toList; decide)) .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor pairTokens 5) (afterName := atCursor pairTokens 6)
    (afterItems := atCursor pairTokens 7) (byteSpan 14 20) (byteSpan 26 27)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor pairTokens 7)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, semicolonToken]
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, semicolonToken]

private theorem pairParsed : PragmaSequenceTraceParses (sourceFileRootRemainder pairTokens)
    [firstDeclaration, secondDeclaration] (atCursor pairTokens 8)
    [firstDiagnostic, secondDiagnostic] :=
  .cons firstParsed (.cons secondParsed (.done (by decide)))

private def pairInput (priorRev : List ParseDiagnostic) : State := {
  file := exampleFile "pragma a x-y; pragma b z-w;"
  tokens := pairTokens.toArray
  cursor := 0
  window := { endIndex := 8, endByte := 27 }
  diagnosticsRev := priorRev
}

/-- Three loop steps suffice for two declarations and the final end check.
An existing copy of a hyphenated pragma is returned but not diagnosed again. -/
theorem existingPragmaPrefix_notRediagnosed (priorRev : List ParseDiagnostic) :
    ∃ output, parseItems 3 [wrapPragma firstDeclaration] (pairInput priorRev) =
        .ok [wrapPragma firstDeclaration, wrapPragma firstDeclaration,
          wrapPragma secondDeclaration] output ∧
      output.declarativeRemainder = atCursor pairTokens 8 ∧
      output.diagnostics = priorRev.reverse ++ [firstDiagnostic, secondDiagnostic] := by
  exact parseItems_pragmaSequence_trace_of_length_lt 3 [wrapPragma firstDeclaration]
    (input := pairInput priorRev) pairParsed (by decide)

/-- The production bound yields the same fresh order and raw trace, with all
supplied comments attached only by the source-file wrapper. -/
theorem pair_sourceFile_exact (priorRev : List ParseDiagnostic) (comments : List Comment) :
    ∃ output, sourceFile comments (pairInput priorRev) = .ok {
        source := exampleSource
        span := SourceSpan.fullFile (exampleFile "pragma a x-y; pragma b z-w;")
        items := [attachTopItemComments (pairInput priorRev).file comments
          (wrapPragma firstDeclaration), attachTopItemComments (pairInput priorRev).file comments
          (wrapPragma secondDeclaration)]
        comments
      } output ∧
      output.declarativeRemainder = atCursor pairTokens 8 ∧
      output.diagnostics = priorRev.reverse ++ [firstDiagnostic, secondDiagnostic] :=
  sourceFile_pragmaSequence_trace comments (input := pairInput priorRev) pairParsed

end Solcore.Test.SyntaxParserPragmaSequenceTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPublicPragmaLaterRejectionExamples
/-! Complete canonical-source outputs after a recognized pragma fails later.
Independent grammar and mixed filtering preserve prior events before the
committed failure, while lexical cascades remove only eligible reports. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaLaterRejectionExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples
open Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures

/-- Comma followed by EOF is not the accepted comma-semicolon trailing form.
The checked-name event precedes the committed missing-identifier report. -/
theorem missingItem_parse_eq_output :
    parse (exampleFile "pragma p a-b,") =
      .ok (expectedOutput "pragma p a-b," (missingItemTokens 0) []
        [hyphenEvent 0, eofUnexpected 13 .identifier]) :=
  parse_eq_ok_of_pragmaRejection missingItemLexes
    (prefixClears 0 [commaToken 12] (.reset rfl .done))
    (prefixKeyword 0 [commaToken 12]) (missingItemDeclRejects 0)
    (parseDiagnosticCascadeFilters_nil_lexical "pragma p a-b,"
      [hyphenEvent 0, eofUnexpected 13 .identifier])

/-- Without a comma, item scanning succeeds and the final semicolon is
expected. No unfinished pragma AST escapes, but its checked-name event remains. -/
theorem missingSemicolon_parse_eq_output :
    parse (exampleFile "pragma p a-b") =
      .ok (expectedOutput "pragma p a-b" (prefixTokens 0) []
        [hyphenEvent 0, eofUnexpected 12 (.symbol .semicolon)]) :=
  parse_eq_ok_of_pragmaRejection missingSemicolonLexes
    (prefixClears 0 [] .done) (prefixKeyword 0 []) (missingSemicolonDeclRejects 0)
    (parseDiagnosticCascadeFilters_nil_lexical "pragma p a-b"
      [hyphenEvent 0, eofUnexpected 12 (.symbol .semicolon)])

/-- A same-line lexical error suppresses only the trailing unexpected event;
the earlier invalid-identifier kind remains protected despite the same line. -/
theorem sameLineMixedFiltered :
    ParseDiagnosticCascadeFilters "§ pragma p a-b," [lexicalInvalid.span]
      [hyphenEvent 3, eofUnexpected 16 .identifier] [hyphenEvent 3] := by
  apply parseDiagnosticCascadeFilters_protected_cons
  · change ¬ False
    exact id
  · apply ParseDiagnosticCascadeFilters.drop
    · refine ⟨True.intro, lexicalInvalid.span, by simp, rfl, Or.inl ?_⟩
      decide
    · exact .nil

/-- Lexical diagnostics and the protected checked-name event survive in the
complete output, while the committed EOF expectation is filtered out. -/
theorem sameLineLexical_parse_eq_output :
    parse (exampleFile "§ pragma p a-b,") =
      .ok (expectedOutput "§ pragma p a-b," (missingItemTokens 3) [lexicalInvalid]
        [hyphenEvent 3]) :=
  parse_eq_ok_of_pragmaRejection sameLineLexes
    (prefixClears 3 [commaToken 15] (.reset rfl .done))
    (prefixKeyword 3 [commaToken 15]) (missingItemDeclRejects 3) sameLineMixedFiltered

/-- The token-to-file entry point returns all the same fields using validity
from the identical canonical lexer fixture, not an assumed parser execution. -/
theorem sameLineLexical_parseLexed_eq_output :
    parseLexed (exampleFile "§ pragma p a-b,")
        (lexicalCarrier (missingItemTokens 3) [lexicalInvalid]) =
      .ok (expectedOutput "§ pragma p a-b," (missingItemTokens 3) [lexicalInvalid]
        [hyphenEvent 3]) :=
  parseLexed_eq_ok_of_pragmaRejection
    ((lexedFileValidationAccepts_iff_validFor _ _).mpr (Lexer.lex_ok_validFor _ _ sameLineLexes))
    (prefixClears 3 [commaToken 15] (.reset rfl .done))
    (prefixKeyword 3 [commaToken 15]) (missingItemDeclRejects 3) sameLineMixedFiltered

end Solcore.Test.SyntaxParserPublicPragmaLaterRejectionExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPublicPragmaPrefixBoundaryExamples
/-! Complete successful-prefix outputs followed by a recognized pragma failure.
The successful AST survives, as do both prior checked-name events; only the
separately committed EOF report is eligible for lexical-cascade suppression. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaPrefixBoundaryExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples
open Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures (eofUnexpected)
open Solcore.Test.SyntaxParserPragmaPrefixBoundaryFixtures

/-- Only the first pragma contributes an AST. Tokens and lexical diagnostics
still describe the entire input, including the unfinished second declaration. -/
private def boundaryOutput (content : String) (offset : Nat)
    (lexical : List LexicalDiagnostic) (kept : List ParseDiagnostic) : ParseOutput := {
  parsed := {
    source := exampleSource
    span := SourceSpan.fullFile (exampleFile content)
    items := [{
      span := keptDeclaration.span
      leadingComments := []
      value := .pragmaDecl keptDeclaration }]
    comments := []
  }
  tokens := boundaryTokens offset
  lexicalDiagnostics := lexical
  parseDiagnostics := kept
}

/-- The successful item's event precedes the rejected pragma's event, followed
exactly once by the committed identifier expectation at EOF byte 27. -/
theorem successfulThenRejected_parse_eq_output :
    parse (exampleFile "pragma p a-b; pragma q c-d,") =
      .ok (boundaryOutput "pragma p a-b; pragma q c-d," 14 []
        [firstEvent, secondEvent 14, eofUnexpected 27 .identifier]) :=
  parse_eq_ok_of_pragmaPrefixBoundary cleanBoundaryLexes (boundaryClears 14) (boundaryParsed 14)
    (parseDiagnosticCascadeFilters_nil_lexical "pragma p a-b; pragma q c-d,"
      [firstEvent, secondEvent 14, eofUnexpected 27 .identifier])

/-- Both protected events retain their exact order and payloads while the
same-line lexical error suppresses only the final unexpected-token report. -/
theorem sameLineMixedFiltered :
    ParseDiagnosticCascadeFilters "pragma p a-b; § pragma q c-d," [lexicalBetween.span]
      [firstEvent, secondEvent 17, eofUnexpected 30 .identifier] [firstEvent, secondEvent 17] := by
  refine .keep (fun h => h.1) (.keep (fun h => h.1) (.drop ?_ .nil))
  refine ⟨True.intro, lexicalBetween.span, by simp, rfl, Or.inl ?_⟩
  decide

/-- A lexical error between the declarations retains the successful singleton
AST and both hyphen events, but removes the committed EOF report from the output. -/
theorem sameLineLexical_parse_eq_output :
    parse (exampleFile "pragma p a-b; § pragma q c-d,") =
      .ok (boundaryOutput "pragma p a-b; § pragma q c-d," 17 [lexicalBetween]
        [firstEvent, secondEvent 17]) :=
  parse_eq_ok_of_pragmaPrefixBoundary sameLineBoundaryLexes
    (boundaryClears 17) (boundaryParsed 17) sameLineMixedFiltered

/-- Validation comes from canonical lexing; no executable parser outcome is
assumed when computing the identical complete token-to-file result. -/
theorem sameLineLexical_parseLexed_eq_output :
    parseLexed (exampleFile "pragma p a-b; § pragma q c-d,")
        (lexicalCarrier (boundaryTokens 17) [lexicalBetween]) =
      .ok (boundaryOutput "pragma p a-b; § pragma q c-d," 17 [lexicalBetween]
        [firstEvent, secondEvent 17]) :=
  parseLexed_eq_ok_of_pragmaPrefixBoundary
    ((lexedFileValidationAccepts_iff_validFor _ _).mpr
      (Lexer.lex_ok_validFor _ _ sameLineBoundaryLexes))
    (boundaryClears 17) (boundaryParsed 17) sameLineMixedFiltered

end Solcore.Test.SyntaxParserPublicPragmaPrefixBoundaryExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPublicPragmaProtectedTraceExamples
/-! Lexical cascades cannot suppress successful pragma's protected identifier
events. A comment fixture also fixes both retained and attached comment lists. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaProtectedTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

private def invalidToken : LexicalDiagnostic := {
  span := byteSpan 0 2, kind := .invalidToken
}

private def protectedTokens : List Token := [pragmaToken 3, identifierToken 10 11 "p",
  identifierToken 12 19 "foo-bar", semicolonToken 19]

private def protectedDeclaration : PragmaDecl := {
  span := byteSpan 3 20
  value := {
    name := { span := byteSpan 10 11, value := "p" }
    items := [{ span := byteSpan 12 19, value := "foo-bar" }]
  }
}

private def protectedTrace : List ParseDiagnostic := [
  { span := byteSpan 12 19, kind := .invalidIdentifierHyphen "foo-bar" }]

private theorem protectedParsed :
    PragmaDeclTraceParses (sourceFileRootRemainder protectedTokens) protectedDeclaration
      (atCursor protectedTokens 4) protectedTrace := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "foo-bar".toList; decide)) .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor protectedTokens 1)
    (afterName := atCursor protectedTokens 2)
    (afterItems := atCursor protectedTokens 3) (byteSpan 3 9) (byteSpan 19 20)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, protectedTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, protectedTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor protectedTokens 3)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, protectedTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, protectedTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, protectedTokens, semicolonToken]
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, protectedTokens, semicolonToken]

set_option maxRecDepth 8192 in
private theorem protectedLexes : Lexer.lex (exampleFile "§ pragma p foo-bar;") =
    .ok (lexicalCarrier protectedTokens [invalidToken]) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- These two spans satisfy the same-LF-line cascade relation that would
suppress an unexpected/recovery report, making protection non-vacuous. -/
theorem sameLineCascadeApplies :
    LexicalCascadeSuppresses "§ pragma p foo-bar;" [invalidToken.span] (byteSpan 12 19) := by
  exact ⟨invalidToken.span, by simp, rfl, Or.inl (by decide)⟩

/-- The lexical invalid character and checked-name diagnostic both remain,
with exact independent spans and a complete singleton-pragma AST. -/
theorem protectedHyphen_parse_eq_output :
    parse (exampleFile "§ pragma p foo-bar;") =
      .ok (pragmaOutput "§ pragma p foo-bar;" (lexicalCarrier protectedTokens [invalidToken])
        protectedDeclaration [] protectedTrace) :=
  parse_eq_ok_of_singlePragmaTrace protectedLexes
    (.preserve rfl (.preserve rfl (.preserve rfl (.reset rfl .done)))) protectedParsed rfl

/-- Already-tokenized public parsing preserves the identical protected trace. -/
theorem protectedHyphen_parseLexed_eq_output :
    parseLexed (exampleFile "§ pragma p foo-bar;") (lexicalCarrier protectedTokens [invalidToken]) =
      .ok (pragmaOutput "§ pragma p foo-bar;" (lexicalCarrier protectedTokens [invalidToken])
        protectedDeclaration [] protectedTrace) :=
  parseLexed_eq_ok_of_singlePragmaTrace
    ((lexedFileValidationAccepts_iff_validFor _ _).mpr (Lexer.lex_ok_validFor _ _ protectedLexes))
    (.preserve rfl (.preserve rfl (.preserve rfl (.reset rfl .done)))) protectedParsed rfl

private def docComment : Comment := {
  kind := .line, text := " doc", span := byteSpan 0 6
}

private def commentedLexed : LexedFile := {
  source := exampleSource, tokens := rawTokens 7, comments := [docComment], diagnostics := []
}

set_option maxRecDepth 8192 in
private theorem commentLexes : Lexer.lex (exampleFile "// doc\npragma foo-bar;") =
    .ok commentedLexed := by
  apply lex_ok_of_toOption
  decide +kernel

/-- The original line comment is retained file-wide and attached once to the
pragma item. The raw hyphenated name still contributes no diagnostic event. -/
theorem commentAttachment_parse_eq_output :
    parse (exampleFile "// doc\npragma foo-bar;") =
      .ok (pragmaOutput "// doc\npragma foo-bar;" commentedLexed
        (rawDeclaration 7) [docComment] []) :=
  parse_eq_ok_of_singlePragmaTrace commentLexes (rawClears 7) (rawParsed 7) rfl

end Solcore.Test.SyntaxParserPublicPragmaProtectedTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPublicPragmaSequenceExamples
/-! Ground complete outputs of two independently traced pragma declarations.
Only lexical fixtures use kernel-backed evaluation; public parsing is derived
from the independent sequence grammar, including ordered protected events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaSequenceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

private def sequenceTokens (secondOffset : Nat) : List Token := [
  pragmaToken 0, identifierToken 7 8 "p", identifierToken 9 12 "a-b", semicolonToken 12,
  pragmaToken secondOffset, identifierToken (secondOffset + 7) (secondOffset + 8) "q",
  identifierToken (secondOffset + 9) (secondOffset + 12) "c-d",
  semicolonToken (secondOffset + 12)]

private def firstDeclaration : PragmaDecl := {
  span := byteSpan 0 13
  value := {
    name := { span := byteSpan 7 8, value := "p" }
    items := [{ span := byteSpan 9 12, value := "a-b" }]
  }
}

private def secondDeclaration (offset : Nat) : PragmaDecl := {
  span := SourceSpan.cover (pragmaToken offset).span (semicolonToken (offset + 12)).span
  value := {
    name := { span := byteSpan (offset + 7) (offset + 8), value := "q" }
    items := [{ span := byteSpan (offset + 9) (offset + 12), value := "c-d" }]
  }
}

private def firstEvent : ParseDiagnostic := {
  span := byteSpan 9 12, kind := .invalidIdentifierHyphen "a-b"
}

private def secondEvent (offset : Nat) : ParseDiagnostic := {
  span := byteSpan (offset + 9) (offset + 12), kind := .invalidIdentifierHyphen "c-d"
}

private theorem firstParsed (offset : Nat) :
    PragmaDeclTraceParses (sourceFileRootRemainder (sequenceTokens offset)) firstDeclaration
      (atCursor (sequenceTokens offset) 4) [firstEvent] := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "a-b".toList; decide)) .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor (sequenceTokens offset) 1)
    (afterName := atCursor (sequenceTokens offset) 2)
    (afterItems := atCursor (sequenceTokens offset) 3) (byteSpan 0 6) (byteSpan 12 13)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor (sequenceTokens offset) 3)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, semicolonToken]
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, semicolonToken]

private theorem secondParsed (offset : Nat) :
    PragmaDeclTraceParses (atCursor (sequenceTokens offset) 4) (secondDeclaration offset)
      (atCursor (sequenceTokens offset) 8) [secondEvent offset] := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "c-d".toList; decide)) .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor (sequenceTokens offset) 5)
    (afterName := atCursor (sequenceTokens offset) 6)
    (afterItems := atCursor (sequenceTokens offset) 7)
    (pragmaToken offset).span (semicolonToken (offset + 12)).span
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor (sequenceTokens offset) 7)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, semicolonToken]
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, semicolonToken]

private theorem sequenceParsed (offset : Nat) :
    PragmaSequenceTraceParses (sourceFileRootRemainder (sequenceTokens offset))
      [firstDeclaration, secondDeclaration offset] (atCursor (sequenceTokens offset) 8)
      [firstEvent, secondEvent offset] :=
  .cons (firstParsed offset) (.cons (secondParsed offset)
    (.done (by simp [atCursor, sourceFileRootRemainder, sequenceTokens])))

private theorem sequenceClears (offset : Nat) : NestingClears (sequenceTokens offset) :=
  .preserve rfl (.preserve rfl (.preserve rfl (.reset rfl
    (.preserve rfl (.preserve rfl (.preserve rfl (.reset rfl .done)))))))

/-- Both AST nodes and both diagnostics are explicit, in written order. -/
private def sequenceOutput (content : String) (offset : Nat)
    (lexical : List LexicalDiagnostic) : ParseOutput := {
  parsed := {
    source := exampleSource
    span := SourceSpan.fullFile (exampleFile content)
    items := [
      { span := firstDeclaration.span, leadingComments := [], value := .pragmaDecl firstDeclaration },
      { span := (secondDeclaration offset).span, leadingComments := [],
        value := .pragmaDecl (secondDeclaration offset) }]
    comments := []
  }
  tokens := sequenceTokens offset
  lexicalDiagnostics := lexical
  parseDiagnostics := [firstEvent, secondEvent offset]
}

set_option maxRecDepth 8192 in
private theorem cleanLexes : Lexer.lex (exampleFile "pragma p a-b; pragma q c-d;") =
    .ok (lexicalCarrier (sequenceTokens 14) []) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- Two declarations emit one event per checked item. The first declaration's
event precedes exactly one event from the second, without duplication. -/
theorem twoPragmas_parse_eq_output :
    parse (exampleFile "pragma p a-b; pragma q c-d;") =
      .ok (sequenceOutput "pragma p a-b; pragma q c-d;" 14 []) :=
  parse_eq_ok_of_pragmaSequence cleanLexes (sequenceClears 14) (sequenceParsed 14)

private def betweenInvalid : LexicalDiagnostic := {
  span := byteSpan 14 16, kind := .invalidToken
}

set_option maxRecDepth 8192 in
private theorem diagnosedLexes : Lexer.lex (exampleFile "pragma p a-b; § pragma q c-d;") =
    .ok (lexicalCarrier (sequenceTokens 17) [betweenInvalid]) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- The lexical error between pragmas is on both events' LF line, so ordinary
expectation or recovery events at either exact span would be suppressed. -/
theorem sameLineCascadeAppliesToBoth :
    LexicalCascadeSuppresses "pragma p a-b; § pragma q c-d;"
        [betweenInvalid.span] firstEvent.span ∧
      LexicalCascadeSuppresses "pragma p a-b; § pragma q c-d;"
        [betweenInvalid.span] (secondEvent 17).span := by
  constructor
  · exact ⟨betweenInvalid.span, by simp, rfl, Or.inl (by decide)⟩
  · exact ⟨betweenInvalid.span, by simp, rfl, Or.inl (by decide)⟩

/-- A real lexical diagnostic between the declarations does not suppress or
reorder either protected checked-name event; the complete carrier is retained. -/
theorem protectedTwoPragmas_parse_eq_output :
    parse (exampleFile "pragma p a-b; § pragma q c-d;") =
      .ok (sequenceOutput "pragma p a-b; § pragma q c-d;" 17 [betweenInvalid]) :=
  parse_eq_ok_of_pragmaSequence diagnosedLexes (sequenceClears 17) (sequenceParsed 17)

/-- The validated token-to-file entry point exposes the identical complete
two-pragma AST, lexical error, and ordered protected diagnostic sequence. -/
theorem protectedTwoPragmas_parseLexed_eq_output :
    parseLexed (exampleFile "pragma p a-b; § pragma q c-d;")
        (lexicalCarrier (sequenceTokens 17) [betweenInvalid]) =
      .ok (sequenceOutput "pragma p a-b; § pragma q c-d;" 17 [betweenInvalid]) :=
  parseLexed_eq_ok_of_pragmaSequence
    ((lexedFileValidationAccepts_iff_validFor _ _).mpr (Lexer.lex_ok_validFor _ _ diagnosedLexes))
    (sequenceClears 17) (sequenceParsed 17)

end Solcore.Test.SyntaxParserPublicPragmaSequenceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPublicPragmaSuccessOutputProperties
/-! Consumers of complete pragma outputs from independent AST/trace grammar.
All reports, their order, and their multiplicity remain part of the result. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaSuccessOutputProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {file : SourceFile} {lexed : LexedFile} {declaration : PragmaDecl}
  {after : Remainder} {trace kept : List ParseDiagnostic}
  (accepted : LexedFileValidationAccepts file lexed)
  (clears : NestingClears lexed.tokens)
  (parsed : PragmaDeclTraceParses (sourceFileRootRemainder lexed.tokens)
    declaration after trace)
  (atEnd : after.cursor = lexed.tokens.length)

example (filtered : ParseDiagnosticCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) trace kept) :
    parseLexed file lexed = .ok {
      parsed := {
        source := file.id
        span := SourceSpan.fullFile file
        items := [Trivia.attachTopItemComments file lexed.comments
          (FileInternals.wrapPragma declaration)]
        comments := lexed.comments
      }
      tokens := lexed.tokens
      lexicalDiagnostics := lexed.diagnostics
      parseDiagnostics := kept
    } :=
  parseLexed_eq_ok_of_singlePragma accepted clears parsed atEnd filtered

example (result : parseLexed file lexed =
    .ok (singlePragmaParseOutput file lexed declaration kept)) :
    LexedFileValidationAccepts file lexed ∧
      ParseDiagnosticCascadeFilters file.content (lexed.diagnostics.map (·.span)) trace kept :=
  (parseLexed_eq_ok_singlePragma_iff clears parsed atEnd).mp result

example (lexing : Lexer.lex file = .ok lexed)
    (filtered : ParseDiagnosticCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) trace kept) :
    parse file = .ok (singlePragmaParseOutput file lexed declaration kept) :=
  parse_eq_ok_of_singlePragma lexing clears parsed atEnd filtered

example (lexing : Lexer.lex file = .ok lexed)
    (result : parse file = .ok (singlePragmaParseOutput file lexed declaration kept)) :
    ParseDiagnosticCascadeFilters file.content (lexed.diagnostics.map (·.span)) trace kept :=
  (parse_eq_ok_singlePragma_iff lexing clears parsed atEnd).mp result

example : parseLexed file lexed =
    .ok (singlePragmaParseOutput file lexed declaration trace) :=
  parseLexed_eq_ok_of_singlePragmaTrace accepted clears parsed atEnd

example (lexing : Lexer.lex file = .ok lexed) :
    parse file = .ok (singlePragmaParseOutput file lexed declaration trace) :=
  parse_eq_ok_of_singlePragmaTrace lexing clears parsed atEnd

example (filtered : ParseDiagnosticCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) trace kept) : kept = trace :=
  filtered.output_unique (parsed.cascadeFilters file.content (lexed.diagnostics.map (·.span)))

example {names : List Identifier} {events : List ParseDiagnostic}
    (diagnostics : IdentifierListDiagnosticTrace names events)
    (source : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters source lexical events events :=
  diagnostics.cascadeFilters source lexical

end Solcore.Test.SyntaxParserPublicPragmaSuccessOutputProperties
end
