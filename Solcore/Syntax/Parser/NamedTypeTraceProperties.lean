import Solcore.Syntax.DeclarativeNamedTypeTraceProperties
import Solcore.Syntax.Parser.QualifiedNameTraceCorrespondenceProperties
import Solcore.Syntax.Parser.NamedTypeArgumentsTraceProperties
import Solcore.Syntax.Parser.NamedTypeFinishingTraceProperties

/-! Raw named-type execution retains exact AST, remainder, and three ordered
diagnostic suffixes. Recursive argument children need only explicit success
and source/full-window contracts. Type-dispatch priority is not assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem named_bind_ok_parts {α β : Type} {first : Parser α} {next : α → Parser β}
    {input output : State} {value : β} (result : (first >>= next) input = .ok value output) :
    ∃ item after, first input = .ok item after ∧ next item after = .ok value output := by
  cases firstResult : first input <;> simp only [bind, firstResult] at result
  case ok item after => exact ⟨item, after, rfl, result⟩
  case reject => contradiction
  case invariant => contradiction

theorem parseNamedType_success_iff_components {input output : State} {value : TypeExpr} :
    parseNamedType nested input = .ok value output ↔
    ∃ name afterName arguments afterArguments,
      qualifiedName .typeExpr .typeExpr input = .ok name afterName ∧
      parseNamedTypeArguments nested afterName = .ok arguments afterArguments ∧
      finishNamedType name arguments afterArguments = .ok value output := by
  constructor
  · intro result
    unfold parseNamedType at result
    rcases named_bind_ok_parts result with ⟨name, afterName, nameResult, rest⟩
    rcases named_bind_ok_parts rest with ⟨arguments, afterArguments, argumentsResult, finished⟩
    exact ⟨name, afterName, arguments, afterArguments, nameResult, argumentsResult, finished⟩
  · rintro ⟨name, afterName, arguments, afterArguments, nameResult, argumentsResult, finished⟩
    simpa only [parseNamedType, bind, nameResult, argumentsResult] using finished

theorem parseNamedType_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessSound (parseNamedType nested) (DeclarativeGrammar.NamedTypeTraceParses elementTrace) := by
  intro input output value result
  rcases parseNamedType_success_iff_components.mp result with
    ⟨name, afterName, arguments, afterArguments, nameResult, argumentsResult, finishedResult⟩
  rcases qualifiedName_trace_success_sound .typeExpr .typeExpr nameResult with ⟨nameEvents, nameParsed, nameEq⟩
  have nameFrame := qualifiedName_success_context .typeExpr .typeExpr nameResult
  rcases parseNamedTypeArguments_trace_success_sound successSound contextFrame argumentsResult with
    ⟨argumentEvents, argumentsParsed, argumentsEq⟩
  rcases finishNamedType_success_trace_sound name arguments finishedResult with
    ⟨finishingEvents, finished, valueEq, stateEq⟩
  refine ⟨nameEvents ++ argumentEvents ++ finishingEvents, ?_, ?_⟩
  · rw [valueEq, stateEq]
    exact .parsed nameParsed (by simpa only [nameFrame.1, nameFrame.2, State.declarativeRemainder]
      using argumentsParsed) finished
  · rw [stateEq]
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]
    change afterArguments.diagnostics ++ finishingEvents = input.diagnostics ++ _
    rw [argumentsEq, nameEq]
    simp only [List.append_assoc]

theorem parseNamedType_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessComplete (parseNamedType nested) (DeclarativeGrammar.NamedTypeTraceParses elementTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed nameParsed argumentsParsed finished =>
      rename_i afterName name arguments nameEvents argumentEvents finishingEvents
      rcases qualifiedName_trace_success_complete .typeExpr .typeExpr nameParsed with
        ⟨next, nameResult, afterEq, nameEq⟩
      have frame := qualifiedName_success_context .typeExpr .typeExpr nameResult
      have argumentsAtNext : DeclarativeGrammar.NamedTypeArgumentsTraceParses elementTrace
          next.file.id next.window.endByte next.declarativeRemainder arguments after argumentEvents := by
        simpa only [frame.1, frame.2, afterEq] using argumentsParsed
      rcases parseNamedTypeArguments_trace_success_complete successComplete contextFrame argumentsAtNext with
        ⟨afterArguments, argumentsResult, finalEq, argumentsEq⟩
      rcases (finishNamedType_trace_success_iff name arguments (input := afterArguments)).mp finished with
        ⟨output, finishedResult, outputEq, eventsEq⟩
      refine ⟨output, parseNamedType_success_iff_components.mpr
        ⟨name, next, arguments, afterArguments, nameResult, argumentsResult, finishedResult⟩,
        outputEq.trans finalEq, ?_⟩
      rw [eventsEq, argumentsEq, nameEq]
      simp only [List.append_assoc]

theorem parseNamedType_success_context
    (contextFrame : ParserSuccessContext nested) : ParserSuccessContext (parseNamedType nested) := by
  intro input output value result
  rcases parseNamedType_success_iff_components.mp result with
    ⟨name, afterName, arguments, afterArguments, nameResult, argumentsResult, finishedResult⟩
  have first := qualifiedName_success_context .typeExpr .typeExpr nameResult
  have middle := parseNamedTypeArguments_success_context contextFrame argumentsResult
  have last := finishNamedType_success_context name arguments finishedResult
  exact ⟨last.1.trans (middle.1.trans first.1), last.2.trans (middle.2.trans first.2)⟩

theorem parseNamedType_trace_success_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {value : TypeExpr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NamedTypeTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, parseNamedType nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseNamedType_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parseNamedType_trace_success_sound successSound contextFrame result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser
