import Solcore.Syntax.Parser.NamedParameterTailTraceStateProperties

/-! Every ordinary raw function/lambda parameter reply preserves the complete
input source file. Diagnostic-producing finishers and retagging do not alter
that source. Recovery loops and public recovering wrappers are not covered. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FunctionParameterInternals

theorem finishTypedParameter_preservesFile (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) :
    Parser.PreservesFile (finishTypedParameter start marker name type) := by
  intro input
  rcases DeclarativeGrammar.typedParameterFinishingTrace_exists type with ⟨trace, events⟩
  rw [finishTypedParameter_eq_ok_of_trace start marker name type input events]
  rfl

theorem errorParameter_preservesFile (span : SourceSpan) (constraint : ParseConstraint) :
    Parser.PreservesFile (errorParameter span constraint) := by
  intro input
  rw [errorParameter_eq_ok_of_trace span constraint input .emitted]
  rfl

theorem ordinaryNamedParameter_preservesFile : Parser.PreservesFile ordinaryNamedParameter := by
  unfold ordinaryNamedParameter
  apply Parser.bind_preservesFile (identifier_preservesFile .parameter)
  intro name
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true]
    apply Parser.bind_preservesFile (emitDiagnostic_preservesFile _)
    intro ignored
    exact namedParameterTail_preservesFile name.span none name name.span
  · simp only [warned, Bool.false_eq_true, if_false]
    exact namedParameterTail_preservesFile name.span none name name.span

theorem comptimeNamedParameter_preservesFile : Parser.PreservesFile comptimeNamedParameter := by
  unfold comptimeNamedParameter
  apply Parser.bind_preservesFile (contextual_preservesFile .comptime .parameter)
  intro marker
  apply Parser.bind_preservesFile (identifier_preservesFile .parameter)
  intro name
  exact namedParameterTail_preservesFile marker.span (some marker.span) name
    (SourceSpan.cover marker.span name.span)

theorem namedParameterCore_preservesFile : Parser.PreservesFile namedParameterCore := by
  intro input
  unfold namedParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeNamedParameter_preservesFile input
    · exact ordinaryNamedParameter_preservesFile input
  · simpa only [Bool.and_false, Bool.false_eq_true, if_false] using ordinaryNamedParameter_preservesFile input

end FunctionParameterInternals

namespace LambdaParameterInternals

theorem ofFunctionParameter_bind_preservesFile {parser : Parser FunctionParameter}
    (preserved : Parser.PreservesFile parser) :
    Parser.PreservesFile (parser >>= fun parameter => pure (ofFunctionParameter parameter)) :=
  Parser.bind_preservesFile preserved (fun _ => Parser.pure_preservesFile _)

theorem ordinaryLambdaParameterTail_preservesFile (name : Identifier) :
    Parser.PreservesFile (ordinaryLambdaParameterTail name) := by
  unfold ordinaryLambdaParameterTail
  apply Parser.bind_preservesFile getState_preservesFile
  intro observed
  split
  · exact ofFunctionParameter_bind_preservesFile
      (FunctionParameterInternals.namedParameterTail_preservesFile name.span none name name.span)
  · exact Parser.pure_preservesFile _

theorem comptimeLambdaParameterTail_preservesFile (marker : Token) (name : Identifier) :
    Parser.PreservesFile (comptimeLambdaParameterTail marker name) := by
  unfold comptimeLambdaParameterTail
  apply Parser.bind_preservesFile getState_preservesFile
  intro observed
  split
  · exact ofFunctionParameter_bind_preservesFile
      (FunctionParameterInternals.namedParameterTail_preservesFile marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span))
  · exact ofFunctionParameter_bind_preservesFile
      (FunctionParameterInternals.errorParameter_preservesFile
        (SourceSpan.cover marker.span name.span) .comptimeParameterRequiresType)

theorem ordinaryLambdaParameter_preservesFile : Parser.PreservesFile ordinaryLambdaParameter := by
  unfold ordinaryLambdaParameter
  apply Parser.bind_preservesFile (identifier_preservesFile .parameter)
  intro name
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true]
    apply Parser.bind_preservesFile (emitDiagnostic_preservesFile _)
    intro ignored
    exact ordinaryLambdaParameterTail_preservesFile name
  · simp only [warned, Bool.false_eq_true, if_false]
    exact ordinaryLambdaParameterTail_preservesFile name

theorem comptimeLambdaParameter_preservesFile : Parser.PreservesFile comptimeLambdaParameter := by
  unfold comptimeLambdaParameter
  apply Parser.bind_preservesFile (contextual_preservesFile .comptime .parameter)
  intro marker
  apply Parser.bind_preservesFile (identifier_preservesFile .parameter)
  intro name
  exact comptimeLambdaParameterTail_preservesFile marker name

theorem lambdaParameterCore_preservesFile : Parser.PreservesFile lambdaParameterCore := by
  intro input
  unfold lambdaParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeLambdaParameter_preservesFile input
    · exact ordinaryLambdaParameter_preservesFile input
  · simpa only [Bool.and_false, Bool.false_eq_true, if_false] using ordinaryLambdaParameter_preservesFile input

end LambdaParameterInternals

end Solcore.Syntax.Parser
