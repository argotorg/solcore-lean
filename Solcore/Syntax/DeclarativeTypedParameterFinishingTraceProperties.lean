import Solcore.Syntax.DeclarativeTypedParameterFinishingTraceGrammar
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Parameter finishing always has exactly one complete trace, including the
empty trace on allowed types. Constraint events are protected independently
of source validity and lexical errors at the same locations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem typedParameterFinishingTrace_exists (type : Syntax.TypeExpr) :
    ∃ trace, TypedParameterFinishingTrace type trace := by
  by_cases allowed : ParameterTypeAllowed type
  · exact ⟨[], .ordinary allowed⟩
  · exact ⟨_, .comptime allowed⟩

theorem TypedParameterFinishingTrace.trace_unique {type : Syntax.TypeExpr}
    {left right : List ParseDiagnostic}
    (leftTrace : TypedParameterFinishingTrace type left)
    (rightTrace : TypedParameterFinishingTrace type right) : left = right := by
  cases leftTrace <;> cases rightTrace <;> first | rfl | contradiction

theorem TypedParameterFinishingTrace.nil_iff {type : Syntax.TypeExpr} :
    TypedParameterFinishingTrace type [] ↔ ParameterTypeAllowed type := by
  constructor
  · intro trace; cases trace with | ordinary allowed => exact allowed
  · exact .ordinary

theorem TypedParameterFinishingTrace.comptime_iff {type : Syntax.TypeExpr} :
    TypedParameterFinishingTrace type [{
      span := type.span, kind := .constraintViolation .comptimeTypeInParameter
    }] ↔ ¬ ParameterTypeAllowed type := by
  constructor
  · intro trace; cases trace with | comptime forbidden => exact forbidden
  · exact .comptime

theorem TypedParameterFinishingTrace.cascadeFilters {type : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (events : TypedParameterFinishingTrace type trace) (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases events with
  | ordinary => exact .nil
  | comptime => exact parseDiagnosticCascadeFilters_protected_cons (by simp [LexicalCascadeCandidate]) .nil

theorem errorParameterFinishingTrace_exists (span : SourceSpan) (constraint : ParseConstraint) :
    ∃ trace, ErrorParameterFinishingTrace span constraint trace := ⟨_, .emitted⟩

theorem ErrorParameterFinishingTrace.trace_eq {span : SourceSpan} {constraint : ParseConstraint}
    {trace : List ParseDiagnostic} (events : ErrorParameterFinishingTrace span constraint trace) :
    trace = [{ span, kind := .constraintViolation constraint }] := by cases events; rfl

theorem ErrorParameterFinishingTrace.trace_unique {span : SourceSpan} {constraint : ParseConstraint}
    {left right : List ParseDiagnostic}
    (leftTrace : ErrorParameterFinishingTrace span constraint left)
    (rightTrace : ErrorParameterFinishingTrace span constraint right) : left = right :=
  leftTrace.trace_eq.trans rightTrace.trace_eq.symm

theorem ErrorParameterFinishingTrace.cascadeFilters {span : SourceSpan} {constraint : ParseConstraint}
    {trace : List ParseDiagnostic} (events : ErrorParameterFinishingTrace span constraint trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases events
  exact parseDiagnosticCascadeFilters_protected_cons (by simp [LexicalCascadeCandidate]) .nil

end Solcore.Syntax.DeclarativeGrammar
