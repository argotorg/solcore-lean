import Solcore.Syntax.DeclarativeCoreLambdaGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Independent parameter-finishing events and exact constructed values.
The already parsed type is retained, but its own events are not replayed.
Only an outer comptime type contributes the parameter-specific diagnostic. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def typedParameterTraceValue (start : SourceSpan) (marker : Option SourceSpan)
    (name : Syntax.Identifier) (type : Syntax.TypeExpr) : Syntax.FunctionParameter := {
  span := SourceSpan.cover start type.span, value := .typed marker name type
}

inductive TypedParameterFinishingTrace (type : Syntax.TypeExpr) : List ParseDiagnostic → Prop where
  | ordinary (allowed : ParameterTypeAllowed type) : TypedParameterFinishingTrace type []
  | comptime (forbidden : ¬ ParameterTypeAllowed type) :
      TypedParameterFinishingTrace type [{
        span := type.span, kind := .constraintViolation .comptimeTypeInParameter
      }]

def errorParameterTraceValue (span : SourceSpan) : Syntax.FunctionParameter :=
  { span, value := .error }

inductive ErrorParameterFinishingTrace (span : SourceSpan) (constraint : ParseConstraint) :
    List ParseDiagnostic → Prop where
  | emitted : ErrorParameterFinishingTrace span constraint [{ span, kind := .constraintViolation constraint }]

end Solcore.Syntax.DeclarativeGrammar
