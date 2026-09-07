import Solcore.Syntax.DeclarativeTypeDispatchTraceGrammar

/-! Fuel-free recursive type traces are the least simultaneous fixed point of
the independent selected layer. Success and rejection share one query domain;
the definition quantifies over closed relations, not executable parsers. It
asserts neither existence of an outcome nor an execution resource bound. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive TypeTraceQuery where
  | success (source : SourceId) (endByte : Nat) (input : Remainder)
      (value : Syntax.TypeExpr) (output : Remainder) (trace : List ParseDiagnostic)
  | rejection (source : SourceId) (endByte : Nat) (input rejected : Remainder)
      (report : ParseDiagnostic) (trace : List ParseDiagnostic)

def TypeTraceLayer (candidate : TypeTraceQuery → Prop) : TypeTraceQuery → Prop
  | .success source endByte input value output trace =>
      TypeDispatchTraceParses (fun source endByte input value output trace =>
        candidate (.success source endByte input value output trace))
        source endByte input value output trace
  | .rejection source endByte input rejected report trace =>
      TypeDispatchTraceRejects (fun source endByte input value output trace =>
        candidate (.success source endByte input value output trace))
        (fun source endByte input rejected report trace =>
          candidate (.rejection source endByte input rejected report trace))
        source endByte input rejected report trace

def TypeTraceLeast (query : TypeTraceQuery) : Prop :=
  ∀ candidate : TypeTraceQuery → Prop,
    (∀ query, TypeTraceLayer candidate query → candidate query) → candidate query

def TypeExprTraceParses (source : SourceId) (endByte : Nat) (input : Remainder)
    (value : Syntax.TypeExpr) (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  TypeTraceLeast (.success source endByte input value output trace)

def TypeExprTraceRejects (source : SourceId) (endByte : Nat) (input rejected : Remainder)
    (report : ParseDiagnostic) (trace : List ParseDiagnostic) : Prop :=
  TypeTraceLeast (.rejection source endByte input rejected report trace)

end Solcore.Syntax.DeclarativeGrammar
