import Solcore.Frontend.LocalExpressionTyping

/-! An opt-in root application of a known single-argument Function. Both
original children use the old pure local profile. This does not extend that
profile, resolve general Invokable instances or integrate function entries. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Preserve the unique argument as written, without packing or an implicit
Unit. Failure is outside this adapter, not rejection by the full language. -/
def elaborateLocalFunctionApplication? (table : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source.value with
  | .call callee ⟨_, [argument]⟩ => do
      let (functionCore, functionType) ← elaborateLocalExpression? table context callee
      let (argumentCore, argumentType) ← elaborateLocalExpression? table context argument
      match functionType with
      | .function parameterType resultType =>
          if argumentType = parameterType then
            some (.apply functionCore argumentCore, resultType)
          else none
      | _ => none
  | _ => none

/-- Whole static typing checks both original children in the same scope. -/
inductive LocalFunctionApplicationHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Ty → Prop where
  | call {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {parameterType resultType : Core.Ty}
      (functionTyped : LocalExpressionHasType table context callee (.function parameterType resultType))
      (argumentTyped : LocalExpressionHasType table context argument parameterType) :
      LocalFunctionApplicationHasType table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ resultType

/-- Exact provenance fixes both resolved children and their positional Core,
separately from their types. No runtime values or executable checks are premises. -/
inductive LocalFunctionApplicationElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | call {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {resolvedFunction resolvedArgument : Resolved.Expr} {functionCore argumentCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (functionResolution : ResolvesLocalExpression table callee resolvedFunction)
      (functionLowered : Resolved.Lowers (Resolved.LocalScope.ids context) resolvedFunction functionCore)
      (functionTyped : Resolved.HasType context resolvedFunction (.function parameterType resultType))
      (argumentResolution : ResolvesLocalExpression table argument resolvedArgument)
      (argumentLowered : Resolved.Lowers (Resolved.LocalScope.ids context) resolvedArgument argumentCore)
      (argumentTyped : Resolved.HasType context resolvedArgument parameterType) :
      LocalFunctionApplicationElaborates table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ (.apply functionCore argumentCore) resultType

end Solcore.Frontend
