import Solcore.SourceSemantics.CoreLowering.BuiltinNamedCallMeaning
import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! Packed values do not determine argument count: unit can mean no arguments
or one unit argument, and a product can be one argument or several. A direct
packed call preserves a Source trace only at the actual callable's arity. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursivePublicCallableArity
open Frontend SourceInference

inductive Arity (program : Program) : Dynamic.Value → Nat → Prop where
  | closure (function : Dynamic.Closure) : Arity program (.closure function) function.parameters.length
  | global {function : Dynamic.GlobalFunction} {body : Dynamic.BodyInstance}
      (instantiates : Dynamic.FunctionInstantiates program function.instantiation body) :
      Arity program (.global function) body.source.inputs.length
  | builtin (function : Dynamic.BuiltinFunction) :
      Arity program (.builtin function) function.id.parameterTypes.length

theorem Arity.closure_count {program : Program} {function : Dynamic.Closure} {count : Nat}
    (arity : Arity program (.closure function) count) : function.parameters.length = count := by
  cases arity
  rfl

theorem Arity.builtin_count {program : Program} {function : Dynamic.BuiltinFunction} {count : Nat}
    (arity : Arity program (.builtin function) count) : function.id.parameterTypes.length = count := by
  cases arity
  rfl

theorem Arity.global_count {program : Program} {function : Dynamic.GlobalFunction} {count : Nat}
    (arity : Arity program (.global function) count) (wellFormed : ProgramWellFormed program)
    {body : Dynamic.BodyInstance}
    (actual : Dynamic.FunctionInstantiates program function.instantiation body) :
    body.source.inputs.length = count := by
  cases arity with
  | global instantiates =>
    cases BuiltinNamedCalls.instantiation_unique_of_wellFormed wellFormed actual instantiates
    rfl

/-- Successful Source application itself fixes the argument count. Faults do
not: an arity mismatch is a Source result at a different unpacking. -/
theorem Arity.of_value {program : Program} {registry : Staging.Recursive.Registry}
    {size : Nat} {scope : Staging.Recursive.Scope} {context : Context}
    {before after : Dynamic.Heap} {function result : Dynamic.Value} {arguments : List Dynamic.Value}
    (trace : Staging.Recursive.Size.Applies program registry size scope context before function arguments
      (.value result) after) : Arity program function arguments.length := by
  cases trace with
  | builtin applied =>
    have arity := (applied.preserves (context := context) (heap := before)).1.length_eq
    exact arity ▸ .builtin _
  | global instantiates _ _ _ _ allocate _ _ =>
    exact allocate.length_eq ▸ .global instantiates
  | closure _ _ _ allocate _ _ =>
    exact allocate.length_eq ▸ .closure _

end Solcore.SourceSemantics.CoreLowering.RecursivePublicCallableArity
