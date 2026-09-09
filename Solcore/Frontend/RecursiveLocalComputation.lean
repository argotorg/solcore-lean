import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.DirectWordBinary

/-! Recursive single-argument calls, groups and direct Word binary operators.
Original children keep their scope; this does not change the older profiles. -/

set_option autoImplicit false

namespace Solcore.Frontend

def elaborateRecursiveLocalComputation? (table : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [argument]⟩⟩ => do
      let (functionCore, functionType) ← elaborateRecursiveLocalComputation? table context callee
      let (argumentCore, argumentType) ← elaborateRecursiveLocalComputation? table context argument
      match functionType with
      | .function parameterType resultType =>
          if argumentType = parameterType then
            some (.apply functionCore argumentCore, resultType)
          else none
      | _ => none
  | ⟨_, .group inner⟩ => elaborateRecursiveLocalComputation? table context inner
  | ⟨_, .binary left ⟨_, sourceOp⟩ right⟩ =>
      match directWordBinary? sourceOp with
      | some op => do
          let (leftCore, leftType) ← elaborateRecursiveLocalComputation? table context left
          let (rightCore, rightType) ← elaborateRecursiveLocalComputation? table context right
          if leftType = op.leftType ∧ rightType = op.rightType then
            some (.binary op leftCore rightCore, op.resultType)
          else none
      | none => elaborateLocalExpression? table context source
  | _ => elaborateLocalExpression? table context source
termination_by sizeOf source

inductive RecursiveLocalComputationHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Ty → Prop where
  | pure {source : Syntax.Expr} {type : Core.Ty}
      (child : LocalExpressionHasType table context source type) :
      RecursiveLocalComputationHasType table context source type
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr} {type : Core.Ty}
      (child : RecursiveLocalComputationHasType table context inner type) :
      RecursiveLocalComputationHasType table context ⟨span, .group inner⟩ type
  | application {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {parameterType resultType : Core.Ty}
      (functionTyped : RecursiveLocalComputationHasType table context callee (.function parameterType resultType))
      (argumentTyped : RecursiveLocalComputationHasType table context argument parameterType) :
      RecursiveLocalComputationHasType table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ resultType

  | binary {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
      (operator : DirectWordBinary sourceOp op)
      (leftTyped : RecursiveLocalComputationHasType table context left op.leftType)
      (rightTyped : RecursiveLocalComputationHasType table context right op.rightType) :
      RecursiveLocalComputationHasType table context
        ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ op.resultType

inductive RecursiveLocalComputationElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | pure {source : Syntax.Expr} {resolved : Resolved.Expr} {core : Core.Expr} {type : Core.Ty}
      (resolution : ResolvesLocalExpression table source resolved)
      (lowered : Resolved.Lowers context.ids resolved core)
      (typing : Resolved.HasType context resolved type) :
      RecursiveLocalComputationElaborates table context source core type
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (child : RecursiveLocalComputationElaborates table context inner core type) :
      RecursiveLocalComputationElaborates table context ⟨span, .group inner⟩ core type
  | application {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {functionCore argumentCore : Core.Expr} {parameterType resultType : Core.Ty}
      (functionElaborated : RecursiveLocalComputationElaborates table context
        callee functionCore (.function parameterType resultType))
      (argumentElaborated : RecursiveLocalComputationElaborates table context argument argumentCore parameterType) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ (.apply functionCore argumentCore) resultType

  | binary {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} {leftCore rightCore : Core.Expr}
      (operator : DirectWordBinary sourceOp op)
      (leftElaborated : RecursiveLocalComputationElaborates table context left leftCore op.leftType)
      (rightElaborated : RecursiveLocalComputationElaborates table context right rightCore op.rightType) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ (.binary op leftCore rightCore) op.resultType

end Solcore.Frontend
