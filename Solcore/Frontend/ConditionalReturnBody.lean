import Solcore.Frontend.ReturnBodyElaboration

/-! A separate, nonrecursive adapter for one terminal if/else statement.
Both arms use the existing singleton-return adapter under the original inputs.
This does not extend function compilation or implement general early returns. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Retain the exact condition and both checked arms; neither an absent else
nor surrounding statements are discarded. -/
def elaborateConditionalReturnBody? (table : LocalNameTable) (context : Resolved.Context)
    (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body.value with
  | [⟨_, .ifThen condition thenBody (some elseBody)⟩] => do
      let (conditionCore, conditionType) ← elaborateLocalExpression? table context condition
      if conditionType = .bool then do
        let (thenCore, thenType) ← elaborateReturnBody? table context thenBody
        let (elseCore, elseType) ← elaborateReturnBody? table context elseBody
        if thenType = elseType then
          return (.ifE conditionCore thenCore elseCore, thenType)
        else none
      else none
  | _ => none

inductive ConditionalReturnBodyHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Ty → Prop where
  | intro {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {type : Core.Ty}
      (conditionTyping : LocalExpressionHasType table context condition .bool)
      (thenTyping : ReturnBodyHasType table context thenBody type)
      (elseTyping : ReturnBodyHasType table context elseBody type) :
      ConditionalReturnBodyHasType table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ type

/-- Exact elaboration is independent of the executable checker and retains
condition resolution, positional lowering, and both original arm elaborations. -/
inductive ConditionalReturnBodyElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Expr → Core.Ty → Prop where
  | intro {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {conditionResolved : Resolved.Expr}
      {conditionCore thenCore elseCore : Core.Expr} {type : Core.Ty}
      (conditionResolution : ResolvesLocalExpression table condition conditionResolved)
      (conditionLowered : Resolved.Lowers (Resolved.LocalScope.ids context) conditionResolved conditionCore)
      (conditionTyping : Resolved.HasType context conditionResolved .bool)
      (thenElaboration : ReturnBodyElaborates table context thenBody thenCore type)
      (elseElaboration : ReturnBodyElaborates table context elseBody elseCore type) :
      ConditionalReturnBodyElaborates table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        (.ifE conditionCore thenCore elseCore) type

namespace LocalInputs

def checkConditionalReturnBody? (inputs : LocalInputs) (body : Syntax.Block) :
    Option (Core.Expr × Core.Ty) :=
  elaborateConditionalReturnBody? inputs.names inputs.context body

/-- Execute only the actual checked Core using the actual ordered values.
Exhaustion remains a present result with its original suspended state. -/
def runConditionalReturnBody? (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block)
    (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkConditionalReturnBody? body
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end LocalInputs

end Solcore.Frontend
