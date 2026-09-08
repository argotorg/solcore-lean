import Solcore.Frontend.ConditionalReturnBody

/-! A nonrecursive body-only union of singleton returns and terminal if/else.
The original adapters retain their contracts; the union adds no Core operation.
Conditional arms remain singleton returns, not recursive terminal bodies. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Dispatch by original whole-body shape, retaining exact successful Core and
type results. Unsupported or malformed children receive no fallback meaning. -/
def elaborateTerminalReturnBody? (table : LocalNameTable) (context : Resolved.Context)
    (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body.value with
  | [⟨_, .returnStmt _⟩] => elaborateReturnBody? table context body
  | [⟨_, .ifThen _ _ (some _)⟩] => elaborateConditionalReturnBody? table context body
  | _ => none

inductive TerminalReturnBodyHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Ty → Prop where
  | single {body : Syntax.Block} {type : Core.Ty}
      (child : ReturnBodyHasType table context body type) :
      TerminalReturnBodyHasType table context body type
  | conditional {body : Syntax.Block} {type : Core.Ty}
      (child : ConditionalReturnBodyHasType table context body type) :
      TerminalReturnBodyHasType table context body type

inductive TerminalReturnBodyElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Expr → Core.Ty → Prop where
  | single {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
      (child : ReturnBodyElaborates table context body core type) :
      TerminalReturnBodyElaborates table context body core type
  | conditional {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
      (child : ConditionalReturnBodyElaborates table context body core type) :
      TerminalReturnBodyElaborates table context body core type

namespace LocalInputs

def checkTerminalReturnBody? (inputs : LocalInputs) (body : Syntax.Block) :
    Option (Core.Expr × Core.Ty) :=
  elaborateTerminalReturnBody? inputs.names inputs.context body

/-- Execute the retained checked Core with the original ordered runtime values;
fuel exhaustion remains a present machine result. -/
def runTerminalReturnBody? (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block)
    (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkTerminalReturnBody? body
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end LocalInputs

end Solcore.Frontend
