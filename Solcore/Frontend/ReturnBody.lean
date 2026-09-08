import Solcore.Frontend.LocalInputsExecution
import Solcore.Frontend.LocalExpressionCost

/-! Exactly one canonical return statement. These wrappers add no Core
operation and do not model general early return or function invocation. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- A singleton bare return yields Unit; an expression return keeps the actual
checked expression. No surrounding or unreachable statement is discarded. -/
def elaborateReturnBody? (table : LocalNameTable) (context : Resolved.Context)
    (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body.value with
  | [⟨_, .returnStmt none⟩] => some (.unit, .unit)
  | [⟨_, .returnStmt (some source)⟩] => elaborateLocalExpression? table context source
  | _ => none

inductive ReturnBodyHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Ty → Prop where
  | bare {blockSpan returnSpan : Syntax.SourceSpan} :
      ReturnBodyHasType table context ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit
  | expression {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr} {type : Core.Ty}
      (child : LocalExpressionHasType table context source type) :
      ReturnBodyHasType table context
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ type

inductive ReturnBodyEvaluates (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | bare {blockSpan returnSpan : Syntax.SourceSpan} {store : Core.Store} :
      ReturnBodyEvaluates table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store
  | expression {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : LocalExpressionEvaluates table environment initialStore source value finalStore) :
      ReturnBodyEvaluates table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore

/-- Costs count the compiled expression's Core transitions, not source control
handling. Expression returns retain the child's exact cost and both stores. -/
inductive ReturnBodyEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | bare {blockSpan returnSpan : Syntax.SourceSpan} {store : Core.Store} :
      ReturnBodyEvaluatesWithCost table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store 1
  | expression {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost) :
      ReturnBodyEvaluatesWithCost table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore cost

namespace LocalInputs

def checkReturnBody? (inputs : LocalInputs) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  elaborateReturnBody? inputs.names inputs.context body

/-- Only execute the actual checked Core; present fuel exhaustion remains a
present result. Caller/store invariants are those of existing typed inputs. -/
def runReturnBody? (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkReturnBody? body
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end LocalInputs

end Solcore.Frontend
