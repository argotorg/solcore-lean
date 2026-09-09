import Solcore.Frontend.LocalInputsApplication
import Solcore.Frontend.LocalFunctionApplicationEvaluation

/-! A separate original singleton return whose child is a local application.
The return retains its child's exact Core and costs without a new control frame.
Existing pure-expression and whole-function endpoints are unchanged. -/

set_option autoImplicit false

namespace Solcore.Frontend

def elaborateLocalApplicationReturnBody? (table : LocalNameTable) (context : Resolved.Context)
    (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body.value with
  | [⟨_, .returnStmt (some source)⟩] => elaborateLocalFunctionApplication? table context source
  | _ => none

inductive LocalApplicationReturnBodyHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Ty → Prop where
  | application {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr} {type : Core.Ty}
      (child : LocalFunctionApplicationHasType table context source type) :
      LocalApplicationReturnBodyHasType table context
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ type

inductive LocalApplicationReturnBodyElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Expr → Core.Ty → Prop where
  | application {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {core : Core.Expr} {type : Core.Ty}
      (child : LocalFunctionApplicationElaborates table context source core type) :
      LocalApplicationReturnBodyElaborates table context
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ core type

inductive LocalApplicationReturnBodyEvaluates (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | application {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : LocalFunctionApplicationEvaluates table environment initialStore source value finalStore) :
      LocalApplicationReturnBodyEvaluates table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore

inductive LocalApplicationReturnBodyEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | application {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : LocalFunctionApplicationEvaluatesWithCost table environment
        initialStore source value finalStore cost) :
      LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore cost

namespace LocalInputs

def checkApplicationReturnBody? (inputs : LocalInputs) (body : Syntax.Block) :
    Option (Core.Expr × Core.Ty) :=
  elaborateLocalApplicationReturnBody? inputs.names inputs.context body

/-- Preserve every checked outcome using the same actual values and store.
The input record alone does not validate allocated cells or their payloads. -/
def runApplicationReturnBody? (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkApplicationReturnBody? body
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end LocalInputs

end Solcore.Frontend
