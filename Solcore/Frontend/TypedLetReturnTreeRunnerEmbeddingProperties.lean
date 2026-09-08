import Solcore.Frontend.TypedLetReturnTreeRunner
import Solcore.Frontend.TypedLetReturnTreeEmbeddingProperties
import Solcore.Frontend.TypedLetReturnBodyRunner
import Solcore.Frontend.TerminalReturnTreeRunner

/-! Singleton returns retain rejection and complete same-fuel results. Other
old profiles embed successful full results only: branch-local lets add success,
so arbitrary old and new optional results are not identified. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem runTypedLetReturnTree?_single
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId) (fuel : Nat)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) (store : Core.Store) :
    inputs.runTypedLetReturnTree? types owner fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store =
      inputs.runReturnBody? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store := by
  simp only [runTypedLetReturnTree?, checkTypedLetReturnTree?, runReturnBody?, checkReturnBody?,
    elaborateTypedLetReturnTree?_single, toTypeInputs_names, toTypeInputs_context]

theorem runTypedLetReturnTree?_some_of_terminalReturnTree
    {inputs : LocalInputs} {body : Syntax.Block} {fuel : Nat} {store : Core.Store}
    {type : Core.Ty} {result : Core.StatefulRunResult}
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (accepted : inputs.runTerminalReturnTree? fuel body store = some (type, result)) :
    inputs.runTypedLetReturnTree? types owner fuel body store = some (type, result) := by
  cases checked : inputs.checkTerminalReturnTree? body with
  | none => simp [runTerminalReturnTree?, checked] at accepted
  | some pair =>
      obtain ⟨core, checkedType⟩ := pair
      have oldChecked : elaborateTerminalReturnTree? inputs.toTypeInputs.names inputs.toTypeInputs.context body =
          some (core, checkedType) := by
        simpa only [checkTerminalReturnTree?, toTypeInputs_names, toTypeInputs_context] using checked
      have preserved : inputs.checkTypedLetReturnTree? types owner body = some (core, checkedType) :=
        elaborateTypedLetReturnTree?_some_of_terminalReturnTree types owner oldChecked
      simpa only [runTypedLetReturnTree?, runTerminalReturnTree?, checked, preserved] using accepted

theorem runTypedLetReturnTree?_some_of_typedLetReturnBody
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {body : Syntax.Block} {fuel : Nat} {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult}
    (accepted : inputs.runTypedLetReturnBody? types owner fuel body store = some (type, result)) :
    inputs.runTypedLetReturnTree? types owner fuel body store = some (type, result) := by
  cases checked : inputs.checkTypedLetReturnBody? types owner body with
  | none => simp [runTypedLetReturnBody?, checked] at accepted
  | some pair =>
      obtain ⟨core, checkedType⟩ := pair
      have preserved : inputs.checkTypedLetReturnTree? types owner body = some (core, checkedType) :=
        elaborateTypedLetReturnTree?_some_of_typedLetReturnBody checked
      simpa only [runTypedLetReturnTree?, runTypedLetReturnBody?, checked, preserved] using accepted

end Solcore.Frontend.LocalInputs
