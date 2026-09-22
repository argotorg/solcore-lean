import Solcore.Frontend.SourceCompiler

/-! Small interface laws for the restricted public source compiler. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCompiler

@[simp] theorem Invocation.coreFresh_kind (arguments : List Core.Value) :
    (Invocation.coreFresh arguments).kind = .coreValues := by
  rfl

@[simp] theorem Invocation.typedFresh_kind
    (arguments : List SourceTypedRuntime.Value) :
    (Invocation.typedFresh arguments).kind = .typedValues := by
  rfl

theorem CompiledEntry.runCore_eq_run (compiled : CompiledEntry)
    (arguments : List Core.Value) (options : RunOptions) (store : Core.Store) :
    compiled.runCore arguments options store =
      compiled.run (.coreValues arguments store) options := by
  rfl

theorem CompiledEntry.runTyped_eq_run (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions)
    (state : SourceTypedRuntime.RuntimeState) :
    compiled.runTyped arguments options state =
      compiled.run (.typedValues arguments state) options := by
  rfl

theorem run_of_compiled (raw : Workspace.RawWorkspace) (seed : Seed)
    (invocation : Invocation) (limits : Limits) (compiled : CompiledEntry)
    (compiledOk : compile raw seed limits.toCheckingOptions = .ok compiled) :
    run raw seed invocation limits =
      (compiled.run invocation limits.toRunOptions).mapError Error.execution := by
  unfold run
  rw [compiledOk]
  change (do
    let compiled ← Except.ok compiled
    (compiled.run invocation limits.toRunOptions).mapError Error.execution) = _
  rfl

end Solcore.Frontend.SourceCompiler
