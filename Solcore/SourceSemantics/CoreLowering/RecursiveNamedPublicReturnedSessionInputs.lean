import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning

/-! A following public start uses the native state of the actual preceding
successful completion. Optional named/builtin issuance preserves that state;
Source closure and heap meaning remain the returned semantic proof's job. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedSessionInputs
open Core Frontend SourceInference
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning

/-- Reconcile the next real startup with the previous returned world and
store, including a finite sequence of actual state-preserving issuances. -/
theorem StartAt.after_succeeded
    {artifact : Artifact} {previous : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {result : Core.Value} {returnedStore : Store} {completion : Completion artifact}
    (returned : previous.SucceededResultAt executionFuel outputFuel generation result returnedStore completion)
    {session : Session artifact} (continued : completion.session.IssuanceChain session)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments inputFuel checkpoint recipe root world store native encodedValues) :
    world = returnedStore.map Core.Value.type ∧ store = returnedStore := by
  have nativeAt := continued.same_runtime.native_at returned.native_at.2
  have current := started.state
  cases session
  rename_i authority actualWorld actualStore stored environmentTyped registry values owner sourcePrefix
  change actualWorld = returnedStore.map Core.Value.type ∧ actualStore = returnedStore at nativeAt
  change actualWorld = world ∧ actualStore = store at current
  exact ⟨current.1.symm.trans nativeAt.1, current.2.symm.trans nativeAt.2⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedSessionInputs
