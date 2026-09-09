import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Core.Safety

/-! Original body typing supplies safety only with the actual environment,
store and pending frames typed in one world. Saved states remain exact; their
world is existential in StateHasType. Positional state safety needs no source
ID alignment or child execution, cost or fragment law. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationReturnTreeElaborates.runtime_checkpoint_safety
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    {world : Core.StoreTyping} {environment : Core.Environment} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world environment inputs.context.values)
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation type resultType) :
    Core.StateHasType ⟨.eval core environment, continuation, store⟩ resultType ∧
      (∀ fuel error faultState, Core.runStateful fuel
        ⟨.eval core environment, continuation, store⟩ ≠ .fault error faultState) ∧
      ∀ {spent checkpoint}, Core.runStateful spent
        ⟨.eval core environment, continuation, store⟩ = .outOfFuel checkpoint →
        Core.StateHasType checkpoint resultType ∧
          ∀ additional error faultState,
            Core.runStateful additional checkpoint ≠ .fault error faultState := by
  have initial : Core.StateHasType ⟨.eval core environment, continuation, store⟩ resultType :=
    .eval storeTyped environmentTyped (elaboration.core_hasType childCoreType) continuationTyped
  refine ⟨initial, fun _ _ _ => Core.well_typed_runStateful_never_faults initial, ?_⟩
  intro spent checkpoint exhausted
  have saved := (Core.runStateful_outOfFuel_sound exhausted).1.preserve_state_type initial
  exact ⟨saved, fun _ _ _ => Core.well_typed_runStateful_never_faults saved⟩

end Solcore.Frontend
