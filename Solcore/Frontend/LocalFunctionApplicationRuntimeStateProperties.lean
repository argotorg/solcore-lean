import Solcore.Frontend.LocalFunctionApplicationProperties
import Solcore.Resolved.Eval
import Solcore.Core.Safety

/-! Runtime-world safety for the exact original Core application. These
state-only results use positional values, not source lookup correspondence;
ordered ID alignment is therefore not a premise. All outer frames are typed. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalFunctionApplicationElaborates.runtime_state_hasType
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation type resultType) :
    Core.StateHasType
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, store⟩ resultType :=
  .eval storeTyped environmentTyped elaboration.core_hasType continuationTyped

theorem LocalFunctionApplicationElaborates.runtime_run_never_faults
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation type resultType)
    (fuel : Nat) (error : Core.MachineFault) (faultState : Core.State) :
    Core.runStateful fuel
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, store⟩ ≠
      .fault error faultState :=
  Core.well_typed_runStateful_never_faults
    (elaboration.runtime_state_hasType environmentTyped storeTyped continuationTyped)

/-- The entire actually suspended state is retained, including its captured
values, frames and current store. Its typing may use an extended world. -/
theorem LocalFunctionApplicationElaborates.runtime_checkpoint_hasType
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation type resultType)
    {spent : Nat} {checkpoint : Core.State}
    (exhausted : Core.runStateful spent
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, store⟩ =
      .outOfFuel checkpoint) :
    Core.StateHasType checkpoint resultType :=
  (Core.runStateful_outOfFuel_sound exhausted).1.preserve_state_type
    (elaboration.runtime_state_hasType environmentTyped storeTyped continuationTyped)

theorem LocalFunctionApplicationElaborates.runtime_checkpoint_never_faults
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation type resultType)
    {spent : Nat} {checkpoint : Core.State}
    (exhausted : Core.runStateful spent
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, store⟩ =
      .outOfFuel checkpoint)
    (additional : Nat) (error : Core.MachineFault) (faultState : Core.State) :
    Core.runStateful additional checkpoint ≠ .fault error faultState :=
  Core.well_typed_runStateful_never_faults
    (elaboration.runtime_checkpoint_hasType environmentTyped storeTyped continuationTyped exhausted)

end Solcore.Frontend
