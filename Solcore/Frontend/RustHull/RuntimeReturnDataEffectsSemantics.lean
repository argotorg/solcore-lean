import Solcore.Frontend.RustHull.RuntimeCodeEffectsSemantics
import Solcore.Frontend.RustHull.ReturnDataSemantics
import Solcore.Frontend.RustHull.MemoryGuardSemantics

/-! Return data belongs to the caller frame. Its size is the existing message
observation, so copying and later calls share one source value for that size. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeReturnDataEffectsSemantics

structure State where
  runtime : RuntimeCodeEffectsSemantics.State := {}
  returnData : MemorySemantics.Entries := []

def size (state : State) : Core.Word :=
  state.runtime.runtime.runtime.environment.direct .returnDataSize

def withRuntime (state : State) (runtime : RuntimeEffectsSemantics.State) : State :=
  {state with runtime := {state.runtime with runtime := RuntimeFullEffectsSemantics.withRuntime state.runtime.runtime runtime}}

inductive Builtin (image : Option (List UInt8)) : String → Ty → List Semantics.Value →
    State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeCodeEffectsSemantics.Builtin image name type arguments state.runtime result final) :
      Builtin image name type arguments state result {state with runtime := final}
  | copy {name type arguments state result final}
      (computed : ReturnDataSemantics.Builtin state.returnData (size state) name type arguments
        state.runtime.runtime.runtime.runtime result final) :
      Builtin image name type arguments state result (withRuntime state final)
  | guard {name type arguments state result}
      (computed : MemoryGuardSemantics.Builtin name type arguments result) :
      Builtin image name type arguments state result state

def effects (image : Option (List UInt8)) : Semantics.ExternalSemantics State where
  builtin := Builtin image
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

private theorem environment_builtin_unchanged {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : EnvironmentSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : EnvironmentSemantics.builtin name type arguments initial = some (result, final)) : final = initial := by
  unfold EnvironmentSemantics.builtin at called
  cases selected : EnvironmentSemantics.operations.find? (fun operation => operation.name == name) with
  | none => simp [selected] at called
  | some operation =>
      cases observed : EnvironmentSemantics.observe initial operation arguments with
      | none => simp [selected, observed] at called
      | some value =>
          simp [selected, observed] at called
          exact called.2.symm

private theorem environment_unchanged {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeEnvironmentEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : RuntimeEnvironmentEffectsSemantics.builtin name type arguments initial = some (result, final)) :
    final.environment = initial.environment := by
  unfold RuntimeEnvironmentEffectsSemantics.builtin at called
  split at called
  · cases Option.some.inj called
    rfl
  · cases observed : EnvironmentSemantics.builtin name type arguments initial.environment with
    | none => simp [observed] at called
    | some value =>
        rcases value with ⟨value, environment⟩
        simp only [observed, Option.map_some, Option.some.injEq, Prod.mk.injEq] at called
        rcases called with ⟨rfl, rfl⟩
        exact environment_builtin_unchanged observed

theorem runtime_environment {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeCodeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (called : RuntimeCodeEffectsSemantics.Builtin image name type arguments initial result final) :
    final.runtime.runtime.environment = initial.runtime.runtime.environment := by
  cases called with
  | copy _ => rfl
  | runtime called =>
      cases called with
      | observation _ => rfl
      | runtime called =>
          cases called with
          | hash _ => rfl
          | runtime called =>
              cases called with
              | copy _ => rfl
              | runtime called =>
                  cases called with
                  | termination _ => rfl
                  | runtime called =>
                      cases called with
                      | logs _ => rfl
                      | runtime called => exact environment_unchanged called

end Solcore.Frontend.RustHull.RuntimeReturnDataEffectsSemantics
