import Solcore.Frontend.RustHull.RuntimeReturnDataEffectsSemantics
import Solcore.Frontend.RustHull.RuntimeCodeEffectsCorrespondence

/-! The return-data extension selects the existing runtime only for names that
it implements. Linked code copying additionally requires installed code slots. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
open Correspondence

def supported (slots : List EffectSlot) (withCode : Bool) (name : String) : Prop :=
  RuntimeAccountEffectsCorrespondence.supported slots name ∨
  (withCode = true ∧ ∃ operation : CodeImageSemantics.Operation, operation.name = name) ∨
  name = "returndatacopy" ∨ name = "memoryguard"

theorem primitive_none {slots : List EffectSlot} {withCode : Bool} {name : String}
    (enabled : supported slots withCode name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with (((((((memory | storage) | environment) | logs) | termination) | copy) | hash) | account) | ⟨_, code⟩ | rfl | rfl
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := termination
    cases operation <;> rfl
  · obtain ⟨operation, rfl, _⟩ := copy
    cases operation <;> rfl
  · subst name
    rfl
  · obtain ⟨operation, rfl⟩ := account
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := code
    cases operation <;> rfl
  · rfl
  · rfl

private theorem runtime_new_unsupported {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeCodeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (newName : name = "returndatacopy" ∨ name = "memoryguard")
    (computed : RuntimeCodeEffectsSemantics.Builtin image name type arguments initial result final) : False := by
  cases computed with
  | copy computed =>
      obtain ⟨operation, named⟩ := computed.named
      rcases newName with rfl | rfl <;> cases operation <;>
        simp [CodeImageSemantics.Operation.name] at named
  | runtime computed =>
      cases computed with
      | observation computed =>
          obtain ⟨operation, named⟩ := computed.named
          rcases newName with rfl | rfl <;> cases operation <;>
            simp [AccountObservationSemantics.Operation.name] at named
      | runtime computed =>
          cases computed with
          | hash computed =>
              cases computed
              simp at newName
          | runtime computed =>
              cases computed with
              | copy computed =>
                  cases computed <;> simp at newName
              | runtime computed =>
                  cases computed with
                  | termination computed =>
                      have missing : TerminationSemantics.builtin name type arguments initial.runtime.runtime.runtime = none := by
                        rcases newName with rfl | rfl <;> rfl
                      rw [missing] at computed
                      contradiction
                  | runtime computed =>
                      cases computed with
                      | logs computed =>
                          cases computed with
                          | log operation _ _ _ _ _ _ =>
                              rcases newName with named | named <;> cases operation <;>
                                simp [LogsSemantics.Operation.name] at named
                      | runtime computed =>
                          have missing : RuntimeEnvironmentEffectsSemantics.builtin name type arguments initial.runtime.runtime = none := by
                            rcases newName with rfl | rfl <;> rfl
                          rw [missing] at computed
                          contradiction

theorem runtime_enabled {slots : List EffectSlot} {withCode : Bool} {image : Option (List UInt8)}
    {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeCodeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (enabled : supported slots withCode name)
    (computed : RuntimeCodeEffectsSemantics.Builtin image name type arguments initial result final) :
    RuntimeCodeEffectsCorrespondence.supported slots name := by
  rcases enabled with account | ⟨_, code⟩ | copying | guard
  · exact .inl account
  · exact .inr code
  · exact False.elim (runtime_new_unsupported (.inl copying) computed)
  · exact False.elim (runtime_new_unsupported (.inr guard) computed)

theorem account_enabled {slots : List EffectSlot} {image : Option (List UInt8)}
    {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeCodeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (enabled : supported slots false name)
    (computed : RuntimeCodeEffectsSemantics.Builtin image name type arguments initial result final) :
    RuntimeAccountEffectsCorrespondence.supported slots name := by
  rcases enabled with account | ⟨impossible, _⟩ | copying | guard
  · exact account
  · cases impossible
  · exact False.elim (runtime_new_unsupported (.inl copying) computed)
  · exact False.elim (runtime_new_unsupported (.inr guard) computed)

theorem code_unsupported {slots : List EffectSlot} (operation : CodeImageSemantics.Operation)
    (enabled : RuntimeAccountEffectsCorrespondence.supported slots operation.name) : False := by
  rcases enabled with ((((((memory | storage) | environment) | logs) | termination) | copy) | hash) | account
  · obtain ⟨other, named⟩ := memory
    cases operation <;> cases other <;> simp [CodeImageSemantics.Operation.name, MemoryBuiltinCorrespondence.Operation.name] at named
  · obtain ⟨other, named⟩ := storage
    cases other with
    | load transient | store transient =>
      cases operation <;> cases transient <;> simp [CodeImageSemantics.Operation.name, StorageBuiltinCorrespondence.Operation.name] at named
  · obtain ⟨other, named, _⟩ := environment
    cases other <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals cases operation <;> simp [CodeImageSemantics.Operation.name, EnvironmentSemantics.Operation.name,
      EnvironmentSemantics.Direct.name, EnvironmentSemantics.AmbientWord.name] at named
  · obtain ⟨other, named⟩ := logs
    cases operation <;> cases other <;> simp [CodeImageSemantics.Operation.name, LogsSemantics.Operation.name] at named
  · obtain ⟨other, named⟩ := termination
    cases operation <;> cases other <;> simp [CodeImageSemantics.Operation.name, TerminationSemantics.Operation.name] at named
  · obtain ⟨other, named, _⟩ := copy
    cases operation <;> cases other <;> simp [CodeImageSemantics.Operation.name, MemoryCopySemantics.Operation.name] at named
  · cases operation <;> simp [CodeImageSemantics.Operation.name] at hash
  · obtain ⟨other, named⟩ := account
    cases operation <;> cases other <;> simp [CodeImageSemantics.Operation.name, AccountObservationSemantics.Operation.name] at named

end Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
