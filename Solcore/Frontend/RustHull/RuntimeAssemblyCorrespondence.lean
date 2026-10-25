import Solcore.Frontend.RustHull.RuntimeFrameCorrespondence
import Solcore.Frontend.RustHull.DerivationProgramCorrespondence
import Solcore.Frontend.RustHull.ProgramSelectionCorrespondence
import Solcore.Frontend.RustHull.GlobalInvocationCorrespondence

/-! Actual assembly with an initialized runtime scope. The compiler's global
allocation, installation and selected invocation retain the independent Hull
result and the concrete external-state representation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution DerivationCorrespondence

/-- Runtime slot names cannot be shadowed by generated function-cell bindings. -/
def EffectSlotsSeparate (slots : List EffectSlot) : Prop :=
  ∀ slot ∈ slots, slot.name.startsWith "function$" = false

theorem effectSlot_ne_function {slots : List EffectSlot} (separated : EffectSlotsSeparate slots)
    {slot : EffectSlot} (member : slot ∈ slots) (name : String) :
    Effects.slotName ("function$" ++ name) ≠ Effects.slotName slot.name := by
  intro same
  have equal : "function$" ++ name = slot.name := by simpa [Effects.slotName] using same
  have forbidden := separated slot member
  rw [← equal] at forbidden
  simp at forbidden

theorem EffectEnvironmentRel.addFunction {slots : List EffectSlot} {scope : Scope}
    {environment : Core.Environment}
    (related : EffectEnvironmentRel slots scope Core.Renaming.id environment)
    (separated : EffectSlotsSeparate slots) (own : Signature) (value : Core.Value) :
    EffectEnvironmentRel slots (globalBinding own :: scope) Core.Renaming.id (value :: environment) := by
  intro slot member binding index looked
  rw [scope_lookup_cons] at looked
  have different := effectSlot_ne_function separated member own.name
  simp only [globalBinding, Option.some_beq_some, beq_eq_false_iff_ne.mpr different,
    Bool.false_eq_true, ↓reduceIte] at looked
  cases previous : scope.lookup (Effects.slotName slot.name) with
  | error error => simp only [previous] at looked; contradiction
  | ok found =>
      rcases found with ⟨oldBinding, oldIndex⟩
      simp only [previous, Except.ok.injEq, Prod.mk.injEq] at looked
      obtain ⟨rfl, rfl⟩ := looked
      exact related slot member oldBinding oldIndex previous

theorem ScopeCoverage.globalScope {source : Semantics.Environment} {runtime : Scope}
    (covered : ScopeCoverage source runtime) (signatures : List Signature) :
    ScopeCoverage source (globalScope signatures runtime) := by
  induction signatures generalizing runtime with
  | nil => exact covered
  | cons own rest ih =>
      have reserved := covered.reserved (globalBinding own) (by
        intro name named
        cases Option.some.inj named
        exact slotName_reserved _)
      simpa only [Correspondence.globalScope, globalBinding, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] using ih reserved

/-- Extend the actual runtime environment by the exact function references
allocated by globalAllocation; the reversed lexical order is derived here. -/
theorem EffectEnvironmentRel.globalScope {slots : List EffectSlot} {runtime : Scope}
    {environment : Core.Environment}
    (related : EffectEnvironmentRel slots runtime Core.Renaming.id environment)
    (separated : EffectSlotsSeparate slots) (signatures : List Signature) (base : Nat) :
    EffectEnvironmentRel slots (globalScope signatures runtime) Core.Renaming.id
      (globalEnvironment signatures base environment) := by
  induction signatures generalizing runtime environment base with
  | nil => exact related
  | cons own rest ih =>
      have next := ih (related.addFunction separated own
        (.cellRef (Core.OptionalCell.cellType own.functionType) base)) (base + 1)
      simpa only [Correspondence.globalScope, globalBinding, globalEnvironment, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append] using next

/-- The assembled expression runs in the real frame's runtime references,
followed by its input bundle and caller environment. All function cells and
captured runtime references come from this same successful assembly. -/
theorem assemble_recursive_program_effects {supported : String → Prop} {σ : Type} {model : StateModel σ} {slots : List EffectSlot}
    {effects : Semantics.ExternalSemantics σ} {functions : List Function} {function : Function}
    {entry : String} {runtime : Scope} {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (external : ExternalCallPreservation supported model slots effects)
    (eligible : ExecutableProgram supported functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State σ} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions effects function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel model world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧ ClosuresPreserved store finalStore := by
  have sourceUnique := assemble_names_unique accepted
  obtain ⟨signatures, codes, sourceFunction, code, index, signaturesCompiled,
    sourceSelected, signatureCompiled, codesCompiled, codeFound, ownEqual,
    _, allocatedEqual⟩ := assemble_selection accepted
  have sameFunction := Option.some.inj (selected.symm.trans sourceSelected)
  subst sourceFunction
  subst own
  subst allocated
  have aligned := codesCompiled.aligned signaturesCompiled
  have signatureTable := compiledSignatures signaturesCompiled
  have unique : (signatures.map Signature.name).Nodup := by
    rw [signatureTable.names]
    exact sourceUnique
  obtain ⟨selectedOwn, signatureSelected, selectedCompiled⟩ := signatureTable.source_selected selected
  have sameOwn := Except.ok.inj (selectedCompiled.symm.trans signatureCompiled)
  subst selectedOwn
  have globals := GlobalEnvironmentRel.of_lookup aligned
    (scope := globalScope signatures runtime)
    (fun slot closure found => globalScope_lookup unique
      (by simp only [← aligned, List.getElem?_map, found, Option.map_some]) runtime)
    store.length (runtimeValues ++ bundleValues targets :: caller)
  have initialized := state.initializeGlobals signatures codes (runtimeValues ++ bundleValues targets :: caller)
  have installed := InstalledGlobals.initialize aligned (runtimeValues ++ bundleValues targets :: caller) store
  obtain ⟨extension, target, finalStore, related, executed, finalState, _, frame⟩ :=
    (DerivationProgramCorrespondence.function_preserves_effects signaturesCompiled codesCompiled unique
      (covered.globalScope signatures) globals (runtimeRelated.globalScope separated signatures store.length)
      external eligible evaluated) selected signatureSelected codeFound values initialized installed
  have invoked := globalInvocation_evaluates aligned codeFound installed executed
  have assembled := globalInitialization_evaluates aligned invoked
  have initialFrame : ClosuresPreserved store
      (initializedGlobals signatures codes (runtimeValues ++ bundleValues targets :: caller) store) := by
    intro location parameter result body environment found
    rw [(initializedGlobals_retains signatures codes (runtimeValues ++ bundleValues targets :: caller) store).read
      location (List.getElem?_eq_some_iff.mp found).1]
    exact found
  exact ⟨extension, target, finalStore, related, by simpa only [runtimeLength] using assembled,
    finalState, initialFrame.trans frame⟩

theorem assemble_recursive_program {σ : Type} {model : StateModel σ} {slots : List EffectSlot}
    {effects : Semantics.ExternalSemantics σ} {functions : List Function} {function : Function}
    {entry : String} {runtime : Scope} {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : RecursiveProgram functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State σ} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions effects function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel model world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧ ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (ExternalCallPreservation.empty model slots effects) eligible values evaluated runtimeLength
    covered runtimeRelated separated state

end Solcore.Frontend.RustHull.Correspondence
