import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues

/-! The actual prepared Header factories expose the complete compiler layout
and the original bootstrap global slot. Their full HeaderAt receipts retain
source metadata, dictionaries and substitution order. A later caller's global
slots are supplied separately by its actual input catalog observation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedHeaderReceipts
open Core Frontend SourceInference GeneralHeap
open RecursiveNamedCatalog RecursiveNamedPublicSpecializationMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}

/-- The original reserved environment contains the signature and physical
location of this actual cached Header slot. -/
theorem bootstrap_slot (header : CallableIndexedOwnedFunctionValues.Header compiled program) :
    (RecursiveNamedCatalogPreparedInitialization.environment compiled)[header.slot]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
        (RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)) :=
  RecursiveNamedCatalogInitialization.global_reference compiled.indexed.base.globals
    compiled.indexed.ancestry.layout.frame
    (CallableIndexedPreparedInventories.cached_global_at compiled header.selected)

section Factory
variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row) {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}

/-- This packet keeps the entire actual compiler/source receipt. The bootstrap
slot is an observation of the original reserved environment. -/
structure Receipt (prepared : Prepared compiled row) (instantiation : DeclarationInstantiation)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) : Prop where
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header
  bootstrap : (RecursiveNamedCatalogPreparedInitialization.environment compiled)[header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
      (RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot))

theorem Receipt.of_prepared
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    Receipt prepared instantiation header :=
  ⟨aligned, bootstrap_slot header⟩

/-- Equality of the full prepared layout is taken from the actual Header
construction, preserving more than its definitions projection. -/
theorem Receipt.same_layouts (receipt : Receipt prepared instantiation header) :
    header.layouts = compiled.indexed.layouts :=
  receipt.aligned.layouts

/-- Canonical metadata uses the original factory with its complete dictionary. -/
theorem canonical_with_evidence
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok prepared.named.signature.key) :
    ∃ header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram),
      Receipt prepared (CallableNamedMetadata.instantiation row) header := by
  obtain ⟨header, aligned⟩ := RecursiveNamedPreparedHeaders.Prepared.canonical_header_with_evidence
    prepared wellFormed range ordinaryReturn ordinaryParameters target
  exact ⟨header, Receipt.of_prepared prepared aligned⟩

/-- Retained metadata keeps its full reversed substitution order through the
same actual compiler Header factory. -/
theorem retained_with_evidence
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key) :
    ∃ header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram),
      Receipt prepared (CallableNamedCanonicalOrder.retainedInstantiation row) header := by
  obtain ⟨header, aligned⟩ := RecursiveNamedPreparedHeaders.Prepared.retained_header_with_evidence
    prepared wellFormed range ordinaryReturn ordinaryParameters target
  exact ⟨header, Receipt.of_prepared prepared aligned⟩
end Factory

/-- The public compiler supplies the original worklist row, full preparation,
Header layout and original bootstrap slot in one receipt. -/
theorem of_public_compile_with_evidence {sourceProgram : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {publicCompiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompiler.compileChecked sourceProgram seeds options = .ok publicCompiled)
    (issued : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (member : row ∈ recipe.compiled.validationPlan.specializations)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures recipe.compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key) :
    ∃ (prepared : Prepared recipe.compiled row)
      (header : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)),
      Receipt prepared (CallableNamedMetadata.instantiation row) header := by
  obtain ⟨prepared, header, aligned⟩ := RecursiveNamedPreparedHeaders.of_public_compile_with_evidence
    accepted issued member wellFormed range ordinaryReturn ordinaryParameters target
  exact ⟨prepared, header, Receipt.of_prepared prepared aligned⟩

section Caller
variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- A caller's original canonical slots are independent from its reached pool. -/
def Globals (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (callerPrefix : Nat) (scope : SourceCoreLocalCell.Scope) (canonical : Environment) : Prop :=
  ∀ header, header ∈ headers → canonical[scope.length + callerPrefix + header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header))

/-- The actual input catalog provides exactly the global-slot family required
by owned expression heads, including its caller prefix and canonical order. -/
theorem globals_of_entry (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    {capturePrefix callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    (entry : Entry (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations capturePrefix callerPrefix scope mapping world heap store canonical) :
    Globals (headers := headers) owner callerPrefix scope canonical :=
  entry.globals

/-- The full captured canonical environment supplies its own original globals.
This observation retains the actual capture prefix and every captured value. -/
theorem globals_of_capture (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {frameLocation : Location}
    (capture : Capture (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix frameLocation header mapping world heap store) :
    Globals (headers := headers) owner owner.key.capturePrefix [] capture.canonical := by
  intro target member
  simpa only [List.length_nil, Nat.zero_add] using capture.coherent target member
end Caller

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedHeaderReceipts
