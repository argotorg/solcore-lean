import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCachedInputs

/-! Actual cached preparation supplies a finite ordinary catalog. Original
declaration or program-entry admission identifies each reached member; other
cache rows impose no admission obligation on that call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog
open Frontend SourceInference
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts

theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (Catalog compiled) := by
  apply collect compiled wellFormed
  intro index named selected eligible
  exact CallableIndexedOwnedPreparedOrdinaryCachedInputs.of_cached compiled wellFormed selected
    eligible.origin eligible.range eligible.ordinaryReturn eligible.ordinaryParameters

theorem eligible_of_admissible {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {context : Context} {instantiation : DeclarationInstantiation}
    (matched : CallableNamedMetadata.Matches named.specialized instantiation)
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ordinaryReturn : instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ instantiation.parameterComptime, flag = false) :
    Eligible compiled named.specialized := by
  obtain ⟨signature, member, declaration⟩ := admissible.signature_id
  have origin := CallableIndexedOwnedPreparedOrdinaryCachedInputs.ordinary_origin compiled wellFormed
    (RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected rfl)
    (by simpa only [signatures] using member) (matched.declaration.trans declaration.symm)
  apply Eligible.of_admissible origin matched admissible signatures
    (matched.returnComptime.trans ordinaryReturn)
  intro binder member
  apply ordinaryParameters binder.comptime
  rw [← matched.parameterComptime]
  exact List.mem_map.mpr ⟨binder, member, rfl⟩

theorem eligible_of_entry {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (matched : CallableNamedMetadata.Matches named.specialized entry.instantiation)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    Eligible compiled named.specialized := by
  cases valid.instantiates with
  | intro _ _ _ _ admitted _ _ _ =>
    exact eligible_of_admissible wellFormed selected matched admitted.toAdmissible rfl
      ordinaryReturn ordinaryParameters

/-- A reached direct target obtains its Header from the actual final cache and
the original Source declaration admission. Other cached rows need no admission. -/
theorem covers_direct {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {context : Context} {instantiation : DeclarationInstantiation}
    {index : Nat} {signature : SourceCoreGeneralFunctions.Signature}
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ordinaryReturn : instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ instantiation.parameterComptime, flag = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation =
      .ok signature.key)
    (global : compiled.indexed.base.globals[index]? = some signature) :
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers catalog.rows,
      header.slot = index ∧ header.named.signature = signature := by
  rw [CallableIndexedPreparedInventories.cached_globals, List.getElem?_map] at global
  cases selected : compiled.indexed.base.functions[index]? with
  | none => simp [selected] at global
  | some named =>
    have same : named.signature = signature := by simpa [selected] using global
    have matched := CallableNamedMetadata.matches_of_exact
      (show SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation =
        .ok named.signature.key by simpa only [same] using target)
      (CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled selected)
    obtain ⟨header, member, slot, namedAt⟩ := catalog.header_at selected
      (eligible_of_admissible wellFormed selected matched admissible signatures
        ordinaryReturn ordinaryParameters)
    exact ⟨header, member, slot, by rw [namedAt]; exact same⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog
