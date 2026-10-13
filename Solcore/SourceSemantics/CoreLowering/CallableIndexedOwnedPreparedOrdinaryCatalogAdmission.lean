import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedConcreteRangeReceipts

/-! Independent declaration admission supplies the complete range of an
actual matched ordinary specialization. The same result applies to a public
program entry without assuming representation of its heap or arguments. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open Frontend SourceInference

theorem Eligible.of_admissible {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {context : Context}
    {instantiation : DeclarationInstantiation}
    (origin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram row)
    (matched : CallableNamedMetadata.Matches row instantiation)
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false) :
    Eligible compiled row := by
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution := by
    obtain ⟨_request, _signature, _generic, _signatureMember, _genericMember, _resolved, accepted⟩ := origin
    simpa only [signatures] using
      CallableIndexedOwnedReachedNamedConcreteRangeReceipts.range_of_admissible_match matched admissible accepted
  exact ⟨origin, range, ordinaryReturn, ordinaryParameters⟩

theorem Eligible.of_entry {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {entry : Dynamic.ProgramEntry}
    {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (origin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram row)
    (matched : CallableNamedMetadata.Matches row entry.instantiation)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false) :
    Eligible compiled row := by
  cases valid.instantiates with
  | intro _ _ _ _ admitted _ _ _ =>
    exact Eligible.of_admissible origin matched admitted.toAdmissible rfl ordinaryReturn ordinaryParameters

theorem Catalog.header_at_admissible {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled) {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {context : Context} {instantiation : DeclarationInstantiation}
    (origin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram named.specialized)
    (matched : CallableNamedMetadata.Matches named.specialized instantiation)
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ named.specialized.function.typedBody.inputs → binder.comptime = false) :
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers catalog.rows,
      header.slot = index ∧ header.named = named :=
  catalog.header_at selected
    (Eligible.of_admissible origin matched admissible signatures ordinaryReturn ordinaryParameters)

theorem Catalog.header_at_entry {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled) {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (origin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram named.specialized)
    (matched : CallableNamedMetadata.Matches named.specialized entry.instantiation)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ named.specialized.function.typedBody.inputs → binder.comptime = false) :
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers catalog.rows,
      header.slot = index ∧ header.named = named :=
  catalog.header_at selected (Eligible.of_entry origin matched valid ordinaryReturn ordinaryParameters)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
