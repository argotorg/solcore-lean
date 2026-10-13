import Solcore.Test.SourceCoreMethodOriginEvidenceCommon
import Solcore.Test.SourceCoreMethodOriginEvidenceRootCompilerSupport
import Solcore.Test.SourceCoreMethodOriginEvidenceUseCompilerSupport
import Solcore.Test.SourceCoreMethodOriginEvidenceRelayCompilerSupport
import Solcore.Test.SourceCoreMethodOriginEvidenceIdentityCompilerSupport
import Solcore.Test.SourceCoreMethodOriginEvidenceFactoryCompilerSupport
import Solcore.Test.SourceCoreMethodOriginEvidenceClosureCompilerSupport
import Solcore.Test.SourceCoreMethodOriginEvidenceMethodCompilerObservation
import Solcore.SourceSemantics.CoreLowering.AcceptedProgramMethodCompletion

/-! The original cache is checked with all ten actual ordinary roots pending.
The two factory closure sources and every method body are also pending.
Accepted compiler actions complete the same shared program certificate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure ObservedProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  pending : AcceptedProgramMethodCompletion.Pending fixture.recipe.compiled
    [observed.wordRow.index, observed.boolRow.index, observed.useWordRow.index, observed.useBoolRow.index, observed.relayWordRow.index, observed.relayBoolRow.index, observed.identityWordRow.index, observed.identityBoolRow.index, observed.makeWordRow.index, observed.makeBoolRow.index] [observed.makeWordRow.index, observed.makeBoolRow.index]
  accepted : AcceptedProgramMethodCompletion.certify fixture.recipe.compiled
    fixture.source_wellFormed [observed.wordRow.index, observed.boolRow.index, observed.useWordRow.index, observed.useBoolRow.index, observed.relayWordRow.index, observed.relayBoolRow.index, observed.identityWordRow.index, observed.identityBoolRow.index, observed.makeWordRow.index, observed.makeBoolRow.index] [observed.makeWordRow.index, observed.makeBoolRow.index] 64 = some pending
  wordSite : CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows observed.wordShape.call.instantiation
  wordAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
    pending.table.rows observed.wordShape.call.instantiation = some ⟨wordSite⟩
  boolSite : CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows observed.boolShape.call.instantiation
  boolAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
    pending.table.rows observed.boolShape.call.instantiation = some ⟨boolSite⟩
  useWordMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.useWordRow.named observed.useWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  useWordMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.useWordRow.named observed.useWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨useWordMetadata⟩
  useBoolMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.useBoolRow.named observed.useBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  useBoolMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.useBoolRow.named observed.useBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨useBoolMetadata⟩
  relayWordMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.relayWordRow.named observed.relayWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  relayWordMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.relayWordRow.named observed.relayWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨relayWordMetadata⟩
  relayBoolMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.relayBoolRow.named observed.relayBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  relayBoolMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.relayBoolRow.named observed.relayBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨relayBoolMetadata⟩
  identityWordMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.identityWordRow.named observed.identityWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  identityWordMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.identityWordRow.named observed.identityWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨identityWordMetadata⟩
  identityBoolMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.identityBoolRow.named observed.identityBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  identityBoolMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.identityBoolRow.named observed.identityBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨identityBoolMetadata⟩
  makeWordSite : CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows observed.makeWordShape.call.instantiation
  makeWordSiteAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
    pending.table.rows observed.makeWordShape.call.instantiation = some ⟨makeWordSite⟩
  makeWordMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.makeWordRow.named observed.makeWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  makeWordMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.makeWordRow.named observed.makeWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨makeWordMetadata⟩
  makeBoolSite : CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows observed.makeBoolShape.call.instantiation
  makeBoolSiteAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
    pending.table.rows observed.makeBoolShape.call.instantiation = some ⟨makeBoolSite⟩
  makeBoolMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.makeBoolRow.named observed.makeBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  makeBoolMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.makeBoolRow.named observed.makeBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨makeBoolMetadata⟩
  methods : ObservedMethodCompilers fixture pending.table.rows
  rows : ∀ row ∈ pending.table.rows, row ∈ [observed.wordRow.row, observed.boolRow.row, observed.makeWordRow.row, observed.makeBoolRow.row, observed.relayWordRow.row, observed.relayBoolRow.row, observed.useWordRow.row, observed.useBoolRow.row, observed.identityWordRow.row, observed.identityBoolRow.row]

private structure ObservedMetadata (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (rows : List SourceSpecialization.SpecializedFunction) : Type where
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    compiled.indexed named source (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite rows)
  accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata? compiled.indexed named source
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite rows) = some ⟨metadata⟩

private def observeMetadata (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (rows : List SourceSpecialization.SpecializedFunction) : IO (ObservedMetadata compiled named source rows) := do
  match accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata? compiled.indexed named source
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite rows) with
  | none => throw (IO.userError "original expression metadata rejected")
  | some metadata => pure ⟨metadata.down, accepted⟩

private structure ObservedSite (rows : List SourceSpecialization.SpecializedFunction)
    (instantiation : DeclarationInstantiation) : Type where
  site : CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite rows instantiation
  accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite? rows instantiation = some ⟨site⟩

private def observeSite (rows : List SourceSpecialization.SpecializedFunction)
    (instantiation : DeclarationInstantiation) : IO (ObservedSite rows instantiation) := do
  match accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite? rows instantiation with
  | none => throw (IO.userError "original factory closure direct target missing")
  | some site => pure ⟨site.down, accepted⟩

def observeProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedProgramCertificate fixture observed) := do
  match accepted : AcceptedProgramMethodCompletion.certify fixture.recipe.compiled
      fixture.source_wellFormed [observed.wordRow.index, observed.boolRow.index, observed.useWordRow.index, observed.useBoolRow.index, observed.relayWordRow.index, observed.relayBoolRow.index, observed.identityWordRow.index, observed.identityBoolRow.index, observed.makeWordRow.index, observed.makeBoolRow.index] [observed.makeWordRow.index, observed.makeBoolRow.index] 64 with
  | none => throw (IO.userError "original method-origin complementary certification rejected")
  | some pending =>
      match wordAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
          pending.table.rows observed.wordShape.call.instantiation with
      | none => throw (IO.userError "original word direct target missing")
      | some ⟨wordSite⟩ =>
        match boolAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
            pending.table.rows observed.boolShape.call.instantiation with
        | none => throw (IO.userError "original bool direct target missing")
        | some ⟨boolSite⟩ =>
          let useWord ← observeMetadata fixture.recipe.compiled observed.useWordRow.named
            observed.useWordRow.row.function.typedBody pending.table.rows
          let useBool ← observeMetadata fixture.recipe.compiled observed.useBoolRow.named
            observed.useBoolRow.row.function.typedBody pending.table.rows
          let relayWord ← observeMetadata fixture.recipe.compiled observed.relayWordRow.named
            observed.relayWordRow.row.function.typedBody pending.table.rows
          let relayBool ← observeMetadata fixture.recipe.compiled observed.relayBoolRow.named
            observed.relayBoolRow.row.function.typedBody pending.table.rows
          let identityWord ← observeMetadata fixture.recipe.compiled observed.identityWordRow.named
            observed.identityWordRow.row.function.typedBody pending.table.rows
          let identityBool ← observeMetadata fixture.recipe.compiled observed.identityBoolRow.named
            observed.identityBoolRow.row.function.typedBody pending.table.rows
          let makeWordSite ← observeSite pending.table.rows observed.makeWordShape.call.instantiation
          let makeBoolSite ← observeSite pending.table.rows observed.makeBoolShape.call.instantiation
          let makeWord ← observeMetadata fixture.recipe.compiled observed.makeWordRow.named
            observed.makeWordRow.row.function.typedBody pending.table.rows
          let makeBool ← observeMetadata fixture.recipe.compiled observed.makeBoolRow.named
            observed.makeBoolRow.row.function.typedBody pending.table.rows
          let ⟨methods⟩ ← observeMethodCompilers fixture pending.table.rows
          if rows : pending.table.rows.all (fun row =>
              [observed.wordRow.row, observed.boolRow.row, observed.makeWordRow.row, observed.makeBoolRow.row, observed.relayWordRow.row, observed.relayBoolRow.row, observed.useWordRow.row, observed.useBoolRow.row, observed.identityWordRow.row, observed.identityBoolRow.row].any (fun expected => row == expected)) = true then
            pure ⟨pending, accepted, wordSite, wordAccepted, boolSite, boolAccepted,
              useWord.metadata, useWord.accepted,
              useBool.metadata, useBool.accepted,
              relayWord.metadata, relayWord.accepted,
              relayBool.metadata, relayBool.accepted,
              identityWord.metadata, identityWord.accepted,
              identityBool.metadata, identityBool.accepted,
              makeWordSite.site, makeWordSite.accepted, makeWord.metadata, makeWord.accepted,
              makeBoolSite.site, makeBoolSite.accepted, makeBool.metadata, makeBool.accepted, methods, by
              intro row member
              obtain ⟨expected, present, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp rows row member)
              exact (eq_of_beq same).symm ▸ present⟩
          else throw (IO.userError "actual direct table contains an unselected ordinary row")

theorem ObservedProgramCertificate.aligned_pending {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned
      [inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.relayWordInput, inventory.relayBoolInput, inventory.useWordInput, inventory.useBoolInput, inventory.identityWordInput, inventory.identityBoolInput] admission.pending.table.rows := by
  intro row member
  have present := admission.rows row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨inventory.wordInput, by simp, inventory.wordSame⟩
  · exact ⟨inventory.boolInput, by simp, inventory.boolSame⟩
  · exact ⟨inventory.makeWordInput, by simp, inventory.makeWordSame⟩
  · exact ⟨inventory.makeBoolInput, by simp, inventory.makeBoolSame⟩
  · exact ⟨inventory.relayWordInput, by simp, inventory.relayWordSame⟩
  · exact ⟨inventory.relayBoolInput, by simp, inventory.relayBoolSame⟩
  · exact ⟨inventory.useWordInput, by simp, inventory.useWordSame⟩
  · exact ⟨inventory.useBoolInput, by simp, inventory.useBoolSame⟩
  · exact ⟨inventory.identityWordInput, by simp, inventory.identityWordSame⟩
  · exact ⟨inventory.identityBoolInput, by simp, inventory.identityBoolSame⟩

/-- Each selected root is derived from its actual Header, then transported
back to that same cached function. Other pending certificate fields are unused. -/
theorem ObservedProgramCertificate.word_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.wordRow.named observed.wordRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.wordRow.named.specialized.function.typedBody)
      observed.wordRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.wordHeader.prepared inventory.wordHeader.aligned
    observed.wordRow.cached observed.wordRow.same
    (inventory.wordHeader.root_compiler_admission observed.wordShape observed.wordNodes observed.noLocals
      admission.wordSite (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.bool_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.boolRow.named observed.boolRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.boolRow.named.specialized.function.typedBody)
      observed.boolRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.boolHeader.prepared inventory.boolHeader.aligned
    observed.boolRow.cached observed.boolRow.same
    (inventory.boolHeader.root_compiler_admission observed.boolShape observed.boolNodes observed.noLocals
      admission.boolSite (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.useWord_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.useWordRow.named observed.useWordRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.useWordRow.named.specialized.function.typedBody)
      observed.useWordRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.useWordHeader.prepared inventory.useWordHeader.aligned
    observed.useWordRow.cached observed.useWordRow.same
    (inventory.useWordHeader.use_compiler_admission observed.useWordShape observed.useWordNodes observed.noLocals
      admission.useWordMetadata admission.useWordMetadataAccepted (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.useBool_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.useBoolRow.named observed.useBoolRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.useBoolRow.named.specialized.function.typedBody)
      observed.useBoolRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.useBoolHeader.prepared inventory.useBoolHeader.aligned
    observed.useBoolRow.cached observed.useBoolRow.same
    (inventory.useBoolHeader.use_compiler_admission observed.useBoolShape observed.useBoolNodes observed.noLocals
      admission.useBoolMetadata admission.useBoolMetadataAccepted (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.relayWord_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.relayWordRow.named observed.relayWordRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.relayWordRow.named.specialized.function.typedBody)
      observed.relayWordRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.relayWordHeader.prepared inventory.relayWordHeader.aligned
    observed.relayWordRow.cached observed.relayWordRow.same
    (inventory.relayWordHeader.relay_compiler_admission observed.relayWordShape observed.relayWordNodes observed.noLocals
      admission.relayWordMetadata admission.relayWordMetadataAccepted (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.relayBool_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.relayBoolRow.named observed.relayBoolRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.relayBoolRow.named.specialized.function.typedBody)
      observed.relayBoolRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.relayBoolHeader.prepared inventory.relayBoolHeader.aligned
    observed.relayBoolRow.cached observed.relayBoolRow.same
    (inventory.relayBoolHeader.relay_compiler_admission observed.relayBoolShape observed.relayBoolNodes observed.noLocals
      admission.relayBoolMetadata admission.relayBoolMetadataAccepted (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.identityWord_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.identityWordRow.named observed.identityWordRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.identityWordRow.named.specialized.function.typedBody)
      observed.identityWordRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.identityWordHeader.prepared inventory.identityWordHeader.aligned
    observed.identityWordRow.cached observed.identityWordRow.same
    (inventory.identityWordHeader.identity_compiler_admission observed.identityWordShape observed.identityWordNodes observed.noLocals
      admission.identityWordMetadata (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.identityBool_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.identityBoolRow.named observed.identityBoolRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.identityBoolRow.named.specialized.function.typedBody)
      observed.identityBoolRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.identityBoolHeader.prepared inventory.identityBoolHeader.aligned
    observed.identityBoolRow.cached observed.identityBoolRow.same
    (inventory.identityBoolHeader.identity_compiler_admission observed.identityBoolShape observed.identityBoolNodes observed.noLocals
      admission.identityBoolMetadata (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.makeWord_closure_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate fixture.recipe.compiled
      observed.makeWordRow.named admission.pending.table.rows false := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact inventory.makeWordHeader.closure_compiler_source observed.makeWordShape observed.makeWordNodes
    observed.noLocals admission.makeWordMetadata admission.makeWordSite
    (fun _ site => site.supported (admission.aligned_pending inventory))

theorem ObservedProgramCertificate.makeBool_closure_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate fixture.recipe.compiled
      observed.makeBoolRow.named admission.pending.table.rows false := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact inventory.makeBoolHeader.closure_compiler_source observed.makeBoolShape observed.makeBoolNodes
    observed.noLocals admission.makeBoolMetadata admission.makeBoolSite
    (fun _ site => site.supported (admission.aligned_pending inventory))

/-- Selection uses actual cache indices. The original complete Certificate is
constructed only after every accepted compiler root fills its own position. -/
def ObservedProgramCertificate.certificate {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedProgramAdmission.Certificate fixture.recipe.compiled :=
  admission.pending.complete_receipts (by
    intro position member named selected
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have same : named = observed.wordRow.named :=
        Option.some.inj (selected.symm.trans observed.wordRow.cached)
      subst named
      exact ⟨.scoped admission.word_source_admission⟩
    · have same : named = observed.boolRow.named :=
        Option.some.inj (selected.symm.trans observed.boolRow.cached)
      subst named
      exact ⟨.scoped admission.bool_source_admission⟩
    · have same : named = observed.useWordRow.named :=
        Option.some.inj (selected.symm.trans observed.useWordRow.cached)
      subst named
      exact ⟨.scoped admission.useWord_source_admission⟩
    · have same : named = observed.useBoolRow.named :=
        Option.some.inj (selected.symm.trans observed.useBoolRow.cached)
      subst named
      exact ⟨.scoped admission.useBool_source_admission⟩
    · have same : named = observed.relayWordRow.named :=
        Option.some.inj (selected.symm.trans observed.relayWordRow.cached)
      subst named
      exact ⟨.scoped admission.relayWord_source_admission⟩
    · have same : named = observed.relayBoolRow.named :=
        Option.some.inj (selected.symm.trans observed.relayBoolRow.cached)
      subst named
      exact ⟨.scoped admission.relayBool_source_admission⟩
    · have same : named = observed.identityWordRow.named :=
        Option.some.inj (selected.symm.trans observed.identityWordRow.cached)
      subst named
      exact ⟨.scoped admission.identityWord_source_admission⟩
    · have same : named = observed.identityBoolRow.named :=
        Option.some.inj (selected.symm.trans observed.identityBoolRow.cached)
      subst named
      exact ⟨.scoped admission.identityBool_source_admission⟩
    · have same : named = observed.makeWordRow.named :=
        Option.some.inj (selected.symm.trans observed.makeWordRow.cached)
      subst named
      obtain ⟨certificate⟩ := observed.makeWord_factory_certificate
      exact ⟨.formation certificate⟩
    · have same : named = observed.makeBoolRow.named :=
        Option.some.inj (selected.symm.trans observed.makeBoolRow.cached)
      subst named
      obtain ⟨certificate⟩ := observed.makeBool_factory_certificate
      exact ⟨.formation certificate⟩) (by
    intro position member named selected
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · have same : named = observed.makeWordRow.named :=
        Option.some.inj (selected.symm.trans observed.makeWordRow.cached)
      subst named
      exact admission.makeWord_closure_source
    · have same : named = observed.makeBoolRow.named :=
        Option.some.inj (selected.symm.trans observed.makeBoolRow.cached)
      subst named
      exact admission.makeBool_closure_source)
    (admission.methods.complete admission.pending.table admission.pending.catalog observed.noLocals)

theorem ObservedProgramCertificate.aligned {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned
      [inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.relayWordInput, inventory.relayBoolInput, inventory.useWordInput, inventory.useBoolInput, inventory.identityWordInput, inventory.identityBoolInput] admission.certificate.table.rows :=
  admission.aligned_pending inventory

/-- The primary production entry point constructs its own complete eligible
ordinary catalog and closes table alignment without the selected subset. -/
theorem ObservedProgramCertificate.automatic_catalog {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed) :
    ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
      Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
        (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        receiver.completion) := by
  exact admission.certificate.issue fixture.source_wellFormed fixture.recipePrepared receiver.issued
    receiver.registry observed.wordRow.entryMember (by rw [fixture.sameProgram]; exact fixture.checked)

/-- This proof is exercised by the same runtime-produced certificate used by
the seven-call regression; catalog construction is kept inside the proof. -/
theorem ObservedProgramCertificate.automatic_catalog_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
        Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
          (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
          receiver.completion) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, admission.automatic_catalog receiver⟩

end Tests.SourceCoreMethodOriginEvidence
