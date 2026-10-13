import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCatalogAdmission
import Solcore.Test.SourceCoreCoercionPublicCatalog
import Solcore.Test.SourceCoreCoercionPublicCommon
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

variable {fixture : CompiledFixture}
  {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

/- The actual finite Source checker supplies the complete metadata and body
syntax for use. Only authentic Header/source alignment is transported here. -/
include rows receiver methods in
theorem ActualHeader.use_admitted_support (observed : ObservedProgram fixture)
    (actual : ActualHeader fixture observed.useRow.row)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := actualRegistry) (semanticFaults := faults) actual.header body) := by
  have indexEq := (observed.useRow.prepared_slot actual.prepared).2
  have selected : fixture.recipe.compiled.indexed.base.functions[observed.useRow.index]? =
      some actual.prepared.named := indexEq ▸ actual.prepared.selected
  have namedEq : actual.prepared.named = observed.useRow.named :=
    Option.some.inj (selected.symm.trans observed.useRow.cached)
  have bodyEq : actual.header.function.body = [observed.useShape.body.statement.id] := by
    rw [actual.aligned.function]
    change actual.prepared.compilation.statements = [observed.useShape.body.statement.id]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, observed.useShape.body.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have resultEq : actual.header.function.resultType = .word := by
    rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
    exact observed.useResultType
  have admission : CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header [] := by
    change CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      actual.prepared.named actual.header.function.source actual.header.function.body actual.header.function.resultType []
    rw [namedEq, actual.source, bodyEq, resultEq]
    exact observed.useAdmission
  obtain ⟨loaded, checked⟩ := fixture.loaded
  exact CallableIndexedOwnedPreparedNamedCatalogAdmission.of_empty_actual rows actual.prepared actual.aligned admission
    fixture.recipePrepared actual.diagnostic receiver fixture.source_wellFormed checked
    (by rw [fixture.sameProgram]; exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked)
    (.generic ⟨methods.formed, methods.assumptions⟩) observed.makeRow.entryMember (actualStagePrepared fixture)

/- The actual finite Source checker supplies the complete metadata and body
syntax for keep. Only authentic Header/source alignment is transported here. -/
include rows receiver methods in
theorem ActualHeader.keep_admitted_support (observed : ObservedProgram fixture)
    (actual : ActualHeader fixture observed.keepRow.row)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := actualRegistry) (semanticFaults := faults) actual.header body) := by
  have indexEq := (observed.keepRow.prepared_slot actual.prepared).2
  have selected : fixture.recipe.compiled.indexed.base.functions[observed.keepRow.index]? =
      some actual.prepared.named := indexEq ▸ actual.prepared.selected
  have namedEq : actual.prepared.named = observed.keepRow.named :=
    Option.some.inj (selected.symm.trans observed.keepRow.cached)
  have bodyEq : actual.header.function.body = [observed.keepShape.statement.id] := by
    rw [actual.aligned.function]
    change actual.prepared.compilation.statements = [observed.keepShape.statement.id]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, observed.keepShape.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have resultEq : actual.header.function.resultType = .bool := by
    rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
    exact observed.keepResultType
  have admission : CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header [] := by
    change CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      actual.prepared.named actual.header.function.source actual.header.function.body actual.header.function.resultType []
    rw [namedEq, actual.source, bodyEq, resultEq]
    exact observed.keepAdmission
  obtain ⟨loaded, checked⟩ := fixture.loaded
  exact CallableIndexedOwnedPreparedNamedCatalogAdmission.of_empty_actual rows actual.prepared actual.aligned admission
    fixture.recipePrepared actual.diagnostic receiver fixture.source_wellFormed checked
    (by rw [fixture.sameProgram]; exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked)
    (.generic ⟨methods.formed, methods.assumptions⟩) observed.makeRow.entryMember (actualStagePrepared fixture)

end Tests.SourceCoreCoercionPublic
