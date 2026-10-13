import Solcore.Test.SourceCoreCoercionPublicCommon
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyAdmission

/-! The actual compiled keep body supplies its statement tree. Only original
expression metadata and its selected return occurrence are supplied here. -/
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
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog fixture.recipe.compiled)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

theorem ActualHeader.keep_compiler_admission (observed : ObservedProgram fixture)
    (actual : ActualHeader fixture observed.keepRow.row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed observed.keepRow.named observed.keepRow.row.function.typedBody
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows)) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header directRows := by
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
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows) := by
    rw [namedEq, actual.source]
    exact metadata
  have found : actual.header.function.source.lookupStatement? observed.keepShape.statement.id =
      some observed.keepShape.statement := by
    rw [actual.source]
    exact observed.keepShape.statementFound
  have child : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
      actual.header.function.source observed.keepShape.read.node.id
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows) := by
    rw [actual.source]
    exact .leaf (.read observed.keepShape.read.found observed.keepShape.read.form)
  exact AcceptedNamedBodyAdmission.of_returning actual.prepared actual.aligned metadata
    bodyEq found observed.keepShape.statementForm child fixture.source_wellFormed

/-- The original cache identity transports the compiler-derived admission to
its exact retained function. No program certificate is needed for this proof. -/
theorem ObservedProgram.keep_source_admission (observed : ObservedProgram fixture)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed observed.keepRow.named observed.keepRow.row.function.typedBody
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows)) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.keepRow.named observed.keepRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements
        observed.keepRow.named.specialized.function.typedBody)
      observed.keepRow.named.specialized.function.inferredBodyType directRows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.keepHeader.prepared
    inventory.keepHeader.aligned observed.keepRow.cached observed.keepRow.same
    (inventory.keepHeader.keep_compiler_admission observed metadata)

include rows receiver methods in
theorem ActualHeader.keep_compiler_support (observed : ObservedProgram fixture)
    (actual : ActualHeader fixture observed.keepRow.row)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := actualRegistry) (semanticFaults := faults) actual.header body) := by
  exact CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual actual.prepared actual.aligned rows
    (.empty _) (actual.keep_compiler_admission observed observed.keepMetadata)
    fixture.recipePrepared actual.diagnostic receiver fixture.source_wellFormed
    (CallableMethodBodyCoherence.of_checked (by rw [fixture.sameProgram]; exact fixture.checked))
    (by rw [fixture.sameProgram]; exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked)
    methods observed.makeRow.entryMember (actualStagePrepared fixture)

end Tests.SourceCoreCoercionPublic
