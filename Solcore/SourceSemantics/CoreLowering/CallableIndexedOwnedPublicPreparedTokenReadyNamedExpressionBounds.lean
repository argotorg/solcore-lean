import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicTokenReadyNamedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts

/-! The actual public compiler constructs a Header together with its retained
diagnostic producer. Assignment preparation is derived internally at that same
Source; genuine typing, child compilation and residual place facts feed the
existing closed ordinary/direct named runtime family. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicReadyNamedExpressionBounds (compilation)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {callerCompilation : SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable {faults : FunctionCalls.FaultRep}

/-- The Header keeps its complete existing public receipt and the diagnostic
identity selected by that same actual compiler preparation. -/
structure PublicReceipt (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) where
  original : CallableIndexedOwnedPublicReadyNamedExpressionBounds.PublicReceipt header
  diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt original.prepared

private theorem selected_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row) :
    prepared.named.signature.key = row.key := by
  have accepted := CallableIndexedActualNamedSourceReceipts.cached_record compiled prepared.selected prepared.compilation.hook
  rw [prepared.same] at accepted
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · next selected found =>
    cases accepted
    have member : row ∈ [row] := List.mem_singleton_self _
    rw [← found] at member
    exact (of_decide_eq_true (List.mem_filter.mp member).2).symm
  · cases accepted

/-- Actual public preparation chooses the Header from its own retained
Prepared receipt. The checked native membership remains authentic input. -/
theorem of_public_compile {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
    (issued : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe)
    (member : row ∈ recipe.compiled.validationPlan.specializations)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures recipe.compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)
    (nativeEntry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts)
    (nativeMember : nativeEntry ∈ recipe.compiled.indexed.entries) :
    ∃ header : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram),
      Nonempty (PublicReceipt header) := by
  obtain ⟨prepared, diagnostic⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.of_public_compile accepted issued member
  obtain ⟨header, aligned⟩ := RecursiveNamedPreparedHeaders.Prepared.canonical_header_with_evidence prepared
    wellFormed range ordinaryReturn ordinaryParameters
    (target.trans (congrArg Except.ok (selected_key prepared).symm))
  obtain ⟨_source, _sourceAccepted, _cached, recipeAccepted⟩ :=
    RecursiveNamedPreparedStageContracts.public_compilation accepted issued
  let original : CallableIndexedOwnedPublicReadyNamedExpressionBounds.PublicReceipt header := {
    recipe := recipe, accepted := recipeAccepted, row := row, prepared := prepared,
    instantiation := CallableNamedMetadata.instantiation row, aligned := aligned,
    nativeEntry := nativeEntry, nativeMember := nativeMember }
  exact ⟨header, ⟨⟨original, diagnostic⟩⟩⟩

/-- Genuine static inputs are tied to the actual public Header and requested
only at real ordinary parameter entries. They contain no interpreted output
predicate, profile provider or expression/body execution law. -/
structure StaticInputs (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) (issued : PublicReceipt header) where
  operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source
  unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped header.function.source
  children : CallableIndexedOwnedNamedTokenProfileExtraction.ChildrenFor
    (header := header) (headers := headers) (registry := registry) (expressionSyntax := expressionSyntax)
    compilation functions owner
  operands : ∀ reason token, GenericAssignmentDiagnostics.OperandRep
    issued.original.prepared.compilation.own.assignments reason token → faults reason token
  unary : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep
    issued.original.prepared.compilation.own.assignments reason token → faults reason token
  places : EmittedDiagnosticTokenPlan.PlaceReceipts (source := header.function.source)
    (tracked := true)
    (invalidOperand := GenericAssignmentDiagnostics.token issued.original.prepared.compilation.own.assignments)
    registry faults

/-- The original canonical caller wraps the same actual ordered pool. -/
private abbrev caller := CallableIndexedOwnedReadyNamedExpressionTreeBounds.caller (headers := headers)
  (compilation := callerCompilation) owner

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (ordinary : owner.key.capturePrefix = 0)
  (publicReceipts : ∀ header, header ∈ headers → PublicReceipt header)
  (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
  (calleeUninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (calleeMissing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (staticInputs : ∀ header (member : header ∈ headers),
    StaticInputs (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults)
      (expressionSyntax := expressionSyntax) header (publicReceipts header member))
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

/-- The genuine retained diagnostic producer supplies the exact first token
and assignment table at this Header. Only proof-local selection is needed. -/
theorem ready_inputs (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) (issued : PublicReceipt header)
    (inputs : StaticInputs (functions := functions) (owner := owner) (headers := headers)
      (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) header issued) :
    Nonempty (CallableIndexedOwnedPublicTokenReadyNamedExpressionBounds.StaticInputs
      (functions := functions) (owner := owner) (headers := headers)
      (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) header issued.original) := by
  obtain ⟨first, assignments⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
    issued.original.prepared issued.diagnostic issued.original.aligned
  exact ⟨⟨first, assignments, inputs.operandsTyped, inputs.unaryTyped,
    inputs.children, inputs.operands, inputs.unary, inputs.places⟩⟩

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped complete staticInputs syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedPublicTokenReadyNamedExpressionBounds.preserves_at_runtime
    (callerCompilation := callerCompilation) (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing ordinary (fun header member => (publicReceipts header member).original) catalog calleeUninitialized calleeMissing escaped
    complete (fun header member => Classical.choice
      (ready_inputs functions owner header (publicReceipts header member) (staticInputs header member))) syntaxTrees
    sameLedger runtimeLedger budget size within

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped complete staticInputs syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedPublicTokenReadyNamedExpressionBounds.reflects_at_runtime
    (callerCompilation := callerCompilation) (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique
    uninitialized missing ordinary (fun header member => (publicReceipts header member).original) catalog calleeUninitialized calleeMissing escaped
    complete (fun header member => Classical.choice
      (ready_inputs functions owner header (publicReceipts header member) (staticInputs header member))) syntaxTrees
    sameLedger runtimeLedger budget size within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds
