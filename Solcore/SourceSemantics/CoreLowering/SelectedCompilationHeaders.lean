import Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedNamedHeaderReceipts

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaders
open Core Frontend SourceInference RecursiveNamedCatalog
open RecursiveNamedPublicSpecializationMeaning
open RecursiveNamedPreparedHeaders.Prepared (HeaderAt policy)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem project_productMany {catalog : SourceCoreCompatibleCatalog.Catalog}
    {types : List TypeSystem.Ty} {native : List Core.Ty}
    (projected : types.mapM catalog.project = .ok native) :
    catalog.project (TypeSystem.Ty.productMany types) = .ok (SourceCoreCompatibleCatalog.packTypes native) := by
  induction types generalizing native with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projected
    subst native
    rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at projected
    obtain ⟨first, projectedHead, projected⟩ := bind_ok projected
    obtain ⟨rest, projectedTail, projected⟩ := bind_ok projected
    cases projected
    cases tail with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projectedTail
      subst rest
      exact projectedHead
    | cons next suffix =>
      have remaining := ih projectedTail
      rw [List.mapM_cons] at projectedTail
      obtain ⟨nextNative, _, projectedTail⟩ := bind_ok projectedTail
      obtain ⟨suffixNative, _, projectedTail⟩ := bind_ok projectedTail
      cases projectedTail
      change (do pure (Ty.product (← catalog.project head)
        (← catalog.project (TypeSystem.Ty.productMany (next :: suffix))))) = _
      rw [projectedHead, remaining]
      rfl

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem prepared_outputs {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {specialized : SourceSpecialization.SpecializedFunction} {named : SourceCoreGeneralFunctions.Function}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named) :
    named.signature.key = specialized.key ∧
      representation.expressions.projectType (.declaration specialized.key.declaration)
        specialized.function.inferredBodyType = .ok named.signature.resultType := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (specialized.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged] at accepted
    cases shape : specialized.function.type <;>
      simp only [shape, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted <;>
      try contradiction
    rename_i parameter result
    by_cases mismatch : result ≠ specialized.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨parameterType, _, accepted⟩ := bind_ok accepted
      obtain ⟨resultType, projected, accepted⟩ := bind_ok accepted
      obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
      cases accepted
      have resultEq : result = specialized.function.inferredBodyType := Classical.byContradiction mismatch
      exact ⟨rfl, by simpa only [resultEq] using mapError_ok projected⟩


variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)

include prepared

theorem instantiated_of_catalog
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    Dynamic.FunctionInstantiates (Program.ofChecked compiled.sourceProgram)
      (CallableNamedMetadata.instantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, resolved, accepted⟩ := prepared.origin
  exact RecursiveNamedSpecializationValidity.instantiated signatureMember genericMember accepted
    (catalog.function_parameters signature signatureMember).1 range

theorem source_frame_of_catalog
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) (CallableNamedMetadata.instantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view := by
  refine ⟨instantiated_of_catalog prepared catalog range, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · exact congrArg (fun row => row.function.typedBody) prepared.same
  · exact congrArg (fun row => (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row).context) prepared.same
  · exact congrArg (fun row => row.function.typedBody.inputs) prepared.same
  · exact congrArg (fun row => row.function.inferredBodyType) prepared.same
  · change Dynamic.StatementRoots row.function.typedBody.roots prepared.compilation.statements
    simpa only [prepared.same] using RecursiveNamedPreparedSourceFrames.compiled_roots prepared.compilation
  · exact CallableEvidenceEnvironment.resolved_covers rfl prepared.resolved

theorem retained_frame_of_catalog
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) (CallableNamedCanonicalOrder.retainedInstantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view := by
  have frame := source_frame_of_catalog prepared catalog range
  exact ⟨RecursiveNamedRetainedSubstitutionFacts.retained_instantiates frame.instantiated,
    frame.source, frame.context, frame.parameters, frame.result, frame.captured, frame.roots, frame.covers⟩

theorem parameter_pack_of_certificate
    {types : List TypeSystem.Ty} {lexical : SourceSemantics.Context} {facts : BodyFacts}
    (certified : Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      (CallableNamedMetadata.instantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      types lexical facts) :
    prepared.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (prepared.named.inputs.map Prod.snd) := by
  have raw := Dynamic.MonoBindersExtend.bodyTypes_eq certified.typing.inputs_extend
  have binders := prepared.agreement.parameters
  have sameInputs : row.function.typedBody.inputs = prepared.named.inputs.map Prod.fst := by
    simpa only [RecursiveNamedPublicSpecializationMeaning.Prepared.view,
      RecursiveNamedPreparedSourceFrames.view, prepared.same] using binders
  change row.function.typedBody.inputs.map (fun binder => binder.scheme.body) = types at raw
  rw [sameInputs] at raw
  simp only [List.map_map, Function.comp_def] at raw
  have shape := certified.callable_type
  change row.function.type = .function (TypeSystem.Ty.productMany types) row.function.inferredBodyType at shape
  rw [← raw] at shape
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled prepared.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  have sourceShape : specialized.function.type = .function
      (TypeSystem.Ty.productMany (prepared.named.inputs.map (fun binding => binding.1.scheme.body)))
      specialized.function.inferredBodyType := by
    rw [same.symm.trans prepared.same]
    exact shape
  have projected := RecursiveNamedHeaderParameterProjections.prepared_parameter accepted sourceShape
  have realProjected := CompatibleExpressionReads.projectType_of_accepted projected
  have vector := project_productMany
    (RecursiveNamedPreparedParameterProjections.cached_projected compiled prepared.selected)
  exact Except.ok.inj (realProjected.symm.trans vector)


private theorem outputs : prepared.named.signature.key = row.key ∧
    compiled.compatible.checked.catalog.project prepared.view.resultType = .ok prepared.named.signature.resultType := by
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled prepared.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  obtain ⟨key, result⟩ := prepared_outputs accepted
  have projected := CompatibleExpressionReads.projectType_of_accepted result
  refine ⟨key.trans (congrArg (·.key) (same.symm.trans prepared.same)), ?_⟩
  change compiled.compatible.checked.catalog.project prepared.named.specialized.function.inferredBodyType = _
  rw [same]
  exact projected


theorem header_of_certificate {values : SourceCoreCompatibleValues.Context}
    {types : List TypeSystem.Ty} {context : SourceSemantics.Context} {facts : BodyFacts}
    (certified : Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      (CallableNamedMetadata.instantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      types context facts)
    {instantiation : DeclarationInstantiation}
    (frame : NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) instantiation
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation =
      .ok prepared.named.signature.key) :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram), HeaderAt prepared instantiation header := by
  have extended : MonoBindersExtend prepared.view.source.owner prepared.view.context
      prepared.view.parameters types context := by
    rw [frame.source, frame.context, frame.parameters]
    exact certified.typing.inputs_extend
  have unique : NodeOccurrencesUnique prepared.view.source := by
    rw [frame.source]
    exact certified.graph_closed.wellFormed.nodeOccurrencesUnique
  have bodyTyped : BodyHasType prepared.view.source context prepared.view.resultType facts := by
    rw [frame.source, frame.result]
    exact certified.typing.body_typed
  have ordinary : ∀ binder, binder ∈ prepared.view.parameters → binder.comptime = false := by
    simpa only [RecursiveNamedPublicSpecializationMeaning.Prepared.view,
      RecursiveNamedPreparedSourceFrames.view, prepared.same] using ordinaryParameters
  have originalLedger : ScopedRequirementLedgerWellFormed prepared.view.context prepared.view.source := by
    simpa only [frame.context, frame.source] using certified.requirement_ledger
  have ledger := (RecursiveNamedInitialContextValidity.mono_fields extended).scopedRequirementLedger originalLedger
  have valid : CompatibleRuntimeContextValidity.Valid
      prepared.named.specialized.function.solvedRequirements context prepared.view.evidence :=
    ⟨(RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements,
      ledger.toRuntime, RecursiveNamedInitialContextValidity.covers frame extended⟩
  let header := Header.of_dictionary_body
    (values := values)
    (function := prepared.view) (instantiation := instantiation)
    (sourceBody := RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
    (frame := frame) (named := prepared.named) (agreement := prepared.agreement)
    (ordinaryReturn := by simpa only [prepared.same] using ordinaryReturn)
    (ordinaryParameters := ordinary) (target := target)
    (context := context) (types := types) (bindings := prepared.named.inputs)
    (parameters := prepared.agreement.parameters) (inputs := prepared.agreement.parameters)
    (extended := extended) (solved := prepared.named.specialized.function.solvedRequirements)
    (reasonAt := prepared.diagnostics.reasonAt prepared.named.signature.key)
    (readFuel := compiled.indexed.fuel) (output := prepared.named.signature.resultType)
    (policy := policy prepared) (fuel := compiled.indexed.fuel)
    (fellThrough := prepared.compilation.own.fellThroughReason)
    (escaped := prepared.compilation.own.table.escapedReason)
    (body := prepared.compilation.body) (parameterCode := prepared.compilation.parameterCode)
    (code := prepared.compilation.output) (layouts := compiled.indexed.layouts)
    (owner := prepared.named.signature.key) (active := []) (globals := compiled.indexed.base.globals.length)
    (onError := fun error => .sourceAllocation (reprStr error))
    (acceptedPrefix := prepared.compilation.parametersCompiled) (hook := prepared.compilation.hook)
    (definitions_eq := rfl) (registered := CallableIndexedAmbient.frame_registered compiled.indexed)
    (unique := unique) (parameterType := parameter_pack_of_certificate prepared certified)
    (resultType := rfl) (representation := CallableIndexedNamedGeneration.representation compiled.indexed)
    (compiledFuel := compiled.indexed.fuel) (compiled := compiled.indexed.secondPass)
    (slot := prepared.index) (selected := prepared.selected)
    (cached := prepared.cached.trans (congrArg some prepared.compilation.emitted))
    (valid := valid)
  refine ⟨header, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    prepared.compilation.bodyCompiled, ⟨facts, bodyTyped⟩, (outputs prepared).2⟩


/-- Selected original body typing constructs the retained Header from the same
accepted compiler action, dictionary and complete parameter substitution. -/
theorem retained_header
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key)
    {values : SourceCoreCompatibleValues.Context} :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram),
      HeaderAt prepared (CallableNamedCanonicalOrder.retainedInstantiation row) header := by
  obtain ⟨types, context, facts, certificate⟩ := bodies.prepared_certificate prepared range
  exact header_of_certificate prepared certificate (retained_frame_of_catalog prepared bodies.signatures range)
    ordinaryReturn ordinaryParameters target

/-- The same instance certificate authenticates all selected diagnostics. -/
theorem diagnostic_typed (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    EmittedDiagnosticTokenPlan.UnaryTyped (CallableIndexedNamedGeneration.source prepared.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (CallableIndexedNamedGeneration.source prepared.named) := by
  obtain ⟨types, context, facts, certificate⟩ := bodies.prepared_certificate prepared range
  have typed := SourceDiagnosticTyping.diagnostic_typed_of_certificate certificate.toBodyInstanceTypingCertificate
  change EmittedDiagnosticTokenPlan.UnaryTyped row.function.typedBody ∧
    AssignmentDiagnosticOrigins.OperandsTyped row.function.typedBody at typed
  simpa only [CallableIndexedNamedGeneration.source, prepared.same] using typed

open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
open CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies
open CallableIndexedOwnedSelectedNamedHeaderReceipts (reissued reissued_view reason_at)

theorem retained_at_prepared (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key) :
    ∃ (selected : SelectedReceipt compiled prepared.named prepared.index)
      (header : CallableIndexedOwnedFunctionValues.Header compiled
        (Program.ofChecked compiled.sourceProgram)),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt (reissued prepared selected)
        (CallableNamedCanonicalOrder.retainedInstantiation row) header ∧
      header.function = prepared.view ∧ header.reasonAt = reasonAt selected := by
  obtain ⟨selected⟩ := at_selected prepared.selected (diagnostic_typed prepared bodies range)
  obtain ⟨header, aligned⟩ :=
    retained_header
      (reissued prepared selected) bodies range ordinaryReturn ordinaryParameters target
  exact ⟨selected, header, aligned, aligned.function.trans (reissued_view prepared selected),
    reason_at prepared selected aligned⟩


/-- Every authentic retained Header keeps a complete instance certificate at
its own parameter row and lexical context. -/
theorem certificate_at
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    {values : SourceCoreCompatibleValues.Context}
    {header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram)}
    (aligned : HeaderAt prepared (CallableNamedCanonicalOrder.retainedInstantiation row) header) :
    ∃ facts, Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      header.instantiation header.sourceBody header.types header.context facts := by
  obtain ⟨types, context, facts, certificate⟩ := bodies.prepared_certificate prepared range
  have retained : Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      (CallableNamedCanonicalOrder.retainedInstantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      types context facts :=
    { certificate.toBodyInstanceTypingCertificate with callable_type := certificate.callable_type }
  rw [← aligned.metadata, ← aligned.sourceBody] at retained
  have extended : MonoBindersExtend header.sourceBody.source.owner header.sourceBody.context
      header.sourceBody.source.inputs header.types header.context := by
    simpa only [header.frame.source, header.frame.context, header.frame.parameters] using header.extended
  have typesEq : header.types = types :=
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended).symm.trans
      (Dynamic.MonoBindersExtend.bodyTypes_eq retained.typing.inputs_extend)
  have contextEq : header.context = context :=
    Dynamic.MonoBindersExtend.functional extended retained.typing.inputs_extend
  rw [typesEq, contextEq]
  exact ⟨facts, retained⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaders
