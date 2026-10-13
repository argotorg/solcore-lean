import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority

/-! Actual direct-call output-coercion receipts identify the selected ordinary
Header before the suffix runs. The raw operand, final output and original
requirement partition remain distinct. No method is represented by a Header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectAuthority
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (ResolvedCaller)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {budget : Nat}
  {source : TypedSource} {scope : SourceCoreBasic.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (actual : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    child budget source scope id callee ids instantiation reasonAt callables node output)

/-- The physical slot comes from the actual unique lookup made by the compiler. -/
theorem native_selected :
    compilation.globals[actual.native.index]? = some actual.native.signature ∧
      actual.native.signature.key = actual.selection.key := by
  have member : (actual.native.signature, actual.native.index) ∈
      compilation.globals.zipIdx.filter (fun row => decide (row.1.key = actual.selection.key)) := by
    rw [actual.native.global]
    exact List.mem_singleton.mpr rfl
  have selected := List.mem_filter.mp member
  exact ⟨List.mk_mem_zipIdx_iff_getElem?.mp selected.1,
    by simpa only [decide_eq_true_eq] using selected.2⟩

theorem target : SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation =
    .ok actual.native.signature.key := by
  rw [actual.selection.targetSelected]
  exact congrArg Except.ok (actual.selection.key_eq.symm.trans (native_selected actual).2.symm)

theorem record : SourceCompilationPlan.exactSpecialization compilation.plan actual.native.signature.key =
    .ok actual.selection.specialized := by
  rw [(native_selected actual).2]
  exact actual.selection.selected

structure Ready (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram))) where
  supported : Supported compilation.plan instantiation
  header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)
  member : header ∈ catalog
  slot : header.slot = actual.native.index
  signature : header.named.signature = actual.native.signature
  specialized : header.named.specialized = actual.selection.specialized
  metadata : instantiation = header.instantiation

/-- Complete retained Source metadata, including its original parameter order,
identifies the selected Header at this one covered slot. -/
theorem of_slot {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (supported : Supported compilation.plan instantiation)
    (covered : ∃ header ∈ catalog,
      header.slot = actual.native.index ∧ header.named.signature = actual.native.signature)
    (plan : compilation.plan = compiled.indexed.base.plan)
    (ordered : ∀ header, header ∈ catalog →
      header.instantiation.parameterSubstitution.map Prod.fst =
        (header.named.specialized.parameterSubstitution.map Prod.fst).reverse) :
    Nonempty (Ready actual catalog) := by
  obtain ⟨header, member, slot, signature⟩ := covered
  have actualRecord := record actual
  have actualTarget := target actual
  have headerRecord := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  rw [signature, ← plan] at headerRecord
  have specialized : header.named.specialized = actual.selection.specialized :=
    Except.ok.inj (headerRecord.symm.trans actualRecord)
  have occurrence := CallableNamedMetadata.matches_of_exact actualTarget actualRecord
  have headerTarget := header.target
  rw [signature, ← plan] at headerTarget
  have headerMatch := CallableNamedMetadata.matches_of_exact headerTarget actualRecord
  have occurrenceEq := occurrence.retained_canonical
    (supported.ordered _ _ actualTarget actualRecord)
  have headerEq := headerMatch.retained_canonical (by
    simpa only [← specialized] using ordered header member)
  exact ⟨⟨supported, header, member, slot, signature, specialized, occurrenceEq.trans headerEq.symm⟩⟩

theorem Ready.source_types
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (ready : Ready actual catalog) {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (application : DeclarationApplicationValid context instantiation types node.rawType instantiation.predicates) :
    types = ready.header.bindings.map (fun binding => binding.1.scheme.body) ∧
      node.rawType = ready.header.function.resultType := by
  cases application with
  | intro member admissible declaration parameters result functionType predicates =>
    have shape := RecursiveNamedSourceSignatureFacts.header_shape ready.header wellFormed
      (signatures ▸ member) (by rw [← ready.metadata]; exact declaration)
    rw [← ready.metadata] at shape
    exact ⟨parameters.symm.trans shape.1, result.symm.trans shape.2⟩

/-- The selected inventory row carries its real preparation and whole Source
dictionary. Capture authority remains the reached physical caller's receipt. -/
structure Port (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram))) extends Ready actual catalog where
  row : SourceSpecialization.SpecializedFunction
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation toReady.header
  rawDictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  function : Dynamic.GlobalFunction
  sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt toReady.header rawDictionary function
  sourceInstantiation : function.instantiation = instantiation
  dictionary : function.evidence = prepared.view.evidence

theorem of_inventory_at {inputs : List (Input compiled)} (rows : Inventory inputs)
    (supported : Supported compilation.plan instantiation)
    (covered : ∃ header ∈ headers rows,
      header.slot = actual.native.index ∧ header.named.signature = actual.native.signature)
    (plan : compilation.plan = compiled.indexed.base.plan) :
    Nonempty (Port actual (headers rows)) := by
  obtain ⟨ready⟩ := of_slot actual supported covered plan
    (CallableIndexedOwnedPreparedFiniteNamedInventories.ordered rows)
  obtain ⟨input, packet, _retained, same⟩ := rows.mem_headers ready.header ready.member
  have aligned := packet.aligned
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation input.row = instantiation :=
    aligned.metadata.symm.trans ((congrArg (·.instantiation) same).trans ready.metadata.symm)
  have aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt
      (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
      instantiation ready.header := by
    rw [← same, ← metadata]
    exact aligned
  have sourceAt := packet.sourceAt
  have sourceMetadata :
      (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized
        input.prepared.available)).instantiation = instantiation := by
    change CallableNamedCanonicalOrder.retainedInstantiation packet.header.named.specialized = instantiation
    rw [packet.aligned.named]
    change CallableNamedCanonicalOrder.retainedInstantiation input.prepared.named.specialized = instantiation
    rw [input.prepared.same]
    exact metadata
  exact ⟨{ toReady := ready
           row := input.row
           prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
           aligned := aligned
           rawDictionary := input.prepared.available
           function := CallableNamedReversal.global
             (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)
           sourceAt := same ▸ sourceAt
           sourceInstantiation := sourceMetadata
           dictionary := (same ▸ sourceAt).dictionary.symm.trans
             (congrArg Dynamic.Closure.evidence aligned.function) }⟩

/-- Evidence belongs to the original call and its full output-coercion
partition, before the selected named invocation starts. -/
structure EvidenceAt {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (port : Port actual catalog) (context : SourceSemantics.Context)
    (callerEvidence : Dynamic.EvidenceEnvironment) : Prop where
  produces : Dynamic.DirectCallProducesEvidence context callerEvidence node.requirements node.coercions
    instantiation.predicates port.function.evidence
  agrees : ∀ evidence, Dynamic.DirectCallProducesEvidence context callerEvidence node.requirements node.coercions
    instantiation.predicates evidence → evidence = port.function.evidence

structure PortWithEvidence (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram)))
    (context : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment)
    extends Port actual catalog where
  evidence : EvidenceAt actual toPort context callerEvidence

/-- Both dictionaries are authenticated by the real resolver and complete
selected record; Source agreement retains the original requirement IDs. -/
theorem authenticated_evidence_of_resolved
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (port : Port actual catalog)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (resolvedCaller : ResolvedCaller compiled.sourceProgram caller callerEvidence)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context) :
    EvidenceAt actual port context callerEvidence := by
  have same : port.row = actual.selection.specialized :=
    port.prepared.same.symm.trans
      ((congrArg (fun named => named.specialized) port.aligned.named).symm.trans port.specialized)
  have actualKey := (CallableNamedMetadata.specialization_of_exact actual.selection.selected).2
  have calleeDictionary : actual.selection.actual = port.prepared.available := by
    apply port.prepared.authenticated_dictionary
    simpa only [same, actualKey] using actual.selection.authenticated
  have input : actual.selection.available = resolvedCaller.available :=
    Except.ok.inj (actual.selection.resolved.symm.trans resolvedCaller.resolved)
  have output : CallableNamedMetadata.environment actual.selection.actual = port.function.evidence := by
    rw [calleeDictionary, port.dictionary]
    rfl
  constructor
  · have produced := actual.selection.direct_produces signatures ledger assumptions
    simpa only [input, output, resolvedCaller.dictionary] using produced
  · intro evidence produced
    have produced : Dynamic.DirectCallProducesEvidence context
        (CallableNamedMetadata.environment actual.selection.available) node.requirements node.coercions
        instantiation.predicates evidence := by
      simpa only [input, resolvedCaller.dictionary] using produced
    exact (actual.selection.direct_agrees ledger
      (CallableCallRequirementLayouts.singletons_of_unique ledger unique) produced).trans output

theorem of_resolved {inputs : List (Input compiled)} (rows : Inventory inputs)
    (supported : Supported compilation.plan instantiation)
    (covered : ∃ header ∈ headers rows,
      header.slot = actual.native.index ∧ header.named.signature = actual.native.signature)
    (plan : compilation.plan = compiled.indexed.base.plan)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (resolvedCaller : ResolvedCaller compiled.sourceProgram caller callerEvidence)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context) :
    Nonempty (PortWithEvidence actual (headers rows) context callerEvidence) := by
  obtain ⟨port⟩ := of_inventory_at actual rows supported covered plan
  exact ⟨{
    toPort := port
    evidence := authenticated_evidence_of_resolved actual port resolvedCaller
      signatures ledger assumptions unique
  }⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectAuthority
