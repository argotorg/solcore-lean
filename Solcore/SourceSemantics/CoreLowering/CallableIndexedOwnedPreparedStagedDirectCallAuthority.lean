import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts

/-! Static direct-call authority is recovered from the exact compiler action
and actual finite inventory. Complete signatures identify physical slots;
accepted specialization records and full metadata identify Source functions.
No runtime global slot, capture, execution or body law is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

/-- A caller's exact executable resolver result and complete semantic dictionary.
This receipt does not require an ordinary Source declaration or Header. -/
structure ResolvedCaller (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (evidence : Dynamic.EvidenceEnvironment) where
  available : SourceTypedRuntime.RuntimeEvidenceEnvironment
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available
  dictionary : evidence = CallableNamedMetadata.environment available

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {program : Program}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id callee ids
    instantiation reasonAt lowered)

structure Ready (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled program)) where
  header : CallableIndexedOwnedFunctionValues.Header compiled program
  member : header ∈ catalog
  slot : header.slot = receipt.index
  signature : header.named.signature = receipt.signature
  specialized : header.named.specialized = receipt.specialized
  metadata : instantiation = header.instantiation

/-- The actual matching record and each authentic Header retain the Source
inference order. Their complete metadata then agrees, including nonempty
substitutions; declaration keys alone do not determine this equality. -/
theorem of_slot
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    (covered : ∃ header ∈ catalog,
      header.slot = receipt.index ∧ header.named.signature = receipt.signature)
    (plan : compilation.plan = compiled.indexed.base.plan)
    (ordered : ∀ header, header ∈ catalog →
      header.instantiation.parameterSubstitution.map Prod.fst =
        (header.named.specialized.parameterSubstitution.map Prod.fst).reverse) :
    Nonempty (Ready receipt catalog) := by
  obtain ⟨header, member, slot, signature⟩ := covered
  have record := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  rw [signature, ← plan] at record
  have specialized : header.named.specialized = receipt.specialized :=
    Except.ok.inj (record.symm.trans receipt.record)
  have occurrence := CallableNamedMetadata.matches_of_exact
    receipt.target receipt.record
  have headerTarget := header.target
  rw [signature, ← plan] at headerTarget
  have headerMatch := CallableNamedMetadata.matches_of_exact headerTarget receipt.record
  have occurrenceEq := occurrence.retained_canonical
    (receipt.supported.ordered _ _ receipt.target receipt.record)
  have headerEq := headerMatch.retained_canonical (by
    simpa only [← specialized] using ordered header member)
  exact ⟨⟨header, member, slot, signature, specialized, occurrenceEq.trans headerEq.symm⟩⟩

theorem of_complete
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) catalog)
    (plan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    (ordered : ∀ header, header ∈ catalog →
      header.instantiation.parameterSubstitution.map Prod.fst =
        (header.named.specialized.parameterSubstitution.map Prod.fst).reverse) :
    Nonempty (Ready receipt catalog) := by
  have selected := receipt.global
  rw [globals] at selected
  exact of_slot receipt (complete receipt.index receipt.signature selected) plan ordered

/-- Independently typed declaration application fixes the original parameter
row and return type of the selected Header. Native packed types are unused. -/
theorem Ready.source_types
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    (ready : Ready receipt catalog) {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty}
    (wellFormed : ProgramWellFormed program)
    (signatures : context.signatures = program.signatures)
    (application : DeclarationApplicationValid context instantiation types
      receipt.node.type instantiation.predicates) :
    types = ready.header.bindings.map (fun binding => binding.1.scheme.body) ∧
      receipt.node.type = ready.header.function.resultType := by
  cases application with
  | intro member admissible declaration parameters result functionType predicates =>
    have shape := RecursiveNamedSourceSignatureFacts.header_shape ready.header wellFormed
      (signatures ▸ member) (by rw [← ready.metadata]; exact declaration)
    rw [← ready.metadata] at shape
    exact ⟨parameters.symm.trans shape.1, result.symm.trans shape.2⟩

/-- A selected finite row retains its authentic preparation, reissued diagnostic
Header and complete Source dictionary. Runtime capture/slot authority remains
separate and must come from the actual caller packet. -/
structure Port (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram))) extends Ready receipt catalog where
  row : SourceSpecialization.SpecializedFunction
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation toReady.header
  rawDictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  function : Dynamic.GlobalFunction
  sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt toReady.header rawDictionary function
  sourceInstantiation : function.instantiation = instantiation
  dictionary : function.evidence = prepared.view.evidence

/-- The real retained Inventory supplies all preparation and Source provenance.
No new public execution premise or unrelated native run is needed. -/
theorem of_inventory_at {inputs : List (Input compiled)} (rows : Inventory inputs)
    (covered : ∃ header ∈ headers rows,
      header.slot = receipt.index ∧ header.named.signature = receipt.signature)
    (plan : compilation.plan = compiled.indexed.base.plan) :
    Nonempty (Port receipt (headers rows)) := by
  obtain ⟨ready⟩ := of_slot receipt covered plan
    (CallableIndexedOwnedPreparedFiniteNamedInventories.ordered rows)
  obtain ⟨input, packet, _retained, same⟩ := rows.mem_headers ready.header ready.member
  have aligned := packet.aligned
  have metadata : (CallableNamedCanonicalOrder.retainedInstantiation input.row) = instantiation :=
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
  refine ⟨{ toReady := ready
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

theorem of_inventory {inputs : List (Input compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers rows))
    (plan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals) :
    Nonempty (Port receipt (headers rows)) := by
  have selected := receipt.global
  rw [globals] at selected
  exact of_inventory_at receipt rows (complete receipt.index receipt.signature selected) plan

/-- Full Source evidence is produced and identified at the actual caller
context. It contains no Source or native body execution premise. -/
structure EvidenceAt {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (port : Port receipt catalog) (context : SourceSemantics.Context)
    (caller : Dynamic.EvidenceEnvironment) : Prop where
  produces : Dynamic.DirectCallProducesEvidence context caller receipt.node.requirements []
    instantiation.predicates port.function.evidence
  agrees : ∀ evidence, Dynamic.DirectCallProducesEvidence context caller receipt.node.requirements []
    instantiation.predicates evidence → evidence = port.function.evidence

structure PortWithEvidence (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram)))
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment)
    extends Port receipt catalog where
  evidence : EvidenceAt receipt toPort context caller

/-- Empty predicates imply the actual prepared dictionary is empty. The full
selected metadata, issued Header and resolver establish this equality. -/
theorem ordinary_evidence
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (port : Port receipt catalog)
    (ordinary : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Ordinary compilation.plan instantiation)
    (requirements : receipt.node.requirements = [])
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment) :
    EvidenceAt receipt port context caller := by
  have same : port.row = receipt.specialized :=
    port.prepared.same.symm.trans
      ((congrArg (fun named => named.specialized) port.aligned.named).symm.trans port.specialized)
  have metadata := CallableNamedMetadata.matches_of_exact receipt.target receipt.record
  have assumptions : port.row.assumptions = [] := by
    rw [same]
    exact metadata.predicates.trans ordinary.predicates
  have empty : port.function.evidence = [] :=
    port.dictionary.trans (RecursiveNamedPreparedHeaders.Prepared.evidence_empty port.prepared assumptions)
  constructor
  · rw [requirements, ordinary.predicates, empty]
    exact .intro (selected := []) (contextual := []) rfl rfl .nil
  · intro evidence produced
    cases produced with
    | intro _ _ produced =>
      have length := produced.length_eq.2
      rw [ordinary.predicates] at length
      exact (List.length_eq_zero_iff.mp length.symm).trans empty.symm

/-- The exact caller resolver and genuine selected callee identify the full
produced dictionary. Reached lexical fields retain the original ledger IDs. -/
theorem authenticated_evidence_of_resolved
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (port : Port receipt catalog)
    {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
    {child : SourceCoreEvidence.Child} {budget : Nat} {callables : SourceCoreFunctions.CallablePolicy}
    (actual : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
      child budget source scope id callee ids instantiation reasonAt callables receipt.node lowered)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (resolvedCaller : ResolvedCaller compiled.sourceProgram caller callerEvidence)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context) :
    EvidenceAt receipt port context callerEvidence := by
  have key : actual.selection.key = receipt.signature.key :=
    actual.selection.key_eq.trans (Except.ok.inj (actual.selection.targetSelected.symm.trans receipt.target))
  have record : SourceCompilationPlan.exactSpecialization compilation.plan receipt.signature.key =
      .ok actual.selection.specialized := by
    rw [← key]
    exact actual.selection.selected
  have same : port.row = actual.selection.specialized :=
    port.prepared.same.symm.trans
      ((congrArg (fun named => named.specialized) port.aligned.named).symm.trans
        (port.specialized.trans (Except.ok.inj (receipt.record.symm.trans record))))
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
    simpa only [receipt.metadata.coercions, input, output, resolvedCaller.dictionary] using produced
  · intro evidence produced
    have produced : Dynamic.DirectCallProducesEvidence context
        (CallableNamedMetadata.environment actual.selection.available) receipt.node.requirements receipt.node.coercions
        instantiation.predicates evidence := by
      simpa only [receipt.metadata.coercions, input, resolvedCaller.dictionary] using produced
    exact (actual.selection.direct_agrees ledger
      (CallableCallRequirementLayouts.singletons_of_unique ledger unique) produced).trans output

/-- The ordinary prepared caller supplies the same general resolver receipt. -/
theorem authenticated_evidence
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (port : Port receipt catalog)
    {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
    {child : SourceCoreEvidence.Child} {budget : Nat} {callables : SourceCoreFunctions.CallablePolicy}
    (actual : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
      child budget source scope id callee ids instantiation reasonAt callables receipt.node lowered)
    (callerPrepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled caller)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (callerDictionary : callerEvidence = callerPrepared.view.evidence) :
    EvidenceAt receipt port context callerEvidence := by
  exact authenticated_evidence_of_resolved receipt port actual
    ⟨callerPrepared.available, callerPrepared.resolved, callerDictionary⟩
    signatures ledger assumptions unique

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
