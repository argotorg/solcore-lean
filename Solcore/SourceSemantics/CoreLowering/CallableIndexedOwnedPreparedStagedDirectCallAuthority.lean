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
  have selected := (NamedCalls.selected_signature_target receipt.selected).2
  rw [globals] at selected
  obtain ⟨header, member, slot, signature⟩ := complete receipt.index receipt.signature selected
  have record := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  rw [signature, ← plan] at record
  have specialized : header.named.specialized = receipt.specialized :=
    Except.ok.inj (record.symm.trans receipt.record)
  have occurrence := CallableNamedMetadata.matches_of_exact
    (NamedCalls.selected_signature_target receipt.selected).1 receipt.record
  have headerTarget := header.target
  rw [signature, ← plan] at headerTarget
  have headerMatch := CallableNamedMetadata.matches_of_exact headerTarget receipt.record
  have occurrenceEq := occurrence.retained_canonical
    (receipt.ordinary.ordered _ _ (NamedCalls.selected_signature_target receipt.selected).1 receipt.record)
  have headerEq := headerMatch.retained_canonical (by
    simpa only [← specialized] using ordered header member)
  exact ⟨⟨header, member, slot, signature, specialized, occurrenceEq.trans headerEq.symm⟩⟩

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
  sourceEvidence : function.evidence = []
  headerEvidence : toReady.header.function.evidence = []

/-- The real retained Inventory supplies all preparation and Source provenance.
No new public execution premise or unrelated native run is needed. -/
theorem of_inventory {inputs : List (Input compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers rows))
    (plan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals) :
    Nonempty (Port receipt (headers rows)) := by
  obtain ⟨ready⟩ := of_complete receipt complete plan globals
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
  have empty : packet.header.function.evidence = [] :=
    CallableIndexedOwnedPreparedOrdinaryNamedEvidenceReceipts.selected_evidence_empty
      sourceAt plan ((congrArg (fun header => header.named.signature) same).trans ready.signature) receipt.selected
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
            sourceEvidence := sourceAt.dictionary.symm.trans empty
            headerEvidence := same ▸ empty }⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
