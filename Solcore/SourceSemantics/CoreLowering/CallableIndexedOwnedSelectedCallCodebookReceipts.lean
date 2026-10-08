import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts

/-! The exact selected decision keeps its original codebook request, argument
count, ledger entry and guard provenance. Public preparation supplies the actual
original sidecar list and generated rows. Source occurrence uniqueness identifies
the same call and ordered arguments. These are static receipts; no child
execution, stage verdict, native type inference or invocation law is supplied. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallCodebookReceipts
open Core Frontend SourceInference SourceCoreStageCodebook
open DataPatternValues CallCodebookCertificates

private theorem output_requested {α β : Type} {relation : α → β → Prop}
    {inputs : List α} {outputs : List β} (related : ListRel relation inputs outputs)
    {output : β} (member : output ∈ outputs) :
    ∃ input, input ∈ inputs ∧ relation input output := by
  induction related with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨input, requested, generated⟩ := ih member
      exact ⟨input, List.mem_cons_of_mem _ requested, generated⟩

private theorem request_source {sidecars : List Sidecar} {entries : List Entry}
    {request : Request} (member : request ∈ requests sidecars entries) :
    request.sidecar ∈ sidecars ∧ request.entry ∈ entries ∧ ∃ node callee metadata,
      ContainsExpression request.sidecar.source request.call node ∧
      node.form = .call callee request.arguments (.indirect metadata) := by
  obtain ⟨sidecar, present, inSource⟩ := List.mem_flatMap.mp member
  obtain ⟨sourceNode, nodePresent, requested⟩ := List.mem_flatMap.mp inSource
  cases sourceNode with
  | statement => cases requested
  | expression node =>
    cases node with
    | mk id span type form requirements coercions localStart =>
      cases form <;> try cases requested
      rename_i callee arguments resolution
      cases resolution <;> try cases requested
      obtain ⟨entry, entryPresent, same⟩ := List.mem_map.mp requested
      cases same
      exact ⟨present, entryPresent, _, _, _, ⟨nodePresent, rfl⟩, rfl⟩

/-- The full original Generated receipt retains the same selected ledger entry,
prepared guard or builtin branch, and the physical argument count. -/
structure Selected (sidecar : Sidecar) (site : SourceCoreCallableContracts.Callsite)
    (callee : ExpressionId) (arguments : List ExpressionId)
    (metadata : IndirectCallResolution) (node : ExpressionNode) (row : Decision) : Prop where
  contains : ContainsExpression sidecar.source site.call node
  form : node.form = .call callee arguments (.indirect metadata)
  found : site.rowAt? row.entry.id = some row
  member : row.entry ∈ site.table.entries
  generated : Generated ⟨sidecar, site.call, arguments, row.entry⟩ row
  authenticated : CallEntryCertificates.Authenticated sidecar.plan row.entry

/-- The actual public codebook and actual selected row construct all fields.
No independently supplied row count or arbitrary accepted guard is needed. -/
theorem selected_at {program : CheckedProgram} {plan : Plan}
    {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {site : SourceCoreCallableContracts.Callsite}
    {sidecar : Sidecar} {node : ExpressionNode} {callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {descriptor : Word} {row : Decision}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok site.table)
    (caller : SourceCoreStageContracts.prepareSidecar plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (unique : NodeOccurrencesUnique sidecar.source)
    (selected : site.rowAt? descriptor = some row) :
    Selected sidecar site callee arguments metadata node row := by
  obtain ⟨inTable, atSite⟩ := List.mem_filter.mp (List.mem_of_find?_eq_some selected)
  have sites : row.caller = site.caller ∧ row.call = site.call := of_decide_eq_true atSite
  obtain ⟨sidecars, original, collected⟩ := prepareWithProjection_collects accepted
  obtain ⟨request, requested, generated⟩ :=
    output_requested (collectDecisions_certifies collected) inTable
  obtain ⟨sidecarMember, entryMember, actualNode, actualCallee, actualMetadata, actualContains, actualForm⟩ :=
    request_source requested
  have key : request.sidecar.caller.key = site.caller := generated.caller.symm.trans sites.1
  have actualCaller := original request.sidecar sidecarMember
  rw [key] at actualCaller
  have sameSidecar := Except.ok.inj (actualCaller.symm.trans caller)
  have actualContains : ContainsExpression sidecar.source site.call actualNode := by
    rw [sameSidecar, ← generated.call, sites.2] at actualContains
    exact actualContains
  have sameNode := Option.some.inj
    ((lookupExpression?_complete unique actualContains).symm.trans (lookupExpression?_complete unique contains))
  have sameArguments : request.arguments = arguments := by
    have shapes := actualForm.symm.trans ((congrArg ExpressionNode.form sameNode).trans form)
    exact (ExpressionForm.call.inj shapes).2.1
  have exactRequest : request = ⟨sidecar, site.call, arguments, row.entry⟩ := by
    cases request
    simp only at sameSidecar generated sameArguments
    cases sameSidecar
    cases generated.call.symm.trans sites.2
    cases sameArguments
    cases generated.entry
    rfl
  have authentic := CallEntryCertificates.prepareWithProjection_authenticates accepted
    row.entry (generated.entry.symm ▸ entryMember)
  have samePlan := (CallContractCertificates.sidecar_of_accepted caller).1
  have descriptorEq : descriptor = row.entry.id :=
    beq_iff_eq.mp (List.find?_some (p := fun decision : Decision => descriptor == decision.entry.id) selected)
  exact ⟨contains, form, descriptorEq ▸ selected, generated.entry.symm ▸ entryMember,
    exactRequest ▸ generated, samePlan.symm ▸ authentic⟩

/-- The existing actual compiled preparation supplies the public factory
receipt; the selected original caller source remains explicit. -/
theorem selected_at_prepared {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (prepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    {site : SourceCoreCallableContracts.Callsite} {sidecar : Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution} {descriptor : Word} {row : Decision}
    (table : site.table = native.table)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (unique : NodeOccurrencesUnique sidecar.source)
    (selected : site.rowAt? descriptor = some row) :
    Selected sidecar site callee arguments metadata node row := by
  have accepted := prepared.accepted
  rw [← table] at accepted
  exact selected_at accepted caller contains form unique selected

/-- The projected ledger keeps the exact selected guard/builtin receipts. -/
theorem Selected.ledger {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {row : Decision}
    (receipt : Selected sidecar site callee arguments metadata node row) :
    Nonempty (CallableLedger.Row sidecar site site.call arguments row.entry) :=
  ⟨⟨row, receipt.found, rfl, receipt.generated.user, receipt.generated.builtin⟩⟩

/-- This physical list length is the original generated request count. -/
theorem Selected.argument_count {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {row : Decision}
    (receipt : Selected sidecar site callee arguments metadata node row) :
    row.argumentCount = arguments.length := receipt.generated.argumentCount

/-- Authentication keeps the original user contract's full parameter count. -/
theorem Selected.parameter_count {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {row : Decision} {contract : Contract}
    (receipt : Selected sidecar site callee arguments metadata node row)
    (retained : row.entry.contract = some contract) :
    row.entry.parameterCount = contract.parameters.length := by
  have authenticated := receipt.authenticated
  unfold CallEntryCertificates.Authenticated at authenticated
  generalize origin : row.entry.origin = actualOrigin at authenticated
  generalize count : row.entry.parameterCount = actualCount at authenticated
  generalize attached : row.entry.contract = actualContract at authenticated
  cases authenticated <;> rw [retained] at attached <;> cases attached <;> rfl

/-- Genuine selected entry arity closes only the independent second gate.
The first guard's stage decision is unchanged and remains separate. -/
theorem Selected.before_application {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {row : Decision}
    (receipt : Selected sidecar site callee arguments metadata node row)
    (count : row.entry.parameterCount = arguments.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown row.entry.id = none := by
  rw [site.decision_known .beforeApplication unknown row.entry.id row receipt.found]
  exact SourceCoreCallableContracts.reason_accepted row site.reasonAt .beforeApplication
    (row.afterArguments_ok (count.trans receipt.argument_count.symm))

/-- Original closure contract binding and real arity close the second gate;
no Source parameter count is inferred from a packed native type. -/
theorem Selected.before_application_for_closure {sidecar : Sidecar}
    {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {row : Decision} {contract : Contract}
    {function : Dynamic.Closure}
    (receipt : Selected sidecar site callee arguments metadata node row)
    (retained : row.entry.contract = some contract)
    (bound : CallableLedger.Binds sidecar.plan (.closure function)
      (CallContractCertificates.semanticContract contract))
    (arity : function.parameters.length = arguments.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown row.entry.id = none := by
  cases bound with
  | closure parameters _ =>
    exact receipt.before_application
      ((receipt.parameter_count retained).trans ((congrArg List.length parameters).trans arity)) unknown

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallCodebookReceipts
