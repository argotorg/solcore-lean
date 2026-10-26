import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedInputs
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceFacts
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchTreeHeads
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeChildrenExtension
import Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedMatchFlow
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAllocationReceipt
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog

/-! A match accepted by the actual compiler tree closes its mixed-cell flow.
The tree's match receipt supplies the certificate, the scrutinee lowering and
the finite branch requests; the enclosing tree induction supplies every branch
at its original Source context with the match's own control. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedMatches
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationAcceptedSourceFacts (head_form expression_node)

/-- Match compilation contexts of an actual body: the checked catalog's initial
values, the body's own marked allocator, and data definitions that the indexed
layouts extend. Both the base and the ambient callback contexts qualify. -/
def Admitted {whole : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : ActualBodyInvocation.BodyRelation}
    (index : ActualBodyInvocation.Index whole bodyRelation)
    (compilation : SourceCoreCompatibleDataMatches.Context) : Prop :=
  compilation.values = .initial whole.compatible.checked ∧
    compilation.sourceCells = index.policy.sourceCells ∧
    compilation.definitions.Extends whole.indexed.layouts.definitions

/-- The original compilation receipt's checker run fixes a well-formed
signature catalog for the compiled program. -/
theorem catalog {whole : SourceCoreUnifiedCompilation.Compiled}
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program) :
    SignatureCatalogWellFormed whole.compatible.checked.signatures := by
  rw [CallableIndexedOwnedPublicSignatureCatalog.signatures whole,
    (SourceCoreCompiler.Compiled.artifact_fields sourceCompiled artifact).1]
  exact SignatureCatalogWellFormed.ofCheckProgram checked

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

include bindings registered in
/-- Both directions for an accepted match head followed by its actual suffix.
Branch bounds are required only at the exact compiler requests and their
original Source contexts; the hidden scrutinee and every pattern binder are
non-inputs by the runtime ownership of the body's local identities. -/
theorem correct (budget : Nat)
    (expressions : CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    (catalog : SignatureCatalogWellFormed whole.compatible.checked.signatures)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {expected : TypeSystem.Ty} {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {stored : Ty}
    {resolution : MatchResolution} {matchedCode tail : Expr}
    {compilation : SourceCoreCompatibleDataMatches.Context}
    (reached : index.Reached (.statement id))
    (read : index.policy.readStatement index.compilerSource id = .ok (node, stored))
    (form : node.form = .matchWith resolution)
    (receipt : AcceptedNamedMatchFlow.Receipt index.policy compilation index.compilerSource scope id resolution
      index.result index.reasonAt escaped fuel matchedCode)
    (admitted : Admitted index compilation) (sameSource : index.compilerSource = index.source)
    (branches : ∀ request ∈ receipt.requests, ∀ {control : ControlContext} {context final : SourceSemantics.Context}
      {facts : BodyFacts}, control.returnType = expected →
      context.signatures = whole.compatible.checked.signatures →
      StatementsHaveType index.source control context request.statements final facts →
      (∃ nativeType, HasType (SourceCoreLocalCell.coreContext request.scope ++ administrative) request.code
        nativeType whole.indexed.layouts.definitions) →
      CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
        registry invocation faults administrative request.scope false request.statements expected index.result
        request.code budget ∧
      CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
        registry invocation faults administrative request.scope false request.statements expected index.result
        request.code budget)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (result : control.returnType = expected)
    (signatures : context.signatures = whole.compatible.checked.signatures)
    (typed : StatementsHaveType index.source control context (id :: rest) final facts)
    (native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative) matchedCode nativeType
      whole.indexed.layouts.definitions)
    (tailBounds : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index
        producer registry invocation faults administrative scope mode rest expected index.result tail budget ∧
      CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index
        producer registry invocation faults administrative scope mode rest expected index.result tail budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope mode (id :: rest) expected index.result
      (LocalLoop.sequence index.result matchedCode tail) budget ∧
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope mode (id :: rest) expected index.result
      (LocalLoop.sequence index.result matchedCode tail) budget := by
  have sourceUnique : NodeOccurrencesUnique index.source := sourceEq ▸ unique
  have statementFound := index.statement_read_reached reached read
  have statementAt : invocation.source.lookupStatement? id = some node := by
    rw [sourceEq]
    exact statementFound
  obtain ⟨_, _, formTyped, _⟩ := head_form sourceUnique typed statementFound
  rw [form] at formTyped
  have sourceFacts : ∃ type caseFacts, ExpressionHasType index.source context resolution.scrutinee type ∧
      MatchCasesHaveType index.source control context type resolution.cases caseFacts ∧
      (∀ statements, resolution.defaultBody = some statements →
        ∃ last bodyFacts, StatementsHaveType index.source control context statements last bodyFacts) := by
    cases formTyped with
    | matchWithoutDefault absent value casesTyped =>
      exact ⟨_, _, value, casesTyped, fun statements present => by simp_all⟩
    | matchWithDefault present value casesTyped defaultTyped =>
      exact ⟨_, _, value, casesTyped, fun statements selected => by
        cases Option.some.inj (present.symm.trans selected)
        exact ⟨_, _, defaultTyped⟩⟩
  obtain ⟨scrutineeType, caseFacts, value, casesTyped, defaultTyped⟩ := sourceFacts
  obtain ⟨scrutineeNode, scrutineeFound, nodeType, scrutineeTyped⟩ := expression_node sourceUnique value
  subst nodeType
  have found : invocation.source.lookupExpression? resolution.scrutinee = some scrutineeNode := by
    rw [sourceEq]
    exact scrutineeFound
  have typedAt : ExpressionHasType invocation.source context resolution.scrutinee scrutineeNode.type := by
    rw [sourceEq]
    exact scrutineeTyped
  have casesAt : MatchCasesHaveType invocation.source control context scrutineeNode.type resolution.cases
      caseFacts := by
    rw [sourceEq]
    exact casesTyped
  have defaultAt : ∀ statements, resolution.defaultBody = some statements →
      ∃ last bodyFacts, StatementsHaveType invocation.source control context statements last bodyFacts := by
    rw [sourceEq]
    exact defaultTyped
  have compilerFound : index.compilerSource.lookupExpression? resolution.scrutinee = some scrutineeNode := by
    rw [sameSource]
    exact scrutineeFound
  obtain ⟨valuesEq, cellsEq, extension⟩ := admitted
  have allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
      whole.indexed.ancestry.layout.frame whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))) :=
    cellsEq.trans index.sourceCells
  obtain ⟨nativeType, matchedNative⟩ := native
  have typedCertificate := CompatibleMatchNativeChildren.Certificate.typed_bodies_extended
    (fun error => .sourceAllocation (reprStr error)) allocator extension receipt.certificate matchedNative
  obtain ⟨requests, certificate, _, typedRequests⟩ :=
    GenericMatchChildren.Certificate.finite_children typedCertificate
  have contexts : ∀ request ∈ requests, ∀ childContext,
      GenericMatchChildren.ScopedContextFor invocation.source context
        (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases
        resolution.defaultBody request childContext →
      CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge childContext model index
        producer registry invocation faults administrative request.scope false request.statements expected
        index.result request.code budget ∧
      CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge childContext model index
        producer registry invocation faults administrative request.scope false request.statements expected
        index.result request.code budget := by
    intro request member childContext related
    obtain ⟨occurs, requestNative⟩ := typedRequests request member
    obtain ⟨_, _, childTyped⟩ := ScopedSourceMatchAdmission.request_typing casesAt defaultAt related.forget
    rw [sourceEq] at childTyped
    exact branches request occurs result (related.closed_fields.1.trans signatures) childTyped ⟨_, requestNative⟩
  cases compilation with
  | mk values solved sourceCells ambientDefinitions =>
  dsimp only at valuesEq
  subst valuesEq
  refine ⟨?_, ?_⟩
  · intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admission authority
      physical owner sameLocation ready finalContext outcome after trace
    obtain ⟨hiddenOrdinary, armsOrdinary⟩ :=
      ScopedSourceMatchAdmission.ordinary_bindings physical.ownership statementFound form
    have ordinary := CompatibleMatchSelectionPrefix.ordinary_of_source_ids certificate
      (index.compiler_noninput hiddenOrdinary)
      (fun arm member binder bound => index.compiler_noninput (armsOrdinary arm member binder bound))
    refine CellAwareInvocationMatchSequences.preserves bridge functions index producer sourceEq ?_ unique
      statementAt form (.inl tailBounds.1) within environments heaps locals agrees actualTyped sourceTyped
      runtime covers sameLedger initial admission authority physical owner sameLocation ready trace
    intro innerSize innerWithin
    exact CellAwareInvocationMatchTreeHeads.preserves bridge functions index
      (fun error => .sourceAllocation (reprStr error)) allocator rfl registered writes.extension certificate
      ordinary signatures catalog found typedAt sourceEq compilerFound rfl statementFound form casesAt defaultAt
      budget producer bindings unique
      (by
        intro childSize smaller childScope expression lowered certified
        rcases certified with ⟨rfl, rfl, rfl⟩
        exact (expressions receipt.childFuel context runtime covers sameLedger).1 childSize smaller
          receipt.generated)
      (fun request member childContext related _ => (contexts request member childContext related).1) innerWithin
  · intro size within mapping world actualContext environment canonical actual before store embedding value
      finalStore environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admission
      authority physical owner sameLocation ready completed
    obtain ⟨hiddenOrdinary, armsOrdinary⟩ :=
      ScopedSourceMatchAdmission.ordinary_bindings physical.ownership statementFound form
    have ordinary := CompatibleMatchSelectionPrefix.ordinary_of_source_ids certificate
      (index.compiler_noninput hiddenOrdinary)
      (fun arm member binder bound => index.compiler_noninput (armsOrdinary arm member binder bound))
    refine CellAwareInvocationMatchSequences.reflects bridge functions index producer sourceEq ?_
      statementAt form (.inl tailBounds.2) within environments heaps locals agrees actualTyped sourceTyped
      runtime covers sameLedger initial admission authority physical owner sameLocation ready completed
    intro innerSize innerWithin
    exact CellAwareInvocationMatchTreeHeads.reflects bridge functions index
      (fun error => .sourceAllocation (reprStr error)) allocator rfl registered writes.extension certificate
      ordinary signatures catalog found typedAt sourceEq compilerFound rfl statementFound form casesAt defaultAt
      budget producer bindings
      (by
        intro childSize smaller childScope expression lowered certified
        rcases certified with ⟨rfl, rfl, rfl⟩
        exact (expressions receipt.childFuel context runtime covers sameLedger).2 childSize smaller
          receipt.generated)
      (fun request member childContext related _ => (contexts request member childContext related).2) innerWithin

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedMatches
