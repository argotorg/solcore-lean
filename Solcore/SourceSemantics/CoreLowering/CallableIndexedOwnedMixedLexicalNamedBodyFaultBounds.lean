import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalFlowFaultBounds

/-! A genuine accepted lexical body consumes strict expression members from
one mixed family. The original Tree and finish retain their causal post and
actual body store, including declaration allocation and early faults. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open NamedLexicalFlowFaultPostContracts RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedMixedLexicalFlowFaultBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {expressionSyntax : ExpressionId → Prop} {flow : Expr}
  (validity : SourceSemantics.Context → Prop)

/-- The exact ordered-pool bridge used by the strict child contracts. -/
def bodyBridge :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

/-- The same literal static inputs without restricting the grammar profile. -/
structure BodyInputs : Prop where
  syntaxTree : GenericLexicalStatements.Syntax header.function.source expressionSyntax header.context true
    header.function.body header.function.resultType
  tree : GenericLexicalStatements.Tree compiled.indexed.layouts header.owner header.active
    compiled.indexed.ancestry.layout.frame header.globals header.onError (.initial compiled.compatible.checked)
    header.function.source certificates header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true
    header.function.body header.function.resultType header.output flow
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok flow
  projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output
  valid : validity header.context
  extend : ∀ {context nextContext binder}, validity context →
    BinderExtends header.function.source.owner context binder nextContext → validity nextContext


variable (inputs : BodyInputs (header := header) (certificates := certificates)
  (expressionSyntax := expressionSyntax) (flow := flow) validity)

include inputs in
private theorem BodyInputs.emitted :
    header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped := by
  have accepted := inputs.accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  rw [inputs.generated] at accepted
  exact Except.ok.inj accepted.symm

include inputs in
private theorem BodyInputs.transfers {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {sourceSize : Nat} {finalContext : SourceSemantics.Context} {control : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt sourceSize true program header.context header.function.evidence
      header.function.source environment before header.function.body finalContext control after) :
    ImperativeFunctionFinish.TransferFaults faults header.escaped control := by
  cases trace with
  | fault failed => constructor <;> intro next same <;> cases same
  | control executed =>
    cases GenericLexicalStatements.syntax_control_shape inputs.syntaxTree header.unique executed.sound <;>
      constructor <;> intro next same <;> cases same

variable (post : ExpressionFailurePostContracts.ExpressionFaultPost)
variable {locations : CallableIndexedOwnedFunctionValues.Header compiled program → Location} {capturePrefix : Nat}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (sourceReceipt : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current)

private theorem body_reference : entry.canonical[
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + header.globals]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) := by
  simpa only [List.length_map, List.length_reverse] using entry.reference

private theorem body_unmapped : frameLocation ∉ entry.mapping := by
  have unmapped := entry.catalog.authority.unmapped
  simpa only [entry.catalog_frame] using unmapped


include inputs sourceReceipt rows stable in
/-- The Source child is strictly smaller than the enclosing mixed member;
its real parameter state supplies admission and the stable allocation hook. -/
theorem source_body_with_post (outer size : Nat) (within : size < outer)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := post) (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) program header.function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates context)
        (context := context) (source := header.function.source) (faults := faults) child)
    : SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
      (faults := faults) entry reached size := by
    intro outcome after trace
    let bridge := bodyBridge (headers := headers) (keys := keys)
    let model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
    let producer := CallableIndexedOwnedAllocationProducer.producer headers keys model
    let condition := CallableIndexedOwnedAllocationProducer.StableOwner keys
    have meaning := flow_preserves bridge functions header.function.evidence
      post header.unique
      (layouts := compiled.indexed.layouts) (owner := header.owner) (active := header.active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
      (expressionSyntax := expressionSyntax) rfl header.registered condition producer
      (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      (fun _ _ seed => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner model seed)
      validity inputs.extend outer size size within (Nat.le_refl size) children inputs.tree
    have lifted := NamedLexicalFunctionFaultPostContracts.PreservesAtWith.of_lexical
      (protocol := protocol headers keys) (readiness := readiness bridge) (condition := condition)
      (facts := GenericLexicalStatements.Syntax header.function.source expressionSyntax)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (evidence := header.function.evidence)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      (meaning := meaning)
    have matchTree := GenericImperativeMatch.Tree.body
      (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      inputs.syntaxTree inputs.tree
    obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame,
      metadata, _exit, finalTransition, retained⟩ :=
      RecursiveNamedFunctionFinishBounds.WithReady.preserves_at_emitted_with_state_when_with_transfers_with_post
        (functions := functions) (program := program) (tree := matchTree) (projection := inputs.projection) (unique := header.unique)
        (FlowPost (post))
        (protocol headers keys) (readiness bridge) condition
        (GenericLexicalStatements.Syntax header.function.source expressionSyntax) (BodyInputs.emitted validity inputs)
        validity size lifted inputs.valid inputs.syntaxTree
        entry.environments entry.heaps sourceReceipt.locals entry.lookups entry.actualTyped
        (body_reference functions entry) entry.state.read (body_unmapped functions entry) reached stable
        (show Admission bridge header.context reached from ⟨sourceReceipt.heapTyped, rows⟩)
        (BodyInputs.transfers validity inputs) trace
    exact ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame,
      metadata, ProtectedStateTransition.FunctionFinish.Reached.forget finalTransition,
      ReachedNamedLexicalBodyFaultPaths.outcome_post_of_finished_for inputs.syntaxTree header.unique retained evaluated⟩


include inputs sourceReceipt rows stable in
/-- Native finish chooses its actual strict flow child. Reflection constructs
an independent Source grade at the same returned body store. -/
theorem native_body_with_post (outer size : Nat) (within : size < outer)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := post) (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) program header.function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates context)
        (context := context) (source := header.function.source) (faults := faults) child)
    : NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
      (faults := faults) entry reached size := by
    intro value bodyStore evaluated
    let bridge := bodyBridge (headers := headers) (keys := keys)
    let model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
    let producer := CallableIndexedOwnedAllocationProducer.producer headers keys model
    let condition := CallableIndexedOwnedAllocationProducer.StableOwner keys
    have meaning : RecursiveNamedBoundedContracts.Below size (fun child =>
        NamedLexicalFunctionFaultPostContracts.ReflectsAtWith
          (post := FlowPost (post))
          (protocol headers keys) (readiness bridge) condition
          (GenericLexicalStatements.Syntax header.function.source expressionSyntax)
          (values := .initial compiled.compatible.checked) functions program header.function.evidence validity
          (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
          (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := header.globals)
          (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
          child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true
          header.function.body header.function.resultType header.output flow) := by
      intro child smaller
      exact NamedLexicalFunctionFaultPostContracts.ReflectsAtWith.of_lexical
        (protocol := protocol headers keys) (readiness := readiness bridge) (condition := condition)
        (facts := GenericLexicalStatements.Syntax header.function.source expressionSyntax)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (functions := functions) (program := program) (evidence := header.function.evidence)
        (meaning := flow_reflects bridge functions header.function.evidence
          post header.unique
          (layouts := compiled.indexed.layouts) (owner := header.owner) (active := header.active)
          (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
          (expressionSyntax := expressionSyntax) rfl header.registered condition producer
          (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
          (fun _ _ seed => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner model seed)
          validity inputs.extend outer child child (Nat.lt_trans smaller within) (Nat.le_refl child) children inputs.tree)
    have matchTree := GenericImperativeMatch.Tree.body
      (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      inputs.syntaxTree inputs.tree
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame,
      metadata, _exit, finalTransition, retained⟩ :=
      RecursiveNamedFunctionFinishBounds.WithReady.reflects_at_emitted_with_state_when_with_transfers_with_post
        (functions := functions) (program := program) (tree := matchTree) (projection := inputs.projection) (unique := header.unique)
        (FlowPost (post))
        (protocol headers keys) (readiness bridge) condition
        (GenericLexicalStatements.Syntax header.function.source expressionSyntax) (BodyInputs.emitted validity inputs)
        validity size size (Nat.le_refl size) meaning inputs.valid inputs.syntaxTree
        entry.environments entry.heaps sourceReceipt.locals entry.lookups entry.actualTyped
        (body_reference functions entry) entry.state.read (body_unmapped functions entry) reached stable
        (show Admission bridge header.context reached from ⟨sourceReceipt.heapTyped, rows⟩)
        (BodyInputs.transfers validity inputs) evaluated
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame,
      metadata, ProtectedStateTransition.FunctionFinish.Reached.forget finalTransition,
      ReachedNamedLexicalBodyFaultPaths.outcome_post_of_finished_for inputs.syntaxTree header.unique retained evaluated.sound⟩


include inputs sourceReceipt rows stable in
/-- Each genuine smaller body member uses the same accepted Tree and finish
at its actual parameter state. -/
theorem source_below (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := post) (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) program header.function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates context)
        (context := context) (source := header.function.source) (faults := faults) child)
    : RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
        (faults := faults) entry reached) := by
  intro child strict
  exact source_body_with_post functions validity inputs post entry reached sourceReceipt rows stable
    outer child (Nat.lt_of_lt_of_le strict within) children

include inputs sourceReceipt rows stable in
/-- Each genuine smaller body member uses the same accepted Tree and finish
at its actual parameter state. -/
theorem native_below (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := post) (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) program header.function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates context)
        (context := context) (source := header.function.source) (faults := faults) child)
    : RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
        (faults := faults) entry reached) := by
  intro child strict
  exact native_body_with_post functions validity inputs post entry reached sourceReceipt rows stable
    outer child (Nat.lt_of_lt_of_le strict within) children

section Parameters
variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {parameterArguments : List Dynamic.Value}
  (parameters : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    functions owner argumentsPool header parameterArguments)

include inputs parameters in
/-- The authentic successful-argument receipt supplies body admission,
all ordered rows and the stable allocation hook internally. -/
theorem source_at_parameters (wellFormed : ProgramWellFormed program)
    (outer size : Nat) (within : size < outer)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := post) (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) program header.function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates context)
        (context := context) (source := header.function.source) (faults := faults) child)
    : SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
      (faults := faults) parameters.body parameters.reached size :=
  source_body_with_post functions validity inputs post parameters.body parameters.reached
    (parameters.source wellFormed) parameters.rows parameters.stable_owner outer size within children

include inputs parameters in
/-- The authentic successful-argument receipt supplies body admission,
all ordered rows and the stable allocation hook internally. -/
theorem native_at_parameters (wellFormed : ProgramWellFormed program)
    (outer size : Nat) (within : size < outer)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := post) (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) program header.function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates context)
        (context := context) (source := header.function.source) (faults := faults) child)
    : NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.bodyPost post)
      (faults := faults) parameters.body parameters.reached size :=
  native_body_with_post functions validity inputs post parameters.body parameters.reached
    (parameters.source wellFormed) parameters.rows parameters.stable_owner outer size within children

end Parameters

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds
