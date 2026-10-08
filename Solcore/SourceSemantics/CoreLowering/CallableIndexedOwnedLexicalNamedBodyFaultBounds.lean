import Solcore.SourceSemantics.CoreLowering.ReachedNamedLexicalBodyFaultPaths
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBuiltinFaultBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness

/-! Static builtin receipts populate the original lexical Tree factors at each
actual reached input. Named body endpoints use the same flow and finish once;
the first concrete profile is finite discard prefixes with a tail or return. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLexicalNamedBodyFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open NamedLexicalFlowFaultPostContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} (evidence : Dynamic.EvidenceEnvironment)
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

/-- Each accepted expression has its own actual fuel, evidence and primitive
certificate. These are static receipts, not a completed expression meaning. -/
def BuiltinInputs (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ fuel solved reasonAt,
    CompatibleExpressionBuiltins.Tree fuel (.initial compiled.compatible.checked) source context solved reasonAt scope id lowered ∧
    CompatibleExpressionLiterals.ContextValid solved context evidence ∧
    ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked) source context reasonAt faults ∧
    IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked) source functions registry
      program context evidence reasonAt faults

structure StaticContext (context : SourceSemantics.Context) : Prop where
  runtime : Dynamic.SourceRuntimeValid program context source
  covers : evidence.Covers context
  children : ∀ {scope id lowered}, certificates context scope id lowered →
    BuiltinInputs (compiled := compiled) (program := program) (registry := registry) (faults := faults) (source := source) functions evidence context scope id lowered

variable
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)

include transport extension faithful observations functionTypes unique wellFormed in
theorem expression_preserves {context : SourceSemantics.Context}
    (inputs : StaticContext (compiled := compiled) (program := program) (registry := registry) (faults := faults) (source := source) (certificates := certificates) functions evidence context)
    (size : Nat) :
    NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt
      (post := ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
      callerProtocol (readiness bridge) program evidence
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (ProtectedStateLexicalSourceSites.ExpressionFacts source) (certificates context)
      (context := context) (source := source) (faults := faults) size := by
  intro scope id lowered certificate node found typed mapping world administrative environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨fuel, solved, reasonAt, tree, valid, reads, missing⟩ := inputs.children certificate
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, postAdmission, retained⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves bridge functions evidence transport extension faithful observations
      functionTypes valid reads missing unique wellFormed inputs.runtime inputs.covers tree found typed
      environments heaps locals agrees actualTyped initial admitted trace
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame,
    metadata, ⟨reached, related, CallableIndexedOwnedAdmittedLexicalReadiness.expression_post bridge postAdmission⟩, ?_⟩
  cases outcome with
  | value sourceValue => trivial
  | fault reason => exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained evaluated

include transport extension faithful observations functionTypes unique wellFormed in
theorem expression_reflects {context : SourceSemantics.Context}
    (inputs : StaticContext (compiled := compiled) (program := program) (registry := registry) (faults := faults) (source := source) (certificates := certificates) functions evidence context)
    (size : Nat) :
    NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt
      (post := ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
      callerProtocol (readiness bridge) program evidence
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (ProtectedStateLexicalSourceSites.ExpressionFacts source) (certificates context)
      (context := context) (source := source) (faults := faults) size := by
  intro scope id lowered certificate node found typed mapping world administrative environment canonical actual
    actualContext before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨fuel, solved, reasonAt, tree, valid, reads, missing⟩ := inputs.children certificate
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, postAdmission, retained⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects bridge functions evidence transport extension faithful observations
      functionTypes valid reads missing unique wellFormed inputs.runtime inputs.covers tree found typed
      environments heaps locals agrees actualTyped initial admitted completed
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame,
    metadata, ⟨reached, related, CallableIndexedOwnedAdmittedLexicalReadiness.expression_post bridge postAdmission⟩, ?_⟩
  cases outcome with
  | value sourceValue => trivial
  | fault reason => exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained completed.sound

section Flows
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {expressionSyntax : ExpressionId → Prop}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (condition : Location → NativeFrame → Prop)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)
  (acquire : ∀ location native, condition location native → ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer location native)
  (validity : SourceSemantics.Context → Prop)
  (contexts : ∀ context, validity context → StaticContext (compiled := compiled) (program := program) (registry := registry) (faults := faults) (source := source) (certificates := certificates) functions evidence context)
  (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext)

include definitions registered producer bindings acquire unique transport extension faithful observations functionTypes wellFormed contexts extend in
theorem flow_preserves (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      source certificates context scope mode statements expected type code) :
    NamedLexicalFlowFaultPostContracts.PreservesAtFor
      (post := FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
      callerProtocol (readiness bridge) condition (GenericLexicalStatements.Syntax source expressionSyntax)
      (values := .initial compiled.compatible.checked) (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frame) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ
    contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  exact RecursiveNamedLexicalTreeBounds.Stateful.WithReady.preserves_at_for_with_post
    (expressionPost := ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
    (headPost := HeadPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
    (flowPost := FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
    (joins := origin_joins _ program evidence source)
    (protocol := callerProtocol) (condition := condition) (producer := producer) (stateBindings := bindings) (acquire := acquire)
    (readiness := readiness bridge) (facts := GenericLexicalStatements.Syntax source expressionSyntax)
    (headFacts := ProtectedStateLexicalSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (sites := ProtectedStateLexicalSourceSites.sites program evidence unique)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    functions definitions registered program evidence validity extend budget size bounded
    (fun child _ context valid => expression_preserves bridge functions evidence transport extension faithful observations functionTypes unique wellFormed (contexts context valid) child)
    tree valid sourceFacts unique environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace

include definitions registered producer bindings acquire unique transport extension faithful observations functionTypes wellFormed contexts extend in
theorem flow_reflects (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      source certificates context scope mode statements expected type code) :
    NamedLexicalFlowFaultPostContracts.ReflectsAtFor
      (post := FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
      callerProtocol (readiness bridge) condition (GenericLexicalStatements.Syntax source expressionSyntax)
      (values := .initial compiled.compatible.checked) (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frame) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ
    contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted evaluated
  exact RecursiveNamedLexicalTreeBounds.Stateful.WithReady.reflects_at_for_with_post
    (expressionPost := ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
    (headPost := HeadPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
    (flowPost := FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
    (joins := origin_joins _ program evidence source)
    (protocol := callerProtocol) (condition := condition) (producer := producer) (stateBindings := bindings) (acquire := acquire)
    (readiness := readiness bridge) (facts := GenericLexicalStatements.Syntax source expressionSyntax)
    (headFacts := ProtectedStateLexicalSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (sites := ProtectedStateLexicalSourceSites.sites program evidence unique)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    functions definitions registered program evidence validity extend budget size bounded
    (fun child _ context valid => expression_reflects bridge functions evidence transport extension faithful observations functionTypes unique wellFormed (contexts context valid) child)
    tree valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted evaluated

end Flows

/-- The first concrete grammar has only executed discards before one real tail
or explicit return. This is a static shape receipt, not a semantic traversal. -/
inductive DiscardReturnProfile (source : TypedSource) : List StatementId → Prop where
  | tail {id node expression} (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression false) : DiscardReturnProfile source [id]
  | returning {id node expression} (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression)) : DiscardReturnProfile source [id]
  | discard {id node expression semicolon rest} (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && true && rest.isEmpty) = false)
      (remaining : DiscardReturnProfile source rest) : DiscardReturnProfile source (id :: rest)

section NamedBodies
open RecursiveNamedCatalogInvocationBounds CallableIndexedHistory
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)

private def poolBridge {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)} :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

variable {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {expressionSyntax : ExpressionId → Prop} {flow : Expr}
  (validity : SourceSemantics.Context → Prop)

/-- The compiler acceptances, literal source grammar and actual child domains
all refer to this Header. No expression, flow or body meaning is a field. -/
structure BodyInputs : Prop where
  profile : DiscardReturnProfile header.function.source header.function.body
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
  contexts : ∀ context, validity context → StaticContext (compiled := compiled) (program := program)
    (registry := registry) (faults := faults) (source := header.function.source) (certificates := certificates)
    functions header.function.evidence context
  extend : ∀ {context nextContext binder}, validity context →
    BinderExtends header.function.source.owner context binder nextContext → validity nextContext

variable (inputs : BodyInputs (functions := functions) (header := header) (registry := registry)
  (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax) (flow := flow) validity)

include inputs in
private theorem BodyInputs.emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped := by
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

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
/-- Authentic static child certificates populate the shared Tree and finish
at this actual parameter state. The fault post remains at the body store. -/
theorem source_body_with_post (size : Nat) :
    SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
  intro outcome after trace
  let bodyBridge := poolBridge (headers := headers) (keys := keys)
  let model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
  let producer := CallableIndexedOwnedAllocationProducer.producer headers keys model
  let condition := CallableIndexedOwnedAllocationProducer.StableOwner keys
  have meaning := flow_preserves bodyBridge functions header.function.evidence
    (administrativeTransport headers keys) extension faithful observations functionTypes header.unique wellFormed
    (layouts := compiled.indexed.layouts) (owner := header.owner) (active := header.active)
    (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
    (expressionSyntax := expressionSyntax) rfl header.registered condition producer
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (fun _ _ seed => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner model seed)
    validity inputs.contexts inputs.extend size size (Nat.le_refl size) inputs.tree
  have lifted := NamedLexicalFunctionFaultPostContracts.PreservesAtWith.of_lexical
    (protocol := protocol headers keys) (readiness := readiness bodyBridge) (condition := condition)
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
      (FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
      (protocol headers keys) (readiness bodyBridge) condition
      (GenericLexicalStatements.Syntax header.function.source expressionSyntax) (BodyInputs.emitted functions validity inputs)
      validity size lifted inputs.valid inputs.syntaxTree
      entry.environments entry.heaps sourceReceipt.locals entry.lookups entry.actualTyped
      (body_reference functions entry) entry.state.read (body_unmapped functions entry) reached stable
      (show Admission bodyBridge header.context reached from ⟨sourceReceipt.heapTyped, rows⟩)
      (BodyInputs.transfers functions validity inputs) trace
  exact ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame,
    metadata, ProtectedStateTransition.FunctionFinish.Reached.forget finalTransition,
    ReachedNamedLexicalBodyFaultPaths.outcome_post_of_finished inputs.syntaxTree header.unique retained evaluated⟩

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
/-- Native finish selects its genuine strict flow child. The Source grade is
constructed independently by the same shared producer at the reached state. -/
theorem native_body_with_post (size : Nat) :
    NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
  intro value bodyStore evaluated
  let bodyBridge := poolBridge (headers := headers) (keys := keys)
  let model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
  let producer := CallableIndexedOwnedAllocationProducer.producer headers keys model
  let condition := CallableIndexedOwnedAllocationProducer.StableOwner keys
  have meaning : RecursiveNamedBoundedContracts.Below size (fun child =>
      NamedLexicalFunctionFaultPostContracts.ReflectsAtWith
        (post := FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
        (protocol headers keys) (readiness bodyBridge) condition
        (GenericLexicalStatements.Syntax header.function.source expressionSyntax)
        (values := .initial compiled.compatible.checked) functions program header.function.evidence validity
        (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
        (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true
        header.function.body header.function.resultType header.output flow) := by
    intro child smaller
    exact NamedLexicalFunctionFaultPostContracts.ReflectsAtWith.of_lexical
      (protocol := protocol headers keys) (readiness := readiness bodyBridge) (condition := condition)
      (facts := GenericLexicalStatements.Syntax header.function.source expressionSyntax)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := program) (evidence := header.function.evidence)
      (meaning := flow_reflects bodyBridge functions header.function.evidence
        (administrativeTransport headers keys) extension faithful observations functionTypes header.unique wellFormed
        (layouts := compiled.indexed.layouts) (owner := header.owner) (active := header.active)
        (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
        (expressionSyntax := expressionSyntax) rfl header.registered condition producer
        (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
        (fun _ _ seed => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner model seed)
        validity inputs.contexts inputs.extend size child (Nat.le_of_lt smaller) inputs.tree)
  have matchTree := GenericImperativeMatch.Tree.body
    (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    inputs.syntaxTree inputs.tree
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame,
    metadata, _exit, finalTransition, retained⟩ :=
    RecursiveNamedFunctionFinishBounds.WithReady.reflects_at_emitted_with_state_when_with_transfers_with_post
      (functions := functions) (program := program) (tree := matchTree) (projection := inputs.projection) (unique := header.unique)
      (FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry))
      (protocol headers keys) (readiness bodyBridge) condition
      (GenericLexicalStatements.Syntax header.function.source expressionSyntax) (BodyInputs.emitted functions validity inputs)
      validity size size (Nat.le_refl size) meaning inputs.valid inputs.syntaxTree
      entry.environments entry.heaps sourceReceipt.locals entry.lookups entry.actualTyped
      (body_reference functions entry) entry.state.read (body_unmapped functions entry) reached stable
      (show Admission bodyBridge header.context reached from ⟨sourceReceipt.heapTyped, rows⟩)
      (BodyInputs.transfers functions validity inputs) evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame,
    metadata, ProtectedStateTransition.FunctionFinish.Reached.forget finalTransition,
    ReachedNamedLexicalBodyFaultPaths.outcome_post_of_finished inputs.syntaxTree header.unique retained evaluated.sound⟩

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
/-- Strict membership retains the same concrete Source body producer. -/
theorem source_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact source_body_with_post functions extension faithful observations functionTypes wellFormed
    validity inputs entry reached sourceReceipt rows stable child

include inputs sourceReceipt rows stable extension faithful observations functionTypes wellFormed in
/-- Each native member uses its own actual measured body completion. -/
theorem native_below (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact native_body_with_post functions extension faithful observations functionTypes wellFormed
    validity inputs entry reached sourceReceipt rows stable child

section Parameters
variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {parameterArguments : List Dynamic.Value}
  (parameters : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    functions owner argumentsPool header parameterArguments)

include inputs parameters extension faithful observations functionTypes wellFormed in
/-- The actual parameter receipt supplies deep Source admission, all rows and
its literal stable hook. No body semantics is supplied by the caller. -/
theorem source_at_parameters (size : Nat) :
    SourceBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) parameters.body parameters.reached size :=
  source_body_with_post functions extension faithful observations functionTypes wellFormed
    validity inputs parameters.body parameters.reached (parameters.source wellFormed) parameters.rows parameters.stable_owner size

include inputs parameters extension faithful observations functionTypes wellFormed in
/-- Native reflection starts at the same real hook and parameter state. -/
theorem native_at_parameters (size : Nat) :
    NativeBodyAtWithPost (ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) parameters.body parameters.reached size :=
  native_body_with_post functions extension faithful observations functionTypes wellFormed
    validity inputs parameters.body parameters.reached (parameters.source wellFormed) parameters.rows parameters.stable_owner size
end Parameters

end NamedBodies

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLexicalNamedBodyFaultBounds
