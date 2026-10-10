import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedClosureArgumentPackets
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedNamedArgumentPackets
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallStageAcceptance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveCalleeBoundaryReceipts

/-! Actual accepted user calls select their argument factory from the literal
closure or named callee. The whole parent consumes that factory and strict body
children through the original dispatcher. Its callee and argument posts, Source
and native grades, and returned caller state remain separate and unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedUserIndirectParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
open CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds (ArgumentPackets)
open CallableIndexedOwnedPreparedIndirectValueSourceSuffix (Suffix)
universe u

/-- The actual user callee fixes its complete invocation dictionary. -/
inductive UserCallee : Dynamic.Value → Dynamic.EvidenceEnvironment → Prop where
  | closure (function : Dynamic.Closure) : UserCallee (.closure function) function.evidence
  | global (function : Dynamic.GlobalFunction) : UserCallee (.global function) function.evidence

private theorem UserCallee.callable {function invocation} (user : UserCallee function invocation) :
    Dynamic.CallableValue function := by
  cases user <;> simp only [Dynamic.CallableValue]

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {context : SourceSemantics.Context} {evidence invocation : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
  {calleeNode : ExpressionNode} {function : Dynamic.Value} {calleeNative : Value}
  {sidecar : SourceCoreStageContracts.Sidecar}

local notation "positive" => functions qualification headers keys bodyRegistry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry positive
local notation "namedBodies" => CallableIndexedOwnedPreparedAcceptedNamedArgumentPackets.StaticBodies
  (qualification := qualification) (headers := headers) (keys := keys)
  (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (profile := profile)
  (certificates := certificates) (expressionSyntax := expressionSyntax)

section Packets
variable {mapping : LocationMap} {world : StoreTyping} {calleeHeap : Dynamic.Heap} {store : Store}
  {canonical : Environment}

include bridge compiler prepared in
/-- Both user alternatives construct their factory from original Source typing,
the same selected row and accepted gate. No application or argument law is an input. -/
theorem user_packets
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (static : namedBodies)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (user : UserCallee function invocation)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap function calleeNode.type)
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world calleeNode.type function calleeNative compiler.calleeCode.type)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      prepared.site prepared.site.call ids function calleeNative)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
      compiler.original dispatch.row)
    (accepted : CallableContract.decision prepared.site.gates .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none) :
    ArgumentPackets (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := invocation) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge positive compiler := by
  cases user with
  | closure function =>
    exact CallableIndexedOwnedPreparedAcceptedClosureArgumentPackets.packets bridge compiler
      actualFunctionType parent tree unique parentTyped calleeFound runtime calleeTyped represented dispatch selected accepted
  | global function =>
    exact CallableIndexedOwnedPreparedAcceptedNamedArgumentPackets.packets bridge compiler
      actualFunctionType static wellFormed parent tree unique parentTyped calleeFound runtime
      calleeTyped represented caller dispatch selected accepted

end Packets

section Parent
variable {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {xi : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (static : CallableIndexedOwnedPreparedAcceptedNamedArgumentPackets.StaticBodies
    (qualification := qualification) (headers := headers) (keys := keys)
    (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (profile := profile)
    (certificates := certificates) (expressionSyntax := expressionSyntax))
  (parent : SourceParent compiler)
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (calleeFound : source.lookupExpression? callee = some calleeNode)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree xi canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (firstAdmission : Admission bridge context first)
  (user : UserCallee function invocation)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := xi) (calleeNode := calleeNode) (context := context)
    bridge (functions qualification headers keys bodyRegistry faults profile) compiler first function calleeHeap calleeNative store mapping world)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
    prepared.site prepared.site.call ids function calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
    compiler.original dispatch.row)
  (stageAccepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar)
    prepared.site.call ids function)
  (secondGate : CallableContract.decision prepared.site.gates .beforeApplication
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee function calleeHeap)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (functions qualification headers keys bodyRegistry faults profile) identities)

include prepared actualFunctionType static parent tree unique parentTyped calleeFound wellFormed runtime covers
  environments locals agrees typed firstAdmission user post caller dispatch selected stageAccepted secondGate calleeTrace observations
/-- The original whole accepted parent consumes the actual callee and argument
posts and the strict body family. Source and native grades remain independent. -/
theorem preserves (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (closures : ClosurePreservesBelow (qualification := qualification) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) positive budget)
    (named : NamedPreservesBelow (headers := headers) (keys := keys) (registry := registry)
      (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax) positive budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : Suffix (Program.ofChecked compiled.sourceProgram) context evidence invocation source environment
      calleeHeap ids function argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename xi) value finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge positive compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, represented, heaps, maps, worlds, frame, metadata, reached, related, admission⟩ := post
  have calleeTyped := admission.at_value.1
  have packets : ArgumentPackets (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := invocation) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge positive compiler := user_packets bridge compiler prepared actualFunctionType static wellFormed
    parent tree unique parentTyped calleeFound runtime user calleeTyped represented caller dispatch selected secondGate
  have firstGate := CallableIndexedOwnedSelectedCallStageAcceptance.before_arguments dispatch stageAccepted
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
  have nativeTyped := represented.runtime_hasType
  have signature := compiler.callableType
  rw [actualFunctionType] at signature
  rw [← signature] at nativeTyped
  exact CallableIndexedOwnedPreparedIndirectValueParentBounds.preserves_with_application bridge positive compiler prepared
    parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed first firstAdmission
    reached related maps worlds frame metadata user.callable nativeTyped heaps rfl rfl
    dispatch.shape firstGate secondGate calleeTrace calleeEvaluation selected budget children suffix
    argumentsWithin callWithin (CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.preserves
      bridge positive compiler packets wellFormed observations budget closures named suffix)

include prepared actualFunctionType static parent tree unique parentTyped calleeFound wellFormed runtime covers
  environments locals agrees typed firstAdmission user post caller dispatch selected stageAccepted secondGate calleeTrace observations
/-- Reflection consumes the literal original native completion. Its own Source
suffix grade and returned caller witness come from the original parent inversion. -/
theorem reflects (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (closures : ClosureReflectsBelow (qualification := qualification) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) positive budget)
    (named : NamedReflectsBelow (headers := headers) (keys := keys) (registry := registry)
      (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax) positive budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename xi) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge positive compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, represented, heaps, maps, worlds, frame, metadata, reached, related, admission⟩ := post
  have calleeTyped := admission.at_value.1
  have packets : ArgumentPackets (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := invocation) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge positive compiler := user_packets bridge compiler prepared actualFunctionType static wellFormed
    parent tree unique parentTyped calleeFound runtime user calleeTyped represented caller dispatch selected secondGate
  have firstGate := CallableIndexedOwnedSelectedCallStageAcceptance.before_arguments dispatch stageAccepted
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
  have nativeTyped := represented.runtime_hasType
  have signature := compiler.callableType
  rw [actualFunctionType] at signature
  rw [← signature] at nativeTyped
  exact CallableIndexedOwnedPreparedIndirectValueParentBounds.reflects_with_application bridge positive compiler prepared
    unique parentTyped first reached parent tree wellFormed runtime covers environments locals agrees typed firstAdmission
    related maps worlds frame metadata nativeTyped heaps rfl rfl user.callable
    dispatch.shape firstGate secondGate calleeTrace calleeEvaluation selected budget children
    (CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.reflects
      bridge positive compiler packets wellFormed observations budget closures named) completed within

end Parent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedUserIndirectParentBounds
