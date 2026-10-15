import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCallableOrigins
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftSequence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds

/-! A lifted indirect callee reaches its actual physical payload before the
original authenticated stage guard is classified. Rejection preserves that
prefix heap; acceptance retains the same state for ordered arguments. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectCalleeLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open Staging.Recursive.Lifting (ExpressionLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functions : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry semanticFaults profile functions]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (certified : certificate scope callee compiler.calleeCode)
  (sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include positive port tree unique parentTyped in
theorem guard_at {value : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (post : CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := port.calleeNode) bridge functions compiler initial
      value after carrier calleeStore finalMap finalWorld) :
    Staging.CallBoundary.GuardAccepts invocation.guards id ids value ∨
      ∃ reason, Staging.CallBoundary.GuardRejects invocation.guards id ids value reason := by
  obtain ⟨_original, _originalMetadata, _contained, _form, _view, boundary⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary
      (sourceEq := rfl) (found := port.calleeFound) (sourceParent := port.sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped)
      bridge profile compiler port.prepared initial port.caller port.view port.originalUnique post
  cases boundary with
  | user dispatch _selected =>
    rcases Staging.CallGuard.complete (CallableLedger.frame port.sidecar).stages _ port.prepared.site.call ids with accepted | ⟨reason, rejected⟩
    · left
      simpa only [port.guardFrame, port.prepared.call] using
        (Staging.CallBoundary.GuardAccepts.contract dispatch.bound accepted)
    · right
      refine ⟨reason, ?_⟩
      simpa only [port.guardFrame, port.prepared.call] using
        (Staging.CallBoundary.GuardRejects.contract dispatch.bound rejected)
  | builtin _receipt => exact .inl (.builtin _)

include positive certified sourceTyped tree unique parentTyped environments heaps locals agrees typed admitted in
theorem callee_value (budget : Nat)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ stageSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults stageSize)
    {size : Nat} {value : Dynamic.Value} {calleeHeap : Dynamic.Heap}
    {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) size context
      invocation.evidence invocation.source environment before callee value calleeHeap)
    (smaller : size < budget) :
    ExpressionLift (Program.ofChecked compiled.sourceProgram) stages invocation context environment before id plain after ∨
    ∃ carrier calleeStore finalMap finalWorld,
      Staging.Recursive.Expression (Program.ofChecked compiled.sourceProgram) stages invocation context environment
        before callee (.value value) calleeHeap ∧
      CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
        (calleeNode := port.calleeNode) bridge functions compiler initial
        value calleeHeap carrier calleeStore finalMap finalWorld ∧
      Staging.CallBoundary.GuardAccepts invocation.guards id ids value := by
  have occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  obtain ⟨staged, reached, lifted, adapted⟩ := children size smaller certified port.calleeFound
    sourceTyped environments heaps locals agrees typed initial admitted (.value trace)
  cases adapted with
  | rejected origin call reason reached =>
    exact .inl ⟨_, _, .calleeFault occurrence lifted, .rejected origin call reason _⟩
  | completed =>
    obtain ⟨stageSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    obtain ⟨carrier, calleeStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      preservation stageSize certified port.calleeFound sourceTyped environments heaps locals agrees typed initial admitted measured
    cases represented with
    | value payload =>
      have full : CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
          (calleeNode := port.calleeNode) bridge functions compiler initial
          value calleeHeap _ calleeStore finalMap finalWorld :=
        ⟨evaluated, payload, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
      rcases guard_at bridge profile compiler port tree unique parentTyped initial full with accepted | ⟨reason, rejected⟩
      · exact .inr ⟨_, _, _, _, lifted, full, accepted⟩
      · exact .inl ⟨_, _, .rejected occurrence lifted rejected, .rejected invocation id reason _⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectCalleeLifting
