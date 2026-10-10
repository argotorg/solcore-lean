import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix

/-! The original indirect parent stops at a real argument failure. Its strict
callee and ordered argument hypotheses run at their actual reached states.
The first gate is reconstructed from the authentic scoped boundary; semantic
and nested stage failures retain the same tag, token and transient effects. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include guardFrame in
/-- The real original row supplies first-gate success at the callee store.
No native acceptance or verdict is added to a compiler certificate. -/
theorem first_gate {sourceValue : Dynamic.Value} {carrier : Value}
    {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
    (boundary : BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (calleeStore : Store) :
    Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore := by
  cases boundary with
  | user dispatch selected =>
      have passed := dispatch.accepted (by simpa only [guardFrame, prepared.call] using accepted)
      have read : Evaluates (carrier :: actual) calleeStore (.second (.var 0))
          (.word dispatch.contract) calleeStore := by
        exact .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
      have gate := prepared.site.dispatch_known .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
        dispatch.contract dispatch.row dispatch.found read
      rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeArguments passed] at gate
      simpa only [CallableContract.resultValue] using gate
  | builtin receipt =>
      exact receipt.first_gate compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown actual calleeStore

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Strict Source descent constructs the callee and argument computations.
The argument fold runs after the accepted first gate and its actual effects
are the parent post; the second gate and application are never evaluated. -/
theorem preserves_argument_fault (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate faults budget)
    {calleeSize argumentsSize : Nat} {sourceValue : Dynamic.Value} {calleeHeap after : Dynamic.Heap}
    {failure : Staging.Recursive.Failure}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.fault failure) after)
    (within : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize]) invocation context environment before id
      (.fault failure) after ∧
    ∃ token finalStore finalMap finalWorld,
      CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
        (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
        bridge functions compiler initial failure after token finalStore finalMap finalWorld := by
  have calleeStrict : calleeSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := calleeSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have argumentsStrict : argumentsSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := argumentsSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, calleeStore, calleeMap, calleeWorld, calleeEvaluated, representation, calleeHeaps,
    calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ :=
    children calleeSize calleeStrict certified actualFound actualTyped environments heaps locals agrees typed initial admitted calleeTrace
  cases representation with
  | value payload =>
      have calleePost : ∃ carrier, CalleePost (registry := registry) (context := context)
          (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
          bridge functions compiler initial sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld :=
        ⟨_, calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩
      obtain ⟨carrier, post⟩ := calleePost
      obtain ⟨calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
        calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ := post
      obtain ⟨originalNode, originalMetadata, _contains, _form, _callView, boundary⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial caller view originalUnique
          ⟨calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
            calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩
      obtain ⟨_rawParameter, _rawResult, _functionType, argumentsTyped, _bundle, _result⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.source_rows
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
      have argumentLayout : EnvironmentsAgree
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
          canonical (.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
      have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
        (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
      obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, postAdmission⟩ :=
        CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_fault bridge budget tree unique argumentsTyped children
          (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
          argumentTyped calleeState calleeAdmission.at_value.2 argumentsTrace (Nat.le_of_lt argumentsStrict)
      have gate := first_gate (actual := actual) compiler prepared guardFrame boundary accepted calleeStore
      have whole : Evaluates actual store
          (CallableContract.call prepared.site.gates
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
            (compiler.calleeCode.expression.rename ξ)
            ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ))
          (.inLeft compiler.resultType (.word token)) finalStore := by
        apply LanguageResult.bind_success compiler.resultType calleeEvaluated
        apply LanguageResult.bind_success compiler.resultType gate
        apply LanguageResult.bind_failure compiler.resultType
        simpa only [← rename_prefix, ← rename_prefix] using argumentsEvaluated
      rw [← prepared.lowered_rename compiler ξ] at whole
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      rw [← loweredType] at whole
      have parentAdmission : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge context compiler.original.type (.fault failure) reached := by
        cases failure with
        | semantic reason => exact ⟨postAdmission.rows, by intro _ impossible; cases impossible⟩
        | stage origin call reason => exact postAdmission.rows
      exact ⟨.argumentsFault occurrence calleeTrace accepted argumentsTrace,
        token, finalStore, finalMap, finalWorld, whole, .fault matched, finalHeaps,
        calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
        calleeMetadata.trans heapMetadata, reached, callerProtocol.trans calleeRelated related, parentAdmission⟩

/-- The constructive whole argument-prefix reflection already contains the
actual parent trace and reached failure receipt. This branch exposes the
independent Source grade without rebuilding or relabeling the child failure. -/
theorem reflects_argument_fault_prefix {value : Value} {finalStore : Store}
    (reflected : CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.ArgumentFaultPrefix
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry)
      (faults := faults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore) :
    ∃ sourceSize failure after token finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id (.fault failure) after ∧
      value = .inLeft lowered.type (.word token) ∧
      CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
        (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
        bridge functions compiler initial failure after token finalStore finalMap finalWorld := by
  obtain ⟨calleeSize, argumentsSize, _sourceValue, _calleeHeap, failure, after, token, finalMap, finalWorld,
    _callee, _accepted, _arguments, parent, sameValue, result⟩ := reflected
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize], failure, after, token,
    finalMap, finalWorld, parent, sameValue, result⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentFaultBounds
