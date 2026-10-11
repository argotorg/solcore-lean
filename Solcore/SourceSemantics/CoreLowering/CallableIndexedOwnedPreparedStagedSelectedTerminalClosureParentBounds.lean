import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds

/-! Internal selected-terminal parent ports for the recursive numeric body family.
A static factory chooses one actual terminal packet per contextual association.
The strict body hypothesis belongs only to that chosen packet; no law for an
arbitrary terminal certificate is inferred from its certifies field. The lower
application and saved-caller restoration proofs retain their original indices.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalClosureParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (ReflectsBelowFor)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}

section Parent
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {argumentMap : LocationMap} {argumentWorld : StoreTyping}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, argumentMap, argumentWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    argumentMap argumentWorld argumentsHeap argumentsStore)
  (maps : LocationMap.Extends mapping argumentMap) (worlds : WorldExtends world argumentWorld)
  (frame : AdministrativePreserved mapping store argumentMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)
  {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
  (count : dispatch.row.entry.parameterCount = ids.length)
  (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids (.closure function))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
  (calleeHeapTyped : Dynamic.HeapWellTyped context calleeHeap)
  (typing : ExpressionsHaveTypes invocation.source context ids sourceTypes)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (calleeRelated : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
    headers keys bodyRegistry registry semanticFaults profile argumentMap argumentWorld
    (.function parameter result) (.closure function) carrier compiler.calleeCode.type)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    argumentMap argumentWorld sourceTypes (compiler.codes.map (·.type)) sources values)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include bridge profile compiler prepared sourceParent occurrence related admitted heaps maps worlds frame heapMetadata
  dispatch selected count accepted wellFormed runtime covers locals calleeHeapTyped typing calleeTyped
  actualFunctionType calleeRelated represented bundle originalResult in
/-- The concrete selected closure suffix constructs the original applied
parent. Both numeric grades and every transient reached effect are retained. -/
theorem reflects_suffix
    (terminals : ∀ {bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults argumentMap argumentWorld function carrier
        bindings parameterCore resultCore), TerminalFor association stages)
    (budget : Nat)
    (children : ∀ {bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults argumentMap argumentWorld function carrier
        bindings parameterCore resultCore),
      ReflectsBelowFor (registry := registry) (faults := faults) association (terminals association) functions budget)
    {calleeSize argumentsSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.closure function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {suffixSize : Nat} {value : Value} {finalStore : Store}
    (suffix : EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : suffixSize ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨raw, valid, bindings, parameterCore, resultCore, member, parameterEq, resultEq, parameters⟩ :=
    CallableIndexedOwnedPreparedStagedClosureArgumentRows.at_arguments bridge profile compiler reached dispatch
      selected count wellFormed runtime covers locals calleeHeapTyped typing calleeTyped bundle admitted
      actualFunctionType calleeRelated represented argumentsTrace
  obtain ⟨association⟩ := member
  let terminal := terminals association
  obtain ⟨applicationSize, strict, application⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.reflects_suffix dispatch.shape
      selected dispatch.found count suffix within
  obtain ⟨applicationSourceSize, outcome, after, finalMap, finalWorld, applied, resultRep, finalHeaps,
    applicationMaps, applicationWorlds, applicationFrame, applicationMetadata, ownedReturned, ownedRelated, ownedPost⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.application_reflects association terminal functions (bridge.pool reached) raw parameters heaps admitted.rows
      runtime valid budget (children association) application (Nat.le_of_lt strict)
  obtain ⟨returned, samePool, callerRelated⟩ := bridge.restore reached ownedReturned
    applicationMaps applicationWorlds applicationFrame applicationMetadata ownedRelated
  have sameSource : compiler.original.type = function.resultType := by
    obtain ⟨_parameters, sourceResult, _signatures, _code, _covers, _captures⟩ := calleeTyped.closure_function_inv
    exact originalResult.trans sourceResult
  have sameCore : lowered.type = resultCore :=
    (congrArg (fun output => output.type) compiler.output).trans (compiler.resultTypeEq.symm.trans resultEq)
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    cases outcome with
    | value sourceValue =>
      change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
      exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
        exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
      | stage failedScope failedCall reason =>
        change StableRows (bridge.pool returned)
        rw [samePool]
        exact ownedPost
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSourceSize],
    outcome, after, finalMap, finalWorld,
    .applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity applied,
    parentRep, finalHeaps, maps.trans applicationMaps, worlds.trans applicationWorlds,
    frame.trans applicationFrame, heapMetadata.trans applicationMetadata,
    returned, callerProtocol.trans related callerRelated, parentPost⟩

end Parent

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalClosureParentBounds
