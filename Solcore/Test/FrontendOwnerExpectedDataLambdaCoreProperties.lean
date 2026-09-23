import Solcore.Frontend.Expected

/- Old, renamed, and Core paths are concrete before either owner/data-lambda
bridge is consumed.  The fixture deliberately has no runtime typing premise. -/
set_option autoImplicit false
namespace Tests.ADR0315OwnerExpectedDataLambdaCoreConsumer
open Solcore Solcore.Frontend

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"OwnerDataLambda", by decide⟩], by decide⟩⟩, index⟩
private def savedOwner := declaration 4
private def foreignOwner := declaration 9
private def callerOwner := declaration 12
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId :=
  ⟨owner, index⟩
private def payloadId := localId savedOwner 7
private def noiseId := localId foreignOwner 31
private def shadowId := localId savedOwner 2
private def calleeId := localId callerOwner 40
private def argumentId := localId callerOwner 41
private def foreignCalleeId := localId foreignOwner 40

private def shift (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { owner with declarationIndex := owner.declarationIndex + 5 }
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨before, same⟩ := onto (declaration 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  change before.declarationIndex + 5 = 0 at impossible
  omega

private def sourceId : Syntax.SourceId := ⟨.main, "owner-data-lambda.sol"⟩
private def span (offset : Nat) : Syntax.SourceSpan := ⟨sourceId, offset, offset + 2⟩
private def ident (offset : Nat) (name : String) : Syntax.Identifier := ⟨span offset, name⟩
private def ref (offset : Nat) (name : String) : Syntax.Expr :=
  ⟨span offset, .identifier (ident offset name)⟩
private def parameter := ident 5 "x"
private def body : Syntax.Block :=
  ⟨span 10, [⟨span 11, .returnStmt (some (ref 12 "x"))⟩]⟩
private def source : Syntax.Expr :=
  ⟨span 0, .lambda (span 1) ⟨span 2, [⟨span 3, .inferred parameter⟩]⟩ none body⟩
private def argument := ref 20 "payload"
private def directCall : Syntax.Expr :=
  ⟨span 21, .call source ⟨span 22, [argument]⟩⟩
private def callee := ref 30 "fn"
private def callerArgument := ref 31 "arg"
private def invocation : Syntax.Expr :=
  ⟨span 32, .call callee ⟨span 33, [callerArgument]⟩⟩

private def inputs : LocalTypeInputs :=
  ⟨[⟨"payload", payloadId, .unit⟩, ⟨"noise", noiseId, .word⟩,
    ⟨"payload", shadowId, .bool⟩], by decide⟩
private def payload : Core.Value :=
  .closure .bool .word (.var 1)
    [.cellRef .word 8, .hostFunction .callerAddress,
      .closure .unit .unit (.var 4) [.hostFunction .storageRead]]
private def environment : Resolved.Environment :=
  [(payloadId, payload), (noiseId, .word (Core.Word.ofNatModulo 99)),
    (shadowId, .bool false)]
private def store : Core.Store :=
  [.word (Core.Word.ofNatModulo 77), .cellRef .word 3,
    .hostFunction .storageWrite, payload]
private def captures : List (Resolved.LocalId × RuntimeValue) :=
  environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))
private def heap : List RuntimeValue := store.map RuntimeValue.ofCore
private def mappedEnvironment : Resolved.Environment :=
  Resolved.LocalScope.mapIds (ownerLocalIdMap shift) environment
private def mappedInputs : LocalTypeInputs :=
  inputs.mapIds (ownerLocalIdMap shift) (ownerLocalIdMap_injective shift shift_injective)

private theorem shape : SourceUnaryLambdaShape source parameter body := .inferred
private theorem dataBody : ClosedSourceDataBody body := .expression .reference
private theorem checked :
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] savedOwner inputs source
      (.function .unit .unit) = some (.lambda .unit .unit (.var 0)) :=
  (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
    (.lambda (.lambda .inferred .omitted) .unit .unit
      (.expression (elaborateLocalExpression?_complete
        (.identifier .head) (.var .head) (.var .head))))
private theorem mappedChecked :
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] (shift savedOwner)
      mappedInputs source (.function .unit .unit) = some (.lambda .unit .unit (.var 0)) := by
  simpa only [mappedInputs] using
    (elaborateExpectedComputationLambda?_mapOwner shift shift_injective elaborateLocalExpression?
      (elaborateLocalExpression?_mapIds (ownerLocalIdMap shift)
        (ownerLocalIdMap_injective shift shift_injective)) [] savedOwner inputs source
      (.function .unit .unit)).trans checked
private theorem sameIds : environment.ids = inputs.context.ids := by rfl
private theorem argumentData : ClosedSourceDataExpression argument := .reference
private theorem argumentResolution :
    ResolvesLocalExpression inputs.names argument (.var payloadId) := .identifier .head
private theorem argumentLowering : Resolved.Lowers environment.ids (.var payloadId) (.var 0) :=
  .var .head

private theorem bodyRaw :
    ClosedSourceBodyEvaluates savedOwner
      ((parameter.value, Resolved.freshLocalId savedOwner inputs.ids) :: inputs.names)
      ((Resolved.freshLocalId savedOwner inputs.ids, RuntimeValue.ofCore payload) :: captures)
      heap body (RuntimeValue.ofCore payload) heap :=
  .expression (.reference .head .head)
private theorem directRaw :
    ClosedSourceExpressionEvaluates savedOwner inputs.names captures heap directCall
      (RuntimeValue.ofCore payload) heap :=
  .call shape (.creation shape) (.reference .head .head) bodyRaw
private theorem mappedDirectRaw :
    ClosedSourceExpressionEvaluates (shift savedOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
      (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap directCall
      (RuntimeValue.ofCore payload) heap := by
  simpa only [captures, heap, mappedEnvironment, mapRuntimeCapturedOwners_ofCore,
    mapRuntimeStoreOwners_ofCore, RuntimeValue.mapOwners_ofCore] using
      directRaw.mapOwners shift shift_injective
/-- Direct creation/application has concrete old, mapped, and Core endpoints,
then the bridge classifies every arbitrary mapped endpoint. -/
theorem direct_application_boundary {actualValue : RuntimeValue}
    {actualFinal : List RuntimeValue} :
    ¬ Function.Surjective shift ∧ store ≠ [] ∧
    environment.ids[0]? = some payloadId ∧ environment.ids[1]? = some noiseId ∧
    inputs.names[0]? = some ("payload", payloadId) ∧
    inputs.names[2]? = some ("payload", shadowId) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] (shift savedOwner)
      mappedInputs source (.function .unit .unit) = some (.lambda .unit .unit (.var 0)) ∧
    mappedEnvironment.ids = mappedInputs.context.ids ∧
    ClosedSourceExpressionEvaluates savedOwner inputs.names captures heap directCall
      (RuntimeValue.ofCore payload) heap ∧
    ClosedSourceExpressionEvaluates (shift savedOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
      (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap directCall
      (RuntimeValue.ofCore payload) heap ∧
    ResolvesLocalExpression (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
      argument (.var (ownerLocalIdMap shift payloadId)) ∧
    Resolved.Lowers mappedEnvironment.ids (.var (ownerLocalIdMap shift payloadId)) (.var 0) ∧
    Core.Evaluates environment.values store
      (.apply (.lambda .unit .unit (.var 0)) (.var 0)) payload store ∧
    (ClosedSourceExpressionEvaluates (shift savedOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
      (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) heap directCall
      actualValue actualFinal ↔
      ∃ value finalStore, actualValue = RuntimeValue.ofCore value ∧
        actualFinal = finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates environment.values store
          (.apply (.lambda .unit .unit (.var 0)) (.var 0)) value finalStore) := by
  have bridge := closedSourceExpectedDataLambda_application_mapOwners_core_iff
    shift shift_injective shape dataBody checked sameIds argumentData argumentResolution
    argumentLowering (initialStore := store) (callSpan := span 21)
    (argumentsSpan := span 22) (actualValue := actualValue) (actualFinal := actualFinal)
  exact ⟨shift_not_surjective, by decide, rfl, rfl, rfl, rfl, mappedChecked, rfl, directRaw,
    mappedDirectRaw, .identifier .head, .var .head, .apply .lambda (.var rfl) (.var rfl),
    (by simpa only [mappedEnvironment, heap, directCall] using bridge.2.2.2.2)⟩

private def saved : RuntimeValue := .sourceClosure source savedOwner inputs.names captures
private def callerNames : LocalNameTable :=
  [("fn", calleeId), ("arg", argumentId), ("fn", foreignCalleeId)]
private def callerCaptured : List (Resolved.LocalId × RuntimeValue) :=
  [(argumentId, RuntimeValue.ofCore payload), (calleeId, saved),
    (calleeId, .sourceClosure argument foreignOwner [] []),
    (foreignCalleeId, saved)]
private theorem calleeRaw : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured
    heap callee saved heap := .reference .head (.tail (by decide) .head)
private theorem callerArgumentRaw : ClosedSourceExpressionEvaluates callerOwner callerNames
    callerCaptured heap callerArgument (RuntimeValue.ofCore payload) heap :=
  .reference (.tail (by decide) .head) .head
private theorem invocationRaw : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured
    heap invocation (RuntimeValue.ofCore payload) heap :=
  .call shape calleeRaw callerArgumentRaw bodyRaw
private theorem mappedCalleeRaw :
    ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap callee
      (.sourceClosure source (shift savedOwner)
        (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
        (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))) heap := by
  simpa only [saved, captures, heap, mappedEnvironment, RuntimeValue.mapOwners_sourceClosure,
    mapRuntimeCapturedOwners_ofCore, mapRuntimeStoreOwners_ofCore] using
      calleeRaw.mapOwners shift shift_injective
private theorem mappedCallerArgumentRaw :
    ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap callerArgument
      (RuntimeValue.ofCore payload) heap := by
  simpa only [heap, mapRuntimeStoreOwners_ofCore, RuntimeValue.mapOwners_ofCore] using
    callerArgumentRaw.mapOwners shift shift_injective
private theorem mappedInvocationRaw :
    ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap invocation
      (RuntimeValue.ofCore payload) heap := by
  simpa only [heap, mapRuntimeStoreOwners_ofCore, RuntimeValue.mapOwners_ofCore] using
    invocationRaw.mapOwners shift shift_injective
private theorem invocationCore :
    Core.Evaluates (payload :: environment.values) store (.var 0) payload store := .var rfl

/-- A separately saved closure retains duplicate and foreign caller rows. Both
prefixes and both complete calls exist before arbitrary mapped endpoints use the bridge. -/
theorem saved_invocation_boundary {actualValue : RuntimeValue}
    {actualFinal : List RuntimeValue} :
    callerNames[2]? = some ("fn", foreignCalleeId) ∧
    callerCaptured[1]?.map Prod.fst = some calleeId ∧
    callerCaptured[2]?.map Prod.fst = some calleeId ∧
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured heap invocation
      (RuntimeValue.ofCore payload) heap ∧
    ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap callee
      (.sourceClosure source (shift savedOwner)
        (LocalNameTable.mapIds (ownerLocalIdMap shift) inputs.names)
        (mappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))) heap ∧
    ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap callerArgument
      (RuntimeValue.ofCore payload) heap ∧
    ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap invocation
      (RuntimeValue.ofCore payload) heap ∧
    Core.Evaluates (payload :: environment.values) store (.var 0) payload store ∧
    (ClosedSourceExpressionEvaluates (shift callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
      (mapRuntimeCapturedOwners shift callerCaptured) heap invocation actualValue actualFinal ↔
      ∃ value finalStore, actualValue = RuntimeValue.ofCore value ∧
        actualFinal = finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates (payload :: environment.values) store (.var 0) value finalStore) := by
  have bridge := closedSourceExpectedDataLambda_invocation_mapOwners_core_iff
    shift shift_injective (initialStore := heap) (calleeStore := heap) shape dataBody checked sameIds
    (by simpa only [heap, mappedEnvironment, mapRuntimeStoreOwners_ofCore] using mappedCalleeRaw)
    (by simpa only [heap, mapRuntimeStoreOwners_ofCore] using mappedCallerArgumentRaw)
    (callSpan := span 32) (argumentsSpan := span 33) (bodyStore := store)
    (actualValue := actualValue) (actualFinal := actualFinal)
  have exactBridge :
      ClosedSourceExpressionEvaluates (shift callerOwner)
        (LocalNameTable.mapIds (ownerLocalIdMap shift) callerNames)
        (mapRuntimeCapturedOwners shift callerCaptured) heap invocation actualValue actualFinal ↔
      ∃ value finalStore, actualValue = RuntimeValue.ofCore value ∧
        actualFinal = finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates (payload :: environment.values) store (.var 0) value finalStore := by
    simpa only [heap, invocation, mapRuntimeStoreOwners_ofCore] using bridge.2.2
  exact ⟨rfl, rfl, rfl, invocationRaw, mappedCalleeRaw, mappedCallerArgumentRaw,
    mappedInvocationRaw, invocationCore, exactBridge⟩

private def swappedEnvironment : Resolved.Environment :=
  [(noiseId, .word (Core.Word.ofNatModulo 99)), (payloadId, payload),
    (shadowId, .bool false)]
private def swappedCaptures : List (Resolved.LocalId × RuntimeValue) :=
  swappedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))
private theorem misalignedRaw :
    ClosedSourceExpressionEvaluates savedOwner inputs.names swappedCaptures heap directCall
      (RuntimeValue.ofCore payload) heap := by
  have created : ClosedSourceExpressionEvaluates savedOwner inputs.names swappedCaptures heap source
      (.sourceClosure source savedOwner inputs.names swappedCaptures) heap := .creation shape
  have evaluatedArgument : ClosedSourceExpressionEvaluates savedOwner inputs.names swappedCaptures
      heap argument (RuntimeValue.ofCore payload) heap :=
    .reference .head (.tail (by decide) .head)
  have evaluatedBody : ClosedSourceBodyEvaluates savedOwner
      ((parameter.value, Resolved.freshLocalId savedOwner inputs.ids) :: inputs.names)
      ((Resolved.freshLocalId savedOwner inputs.ids, RuntimeValue.ofCore payload) ::
        swappedCaptures) heap body (RuntimeValue.ofCore payload) heap :=
    .expression (.reference .head .head)
  exact .call shape created evaluatedArgument evaluatedBody
private def nonDataBody : Syntax.Block :=
  ⟨span 50, [⟨span 51, .returnStmt (some source)⟩]⟩
private def nonimage : RuntimeValue :=
  .sourceClosure source savedOwner
    ((parameter.value, Resolved.freshLocalId savedOwner inputs.ids) :: inputs.names)
    ((Resolved.freshLocalId savedOwner inputs.ids, RuntimeValue.ofCore payload) :: captures)
private theorem nonDataRaw : ClosedSourceBodyEvaluates savedOwner
    ((parameter.value, Resolved.freshLocalId savedOwner inputs.ids) :: inputs.names)
    ((Resolved.freshLocalId savedOwner inputs.ids, RuntimeValue.ofCore payload) :: captures)
    heap nonDataBody nonimage heap := .expression (.creation shape)

/-- Raw success alone cannot recover expected-function checking, ID alignment,
the data-body gate, or a Core-image result. -/
theorem missing_premises_remain_observable :
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] savedOwner inputs source .unit = none ∧
    swappedEnvironment.ids ≠ inputs.context.ids ∧
    ClosedSourceExpressionEvaluates savedOwner inputs.names swappedCaptures heap directCall
      (RuntimeValue.ofCore payload) heap ∧
    ClosedSourceBodyEvaluates savedOwner
      ((parameter.value, Resolved.freshLocalId savedOwner inputs.ids) :: inputs.names)
      ((Resolved.freshLocalId savedOwner inputs.ids, RuntimeValue.ofCore payload) :: captures)
      heap nonDataBody nonimage heap ∧
    ¬ ClosedSourceDataBody nonDataBody ∧ ¬ ∃ value, nonimage = RuntimeValue.ofCore value := by
  refine ⟨rfl, ?_, misalignedRaw, nonDataRaw, ?_, ?_⟩
  · change [noiseId, payloadId, shadowId] ≠ [payloadId, noiseId, shadowId]
    decide
  · intro admitted
    cases admitted with
    | expression child => cases child
  · rintro ⟨value, same⟩
    have projected := congrArg RuntimeValue.toCore? same
    simp only [nonimage, RuntimeValue.toCore?, RuntimeValue.toCore?_ofCore, reduceCtorEq] at projected

end Tests.ADR0315OwnerExpectedDataLambdaCoreConsumer
