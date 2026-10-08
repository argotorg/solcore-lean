import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer

/-! Genuine method lambda formation supplies a Header-free selected call.
The original compiler receipt, two accepted guards and ordered arguments stay
explicit. Arguments run at the actual formation post; the shared family's
strict body child consumes their real reached pool and original Source types. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSelectedCall
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

section Completion
variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)

/-- Accepted completion retains the exact capture suffix and actual stores. -/
inductive Completion (budget : Nat) (arguments : Expr) (store : Store) : Value → Store → Prop where
  | failed {size : Nat} {input : Ty} {token : Value} {after : Store}
      (trace : EvaluationSize size (.unit :: value code captured.embedding history.native actual :: actual) store
        ((arguments.weakenAt 0).weakenAt 0) (.inLeft input token) after)
      (strict : size < budget) : Completion budget arguments store (.inLeft code.receipt.resultCore token) after
  | applied {argumentsSize bodySize : Nat} {input : Ty} {argument result : Value} {middle after : Store}
      (argumentsTrace : EvaluationSize argumentsSize (.unit :: value code captured.embedding history.native actual :: actual) store
        ((arguments.weakenAt 0).weakenAt 0) (.inRight input argument) middle)
      (bodyTrace : EvaluationSize bodySize
        (argument :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native :: actual)
        middle (code.body.rename captured.embedding.lift.lift) result after)
      (argumentsStrict : argumentsSize < budget) (bodyStrict : bodySize < budget) :
      Completion budget arguments store result after

/-- Finite inversion of the existing call protocol identifies only the actual
callee, accepted guards and pure projections. The body remains its real child. -/
theorem completed {budget size : Nat} {store finalStore : Store}
    {callee arguments : Expr} {gates : List CallableContract.Gate} {unknown : Word} {result : Value}
    (formed : Evaluates actual store callee
      (.inRight .word (value code captured.embedding history.native actual)) store)
    (stage : CallableContract.decision gates .beforeArguments unknown code.descriptor.id = none)
    (arity : CallableContract.decision gates .beforeApplication unknown code.descriptor.id = none)
    (trace : EvaluationSize size actual store
      (CallableContract.call gates unknown code.receipt.resultCore callee arguments) result finalStore)
    (within : size ≤ budget) : Completion captured code history budget arguments store result finalStore := by
  have descriptor : Evaluates (value code captured.embedding history.native actual :: actual) store
      (.second (.var 0)) (.word code.descriptor.id) store := .second (.var rfl)
  cases CallableIndirectCallBounds.call_completed trace within with
  | calleeFailure first _ =>
    obtain ⟨same, _⟩ := evaluation_deterministic first.sound formed
    cases same
  | stageRejected first gate _ _ =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic first.sound formed
    cases same
    obtain ⟨same, _⟩ := CallableIndirectCallBounds.dispatch_decision descriptor gate
    simp only [stage, CallableContract.resultValue] at same
    cases same
  | argumentFailure first gate argumentsTrace _ _ strict =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic first.sound formed
    cases same
    obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision descriptor gate
    simp only [stage, CallableContract.resultValue] at same
    cases same
    exact .failed argumentsTrace strict
  | arityRejected first gate _ second _ _ _ _ =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic first.sound formed
    cases same
    obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision descriptor gate
    simp only [stage, CallableContract.resultValue] at same
    cases same
    obtain ⟨same, _⟩ := CallableIndirectCallBounds.dispatch_decision (.second (.var rfl)) second
    simp only [arity, CallableContract.resultValue] at same
    cases same
  | applied first gate argumentsTrace second functionTrace parameterTrace bodyTrace
      _ _ argumentsStrict _ _ _ bodyStrict =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic first.sound formed
    cases same
    obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision descriptor gate
    simp only [stage, CallableContract.resultValue] at same
    cases same
    obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision (.second (.var rfl)) second
    simp only [arity, CallableContract.resultValue] at same
    cases same
    obtain ⟨same, rfl⟩ := evaluation_deterministic
      (right := .closure code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore)
        (code.body.rename captured.embedding.lift.lift)
        (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native :: actual))
      functionTrace.sound (.second (.first (.var rfl)))
    cases same
    obtain ⟨same, rfl⟩ := evaluation_deterministic parameterTrace.sound (.var rfl)
    cases same
    exact .applied argumentsTrace bodyTrace argumentsStrict bodyStrict
end Completion

/-- This static row conversion retains every represented value in order. -/
private theorem arguments_of_values {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} (bindings : List CallableIndexedParameterCertificates.Binding)
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (bindings.map (fun binding => binding.1.scheme.body)) (bindings.map Prod.snd) sources payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads := by
  induction bindings generalizing sources payloads with
  | nil => cases represented; exact .nil
  | cons binding tail ih => cases represented with
    | cons head rest => exact .cons head (ih rest)

section Parent
variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {id : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation function.source scope
    id code.id ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {certificate : GenericExpressionMeaning.Certificate}
  (selection : CallableIndexedOwnedSelectedIndirectHeads.Selection (compiled := compiled)
    (faults := faults) (certificate := certificate) compiler prepared code)
  (sameCallee : compiler.calleeCode = code.lowered)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (sourceArguments : ExpressionsHaveTypes function.source function.context ids support.body.types)
  (sourceCount : support.body.types.length = metadata.argumentCount)
  (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include wellFormed runtime covers locals admitted sourceArguments in
/-- Original Source argument preservation supplies both raw parameter types
and deep typing of the actual argument heap. Native vectors are independent. -/
private theorem arguments_admitted {size : Nat} {arguments : List Dynamic.Value} {middle : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap ids arguments middle) :
    Dynamic.ValuesHaveTypes function.context middle arguments support.body.types ∧
      Dynamic.HeapWellTyped function.context middle := by
  have expressionPreserves : Dynamic.ExpressionExecutionPreserves (Program.ofChecked compiled.sourceProgram)
      function.context function.evidence function.source function.captured := by
    intro before after id value type covers locals heapTyped typed execution
    exact wellFormed.wholeLanguagePreservation.expression function.context function.evidence function.source
      function.captured before after id value type runtime covers locals heapTyped typed execution
  have reached := Dynamic.ExpressionsEvaluate.preserves expressionPreserves covers locals admitted.heap sourceArguments trace.sound
  exact ⟨reached.1, reached.2.1⟩

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include ordinary coercions heaps admitted selection sourceArguments in
/-- The genuine formation value is the real guard prefix of the unchanged
admitted sequence fold. Its Source typing row stays independent of Tree types. -/
theorem sequence_preserves (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
      function.context function.evidence function.source certificate faults size)
    (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured) :
    ProtectedStateExpressionSequenceProducer.Preserves
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) ⟨initial, packet⟩ budget := by
  intro size outcome after trace bounded
  obtain ⟨_source, _native, represented, _determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation captured code support owner initial packet profile
      heaps.runtime_hasTypes ordinary coercions
  have closureTyped := (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile).runtime_hasType
    (registry := registry) represented
  exact CallableIndexedOwnedAdmittedSequenceProducer.preserves
    (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ admitted selection.children support.unique sourceArguments captured.represented heaps locals
    (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix captured.agrees _) .unit)
    (.cons .unit (.cons closureTyped captured.typed)) budget children trace bounded

include ordinary coercions heaps admitted selection sourceArguments in
/-- Native arguments use the same actual guarded input and independent Source
row, preserving the original strict sequence grade. -/
theorem sequence_reflects (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
      function.context function.evidence function.source certificate faults size)
    (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured) :
    ProtectedStateExpressionSequenceProducer.Reflects
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) ⟨initial, packet⟩ budget := by
  intro size result finalStore trace bounded
  obtain ⟨_source, _native, represented, _determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation captured code support owner initial packet profile
      heaps.runtime_hasTypes ordinary coercions
  have closureTyped := (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile).runtime_hasType
    (registry := registry) represented
  exact CallableIndexedOwnedAdmittedSequenceProducer.reflects
    (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ admitted selection.children support.unique sourceArguments captured.represented heaps locals
    (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix captured.agrees _) .unit)
    (.cons .unit (.cons closureTyped captured.typed)) budget children trace bounded

include syntaxTree wellFormed runtime covers locals admitted sourceArguments selection in
/-- The actual ordered argument post supplies raw Source admission and its
current owned row to the selected parameter/body prefix. -/
theorem arguments_preserves
    (budget : Nat)
    (sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) ⟨initial, packet⟩ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget)
    {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      function.context function.evidence function.source function.captured heap ids arguments middle)
    (argumentsWithin : argumentsSize ≤ budget)
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize
      function.context function.evidence function.evidence middle (.closure function) arguments outcome after)
    (callWithin : callSize ≤ budget) :
    ∃ payloads middleStore result finalStore finalMap finalWorld,
      Evaluates (.unit :: value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual :: actual)
        store (((SourceCoreCalls.packArguments compiler.codes).expression.rename captured.embedding).weakenAt 0 |>.weakenAt 0)
        (.inRight .word (DataPatternValues.packValues payloads)) middleStore ∧
      Evaluates (DataPatternValues.packValues payloads :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native :: actual)
        middleStore (code.body.rename captured.embedding.lift.lift) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
        ⟨initial, packet⟩ ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩ := by
  obtain ⟨packed, middleStore, middleMap, middleWorld, argumentEvaluation, argumentResult, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentState, argumentRelated⟩ :=
    sequence (.values argumentsTrace) argumentsWithin
  cases argumentResult with
  | @values sources payloads represented =>
    rw [selection.nativeTypes] at represented
    have representedArguments := arguments_of_values code.receipt.loweredParameters represented
    let future := captured.extend argumentMaps argumentWorlds
    let history := CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet
    have raw := arguments_admitted captured code support owner initial packet sourceArguments wellFormed runtime covers locals admitted argumentsTrace
    have stable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative initial argumentState.val admitted.rows argumentFrame
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : future.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code support]
      exact packet.observed.reference
    have capturesValid : FunctionValues.SourceCapturesValid middle (.closure function) :=
      (show FunctionValues.SourceCapturesValid heap (.closure function) from locals).extend argumentMetadata
    have meaning := CallableIndexedOwnedExtendedJointReadyContinuations.method_lambda_source_continuation
      (nativeArguments := payloads) (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed
      future code history support (CallableIndexedOwnedMethodLambdaFormationReceipts.source_origin captured code support owner initial packet)
      owner packet.observed (CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code support owner initial packet)
      argumentState.val selection.escaped raw.2 raw.1 stable syntaxTree budget below
    obtain ⟨result, finalStore, finalMap, finalWorld, bodyEvaluation, resultRep, finalHeaps,
        maps, worlds, frame, metadata, finalState, related⟩ :=
      CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at
        future code history support.body.toContext (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
        representedArguments owner argumentState.val middleHeaps capturesValid reference currentCarried
        (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) (support.body_origin selection.escaped)
        budget meaning called callWithin
    obtain ⟨returned, _samePool, relatedCaller⟩ :=
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named).restore
        ⟨initial, packet⟩ finalState (argumentMaps.trans maps) (argumentWorlds.trans worlds)
        (argumentFrame.trans frame) (argumentMetadata.trans metadata) (argumentRelated.trans related)
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentEvaluation
    exact ⟨_, middleStore, result, finalStore, finalMap, finalWorld, argumentEvaluation, bodyEvaluation,
      resultRep, finalHeaps, argumentMaps.trans maps, argumentWorlds.trans worlds,
      argumentFrame.trans frame, argumentMetadata.trans metadata, returned, relatedCaller⟩

include syntaxTree wellFormed runtime covers locals admitted sourceArguments selection in
/-- The native argument completion reconstructs its own Source grade before
selecting the exact actual body prefix and the same restored caller pool. -/
theorem arguments_reflects (budget : Nat)
    (sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) ⟨initial, packet⟩ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget)
    {argumentsSize bodySize : Nat} {argumentInput : Ty} {argument result : Value} {middleStore finalStore : Store}
    (argumentsTrace : EvaluationSize argumentsSize (.unit :: value code captured.embedding
      (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual :: actual)
      store (((SourceCoreCalls.packArguments compiler.codes).expression.rename captured.embedding).weakenAt 0 |>.weakenAt 0)
      (.inRight argumentInput argument) middleStore)
    (argumentsWithin : argumentsSize < budget)
    (bodyTrace : EvaluationSize bodySize (argument :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
      (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native :: actual)
      middleStore (code.body.rename captured.embedding.lift.lift) result finalStore)
    (bodyWithin : bodySize ≤ budget) :
    ∃ sourceArgumentsSize sourceCallSize arguments middle outcome after finalMap finalWorld,
      SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceArgumentsSize
        function.context function.evidence function.source function.captured heap ids arguments middle ∧
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceCallSize
        function.context function.evidence function.evidence middle (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
        ⟨initial, packet⟩ ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩ := by
  rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
  obtain ⟨sourceArgumentsSize, argumentOutcome, middle, middleMap, middleWorld, argumentTrace, argumentResult, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentState, argumentRelated⟩ :=
    sequence argumentsTrace argumentsWithin
  cases argumentResult with
  | @values sources payloads represented =>
    cases argumentTrace with
    | values sourceArgumentsTrace =>
      rw [selection.nativeTypes] at represented
      have representedArguments := arguments_of_values code.receipt.loweredParameters represented
      let future := captured.extend argumentMaps argumentWorlds
      let history := CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet
      have raw := arguments_admitted captured code support owner initial packet sourceArguments wellFormed runtime covers locals admitted sourceArgumentsTrace
      have stable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative initial argumentState.val admitted.rows argumentFrame
      obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
      have reference : future.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code support]
        exact packet.observed.reference
      have capturesValid : FunctionValues.SourceCapturesValid middle (.closure function) :=
        (show FunctionValues.SourceCapturesValid heap (.closure function) from locals).extend argumentMetadata
      have meaning := CallableIndexedOwnedExtendedJointReadyContinuations.method_lambda_native_continuation
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed
        future code history support (CallableIndexedOwnedMethodLambdaFormationReceipts.source_origin captured code support owner initial packet)
        owner packet.observed (CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code support owner initial packet)
        argumentState.val selection.escaped raw.2 raw.1 stable syntaxTree budget below
      obtain ⟨sourceCallSize, outcome, after, finalMap, finalWorld, called, resultRep, finalHeaps,
          maps, worlds, frame, metadata, finalState, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at
          future code history support.body.toContext (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
          representedArguments owner argumentState.val middleHeaps capturesValid reference currentCarried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) (support.body_origin selection.escaped)
          budget meaning bodyTrace bodyWithin
      obtain ⟨returned, _samePool, relatedCaller⟩ :=
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named).restore
          ⟨initial, packet⟩ finalState (argumentMaps.trans maps) (argumentWorlds.trans worlds)
          (argumentFrame.trans frame) (argumentMetadata.trans metadata) (argumentRelated.trans related)
      exact ⟨sourceArgumentsSize, sourceCallSize, sources, middle, outcome, after, finalMap, finalWorld,
        sourceArgumentsTrace, called, resultRep, finalHeaps, argumentMaps.trans maps, argumentWorlds.trans worlds,
        argumentFrame.trans frame, argumentMetadata.trans metadata, returned, relatedCaller⟩

include selection in
/-- The same original parent type and projected result are retained. -/
private theorem parent_result {finalMap : LocationMap} {finalWorld : StoreTyping}
    {outcome : Dynamic.ExpressionOutcome} {result : Value}
    (represented : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result) :
    GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
      finalMap finalWorld compiler.original.type lowered.type faults outcome result := by
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  rw [loweredType, selection.nativeResult]
  cases represented with
  | value related => exact .value (.compatible selection.rawResult related)
  | fault matched => exact .fault matched

/-- The original Source lambda occurrence accompanies the exact compiler code. -/
def lambda : CallableIndexedOwnedSelectedIndirectHeads.LambdaCallee function.source code.id :=
  ⟨code.sourceNode, code.sourceFound, function.parameters, function.resultType, function.body,
    code.sourceForm, coercions⟩

theorem lambda_function : (lambda captured code coercions).function
    function.context function.evidence function.captured = function := rfl

variable (parentTyped : ExpressionHasType function.source function.context id compiler.original.type)

/-- Full whole-parent outputs preserve the same actual reached principal pool,
with deep admission only on successful Source completion. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
    finalMap finalWorld compiler.original.type lowered.type faults outcome result ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
  ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
      ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩,
    (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
    PostAdmission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      function.context compiler.original.type outcome reached

include selection sameCallee ordinary coercions parent sourceCount sourceArguments syntaxTree
  wellFormed runtime covers locals heaps admitted parentTyped in
/-- The original method-lambda formation closes the callee internally. Ordered
admitted children and the strict dependent body IH close the whole call. -/
theorem preserves_bounded (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
      function.context function.evidence function.source certificate faults size)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap id outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename captured.embedding) result finalStore ∧
      ResultAt captured code support owner initial packet profile compiler outcome after result finalStore finalMap finalWorld := by
  obtain ⟨calleeSize, argumentsSize, callSize, calleeTrace, suffix, _calleeSmall, argumentsSmall, callWithin⟩ :=
    CallableIndexedOwnedSelectedIndirectHeads.suffix_of_source compiler.found compiler.originalForm parent.coercions
      compiler.argumentCoercions parent.arity (lambda captured code coercions) support.unique wellFormed runtime covers locals
      admitted.heap sourceArguments sourceCount trace
  rw [lambda_function captured code coercions] at calleeTrace suffix
  obtain ⟨_source, formed, _represented, _determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation captured code support owner initial packet profile
      heaps.runtime_hasTypes ordinary coercions
  have calleeEvaluation : Evaluates actual store (compiler.calleeCode.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)) store := by
    rw [sameCallee]; exact formed
  have sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) ⟨initial, packet⟩ budget := by
    intro size outcome after childTrace childBound
    exact sequence_preserves captured code support owner initial packet profile compiler prepared selection
      ordinary coercions sourceArguments heaps admitted budget children locals childTrace childBound
  have emitted := prepared.lowered_rename compiler captured.embedding
  rw [selection.nativeResult] at emitted
  cases suffix with
  | argumentFault failed =>
    obtain ⟨value, finalStore, finalMap, finalWorld, argumentEvaluation, result, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ :=
      sequence (.fault failed) (Nat.le_trans (Nat.le_of_lt argumentsSmall) within)
    cases result with
    | fault matched =>
      rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentEvaluation
      have whole := CallableContract.call_argument_failure (result := code.receipt.resultCore) prepared.site.gates native.diagnostics.unknown
        calleeEvaluation selection.stageAccepted argumentEvaluation
      rw [← emitted] at whole
      exact ⟨_, finalStore, finalMap, finalWorld, whole,
        parent_result captured code profile compiler prepared selection (.fault matched), finalHeaps,
        maps, worlds, frame, metadata, reached, related,
        after_expression_sized (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals parentTyped trace frame⟩
  | called argumentsTrace called =>
    obtain ⟨payloads, middleStore, result, finalStore, finalMap, finalWorld, argumentEvaluation, bodyEvaluation,
        resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      arguments_preserves captured code support owner initial packet profile compiler prepared selection sourceArguments
        syntaxTree wellFormed runtime covers locals admitted budget sequence below argumentsTrace
        (Nat.le_trans (Nat.le_of_lt argumentsSmall) within) called (Nat.le_trans callWithin within)
    have whole := CallableContract.call_success prepared.site.gates native.diagnostics.unknown calleeEvaluation
      selection.stageAccepted argumentEvaluation selection.arityAccepted bodyEvaluation
    rw [← emitted] at whole
    exact ⟨result, finalStore, finalMap, finalWorld, whole,
      parent_result captured code profile compiler prepared selection resultRep, finalHeaps,
      maps, worlds, frame, metadata, reached, related,
      after_expression_sized (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

include selection sameCallee ordinary coercions parent sourceCount sourceArguments syntaxTree
  wellFormed runtime covers locals heaps admitted parentTyped in
/-- The original native call exposes its measured arguments and body children.
Reflection reconstructs the whole Source parent with independent grades. -/
theorem reflects_bounded (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
      function.context function.evidence function.source certificate faults size)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget)
    {size : Nat} {result : Value} {finalStore : Store}
    (trace : EvaluationSize size actual store (lowered.expression.rename captured.embedding) result finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap id outcome after ∧
      ResultAt captured code support owner initial packet profile compiler outcome after result finalStore finalMap finalWorld := by
  obtain ⟨sourceCallee, formed, _represented, _determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation captured code support owner initial packet profile
      heaps.runtime_hasTypes ordinary coercions
  obtain ⟨calleeSize, calleeTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size sourceCallee
  have calleeEvaluation : Evaluates actual store (compiler.calleeCode.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)) store := by
    rw [sameCallee]; exact formed
  have sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) ⟨initial, packet⟩ budget := by
    intro size result finalStore childTrace childBound
    exact sequence_reflects captured code support owner initial packet profile compiler prepared selection
      ordinary coercions sourceArguments heaps admitted budget children locals childTrace childBound
  have emitted := prepared.lowered_rename compiler captured.embedding
  rw [emitted, selection.nativeResult] at trace
  cases completed captured code (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet)
      calleeEvaluation selection.stageAccepted selection.arityAccepted trace within with
  | failed argumentsTrace argumentsStrict =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨sourceArgumentsSize, argumentOutcome, after, finalMap, finalWorld, argumentTrace, resultRep, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ := sequence argumentsTrace argumentsStrict
    cases resultRep with
    | fault matched =>
      cases argumentTrace with
      | fault failed =>
        obtain ⟨sourceSize, sourceTrace⟩ := CallableIndexedOwnedIndirectSourceAdapters.SourceSuffix.to_expression
          compiler.found compiler.originalForm parent.requirements parent.coercions compiler.argumentCoercions parent.arity
          wellFormed runtime covers locals admitted.heap sourceArguments sourceCount calleeTrace
          (CallableIndexedOwnedIndirectExpressionHeads.SourceSuffix.argumentFault failed)
        exact ⟨sourceSize, _, after, finalMap, finalWorld, sourceTrace,
          parent_result captured code profile compiler prepared selection (.fault matched), finalHeaps,
          maps, worlds, frame, metadata, reached, related,
          after_expression_sized (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals parentTyped sourceTrace frame⟩
  | applied argumentsTrace bodyTrace argumentsStrict bodyStrict =>
    obtain ⟨sourceArgumentsSize, sourceCallSize, arguments, middle, outcome, after, finalMap, finalWorld,
        sourceArgumentsTrace, called, resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      arguments_reflects captured code support owner initial packet profile compiler prepared selection sourceArguments
        syntaxTree wellFormed runtime covers locals admitted budget sequence below argumentsTrace argumentsStrict bodyTrace (Nat.le_of_lt bodyStrict)
    obtain ⟨sourceSize, sourceTrace⟩ := CallableIndexedOwnedIndirectSourceAdapters.SourceSuffix.to_expression
      compiler.found compiler.originalForm parent.requirements parent.coercions compiler.argumentCoercions parent.arity
      wellFormed runtime covers locals admitted.heap sourceArguments sourceCount calleeTrace
      (CallableIndexedOwnedIndirectExpressionHeads.SourceSuffix.called sourceArgumentsTrace called)
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace,
      parent_result captured code profile compiler prepared selection resultRep, finalHeaps,
      maps, worlds, frame, metadata, reached, related,
      after_expression_sized (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals parentTyped sourceTrace frame⟩

/-- A finite original compiler selection contains only static Source/code
receipts. Its parameters retain the full authentic method Support and Code. -/
structure Receipt (certificate : GenericExpressionMeaning.Certificate) where
  native : SourceCoreGeneralFunctions.CallableContext
  prepared : Prepared compiler native
  parent : SourceParent compiler
  selection : CallableIndexedOwnedSelectedIndirectHeads.Selection (compiled := compiled)
    (faults := faults) (certificate := certificate) compiler prepared code
  sameCallee : compiler.calleeCode = code.lowered
  ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions []
  coercions : code.sourceNode.coercions = []
  sourceArguments : ExpressionsHaveTypes function.source function.context ids support.body.types
  sourceCount : support.body.types.length = metadata.argumentCount
  syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType
  parentTyped : ExpressionHasType function.source function.context id compiler.original.type

include wellFormed runtime covers locals heaps admitted in
/-- This actual static receipt selects the internally proved literal producer;
only genuine strictly smaller argument and extended-family body children remain. -/
theorem preserves_at_receipt (issued : Receipt captured code support compiler certificate) (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
      function.context function.evidence function.source certificate faults size)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap id outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename captured.embedding) result finalStore ∧
      ResultAt captured code support owner initial packet profile compiler outcome after result finalStore finalMap finalWorld := by
  exact preserves_bounded (captured := captured) (code := code) (support := support) (owner := owner)
    (initial := initial) (packet := packet) (profile := profile) (compiler := compiler)
    (prepared := issued.prepared) (parent := issued.parent) (selection := issued.selection)
    (sameCallee := issued.sameCallee) (ordinary := issued.ordinary) (coercions := issued.coercions)
    (sourceArguments := issued.sourceArguments) (sourceCount := issued.sourceCount) (syntaxTree := issued.syntaxTree)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals) (heaps := heaps)
    (admitted := admitted) (parentTyped := issued.parentTyped) budget children below trace within

include wellFormed runtime covers locals heaps admitted in
/-- Native receipt selection preserves its measured child bounds while the
whole Source trace and successful admission are reconstructed independently. -/
theorem reflects_at_receipt (issued : Receipt captured code support compiler certificate) (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
      function.context function.evidence function.source certificate faults size)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget)
    {size : Nat} {result : Value} {finalStore : Store}
    (trace : EvaluationSize size actual store (lowered.expression.rename captured.embedding) result finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap id outcome after ∧
      ResultAt captured code support owner initial packet profile compiler outcome after result finalStore finalMap finalWorld := by
  exact reflects_bounded (captured := captured) (code := code) (support := support) (owner := owner)
    (initial := initial) (packet := packet) (profile := profile) (compiler := compiler)
    (prepared := issued.prepared) (parent := issued.parent) (selection := issued.selection)
    (sameCallee := issued.sameCallee) (ordinary := issued.ordinary) (coercions := issued.coercions)
    (sourceArguments := issued.sourceArguments) (sourceCount := issued.sourceCount) (syntaxTree := issued.syntaxTree)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals) (heaps := heaps)
    (admitted := admitted) (parentTyped := issued.parentTyped) budget children below trace within

end Parent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSelectedCall
