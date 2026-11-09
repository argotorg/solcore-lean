import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReadyContinuations
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.ExpressionTrees

/-!
# Owned callables: method lambdas

Selected calls, expression heads and runtime bounds of method lambdas.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSelectedCall
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
variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {actual : Environment}
  (code : Code compiled.indexed function scope administrative) (history : History code)
  (embedding : Renaming) (closureActual : Environment)

/-- Accepted completion retains the exact capture suffix and actual stores. The
callee value is the formed closure over its own native environment; arguments
run in the caller's environment and the body in the closure's. -/
inductive Completion (budget : Nat) (arguments : Expr) (store : Store) : Value → Store → Prop where
  | failed {size : Nat} {input : Ty} {token : Value} {after : Store}
      (trace : EvaluationSize size (.unit :: value code embedding history.native closureActual :: actual) store
        ((arguments.weakenAt 0).weakenAt 0) (.inLeft input token) after)
      (strict : size < budget) : Completion budget arguments store (.inLeft code.receipt.resultCore token) after
  | applied {argumentsSize bodySize : Nat} {input : Ty} {argument result : Value} {middle after : Store}
      (argumentsTrace : EvaluationSize argumentsSize (.unit :: value code embedding history.native closureActual :: actual)
        store ((arguments.weakenAt 0).weakenAt 0) (.inRight input argument) middle)
      (bodyTrace : EvaluationSize bodySize
        (argument :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native :: closureActual)
        middle (code.body.rename embedding.lift.lift) result after)
      (argumentsStrict : argumentsSize < budget) (bodyStrict : bodySize < budget) :
      Completion budget arguments store result after

/-- Finite inversion of the existing call protocol identifies only the actual
callee, accepted guards and pure projections. The body remains its real child. -/
theorem completed {budget size : Nat} {store calleeStore finalStore : Store}
    {callee arguments : Expr} {gates : List CallableContract.Gate} {unknown : Word} {result : Value}
    (formed : Evaluates actual store callee
      (.inRight .word (value code embedding history.native closureActual)) calleeStore)
    (stage : CallableContract.decision gates .beforeArguments unknown code.descriptor.id = none)
    (arity : CallableContract.decision gates .beforeApplication unknown code.descriptor.id = none)
    (trace : EvaluationSize size actual store
      (CallableContract.call gates unknown code.receipt.resultCore callee arguments) result finalStore)
    (within : size ≤ budget) :
    Completion (actual := actual) code history embedding closureActual budget arguments calleeStore result finalStore := by
  have descriptor : Evaluates (value code embedding history.native closureActual :: actual) calleeStore
      (.second (.var 0)) (.word code.descriptor.id) calleeStore := .second (.var rfl)
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
        (code.body.rename embedding.lift.lift)
        (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native :: closureActual))
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
  (copied : code.policy.snapshotLambda code.id = true)
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

include wellFormed runtime covers sourceArguments in
/-- Original Source argument preservation supplies both raw parameter types
and deep typing of the actual argument heap. Native vectors are independent. -/
private theorem arguments_admitted {start : Dynamic.Heap}
    (startLocals : Dynamic.EnvironmentAgrees start function.context.locals function.captured)
    (startTyped : Dynamic.HeapWellTyped function.context start)
    {size : Nat} {arguments : List Dynamic.Value} {middle : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured start ids arguments middle) :
    Dynamic.ValuesHaveTypes function.context middle arguments support.body.types ∧
      Dynamic.HeapWellTyped function.context middle := by
  have expressionPreserves : Dynamic.ExpressionExecutionPreserves (Program.ofChecked compiled.sourceProgram)
      function.context function.evidence function.source function.captured := by
    intro before after id value type covers locals heapTyped typed execution
    exact wellFormed.wholeLanguagePreservation.expression function.context function.evidence function.source
      function.captured before after id value type runtime covers locals heapTyped typed execution
  have reached := Dynamic.ExpressionsEvaluate.preserves expressionPreserves covers startLocals startTyped sourceArguments trace.sound
  exact ⟨reached.1, reached.2.1⟩

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) captured code
    (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet) heap store
    owner.key.frameLocation)

/-- The caller packet, transported to the formed state that holds the copies
of the callee's captured cells. -/
def formedState : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
    ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩ :=
  (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named).extend ⟨initial, packet⟩
    formed.maps formed.worlds formed.frame formed.copy.metadata_extends

/-- Transport relates the caller packet to its formed state. -/
theorem formedState_related : Relates initial (formedState captured code support owner initial packet profile formed).val :=
  (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named).related ⟨initial, packet⟩
    formed.maps formed.worlds formed.frame formed.copy.metadata_extends

include admitted in
/-- Admission holds at the formed state: copies keep the heap typing, and rows
stay stable across the administrative extension. -/
theorem formedState_admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context (formedState captured code support owner initial packet profile formed) :=
  ⟨admitted.heap.copy formed.copy,
    CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative initial (formedState captured code support owner initial packet profile formed).val
      admitted.rows formed.frame⟩

include heaps admitted selection sourceArguments in
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
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) (formedState captured code support owner initial packet profile formed) budget := by
  intro size outcome after trace bounded
  have closureTyped := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formed.represents heaps.runtime_hasTypes)
  exact CallableIndexedOwnedAdmittedSequenceProducer.preserves
    (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (formedState captured code support owner initial packet profile formed) (formedState_admitted captured code support owner initial packet profile admitted formed) selection.children support.unique sourceArguments
    (captured.represented.extend formed.maps formed.worlds) formed.heaps (locals.mono formed.copy.metadata_extends)
    (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix captured.agrees _) .unit)
    (.cons .unit (.cons closureTyped (captured.typed.weaken formed.worlds))) budget children trace bounded

include heaps admitted selection sourceArguments in
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
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) (formedState captured code support owner initial packet profile formed) budget := by
  intro size result finalStore trace bounded
  have closureTyped := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formed.represents heaps.runtime_hasTypes)
  exact CallableIndexedOwnedAdmittedSequenceProducer.reflects
    (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (formedState captured code support owner initial packet profile formed) (formedState_admitted captured code support owner initial packet profile admitted formed) selection.children support.unique sourceArguments
    (captured.represented.extend formed.maps formed.worlds) formed.heaps (locals.mono formed.copy.metadata_extends)
    (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix captured.agrees _) .unit)
    (.cons .unit (.cons closureTyped (captured.typed.weaken formed.worlds))) budget children trace bounded

include syntaxTree wellFormed runtime covers locals admitted sourceArguments selection in
/-- The actual ordered argument post supplies raw Source admission and its
current owned row to the selected parameter/body prefix. -/
theorem arguments_preserves
    (budget : Nat)
    (sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) (formedState captured code support owner initial packet profile formed) budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget)
    {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      function.context function.evidence function.source function.captured formed.finalHeap ids arguments middle)
    (argumentsWithin : argumentsSize ≤ budget)
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize
      function.context function.evidence function.evidence middle (.closure formed.closure) arguments outcome after)
    (callWithin : callSize ≤ budget) :
    ∃ payloads middleStore result finalStore finalMap finalWorld,
      Evaluates (.unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
        formed.finalStore (((SourceCoreCalls.packArguments compiler.codes).expression.rename captured.embedding).weakenAt 0 |>.weakenAt 0)
        (.inRight .word (DataPatternValues.packValues payloads)) middleStore ∧
      Evaluates (DataPatternValues.packValues payloads :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native :: formed.closureActual)
        middleStore (code.body.rename formed.embedding.lift.lift) result finalStore ∧
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
    let future := formed.captures.extend argumentMaps argumentWorlds
    let history := formed.closureHistory
    have raw := arguments_admitted captured code support sourceArguments wellFormed runtime covers
      (locals.mono formed.copy.metadata_extends) (admitted.heap.copy formed.copy) argumentsTrace
    have stable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative initial argumentState.val admitted.rows (formed.frame.trans argumentFrame)
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : future.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code support]
      exact (packet.observed.of_slots formed.slots).reference
    have capturesValid : FunctionValues.SourceCapturesValid middle (.closure formed.closure) :=
      (show FunctionValues.SourceCapturesValid formed.finalHeap (.closure formed.closure) from
        formed.copy.agrees locals).extend argumentMetadata
    let recaptured : Support formed.closureCode registry faults :=
      (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support formed.captured)
    have recapturedSyntax : GenericImperativeMatch.Syntax function.source (recaptured.expressionSyntax function.source)
        recaptured.body.context (.statements true function.body) function.resultType := syntaxTree
    have meaning := CallableIndexedOwnedExtendedJointReadyContinuations.method_lambda_source_continuation
      (nativeArguments := payloads) (function := formed.closure)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed
      future formed.closureCode history recaptured
      (CallableIndexedOwnedMethodLambdaValues.recaptureOrigin
        (CallableIndexedOwnedMethodLambdaFormationReceipts.source_origin captured code support owner initial packet) formed.captured)
      owner (packet.observed.of_slots formed.slots)
      (CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code support owner initial packet)
      argumentState.val selection.escaped raw.2 raw.1 stable recapturedSyntax budget below
    obtain ⟨result, finalStore, finalMap, finalWorld, bodyEvaluation, resultRep, finalHeaps,
        maps, worlds, frame, metadata, finalState, related⟩ :=
      CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at (function := formed.closure)
        future formed.closureCode history recaptured.body.toContext
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
        representedArguments owner argumentState.val middleHeaps capturesValid reference currentCarried
        (CallableIndexedLambdaTemplatePermission.lambda_allowed formed.closureCode history)
        (recaptured.body_origin selection.escaped)
        budget meaning called callWithin
    obtain ⟨returned, _samePool, relatedCaller⟩ :=
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named).restore
        ⟨initial, packet⟩ finalState (formed.maps.trans (argumentMaps.trans maps))
        (formed.worlds.trans (argumentWorlds.trans worlds)) (formed.frame.trans (argumentFrame.trans frame))
        (formed.copy.metadata_extends.trans (argumentMetadata.trans metadata))
        ((formedState_related captured code support owner initial packet profile formed).trans (argumentRelated.trans related))
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentEvaluation
    exact ⟨_, middleStore, result, finalStore, finalMap, finalWorld, argumentEvaluation, bodyEvaluation,
      resultRep, finalHeaps, formed.maps.trans (argumentMaps.trans maps), formed.worlds.trans (argumentWorlds.trans worlds),
      formed.frame.trans (argumentFrame.trans frame), formed.copy.metadata_extends.trans (argumentMetadata.trans metadata),
      returned, relatedCaller⟩

include syntaxTree wellFormed runtime covers locals admitted sourceArguments selection in
/-- The native argument completion reconstructs its own Source grade before
selecting the exact actual body prefix and the same restored caller pool. -/
theorem arguments_reflects (budget : Nat)
    (sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) (formedState captured code support owner initial packet profile formed) budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget)
    {argumentsSize bodySize : Nat} {argumentInput : Ty} {argument result : Value} {middleStore finalStore : Store}
    (argumentsTrace : EvaluationSize argumentsSize (.unit :: value code formed.embedding
      (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      formed.finalStore (((SourceCoreCalls.packArguments compiler.codes).expression.rename captured.embedding).weakenAt 0 |>.weakenAt 0)
      (.inRight argumentInput argument) middleStore)
    (argumentsWithin : argumentsSize < budget)
    (bodyTrace : EvaluationSize bodySize (argument :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
      (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native :: formed.closureActual)
      middleStore (code.body.rename formed.embedding.lift.lift) result finalStore)
    (bodyWithin : bodySize ≤ budget) :
    ∃ sourceArgumentsSize sourceCallSize arguments middle outcome after finalMap finalWorld,
      SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceArgumentsSize
        function.context function.evidence function.source function.captured formed.finalHeap ids arguments middle ∧
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceCallSize
        function.context function.evidence function.evidence middle (.closure formed.closure) arguments outcome after ∧
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
      let future := formed.captures.extend argumentMaps argumentWorlds
      let history := formed.closureHistory
      have raw := arguments_admitted captured code support sourceArguments wellFormed runtime covers
        (locals.mono formed.copy.metadata_extends) (admitted.heap.copy formed.copy) sourceArgumentsTrace
      have stable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative initial argumentState.val admitted.rows (formed.frame.trans argumentFrame)
      obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
      have reference : future.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code support]
        exact (packet.observed.of_slots formed.slots).reference
      have capturesValid : FunctionValues.SourceCapturesValid middle (.closure formed.closure) :=
        (show FunctionValues.SourceCapturesValid formed.finalHeap (.closure formed.closure) from
          formed.copy.agrees locals).extend argumentMetadata
      let recaptured : Support formed.closureCode registry faults :=
        (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support formed.captured)
      have recapturedSyntax : GenericImperativeMatch.Syntax function.source (recaptured.expressionSyntax function.source)
          recaptured.body.context (.statements true function.body) function.resultType := syntaxTree
      have meaning := CallableIndexedOwnedExtendedJointReadyContinuations.method_lambda_native_continuation
        (function := formed.closure) (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed
        future formed.closureCode history recaptured
        (CallableIndexedOwnedMethodLambdaValues.recaptureOrigin
          (CallableIndexedOwnedMethodLambdaFormationReceipts.source_origin captured code support owner initial packet) formed.captured)
        owner (packet.observed.of_slots formed.slots)
        (CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code support owner initial packet)
        argumentState.val selection.escaped raw.2 raw.1 stable recapturedSyntax budget below
      obtain ⟨sourceCallSize, outcome, after, finalMap, finalWorld, called, resultRep, finalHeaps,
          maps, worlds, frame, metadata, finalState, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at (function := formed.closure)
          future formed.closureCode history recaptured.body.toContext
          (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
          representedArguments owner argumentState.val middleHeaps capturesValid reference currentCarried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed formed.closureCode history)
          (recaptured.body_origin selection.escaped)
          budget meaning bodyTrace bodyWithin
      obtain ⟨returned, _samePool, relatedCaller⟩ :=
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named).restore
          ⟨initial, packet⟩ finalState (formed.maps.trans (argumentMaps.trans maps))
          (formed.worlds.trans (argumentWorlds.trans worlds)) (formed.frame.trans (argumentFrame.trans frame))
          (formed.copy.metadata_extends.trans (argumentMetadata.trans metadata))
          ((formedState_related captured code support owner initial packet profile formed).trans (argumentRelated.trans related))
      exact ⟨sourceArgumentsSize, sourceCallSize, sources, middle, outcome, after, finalMap, finalWorld,
        sourceArgumentsTrace, called, resultRep, finalHeaps, formed.maps.trans (argumentMaps.trans maps),
        formed.worlds.trans (argumentWorlds.trans worlds), formed.frame.trans (argumentFrame.trans frame),
        formed.copy.metadata_extends.trans (argumentMetadata.trans metadata), returned, relatedCaller⟩

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

theorem lambda_function (environment : Dynamic.Environment) : (lambda captured code coercions).function
    function.context function.evidence environment = { function with captured := environment } := rfl

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

include selection sameCallee copied ordinary coercions parent sourceCount sourceArguments syntaxTree
  wellFormed runtime covers locals heaps admitted parentTyped in
/-- The original method-lambda formation closes the callee internally, copying
its captured cells. Ordered admitted children and the strict dependent body IH
close the whole call at the formed state. -/
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
  obtain ⟨calleeSize, argumentsSize, callSize, calleeCaptured, calleeHeap, calleeTrace, calleeCopy, suffix,
      _calleeSmall, argumentsSmall, callWithin⟩ :=
    CallableIndexedOwnedSelectedIndirectHeads.suffix_of_source compiler.found compiler.originalForm parent.coercions
      compiler.argumentCoercions parent.arity (lambda captured code coercions) support.unique wellFormed runtime covers locals
      admitted.heap sourceArguments sourceCount trace
  obtain ⟨formed, _source, nativeFormed, _represented, _determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation captured code support owner initial packet profile
      heaps copied ordinary coercions
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional calleeCopy formed.copy
  rw [lambda_function captured code coercions] at calleeTrace suffix
  have calleeEvaluation : Evaluates actual store (compiler.calleeCode.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual)) formed.finalStore := by
    rw [sameCallee]; exact nativeFormed
  have sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) (formedState captured code support owner initial packet profile formed) budget := by
    intro size outcome after childTrace childBound
    exact sequence_preserves captured code support owner initial packet profile compiler prepared selection
      sourceArguments heaps admitted formed budget children locals childTrace childBound
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
        formed.maps.trans maps, formed.worlds.trans worlds, formed.frame.trans frame,
        formed.copy.metadata_extends.trans metadata, reached, (formedState_related captured code support owner initial packet profile formed).trans related,
        after_expression_sized (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals
          parentTyped trace (formed.frame.trans frame)⟩
  | called argumentsTrace called =>
    obtain ⟨payloads, middleStore, result, finalStore, finalMap, finalWorld, argumentEvaluation, bodyEvaluation,
        resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      arguments_preserves captured code support owner initial packet profile compiler prepared selection sourceArguments
        syntaxTree wellFormed runtime covers locals admitted formed budget sequence below argumentsTrace
        (Nat.le_trans (Nat.le_of_lt argumentsSmall) within) called (Nat.le_trans callWithin within)
    have whole := CallableContract.call_success prepared.site.gates native.diagnostics.unknown calleeEvaluation
      selection.stageAccepted argumentEvaluation selection.arityAccepted bodyEvaluation
    rw [← emitted] at whole
    exact ⟨result, finalStore, finalMap, finalWorld, whole,
      parent_result captured code profile compiler prepared selection resultRep, finalHeaps,
      maps, worlds, frame, metadata, reached, related,
      after_expression_sized (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

include selection sameCallee copied ordinary coercions parent sourceCount sourceArguments syntaxTree
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
  obtain ⟨formed, sourceCallee, nativeFormed, _represented, _determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation captured code support owner initial packet profile
      heaps copied ordinary coercions
  obtain ⟨calleeSize, calleeTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size sourceCallee
  have calleeEvaluation : Evaluates actual store (compiler.calleeCode.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual)) formed.finalStore := by
    rw [sameCallee]; exact nativeFormed
  have sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)) (formedState captured code support owner initial packet profile formed) budget := by
    intro size result finalStore childTrace childBound
    exact sequence_reflects captured code support owner initial packet profile compiler prepared selection
      sourceArguments heaps admitted formed budget children locals childTrace childBound
  have emitted := prepared.lowered_rename compiler captured.embedding
  rw [emitted, selection.nativeResult] at trace
  cases completed code (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet) formed.embedding formed.closureActual
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
          wellFormed runtime covers (locals.mono formed.copy.metadata_extends) (admitted.heap.copy formed.copy)
          sourceArguments sourceCount calleeTrace
          (CallableIndexedOwnedIndirectExpressionHeads.SourceSuffix.argumentFault failed)
        exact ⟨sourceSize, _, after, finalMap, finalWorld, sourceTrace,
          parent_result captured code profile compiler prepared selection (.fault matched), finalHeaps,
          formed.maps.trans maps, formed.worlds.trans worlds, formed.frame.trans frame,
          formed.copy.metadata_extends.trans metadata, reached, (formedState_related captured code support owner initial packet profile formed).trans related,
          after_expression_sized (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals
            parentTyped sourceTrace (formed.frame.trans frame)⟩
  | applied argumentsTrace bodyTrace argumentsStrict bodyStrict =>
    obtain ⟨sourceArgumentsSize, sourceCallSize, arguments, middle, outcome, after, finalMap, finalWorld,
        sourceArgumentsTrace, called, resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      arguments_reflects captured code support owner initial packet profile compiler prepared selection sourceArguments
        syntaxTree wellFormed runtime covers locals admitted formed budget sequence below argumentsTrace argumentsStrict
        bodyTrace (Nat.le_of_lt bodyStrict)
    obtain ⟨sourceSize, sourceTrace⟩ := CallableIndexedOwnedIndirectSourceAdapters.SourceSuffix.to_expression
      compiler.found compiler.originalForm parent.requirements parent.coercions compiler.argumentCoercions parent.arity
      wellFormed runtime covers (locals.mono formed.copy.metadata_extends) (admitted.heap.copy formed.copy)
      sourceArguments sourceCount calleeTrace
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
  copied : code.policy.snapshotLambda code.id = true
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
    (copied := issued.copied)
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
    (copied := issued.copied)
    (sourceArguments := issued.sourceArguments) (sourceCount := issued.sourceCount) (syntaxTree := issued.syntaxTree)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals) (heaps := heaps)
    (admitted := admitted) (parentTyped := issued.parentTyped) budget children below trace within

end Parent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSelectedCall
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionHeads
/-! Actual method lambda sites produce finite formation and call certificates.
The static site retains its original empty capture environment and full body
receipt. At each genuine input the principal packet determines the used native
prefix, and the original Code and body are recaptured at that actual Source
environment. No semantic callee factory is stored in a certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context)

/-- The complete accepted static site and body belong to this actual method
Source occurrence. Only the capture environment is filled at execution input. -/
structure Formation (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
    context principal.dictionary [] scope (CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal)
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
    expressionSyntax certificates site.code (Program.ofChecked compiled.sourceProgram) registry faults
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  sourceType : site.code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure principal.named parameters result statements context principal.dictionary [])
  ordinary : Dynamic.OrdinaryRequirementLayout site.code.sourceNode.requirements site.code.sourceNode.coercions []
  coercions : site.code.sourceNode.coercions = []
  syntaxTree : GenericImperativeMatch.Syntax
    (CallableIndexedNamedGeneration.source principal.named)
    (expressionSyntax (CallableIndexedNamedGeneration.source principal.named)) body.context
    (.statements true statements) result

variable {principal context}

/-- Actual capture locations change no accepted compiler or Source field. -/
def Formation.function {scope id lowered}
    (head : Formation (registry := registry) (faults := faults) principal context scope id lowered)
    (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure principal.named head.parameters head.result head.statements
    context principal.dictionary environment

def Formation.code {scope id lowered}
    (head : Formation (registry := registry) (faults := faults) principal context scope id lowered)
    (environment : Dynamic.Environment) : Code compiled.indexed (head.function environment) scope
      (CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal) :=
  RecursiveNamedLambdaFormationHeads.recaptureCode (values := .initial compiled.compatible.checked)
    (indexed := compiled.indexed) head.site.code environment

/-- Original static body recapture retains its complete Source frame,
dictionary, Tree, certificates and accepted emitted body. -/
def Formation.support {scope id lowered}
    (head : Formation (registry := registry) (faults := faults) principal context scope id lowered)
    (environment : Dynamic.Environment) : Support (head.code environment) registry faults where
  method := method
  principal := principal
  expressionSyntax := head.expressionSyntax
  certificates := head.certificates
  source := rfl
  compilation := head.site.compilation
  active := head.site.active
  body := RecursiveNamedLambdaFormationHeads.recaptureBodyWith (values := .initial compiled.compatible.checked)
    (indexed := compiled.indexed) head.site.code head.body environment

variable (principal context)

/-- The ordered original compiler argument receipt and genuine Source row
remain independent. Both guards select this same accepted literal Code. -/
structure Call (certificate : GenericExpressionMeaning.Certificate)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  callee : ExpressionId
  calleeCode : SourceCoreBasic.LoweredExpr
  formation : Formation (registry := registry) (faults := faults) principal context scope callee calleeCode
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  fuel : Nat
  compilation : SourceCoreFunctions.Context
  ids : List ExpressionId
  metadata : IndirectCallResolution
  reasonAt : ExpressionId → Word
  compiler : CallableIndirectCallCertificates.Receipt policy lowerBody fuel compilation
    (CallableIndexedNamedGeneration.source principal.named) scope id formation.site.code.id ids metadata reasonAt lowered
  native : SourceCoreGeneralFunctions.CallableContext
  prepared : Prepared compiler native
  parent : SourceParent compiler
  selection : CallableIndexedOwnedSelectedIndirectHeads.Selection (compiled := compiled)
    (faults := faults) (certificate := certificate) compiler prepared formation.site.code
  sameCallee : compiler.calleeCode = formation.site.code.lowered
  sourceArguments : ExpressionsHaveTypes (CallableIndexedNamedGeneration.source principal.named)
    context ids formation.body.types
  sourceCount : formation.body.types.length = metadata.argumentCount

/-- This finite sum is a genuine expression Certificate transformer. Neither
branch classifies arbitrary values or contains an evaluation law. -/
inductive Head (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (context : SourceSemantics.Context) (certificate : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | formation {scope id lowered}
      (head : Formation (registry := registry) (faults := faults) principal context scope id lowered) :
      Head principal context certificate scope id lowered
  | call {scope id lowered}
      (head : Call (registry := registry) (faults := faults) principal context certificate scope id lowered) :
      Head principal context certificate scope id lowered


def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) :=
  CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner principal.named

def model (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  {certificate : GenericExpressionMeaning.Certificate}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include complete slots wellFormed runtime covers in
/-- Each authentic finite branch constructs captures, Code and Support at
its actual input. Strict arguments and the joint body's own strict IH remain. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (registry := registry) (faults := faults) principal context certificate) faults size := by
  intro scope id lowered head node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  let captured := CallableIndexedOwnedMethodPrincipalCaptures.captures principal owner initial.val initial.property
    complete environments agrees nativeTyped
  have packet := CallableIndexedOwnedMethodPrincipalCaptures.captured_packet principal owner initial.val initial.property
    complete environments agrees nativeTyped slots
  let capturedInitial : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named).State
      ⟨scope, mapping, world, before, store, captured.canonical⟩ := ⟨initial.val, packet⟩
  have capturedAdmission : Admission (bridge (headers := headers) principal owner) context capturedInitial :=
    ⟨admitted.heap, admitted.rows⟩
  cases head with
  | formation head =>
    let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
    let support : Support code registry faults := head.support environment
    have sourceFound : (CallableIndexedNamedGeneration.source principal.named).lookupExpression? id = some code.sourceNode := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode, CallableIndexedLambdaGeneration.closure, head.identifier] using
        head.site.code.sourceFound
    have same := Option.some.inj (found.symm.trans sourceFound)
    subst node
    have nativeTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
        (head.function environment).context (head.function environment).evidence (head.function environment).source
        (head.function environment).captured before code.id outcome after := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using trace
    have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context code.id code.sourceNode.type := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using typed
    obtain ⟨result, finalStore, evaluated, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedMethodLambdaFormation.preserves_at
        (function := head.function environment) (scope := scope) (actual := actual) captured code support owner initial.val packet profile
        wellFormed runtime covers locals actualTyped head.sourceType head.site.snapshots head.ordinary head.coercions heaps
        capturedAdmission nativeTrace
    have evaluated : Evaluates actual store (lowered.expression.rename ξ) result finalStore := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode,
        head.emitted, captured, CallableIndexedOwnedMethodPrincipalCaptures.captures] using evaluated
    have represented : GenericExpressionMeaning.ResultRepresents
        (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
        finalMap finalWorld code.sourceNode.type lowered.type faults outcome result := by
      simpa only [model, code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode, head.emitted] using represented
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩
  | call head =>
    let code : Code compiled.indexed (head.formation.function environment) scope captured.administrative := head.formation.code environment
    let support : Support code registry faults := head.formation.support environment
    have same := Option.some.inj (found.symm.trans head.compiler.found)
    subst node
    let issued : CallableIndexedOwnedMethodLambdaSelectedCall.Receipt
        (function := head.formation.function environment) captured code support head.compiler certificate := {
      native := head.native, prepared := head.prepared, parent := head.parent,
      selection := ⟨head.selection.children, head.selection.nativeTypes, head.selection.escaped,
        head.selection.rawResult, head.selection.nativeResult, head.selection.stageAccepted, head.selection.arityAccepted⟩,
      sameCallee := head.sameCallee, ordinary := head.formation.ordinary, coercions := head.formation.coercions,
      copied := head.formation.site.snapshots, sourceArguments := head.sourceArguments, sourceCount := head.sourceCount,
      syntaxTree := head.formation.syntaxTree, parentTyped := typed }
    obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedMethodLambdaSelectedCall.preserves_at_receipt
        (function := head.formation.function environment) (scope := scope) (actual := actual)
        (captured := captured) (code := code) (support := support) (owner := owner) (initial := initial.val) (packet := packet)
        (profile := profile) (compiler := head.compiler) (wellFormed := wellFormed) (runtime := runtime)
        (covers := covers) (locals := locals) (heaps := heaps)
        (admitted := capturedAdmission) issued budget children below trace within
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩

include complete slots wellFormed runtime covers in
/-- Native child bounds are measured independently. The same static branch
producer reconstructs the authentic Source trace and restores its exact pool. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (registry := registry) (faults := faults) principal context certificate) faults size := by
  intro scope id lowered head node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  let captured := CallableIndexedOwnedMethodPrincipalCaptures.captures principal owner initial.val initial.property
    complete environments agrees nativeTyped
  have packet := CallableIndexedOwnedMethodPrincipalCaptures.captured_packet principal owner initial.val initial.property
    complete environments agrees nativeTyped slots
  let capturedInitial : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named).State
      ⟨scope, mapping, world, before, store, captured.canonical⟩ := ⟨initial.val, packet⟩
  have capturedAdmission : Admission (bridge (headers := headers) principal owner) context capturedInitial :=
    ⟨admitted.heap, admitted.rows⟩
  cases head with
  | formation head =>
    let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
    let support : Support code registry faults := head.support environment
    have sourceFound : (CallableIndexedNamedGeneration.source principal.named).lookupExpression? id = some code.sourceNode := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode,
        CallableIndexedLambdaGeneration.closure, head.identifier] using head.site.code.sourceFound
    have same := Option.some.inj (found.symm.trans sourceFound)
    subst node
    have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context code.id code.sourceNode.type := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using typed
    have actualCompleted : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) value finalStore := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode,
        head.emitted, captured, CallableIndexedOwnedMethodPrincipalCaptures.captures] using completed
    obtain ⟨sourceSize, outcome, after, trace, _native, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame,
        metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedMethodLambdaFormation.reflects_at
        (function := head.function environment) (scope := scope) (actual := actual) captured code support owner initial.val packet profile
        wellFormed runtime covers locals actualTyped head.sourceType head.site.snapshots head.ordinary head.coercions heaps
        capturedAdmission actualCompleted
    have sourceTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) environment before id outcome after := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using trace
    have represented : GenericExpressionMeaning.ResultRepresents
        (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
        finalMap finalWorld code.sourceNode.type lowered.type faults outcome value := by
      simpa only [model, code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode, head.emitted] using represented
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed sourceTrace frame⟩
  | call head =>
    let code : Code compiled.indexed (head.formation.function environment) scope captured.administrative := head.formation.code environment
    let support : Support code registry faults := head.formation.support environment
    have same := Option.some.inj (found.symm.trans head.compiler.found)
    subst node
    let issued : CallableIndexedOwnedMethodLambdaSelectedCall.Receipt
        (function := head.formation.function environment) captured code support head.compiler certificate := {
      native := head.native, prepared := head.prepared, parent := head.parent,
      selection := ⟨head.selection.children, head.selection.nativeTypes, head.selection.escaped,
        head.selection.rawResult, head.selection.nativeResult, head.selection.stageAccepted, head.selection.arityAccepted⟩,
      sameCallee := head.sameCallee, ordinary := head.formation.ordinary, coercions := head.formation.coercions,
      copied := head.formation.site.snapshots, sourceArguments := head.sourceArguments, sourceCount := head.sourceCount,
      syntaxTree := head.formation.syntaxTree, parentTyped := typed }
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedMethodLambdaSelectedCall.reflects_at_receipt
        (function := head.formation.function environment) (scope := scope) (actual := actual)
        (captured := captured) (code := code) (support := support) (owner := owner) (initial := initial.val) (packet := packet)
        (profile := profile) (compiler := head.compiler) (wellFormed := wellFormed) (runtime := runtime)
        (covers := covers) (locals := locals) (heaps := heaps)
        (admitted := capturedAdmission) issued budget children below completed within
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSelectedCallWithFunctions
/-! Accepted method lambda calls retain a single caller function model across
formation, ordered arguments, body execution and the restored full caller pool.
Forward inclusion applies only to the authentic formation value. The original
compiler Receipt, finite native completion and static Source callee are reused. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSelectedCallWithFunctions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)
open CallableIndexedOwnedMethodLambdaSelectedCall (Receipt Completion completed lambda lambda_function)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

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
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile).Includes functions)
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
  (copied : code.policy.snapshotLambda code.id = true)
  (sourceArguments : ExpressionsHaveTypes function.source function.context ids support.body.types)
  (sourceCount : support.body.types.length = metadata.argumentCount)
  (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include wellFormed runtime covers sourceArguments in
/-- Original Source argument preservation supplies both raw parameter types
and deep typing of the actual argument heap. Native vectors are independent. -/
private theorem arguments_admitted {start : Dynamic.Heap}
    (startLocals : Dynamic.EnvironmentAgrees start function.context.locals function.captured)
    (startTyped : Dynamic.HeapWellTyped function.context start)
    {size : Nat} {arguments : List Dynamic.Value} {middle : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured start ids arguments middle) :
    Dynamic.ValuesHaveTypes function.context middle arguments support.body.types ∧
      Dynamic.HeapWellTyped function.context middle := by
  have expressionPreserves : Dynamic.ExpressionExecutionPreserves (Program.ofChecked compiled.sourceProgram)
      function.context function.evidence function.source function.captured := by
    intro before after id value type covers locals heapTyped typed execution
    exact wellFormed.wholeLanguagePreservation.expression function.context function.evidence function.source
      function.captured before after id value type runtime covers locals heapTyped typed execution
  have reached := Dynamic.ExpressionsEvaluate.preserves expressionPreserves covers startLocals startTyped sourceArguments trace.sound
  exact ⟨reached.1, reached.2.1⟩

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
    functions) captured code
    (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet) heap store
    owner.key.frameLocation)

/-- The caller packet, transported to the formed state that holds the copies
of the callee's captured cells. -/
def formedState : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
    ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩ :=
  (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named).extend ⟨initial, packet⟩
    formed.maps formed.worlds formed.frame formed.copy.metadata_extends

/-- Transport relates the caller packet to its formed state. -/
theorem formedState_related : Relates initial (formedState captured code support owner initial packet functions formed).val :=
  (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named).related ⟨initial, packet⟩
    formed.maps formed.worlds formed.frame formed.copy.metadata_extends

include admitted in
/-- Admission holds at the formed state: copies keep the heap typing, and rows
stay stable across the administrative extension. -/
theorem formedState_admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context (formedState captured code support owner initial packet functions formed) :=
  ⟨admitted.heap.copy formed.copy,
    CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative initial (formedState captured code support owner initial packet functions formed).val
      admitted.rows formed.frame⟩

include profile heaps admitted selection sourceArguments in
/-- The genuine formation value is the real guard prefix of the unchanged
admitted sequence fold. Its Source typing row stays independent of Tree types. -/
theorem sequence_preserves (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      function.context function.evidence function.source certificate faults size)
    (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured) :
    ProtectedStateExpressionSequenceProducer.Preserves
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions) (formedState captured code support owner initial packet functions formed) budget := by
  intro size outcome after trace bounded
  have closureTyped := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formed.represents heaps.runtime_hasTypes)
  exact CallableIndexedOwnedAdmittedSequenceProducer.preserves
    (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (formedState captured code support owner initial packet functions formed) (formedState_admitted captured code support owner initial packet functions admitted formed) selection.children support.unique sourceArguments
    (captured.represented.extend formed.maps formed.worlds) formed.heaps (locals.mono formed.copy.metadata_extends)
    (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix captured.agrees _) .unit)
    (.cons .unit (.cons closureTyped (captured.typed.weaken formed.worlds))) budget children trace bounded

include profile heaps admitted selection sourceArguments in
/-- Native arguments use the same actual guarded input and independent Source
row, preserving the original strict sequence grade. -/
theorem sequence_reflects (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      function.context function.evidence function.source certificate faults size)
    (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured) :
    ProtectedStateExpressionSequenceProducer.Reflects
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions) (formedState captured code support owner initial packet functions formed) budget := by
  intro size result finalStore trace bounded
  have closureTyped := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formed.represents heaps.runtime_hasTypes)
  exact CallableIndexedOwnedAdmittedSequenceProducer.reflects
    (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (formedState captured code support owner initial packet functions formed) (formedState_admitted captured code support owner initial packet functions admitted formed) selection.children support.unique sourceArguments
    (captured.represented.extend formed.maps formed.worlds) formed.heaps (locals.mono formed.copy.metadata_extends)
    (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix captured.agrees _) .unit)
    (.cons .unit (.cons closureTyped (captured.typed.weaken formed.worlds))) budget children trace bounded

include syntaxTree wellFormed runtime covers locals admitted sourceArguments selection in
/-- The actual ordered argument post supplies raw Source admission and its
current owned row to the selected parameter/body prefix. -/
theorem arguments_preserves
    (budget : Nat)
    (sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions) (formedState captured code support owner initial packet functions formed) budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget)
    {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      function.context function.evidence function.source function.captured formed.finalHeap ids arguments middle)
    (argumentsWithin : argumentsSize ≤ budget)
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize
      function.context function.evidence function.evidence middle (.closure formed.closure) arguments outcome after)
    (callWithin : callSize ≤ budget) :
    ∃ payloads middleStore result finalStore finalMap finalWorld,
      Evaluates (.unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
        formed.finalStore (((SourceCoreCalls.packArguments compiler.codes).expression.rename captured.embedding).weakenAt 0 |>.weakenAt 0)
        (.inRight .word (DataPatternValues.packValues payloads)) middleStore ∧
      Evaluates (DataPatternValues.packValues payloads :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native :: formed.closureActual)
        middleStore (code.body.rename formed.embedding.lift.lift) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        functions finalMap finalWorld after finalStore ∧
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
    let future := formed.captures.extend argumentMaps argumentWorlds
    let history := formed.closureHistory
    have raw := arguments_admitted captured code support sourceArguments wellFormed runtime covers
      (locals.mono formed.copy.metadata_extends) (admitted.heap.copy formed.copy) argumentsTrace
    have stable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative initial argumentState.val admitted.rows (formed.frame.trans argumentFrame)
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : future.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code support]
      exact (packet.observed.of_slots formed.slots).reference
    have capturesValid : FunctionValues.SourceCapturesValid middle (.closure formed.closure) :=
      (show FunctionValues.SourceCapturesValid formed.finalHeap (.closure formed.closure) from
        formed.copy.agrees locals).extend argumentMetadata
    let recaptured : Support formed.closureCode registry faults := (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support formed.captured)
    have recapturedSyntax : GenericImperativeMatch.Syntax function.source (recaptured.expressionSyntax function.source)
        recaptured.body.context (.statements true function.body) function.resultType := syntaxTree
    have meaning := CallableIndexedOwnedExtendedJointReadyContinuations.method_lambda_source_continuation
      (nativeArguments := payloads) (function := formed.closure) functions wellFormed
      future formed.closureCode history recaptured
      (CallableIndexedOwnedMethodLambdaValues.recaptureOrigin
        (CallableIndexedOwnedMethodLambdaFormationReceipts.source_origin captured code support owner initial packet) formed.captured)
      owner (packet.observed.of_slots formed.slots)
      (CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code support owner initial packet)
      argumentState.val selection.escaped raw.2 raw.1 stable recapturedSyntax budget below
    obtain ⟨result, finalStore, finalMap, finalWorld, bodyEvaluation, resultRep, finalHeaps,
        maps, worlds, frame, metadata, finalState, related⟩ :=
      CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at (function := formed.closure)
        future formed.closureCode history recaptured.body.toContext functions
        representedArguments owner argumentState.val middleHeaps capturesValid reference currentCarried
        (CallableIndexedLambdaTemplatePermission.lambda_allowed formed.closureCode history)
        (recaptured.body_origin selection.escaped)
        budget meaning called callWithin
    obtain ⟨returned, _samePool, relatedCaller⟩ :=
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named).restore
        ⟨initial, packet⟩ finalState (formed.maps.trans (argumentMaps.trans maps))
        (formed.worlds.trans (argumentWorlds.trans worlds)) (formed.frame.trans (argumentFrame.trans frame))
        (formed.copy.metadata_extends.trans (argumentMetadata.trans metadata))
        ((formedState_related captured code support owner initial packet functions formed).trans (argumentRelated.trans related))
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentEvaluation
    exact ⟨_, middleStore, result, finalStore, finalMap, finalWorld, argumentEvaluation, bodyEvaluation,
      resultRep, finalHeaps, formed.maps.trans (argumentMaps.trans maps), formed.worlds.trans (argumentWorlds.trans worlds),
      formed.frame.trans (argumentFrame.trans frame), formed.copy.metadata_extends.trans (argumentMetadata.trans metadata),
      returned, relatedCaller⟩

include syntaxTree wellFormed runtime covers locals admitted sourceArguments selection in
/-- The native argument completion reconstructs its own Source grade before
selecting the exact actual body prefix and the same restored caller pool. -/
theorem arguments_reflects (budget : Nat)
    (sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions) (formedState captured code support owner initial packet functions formed) budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget)
    {argumentsSize bodySize : Nat} {argumentInput : Ty} {argument result : Value} {middleStore finalStore : Store}
    (argumentsTrace : EvaluationSize argumentsSize (.unit :: value code formed.embedding
      (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      formed.finalStore (((SourceCoreCalls.packArguments compiler.codes).expression.rename captured.embedding).weakenAt 0 |>.weakenAt 0)
      (.inRight argumentInput argument) middleStore)
    (argumentsWithin : argumentsSize < budget)
    (bodyTrace : EvaluationSize bodySize (argument :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
      (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native :: formed.closureActual)
      middleStore (code.body.rename formed.embedding.lift.lift) result finalStore)
    (bodyWithin : bodySize ≤ budget) :
    ∃ sourceArgumentsSize sourceCallSize arguments middle outcome after finalMap finalWorld,
      SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceArgumentsSize
        function.context function.evidence function.source function.captured formed.finalHeap ids arguments middle ∧
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceCallSize
        function.context function.evidence function.evidence middle (.closure formed.closure) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        functions finalMap finalWorld after finalStore ∧
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
      let future := formed.captures.extend argumentMaps argumentWorlds
      let history := formed.closureHistory
      have raw := arguments_admitted captured code support sourceArguments wellFormed runtime covers
        (locals.mono formed.copy.metadata_extends) (admitted.heap.copy formed.copy) sourceArgumentsTrace
      have stable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative initial argumentState.val admitted.rows (formed.frame.trans argumentFrame)
      obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
      have reference : future.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code support]
        exact (packet.observed.of_slots formed.slots).reference
      have capturesValid : FunctionValues.SourceCapturesValid middle (.closure formed.closure) :=
        (show FunctionValues.SourceCapturesValid formed.finalHeap (.closure formed.closure) from
          formed.copy.agrees locals).extend argumentMetadata
      let recaptured : Support formed.closureCode registry faults := (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support formed.captured)
      have recapturedSyntax : GenericImperativeMatch.Syntax function.source (recaptured.expressionSyntax function.source)
          recaptured.body.context (.statements true function.body) function.resultType := syntaxTree
      have meaning := CallableIndexedOwnedExtendedJointReadyContinuations.method_lambda_native_continuation
        (function := formed.closure) functions wellFormed
        future formed.closureCode history recaptured
        (CallableIndexedOwnedMethodLambdaValues.recaptureOrigin
          (CallableIndexedOwnedMethodLambdaFormationReceipts.source_origin captured code support owner initial packet) formed.captured)
        owner (packet.observed.of_slots formed.slots)
        (CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code support owner initial packet)
        argumentState.val selection.escaped raw.2 raw.1 stable recapturedSyntax budget below
      obtain ⟨sourceCallSize, outcome, after, finalMap, finalWorld, called, resultRep, finalHeaps,
          maps, worlds, frame, metadata, finalState, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at (function := formed.closure)
          future formed.closureCode history recaptured.body.toContext functions
          representedArguments owner argumentState.val middleHeaps capturesValid reference currentCarried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed formed.closureCode history)
          (recaptured.body_origin selection.escaped)
          budget meaning bodyTrace bodyWithin
      obtain ⟨returned, _samePool, relatedCaller⟩ :=
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named).restore
          ⟨initial, packet⟩ finalState (formed.maps.trans (argumentMaps.trans maps))
          (formed.worlds.trans (argumentWorlds.trans worlds)) (formed.frame.trans (argumentFrame.trans frame))
          (formed.copy.metadata_extends.trans (argumentMetadata.trans metadata))
          ((formedState_related captured code support owner initial packet functions formed).trans (argumentRelated.trans related))
      exact ⟨sourceArgumentsSize, sourceCallSize, sources, middle, outcome, after, finalMap, finalWorld,
        sourceArgumentsTrace, called, resultRep, finalHeaps, formed.maps.trans (argumentMaps.trans maps),
        formed.worlds.trans (argumentWorlds.trans worlds), formed.frame.trans (argumentFrame.trans frame),
        formed.copy.metadata_extends.trans (argumentMetadata.trans metadata), returned, relatedCaller⟩

include selection in
/-- The same original parent type and projected result are retained. -/
private theorem parent_result {finalMap : LocationMap} {finalWorld : StoreTyping}
    {outcome : Dynamic.ExpressionOutcome} {result : Value}
    (represented : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result) :
    GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      functions)
      finalMap finalWorld compiler.original.type lowered.type faults outcome result := by
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  rw [loweredType, selection.nativeResult]
  cases represented with
  | value related => exact .value (.compatible selection.rawResult related)
  | fault matched => exact .fault matched

variable (parentTyped : ExpressionHasType function.source function.context id compiler.original.type)

/-- Full whole-parent outputs preserve the same actual reached principal pool,
with deep admission only on successful Source completion. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
    functions)
    finalMap finalWorld compiler.original.type lowered.type faults outcome result ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
  ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
      ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩,
    (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
    PostAdmission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      function.context compiler.original.type outcome reached

include inclusion selection sameCallee copied ordinary coercions parent sourceCount sourceArguments syntaxTree
  wellFormed runtime covers locals heaps admitted parentTyped in
/-- The original method-lambda formation closes the callee internally. Ordered
admitted children and the strict dependent body IH close the whole call. -/
theorem preserves_bounded (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      function.context function.evidence function.source certificate faults size)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap id outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename captured.embedding) result finalStore ∧
      ResultAt captured code support owner initial packet functions compiler outcome after result finalStore finalMap finalWorld := by
  obtain ⟨calleeSize, argumentsSize, callSize, calleeCaptured, calleeHeap, calleeTrace, calleeCopy, suffix,
      _calleeSmall, argumentsSmall, callWithin⟩ :=
    CallableIndexedOwnedSelectedIndirectHeads.suffix_of_source compiler.found compiler.originalForm parent.coercions
      compiler.argumentCoercions parent.arity (lambda captured code coercions) support.unique wellFormed runtime covers locals
      admitted.heap sourceArguments sourceCount trace
  obtain ⟨formed, _source, nativeFormed, _represented, _determined⟩ :=
    CallableIndexedOwnedAdmittedMethodLambdaFormationWithFunctions.formation captured code support owner initial packet profile functions inclusion
      heaps copied ordinary coercions
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional calleeCopy formed.copy
  rw [lambda_function captured code coercions] at calleeTrace suffix
  have calleeEvaluation : Evaluates actual store (compiler.calleeCode.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual)) formed.finalStore := by
    rw [sameCallee]; exact nativeFormed
  have sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions) (formedState captured code support owner initial packet functions formed) budget := by
    intro size outcome after childTrace childBound
    exact sequence_preserves captured code support owner initial packet profile functions compiler prepared selection
      sourceArguments heaps admitted formed budget children locals childTrace childBound
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
        parent_result captured code functions compiler prepared selection (.fault matched), finalHeaps,
        formed.maps.trans maps, formed.worlds.trans worlds, formed.frame.trans frame,
        formed.copy.metadata_extends.trans metadata, reached, (formedState_related captured code support owner initial packet functions formed).trans related,
        after_expression_sized (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals
          parentTyped trace (formed.frame.trans frame)⟩
  | called argumentsTrace called =>
    obtain ⟨payloads, middleStore, result, finalStore, finalMap, finalWorld, argumentEvaluation, bodyEvaluation,
        resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      arguments_preserves captured code support owner initial packet functions compiler prepared selection sourceArguments
        syntaxTree wellFormed runtime covers locals admitted formed budget sequence below argumentsTrace
        (Nat.le_trans (Nat.le_of_lt argumentsSmall) within) called (Nat.le_trans callWithin within)
    have whole := CallableContract.call_success prepared.site.gates native.diagnostics.unknown calleeEvaluation
      selection.stageAccepted argumentEvaluation selection.arityAccepted bodyEvaluation
    rw [← emitted] at whole
    exact ⟨result, finalStore, finalMap, finalWorld, whole,
      parent_result captured code functions compiler prepared selection resultRep, finalHeaps,
      maps, worlds, frame, metadata, reached, related,
      after_expression_sized (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

include inclusion selection sameCallee copied ordinary coercions parent sourceCount sourceArguments syntaxTree
  wellFormed runtime covers locals heaps admitted parentTyped in
/-- The original native call exposes its measured arguments and body children.
Reflection reconstructs the whole Source parent with independent grades. -/
theorem reflects_bounded (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      function.context function.evidence function.source certificate faults size)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget)
    {size : Nat} {result : Value} {finalStore : Store}
    (trace : EvaluationSize size actual store (lowered.expression.rename captured.embedding) result finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap id outcome after ∧
      ResultAt captured code support owner initial packet functions compiler outcome after result finalStore finalMap finalWorld := by
  obtain ⟨formed, sourceCallee, nativeFormed, _represented, _determined⟩ :=
    CallableIndexedOwnedAdmittedMethodLambdaFormationWithFunctions.formation captured code support owner initial packet profile functions inclusion
      heaps copied ordinary coercions
  obtain ⟨calleeSize, calleeTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size sourceCallee
  have calleeEvaluation : Evaluates actual store (compiler.calleeCode.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual)) formed.finalStore := by
    rw [sameCallee]; exact nativeFormed
  have sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (protocol := CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions) (formedState captured code support owner initial packet functions formed) budget := by
    intro size result finalStore childTrace childBound
    exact sequence_reflects captured code support owner initial packet profile functions compiler prepared selection
      sourceArguments heaps admitted formed budget children locals childTrace childBound
  have emitted := prepared.lowered_rename compiler captured.embedding
  rw [emitted, selection.nativeResult] at trace
  cases completed code (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet) formed.embedding formed.closureActual
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
          wellFormed runtime covers (locals.mono formed.copy.metadata_extends) (admitted.heap.copy formed.copy)
          sourceArguments sourceCount calleeTrace
          (CallableIndexedOwnedIndirectExpressionHeads.SourceSuffix.argumentFault failed)
        exact ⟨sourceSize, _, after, finalMap, finalWorld, sourceTrace,
          parent_result captured code functions compiler prepared selection (.fault matched), finalHeaps,
          formed.maps.trans maps, formed.worlds.trans worlds, formed.frame.trans frame,
          formed.copy.metadata_extends.trans metadata, reached, (formedState_related captured code support owner initial packet functions formed).trans related,
          after_expression_sized (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals
            parentTyped sourceTrace (formed.frame.trans frame)⟩
  | applied argumentsTrace bodyTrace argumentsStrict bodyStrict =>
    obtain ⟨sourceArgumentsSize, sourceCallSize, arguments, middle, outcome, after, finalMap, finalWorld,
        sourceArgumentsTrace, called, resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      arguments_reflects captured code support owner initial packet functions compiler prepared selection sourceArguments
        syntaxTree wellFormed runtime covers locals admitted formed budget sequence below argumentsTrace argumentsStrict
        bodyTrace (Nat.le_of_lt bodyStrict)
    obtain ⟨sourceSize, sourceTrace⟩ := CallableIndexedOwnedIndirectSourceAdapters.SourceSuffix.to_expression
      compiler.found compiler.originalForm parent.requirements parent.coercions compiler.argumentCoercions parent.arity
      wellFormed runtime covers (locals.mono formed.copy.metadata_extends) (admitted.heap.copy formed.copy)
      sourceArguments sourceCount calleeTrace
      (CallableIndexedOwnedIndirectExpressionHeads.SourceSuffix.called sourceArgumentsTrace called)
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace,
      parent_result captured code functions compiler prepared selection resultRep, finalHeaps,
      maps, worlds, frame, metadata, reached, related,
      after_expression_sized (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals parentTyped sourceTrace frame⟩

include inclusion wellFormed runtime covers locals heaps admitted in
/-- This actual static receipt selects the internally proved literal producer;
only genuine strictly smaller argument and extended-family body children remain. -/
theorem preserves_at_receipt (issued : Receipt captured code support compiler certificate) (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      function.context function.evidence function.source certificate faults size)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap id outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename captured.embedding) result finalStore ∧
      ResultAt captured code support owner initial packet functions compiler outcome after result finalStore finalMap finalWorld := by
  exact preserves_bounded (captured := captured) (code := code) (support := support) (owner := owner)
    (initial := initial) (packet := packet) (profile := profile) (functions := functions) (inclusion := inclusion) (compiler := compiler)
    (prepared := issued.prepared) (parent := issued.parent) (selection := issued.selection)
    (sameCallee := issued.sameCallee) (ordinary := issued.ordinary) (coercions := issued.coercions)
    (copied := issued.copied)
    (sourceArguments := issued.sourceArguments) (sourceCount := issued.sourceCount) (syntaxTree := issued.syntaxTree)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals) (heaps := heaps)
    (admitted := admitted) (parentTyped := issued.parentTyped) budget children below trace within

include inclusion wellFormed runtime covers locals heaps admitted in
/-- Native receipt selection preserves its measured child bounds while the
whole Source trace and successful admission are reconstructed independently. -/
theorem reflects_at_receipt (issued : Receipt captured code support compiler certificate) (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      function.context function.evidence function.source certificate faults size)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget)
    {size : Nat} {result : Value} {finalStore : Store}
    (trace : EvaluationSize size actual store (lowered.expression.rename captured.embedding) result finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap id outcome after ∧
      ResultAt captured code support owner initial packet functions compiler outcome after result finalStore finalMap finalWorld := by
  exact reflects_bounded (captured := captured) (code := code) (support := support) (owner := owner)
    (initial := initial) (packet := packet) (profile := profile) (functions := functions) (inclusion := inclusion) (compiler := compiler)
    (prepared := issued.prepared) (parent := issued.parent) (selection := issued.selection)
    (sameCallee := issued.sameCallee) (ordinary := issued.ordinary) (coercions := issued.coercions)
    (copied := issued.copied)
    (sourceArguments := issued.sourceArguments) (sourceCount := issued.sourceCount) (syntaxTree := issued.syntaxTree)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals) (heaps := heaps)
    (admitted := admitted) (parentTyped := issued.parentTyped) budget children below trace within

end Parent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSelectedCallWithFunctions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionHeadsWithFunctions
/-! Authentic method lambda Head certificates are unchanged. The caller's
function model remains generic through formation, ordered arguments, body and
restoration. Forward inclusion transfers only the original formed closure;
all real heap/state and independently graded Source receipts retain that model. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionHeadsWithFunctions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)
open CallableIndexedOwnedMethodLambdaExpressionHeads (Formation Call Head bridge)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context)

/-- Every child and returned heap retains the caller's same function model. -/
def model (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) :=
  CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile).Includes functions)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  {certificate : GenericExpressionMeaning.Certificate}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include inclusion complete slots wellFormed runtime covers in
/-- Each authentic finite branch constructs captures, Code and Support at
its actual input. Strict arguments and the joint body's own strict IH remain. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (registry := registry) (faults := faults) principal context certificate) faults size := by
  intro scope id lowered head node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  let captured := CallableIndexedOwnedMethodPrincipalCaptures.captures principal owner initial.val initial.property
    complete environments agrees nativeTyped
  have packet := CallableIndexedOwnedMethodPrincipalCaptures.captured_packet principal owner initial.val initial.property
    complete environments agrees nativeTyped slots
  let capturedInitial : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named).State
      ⟨scope, mapping, world, before, store, captured.canonical⟩ := ⟨initial.val, packet⟩
  have capturedAdmission : Admission (bridge (headers := headers) principal owner) context capturedInitial :=
    ⟨admitted.heap, admitted.rows⟩
  cases head with
  | formation head =>
    let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
    let support : Support code registry faults := head.support environment
    have sourceFound : (CallableIndexedNamedGeneration.source principal.named).lookupExpression? id = some code.sourceNode := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode, CallableIndexedLambdaGeneration.closure, head.identifier] using
        head.site.code.sourceFound
    have same := Option.some.inj (found.symm.trans sourceFound)
    subst node
    have nativeTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
        (head.function environment).context (head.function environment).evidence (head.function environment).source
        (head.function environment).captured before code.id outcome after := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using trace
    have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context code.id code.sourceNode.type := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using typed
    obtain ⟨result, finalStore, evaluated, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedMethodLambdaFormationWithFunctions.preserves_at
        (function := head.function environment) (scope := scope) (actual := actual) captured code support owner initial.val packet profile functions inclusion
        wellFormed runtime covers locals actualTyped head.sourceType head.site.snapshots head.ordinary head.coercions heaps
        capturedAdmission nativeTrace
    have evaluated : Evaluates actual store (lowered.expression.rename ξ) result finalStore := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode,
        head.emitted, captured, CallableIndexedOwnedMethodPrincipalCaptures.captures] using evaluated
    have represented : GenericExpressionMeaning.ResultRepresents
        (model (registry := registry) functions)
        finalMap finalWorld code.sourceNode.type lowered.type faults outcome result := by
      simpa only [model, code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode, head.emitted] using represented
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩
  | call head =>
    let code : Code compiled.indexed (head.formation.function environment) scope captured.administrative := head.formation.code environment
    let support : Support code registry faults := head.formation.support environment
    have same := Option.some.inj (found.symm.trans head.compiler.found)
    subst node
    let issued : CallableIndexedOwnedMethodLambdaSelectedCall.Receipt
        (function := head.formation.function environment) captured code support head.compiler certificate := {
      native := head.native, prepared := head.prepared, parent := head.parent,
      selection := ⟨head.selection.children, head.selection.nativeTypes, head.selection.escaped,
        head.selection.rawResult, head.selection.nativeResult, head.selection.stageAccepted, head.selection.arityAccepted⟩,
      sameCallee := head.sameCallee, ordinary := head.formation.ordinary, coercions := head.formation.coercions,
      copied := head.formation.site.snapshots, sourceArguments := head.sourceArguments, sourceCount := head.sourceCount,
      syntaxTree := head.formation.syntaxTree, parentTyped := typed }
    obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedMethodLambdaSelectedCallWithFunctions.preserves_at_receipt
        (function := head.formation.function environment) (scope := scope) (actual := actual)
        (captured := captured) (code := code) (support := support) (owner := owner) (initial := initial.val) (packet := packet)
        (profile := profile) (functions := functions) (inclusion := inclusion) (compiler := head.compiler) (wellFormed := wellFormed) (runtime := runtime)
        (covers := covers) (locals := locals) (heaps := heaps)
        (admitted := capturedAdmission) issued budget children below trace within
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩

include inclusion complete slots wellFormed runtime covers in
/-- Native child bounds are measured independently. The same static branch
producer reconstructs the authentic Source trace and restores its exact pool. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (registry := registry) (faults := faults) principal context certificate) faults size := by
  intro scope id lowered head node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  let captured := CallableIndexedOwnedMethodPrincipalCaptures.captures principal owner initial.val initial.property
    complete environments agrees nativeTyped
  have packet := CallableIndexedOwnedMethodPrincipalCaptures.captured_packet principal owner initial.val initial.property
    complete environments agrees nativeTyped slots
  let capturedInitial : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named).State
      ⟨scope, mapping, world, before, store, captured.canonical⟩ := ⟨initial.val, packet⟩
  have capturedAdmission : Admission (bridge (headers := headers) principal owner) context capturedInitial :=
    ⟨admitted.heap, admitted.rows⟩
  cases head with
  | formation head =>
    let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
    let support : Support code registry faults := head.support environment
    have sourceFound : (CallableIndexedNamedGeneration.source principal.named).lookupExpression? id = some code.sourceNode := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode,
        CallableIndexedLambdaGeneration.closure, head.identifier] using head.site.code.sourceFound
    have same := Option.some.inj (found.symm.trans sourceFound)
    subst node
    have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context code.id code.sourceNode.type := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using typed
    have actualCompleted : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) value finalStore := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode,
        head.emitted, captured, CallableIndexedOwnedMethodPrincipalCaptures.captures] using completed
    obtain ⟨sourceSize, outcome, after, trace, _native, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame,
        metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedMethodLambdaFormationWithFunctions.reflects_at
        (function := head.function environment) (scope := scope) (actual := actual) captured code support owner initial.val packet profile functions inclusion
        wellFormed runtime covers locals actualTyped head.sourceType head.site.snapshots head.ordinary head.coercions heaps
        capturedAdmission actualCompleted
    have sourceTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) environment before id outcome after := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using trace
    have represented : GenericExpressionMeaning.ResultRepresents
        (model (registry := registry) functions)
        finalMap finalWorld code.sourceNode.type lowered.type faults outcome value := by
      simpa only [model, code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode, head.emitted] using represented
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed sourceTrace frame⟩
  | call head =>
    let code : Code compiled.indexed (head.formation.function environment) scope captured.administrative := head.formation.code environment
    let support : Support code registry faults := head.formation.support environment
    have same := Option.some.inj (found.symm.trans head.compiler.found)
    subst node
    let issued : CallableIndexedOwnedMethodLambdaSelectedCall.Receipt
        (function := head.formation.function environment) captured code support head.compiler certificate := {
      native := head.native, prepared := head.prepared, parent := head.parent,
      selection := ⟨head.selection.children, head.selection.nativeTypes, head.selection.escaped,
        head.selection.rawResult, head.selection.nativeResult, head.selection.stageAccepted, head.selection.arityAccepted⟩,
      sameCallee := head.sameCallee, ordinary := head.formation.ordinary, coercions := head.formation.coercions,
      copied := head.formation.site.snapshots, sourceArguments := head.sourceArguments, sourceCount := head.sourceCount,
      syntaxTree := head.formation.syntaxTree, parentTyped := typed }
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedMethodLambdaSelectedCallWithFunctions.reflects_at_receipt
        (function := head.formation.function environment) (scope := scope) (actual := actual)
        (captured := captured) (code := code) (support := support) (owner := owner) (initial := initial.val) (packet := packet)
        (profile := profile) (functions := functions) (inclusion := inclusion) (compiler := head.compiler) (wellFormed := wellFormed) (runtime := runtime)
        (covers := covers) (locals := locals) (heaps := heaps)
        (admitted := capturedAdmission) issued budget children below completed within
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionHeadsWithFunctions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodMixedExpressionHeads
/-! A method caller uses one genuine principal packet and one function model
for named calls and accepted method-lambda formation/calls. The real compiler
prefix authenticates its global slots. Both finite branches retain their original
Source/compiler receipts and consume only strict children of the shared family. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodMixedExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaExpressionHeads (bridge)
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context) (compilation : SourceCoreFunctions.Context)

/-- Original named selections and method lambda selections form a finite sum.
The child certificate remains the actual certificate issued by the same Tree. -/
inductive Head (certificate : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | named {scope id lowered}
      (head : RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation (CallableIndexedNamedGeneration.source principal.named) context principal.dictionary certificate scope id lowered) :
      Head certificate scope id lowered
  | method_lambda {scope id lowered}
      (head : CallableIndexedOwnedMethodLambdaExpressionHeads.Head (registry := registry) (faults := faults)
        principal context certificate scope id lowered) : Head certificate scope id lowered

variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- Only the slot proof changes. The full original caller pool and restoration
retain the genuine principal's bundle, Source seed and actual reached history. -/
def named_caller (prefixOne : compilation.administrativePrefix = 1) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner
        compilation.administrativePrefix index.scope index.canonical)
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named) where
  pool := fun state => state.val
  records_eq := fun _ => rfl
  related := fun related => related
  slots := fun state => prefixOne.symm ▸ state.property.globals
  restore := (CallableIndexedOwnedOriginCanonicalState.carrier (headers := headers) owner principal.named).restore

/-- Erasing slot proofs recovers the same original caller bridge definitionally. -/
theorem named_bridge (prefixOne : compilation.administrativePrefix = 1) :
    CallableIndexedOwnedIndirectCallerProtocol.forget_slots (named_caller principal compilation owner prefixOne) =
      bridge (headers := headers) principal owner := rfl

variable
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile).Includes functions)
  (prefixOne : compilation.administrativePrefix = 1)
  (prefixZero : owner.key.capturePrefix = 0)
  (globalCounts : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  {certificate : GenericExpressionMeaning.Certificate}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include inclusion prefixOne prefixZero globalCounts complete slots wellFormed runtime covers unique owners idsUnique
  sameLayouts escaped profiles syntaxTrees in
/-- Each selected finite branch runs at the same input and returned caller.
Its body obligation is the actual strict child of the extended shared family. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation certificate) faults size := by
  have named : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation (CallableIndexedNamedGeneration.source principal.named) context principal.dictionary certificate) faults size :=
    CallableIndexedOwnedAdmittedNamedExpressionHeads.preserves_at
    (functions := functions) (owner := owner) (runtime := true) principal.dictionary
    (named_caller principal compilation owner prefixOne) wellFormed runtime covers unique idsUnique
    sameLayouts escaped profiles owners budget size within children
    (fun header member => CallableIndexedOwnedNamedNestedReadyFamilyReceipts.source_bodies
      (functions := functions) (owner := owner) (runtime := true) wellFormed prefixZero (globalCounts header member)
      member (syntaxTrees header member) (fun index => below (.namedNested index)))
  have methodLambda : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CallableIndexedOwnedMethodLambdaExpressionHeads.Head (registry := registry) (faults := faults) principal context certificate) faults size :=
    CallableIndexedOwnedMethodLambdaExpressionHeadsWithFunctions.preserves_at
    principal context owner profile functions inclusion complete slots wellFormed runtime covers budget size within children below
  intro scope id lowered head node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  cases head with
  | named head => exact named head found sourceTyped environments heaps locals agrees typed initial admitted trace
  | method_lambda head => exact methodLambda head found sourceTyped environments heaps locals agrees typed initial admitted trace

include inclusion prefixOne prefixZero globalCounts complete slots wellFormed runtime covers unique
  sameLayouts escaped profiles syntaxTrees in
/-- Native finite selection keeps the original measured children and restores
the same full caller while independently reconstructing the Source parent. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation certificate) faults size := by
  have named : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation (CallableIndexedNamedGeneration.source principal.named) context principal.dictionary certificate) faults size :=
    CallableIndexedOwnedAdmittedNamedExpressionHeads.reflects_at
    (functions := functions) (owner := owner) (runtime := true) principal.dictionary
    (named_caller principal compilation owner prefixOne) wellFormed runtime covers unique
    sameLayouts escaped profiles budget size within children
    (fun header member => CallableIndexedOwnedNamedNestedReadyFamilyReceipts.native_bodies
      (functions := functions) (owner := owner) (runtime := true) wellFormed prefixZero (globalCounts header member)
      member (syntaxTrees header member) (fun index => below (.namedNested index)))
  have methodLambda : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CallableIndexedOwnedMethodLambdaExpressionHeads.Head (registry := registry) (faults := faults) principal context certificate) faults size :=
    CallableIndexedOwnedMethodLambdaExpressionHeadsWithFunctions.reflects_at
    principal context owner profile functions inclusion complete slots wellFormed runtime covers budget size within children below
  intro scope id lowered head node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  cases head with
  | named head => exact named head found sourceTyped environments heaps locals agrees typed initial admitted completed
  | method_lambda head => exact methodLambda head found sourceTyped environments heaps locals agrees typed initial admitted completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodMixedExpressionHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodMixedExpressionRuntimeBounds
/-! Genuine named/direct named calls and accepted method-lambda formation/calls
share the same principal packet and supplied function model. The existing
expression support fold consumes this finite static Head sum and internally
constructed runtime literals. The compiler prefix and genuine named profiles
remain explicit; strict extended-family body children supply the measured IH. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodMixedExpressionRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaExpressionHeads (bridge)
open CallableIndexedOwnedMethodMixedExpressionHeads (Head)
open CallableIndexedOwnedMethodLambdaExpressionHeadsWithFunctions (model)
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context) (compilation : SourceCoreFunctions.Context)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

/-- The original expression Tree construction uses the genuine finite Head sum. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree
    (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation)
    fuel (.initial compiled.compatible.checked) (CallableIndexedNamedGeneration.source principal.named)
    context solved reasonAt

/-- Runtime literals retain their actual requirement ledger receipts. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree.WithLiterals
    (calls := Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) (fuel := fuel)
    (values := .initial compiled.compatible.checked)
    (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
    (solved := solved) (reasonAt := reasonAt)
    (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved
      (CallableIndexedNamedGeneration.source principal.named) id lowered)

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile).Includes functions)
  (prefixOne : compilation.administrativePrefix = 1)
  (prefixZero : owner.key.capturePrefix = 0)
  (globalCounts : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include inclusion prefixOne prefixZero globalCounts complete slots extension faithful observations functionTypes
  wellFormed runtime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees owners idsUnique in
theorem preserves_at_with_literals [FunctionCalls.FaultTokens faults] {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary
      (CallableIndexedNamedGeneration.source principal.named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions
    (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              principal.dictionary unique uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (bridge (headers := headers) principal owner)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      functions
      extension faithful observations functionTypes principal.dictionary unique missing wellFormed runtime covers
      (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) budget child childWithin children
    exact CallableIndexedOwnedMethodMixedExpressionHeads.preserves_at
      (principal := principal) (context := context) (compilation := compilation) (owner := owner)
      (profile := profile) (functions := functions) (inclusion := inclusion) (prefixOne := prefixOne)
      (prefixZero := prefixZero) (globalCounts := globalCounts) (complete := complete) (slots := slots)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (unique := unique)
      (owners := owners) (idsUnique := idsUnique) (sameLayouts := sameLayouts) (escaped := escaped)
      (profiles := profiles) (syntaxTrees := syntaxTrees) budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion prefixOne prefixZero globalCounts complete slots extension faithful observations functionTypes
  wellFormed runtime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem reflects_at_with_literals [FunctionCalls.FaultTokens faults] {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary
      (CallableIndexedNamedGeneration.source principal.named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions
    (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              principal.dictionary uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (bridge (headers := headers) principal owner)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      functions
      extension faithful observations functionTypes principal.dictionary unique missing wellFormed runtime covers
      (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation) budget child childWithin children
    exact CallableIndexedOwnedMethodMixedExpressionHeads.reflects_at
      (principal := principal) (context := context) (compilation := compilation) (owner := owner)
      (profile := profile) (functions := functions) (inclusion := inclusion) (prefixOne := prefixOne)
      (prefixZero := prefixZero) (globalCounts := globalCounts) (complete := complete) (slots := slots)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (unique := unique)
      (sameLayouts := sameLayouts) (escaped := escaped)
      (profiles := profiles) (syntaxTrees := syntaxTrees) budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion prefixOne prefixZero globalCounts complete slots extension faithful observations functionTypes
  wellFormed runtime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees owners idsUnique in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem preserves_at_runtime [FunctionCalls.FaultTokens faults] (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RuntimeTree (headers := headers) (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context compilation) faults size := by
  exact preserves_at_with_literals
    (principal := principal) (context := context) (compilation := compilation) (owner := owner)
    (profile := profile) (functions := functions) (inclusion := inclusion) (prefixOne := prefixOne)
    (prefixZero := prefixZero) (globalCounts := globalCounts) (complete := complete) (slots := slots)
    (extension := extension) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (unique := unique)
    (owners := owners) (idsUnique := idsUnique) (uninitialized := uninitialized) (missing := missing)
    (sameLayouts := sameLayouts) (escaped := escaped) (profiles := profiles) (syntaxTrees := syntaxTrees)
    (CompatibleExpressionLiteralRuntime.preserves
      functions
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger unique faults)
    budget size within below

include inclusion prefixOne prefixZero globalCounts complete slots extension faithful observations functionTypes
  wellFormed runtime covers unique uninitialized missing sameLayouts escaped profiles syntaxTrees in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem reflects_at_runtime [FunctionCalls.FaultTokens faults] (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RuntimeTree (headers := headers) (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context compilation) faults size := by
  exact reflects_at_with_literals
    (principal := principal) (context := context) (compilation := compilation) (owner := owner)
    (profile := profile) (functions := functions) (inclusion := inclusion) (prefixOne := prefixOne)
    (prefixZero := prefixZero) (globalCounts := globalCounts) (complete := complete) (slots := slots)
    (extension := extension) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (unique := unique)
    (uninitialized := uninitialized) (missing := missing)
    (sameLayouts := sameLayouts) (escaped := escaped) (profiles := profiles) (syntaxTrees := syntaxTrees)
    (CompatibleExpressionLiteralRuntime.reflects
      functions
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger (CallableIndexedNamedGeneration.source principal.named) faults)
    budget size within below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodMixedExpressionRuntimeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionRuntimeBounds
/-! The existing expression support fold consumes authentic method-lambda
formation and selected-call heads. Every argument remains a child of the same
Tree; actual principal packets and runtime literals are constructed internally.
Strict extended body children remain the measured family obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaExpressionHeads (bridge model Head)
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

/-- The original compiler Tree retains genuine finite method-lambda heads. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree (Head (registry := registry) (faults := faults) principal context)
    fuel (.initial compiled.compatible.checked) (CallableIndexedNamedGeneration.source principal.named)
    context solved reasonAt

/-- Numeric literals retain their actual runtime ledger receipts. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree.WithLiterals
    (calls := Head (registry := registry) (faults := faults) principal context) (fuel := fuel)
    (values := .initial compiled.compatible.checked)
    (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
    (solved := solved) (reasonAt := reasonAt)
    (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved
      (CallableIndexedNamedGeneration.source principal.named) id lowered)

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named))
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
theorem preserves_at_with_literals [FunctionCalls.FaultTokens faults] {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary
      (CallableIndexedNamedGeneration.source principal.named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (registry := registry) (faults := faults) principal context) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
    (Head (registry := registry) (faults := faults) principal context) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals
              (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              principal.dictionary unique uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (bridge (headers := headers) principal owner)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
      extension faithful observations functionTypes principal.dictionary unique missing wellFormed runtime covers
      (Head (registry := registry) (faults := faults) principal context) budget child childWithin children
    exact CallableIndexedOwnedMethodLambdaExpressionHeads.preserves_at
      principal context owner profile complete slots wellFormed runtime covers budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
theorem reflects_at_with_literals [FunctionCalls.FaultTokens faults] {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary
      (CallableIndexedNamedGeneration.source principal.named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (registry := registry) (faults := faults) principal context) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
    (Head (registry := registry) (faults := faults) principal context) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals
              (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              principal.dictionary uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (bridge (headers := headers) principal owner)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
      extension faithful observations functionTypes principal.dictionary unique missing wellFormed runtime covers
      (Head (registry := registry) (faults := faults) principal context) budget child childWithin children
    exact CallableIndexedOwnedMethodLambdaExpressionHeads.reflects_at
      principal context owner profile complete slots wellFormed runtime covers budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem preserves_at_runtime [FunctionCalls.FaultTokens faults] (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RuntimeTree (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context) faults size := by
  exact preserves_at_with_literals principal context owner profile complete slots extension faithful observations
    functionTypes wellFormed runtime covers unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.preserves
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger unique faults)
    budget size within below

include complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem reflects_at_runtime [FunctionCalls.FaultTokens faults] (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RuntimeTree (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context) faults size := by
  exact reflects_at_with_literals principal context owner profile complete slots extension faithful observations
    functionTypes wellFormed runtime covers unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.reflects
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger (CallableIndexedNamedGeneration.source principal.named) faults)
    budget size within below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionRuntimeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionRuntimeBoundsWithFunctions
/-! The same existing expression support fold consumes authentic method-lambda
formation and selected-call heads. Every argument remains a child of the same
Tree; actual principal packets and runtime literals are constructed internally.
Strict extended body children remain the measured family obligation. The same
caller function model is retained by every heap and expression result. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionRuntimeBoundsWithFunctions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaExpressionHeads (bridge Head)
open CallableIndexedOwnedMethodLambdaExpressionHeadsWithFunctions (model)
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

/-- Certificate identity is the original static compiler Tree. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedMethodLambdaExpressionRuntimeBounds.Tree (registry := registry) (faults := faults)
    (solved := solved) (reasonAt := reasonAt) (fuel := fuel) principal context

/-- Runtime literal receipts remain the original static certificate family. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedMethodLambdaExpressionRuntimeBounds.RuntimeTree (registry := registry) (faults := faults)
    (solved := solved) (reasonAt := reasonAt) (fuel := fuel) principal context

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile).Includes functions)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named))
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include inclusion complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
theorem preserves_at_with_literals [FunctionCalls.FaultTokens faults] {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary
      (CallableIndexedNamedGeneration.source principal.named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (registry := registry) (faults := faults) principal context) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions
    (Head (registry := registry) (faults := faults) principal context) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              principal.dictionary unique uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (bridge (headers := headers) principal owner)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      functions
      extension faithful observations functionTypes principal.dictionary unique missing wellFormed runtime covers
      (Head (registry := registry) (faults := faults) principal context) budget child childWithin children
    exact CallableIndexedOwnedMethodLambdaExpressionHeadsWithFunctions.preserves_at
      principal context owner profile functions inclusion complete slots wellFormed runtime covers budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
theorem reflects_at_with_literals [FunctionCalls.FaultTokens faults] {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary
      (CallableIndexedNamedGeneration.source principal.named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (registry := registry) (faults := faults) principal context) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := CallableIndexedNamedGeneration.source principal.named) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions
    (Head (registry := registry) (faults := faults) principal context) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              principal.dictionary uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (bridge (headers := headers) principal owner)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named)
      functions
      extension faithful observations functionTypes principal.dictionary unique missing wellFormed runtime covers
      (Head (registry := registry) (faults := faults) principal context) budget child childWithin children
    exact CallableIndexedOwnedMethodLambdaExpressionHeadsWithFunctions.reflects_at
      principal context owner profile functions inclusion complete slots wellFormed runtime covers budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem preserves_at_runtime [FunctionCalls.FaultTokens faults] (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RuntimeTree (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context) faults size := by
  exact preserves_at_with_literals principal context owner profile functions inclusion complete slots extension faithful observations
    functionTypes wellFormed runtime covers unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.preserves
      functions
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger unique faults)
    budget size within below

include inclusion complete slots extension faithful observations functionTypes wellFormed runtime covers unique uninitialized missing in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem reflects_at_runtime [FunctionCalls.FaultTokens faults] (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (registry := registry) functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RuntimeTree (registry := registry) (faults := faults) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) principal context) faults size := by
  exact reflects_at_with_literals principal context owner profile functions inclusion complete slots extension faithful observations
    functionTypes wellFormed runtime covers unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.reflects
      functions
      (Program.ofChecked compiled.sourceProgram) context principal.dictionary sameLedger runtimeLedger (CallableIndexedNamedGeneration.source principal.named) faults)
    budget size within below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionRuntimeBoundsWithFunctions
end
