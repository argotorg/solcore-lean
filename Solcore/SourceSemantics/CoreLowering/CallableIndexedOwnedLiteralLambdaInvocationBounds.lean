import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralLambdaBodyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaInvocation

/-! A genuine chosen singleton-return Support supplies its literal continuation
internally. The original invocation installs parameters and restores the caller
once, preserving the independent Source and native grades and the full pool. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralLambdaInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedLambdaEntryPrefix SourceCoreCallableIndexedFrames
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedChosenWordLiteralExpressionBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (literalRoot : LiteralRootReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (literalId : ExpressionId) (node : ExpressionNode)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (chosen : ChosenFactory literalRoot.root (approved literalId) receipt)
  (capturedEnvironment : Dynamic.Environment)
  (facts : WordNodeFacts (caller := caller) literalId node)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {statement : StatementId} {statementNode : StatementNode}
  (found : (receipt.formation.function capturedEnvironment).source.lookupStatement? statement = some statementNode)
  (form : statementNode.form = .returnStmt (some literalId))
  (singleton : (receipt.formation.function capturedEnvironment).body = [statement])
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {mapping : LocationMap} {world : StoreTyping} {actualEnvironment : Environment}
  (captured : Captures compiled.indexed mapping world scope
    (receipt.formation.function capturedEnvironment).captured actualEnvironment)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (history : History (receipt.formation.code capturedEnvironment))
  (origin : SourceOrigin (receipt.formation.support capturedEnvironment) history)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (first : State headers keys ⟨callerScope, mapping, world, before, store, canonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped (receipt.formation.function capturedEnvironment).context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes (receipt.formation.function capturedEnvironment).context
    before arguments (receipt.formation.support capturedEnvironment).body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows first)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world (receipt.formation.code capturedEnvironment).receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before (receipt.formation.function capturedEnvironment).context.locals
    (receipt.formation.function capturedEnvironment).captured)
  (reference : captured.canonical[(receipt.formation.code capturedEnvironment).referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))

include chosen facts found form singleton origin observed beforeTyped argumentsTyped stable represented heaps locals reference in
/-- The actual literal continuation feeds one original invocation and restoration. -/
theorem invocation_preserves (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence (receipt.formation.function capturedEnvironment).evidence before
      (.closure (receipt.formation.function capturedEnvironment)) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: actualEnvironment)
        store ((receipt.formation.code capturedEnvironment).body.rename captured.embedding.lift.lift) value finalStore ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
        (receipt.formation.code capturedEnvironment) functions first outcome after value finalStore finalMap finalWorld := by
  have bodyLedger : (receipt.formation.support capturedEnvironment).body.context.solvedRequirements =
      (context compiled.indexed caller.named).solvedRequirements := by
    exact (receipt.formation.support capturedEnvironment).body.valid.ledger.trans
      (congrArg (fun c : SourceCoreFunctions.Context => c.solvedRequirements)
        (receipt.formation.support capturedEnvironment).compilation)
  have continuation := CallableIndexedOwnedLiteralLambdaBodyContinuations.source_continuation
      (registry := registry) (faults := faults) (nativeArguments := nativeArguments)
      (literalRoot := literalRoot) (literalId := literalId) (node := node) (receipt := receipt)
      (chosen := chosen) (capturedEnvironment := capturedEnvironment) (facts := facts) (functions := functions)
      (found := found) (form := form) (singleton := singleton)
      (bodyLedger := bodyLedger) (bodyRuntime := (receipt.formation.support capturedEnvironment).body.valid.runtime)
      (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
      (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
      (argumentsTyped := argumentsTyped) (stable := stable) budget
  obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
  exact CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at_with_continuation
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
    (receipt.formation.code capturedEnvironment) history
    (receipt.formation.support capturedEnvironment).body.toBody.toContext functions represented owner first heaps locals
    reference currentCarried
    (CallableIndexedLambdaTemplatePermission.lambda_allowed (receipt.formation.code capturedEnvironment) history)
    budget continuation trace within

include chosen facts found form singleton origin observed beforeTyped argumentsTyped stable represented heaps locals reference in
/-- The native child retains its own grade and uses the genuine closure frame. -/
theorem invocation_reflects (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: actualEnvironment)
        store ((receipt.formation.code capturedEnvironment).body.rename captured.embedding.lift.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence (receipt.formation.function capturedEnvironment).evidence before
        (.closure (receipt.formation.function capturedEnvironment)) arguments outcome after ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
        (receipt.formation.code capturedEnvironment) functions first outcome after value finalStore finalMap finalWorld := by
  have bodyLedger : (receipt.formation.support capturedEnvironment).body.context.solvedRequirements =
      (context compiled.indexed caller.named).solvedRequirements := by
    exact (receipt.formation.support capturedEnvironment).body.valid.ledger.trans
      (congrArg (fun c : SourceCoreFunctions.Context => c.solvedRequirements)
        (receipt.formation.support capturedEnvironment).compilation)
  have continuation := CallableIndexedOwnedLiteralLambdaBodyContinuations.native_continuation
      (registry := registry) (faults := faults)
      (literalRoot := literalRoot) (literalId := literalId) (node := node) (receipt := receipt)
      (chosen := chosen) (capturedEnvironment := capturedEnvironment) (facts := facts) (functions := functions)
      (found := found) (form := form) (singleton := singleton)
      (bodyLedger := bodyLedger) (bodyRuntime := (receipt.formation.support capturedEnvironment).body.valid.runtime)
      (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
      (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
      (argumentsTyped := argumentsTyped) (stable := stable) budget
  obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
  exact CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at_with_continuation
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
    (receipt.formation.code capturedEnvironment) history
    (receipt.formation.support capturedEnvironment).body.toBody.toContext functions represented owner first heaps locals
    reference currentCarried
    (CallableIndexedLambdaTemplatePermission.lambda_allowed (receipt.formation.code capturedEnvironment) history)
    (receipt.formation.support capturedEnvironment).body.frame budget continuation completed within

include chosen facts found form singleton origin observed beforeTyped argumentsTyped stable represented heaps locals reference in
/-- The original application edge carries that same restored invocation tuple. -/
theorem application_preserves (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence (receipt.formation.function capturedEnvironment).evidence before
      (.closure (receipt.formation.function capturedEnvironment)) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value (receipt.formation.code capturedEnvironment) captured.embedding history.native actualEnvironment,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
        (receipt.formation.code capturedEnvironment) functions first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result⟩ :=
    invocation_preserves (literalRoot := literalRoot) (literalId := literalId) (node := node) (receipt := receipt)
      (chosen := chosen) (capturedEnvironment := capturedEnvironment) (facts := facts) (functions := functions)
      (found := found) (form := form) (singleton := singleton) (owner := owner) (captured := captured)
      (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed)
      (first := first) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
      (represented := represented) (heaps := heaps) (locals := locals) (reference := reference) budget trace within
  exact ⟨value, finalStore, finalMap, finalWorld,
    .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result⟩

include chosen facts found form singleton origin observed beforeTyped argumentsTyped stable represented heaps locals reference in
/-- The actual strict application child reconstructs an independently sized Source call. -/
theorem application_reflects (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [CallableIndexedLambdaValues.value (receipt.formation.code capturedEnvironment) captured.embedding history.native actualEnvironment,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence (receipt.formation.function capturedEnvironment).evidence before
        (.closure (receipt.formation.function capturedEnvironment)) arguments outcome after ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
        (receipt.formation.code capturedEnvironment) functions first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact invocation_reflects (literalRoot := literalRoot) (literalId := literalId) (node := node) (receipt := receipt)
      (chosen := chosen) (capturedEnvironment := capturedEnvironment) (facts := facts) (functions := functions)
      (found := found) (form := form) (singleton := singleton) (owner := owner) (captured := captured)
      (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed)
      (first := first) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
      (represented := represented) (heaps := heaps) (locals := locals) (reference := reference) budget applied
    (Nat.le_trans (Nat.le_of_lt smaller) within)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralLambdaInvocationBounds
