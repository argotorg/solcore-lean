import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredMembers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenNestedLambdaBodyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaInvocation

/-! A positive chosen member supplies its literal factory and body. The nested
continuation is derived internally, then the original invocation restores the
actual caller pool once. Current arguments and static domains stay authentic. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedChosenOrdinaryFormedMembers (FactoryMember)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt)
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)

variable {i : OrdinaryIndex compiled} {history : History i.code}

/-- These fields are the same actual positive constructor, indexed by its owner. -/
structure ChosenFor (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (i : OrdinaryIndex compiled) (history : History i.code) : Prop where
  factory : FactoryMember root expressionSyntax i
  origin : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.SourceOrigin i.support history
  prefixContext : i.captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) i.support.caller
  globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 i.scope i.captured.canonical owner.key.frameLocation
  referenceIndex : i.code.referenceIndex = i.scope.length + 1 + compiled.indexed.base.globals.length
  typed : RuntimeValueHasType i.world (value i.code i.captured.embedding history.native i.capturedActual)
    (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)
    compiled.indexed.layouts.definitions

/-- Only the genuine positive constructor exposes its own actual owner. -/
theorem chosen_for (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    ∃ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, ChosenFor (headers := headers) root expressionSyntax owner i history := by
  cases member with
  | ordinary owner factory origin prefixContext globals referenceIndex typed =>
    exact ⟨owner, factory, origin, prefixContext, globals, referenceIndex, typed⟩

/-- The complete actual ledger accompanies independent Source runtime validity. -/
def Validity (i : OrdinaryIndex compiled) (context : SourceSemantics.Context) : Prop :=
  CompatibleRuntimeContextValidity.Valid i.code.compilation.solvedRequirements context i.function.evidence ∧
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context i.function.source

variable
  (i : OrdinaryIndex compiled) (history : History i.code)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (member : ChosenFor (headers := headers) root expressionSyntax owner i history)

variable
  (domains : ∀ context, Validity i context → ∀ childScope,
    DomainAt root expressionSyntax ((i.support).body).readFuel context i.function.evidence childScope headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : ∀ context, Validity i context → RequirementIdsUnique context)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (noIndirect : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirect (source caller.named))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) identities)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((rootReasonAt id).add tag))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : (i.support).issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep (i.support).issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep (i.support).issued.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity i context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (i.support).certificates ((i.support).body).readFuel (i.function).source)
      (administrative := i.captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (i.support).diagnosticPolicy (i.function).source (i.support).issued.invalidOperand)
      (faults := faults) (registry := registry) (i.support).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) table)


variable {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (first : State headers keys ⟨callerScope, i.mapping, i.world, before, store, canonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped i.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes i.function.context before arguments i.support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows first)

/-- The actual stored reference follows from this same owner's positive globals. -/
theorem ChosenFor.reference (member : ChosenFor (headers := headers) root expressionSyntax owner i history) :
    i.captured.canonical[i.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
  rw [member.referenceIndex]
  exact member.globals.reference

namespace ForModel

variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions)
  (functionTypes : FunctionRuntimeViews functions)
  (observationsGeneric : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (interpretsGeneric : ∀ context, Validity i context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (i.support).certificates ((i.support).body).readFuel (i.function).source)
      (administrative := i.captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (i.support).diagnosticPolicy (i.function).source (i.support).issued.invalidOperand)
      (faults := faults) (registry := registry) (i.support).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions table)

include functions members functionTypes profile member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable in
/-- The same positive factory internally supplies the genuine nested Source continuation. -/
theorem source_continuation_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      i.captured i.code history i.support.body.toBody.toContext
      functions owner first budget := by
  obtain ⟨factory, origin, _prefixContext, observed, _referenceIndex, _typed⟩ := member
  cases factory with
  | formed receipt chosen environment captured prefixContext =>
    exact CallableIndexedOwnedChosenNestedLambdaBodyContinuations.ForModel.source_continuation_on
      (functions := functions) (members := members)
      (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen)
      (environment := environment) (profile := profile) (owner := owner) (domains := domains)
      (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (idsUnique := idsUnique)
      (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero)
      (noIndirectOn := noIndirectOn) (extension := extension) (faithful := faithful)
      (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypes)
      (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt)
      (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (interpretsGeneric := interpretsGeneric)
      (captured := captured) (prefixContext := prefixContext) (history := history) (origin := origin)
      (observed := observed) (first := first) (beforeTyped := beforeTyped)
      (argumentsTyped := argumentsTyped) (stable := stable) outer budget within ih

include functions members functionTypes profile member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable in
/-- The same positive factory internally supplies the genuine nested Source continuation. -/
theorem source_continuation (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      i.captured i.code history i.support.body.toBody.toContext
      functions owner first budget := by
  exact source_continuation_on
    (noIndirectOn := fun _allowed found => noIndirect found)
    (functions := functions)
    (members := members)
    (functionTypes := functionTypes)
    (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable outer budget within ih

include functions members functionTypes profile member domains wellFormed sameLayouts complete globals slots prefixZero
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable in
/-- Reflection keeps the independent Source grade of the same literal nested continuation. -/
theorem native_continuation_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      i.captured i.code history i.support.body.toBody.toContext
      functions owner first budget := by
  obtain ⟨factory, origin, _prefixContext, observed, _referenceIndex, _typed⟩ := member
  cases factory with
  | formed receipt chosen environment captured prefixContext =>
    exact CallableIndexedOwnedChosenNestedLambdaBodyContinuations.ForModel.native_continuation_on
      (functions := functions) (members := members)
      (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen)
      (environment := environment) (profile := profile) (owner := owner) (domains := domains)
      (wellFormed := wellFormed) (sameLayouts := sameLayouts)
      (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero)
      (noIndirectOn := noIndirectOn) (extension := extension) (faithful := faithful)
      (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypes)
      (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt)
      (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (interpretsGeneric := interpretsGeneric)
      (captured := captured) (prefixContext := prefixContext) (history := history) (origin := origin)
      (observed := observed) (first := first) (beforeTyped := beforeTyped)
      (argumentsTyped := argumentsTyped) (stable := stable) outer budget within ih

include functions members functionTypes profile member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable in
/-- Reflection keeps the independent Source grade of the same literal nested continuation. -/
theorem native_continuation (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      i.captured i.code history i.support.body.toBody.toContext
      functions owner first budget := by
  exact native_continuation_on
    (noIndirectOn := fun _allowed found => noIndirect found)
    (functions := functions)
    (members := members)
    (functionTypes := functionTypes)
    (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts complete globals slots prefixZero extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable outer budget within ih

/-- The represented result and exact restored caller pool are the original tuple. -/
def InvocationResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt
    (registry := registry) (faults := faults) i.captured i.code
    functions first
    outcome after value finalStore finalMap finalWorld

variable
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      functions)
    i.mapping i.world i.code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions
    i.mapping i.world before store)
  (locals : Dynamic.EnvironmentAgrees before i.function.context.locals i.function.captured)

include functions members functionTypes profile member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- One internally built continuation feeds the original invocation and restoration once. -/
theorem invocation_preserves_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)
        store (i.code.body.rename i.captured.embedding.lift.lift) value finalStore ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  have continuation := source_continuation_on (noIndirectOn := noIndirectOn) (nativeArguments := nativeArguments) (functions := functions) (members := members) (functionTypes := functionTypes) (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric) root expressionSyntax i history profile owner member
    domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero extension faithful
    uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable
    outer budget withinOuter ih
  obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
  exact CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at_with_continuation
    i.captured i.code history i.support.body.toBody.toContext
    functions represented owner first heaps locals
    (member.reference root expressionSyntax) currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed i.code history)
    budget continuation trace within

include functions members functionTypes profile member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- One internally built continuation feeds the original invocation and restoration once. -/
theorem invocation_preserves (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)
        store (i.code.body.rename i.captured.embedding.lift.lift) value finalStore ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  exact invocation_preserves_on
    (noIndirectOn := fun _allowed found => noIndirect found)
    (functions := functions)
    (members := members)
    (functionTypes := functionTypes)
    (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih trace within

include functions members functionTypes profile member domains wellFormed sameLayouts complete globals slots prefixZero
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- Native completion invokes the same continuation and restores the actual caller pool once. -/
theorem invocation_reflects_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)
      store (i.code.body.rename i.captured.embedding.lift.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  have continuation := native_continuation_on (noIndirectOn := noIndirectOn) (arguments := arguments) (functions := functions) (members := members) (functionTypes := functionTypes) (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric) root expressionSyntax i history profile owner member
    domains wellFormed sameLayouts complete globals slots prefixZero extension faithful
    uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable
    outer budget withinOuter ih
  obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
  exact CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at_with_continuation
    i.captured i.code history i.support.body.toBody.toContext
    functions represented owner first heaps locals
    (member.reference root expressionSyntax) currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed i.code history)
    i.support.body.frame budget continuation completed within

include functions members functionTypes profile member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- Native completion invokes the same continuation and restores the actual caller pool once. -/
theorem invocation_reflects (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)
      store (i.code.body.rename i.captured.embedding.lift.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  exact invocation_reflects_on
    (noIndirectOn := fun _allowed found => noIndirect found)
    (functions := functions)
    (members := members)
    (functionTypes := functionTypes)
    (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts complete globals slots prefixZero extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih completed within

include functions members functionTypes profile member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- The genuine payload application edge retains that same invocation tuple. -/
theorem application_preserves_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result⟩ :=
    invocation_preserves_on (noIndirectOn := noIndirectOn) (functions := functions) (members := members) (functionTypes := functionTypes) (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric) root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique
      complete globals slots prefixZero extension faithful uninitialized missing rebuilt
      operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals
      outer budget withinOuter ih trace within
  exact ⟨value, finalStore, finalMap, finalWorld,
    .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result⟩

include functions members functionTypes profile member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- The genuine payload application edge retains that same invocation tuple. -/
theorem application_preserves (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  exact application_preserves_on
    (noIndirectOn := fun _allowed found => noIndirect found)
    (functions := functions)
    (members := members)
    (functionTypes := functionTypes)
    (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih trace within

include functions members functionTypes profile member domains wellFormed sameLayouts complete globals slots prefixZero
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- The real application child keeps its strict native bound and independent Source grade. -/
theorem application_reflects_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact invocation_reflects_on (noIndirectOn := noIndirectOn) (functions := functions) (members := members) (functionTypes := functionTypes) (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric) root expressionSyntax i history profile owner member domains wellFormed sameLayouts
    complete globals slots prefixZero extension faithful uninitialized missing rebuilt
    operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals
    outer budget withinOuter ih applied (Nat.le_trans (Nat.le_of_lt smaller) within)

include functions members functionTypes profile member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- The real application child keeps its strict native bound and independent Source grade. -/
theorem application_reflects (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  exact application_reflects_on
    (noIndirectOn := fun _allowed found => noIndirect found)
    (functions := functions)
    (members := members)
    (functionTypes := functionTypes)
    (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts complete globals slots prefixZero extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih completed within
end ForModel

include member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  beforeTyped argumentsTyped stable in
/-- The same positive factory internally supplies the genuine nested Source continuation. -/
theorem source_continuation_chosen (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner index)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      i.captured i.code history i.support.body.toBody.toContext
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner first budget :=
  ForModel.source_continuation
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (observationsGeneric := observations) (interpretsGeneric := interprets)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable outer budget within ih

include member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  beforeTyped argumentsTyped stable in
/-- Reflection keeps the independent Source grade of the same literal nested continuation. -/
theorem native_continuation_chosen (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner index)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      i.captured i.code history i.support.body.toBody.toContext
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner first budget :=
  ForModel.native_continuation
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (observationsGeneric := observations) (interpretsGeneric := interprets)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable outer budget within ih

/-- The represented result and exact restored caller pool are the original tuple. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt
    (registry := registry) (faults := faults) i.captured i.code
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) first
    outcome after value finalStore finalMap finalWorld

variable
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    i.mapping i.world i.code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    i.mapping i.world before store)
  (locals : Dynamic.EnvironmentAgrees before i.function.context.locals i.function.captured)

include member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  beforeTyped argumentsTyped stable represented heaps locals in
/-- One internally built continuation feeds the original invocation and restoration once. -/
theorem invocation_preserves_chosen (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)
        store (i.code.body.rename i.captured.embedding.lift.lift) value finalStore ∧
      ResultAt (registry := registry) (faults := faults) i profile first outcome after value finalStore finalMap finalWorld :=
  ForModel.invocation_preserves
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (observationsGeneric := observations) (interpretsGeneric := interprets)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih trace within

include member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  beforeTyped argumentsTyped stable represented heaps locals in
/-- Native completion invokes the same continuation and restores the actual caller pool once. -/
theorem invocation_reflects_chosen (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)
      store (i.code.body.rename i.captured.embedding.lift.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) i profile first outcome after value finalStore finalMap finalWorld :=
  ForModel.invocation_reflects
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (observationsGeneric := observations) (interpretsGeneric := interprets)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih completed within

include member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  beforeTyped argumentsTyped stable represented heaps locals in
/-- The genuine payload application edge retains that same invocation tuple. -/
theorem application_preserves_chosen (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) i profile first outcome after value finalStore finalMap finalWorld :=
  ForModel.application_preserves
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (observationsGeneric := observations) (interpretsGeneric := interprets)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih trace within

include member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  beforeTyped argumentsTyped stable represented heaps locals in
/-- The real application child keeps its strict native bound and independent Source grade. -/
theorem application_reflects_chosen (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) i profile first outcome after value finalStore finalMap finalWorld :=
  ForModel.application_reflects
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (observationsGeneric := observations) (interpretsGeneric := interprets)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih completed within
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaInvocation
