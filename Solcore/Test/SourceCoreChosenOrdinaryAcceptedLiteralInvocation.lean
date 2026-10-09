import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralLambdaInvocationBounds

/-! The accepted fixture validates the actual recaptured entry against its
original lambda occurrence and parameter extension. Runtime invocation ports
retain the same chosen compiler receipt rather than selecting another Site. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralInvocation
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    {lowered : SourceCoreBasic.LoweredExpr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
      fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (expressionId fixture.packet 1) lowered)
    (environment : Dynamic.Environment)

include atHeader in
/-- The same actual Source lookup fixes the recaptured function indices. -/
theorem support_shape :
    (receipt.formation.function environment).parameters = fixture.graph.parameters ∧
    (receipt.formation.function environment).resultType = wordType ∧
    (receipt.formation.function environment).body = [statementId fixture.packet 2] := by
  exact SourceCoreChosenOrdinaryAcceptedLiteralSupport.produced_shape fixture atHeader receipt.formation.produced

include atHeader in
/-- The retained return node belongs to the same recaptured function Source. -/
theorem return_found :
    (receipt.formation.function environment).source.lookupStatement? (statementId fixture.packet 2) =
      some fixture.graph.returned := by
  change (source caller.named).lookupStatement? _ = _
  simpa only [atHeader.named] using fixture.graph.returnedFound

variable (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)

include atHeader shape in
/-- Original monomorphic parameter installation identifies the actual native
entry types, independently of any execution or packed-value inverse. -/
theorem body_types :
    (receipt.formation.support environment).body.types = [parameterType] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq
    (receipt.formation.support environment).body.extended
  rw [(support_shape fixture atHeader receipt environment).1, shape.parameters] at types
  simpa only [List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono] using types.symm

include atHeader shape in
/-- Functional binder extension aligns the actual entry context with the
fixture's genuine parameter context; capture changes only the environment. -/
theorem body_context :
    (receipt.formation.support environment).body.context = shape.bodyContext := by
  have actual := (receipt.formation.support environment).body.extended
  rw [(support_shape fixture atHeader receipt environment).1,
    body_types fixture atHeader receipt environment shape] at actual
  have original : MonoBindersExtend (source caller.named).owner (runtimeContext fixture.packet)
      fixture.graph.parameters [parameterType] shape.bodyContext := by
    simpa only [atHeader.named] using shape.parameters_extend
  exact Dynamic.MonoBindersExtend.functional actual original

include atHeader shape in
/-- The entry retains the actual solved numeric rows, so runtime requirement
validity is derived for this context rather than supplied as a body law. -/
theorem body_runtime :
    RuntimeRequirementLedgerValid (receipt.formation.support environment).body.context := by
  rw [body_context fixture atHeader receipt environment shape]
  exact numeric_runtime_ledger fixture.runtime.rows


variable {rootFuel : Nat}
    (root : CallableIndexedOwnedLiteralReturnSiteShells.LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      rootFuel (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
      lowered)
    (chosen : CallableIndexedOwnedPreparedMixedBodySiteInputs.ChosenFactory root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) receipt)

section Invocation
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    {mapping : LocationMap} {world : StoreTyping} {actualEnvironment : Environment}
    (captured : Captures fixture.packet.compiled.indexed mapping world (initialScope fixture.packet)
      (receipt.formation.function []).captured actualEnvironment)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial fixture.packet.compiled.compatible.checked) caller)
    (history : CallableIndexedLambdaValues.History (receipt.formation.code []))
    (origin : SourceOrigin (receipt.formation.support []) history)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation)
    {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (first : CallableIndexedOwnedFunctionState.State headers keys
      ⟨callerScope, mapping, world, before, store, canonical⟩)
    (beforeTyped : Dynamic.HeapWellTyped (runtimeContext fixture.packet) before)
    (argumentsTyped : Dynamic.ValuesHaveTypes (runtimeContext fixture.packet) before arguments [parameterType])
    (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows first)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      mapping world (receipt.formation.code []).receipt.loweredParameters arguments nativeArguments)
    (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions
      mapping world before store)
    (reference : captured.canonical[(receipt.formation.code []).referenceIndex]? =
      some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))

include atHeader shape chosen origin observed beforeTyped argumentsTyped stable represented heaps reference in
/-- The fixture's actual Source and parameter rows instantiate the original
literal invocation port; capture, history and current pool remain genuine. -/
theorem invocation_preserves (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      callContext callerEvidence (receipt.formation.function []).evidence before
      (.closure (receipt.formation.function [])) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode fixture.packet.compiled.indexed.ancestry.layout.frame history.native :: actualEnvironment)
        store ((receipt.formation.code []).body.rename captured.embedding.lift.lift) value finalStore ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] captured prefixContext)
        (receipt.formation.code []) functions first outcome after value finalStore finalMap finalWorld  := by
  have actualArguments : Dynamic.ValuesHaveTypes (receipt.formation.function []).context
      before arguments (receipt.formation.support []).body.types := by
    rw [body_types fixture atHeader receipt [] shape]
    exact argumentsTyped
  have locals : Dynamic.EnvironmentAgrees before (receipt.formation.function []).context.locals
      (receipt.formation.function []).captured := .nil
  exact CallableIndexedOwnedLiteralLambdaInvocationBounds.invocation_preserves
    (literalRoot := root) (literalId := expressionId fixture.packet 3) (node := fixture.graph.literal)
    (receipt := receipt) (chosen := chosen) (capturedEnvironment := [])
    (facts := SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts.word_facts fixture atHeader)
    (functions := functions) (found := return_found fixture atHeader receipt [])
    (form := fixture.graph.returnedForm) (singleton := (support_shape fixture atHeader receipt []).2.2)
    (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
    (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
    (argumentsTyped := actualArguments) (stable := stable) (represented := represented)
    (heaps := heaps) (locals := locals) (reference := reference) budget trace within

include atHeader shape chosen origin observed beforeTyped argumentsTyped stable represented heaps reference in
/-- The fixture's actual Source and parameter rows instantiate the original
literal invocation port; capture, history and current pool remain genuine. -/
theorem invocation_reflects (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues nativeArguments :: encode fixture.packet.compiled.indexed.ancestry.layout.frame history.native :: actualEnvironment)
        store ((receipt.formation.code []).body.rename captured.embedding.lift.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) sourceSize
        callContext callerEvidence (receipt.formation.function []).evidence before
        (.closure (receipt.formation.function [])) arguments outcome after ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] captured prefixContext)
        (receipt.formation.code []) functions first outcome after value finalStore finalMap finalWorld  := by
  have actualArguments : Dynamic.ValuesHaveTypes (receipt.formation.function []).context
      before arguments (receipt.formation.support []).body.types := by
    rw [body_types fixture atHeader receipt [] shape]
    exact argumentsTyped
  have locals : Dynamic.EnvironmentAgrees before (receipt.formation.function []).context.locals
      (receipt.formation.function []).captured := .nil
  exact CallableIndexedOwnedLiteralLambdaInvocationBounds.invocation_reflects
    (literalRoot := root) (literalId := expressionId fixture.packet 3) (node := fixture.graph.literal)
    (receipt := receipt) (chosen := chosen) (capturedEnvironment := [])
    (facts := SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts.word_facts fixture atHeader)
    (functions := functions) (found := return_found fixture atHeader receipt [])
    (form := fixture.graph.returnedForm) (singleton := (support_shape fixture atHeader receipt []).2.2)
    (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
    (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
    (argumentsTyped := actualArguments) (stable := stable) (represented := represented)
    (heaps := heaps) (locals := locals) (reference := reference) budget completed within

include atHeader shape chosen origin observed beforeTyped argumentsTyped stable represented heaps reference in
/-- The fixture's actual Source and parameter rows instantiate the original
literal invocation port; capture, history and current pool remain genuine. -/
theorem application_preserves (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      callContext callerEvidence (receipt.formation.function []).evidence before
      (.closure (receipt.formation.function [])) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value (receipt.formation.code []) captured.embedding history.native actualEnvironment,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] captured prefixContext)
        (receipt.formation.code []) functions first outcome after value finalStore finalMap finalWorld  := by
  have actualArguments : Dynamic.ValuesHaveTypes (receipt.formation.function []).context
      before arguments (receipt.formation.support []).body.types := by
    rw [body_types fixture atHeader receipt [] shape]
    exact argumentsTyped
  have locals : Dynamic.EnvironmentAgrees before (receipt.formation.function []).context.locals
      (receipt.formation.function []).captured := .nil
  exact CallableIndexedOwnedLiteralLambdaInvocationBounds.application_preserves
    (literalRoot := root) (literalId := expressionId fixture.packet 3) (node := fixture.graph.literal)
    (receipt := receipt) (chosen := chosen) (capturedEnvironment := [])
    (facts := SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts.word_facts fixture atHeader)
    (functions := functions) (found := return_found fixture atHeader receipt [])
    (form := fixture.graph.returnedForm) (singleton := (support_shape fixture atHeader receipt []).2.2)
    (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
    (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
    (argumentsTyped := actualArguments) (stable := stable) (represented := represented)
    (heaps := heaps) (locals := locals) (reference := reference) budget trace within

include atHeader shape chosen origin observed beforeTyped argumentsTyped stable represented heaps reference in
/-- The fixture's actual Source and parameter rows instantiate the original
literal invocation port; capture, history and current pool remain genuine. -/
theorem application_reflects (budget : Nat)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [CallableIndexedLambdaValues.value (receipt.formation.code []) captured.embedding history.native actualEnvironment,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) sourceSize
        callContext callerEvidence (receipt.formation.function []).evidence before
        (.closure (receipt.formation.function [])) arguments outcome after ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] captured prefixContext)
        (receipt.formation.code []) functions first outcome after value finalStore finalMap finalWorld  := by
  have actualArguments : Dynamic.ValuesHaveTypes (receipt.formation.function []).context
      before arguments (receipt.formation.support []).body.types := by
    rw [body_types fixture atHeader receipt [] shape]
    exact argumentsTyped
  have locals : Dynamic.EnvironmentAgrees before (receipt.formation.function []).context.locals
      (receipt.formation.function []).captured := .nil
  exact CallableIndexedOwnedLiteralLambdaInvocationBounds.application_reflects
    (literalRoot := root) (literalId := expressionId fixture.packet 3) (node := fixture.graph.literal)
    (receipt := receipt) (chosen := chosen) (capturedEnvironment := [])
    (facts := SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts.word_facts fixture atHeader)
    (functions := functions) (found := return_found fixture atHeader receipt [])
    (form := fixture.graph.returnedForm) (singleton := (support_shape fixture atHeader receipt []).2.2)
    (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
    (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
    (argumentsTyped := actualArguments) (stable := stable) (represented := represented)
    (heaps := heaps) (locals := locals) (reference := reference) budget completed within

end Invocation
end Tests.SourceCoreChosenOrdinaryAcceptedLiteralInvocation
