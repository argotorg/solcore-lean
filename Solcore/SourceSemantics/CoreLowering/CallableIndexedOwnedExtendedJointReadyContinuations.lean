import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyFamilyInputs

/-! Each actual method-lambda or nested named parameter receipt embeds its
own authentic index into the extended joint family. The original pointwise
continuation proofs consume only that branch's strict body IH and retain the
same actual entries, saved caller writes and independently graded results. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedExtendedJointReadyFamilyInputs

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

/-- The existing measured family supplies this genuine dependent source IH. -/
abbrev PreservingBelow (budget : Nat) : Prop :=
  ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyReadyOrigins.PreservesAt (protocol index) (readiness (bridge index))
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index).facts
        functions (Program.ofChecked compiled.sourceProgram) (origin index))

/-- Native strict body grades retain each branch's independent Source result. -/
abbrev ReflectingBelow (budget : Nat) : Prop :=
  ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol index) (readiness (bridge index))
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index).facts
        functions (Program.ofChecked compiled.sourceProgram) (origin index))

section MethodLambda
variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
  (sourceOrigin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType)

include observed leading sourceOrigin beforeTyped argumentsTyped stable syntaxTree wellFormed in
/-- The original actual Source entry constructs its genuine method-lambda
index and selects that exact extended-family child; no Header is introduced. -/
theorem method_lambda_source_continuation (budget : Nat)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history support.body.toContext functions owner caller (support.body_origin escaped) budget := by
  exact CallableIndexedOwnedMethodLambdaReadyFamilyReceipts.source_continuation
    captured code history support sourceOrigin functions owner observed leading caller escaped
    beforeTyped argumentsTyped stable syntaxTree wellFormed budget
    (fun index => below (.methodLambda index))

include observed leading sourceOrigin beforeTyped argumentsTyped stable syntaxTree wellFormed in
/-- The measured original Prefix constructs its own exact index. The same
continuation returns the actual body pool and independent reflected grade. -/
theorem method_lambda_native_continuation (budget : Nat)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history support.body.toContext functions owner caller (support.body_origin escaped) budget := by
  exact CallableIndexedOwnedMethodLambdaReadyFamilyReceipts.native_continuation
    captured code history support sourceOrigin functions owner observed leading caller escaped
    beforeTyped argumentsTyped stable syntaxTree wellFormed budget
    (fun index => below (.methodLambda index))
end MethodLambda

section NamedNested
variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (prefixZero : owner.key.capturePrefix = 0)
  (globals : header.globals = compiled.indexed.base.globals.length)
  (member : header ∈ headers)
  (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
    (.statements true header.function.body) header.function.resultType)

include functions wellFormed prefixZero globals member syntaxTree in
/-- Actual successful named parameter receipts build the nested index from
real profile/Source admission and preserve their complete seed/bundle packet. -/
theorem named_nested_source_bodies (budget : Nat)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.SourceBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true)
      wellFormed header budget := by
  exact CallableIndexedOwnedNamedNestedReadyFamilyReceipts.source_bodies
    (functions := functions) (owner := owner) (runtime := true)
    wellFormed prefixZero globals member syntaxTree
    (fun index => below (.namedNested index))

include functions wellFormed prefixZero globals member syntaxTree in
/-- The native callback keeps its original measured parameter prefix and
saved caller write, projecting only facets beside the same returned pool. -/
theorem named_nested_native_bodies (budget : Nat)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.NativeBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true)
      wellFormed header budget := by
  exact CallableIndexedOwnedNamedNestedReadyFamilyReceipts.native_bodies
    (functions := functions) (owner := owner) (runtime := true)
    wellFormed prefixZero globals member syntaxTree
    (fun index => below (.namedNested index))
end NamedNested
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyContinuations
