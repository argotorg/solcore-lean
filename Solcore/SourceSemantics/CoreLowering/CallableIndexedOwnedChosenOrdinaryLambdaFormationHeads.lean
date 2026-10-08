import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredMembers

/-! Actual formation heads preserve the positive compiler factory in the
receiving model. Original capture and formation producers construct the same
complete tuple once; no inverse on a stored value or finished body law is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedOrdinaryLambdaFormation (Formation)
open RecursiveNamedLambdaFormationHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
    caller.named diagnostics namedCode compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)

/-- A certificate keeps the actual selected compiler receipt and its factory. -/
inductive Certificate : SourceCoreLocalCell.Scope → ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | formed {scope id lowered}
      (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
        context evidence scope id lowered)
      (chosen : CallableIndexedOwnedPreparedMixedBodySiteInputs.ChosenFactory root expressionSyntax receipt) :
      Certificate scope id lowered

/-- This constructor registers only a positively qualified literal closure.
It asks for no classifier of an arbitrary function value or heap cell. -/
def Members (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) : Prop :=
  ∀ (i : CallableIndexedOwnedPreparedRuntimeFamilyMembers.OrdinaryIndex compiled) (history : History i.code),
    CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenAt root expressionSyntax headers keys registry faults i history →
    functions.Represents registry i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)

def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) :=
  CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller

def model (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) :=
  CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : Members (headers := headers) (keys := keys) (registry := registry) (faults := faults) caller root expressionSyntax functions)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {source : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)

include profile members complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Actual catalog/capture receipts construct the whole finite formation leaf.
The actual factory is retained by the local model constructor. -/
theorem preserves_head_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) caller owner)
      (model (registry := registry) functions) context evidence source
      (Certificate caller context evidence root expressionSyntax) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  cases certified with
  | formed receipt chosen =>
    let head := receipt.formation
    let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
      initial.property.observed initial.property.carried initial.property.bundle globals
    let originalCapture := captures_for complete globals entry environments agrees nativeTyped
    let i := CallableIndexedOwnedChosenOrdinaryFormedMembers.index receipt environment originalCapture rfl
    let captured := i.captured
    have observed := capture_globals_for complete globals slots entry environments agrees nativeTyped
    have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
      change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope
        captured.canonical (initial.val.rows owner.position).authority.frameLocation at observed
      rw [(initial.val.rows owner.position).frame_eq] at observed
      exact observed
    let code := i.code
    let support := i.support
    have sourceFound : source.lookupExpression? id = some code.sourceNode := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, recaptureCode,
        CallableIndexedLambdaGeneration.closure, head.produced.identifier] using head.produced.site.code.sourceFound
    have same := Option.some.inj (found.symm.trans sourceFound)
    subst node
    have original : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
        (head.function environment).context (head.function environment).evidence (head.function environment).source
        (head.function environment).captured before code.id outcome after := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, Formation.function,
        CallableIndexedLambdaGeneration.closure, recaptureCode, head.produced.identifier] using trace
    have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context
        code.id code.sourceNode.type := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, Formation.function,
        CallableIndexedLambdaGeneration.closure, recaptureCode, head.produced.identifier] using typed
    obtain ⟨result, finalStore, native, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, post⟩ :=
      CallableIndexedOwnedPreparedOrdinaryLambdaFormation.preserves_at_with_member
        (function := head.function environment) (actual := actual)
        captured code support owner initial.val initial.property profile observed functions
        wellFormed (by simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, Formation.function, CallableIndexedLambdaGeneration.closure] using runtime) covers locals actualTyped head.sourceType
        head.ordinary head.coercions heaps admitted
        (fun nativeTyped =>
          let history : History code := CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at
            captured code support owner initial.val initial.property
          have positive : CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenAt
              root expressionSyntax headers keys registry faults i history := by
            exact .ordinary owner (.formed receipt chosen environment originalCapture rfl)
              (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.source_origin
                captured code support owner initial.val initial.property) rfl observed
              (by
                change code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length
                exact CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reference_index captured code support)
              (by simpa only [i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at, captured, code, head, history, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at] using nativeTyped)
          by simpa only [i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at, captured, code, head, history, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at] using members i history positive) original
    have native : Evaluates actual store (lowered.expression.rename ξ) result finalStore := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, recaptureCode, head.produced.emitted, captured, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index,
        CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at, originalCapture, captures_for] using native
    have represented : GenericExpressionMeaning.ResultRepresents (model (registry := registry) functions)
        mapping world code.sourceNode.type lowered.type faults outcome result := by
      simpa only [head, receipt.formation.produced.emitted, model, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, recaptureCode, head.produced.emitted] using represented
    exact ⟨result, finalStore, mapping, world, native, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩

include profile members complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Actual native formation reflects the original Source leaf with its own
independent grade, preserving the same caller packet and generic heap model. -/
theorem reflects_head_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge (headers := headers) caller owner)
      (model (registry := registry) functions) context evidence source
      (Certificate caller context evidence root expressionSyntax) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  cases certified with
  | formed receipt chosen =>
    let head := receipt.formation
    let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
      initial.property.observed initial.property.carried initial.property.bundle globals
    let originalCapture := captures_for complete globals entry environments agrees nativeTyped
    let i := CallableIndexedOwnedChosenOrdinaryFormedMembers.index receipt environment originalCapture rfl
    let captured := i.captured
    have observed := capture_globals_for complete globals slots entry environments agrees nativeTyped
    have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
      change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope
        captured.canonical (initial.val.rows owner.position).authority.frameLocation at observed
      rw [(initial.val.rows owner.position).frame_eq] at observed
      exact observed
    let code := i.code
    let support := i.support
    have sourceFound : source.lookupExpression? id = some code.sourceNode := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, recaptureCode,
        CallableIndexedLambdaGeneration.closure, head.produced.identifier] using head.produced.site.code.sourceFound
    have same := Option.some.inj (found.symm.trans sourceFound)
    subst node
    have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context
        code.id code.sourceNode.type := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, Formation.function,
        CallableIndexedLambdaGeneration.closure, recaptureCode, head.produced.identifier] using typed
    have actualCompleted : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) value finalStore := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, recaptureCode, head.produced.emitted, captured, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index,
        CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at, originalCapture, captures_for] using completed
    obtain ⟨sourceSize, outcome, after, trace, native, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, post⟩ :=
      CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reflects_at_with_member
        (function := head.function environment) (actual := actual)
        captured code support owner initial.val initial.property profile observed functions
        wellFormed (by simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, Formation.function, CallableIndexedLambdaGeneration.closure] using runtime) covers locals actualTyped head.sourceType
        head.ordinary head.coercions heaps admitted
        (fun nativeTyped =>
          let history : History code := CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at
            captured code support owner initial.val initial.property
          have positive : CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenAt
              root expressionSyntax headers keys registry faults i history := by
            exact .ordinary owner (.formed receipt chosen environment originalCapture rfl)
              (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.source_origin
                captured code support owner initial.val initial.property) rfl observed
              (by
                change code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length
                exact CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reference_index captured code support)
              (by simpa only [i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at, captured, code, head, history, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at] using nativeTyped)
          by simpa only [i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at, captured, code, head, history, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at] using members i history positive) actualCompleted
    have sourceTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after := by
      simpa only [head, receipt.formation.produced.identifier, receipt.formation.produced.emitted, sameSource, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, Formation.function,
        CallableIndexedLambdaGeneration.closure, recaptureCode, head.produced.identifier] using trace
    have represented : GenericExpressionMeaning.ResultRepresents (model (registry := registry) functions)
        mapping world code.sourceNode.type lowered.type faults outcome value := by
      simpa only [head, receipt.formation.produced.emitted, model, code, i, CallableIndexedOwnedChosenOrdinaryFormedMembers.index, Formation.code, recaptureCode, head.produced.emitted] using represented
    exact ⟨sourceSize, outcome, after, mapping, world, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads
