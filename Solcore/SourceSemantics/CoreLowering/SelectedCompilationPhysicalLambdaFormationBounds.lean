import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationLambdaAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionExclusion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalLambdaFormationHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNestedCanonicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds

/-! Ordinary lambda formation uses the actual named packet and keeps the
same positive closure member in the public receiving model. The retained
Site and body are static compiler receipts; captures come from this input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalLambdaFormationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open RecursiveNamedLambdaFormationHeads
open CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads (Formation)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry receiving : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (context : SourceSemantics.Context) {stages : Staging.Recursive.Registry}
  (invocation : Staging.Recursive.Scope)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (sameSource : invocation.source = CallableIndexedNamedGeneration.source caller.named)

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "bridge" => CallableIndexedOwnedPhysicalNestedCanonicalState.bridge (headers := headers) owner caller

abbrev Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
    caller context invocation.evidence scope id lowered)

private theorem no_stage
    {program : Program} {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {size : Nat}
    {parameters result body failedScope call reason}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body)
    (coercions : node.coercions = [])
    (trace : Staging.Recursive.Size.Expression program registry size scope context environment
      before id (.fault (.stage failedScope call reason)) after) : False := by
  have actual : ∀ {shape requirements}, Staging.Recursive.Occurrence scope id shape requirements →
      shape = .lambda parameters result body := by
    intro shape requirements occurrence
    obtain ⟨actualNode, contains, sameForm, _requirements, _coercions⟩ := occurrence
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    exact sameForm.symm.trans form
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found coercions contains))
  | group occurrence _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _ | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _
  | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
      cases actual occurrence


variable (unique : NodeOccurrencesUnique invocation.source)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (faults : RecursiveStageMeaning.FaultRep)

include globals slots prefixZero sameSource unique runtime covers in
theorem preserves (size : Nat) :
    PreservesAt bridge context model stages invocation
      (Certificate (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) caller context invocation) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  obtain ⟨receipt⟩ := certified
  let head := receipt.toFormation
  let code := head.code environment
  have sourceFound : invocation.source.lookupExpression? id = some receipt.site.code.sourceNode := by
    simpa only [sameSource, receipt.identifier, CallableIndexedLambdaGeneration.closure] using receipt.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  have changed : outcome = .value (.closure (head.function environment)) ∧ after = before := by
    cases outcome with
    | value value =>
      have evaluated : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
          (head.function environment).context (head.function environment).evidence
          (head.function environment).source (head.function environment).captured before code.id value after := by
        simpa only [sameSource, code, head, Formation.code, Formation.function,
          CallableIndexedLambdaGeneration.closure, recaptureCode, receipt.identifier] using trace.sound.value_plain
      obtain ⟨rfl, rfl⟩ := source_value_of_code (values := .initial compiled.compatible.checked) code
        (by simpa only [head, Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using unique)
        receipt.coercions evaluated
      exact ⟨rfl, rfl⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        apply False.elim
        apply excludes_fault_of_code (values := .initial compiled.compatible.checked) code
          (by simpa only [head, Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using unique)
          receipt.coercions
        simpa only [sameSource, code, head, Formation.code, Formation.function,
          CallableIndexedLambdaGeneration.closure, recaptureCode, receipt.identifier] using trace.sound.semanticFault_plain
      | stage failedScope call reason =>
        exact False.elim (no_stage unique sourceFound receipt.site.code.sourceForm receipt.coercions trace)
  obtain ⟨rfl, rfl⟩ := changed
  obtain ⟨payload, native, represented⟩ := SelectedCompilationPhysicalLambdaFormationHeads.forms caller owner context invocation profile globals slots
    prefixZero receipt environments heaps agrees nativeTyped initial.base.property initial.base.val
  refine ⟨.inRight .word payload, store, mapping, world, native, .value represented,
    heaps, .refl _, .refl _, .refl _ _, .refl _, initial, Relates.refl initial.base.val.val, ?_⟩
  have closureTyped := SelectedCompilationLambdaAdmission.value_typed runtime covers locals
    sourceFound receipt.site.code.sourceForm receipt.coercions typed
  refine ⟨admitted.rows, ?_⟩
  intro value same
  cases same
  refine ⟨?_, admitted.heap⟩
  simpa only [head, Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using closureTyped

include globals slots prefixZero sameSource runtime covers in
theorem reflects (size : Nat) :
    ReflectsAt bridge context model stages invocation
      (Certificate (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) caller context invocation) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  obtain ⟨receipt⟩ := certified
  have sourceFound : invocation.source.lookupExpression? id = some receipt.site.code.sourceNode := by
    simpa only [sameSource, receipt.identifier, CallableIndexedLambdaGeneration.closure] using receipt.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨payload, native, represented⟩ := SelectedCompilationPhysicalLambdaFormationHeads.forms caller owner context invocation profile globals slots
    prefixZero receipt environments heaps agrees nativeTyped initial.base.property initial.base.val
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic native completed.sound
  have sourceTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize []) invocation context environment before id
      (.value (.closure (receipt.toFormation.function environment))) before := by
    apply Staging.Recursive.Size.Expression.atomicValue (lookupExpression?_sound sourceFound)
      (receipt.site.code.sourceForm ▸ Staging.Recursive.AtomicForm.lambda _ _ _) receipt.coercions
    rw [receipt.site.code.sourceForm]
    simpa only [Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource, receipt.coercions] using
      (Dynamic.ExpressionFormEvaluates.lambda (program := Program.ofChecked compiled.sourceProgram)
        (context := context) (evidence := invocation.evidence) (source := invocation.source)
        (environment := environment) (heap := before)
        (parameters := receipt.parameters) (returnType := receipt.result) (body := receipt.statements) receipt.ordinary)
  refine ⟨Staging.Recursive.Size.stepSize [], _, before, mapping, world, sourceTrace, .value represented,
    heaps, .refl _, .refl _, .refl _ _, .refl _, initial, Relates.refl initial.base.val.val, ?_⟩
  have closureTyped := SelectedCompilationLambdaAdmission.value_typed runtime covers locals
    sourceFound receipt.site.code.sourceForm receipt.coercions typed
  refine ⟨admitted.rows, ?_⟩
  intro value same
  cases same
  refine ⟨?_, admitted.heap⟩
  simpa only [ Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using closureTyped

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalLambdaFormationBounds
