import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedLambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.OrdinaryMethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.AcceptedFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinaryMethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DiscardSequences
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.LambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Coercions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport

/-!
# Selected compilations: prepared closures and method roots

Closure admission, physical lambda formation and method roots of prepared bodies, for the ordinary and branching forms.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedProgramCertificates
/-! Selected execution retains prepared closure bodies. Its finite certificate
uses the widened scoped Source inventory, independently of the legacy uniform
body package, while keeping all original rows and actual issuers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedProgramCertificates
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedProgramAdmission (Selection)

inductive RootCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction) where
  | scoped (source : CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission
      compiled named named.specialized.function.typedBody (statements named.specialized.function.typedBody)
      named.specialized.function.inferredBodyType directRows)
  | formation (source : CallableIndexedOwnedPreparedNamedFactoryAdmission.Certificate compiled named)
  | scopedFactory (source : SelectedCompilationScopedFactorySourceCertificate.Certificate compiled named)
  | excluded (absent : ∀ signature ∈ compiled.sourceProgram.signatures.functions,
      named.specialized.declaration ≠ signature.id)


structure RowCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) where
  root : RootCertificate compiled named directRows
  closures : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate compiled named directRows allowCoerced


structure Certificate (compiled : SourceCoreUnifiedCompilation.Compiled) where
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  selection : Selection compiled table.rows
  rows : ∀ named ∈ compiled.indexed.base.functions,
    Nonempty (RowCertificate compiled named table.rows selection.allowCoerced)
  profile : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedProgramCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingPhysicalLambdaFormationHeads
/-! Ordinary lambda formation uses the actual named packet and keeps the
same positive closure member in the public receiving model. The retained
Site and body are static compiler receipts; captures come from this input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingPhysicalLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open RecursiveNamedLambdaFormationHeads
open PreparedLambdaBodyFormation (Formation)


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
local notation "bridge" => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller

abbrev Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (PreparedLambdaBodyFormation.Formation
    caller context invocation.evidence scope id lowered)

include globals slots prefixZero in
/-- The literal formation copies the captured cells; the formed closure over the
copies is represented in the formed state. -/
theorem forms {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : PreparedLambdaBodyFormation.Formation
      caller context invocation.evidence scope id lowered)
    {mapping world administrative environment canonical actual actualContext before store ξ}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (nativeTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (allSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope canonical)
    (initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨scope, mapping, world, before, store, canonical⟩) :
    ∃ captured after payload finalStore finalMap finalWorld,
      Dynamic.EnvironmentCopies (CallableIndexedNamedGeneration.source caller.named) environment before captured after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word payload) finalStore ∧
      ValueRep compiled.compatible.checked receiving functions finalMap finalWorld
        receipt.produced.site.code.sourceNode.type (.closure (receipt.function captured)) payload lowered.type ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after
        finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  let head := receipt
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
    initial.property.observed initial.property.carried initial.property.bundle globals
  let captured := CallableIndexedOwnedPhysicalLambdaCaptures.captures_for allSlots globals entry environments agrees nativeTyped
  have observed := CallableIndexedOwnedPhysicalLambdaCaptures.capture_globals_for allSlots globals slots entry environments agrees nativeTyped
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical
      (initial.val.rows owner.position).authority.frameLocation at observed
    rw [(initial.val.rows owner.position).frame_eq] at observed
    exact observed
  have capturedSlots := CallableIndexedOwnedPhysicalLambdaCaptures.capture_slots_for allSlots globals entry environments agrees nativeTyped
  let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
  let support : PreparedLambdaBodySupport.Support code := head.support environment
  obtain ⟨formed, _sourceTrace, native, _determined, member⟩ :=
    @PreparedLambdaBodyPhysicalFormation.formation_member compiled headers keys
      bodyRegistry semanticFaults mapping world (head.function environment) scope actual canonical before store
      captured code support owner initial.val initial.property profile rfl observed (receipt.prepared environment)
      capturedSlots ⟨receipt.callerReceipt⟩ _ _ heaps receipt.ordinary receipt.coercions
  have payload := CallableIndexedOwnedPreparedPhysicalCellOrigins.payload_static_member (registry := receiving) profile member
  let actualHistory : History code :=
    @PreparedLambdaBodyPhysicalFormation.history_at compiled headers keys mapping world (head.function environment) scope actual canonical before store
      captured code support owner initial.val initial.property
  refine ⟨formed.captured, formed.finalHeap, value code formed.embedding actualHistory.native formed.closureActual,
    formed.finalStore, formed.finalMap, formed.finalWorld, formed.copy, ?_, ?_, formed.heaps, formed.maps, formed.worlds,
    formed.frame⟩
  · simpa only [code, PreparedLambdaBodyFormation.Formation.code, recaptureCode, head, receipt.produced.emitted, captured, CallableIndexedOwnedPhysicalLambdaCaptures.captures_for, actualHistory] using native
  have sourceType : receipt.produced.site.code.sourceNode.type = FunctionValues.sourceType (head.function environment) := receipt.sourceType
  have nativeType := CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type
    (compiled := compiled) (function := head.function environment) captured code
  rw [sourceType]
  have emittedType : lowered.type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
    simpa only [code, PreparedLambdaBodyFormation.Formation.code, recaptureCode, head, receipt.produced.emitted] using nativeType
  rw [emittedType]
  exact payload

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingPhysicalLambdaFormationHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingPhysicalLambdaFormationBounds
/-! Ordinary lambda formation uses the actual named packet and keeps the
same positive closure member in the public receiving model. The retained
Site and body are static compiler receipts; captures come from this input,
and the formation copies them, so the caller packet is transported to the
formed state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingPhysicalLambdaFormationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open RecursiveNamedLambdaFormationHeads
open PreparedLambdaBodyFormation (Formation)


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
  fun scope id lowered => Nonempty (PreparedLambdaBodyFormation.Formation
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
  | generalizedLocal contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
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
      (Certificate caller context invocation) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  obtain ⟨receipt⟩ := certified
  let head := receipt
  let code := head.code environment
  have sourceFound : invocation.source.lookupExpression? id = some receipt.produced.site.code.sourceNode := by
    simpa only [sameSource, receipt.produced.identifier, CallableIndexedLambdaGeneration.closure] using receipt.produced.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  have changed : ∃ captured, outcome = .value (.closure {head.function environment with captured := captured}) ∧
      Dynamic.EnvironmentCopies (head.function environment).source (head.function environment).captured before captured after := by
    cases outcome with
    | value value =>
      have evaluated : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
          (head.function environment).context (head.function environment).evidence
          (head.function environment).source (head.function environment).captured before code.id value after := by
        simpa only [sameSource, code, head, PreparedLambdaBodyFormation.Formation.code, PreparedLambdaBodyFormation.Formation.function,
          CallableIndexedLambdaGeneration.closure, recaptureCode, receipt.produced.identifier] using trace.sound.value_plain
      obtain ⟨captured, rfl, copy⟩ := source_value_of_code (values := .initial compiled.compatible.checked) code
        (by simpa only [head, PreparedLambdaBodyFormation.Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using unique)
        receipt.coercions evaluated
      exact ⟨captured, rfl, copy⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        apply False.elim
        apply excludes_fault_of_code (values := .initial compiled.compatible.checked) code
          (by simpa only [head, PreparedLambdaBodyFormation.Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using unique)
          receipt.coercions
        simpa only [sameSource, code, head, PreparedLambdaBodyFormation.Formation.code, PreparedLambdaBodyFormation.Formation.function,
          CallableIndexedLambdaGeneration.closure, recaptureCode, receipt.produced.identifier] using trace.sound.semanticFault_plain
      | stage failedScope call reason =>
        exact False.elim (no_stage unique sourceFound receipt.produced.site.code.sourceForm receipt.coercions trace)
  obtain ⟨captured, rfl, copy⟩ := changed
  obtain ⟨formedCaptured, formedHeap, payload, finalStore, finalMap, finalWorld, formedCopy, native, represented,
      finalHeaps, maps, worlds, frame⟩ := SelectedCompilationPreparedBranchingPhysicalLambdaFormationHeads.forms caller owner context invocation profile globals slots
    prefixZero receipt environments heaps agrees nativeTyped initial.base.property initial.base.val
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formedCopy
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedPhysicalNestedCanonicalState.protocol (headers := headers) owner caller)
    (CallableIndexedOwnedPhysicalNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
    initial maps worlds frame copy.metadata_extends
  refine ⟨.inRight .word payload, finalStore, finalMap, finalWorld, native, .value represented,
    finalHeaps, maps, worlds, frame, copy.metadata_extends, reached, related, ?_⟩
  have closureTyped := SelectedCompilationLambdaAdmission.value_typed runtime covers (copy.agrees locals)
    sourceFound receipt.produced.site.code.sourceForm receipt.coercions typed
  refine ⟨CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative ((bridge).pool initial)
    ((bridge).pool reached) admitted.rows frame, ?_⟩
  intro value same
  cases same
  refine ⟨?_, admitted.heap.copy copy⟩
  simpa only [head, PreparedLambdaBodyFormation.Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using closureTyped

include globals slots prefixZero sameSource runtime covers in
theorem reflects (size : Nat) :
    ReflectsAt bridge context model stages invocation
      (Certificate caller context invocation) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  obtain ⟨receipt⟩ := certified
  have sourceFound : invocation.source.lookupExpression? id = some receipt.produced.site.code.sourceNode := by
    simpa only [sameSource, receipt.produced.identifier, CallableIndexedLambdaGeneration.closure] using receipt.produced.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨captured, after, payload, formedStore, finalMap, finalWorld, copy, native, represented, finalHeaps, maps,
      worlds, frame⟩ := SelectedCompilationPreparedBranchingPhysicalLambdaFormationHeads.forms caller owner context invocation profile globals slots
    prefixZero receipt environments heaps agrees nativeTyped initial.base.property initial.base.val
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic native completed.sound
  have sourceTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize []) invocation context environment before id
      (.value (.closure (receipt.function captured))) after := by
    apply Staging.Recursive.Size.Expression.atomicValue (lookupExpression?_sound sourceFound)
      (receipt.produced.site.code.sourceForm ▸ Staging.Recursive.AtomicForm.lambda _ _ _) receipt.coercions
    rw [receipt.produced.site.code.sourceForm]
    simpa only [PreparedLambdaBodyFormation.Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource, receipt.coercions] using
      (Dynamic.ExpressionFormEvaluates.lambda (program := Program.ofChecked compiled.sourceProgram)
        (context := context) (evidence := invocation.evidence) (source := invocation.source)
        (environment := environment) (before := before) (after := after) (captured := captured)
        (parameters := receipt.parameters) (returnType := receipt.result) (body := receipt.statements) receipt.ordinary
        (by rw [sameSource]; exact copy))
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedPhysicalNestedCanonicalState.protocol (headers := headers) owner caller)
    (CallableIndexedOwnedPhysicalNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
    initial maps worlds frame copy.metadata_extends
  refine ⟨Staging.Recursive.Size.stepSize [], _, after, finalMap, finalWorld, sourceTrace, .value represented,
    finalHeaps, maps, worlds, frame, copy.metadata_extends, reached, related, ?_⟩
  have closureTyped := SelectedCompilationLambdaAdmission.value_typed runtime covers (copy.agrees locals)
    sourceFound receipt.produced.site.code.sourceForm receipt.coercions typed
  refine ⟨CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative ((bridge).pool initial)
    ((bridge).pool reached) admitted.rows frame, ?_⟩
  intro value same
  cases same
  refine ⟨?_, admitted.heap.copy copy⟩
  simpa only [ PreparedLambdaBodyFormation.Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using closureTyped

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingPhysicalLambdaFormationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedPhysicalLambdaFormationHeads
/-! Ordinary lambda formation uses the actual named packet and keeps the
same positive closure member in the public receiving model. The retained
Site and body are static compiler receipts; captures come from this input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedPhysicalLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open RecursiveNamedLambdaFormationHeads
open CallableIndexedOwnedPreparedOrdinaryLambdaFormation (Formation)
open PreparedBranchingLambdaFormation (Formation)


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
local notation "bridge" => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller

abbrev Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (PreparedBranchingLambdaFormation.Formation
    caller context invocation.evidence scope id lowered)

include globals slots prefixZero in
/-- The literal formation copies the captured cells; the formed closure over the
copies is represented in the formed state. -/
theorem forms {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : PreparedBranchingLambdaFormation.Formation
      caller context invocation.evidence scope id lowered)
    {mapping world administrative environment canonical actual actualContext before store ξ}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (nativeTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (allSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope canonical)
    (initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨scope, mapping, world, before, store, canonical⟩) :
    ∃ captured after payload finalStore finalMap finalWorld,
      Dynamic.EnvironmentCopies (CallableIndexedNamedGeneration.source caller.named) environment before captured after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word payload) finalStore ∧
      ValueRep compiled.compatible.checked receiving functions finalMap finalWorld
        receipt.produced.site.code.sourceNode.type (.closure (receipt.toFormation.function captured)) payload lowered.type ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after
        finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  let head := receipt.toFormation
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
    initial.property.observed initial.property.carried initial.property.bundle globals
  let captured := CallableIndexedOwnedPhysicalLambdaCaptures.captures_for allSlots globals entry environments agrees nativeTyped
  have observed := CallableIndexedOwnedPhysicalLambdaCaptures.capture_globals_for allSlots globals slots entry environments agrees nativeTyped
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical
      (initial.val.rows owner.position).authority.frameLocation at observed
    rw [(initial.val.rows owner.position).frame_eq] at observed
    exact observed
  have capturedSlots := CallableIndexedOwnedPhysicalLambdaCaptures.capture_slots_for allSlots globals entry environments agrees nativeTyped
  let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
  let support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code := head.support environment
  obtain ⟨formed, _sourceTrace, native, _determined, member⟩ :=
    @CallableIndexedOwnedPreparedPhysicalLambdaFormation.formation_member compiled headers keys
      bodyRegistry semanticFaults mapping world (head.function environment) scope actual canonical before store
      captured code support owner initial.val initial.property profile rfl observed (receipt.toFormation.prepared environment)
      capturedSlots ⟨receipt.callerReceipt⟩ _ _ heaps receipt.ordinary receipt.coercions
  have payload := CallableIndexedOwnedPreparedPhysicalCellOrigins.payload_static_member (registry := receiving) profile member
  let actualHistory : History code :=
    @CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at compiled headers keys (head.function environment) scope mapping world before store actual canonical
      captured code support owner initial.val initial.property
  refine ⟨formed.captured, formed.finalHeap, value code formed.embedding actualHistory.native formed.closureActual,
    formed.finalStore, formed.finalMap, formed.finalWorld, formed.copy, ?_, ?_, formed.heaps, formed.maps, formed.worlds,
    formed.frame⟩
  · simpa only [code, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.code, recaptureCode, head, receipt.produced.emitted, captured, CallableIndexedOwnedPhysicalLambdaCaptures.captures_for, actualHistory] using native
  have sourceType : receipt.produced.site.code.sourceNode.type = FunctionValues.sourceType (head.function environment) := receipt.sourceType
  have nativeType := CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type
    (compiled := compiled) (function := head.function environment) captured code
  rw [sourceType]
  have emittedType : lowered.type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
    simpa only [code, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.code, recaptureCode, head, receipt.produced.emitted] using nativeType
  rw [emittedType]
  exact payload

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedPhysicalLambdaFormationHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedPhysicalLambdaFormationBounds
/-! Ordinary lambda formation uses the actual named packet and keeps the
same positive closure member in the public receiving model. The retained
Site and body are static compiler receipts; captures come from this input,
and the formation copies them, so the caller packet is transported to the
formed state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedPhysicalLambdaFormationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open RecursiveNamedLambdaFormationHeads
open CallableIndexedOwnedPreparedOrdinaryLambdaFormation (Formation)
open PreparedBranchingLambdaFormation (Formation)


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
  fun scope id lowered => Nonempty (PreparedBranchingLambdaFormation.Formation
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
  | generalizedLocal contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
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
      (Certificate caller context invocation) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  obtain ⟨receipt⟩ := certified
  let head := receipt.toFormation
  let code := head.code environment
  have sourceFound : invocation.source.lookupExpression? id = some receipt.produced.site.code.sourceNode := by
    simpa only [sameSource, receipt.produced.identifier, CallableIndexedLambdaGeneration.closure] using receipt.produced.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  have changed : ∃ captured, outcome = .value (.closure {head.function environment with captured := captured}) ∧
      Dynamic.EnvironmentCopies (head.function environment).source (head.function environment).captured before captured after := by
    cases outcome with
    | value value =>
      have evaluated : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
          (head.function environment).context (head.function environment).evidence
          (head.function environment).source (head.function environment).captured before code.id value after := by
        simpa only [sameSource, code, head, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.code, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.function,
          CallableIndexedLambdaGeneration.closure, recaptureCode, receipt.produced.identifier] using trace.sound.value_plain
      obtain ⟨captured, rfl, copy⟩ := source_value_of_code (values := .initial compiled.compatible.checked) code
        (by simpa only [head, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using unique)
        receipt.coercions evaluated
      exact ⟨captured, rfl, copy⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        apply False.elim
        apply excludes_fault_of_code (values := .initial compiled.compatible.checked) code
          (by simpa only [head, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using unique)
          receipt.coercions
        simpa only [sameSource, code, head, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.code, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.function,
          CallableIndexedLambdaGeneration.closure, recaptureCode, receipt.produced.identifier] using trace.sound.semanticFault_plain
      | stage failedScope call reason =>
        exact False.elim (no_stage unique sourceFound receipt.produced.site.code.sourceForm receipt.coercions trace)
  obtain ⟨captured, rfl, copy⟩ := changed
  obtain ⟨formedCaptured, formedHeap, payload, finalStore, finalMap, finalWorld, formedCopy, native, represented,
      finalHeaps, maps, worlds, frame⟩ := SelectedCompilationPreparedPhysicalLambdaFormationHeads.forms caller owner context invocation profile globals slots
    prefixZero receipt environments heaps agrees nativeTyped initial.base.property initial.base.val
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formedCopy
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedPhysicalNestedCanonicalState.protocol (headers := headers) owner caller)
    (CallableIndexedOwnedPhysicalNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
    initial maps worlds frame copy.metadata_extends
  refine ⟨.inRight .word payload, finalStore, finalMap, finalWorld, native, .value represented,
    finalHeaps, maps, worlds, frame, copy.metadata_extends, reached, related, ?_⟩
  have closureTyped := SelectedCompilationLambdaAdmission.value_typed runtime covers (copy.agrees locals)
    sourceFound receipt.produced.site.code.sourceForm receipt.coercions typed
  refine ⟨CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative ((bridge).pool initial)
    ((bridge).pool reached) admitted.rows frame, ?_⟩
  intro value same
  cases same
  refine ⟨?_, admitted.heap.copy copy⟩
  simpa only [head, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using closureTyped

include globals slots prefixZero sameSource runtime covers in
theorem reflects (size : Nat) :
    ReflectsAt bridge context model stages invocation
      (Certificate caller context invocation) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  obtain ⟨receipt⟩ := certified
  have sourceFound : invocation.source.lookupExpression? id = some receipt.produced.site.code.sourceNode := by
    simpa only [sameSource, receipt.produced.identifier, CallableIndexedLambdaGeneration.closure] using receipt.produced.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨captured, after, payload, formedStore, finalMap, finalWorld, copy, native, represented, finalHeaps, maps,
      worlds, frame⟩ := SelectedCompilationPreparedPhysicalLambdaFormationHeads.forms caller owner context invocation profile globals slots
    prefixZero receipt environments heaps agrees nativeTyped initial.base.property initial.base.val
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic native completed.sound
  have sourceTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize []) invocation context environment before id
      (.value (.closure (receipt.toFormation.function captured))) after := by
    apply Staging.Recursive.Size.Expression.atomicValue (lookupExpression?_sound sourceFound)
      (receipt.produced.site.code.sourceForm ▸ Staging.Recursive.AtomicForm.lambda _ _ _) receipt.coercions
    rw [receipt.produced.site.code.sourceForm]
    simpa only [CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource, receipt.coercions] using
      (Dynamic.ExpressionFormEvaluates.lambda (program := Program.ofChecked compiled.sourceProgram)
        (context := context) (evidence := invocation.evidence) (source := invocation.source)
        (environment := environment) (before := before) (after := after) (captured := captured)
        (parameters := receipt.parameters) (returnType := receipt.result) (body := receipt.statements) receipt.ordinary
        (by rw [sameSource]; exact copy))
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedPhysicalNestedCanonicalState.protocol (headers := headers) owner caller)
    (CallableIndexedOwnedPhysicalNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
    initial maps worlds frame copy.metadata_extends
  refine ⟨Staging.Recursive.Size.stepSize [], _, after, finalMap, finalWorld, sourceTrace, .value represented,
    finalHeaps, maps, worlds, frame, copy.metadata_extends, reached, related, ?_⟩
  have closureTyped := SelectedCompilationLambdaAdmission.value_typed runtime covers (copy.agrees locals)
    sourceFound receipt.produced.site.code.sourceForm receipt.coercions typed
  refine ⟨CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative ((bridge).pool initial)
    ((bridge).pool reached) admitted.rows frame, ?_⟩
  intro value same
  cases same
  refine ⟨?_, admitted.heap.copy copy⟩
  simpa only [ CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using closureTyped

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedPhysicalLambdaFormationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingMethodScopedRoots
/-! Each actual ordinary lexical callback keeps its original Source context,
physical scope and retained Code. General expression certificates are recovered
from the real view compiler; finite direct/index authority stays static. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingMethodScopedRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax Certificate)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles
open CallableIndexedOwnedPreparedStagedOrdinaryMethodPolicy
open CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open SelectedCompilationRootStaticSupport
open SelectedCompilationMixedRootSupport (Root)

section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (support : PreparedLambdaBodySupport.Support code)
  (provenance : PreparedLambdaBodySupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (metadata : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

include receiver bodies certified supported metadata rows covered checked catalog methods signatureMember sourceOwner provenance callerReceipt in
/-- The actual binder fields transport typing, ledger and evidence. The root
retains the concrete Code compiler, including its original prefix and reasons. -/
theorem of_original_child_with_catalog
    {child : Staging.Recursive.Scope} (selected : (stages).Closure function child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields support.body.context context)
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    (tree : GeneralSyntax function.source id directSites)
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation function.source current id code.reasonAt = .ok lowered) :
    Nonempty (Σ rawType, Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered rawType faults) := by
  have sameSource := (stages).source selected
  have unique : NodeOccurrencesUnique child.source := sameSource ▸ support.unique
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      compiled.indexed.base.callableContext [] := by rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  have originalProfile := retained_policy_for provenance.policy_recipe metadata callables supported current code.reasonAt
  have profile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodStepPolicyFor
      code.policy code.compilation compiled.indexed.fuel (.initial compiled.compatible.checked)
      child.source current code.reasonAt directSites := by simpa only [sameSource] using originalProfile
  have coercions : ∀ id actualNode, GeneralSyntax child.source id directSites →
      child.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sameSource] using syntaxTree)
      actualNode (by simpa only [sameSource] using actualFound)
  have childTree : GeneralSyntax child.source id directSites := by simpa only [sameSource] using tree
  have childFound : child.source.lookupExpression? id = some node := by simpa only [sameSource] using found
  have childTyped : ExpressionHasType child.source context id node.type := by simpa only [sameSource] using typed
  have childDeclarations : CompatibleExpressionReads.ScopeDeclarations child.source current context := by
    simpa only [sameSource] using declarations
  have compiledChild : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation child.source current id code.reasonAt = .ok lowered := by
    simpa only [sameSource] using accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable code.active code.callables
    unique childDeclarations profile coercions childTree childFound childTyped compiledChild
  have atOwner : SelectedCompilationOrdinaryAnnotationCoherence.AtOwner compiled.sourceProgram function.source.owner := by
    let caller := callerReceipt.extend (Dynamic.MonoBindersExtend.runtimeContextFields support.body.extended)
    rw [support.source]
    exact SelectedCompilationOrdinaryAnnotationCoherence.at_prepared bodies caller.prepared
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) certificate :=
    SelectedCompilationOrdinaryEvidenceCallsReady.calls_ready stagePrepared
      code (fun id tree => retained_read_policy provenance.policy_recipe metadata tree) support.source_receipt support.unique
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) bodies atOwner signatureMember sourceOwner
      selected childTyped certificate childTree
  have directReady : ∀ {callFuel callScope callId callee ids instantiation callCode}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        code.policy code.lowerBody callFuel code.compilation
        (.initial compiled.compatible.checked) child.source callScope callId callee ids
        instantiation code.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler certificate →
      Nonempty {port : CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler
        headers context child.evidence // SelectedCompilationNamedSourceTyping.Certified port.header ∧
          SelectedCompilationSourceSignatureFacts.Shape port.header} := by
    intro callFuel callScope callId callee ids instantiation callCode compiler path
    have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path childTree
    have site := actualTree.direct_site compiler.metadata.found compiler.form
    obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory_at compiler rows
      (covered instantiation site compiler.index compiler.signature compiler.target compiler.global)
      (by rw [support.compilation]; rfl)
    have childMetadata : MetadataFor compiled.indexed support.caller.named child.source directSites := by
      simpa only [sameSource] using metadata
    rcases retained_accepted_direct_action provenance.policy_recipe childMetadata actualTree
      compiler.metadata.found compiler.form compiler.accepted with bypass | authentic
    · obtain ⟨requirements, assumptions⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct
          compiler.metadata.found compiler.form bypass
      have special := fun callback budget =>
        (retained_direct_hook provenance.policy_recipe childMetadata actualTree
          compiler.metadata.found compiler.form callback budget callScope code.reasonAt).trans
          (CallableCallEvidenceCertificates.direct_bypass compiler.metadata.found compiler.form requirements
            compiler.metadata.coercions assumptions)
      have ordinary := compiler.ordinary special
        (retained_read_policy provenance.policy_recipe childMetadata actualTree)
      exact ⟨⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
        compiler port ordinary requirements context child.evidence⟩,
        SelectedCompilationCatalog.certificates bodies rows port.header port.member,
        SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member⟩⟩
    · obtain ⟨action⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
        compiler.metadata.found compiler.form authentic
      rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at action
      let originalCaller := callerReceipt.extend (Dynamic.MonoBindersExtend.runtimeContextFields support.body.extended)
      let caller := (originalCaller.extend fields).with_evidence ((stages).evidence selected)
      have parameters := RecursiveNamedInitialContextValidity.mono_fields support.caller.extended
      have signatures : context.signatures = compiled.sourceProgram.signatures := by
        rw [caller.fields.signatures, parameters.signatures, caller.aligned.function]
        rfl
      have ledger : context.solvedRequirements = support.caller.named.specialized.function.solvedRequirements :=
        caller.fields.solvedRequirements.trans (support.caller.valid.ledger.trans
          (caller.aligned.solved.trans (congrArg (fun named => named.specialized.function.solvedRequirements)
            caller.aligned.named.symm)))
      have assumptions : ∀ goal, goal ∈ support.caller.named.specialized.assumptions → goal ∈ context.assumptions := by
        intro goal member
        rw [caller.fields.assumptions, parameters.assumptions, caller.aligned.function]
        change goal ∈ caller.prepared.named.specialized.assumptions
        rw [← caller.aligned.named]
        exact member
      have idsUnique : RequirementIdsUnique context := by
        simpa only [RequirementIdsUnique, caller.fields.solvedRequirements] using
          (SelectedCompilationHeaderFacts.scoped_ledger certified).idsUnique
      exact ⟨⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence
        compiler port action caller.prepared signatures ledger assumptions idsUnique caller.dictionary⟩,
        SelectedCompilationCatalog.certificates bodies rows port.header port.member,
        SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member⟩⟩
  have methodReady : ∀ {callFuel callScope callId callCode}
      (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        code.policy code.lowerBody callFuel code.compilation (.initial compiled.compatible.checked)
        child.source callScope callId code.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodCalls compiler certificate →
      Nonempty {port : CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
        compiler context child.evidence stages //
        Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context child.evidence
          port.principal.traitName port.principal.methodName compiler.node.requirements
          port.principal.sourceBody port.principal.dictionary} := by
    intro callFuel callScope callId callCode compiler path
    have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.method_calls_syntax_of path childTree
    have childMetadata : MetadataFor compiled.indexed support.caller.named child.source directSites := by
      simpa only [sameSource] using metadata
    have form : (∃ operator operand, compiler.node.form = .unary operator operand) ∨
        (∃ operator left right, compiler.node.form = .binary left operator right) := by
      rcases compiler.operator.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
      · exact .inl ⟨operator, operand, form⟩
      · exact .inr ⟨operator, left, right, form⟩
    have hook := retained_operator_hook provenance.policy_recipe childMetadata actualTree compiler.metadata.found form
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child code.policy code.lowerBody callFuel code.compilation)
      (callFuel + 1) callScope code.reasonAt
    have acceptedMethod := hook.symm.trans compiler.special
    have nonempty : compiler.node.requirements ≠ [] := by
      intro empty
      exact compiler.operator.nonempty ((CallableIndexedOwnedPreparedStagedMethodArgumentRows.requirements compiler).trans empty)
    obtain ⟨actual⟩ := CallablePreparedMethodSelection.of_accepted compiler.metadata.found form
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.ordinary_requirements compiler.metadata.coercions)
      nonempty acceptedMethod
    rw [← callables] at actual
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at actual
    obtain ⟨sourceReceipt⟩ := CallablePreparedMethodRuntimeMeaning.OperatorSource.of_accepted actual
    let originalCaller := callerReceipt.extend (Dynamic.MonoBindersExtend.runtimeContextFields support.body.extended)
    let caller := (originalCaller.extend fields).with_evidence ((stages).evidence selected)
    have parameters := RecursiveNamedInitialContextValidity.mono_fields support.caller.extended
    have signatures : context.signatures = compiled.sourceProgram.signatures := by
      rw [caller.fields.signatures, parameters.signatures, caller.aligned.function]
      rfl
    have ledger : context.solvedRequirements = support.caller.named.specialized.function.solvedRequirements :=
      caller.fields.solvedRequirements.trans (support.caller.valid.ledger.trans
        (caller.aligned.solved.trans (congrArg (fun named => named.specialized.function.solvedRequirements)
          caller.aligned.named.symm)))
    have assumptions : ∀ goal, goal ∈ support.caller.named.specialized.assumptions → goal ∈ context.assumptions := by
      intro goal member
      rw [caller.fields.assumptions, parameters.assumptions, caller.aligned.function]
      change goal ∈ caller.prepared.named.specialized.assumptions
      rw [← caller.aligned.named]
      exact member
    have idsUnique : RequirementIdsUnique context := by
      simpa only [RequirementIdsUnique, caller.fields.solvedRequirements] using
        (SelectedCompilationHeaderFacts.scoped_ledger certified).idsUnique
    have parentTyped := CallableIndexedOwnedPreparedStagedMethodPathTyping.parent_typed compiler unique childTyped path
    have callerMember := (CallableNamedMetadata.specialization_of_exact
      (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)).1
    have sourceEq : child.source = support.caller.named.specialized.function.typedBody :=
      sameSource.trans support.source
    have nodeMember : .expression compiler.node ∈ support.caller.named.specialized.function.typedBody.nodes := by
      have found : support.caller.named.specialized.function.typedBody.lookupExpression? callId = some compiler.node :=
        by simpa only [sourceEq] using compiler.metadata.found
      exact (lookupExpression?_sound found).1
    have dictionary : child.evidence = CallableNamedMetadata.environment actual.available := by
      have same := Except.ok.inj (actual.resolved.symm.trans caller.prepared.resolved)
      rw [caller.dictionary, same]
      rfl
    exact SelectedCompilationMethodSelectionIssuer.of_actual compiler actual compiler.special
      sourceReceipt methods checked bodies catalog
      (by rw [support.compilation]; exact SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
      (by rw [support.compilation]; exact callerMember) nodeMember
      (by rw [support.compilation]; rfl) (by rw [support.compilation]; rfl)
      signatures ledger assumptions idsUnique dictionary unique parentTyped stagePrepared
  let root : RootData compiled code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered node.type faults := {
    compilerFuel := fuel
    accepted := compiledChild
    certificate := certificate
    node := node
    found := childFound
    rawResult := rfl
    typed := childTyped
    sameLedger := fields.solvedRequirements.trans support.body.valid.ledger
    runtimeLedger := fields.runtimeRequirementLedger support.body.valid.runtime
    unique := unique
    catalog := bodies.signatures
    runtime := by
      rw [sameSource]
      exact ((CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
        support.body.frame support.body.toContext.extended).1).transport fields
    covers := by rw [(stages).evidence selected]; exact fields.covers support.body.valid.covers
    actualFunctionType := by rw [code.callables]; rfl
    uninitialized := by
      intro current readId lowered receipt childReached location
      have originalReached : Reaches function.source [.expression id] (.expression readId) := by
        simpa only [sameSource] using childReached
      exact CallableIndexedOwnedContextualLambdaReadDiagnostics.prepared_branching_uninitialized support provenance.body_reasons
        receiver (reached.from_root originalReached) (by simpa only [sameSource] using receipt) location
    callsReady := ready }
  exact ⟨⟨node.type, ⟨root, directReady,
    CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.prepared_branching_ready support provenance.body_reasons
      sameSource reached certificate, methodReady⟩⟩⟩

include receiver bodies certified supported metadata rows covered checked catalog methods signatureMember sourceOwner provenance callerReceipt in
/-- The real body-view callback supplies a root for the original Source at its
actual lexical context, using the unchanged compiler and retained dictionary. -/
theorem of_child_with_catalog
    {child : Staging.Recursive.Scope} (selected : (stages).Closure function child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields support.body.context context)
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    (tree : GeneralSyntax function.source id directSites)
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation code.view current id code.reasonAt = .ok lowered) :
    Nonempty (Σ rawType, Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered rawType faults) := by
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      compiled.indexed.base.callableContext [] := by
    rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  exact of_original_child_with_catalog stagePrepared code support provenance callerReceipt receiver bodies certified supported metadata
    rows covered checked catalog methods signatureMember sourceOwner selected fields declarations tree reached found typed
    (CallableIndexedOwnedPreparedStagedMethodBodyViewTransport.accepted_original
      code provenance.policy_recipe provenance.body_view callables metadata tree reached accepted)

end Generic
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingMethodScopedRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingMethodTerminalSupport
/-! The genuine retained ordinary terminal body supplies each selected mixed
root with its complete caller dictionary and actual method selection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingMethodTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (Terminal)
open SelectedCompilationPhysicalClosureStaticSupport (SelectedBody)
section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (support : PreparedLambdaBodySupport.Support code)
  (provenance : PreparedLambdaBodySupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (metadata : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows


include receiver bodies certified supported metadata rows covered checked catalog methods signatureMember sourceOwner provenance callerReceipt in
/-- The accepted terminal callback yields the original method-aware expression
root at every genuine selected Source scope. -/
theorem of_actual_with_catalog
    (expression : ExpressionId)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source expression function.body)
    (tree : GeneralSyntax function.source expression directSites)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : Terminal code stages,
      SelectedBody («headers» := headers) code support.body.toContext stages packet faults) := by
  obtain ⟨packet, expressionEq, callback, reason, _child, point, prefixEq⟩ :=
    SelectedCompilationPreparedBranchingTerminalChoice.of_actual code support provenance
      expression terminal child selected
  refine ⟨⟨packet, { point := point, readFuel := compiled.indexed.fuel, «prefix» := prefixEq, roots := ?_ }⟩⟩
  intro selectedChild selectedAt
  apply Classical.choice
  have sameSource := (stages).source selectedAt
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code support.body.toContext support.body.frame
    provenance.scope_declarations selectedAt
  obtain ⟨node, found, rawType, typed⟩ :=
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type
      code packet support.body.toContext support.body.frame selectedChild selectedAt
  have accepted := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.accepted_view_action code packet callback reason
  obtain ⟨⟨actualType, root⟩⟩ :=
    SelectedCompilationPreparedBranchingMethodScopedRoots.of_child_with_catalog stagePrepared code support provenance callerReceipt
      receiver bodies certified supported metadata rows covered checked catalog methods signatureMember sourceOwner
      selectedAt (Dynamic.RuntimeContextFields.refl _)
      (by simpa only [sameSource] using declarations)
      (expressionEq.symm ▸ tree)
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet)
      (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed) accepted
  have sameNode := Option.some.inj (root.found.symm.trans found)
  have resultEq : actualType = function.resultType := root.rawResult.symm.trans (sameNode ▸ rawType)
  exact ⟨resultEq ▸ root⟩

end Generic
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingMethodTerminalSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingClosureAdmission
/-! Finite original-source lambda checks cover ordinary terminal roots and the
existing constrained coerced terminal roots. Catalog capability controls the
coerced branch; original bodies and metadata are retained in both branches. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedClosureAdmission (OrdinaryBodyCertificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : PreparedLambdaBodySupport.Support code)
  (provenance : PreparedLambdaBodySupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)

include stagePrepared code support provenance callerReceipt receiver bodies rows aligned checked catalog methods callerReceipt in
theorem of_ordinary
    (certificate : OrdinaryBodyCertificate compiled support.caller.named directRows function.body) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SelectedCompilationPhysicalClosureStaticSupport.SelectedBody (headers := headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have certified := SelectedCompilationOrdinaryClosureFacts.certified bodies callerReceipt
  have supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation := by
    intro instantiation site
    rw [support.compilation]
    exact site.supported aligned
  have covered : ∀ instantiation, DirectSite directRows instantiation → ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro instantiation site index signature target global
    rw [support.compilation] at target global
    exact site.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  exact SelectedCompilationPreparedBranchingMethodTerminalSupport.of_actual_with_catalog
    stagePrepared code support provenance callerReceipt receiver bodies certified supported
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows covered checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    certificate.expression
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.terminal)
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.tree)
    _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingClosureAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingMethodScopedSupport
/-! General expressions at actual ordinary lexical scopes retain the same
Code compiler and genuine canonical-root authorities. Existing branching
collector/flow trees handle local allocation, assignment and finite control. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingMethodScopedSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability CallableLambdaViewEdits
open SelectedCompilationMixedRootSupport (Root)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private theorem accepted_child
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
    {stages : Staging.Recursive.Registry}
    (choice : CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts.Choice code (stages := stages))
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : choice.packet.policy.lowerExpression fuel code.view current id choice.packet.reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody (min fuel code.fuel)
      code.compilation code.view current id code.reasonAt = .ok lowered := by
  have callback := choice.callback
  have reason := choice.reason
  rw [callback, reason] at accepted
  exact accepted


section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : PreparedLambdaBodySupport.Support code)
  (provenance : PreparedLambdaBodySupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (original : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

variable (choice : Choice code
  («stages» := RecursiveNamedPreparedStageScopes.registry stagePrepared))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include provenance callerReceipt receiver bodies certified supported original rows covered checked catalog methods signatureMember sourceOwner in
/-- Every original expression is issued at its real lexical context, including the
RHS and later reads after a genuine assignment or local allocation. -/
def support_general_with_catalog
    (choiceIssued : choice.Issued code support.caller.named)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType) :
    SelectedCompilationPhysicalBranchingClosureStaticSupport.SelectedBody
      headers code support.body.toContext stages choice.packet faults := by
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
    support.body.frame support.body.extended).1
  have sourceSignatures : support.body.context.signatures = compiled.compatible.checked.signatures :=
    (runtime.signatures.trans
      (RecursiveNamedSelectedExpressionFactory.header_program_signatures
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) support.caller).symm).trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := support.caller))
  have ownership : LocalIdentityOwnership function.source := by
    obtain ⟨_, certificate⟩ := certified
    rw [support.source]
    change LocalIdentityOwnership support.caller.named.specialized.function.typedBody
    rw [← support.caller.agreement.source, support.caller.frame.source]
    exact certificate.local_identity_ownership
  refine ⟨support.body.frame, support.body.projection, compiled.indexed.fuel, ?_,
    choice.invalidProjection, choice.missingDefault,
    choiceIssued.assignmentAuthority code support.caller.selected support.source support.body.unique, ?_⟩
  · rw [support.compilation]; rfl
  intro child selected
  have actual := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport.collected
    code support.body.toContext support.body.frame choice provenance.body_view provenance.scope_declarations
    sourceSignatures (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    (by rw [CallableIndexedOwnedPublicSignatureCatalog.signatures compiled]; exact bodies.signatures)
    support.body.valid.ledger support.body.projection
    (fun origin rawProfile => choiceIssued.operands code support.caller.selected support.source receiver origin rawProfile)
    (fun origin rawWord => choiceIssued.unary code support.caller.selected support.source receiver origin rawWord) syntaxTree
    (certificates := fun context scope id lowered => Nonempty (Σ rawType,
      Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
        context child code.reasonAt scope id lowered rawType faults))
    (fun context fields current fuel id node lowered declarations tree reached found typed accepted _nativeType _native => by
      exact SelectedCompilationPreparedBranchingMethodScopedRoots.of_child_with_catalog
        stagePrepared code support provenance callerReceipt receiver bodies certified supported original rows covered checked catalog methods signatureMember sourceOwner
        selected fields declarations tree reached found typed (accepted_child code choice accepted))
  have weakened := CallableLambdaViewMatchRuntimeCertificates.transport_with
    (LocalView.refl function.source) (by intro id member; cases member)
    support.body.unique (fun _ _ _ => True.intro)
    (fun _ _ _ _ _ value => value) actual.tree
    (fun id member => Reaches.root (List.mem_map.mpr ⟨id, member, rfl⟩))
  rw [(stages).source selected]
  refine ⟨weakened, ?_⟩
  intro currentRegistry
  obtain ⟨tree, sites⟩ := PreparedBranchingCatalogTransport.weaken support.body.unique
    (actual.sites currentRegistry)
  exact sites

include provenance callerReceipt receiver bodies certified supported original rows covered checked catalog methods signatureMember sourceOwner in
omit choice in
/-- The real lowerer and typed original syntax produce the same-model packet
and all static support together, without selecting a proof as runtime data. -/
theorem of_actual_with_catalog
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code stages,
      SelectedCompilationPhysicalBranchingClosureStaticSupport.SelectedBody
        headers code support.body.toContext stages packet faults) := by
  obtain ⟨choice, choiceIssued⟩ := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts.choose_issued
    code support.caller.named provenance.issued_recipe support.compilation shape child selected
  exact ⟨⟨choice.packet,
    support_general_with_catalog stagePrepared code support provenance callerReceipt receiver bodies certified supported original rows covered checked catalog methods
      signatureMember sourceOwner choice choiceIssued syntaxTree⟩⟩

end Generic
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingMethodScopedSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingScopedClosureAdmission
/-! Compiler-derived scoped body certificates use the existing branching closure
collector at the original Source frame and exact current parameter context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingScopedClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedScopedClosureAdmission (SourceBodyCertificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : PreparedLambdaBodySupport.Support code)
  (provenance : PreparedLambdaBodySupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)

include stagePrepared code support provenance callerReceipt receiver bodies rows aligned checked catalog methods callerReceipt in
theorem of_actual
    (certificate : SourceBodyCertificate compiled support.caller.named directRows function.body) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SelectedCompilationPhysicalBranchingClosureStaticSupport.SelectedBody (headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have certified := SelectedCompilationOrdinaryClosureFacts.certified bodies callerReceipt
  have supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation := by
    intro instantiation site
    rw [support.compilation]
    exact site.supported aligned
  have covered : ∀ instantiation, DirectSite directRows instantiation → ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro instantiation site index signature target global
    rw [support.compilation] at target global
    exact site.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  obtain ⟨finalContext, facts, typed, completed⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters support.body.frame support.body.extended
  have scan : ScopedSourceBodyAdmission.Scan function.source
      (fun id => GeneralSyntax function.source id (DirectSite directRows)) certificate.result true function.body := by
    simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.scan
  have result : function.resultType = certificate.result :=
    scan.result_eq_of_completes support.body.unique typed completed
  have syntaxTree := scan.syntax support.body.unique result typed
  rw [← result] at syntaxTree
  exact SelectedCompilationPreparedBranchingMethodScopedSupport.of_actual_with_catalog
    stagePrepared code support provenance callerReceipt receiver bodies certified supported
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows covered checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    scan.shape syntaxTree
    _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingScopedClosureAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedDirectRoots
/-! Original direct output coercions retain the real caller, ordered argument
compiler actions, and selected conversion packets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedDirectRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor)
open SelectedCompilationMixedRootSupport (Root CoercedDirectRoot CoercionMethods)

private theorem arguments_typed {source : TypedSource} {context : SourceSemantics.Context}
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (typed : ExpressionHasType source context id node.type) :
    ∃ types, ExpressionsHaveTypes source context ids types := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | intro contains raw _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst_vars
    rw [form] at raw
    cases raw with
    | directCall _ _ arguments => exact ⟨_, arguments⟩

private theorem output_path {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type) :
    CoercionPathValid context node.rawType node.type node.coercions := by
  obtain ⟨actual, rawType, contains, result, raw, _admissible, path⟩ := typed.raw_type_and_output_path
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst actual
  simpa only [← raw] using path

private theorem argument_tree {source : TypedSource} {context : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (compile : ExpressionId → Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr)
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (accepted : ids.mapM compile = .ok codes)
    (extract : ∀ id ∈ ids, ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type → compile id = .ok code → certificate scope id code) :
    ∃ actualTypes, DataExpressionSequence.Tree source certificate scope ids actualTypes codes := by
  induction ids generalizing types codes with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst codes
    exact ⟨[], .nil⟩
  | cons id ids ih =>
    cases typed with
    | cons head tail =>
      cases first : compile id with
      | error error => simp [List.mapM_cons, first, bind, Except.bind] at accepted
      | ok code =>
        cases rest : ids.mapM compile with
        | error error => simp [List.mapM_cons, first, rest, bind, Except.bind] at accepted
        | ok restCodes =>
          simp only [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
          subst codes
          obtain ⟨node, contains, typeEq⟩ := head.stored_type
          have found := lookupExpression?_complete unique contains
          have child := extract id (by simp) node code found (typeEq ▸ head) first
          obtain ⟨tailTypes, tailTree⟩ := ih tail rest (fun id member => extract id (by simp [member]))
          cases tailTree with
          | nil => exact ⟨_, .single found child⟩
          | single nextFound nextChild => exact ⟨_, .cons found child (.single nextFound nextChild)⟩
          | cons nextFound nextChild tailTree => exact ⟨_, .cons found child (.cons nextFound nextChild tailTree)⟩

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (support : PreparedLambdaBodySupport.Support code)
  (provenance : PreparedLambdaBodySupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (metadata : NativeMetadataFor compiled.indexed support.caller.named function.source (fun _ => False))
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
  {signature : ProgramFunctionSignature} (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows


include receiver bodies certified metadata rows checked catalog methods signatureMember sourceOwner provenance callerReceipt in
theorem of_original_child
    (methodBodies : ∀ {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (_diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    (_certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt),
    ∃ packet : SelectedCompilationMethodBodySupport.Packet principal,
      packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodySupport.Support
        principal packet (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))

    {child : Staging.Recursive.Scope} (selected : (stages).Closure function child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields support.body.context context)
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    (children : ∀ argument ∈ ids, GeneralSyntax function.source argument (fun _ => False))
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (nonempty : node.coercions ≠ []) (requirements : node.requirements ≠ [])
    (noInitializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed support.caller.named).owner ∧
        binding.initializer = id)) = none)
    (supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
    (covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers, header.slot = index ∧ header.named.signature = signature)
    (typed : ExpressionHasType function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody (fuel+1)
      code.compilation function.source current id code.reasonAt = .ok lowered) :
    Nonempty (CoercedDirectRoot compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered node.type faults) := by
  have sameSource := (stages).source selected
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      compiled.indexed.base.callableContext [] := by
    rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  have authentic : SourceCoreEvidence.lowerWithProjector compiled.sourceProgram
      ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext support.caller.named.signature.key []).expressions.projectType
      support.caller.named.specialized code.compilation
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child code.policy code.lowerBody fuel code.compilation)
      (fuel+1) child.source current id code.reasonAt code.policy.callables = .ok (some lowered) := by
    obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, sameCompilation⟩ := provenance.policy_recipe
    rw [sameCompilation] at accepted ⊢
    rw [sameSource, callables]
    rcases CallableIndexedOwnedPreparedStagedCoercedBodyViewTransport.accepted_direct_action
      recipe noInitializer found form accepted with bypass | actual
    · exact False.elim (requirements (CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct found form bypass).1)
    · simpa only [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] using actual
  have childFound : child.source.lookupExpression? id = some node := by simpa only [sameSource] using found
  obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted childFound form authentic
  let originalCaller := callerReceipt.extend (Dynamic.MonoBindersExtend.runtimeContextFields support.body.extended)
  let caller := (originalCaller.extend fields).with_evidence ((stages).evidence selected)
  have parameters := RecursiveNamedInitialContextValidity.mono_fields support.caller.extended
  have signatures : context.signatures = compiled.sourceProgram.signatures := by
    rw [caller.fields.signatures, parameters.signatures, caller.aligned.function]
    rfl
  have ledger : context.solvedRequirements = support.caller.named.specialized.function.solvedRequirements :=
    caller.fields.solvedRequirements.trans (support.caller.valid.ledger.trans
      (caller.aligned.solved.trans (congrArg (fun named => named.specialized.function.solvedRequirements) caller.aligned.named.symm)))
  have assumptions : ∀ goal, goal ∈ support.caller.named.specialized.assumptions → goal ∈ context.assumptions := by
    intro goal member
    rw [caller.fields.assumptions, parameters.assumptions, caller.aligned.function]
    change goal ∈ caller.prepared.named.specialized.assumptions
    rw [← caller.aligned.named]
    exact member
  have idsUnique : RequirementIdsUnique context := by
    simpa only [RequirementIdsUnique, caller.fields.solvedRequirements] using
      (SelectedCompilationHeaderFacts.scoped_ledger certified).idsUnique
  have dictionary : child.evidence = CallableNamedMetadata.environment actual.available := by
    have same := Except.ok.inj (actual.resolved.symm.trans caller.prepared.resolved)
    rw [caller.dictionary, same]
    rfl
  obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedRawDirectAuthority.of_resolved actual rows supported
    (covered actual.native.index actual.native.signature
      (CallableIndexedOwnedPreparedStagedRawDirectAuthority.target actual)
      (CallableIndexedOwnedPreparedStagedRawDirectAuthority.native_selected actual).1)
    (by rw [support.compilation]; rfl)
    ⟨actual.available, actual.resolved, dictionary⟩ signatures ledger assumptions idsUnique
  have childTyped : ExpressionHasType child.source context id node.type := by simpa only [sameSource] using typed
  have unique : NodeOccurrencesUnique child.source := sameSource ▸ support.unique
  have callerMember := (CallableNamedMetadata.specialization_of_exact
    (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)).1
  have nodeMember : .expression node ∈ support.caller.named.specialized.function.typedBody.nodes := by
    have lookup : support.caller.named.specialized.function.typedBody.lookupExpression? id = some node := by
      have sourceEq : function.source = support.caller.named.specialized.function.typedBody := support.source
      rw [← sourceEq]
      exact found
    exact (lookupExpression?_sound lookup).1
  obtain ⟨calls, spine⟩ := CallableCoercionSpine.of_accepted actual.suffix.accepted
  obtain ⟨⟨chain, certifiedChain⟩⟩ := SelectedCompilationCoercionChainIssuance.of_spine methods checked bodies catalog
    (by rw [support.compilation]; exact SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
    (by rw [support.compilation]; exact callerMember) nodeMember
    (by rw [support.compilation]; rfl) (by rw [support.compilation]; rfl)
    signatures ledger assumptions actual.resolved idsUnique dictionary stagePrepared spine
    (output_path unique childFound childTyped) (fun step member => List.mem_append_left _ member)
  have methodPackets : ∀ {src tgt input output steps calls} (selectedChain :
      CallableIndexedOwnedPreparedStagedCoercionChain.Chain compiled
        ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext support.caller.named.signature.key []).expressions.projectType code.compilation
        support.caller.named.specialized actual.available current node code.policy.callables context child stages
        src tgt input steps output calls), SelectedCompilationCoercionChainIssuance.Certified stagePrepared selectedChain →
        CoercionMethods headers faults selectedChain := by
    intro src tgt input output steps calls selectedChain certificates
    induction selectedChain with
    | nil => trivial
    | cons head port valid tail ih =>
      obtain ⟨headCertified, tailCertified⟩ := certificates
      obtain ⟨packet, same, supported⟩ := methodBodies port.principal port.sourceAt ⟨port.diagnostics⟩ headCertified
      exact ⟨⟨packet, same, same.symm ▸ headCertified, supported⟩, ih tailCertified⟩
  let certificate : GenericExpressionMeaning.Certificate := fun current id lowered =>
    ∃ rawType, Nonempty (Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered rawType faults)
  obtain ⟨rawTypes, argsTyped⟩ := arguments_typed unique childFound form childTyped
  have argumentsAccepted : ids.mapM (fun argument => SourceCoreFunctions.lowerExpressionWithPolicy
      code.policy code.lowerBody fuel code.compilation child.source current argument code.reasonAt) = .ok actual.loweredArguments := by
    simpa only [CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child, Nat.min_eq_right (Nat.le_succ fuel)] using actual.argumentsAccepted
  obtain ⟨argumentTypes, argumentTree⟩ := argument_tree (certificate := certificate) _ unique argsTyped argumentsAccepted (by
    intro argument member argumentNode argumentCode argumentFound argumentTyped argumentAccepted
    obtain ⟨⟨rawType, root⟩⟩ := SelectedCompilationPreparedBranchingMethodScopedRoots.of_original_child_with_catalog
      stagePrepared code support provenance callerReceipt receiver bodies certified (fun _ impossible => False.elim impossible)
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor.of_native metadata) rows
      (fun _ impossible => False.elim impossible) checked catalog (.generic ⟨methods.formed, methods.assumptions⟩)
      signatureMember sourceOwner selected fields declarations (children argument member)
      (.expression reached found (by simp [form, ExpressionForm.references, member]))
      (by simpa only [sameSource] using argumentFound) (by simpa only [sameSource] using argumentTyped)
      (by simpa only [sameSource] using argumentAccepted)
    exact ⟨rawType, ⟨root⟩⟩)
  exact ⟨{
    compilerFuel := fuel+1
    accepted := by simpa only [sameSource] using accepted
    project := _
    caller := support.caller.named.specialized
    child := _
    fuel := fuel+1
    node := node
    callee := callee
    arguments := ids
    instantiation := instantiation
    actual := actual
    nonempty := nonempty
    result := rfl
    typed := childTyped
    port := port
    certified := SelectedCompilationCatalog.certificates bodies rows port.header port.member
    shape := SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member
    argumentTypes := argumentTypes
    argumentCertificate := certificate
    argumentTree := argumentTree
    argumentRoots := fun proof => proof
    calls := calls
    chain := chain
    methods := methodPackets chain certifiedChain
    ledger := ledger
    runtimeLedger := fields.runtimeRequirementLedger support.body.valid.runtime
    unique := unique
    catalog := bodies.signatures
    runtime := by
      rw [sameSource]
      exact ((CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
        support.body.frame support.body.toContext.extended).1).transport fields
    covers := by rw [(stages).evidence selected]; exact fields.covers support.body.valid.covers
  }⟩
end Actual
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedDirectRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedTerminalSupport
/-! The authentic retained terminal callback yields an original coerced root
at every selected Source scope. Body-view transport keeps the complete parent
node and composes the actual ordered argument compiler actions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (Terminal)
open SelectedCompilationPhysicalClosureStaticSupport (SelectedBody)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (support : PreparedLambdaBodySupport.Support code)
  (provenance : PreparedLambdaBodySupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (metadata : NativeMetadataFor compiled.indexed support.caller.named function.source (fun _ => False))
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
  {signature : ProgramFunctionSignature} (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows



include receiver bodies certified metadata rows checked catalog methods signatureMember sourceOwner provenance callerReceipt in
theorem of_actual
    (methodBodies : ∀ {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (_diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    (_certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt),
    ∃ packet : SelectedCompilationMethodBodySupport.Packet principal,
      packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodySupport.Support
        principal packet (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))

    (expression : ExpressionId)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source expression function.body)
    {node : ExpressionNode} {callee : ExpressionId} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation}
    (found : function.source.lookupExpression? expression = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (nonempty : node.coercions ≠ []) (requirements : node.requirements ≠ [])
    (children : ∀ argument ∈ ids, GeneralSyntax function.source argument (fun _ => False))
    (noInitializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed support.caller.named).owner ∧
        binding.initializer = expression)) = none)
    (supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
    (covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers, header.slot = index ∧ header.named.signature = signature)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : Terminal code stages,
      SelectedBody («headers» := headers) code support.body.toContext stages packet faults) := by
  obtain ⟨packet, expressionEq, callback, reason, _child, point, prefixEq⟩ :=
    SelectedCompilationPreparedBranchingTerminalChoice.of_actual code support provenance
      expression terminal child selected
  subst expression
  refine ⟨⟨packet, { point := point, readFuel := compiled.indexed.fuel, «prefix» := prefixEq, roots := ?_ }⟩⟩
  intro selectedChild selectedAt
  apply Classical.choice
  have sameSource := (stages).source selectedAt
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code support.body.toContext support.body.frame
    provenance.scope_declarations selectedAt
  obtain ⟨actualNode, actualFound, rawType, typed⟩ :=
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type
      code packet support.body.toContext support.body.frame selectedChild selectedAt
  have originalFound : function.source.lookupExpression? packet.expression = some actualNode := by
    simpa only [sameSource] using actualFound
  cases Option.some.inj (originalFound.symm.trans found)
  have reached := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet
  have accepted := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.accepted_view_action code packet callback reason
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [] := by
    rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  generalize fuelEq : min packet.receipt.childFuel code.fuel = fuel at accepted
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
      have original := CallableIndexedOwnedPreparedStagedCoercedBodyViewTransport.accepted_original
        code provenance.policy_recipe provenance.body_view callables
        (CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor.of_native metadata)
        noInitializer found form requirements children reached accepted
      obtain ⟨root⟩ := SelectedCompilationPreparedBranchingCoercedDirectRoots.of_original_child
        stagePrepared code support provenance callerReceipt receiver bodies certified metadata rows checked catalog methods
        signatureMember sourceOwner methodBodies selectedAt (Dynamic.RuntimeContextFields.refl _)
        (by simpa only [sameSource] using declarations) children reached found form nonempty requirements
        noInitializer supported covered (by simpa only [sameSource] using typed) original
      refine ⟨.coercedDirect ?_⟩
      simpa only [rawType] using root

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedTerminalSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedClosureAdmission
/-! Finite checks retain each original lambda body and its constrained direct
call. The original coercion rows and captured Source remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedCoercedClosureAdmission (BodyCertificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : PreparedLambdaBodySupport.Support code)
  (provenance : PreparedLambdaBodySupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)

include stagePrepared code support provenance callerReceipt receiver bodies rows aligned checked catalog methods callerReceipt in
theorem of_actual
    (certificate : BodyCertificate compiled support.caller.named directRows function.body)
    (methodBodies : ∀ {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
        (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
      (_diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
      (_certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt),
      ∃ packet : SelectedCompilationMethodBodySupport.Packet principal,
        packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodySupport.Support
          principal packet (headers rows) (RecursiveNamedPreparedStageScopes.registry stagePrepared)
          (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SelectedCompilationPhysicalClosureStaticSupport.SelectedBody (headers := headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have certified := SelectedCompilationOrdinaryClosureFacts.certified bodies callerReceipt
  have supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
      code.compilation.plan certificate.instantiation := by
    rw [support.compilation]
    exact certificate.direct.supported aligned
  have covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan certificate.instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro index signature target global
    rw [support.compilation] at target global
    exact certificate.direct.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  exact SelectedCompilationPreparedBranchingCoercedTerminalSupport.of_actual
    stagePrepared code support provenance callerReceipt receiver bodies certified
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    methodBodies certificate.expression
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.terminal)
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.found)
    certificate.form certificate.coercions certificate.requirements
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.children)
    certificate.initializer supported covered _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedClosureAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryMethodScopedRoots
/-! Each actual ordinary lexical callback keeps its original Source context,
physical scope and retained Code. General expression certificates are recovered
from the real view compiler; finite direct/index authority stays static. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryMethodScopedRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax Certificate)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles
open CallableIndexedOwnedPreparedStagedOrdinaryMethodPolicy
open CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open SelectedCompilationRootStaticSupport
open SelectedCompilationMixedRootSupport (Root)

section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (provenance : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (metadata : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

include receiver bodies certified supported metadata rows covered checked catalog methods signatureMember sourceOwner provenance callerReceipt in
/-- The actual binder fields transport typing, ledger and evidence. The root
retains the concrete Code compiler, including its original prefix and reasons. -/
theorem of_original_child_with_catalog
    {child : Staging.Recursive.Scope} (selected : (stages).Closure function child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields support.body.context context)
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    (tree : GeneralSyntax function.source id directSites)
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation function.source current id code.reasonAt = .ok lowered) :
    Nonempty (Σ rawType, Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered rawType faults) := by
  have sameSource := (stages).source selected
  have unique : NodeOccurrencesUnique child.source := sameSource ▸ support.unique
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      compiled.indexed.base.callableContext [] := by rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  have originalProfile := retained_policy_for provenance.policy_recipe metadata callables supported current code.reasonAt
  have profile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodStepPolicyFor
      code.policy code.compilation compiled.indexed.fuel (.initial compiled.compatible.checked)
      child.source current code.reasonAt directSites := by simpa only [sameSource] using originalProfile
  have coercions : ∀ id actualNode, GeneralSyntax child.source id directSites →
      child.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sameSource] using syntaxTree)
      actualNode (by simpa only [sameSource] using actualFound)
  have childTree : GeneralSyntax child.source id directSites := by simpa only [sameSource] using tree
  have childFound : child.source.lookupExpression? id = some node := by simpa only [sameSource] using found
  have childTyped : ExpressionHasType child.source context id node.type := by simpa only [sameSource] using typed
  have childDeclarations : CompatibleExpressionReads.ScopeDeclarations child.source current context := by
    simpa only [sameSource] using declarations
  have compiledChild : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation child.source current id code.reasonAt = .ok lowered := by
    simpa only [sameSource] using accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable code.active code.callables
    unique childDeclarations profile coercions childTree childFound childTyped compiledChild
  have atOwner : SelectedCompilationOrdinaryAnnotationCoherence.AtOwner compiled.sourceProgram function.source.owner := by
    let caller := callerReceipt.extend (Dynamic.MonoBindersExtend.runtimeContextFields support.body.extended)
    rw [support.source]
    exact SelectedCompilationOrdinaryAnnotationCoherence.at_prepared bodies caller.prepared
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) certificate :=
    SelectedCompilationOrdinaryEvidenceCallsReady.calls_ready stagePrepared
      code (fun id tree => retained_read_policy provenance.policy_recipe metadata tree) support.source_receipt support.unique
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) bodies atOwner signatureMember sourceOwner
      selected childTyped certificate childTree
  have directReady : ∀ {callFuel callScope callId callee ids instantiation callCode}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        code.policy code.lowerBody callFuel code.compilation
        (.initial compiled.compatible.checked) child.source callScope callId callee ids
        instantiation code.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler certificate →
      Nonempty {port : CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler
        headers context child.evidence // SelectedCompilationNamedSourceTyping.Certified port.header ∧
          SelectedCompilationSourceSignatureFacts.Shape port.header} := by
    intro callFuel callScope callId callee ids instantiation callCode compiler path
    have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path childTree
    have site := actualTree.direct_site compiler.metadata.found compiler.form
    obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory_at compiler rows
      (covered instantiation site compiler.index compiler.signature compiler.target compiler.global)
      (by rw [support.compilation]; rfl)
    have childMetadata : MetadataFor compiled.indexed support.caller.named child.source directSites := by
      simpa only [sameSource] using metadata
    rcases retained_accepted_direct_action provenance.policy_recipe childMetadata actualTree
      compiler.metadata.found compiler.form compiler.accepted with bypass | authentic
    · obtain ⟨requirements, assumptions⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct
          compiler.metadata.found compiler.form bypass
      have special := fun callback budget =>
        (retained_direct_hook provenance.policy_recipe childMetadata actualTree
          compiler.metadata.found compiler.form callback budget callScope code.reasonAt).trans
          (CallableCallEvidenceCertificates.direct_bypass compiler.metadata.found compiler.form requirements
            compiler.metadata.coercions assumptions)
      have ordinary := compiler.ordinary special
        (retained_read_policy provenance.policy_recipe childMetadata actualTree)
      exact ⟨⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
        compiler port ordinary requirements context child.evidence⟩,
        SelectedCompilationCatalog.certificates bodies rows port.header port.member,
        SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member⟩⟩
    · obtain ⟨action⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
        compiler.metadata.found compiler.form authentic
      rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at action
      let originalCaller := callerReceipt.extend (Dynamic.MonoBindersExtend.runtimeContextFields support.body.extended)
      let caller := (originalCaller.extend fields).with_evidence ((stages).evidence selected)
      have parameters := RecursiveNamedInitialContextValidity.mono_fields support.caller.extended
      have signatures : context.signatures = compiled.sourceProgram.signatures := by
        rw [caller.fields.signatures, parameters.signatures, caller.aligned.function]
        rfl
      have ledger : context.solvedRequirements = support.caller.named.specialized.function.solvedRequirements :=
        caller.fields.solvedRequirements.trans (support.caller.valid.ledger.trans
          (caller.aligned.solved.trans (congrArg (fun named => named.specialized.function.solvedRequirements)
            caller.aligned.named.symm)))
      have assumptions : ∀ goal, goal ∈ support.caller.named.specialized.assumptions → goal ∈ context.assumptions := by
        intro goal member
        rw [caller.fields.assumptions, parameters.assumptions, caller.aligned.function]
        change goal ∈ caller.prepared.named.specialized.assumptions
        rw [← caller.aligned.named]
        exact member
      have idsUnique : RequirementIdsUnique context := by
        simpa only [RequirementIdsUnique, caller.fields.solvedRequirements] using
          (SelectedCompilationHeaderFacts.scoped_ledger certified).idsUnique
      exact ⟨⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence
        compiler port action caller.prepared signatures ledger assumptions idsUnique caller.dictionary⟩,
        SelectedCompilationCatalog.certificates bodies rows port.header port.member,
        SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member⟩⟩
  have methodReady : ∀ {callFuel callScope callId callCode}
      (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        code.policy code.lowerBody callFuel code.compilation (.initial compiled.compatible.checked)
        child.source callScope callId code.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodCalls compiler certificate →
      Nonempty {port : CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
        compiler context child.evidence stages //
        Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context child.evidence
          port.principal.traitName port.principal.methodName compiler.node.requirements
          port.principal.sourceBody port.principal.dictionary} := by
    intro callFuel callScope callId callCode compiler path
    have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.method_calls_syntax_of path childTree
    have childMetadata : MetadataFor compiled.indexed support.caller.named child.source directSites := by
      simpa only [sameSource] using metadata
    have form : (∃ operator operand, compiler.node.form = .unary operator operand) ∨
        (∃ operator left right, compiler.node.form = .binary left operator right) := by
      rcases compiler.operator.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
      · exact .inl ⟨operator, operand, form⟩
      · exact .inr ⟨operator, left, right, form⟩
    have hook := retained_operator_hook provenance.policy_recipe childMetadata actualTree compiler.metadata.found form
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child code.policy code.lowerBody callFuel code.compilation)
      (callFuel + 1) callScope code.reasonAt
    have acceptedMethod := hook.symm.trans compiler.special
    have nonempty : compiler.node.requirements ≠ [] := by
      intro empty
      exact compiler.operator.nonempty ((CallableIndexedOwnedPreparedStagedMethodArgumentRows.requirements compiler).trans empty)
    obtain ⟨actual⟩ := CallablePreparedMethodSelection.of_accepted compiler.metadata.found form
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.ordinary_requirements compiler.metadata.coercions)
      nonempty acceptedMethod
    rw [← callables] at actual
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at actual
    obtain ⟨sourceReceipt⟩ := CallablePreparedMethodRuntimeMeaning.OperatorSource.of_accepted actual
    let originalCaller := callerReceipt.extend (Dynamic.MonoBindersExtend.runtimeContextFields support.body.extended)
    let caller := (originalCaller.extend fields).with_evidence ((stages).evidence selected)
    have parameters := RecursiveNamedInitialContextValidity.mono_fields support.caller.extended
    have signatures : context.signatures = compiled.sourceProgram.signatures := by
      rw [caller.fields.signatures, parameters.signatures, caller.aligned.function]
      rfl
    have ledger : context.solvedRequirements = support.caller.named.specialized.function.solvedRequirements :=
      caller.fields.solvedRequirements.trans (support.caller.valid.ledger.trans
        (caller.aligned.solved.trans (congrArg (fun named => named.specialized.function.solvedRequirements)
          caller.aligned.named.symm)))
    have assumptions : ∀ goal, goal ∈ support.caller.named.specialized.assumptions → goal ∈ context.assumptions := by
      intro goal member
      rw [caller.fields.assumptions, parameters.assumptions, caller.aligned.function]
      change goal ∈ caller.prepared.named.specialized.assumptions
      rw [← caller.aligned.named]
      exact member
    have idsUnique : RequirementIdsUnique context := by
      simpa only [RequirementIdsUnique, caller.fields.solvedRequirements] using
        (SelectedCompilationHeaderFacts.scoped_ledger certified).idsUnique
    have parentTyped := CallableIndexedOwnedPreparedStagedMethodPathTyping.parent_typed compiler unique childTyped path
    have callerMember := (CallableNamedMetadata.specialization_of_exact
      (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)).1
    have sourceEq : child.source = support.caller.named.specialized.function.typedBody :=
      sameSource.trans support.source
    have nodeMember : .expression compiler.node ∈ support.caller.named.specialized.function.typedBody.nodes := by
      have found : support.caller.named.specialized.function.typedBody.lookupExpression? callId = some compiler.node :=
        by simpa only [sourceEq] using compiler.metadata.found
      exact (lookupExpression?_sound found).1
    have dictionary : child.evidence = CallableNamedMetadata.environment actual.available := by
      have same := Except.ok.inj (actual.resolved.symm.trans caller.prepared.resolved)
      rw [caller.dictionary, same]
      rfl
    exact SelectedCompilationMethodSelectionIssuer.of_actual compiler actual compiler.special
      sourceReceipt methods checked bodies catalog
      (by rw [support.compilation]; exact SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
      (by rw [support.compilation]; exact callerMember) nodeMember
      (by rw [support.compilation]; rfl) (by rw [support.compilation]; rfl)
      signatures ledger assumptions idsUnique dictionary unique parentTyped stagePrepared
  let root : RootData compiled code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered node.type faults := {
    compilerFuel := fuel
    accepted := compiledChild
    certificate := certificate
    node := node
    found := childFound
    rawResult := rfl
    typed := childTyped
    sameLedger := fields.solvedRequirements.trans support.body.valid.ledger
    runtimeLedger := fields.runtimeRequirementLedger support.body.valid.runtime
    unique := unique
    catalog := bodies.signatures
    runtime := by
      rw [sameSource]
      exact ((CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
        support.body.frame support.body.toContext.extended).1).transport fields
    covers := by rw [(stages).evidence selected]; exact fields.covers support.body.valid.covers
    actualFunctionType := by rw [code.callables]; rfl
    uninitialized := by
      intro current readId lowered receipt childReached location
      have originalReached : Reaches function.source [.expression id] (.expression readId) := by
        simpa only [sameSource] using childReached
      exact CallableIndexedOwnedContextualLambdaReadDiagnostics.prepared_uninitialized support provenance.body_reasons
        receiver (reached.from_root originalReached) (by simpa only [sameSource] using receipt) location
    callsReady := ready }
  exact ⟨⟨node.type, ⟨root, directReady,
    CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.prepared_ordinary_ready support provenance.body_reasons
      sameSource reached certificate, methodReady⟩⟩⟩

include receiver bodies certified supported metadata rows covered checked catalog methods signatureMember sourceOwner provenance callerReceipt in
/-- The real body-view callback supplies a root for the original Source at its
actual lexical context, using the unchanged compiler and retained dictionary. -/
theorem of_child_with_catalog
    {child : Staging.Recursive.Scope} (selected : (stages).Closure function child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields support.body.context context)
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    (tree : GeneralSyntax function.source id directSites)
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation code.view current id code.reasonAt = .ok lowered) :
    Nonempty (Σ rawType, Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered rawType faults) := by
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      compiled.indexed.base.callableContext [] := by
    rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  exact of_original_child_with_catalog stagePrepared code support provenance callerReceipt receiver bodies certified supported metadata
    rows covered checked catalog methods signatureMember sourceOwner selected fields declarations tree reached found typed
    (CallableIndexedOwnedPreparedStagedMethodBodyViewTransport.accepted_original
      code provenance.policy_recipe provenance.body_view callables metadata tree reached accepted)

end Generic
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryMethodScopedRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryMethodTerminalSupport
/-! The genuine retained ordinary terminal body supplies each selected mixed
root with its complete caller dictionary and actual method selection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryMethodTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (Terminal)
open SelectedCompilationPhysicalClosureStaticSupport (SelectedBody)
section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (provenance : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (metadata : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows


include receiver bodies certified supported metadata rows covered checked catalog methods signatureMember sourceOwner provenance callerReceipt in
/-- The accepted terminal callback yields the original method-aware expression
root at every genuine selected Source scope. -/
theorem of_actual_with_catalog
    (expression : ExpressionId)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source expression function.body)
    (tree : GeneralSyntax function.source expression directSites)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : Terminal code stages,
      SelectedBody («headers» := headers) code support.body.toContext stages packet faults) := by
  obtain ⟨packet, expressionEq, callback, reason, _child, point, prefixEq⟩ :=
    SelectedCompilationPreparedOrdinaryTerminalChoice.of_actual code support provenance
      expression terminal child selected
  refine ⟨⟨packet, { point := point, readFuel := compiled.indexed.fuel, «prefix» := prefixEq, roots := ?_ }⟩⟩
  intro selectedChild selectedAt
  apply Classical.choice
  have sameSource := (stages).source selectedAt
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code support.body.toContext support.body.frame
    provenance.scope_declarations selectedAt
  obtain ⟨node, found, rawType, typed⟩ :=
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type
      code packet support.body.toContext support.body.frame selectedChild selectedAt
  have accepted := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.accepted_view_action code packet callback reason
  obtain ⟨⟨actualType, root⟩⟩ :=
    SelectedCompilationPreparedOrdinaryMethodScopedRoots.of_child_with_catalog stagePrepared code support provenance callerReceipt
      receiver bodies certified supported metadata rows covered checked catalog methods signatureMember sourceOwner
      selectedAt (Dynamic.RuntimeContextFields.refl _)
      (by simpa only [sameSource] using declarations)
      (expressionEq.symm ▸ tree)
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet)
      (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed) accepted
  have sameNode := Option.some.inj (root.found.symm.trans found)
  have resultEq : actualType = function.resultType := root.rawResult.symm.trans (sameNode ▸ rawType)
  exact ⟨resultEq ▸ root⟩

end Generic
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryMethodTerminalSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedClosureAdmission
/-! Finite original-source lambda checks cover ordinary terminal roots and the
existing constrained coerced terminal roots. Catalog capability controls the
coerced branch; original bodies and metadata are retained in both branches. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedClosureAdmission (OrdinaryBodyCertificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (provenance : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)

include stagePrepared code support provenance callerReceipt receiver bodies rows aligned checked catalog methods callerReceipt in
theorem of_ordinary
    (certificate : OrdinaryBodyCertificate compiled support.caller.named directRows function.body) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SelectedCompilationPhysicalClosureStaticSupport.SelectedBody (headers := headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have certified := SelectedCompilationOrdinaryClosureFacts.certified bodies callerReceipt
  have supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation := by
    intro instantiation site
    rw [support.compilation]
    exact site.supported aligned
  have covered : ∀ instantiation, DirectSite directRows instantiation → ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro instantiation site index signature target global
    rw [support.compilation] at target global
    exact site.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  exact SelectedCompilationPreparedOrdinaryMethodTerminalSupport.of_actual_with_catalog
    stagePrepared code support provenance callerReceipt receiver bodies certified supported
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows covered checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    certificate.expression
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.terminal)
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.tree)
    _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedClosureAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryMethodScopedSupport
/-! General expressions at actual ordinary lexical scopes retain the same
Code compiler and genuine canonical-root authorities. Existing branching
collector/flow trees handle local allocation, assignment and finite control. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryMethodScopedSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability CallableLambdaViewEdits
open SelectedCompilationMixedRootSupport (Root)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private theorem accepted_child
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
    {stages : Staging.Recursive.Registry}
    (choice : CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts.Choice code (stages := stages))
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : choice.packet.policy.lowerExpression fuel code.view current id choice.packet.reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody (min fuel code.fuel)
      code.compilation code.view current id code.reasonAt = .ok lowered := by
  have callback := choice.callback
  have reason := choice.reason
  rw [callback, reason] at accepted
  exact accepted


section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (provenance : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (original : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

variable (choice : Choice code
  («stages» := RecursiveNamedPreparedStageScopes.registry stagePrepared))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include provenance callerReceipt receiver bodies certified supported original rows covered checked catalog methods signatureMember sourceOwner in
/-- Every original expression is issued at its real lexical context, including the
RHS and later reads after a genuine assignment or local allocation. -/
def support_general_with_catalog
    (choiceIssued : choice.Issued code support.caller.named)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType) :
    SelectedCompilationPhysicalBranchingClosureStaticSupport.SelectedBody
      headers code support.body.toContext stages choice.packet faults := by
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
    support.body.frame support.body.extended).1
  have sourceSignatures : support.body.context.signatures = compiled.compatible.checked.signatures :=
    (runtime.signatures.trans
      (RecursiveNamedSelectedExpressionFactory.header_program_signatures
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) support.caller).symm).trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := support.caller))
  have ownership : LocalIdentityOwnership function.source := by
    obtain ⟨_, certificate⟩ := certified
    rw [support.source]
    change LocalIdentityOwnership support.caller.named.specialized.function.typedBody
    rw [← support.caller.agreement.source, support.caller.frame.source]
    exact certificate.local_identity_ownership
  refine ⟨support.body.frame, support.body.projection, compiled.indexed.fuel, ?_,
    choice.invalidProjection, choice.missingDefault,
    choiceIssued.assignmentAuthority code support.caller.selected support.source support.body.unique, ?_⟩
  · rw [support.compilation]; rfl
  intro child selected
  have actual := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport.collected
    code support.body.toContext support.body.frame choice provenance.body_view provenance.scope_declarations
    sourceSignatures (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    (by rw [CallableIndexedOwnedPublicSignatureCatalog.signatures compiled]; exact bodies.signatures)
    support.body.valid.ledger support.body.projection
    (fun origin rawProfile => choiceIssued.operands code support.caller.selected support.source receiver origin rawProfile)
    (fun origin rawWord => choiceIssued.unary code support.caller.selected support.source receiver origin rawWord) syntaxTree
    (certificates := fun context scope id lowered => Nonempty (Σ rawType,
      Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
        context child code.reasonAt scope id lowered rawType faults))
    (fun context fields current fuel id node lowered declarations tree reached found typed accepted _nativeType _native => by
      exact SelectedCompilationPreparedOrdinaryMethodScopedRoots.of_child_with_catalog
        stagePrepared code support provenance callerReceipt receiver bodies certified supported original rows covered checked catalog methods signatureMember sourceOwner
        selected fields declarations tree reached found typed (accepted_child code choice accepted))
  have weakened := CallableLambdaViewMatchRuntimeCertificates.transport_with
    (LocalView.refl function.source) (by intro id member; cases member)
    support.body.unique (fun _ _ _ => True.intro)
    (fun _ _ _ _ _ value => value) actual.tree
    (fun id member => Reaches.root (List.mem_map.mpr ⟨id, member, rfl⟩))
  rw [(stages).source selected]
  refine ⟨weakened, ?_⟩
  intro currentRegistry
  obtain ⟨tree, sites⟩ := PreparedBranchingCatalogTransport.weaken support.body.unique
    (actual.sites currentRegistry)
  exact sites

include provenance callerReceipt receiver bodies certified supported original rows covered checked catalog methods signatureMember sourceOwner in
omit choice in
/-- The real lowerer and typed original syntax produce the same-model packet
and all static support together, without selecting a proof as runtime data. -/
theorem of_actual_with_catalog
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code stages,
      SelectedCompilationPhysicalBranchingClosureStaticSupport.SelectedBody
        headers code support.body.toContext stages packet faults) := by
  obtain ⟨choice, choiceIssued⟩ := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts.choose_issued
    code support.caller.named provenance.issued_recipe support.compilation shape child selected
  exact ⟨⟨choice.packet,
    support_general_with_catalog stagePrepared code support provenance callerReceipt receiver bodies certified supported original rows covered checked catalog methods
      signatureMember sourceOwner choice choiceIssued syntaxTree⟩⟩

end Generic
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryMethodScopedSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedScopedClosureAdmission
/-! Compiler-derived scoped body certificates use the existing branching closure
collector at the original Source frame and exact current parameter context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedScopedClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedScopedClosureAdmission (SourceBodyCertificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (provenance : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)

include stagePrepared code support provenance callerReceipt receiver bodies rows aligned checked catalog methods callerReceipt in
theorem of_actual
    (certificate : SourceBodyCertificate compiled support.caller.named directRows function.body) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SelectedCompilationPhysicalBranchingClosureStaticSupport.SelectedBody (headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have certified := SelectedCompilationOrdinaryClosureFacts.certified bodies callerReceipt
  have supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation := by
    intro instantiation site
    rw [support.compilation]
    exact site.supported aligned
  have covered : ∀ instantiation, DirectSite directRows instantiation → ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro instantiation site index signature target global
    rw [support.compilation] at target global
    exact site.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  obtain ⟨finalContext, facts, typed, completed⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters support.body.frame support.body.extended
  have scan : ScopedSourceBodyAdmission.Scan function.source
      (fun id => GeneralSyntax function.source id (DirectSite directRows)) certificate.result true function.body := by
    simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.scan
  have result : function.resultType = certificate.result :=
    scan.result_eq_of_completes support.body.unique typed completed
  have syntaxTree := scan.syntax support.body.unique result typed
  rw [← result] at syntaxTree
  exact SelectedCompilationPreparedOrdinaryMethodScopedSupport.of_actual_with_catalog
    stagePrepared code support provenance callerReceipt receiver bodies certified supported
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows covered checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    scan.shape syntaxTree
    _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedScopedClosureAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryCoercedDirectRoots
/-! Original direct output coercions retain the real caller, ordered argument
compiler actions, and selected conversion packets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryCoercedDirectRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor)
open SelectedCompilationMixedRootSupport (Root CoercedDirectRoot CoercionMethods)

private theorem arguments_typed {source : TypedSource} {context : SourceSemantics.Context}
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (typed : ExpressionHasType source context id node.type) :
    ∃ types, ExpressionsHaveTypes source context ids types := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | intro contains raw _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst_vars
    rw [form] at raw
    cases raw with
    | directCall _ _ arguments => exact ⟨_, arguments⟩

private theorem output_path {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type) :
    CoercionPathValid context node.rawType node.type node.coercions := by
  obtain ⟨actual, rawType, contains, result, raw, _admissible, path⟩ := typed.raw_type_and_output_path
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst actual
  simpa only [← raw] using path

private theorem argument_tree {source : TypedSource} {context : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (compile : ExpressionId → Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr)
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (accepted : ids.mapM compile = .ok codes)
    (extract : ∀ id ∈ ids, ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type → compile id = .ok code → certificate scope id code) :
    ∃ actualTypes, DataExpressionSequence.Tree source certificate scope ids actualTypes codes := by
  induction ids generalizing types codes with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst codes
    exact ⟨[], .nil⟩
  | cons id ids ih =>
    cases typed with
    | cons head tail =>
      cases first : compile id with
      | error error => simp [List.mapM_cons, first, bind, Except.bind] at accepted
      | ok code =>
        cases rest : ids.mapM compile with
        | error error => simp [List.mapM_cons, first, rest, bind, Except.bind] at accepted
        | ok restCodes =>
          simp only [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
          subst codes
          obtain ⟨node, contains, typeEq⟩ := head.stored_type
          have found := lookupExpression?_complete unique contains
          have child := extract id (by simp) node code found (typeEq ▸ head) first
          obtain ⟨tailTypes, tailTree⟩ := ih tail rest (fun id member => extract id (by simp [member]))
          cases tailTree with
          | nil => exact ⟨_, .single found child⟩
          | single nextFound nextChild => exact ⟨_, .cons found child (.single nextFound nextChild)⟩
          | cons nextFound nextChild tailTree => exact ⟨_, .cons found child (.cons nextFound nextChild tailTree)⟩

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (provenance : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (metadata : NativeMetadataFor compiled.indexed support.caller.named function.source (fun _ => False))
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
  {signature : ProgramFunctionSignature} (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows


include receiver bodies certified metadata rows checked catalog methods signatureMember sourceOwner provenance callerReceipt in
theorem of_original_child
    (methodBodies : ∀ {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (_diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    (_certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt),
    ∃ packet : SelectedCompilationMethodBodySupport.Packet principal,
      packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodySupport.Support
        principal packet (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))

    {child : Staging.Recursive.Scope} (selected : (stages).Closure function child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields support.body.context context)
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    (children : ∀ argument ∈ ids, GeneralSyntax function.source argument (fun _ => False))
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (nonempty : node.coercions ≠ []) (requirements : node.requirements ≠ [])
    (noInitializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed support.caller.named).owner ∧
        binding.initializer = id)) = none)
    (supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
    (covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers, header.slot = index ∧ header.named.signature = signature)
    (typed : ExpressionHasType function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody (fuel+1)
      code.compilation function.source current id code.reasonAt = .ok lowered) :
    Nonempty (CoercedDirectRoot compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered node.type faults) := by
  have sameSource := (stages).source selected
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      compiled.indexed.base.callableContext [] := by
    rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  have authentic : SourceCoreEvidence.lowerWithProjector compiled.sourceProgram
      ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext support.caller.named.signature.key []).expressions.projectType
      support.caller.named.specialized code.compilation
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child code.policy code.lowerBody fuel code.compilation)
      (fuel+1) child.source current id code.reasonAt code.policy.callables = .ok (some lowered) := by
    obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, sameCompilation⟩ := provenance.policy_recipe
    rw [sameCompilation] at accepted ⊢
    rw [sameSource, callables]
    rcases CallableIndexedOwnedPreparedStagedCoercedBodyViewTransport.accepted_direct_action
      recipe noInitializer found form accepted with bypass | actual
    · exact False.elim (requirements (CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct found form bypass).1)
    · simpa only [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] using actual
  have childFound : child.source.lookupExpression? id = some node := by simpa only [sameSource] using found
  obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted childFound form authentic
  let originalCaller := callerReceipt.extend (Dynamic.MonoBindersExtend.runtimeContextFields support.body.extended)
  let caller := (originalCaller.extend fields).with_evidence ((stages).evidence selected)
  have parameters := RecursiveNamedInitialContextValidity.mono_fields support.caller.extended
  have signatures : context.signatures = compiled.sourceProgram.signatures := by
    rw [caller.fields.signatures, parameters.signatures, caller.aligned.function]
    rfl
  have ledger : context.solvedRequirements = support.caller.named.specialized.function.solvedRequirements :=
    caller.fields.solvedRequirements.trans (support.caller.valid.ledger.trans
      (caller.aligned.solved.trans (congrArg (fun named => named.specialized.function.solvedRequirements) caller.aligned.named.symm)))
  have assumptions : ∀ goal, goal ∈ support.caller.named.specialized.assumptions → goal ∈ context.assumptions := by
    intro goal member
    rw [caller.fields.assumptions, parameters.assumptions, caller.aligned.function]
    change goal ∈ caller.prepared.named.specialized.assumptions
    rw [← caller.aligned.named]
    exact member
  have idsUnique : RequirementIdsUnique context := by
    simpa only [RequirementIdsUnique, caller.fields.solvedRequirements] using
      (SelectedCompilationHeaderFacts.scoped_ledger certified).idsUnique
  have dictionary : child.evidence = CallableNamedMetadata.environment actual.available := by
    have same := Except.ok.inj (actual.resolved.symm.trans caller.prepared.resolved)
    rw [caller.dictionary, same]
    rfl
  obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedRawDirectAuthority.of_resolved actual rows supported
    (covered actual.native.index actual.native.signature
      (CallableIndexedOwnedPreparedStagedRawDirectAuthority.target actual)
      (CallableIndexedOwnedPreparedStagedRawDirectAuthority.native_selected actual).1)
    (by rw [support.compilation]; rfl)
    ⟨actual.available, actual.resolved, dictionary⟩ signatures ledger assumptions idsUnique
  have childTyped : ExpressionHasType child.source context id node.type := by simpa only [sameSource] using typed
  have unique : NodeOccurrencesUnique child.source := sameSource ▸ support.unique
  have callerMember := (CallableNamedMetadata.specialization_of_exact
    (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)).1
  have nodeMember : .expression node ∈ support.caller.named.specialized.function.typedBody.nodes := by
    have lookup : support.caller.named.specialized.function.typedBody.lookupExpression? id = some node := by
      have sourceEq : function.source = support.caller.named.specialized.function.typedBody := support.source
      rw [← sourceEq]
      exact found
    exact (lookupExpression?_sound lookup).1
  obtain ⟨calls, spine⟩ := CallableCoercionSpine.of_accepted actual.suffix.accepted
  obtain ⟨⟨chain, certifiedChain⟩⟩ := SelectedCompilationCoercionChainIssuance.of_spine methods checked bodies catalog
    (by rw [support.compilation]; exact SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
    (by rw [support.compilation]; exact callerMember) nodeMember
    (by rw [support.compilation]; rfl) (by rw [support.compilation]; rfl)
    signatures ledger assumptions actual.resolved idsUnique dictionary stagePrepared spine
    (output_path unique childFound childTyped) (fun step member => List.mem_append_left _ member)
  have methodPackets : ∀ {src tgt input output steps calls} (selectedChain :
      CallableIndexedOwnedPreparedStagedCoercionChain.Chain compiled
        ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext support.caller.named.signature.key []).expressions.projectType code.compilation
        support.caller.named.specialized actual.available current node code.policy.callables context child stages
        src tgt input steps output calls), SelectedCompilationCoercionChainIssuance.Certified stagePrepared selectedChain →
        CoercionMethods headers faults selectedChain := by
    intro src tgt input output steps calls selectedChain certificates
    induction selectedChain with
    | nil => trivial
    | cons head port valid tail ih =>
      obtain ⟨headCertified, tailCertified⟩ := certificates
      obtain ⟨packet, same, supported⟩ := methodBodies port.principal port.sourceAt ⟨port.diagnostics⟩ headCertified
      exact ⟨⟨packet, same, same.symm ▸ headCertified, supported⟩, ih tailCertified⟩
  let certificate : GenericExpressionMeaning.Certificate := fun current id lowered =>
    ∃ rawType, Nonempty (Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered rawType faults)
  obtain ⟨rawTypes, argsTyped⟩ := arguments_typed unique childFound form childTyped
  have argumentsAccepted : ids.mapM (fun argument => SourceCoreFunctions.lowerExpressionWithPolicy
      code.policy code.lowerBody fuel code.compilation child.source current argument code.reasonAt) = .ok actual.loweredArguments := by
    simpa only [CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child, Nat.min_eq_right (Nat.le_succ fuel)] using actual.argumentsAccepted
  obtain ⟨argumentTypes, argumentTree⟩ := argument_tree (certificate := certificate) _ unique argsTyped argumentsAccepted (by
    intro argument member argumentNode argumentCode argumentFound argumentTyped argumentAccepted
    obtain ⟨⟨rawType, root⟩⟩ := SelectedCompilationPreparedOrdinaryMethodScopedRoots.of_original_child_with_catalog
      stagePrepared code support provenance callerReceipt receiver bodies certified (fun _ impossible => False.elim impossible)
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor.of_native metadata) rows
      (fun _ impossible => False.elim impossible) checked catalog (.generic ⟨methods.formed, methods.assumptions⟩)
      signatureMember sourceOwner selected fields declarations (children argument member)
      (.expression reached found (by simp [form, ExpressionForm.references, member]))
      (by simpa only [sameSource] using argumentFound) (by simpa only [sameSource] using argumentTyped)
      (by simpa only [sameSource] using argumentAccepted)
    exact ⟨rawType, ⟨root⟩⟩)
  exact ⟨{
    compilerFuel := fuel+1
    accepted := by simpa only [sameSource] using accepted
    project := _
    caller := support.caller.named.specialized
    child := _
    fuel := fuel+1
    node := node
    callee := callee
    arguments := ids
    instantiation := instantiation
    actual := actual
    nonempty := nonempty
    result := rfl
    typed := childTyped
    port := port
    certified := SelectedCompilationCatalog.certificates bodies rows port.header port.member
    shape := SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member
    argumentTypes := argumentTypes
    argumentCertificate := certificate
    argumentTree := argumentTree
    argumentRoots := fun proof => proof
    calls := calls
    chain := chain
    methods := methodPackets chain certifiedChain
    ledger := ledger
    runtimeLedger := fields.runtimeRequirementLedger support.body.valid.runtime
    unique := unique
    catalog := bodies.signatures
    runtime := by
      rw [sameSource]
      exact ((CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
        support.body.frame support.body.toContext.extended).1).transport fields
    covers := by rw [(stages).evidence selected]; exact fields.covers support.body.valid.covers
  }⟩
end Actual
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryCoercedDirectRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryCoercedTerminalSupport
/-! The authentic retained terminal callback yields an original coerced root
at every selected Source scope. Body-view transport keeps the complete parent
node and composes the actual ordered argument compiler actions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryCoercedTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (Terminal)
open SelectedCompilationPhysicalClosureStaticSupport (SelectedBody)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (provenance : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (metadata : NativeMetadataFor compiled.indexed support.caller.named function.source (fun _ => False))
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
  {signature : ProgramFunctionSignature} (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows



include receiver bodies certified metadata rows checked catalog methods signatureMember sourceOwner provenance callerReceipt in
theorem of_actual
    (methodBodies : ∀ {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (_diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    (_certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt),
    ∃ packet : SelectedCompilationMethodBodySupport.Packet principal,
      packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodySupport.Support
        principal packet (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))

    (expression : ExpressionId)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source expression function.body)
    {node : ExpressionNode} {callee : ExpressionId} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation}
    (found : function.source.lookupExpression? expression = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (nonempty : node.coercions ≠ []) (requirements : node.requirements ≠ [])
    (children : ∀ argument ∈ ids, GeneralSyntax function.source argument (fun _ => False))
    (noInitializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed support.caller.named).owner ∧
        binding.initializer = expression)) = none)
    (supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
    (covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers, header.slot = index ∧ header.named.signature = signature)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : Terminal code stages,
      SelectedBody («headers» := headers) code support.body.toContext stages packet faults) := by
  obtain ⟨packet, expressionEq, callback, reason, _child, point, prefixEq⟩ :=
    SelectedCompilationPreparedOrdinaryTerminalChoice.of_actual code support provenance
      expression terminal child selected
  subst expression
  refine ⟨⟨packet, { point := point, readFuel := compiled.indexed.fuel, «prefix» := prefixEq, roots := ?_ }⟩⟩
  intro selectedChild selectedAt
  apply Classical.choice
  have sameSource := (stages).source selectedAt
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code support.body.toContext support.body.frame
    provenance.scope_declarations selectedAt
  obtain ⟨actualNode, actualFound, rawType, typed⟩ :=
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type
      code packet support.body.toContext support.body.frame selectedChild selectedAt
  have originalFound : function.source.lookupExpression? packet.expression = some actualNode := by
    simpa only [sameSource] using actualFound
  cases Option.some.inj (originalFound.symm.trans found)
  have reached := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet
  have accepted := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.accepted_view_action code packet callback reason
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [] := by
    rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  generalize fuelEq : min packet.receipt.childFuel code.fuel = fuel at accepted
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
      have original := CallableIndexedOwnedPreparedStagedCoercedBodyViewTransport.accepted_original
        code provenance.policy_recipe provenance.body_view callables
        (CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor.of_native metadata)
        noInitializer found form requirements children reached accepted
      obtain ⟨root⟩ := SelectedCompilationPreparedOrdinaryCoercedDirectRoots.of_original_child
        stagePrepared code support provenance callerReceipt receiver bodies certified metadata rows checked catalog methods
        signatureMember sourceOwner methodBodies selectedAt (Dynamic.RuntimeContextFields.refl _)
        (by simpa only [sameSource] using declarations) children reached found form nonempty requirements
        noInitializer supported covered (by simpa only [sameSource] using typed) original
      refine ⟨.coercedDirect ?_⟩
      simpa only [rawType] using root

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryCoercedTerminalSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedCoercedClosureAdmission
/-! Finite checks retain each original lambda body and its constrained direct
call. The original coercion rows and captured Source remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedCoercedClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedCoercedClosureAdmission (BodyCertificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (provenance : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)

include stagePrepared code support provenance callerReceipt receiver bodies rows aligned checked catalog methods callerReceipt in
theorem of_actual
    (certificate : BodyCertificate compiled support.caller.named directRows function.body)
    (methodBodies : ∀ {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
        (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
      (_diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
      (_certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt),
      ∃ packet : SelectedCompilationMethodBodySupport.Packet principal,
        packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodySupport.Support
          principal packet (headers rows) (RecursiveNamedPreparedStageScopes.registry stagePrepared)
          (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SelectedCompilationPhysicalClosureStaticSupport.SelectedBody (headers := headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have certified := SelectedCompilationOrdinaryClosureFacts.certified bodies callerReceipt
  have supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
      code.compilation.plan certificate.instantiation := by
    rw [support.compilation]
    exact certificate.direct.supported aligned
  have covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan certificate.instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro index signature target global
    rw [support.compilation] at target global
    exact certificate.direct.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  exact SelectedCompilationPreparedOrdinaryCoercedTerminalSupport.of_actual
    stagePrepared code support provenance callerReceipt receiver bodies certified
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    methodBodies certificate.expression
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.terminal)
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.found)
    certificate.form certificate.coercions certificate.requirements
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.children)
    certificate.initializer supported covered _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedCoercedClosureAdmission
end
