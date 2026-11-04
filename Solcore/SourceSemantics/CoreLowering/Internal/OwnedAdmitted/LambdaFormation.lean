import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFormationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralLambdaValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaFormationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol

/-!
# Admitted profile: lambda formation

Formation of method, ordinary, contextual and principal lambdas.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormation
/-! A genuine method lambda is a finite expression leaf. Its original Source
occurrence and typing remain explicit; actual packet formation establishes
the native completion and full method representation internally. The
formation copies the captured cells, so admission holds at the formed pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaFormationReceipts

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

/-- The original accepted same-Code ensureType receipt fixes its result type. -/
theorem native_type : code.lowered.type = CallableContract.functionType
    code.receipt.parameterCore code.receipt.resultCore := by
  have checked := code.receipt.checked
  rw [code.callables] at checked
  unfold SourceCoreBasic.ensureType at checked
  have reported : code.reported = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
    split at checked
    · assumption
    · cases checked
  exact (congrArg SourceCoreBasic.LoweredExpr.type code.receipt.emitted).trans reported

/-- The output retains all ordinary leaf effects and the exact packet state,
in the formed state that holds the copies. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
        ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩,
      (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
      PostAdmission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        function.context code.sourceNode.type outcome reached

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (copied : code.policy.snapshotLambda code.id = true)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- Original Source value and fault inversion select the authentic lambda
leaf. Its proved formation supplies the actual native and admitted post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt captured code support owner initial packet profile outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨formed, sourceTrace, native, represented, _determined⟩ :=
      formation captured code support owner initial packet profile heaps copied ordinary coercions
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
    have valueRep : ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) formed.finalMap formed.finalWorld
        code.sourceNode.type (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.lowered.type := by
      rw [sourceType, native_type captured code]
      exact .function represented
    obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
      ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
    have post := after_expression
      (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
      ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
      (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
    exact ⟨_, formed.finalStore, native, formed.finalMap, formed.finalWorld, .value valueRep, formed.heaps,
      formed.maps, formed.worlds, formed.frame, formed.copy.metadata_extends, reached, related, post⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- The original native completion is deterministic against authentic
formation; its independently sized Source trace supplies the same admission. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt captured code support owner initial packet profile outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, _native, _represented, determined⟩ :=
    formation captured code support owner initial packet profile heaps copied ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  obtain ⟨nativeResult, reachedStore, resultAt⟩ := preserves_at captured code support owner initial packet profile
    wellFormed runtime covers locals typed sourceType copied ordinary coercions heaps admitted sized
  obtain ⟨rfl, rfl⟩ := determined nativeResult reachedStore resultAt.1
  exact ⟨sourceSize, _, formed.finalHeap, sized, resultAt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation
/-! Genuine unrestricted ordinary support forms a closure at its actual
nested Header packet. Source attribution and the full carried seed stay original.
Forward inclusion transfers only the new closure, with one function model for
all actual input/output heaps. The formation copies the captured cells, so the
reached packet is the original one transported to the formed state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {actual canonical : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

/-- Full captured history comes from this actual Header row and genuine seed. -/
def history_at : History code where
  native := (initial.rows owner.position).authority.current
  ghost := (initial.rows owner.position).authority.ghost
  metadata := CallableIndexedNamedGeneration.state support.caller.named
  carried := packet.carried
  source := support.source.symm
  owner := by rw [support.compilation]; rfl
  active := support.active.symm

/-- The original named Source seed is retained by construction. -/
theorem source_origin : SourceOrigin support (history_at captured code support owner initial packet) := ⟨rfl⟩

include support in
/-- Actual ordinary compilation fixes the physical frame reference slot. -/
theorem reference_index : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  rw [CallableIndexedLambdaValues.Code.referenceIndex, support.compilation]
  rfl

variable
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)

include packet prefixContext observed inclusion in
/-- The original actual formation supplies the closure over the copies of its
captured cells. Only its function representation is transferred forward to the
caller's model. -/
theorem formation
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, native, represented, determined⟩ :=
    CallableIndexedOwnedGeneralLambdaValues.ordinary_lambda_of_formation initial owner captured code
      (history_at captured code support owner initial packet) support
      (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) rfl profile heaps copied ordinary coercions
  exact ⟨formed, sourceTrace, native, inclusion represented, determined⟩

/-- The output retains all ordinary leaf effects and the exact packet state,
in the formed state that holds the copies. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
      PostAdmission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        function.context code.sourceNode.type outcome reached

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (copied : code.policy.snapshotLambda code.id = true)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include prefixContext observed inclusion sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- Original Source value and fault inversion select the authentic lambda
leaf. Its proved formation supplies the actual native and admitted post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨formed, sourceTrace, native, represented, _determined⟩ :=
      formation captured code support owner initial packet profile prefixContext observed functions inclusion heaps
        copied ordinary coercions
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
    have valueRep : ValueRep compiled.compatible.checked registry
        functions formed.finalMap formed.finalWorld
        code.sourceNode.type (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.lowered.type := by
      rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
      exact .function represented
    obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner support.caller)
      ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
    have post := after_expression
      (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
      ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
      (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
    exact ⟨_, formed.finalStore, native, formed.finalMap, formed.finalWorld, .value valueRep, formed.heaps,
      formed.maps, formed.worlds, formed.frame, formed.copy.metadata_extends, reached, related, post⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include prefixContext observed inclusion sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- The original native completion is deterministic against authentic
formation; its independently sized Source trace supplies the same admission. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, _native, _represented, determined⟩ :=
    formation captured code support owner initial packet profile prefixContext observed functions inclusion heaps
      copied ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  obtain ⟨nativeResult, reachedStore, resultAt⟩ := preserves_at captured code support owner initial packet profile prefixContext observed functions inclusion
    wellFormed runtime covers locals typed sourceType copied ordinary coercions heaps admitted sized
  obtain ⟨rfl, rfl⟩ := determined nativeResult reachedStore resultAt.1
  exact ⟨sourceSize, _, formed.finalHeap, sized, resultAt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation
/-! The actual formation retains its contextual provenance. Original finite
formation and admitted endpoints provide the same traces and reached packet;
only the represented output closure gains its authentic static receipt. The
formed closure captures the copies of its captured cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {actual canonical : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

open CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation (history_at source_origin reference_index)

variable (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
variable
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)


/-- The contextual seed of a code is the seed of the same code over other
captures. -/
theorem provenance_recapture {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code registry faults}
    (receipt : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
    (environment : Dynamic.Environment) :
    CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt (code.recapture environment)
      (support.recapture environment) := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe
      bodyView bodyReasons declarations syntaxTree _ globals callerReceipt =>
    exact .recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe
      bodyView bodyReasons declarations syntaxTree environment globals callerReceipt

include packet prefixContext observed inclusion provenance in
theorem formation
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, native, represented, determined⟩ :=
    CallableIndexedOwnedGeneralLambdaValues.ordinary_lambda_of_formation initial owner captured code
      (history_at captured code support owner initial packet) support
      (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) rfl profile heaps copied ordinary coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).runtime_hasType
    (registry := registry) represented
  have retained : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults
      formed.finalMap formed.finalWorld (FunctionValues.sourceType function) (.closure formed.closure)
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
    .contextual_ordinary_lambda (function := formed.closure) owner formed.captures formed.closureCode
      formed.closureHistory (support.recapture formed.captured)
      ⟨(source_origin captured code support owner initial packet).metadata⟩ prefixContext
      (observed.of_slots formed.slots) (reference_index captured code support) typed
      (provenance_recapture provenance formed.captured)
  exact ⟨formed, sourceTrace, native, inclusion retained, determined⟩

/-- The original full reached result is retained verbatim, together with
its exact contextual packet, the actual formed Source/native value over the
copies, and the formed closure's representation with its contextual receipt. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.ResultAt captured code support owner initial packet functions outcome after result finalStore ∧
  CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support ∧
  ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
      (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
    outcome = .value (.closure formed.closure) ∧ after = formed.finalHeap ∧
    result = .inRight .word (value code formed.embedding
      (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native
      formed.closureActual) ∧
    finalStore = formed.finalStore ∧
    ValueRep compiled.compatible.checked registry functions formed.finalMap formed.finalWorld
      code.sourceNode.type (.closure formed.closure)
      (value code formed.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native
        formed.closureActual)
      code.lowered.type

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (copied : code.policy.snapshotLambda code.id = true)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)


include prefixContext observed inclusion sourceType copied ordinary coercions heaps provenance in
private theorem strengthen_result {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {result : Value} {finalStore : Store}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after)
    (original : CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.ResultAt captured code support owner initial packet functions outcome after result finalStore) :
    ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨formed, _sourceTrace, _native, represented, determined⟩ :=
      formation captured code support owner initial packet profile prefixContext observed provenance functions inclusion
        heaps copied ordinary coercions
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
    obtain ⟨rfl, rfl⟩ := determined result finalStore original.1
    have payload : ValueRep compiled.compatible.checked registry functions formed.finalMap formed.finalWorld
        code.sourceNode.type (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.lowered.type := by
      rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
      exact .function represented
    exact ⟨original, provenance, formed, rfl, rfl, rfl, rfl, payload⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include prefixContext observed inclusion sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed provenance in
/-- Original admitted preservation fixes the actual state and post. The
contextual representation strengthens only its freshly formed value. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  obtain ⟨result, finalStore, original⟩ :=
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.preserves_at captured code support owner initial packet profile prefixContext observed functions inclusion
      wellFormed runtime covers locals typed sourceType copied ordinary coercions heaps admitted trace
  exact ⟨result, finalStore, strengthen_result captured code support owner initial packet profile prefixContext observed provenance functions inclusion
    sourceType copied ordinary coercions heaps trace original⟩

include prefixContext observed inclusion sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed provenance in
/-- The original native reflection supplies its independent Source grade and
reached packet. No native type is inverted to obtain contextual provenance. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  obtain ⟨sourceSize, outcome, after, trace, original⟩ :=
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reflects_at captured code support owner initial packet profile prefixContext observed functions inclusion
      wellFormed runtime covers locals typed sourceType copied ordinary coercions heaps admitted completed
  exact ⟨sourceSize, outcome, after, trace, strengthen_result captured code support owner initial packet profile prefixContext observed provenance functions inclusion
    sourceType copied ordinary coercions heaps trace original⟩

end CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation
end Solcore.SourceSemantics.CoreLowering
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPrincipalLambdaFormation
/-! Principal method formation retains its actual leading bundle and captured
globals in the shared model. Forward inclusion transfers only the newly formed
closure; the caller's heap model and principal packet are transported to the
formed state that holds the copies of the captured cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPrincipalLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaFormationReceipts

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

variable
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)

include packet profile in
/-- The original formation keeps the complete principal capture receipts
in the represented closure, including its actual leading bundle. -/
theorem principal_representation
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code (history_at captured code support owner initial packet) heap store
        owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults formed.finalMap formed.finalWorld
        (FunctionValues.sourceType function) (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, native, represented, determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation captured code support owner initial packet
      profile heaps copied ordinary coercions
  have typed := (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile).runtime_hasType
    (registry := registry) represented
  have leadingFormed : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    leading captured code support owner initial packet
  exact ⟨formed, sourceTrace, native,
    .principal_lambda (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support formed.captured)
      (CallableIndexedOwnedMethodLambdaValues.recaptureOrigin (source_origin captured code support owner initial packet)
        formed.captured)
      (packet.observed.of_slots formed.slots) leadingFormed (reference_index captured code support) typed,
    determined⟩


include packet inclusion in
/-- The original actual formation supplies the closure. Only its function
representation is transferred forward to the caller's model. -/
theorem formation
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, native, represented, determined⟩ :=
    principal_representation captured code support owner initial packet
      profile heaps copied ordinary coercions
  exact ⟨formed, sourceTrace, native, inclusion represented, determined⟩

/-- The output retains all ordinary leaf effects and the exact packet state,
in the formed state that holds the copies. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
        ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩,
      (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
      PostAdmission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        function.context code.sourceNode.type outcome reached

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (copied : code.policy.snapshotLambda code.id = true)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include inclusion sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- Original Source value and fault inversion select the authentic lambda
leaf. Its proved formation supplies the actual native and admitted post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨formed, sourceTrace, native, represented, _determined⟩ :=
      formation captured code support owner initial packet profile functions inclusion heaps copied ordinary coercions
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
    have valueRep : ValueRep compiled.compatible.checked registry
        functions formed.finalMap formed.finalWorld
        code.sourceNode.type (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.lowered.type := by
      rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
      exact .function represented
    obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
      ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
    have post := after_expression
      (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
      ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
      (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
    exact ⟨_, formed.finalStore, native, formed.finalMap, formed.finalWorld, .value valueRep, formed.heaps,
      formed.maps, formed.worlds, formed.frame, formed.copy.metadata_extends, reached, related, post⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include inclusion sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- The original native completion is deterministic against authentic
formation; its independently sized Source trace supplies the same admission. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, _native, _represented, determined⟩ :=
    formation captured code support owner initial packet profile functions inclusion heaps copied ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  obtain ⟨nativeResult, reachedStore, resultAt⟩ := preserves_at captured code support owner initial packet profile functions inclusion
    wellFormed runtime covers locals typed sourceType copied ordinary coercions heaps admitted sized
  obtain ⟨rfl, rfl⟩ := determined nativeResult reachedStore resultAt.1
  exact ⟨sourceSize, _, formed.finalHeap, sized, resultAt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPrincipalLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation
/-! Principal method formation retains its actual leading bundle and captured
globals in the shared model. Forward inclusion transfers only the newly formed
closure; the caller's heap model, principal packet and Source post stay unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaFormationReceipts

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

variable
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)


variable (provenance : CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code support)

/-- The contextual principal seed of a code is the seed of the same code over
other captures. -/
theorem provenance_recapture {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code registry faults}
    (receipt : CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code support)
    (environment : Dynamic.Environment) :
    CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt (code.recapture environment)
      (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support environment) := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe
      bodyView syntaxTree _ =>
    exact .recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe
      bodyView syntaxTree environment

include packet inclusion provenance in
theorem formation
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, native, represented, determined⟩ :=
    CallableIndexedOwnedAdmittedPrincipalLambdaFormation.principal_representation captured code support owner initial packet
      profile heaps copied ordinary coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).runtime_hasType
    (registry := registry) represented
  have leadingFormed : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    leading captured code support owner initial packet
  have retained : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults
      formed.finalMap formed.finalWorld (FunctionValues.sourceType function) (.closure formed.closure)
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
    .contextual_principal_lambda (function := formed.closure) owner formed.captures formed.closureCode
      formed.closureHistory (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support formed.captured)
      (CallableIndexedOwnedMethodLambdaValues.recaptureOrigin (source_origin captured code support owner initial packet)
        formed.captured)
      (packet.observed.of_slots formed.slots) leadingFormed (reference_index captured code support) typed
      (provenance_recapture provenance formed.captured)
  exact ⟨formed, sourceTrace, native, inclusion retained, determined⟩

/-- The original full reached result is retained verbatim, together with
its exact contextual packet, the actual formed Source/native value over the
copies, and the formed closure's representation with its contextual receipt. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  CallableIndexedOwnedAdmittedPrincipalLambdaFormation.ResultAt captured code support owner initial packet functions outcome after result finalStore ∧
  CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code support ∧
  ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
      (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet) heap store
      owner.key.frameLocation,
    outcome = .value (.closure formed.closure) ∧ after = formed.finalHeap ∧
    result = .inRight .word (value code formed.embedding
      (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
      formed.closureActual) ∧
    finalStore = formed.finalStore ∧
    ValueRep compiled.compatible.checked registry functions formed.finalMap formed.finalWorld
      code.sourceNode.type (.closure formed.closure)
      (value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
        formed.closureActual)
      code.lowered.type

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (copied : code.policy.snapshotLambda code.id = true)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)


include inclusion sourceType copied ordinary coercions heaps provenance in
private theorem strengthen_result {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {result : Value} {finalStore : Store}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after)
    (original : CallableIndexedOwnedAdmittedPrincipalLambdaFormation.ResultAt captured code support owner initial packet functions outcome after result finalStore) :
    ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨formed, _sourceTrace, _native, represented, determined⟩ :=
      formation captured code support owner initial packet profile functions inclusion provenance heaps copied
        ordinary coercions
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
    obtain ⟨rfl, rfl⟩ := determined result finalStore original.1
    have payload : ValueRep compiled.compatible.checked registry functions formed.finalMap formed.finalWorld
        code.sourceNode.type (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.lowered.type := by
      rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
      exact .function represented
    exact ⟨original, provenance, formed, rfl, rfl, rfl, rfl, payload⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include inclusion sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed provenance in
/-- Original admitted preservation fixes the actual state and post. The
contextual representation strengthens only its freshly formed value. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  obtain ⟨result, finalStore, original⟩ :=
    CallableIndexedOwnedAdmittedPrincipalLambdaFormation.preserves_at captured code support owner initial packet profile functions inclusion
      wellFormed runtime covers locals typed sourceType copied ordinary coercions heaps admitted trace
  exact ⟨result, finalStore, strengthen_result captured code support owner initial packet profile functions inclusion provenance
    sourceType copied ordinary coercions heaps trace original⟩

include inclusion sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed provenance in
/-- The original native reflection supplies its independent Source grade and
reached packet. No native type is inverted to obtain contextual provenance. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  obtain ⟨sourceSize, outcome, after, trace, original⟩ :=
    CallableIndexedOwnedAdmittedPrincipalLambdaFormation.reflects_at captured code support owner initial packet profile functions inclusion
      wellFormed runtime covers locals typed sourceType copied ordinary coercions heaps admitted completed
  exact ⟨sourceSize, outcome, after, trace, strengthen_result captured code support owner initial packet profile functions inclusion provenance
    sourceType copied ordinary coercions heaps trace original⟩

end CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation
end Solcore.SourceSemantics.CoreLowering
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormationWithFunctions
/-! Method formation keeps the caller's function model throughout its heap
and result receipts. Forward inclusion transfers only the authentic newly
formed closure; the real principal packet and Source post stay unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormationWithFunctions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaFormationReceipts

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

variable
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile).Includes functions)

include packet inclusion in
/-- The original actual formation supplies the closure. Only its function
representation is transferred forward to the caller's model. -/
theorem formation
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, native, represented, determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation captured code support owner initial packet
      profile heaps copied ordinary coercions
  exact ⟨formed, sourceTrace, native, inclusion represented, determined⟩

/-- The output retains all ordinary leaf effects and the exact packet state,
in the formed state that holds the copies. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
        ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩,
      (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
      PostAdmission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        function.context code.sourceNode.type outcome reached

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (copied : code.policy.snapshotLambda code.id = true)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include inclusion sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- Original Source value and fault inversion select the authentic lambda
leaf. Its proved formation supplies the actual native and admitted post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨formed, sourceTrace, native, represented, _determined⟩ :=
      formation captured code support owner initial packet profile functions inclusion heaps copied ordinary coercions
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
    have valueRep : ValueRep compiled.compatible.checked registry
        functions formed.finalMap formed.finalWorld
        code.sourceNode.type (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.lowered.type := by
      rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
      exact .function represented
    obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
      (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
      ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
    have post := after_expression
      (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
      ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
      (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
    exact ⟨_, formed.finalStore, native, formed.finalMap, formed.finalWorld, .value valueRep, formed.heaps,
      formed.maps, formed.worlds, formed.frame, formed.copy.metadata_extends, reached, related, post⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include inclusion sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- The original native completion is deterministic against authentic
formation; its independently sized Source trace supplies the same admission. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, _native, _represented, determined⟩ :=
    formation captured code support owner initial packet profile functions inclusion heaps copied ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  obtain ⟨nativeResult, reachedStore, resultAt⟩ := preserves_at captured code support owner initial packet profile functions inclusion
    wellFormed runtime covers locals typed sourceType copied ordinary coercions heaps admitted sized
  obtain ⟨rfl, rfl⟩ := determined nativeResult reachedStore resultAt.1
  exact ⟨sourceSize, _, formed.finalHeap, sized, resultAt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormationWithFunctions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedOrdinaryLambdaFormation
/-! Original Header-supported lambda formation remains authentic under the
additive method-lambda model. Only the proved forward inclusion transfers
its representation. The actual nested packet, Source occurrence and captured
history stay original; formation copies the captured cells, and the packet and
admission are transported to the formed pool and store. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedOrdinaryLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedLambdaNestedRuntimeBodyMeaning RecursiveNamedLambdaFormationHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)} {rank : Nat}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
    source context evidence scope id lowered)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (prefixZero : owner.key.capturePrefix = 0)
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (nativeTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)

include complete globals slots prefixZero packet related agrees nativeTyped in
/-- Genuine nested packet facets select the original formation producer.
Forward inclusion adds the model alternative without weakening Source authority. -/
theorem formation
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) mapping world heap store) :
    ∃ value captured finalHeap finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
        (CallableIndexedNamedGeneration.source caller.named) environment heap id (.closure (formed head captured))
        finalHeap ∧
      Dynamic.EnvironmentCopies (CallableIndexedNamedGeneration.source caller.named) environment heap captured
        finalHeap ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word value) finalStore ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
        finalMap finalWorld head.code.sourceNode.type (.closure (formed head captured)) value lowered.type ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) finalMap finalWorld finalHeap
        finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap finalHeap := by
  obtain ⟨value, captured, finalHeap, finalStore, finalMap, finalWorld, sourceTrace, copy, native, represented,
      finalHeaps, maps, worlds, frame, metadata, _transition⟩ :=
    CallableIndexedOwnedLambdaViewHeads.formation_in head profile complete globals slots initial owner prefixZero
      packet.observed packet.carried packet.bundle related agrees nativeTyped
      (CallableIndexedOwnedMethodLambdaValues.includes_original keys registry faults profile) heaps
  exact ⟨value, captured, finalHeap, finalStore, finalMap, finalWorld, sourceTrace, copy, native, represented,
    finalHeaps, maps, worlds, frame, metadata⟩

/-- Full expression leaf effects accompany the same authentic nested packet,
in the formed state that holds the copies. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  Evaluates actual store (lowered.expression.rename ξ) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
      finalMap finalWorld head.code.sourceNode.type lowered.type faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      (CallableIndexedOwnedNestedCanonicalState.protocol owner caller).Relates ⟨initial, packet⟩ reached ∧
      PostAdmission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
        context head.code.sourceNode.type outcome reached

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (typed : ExpressionHasType source context id head.code.sourceNode.type)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  (unique : NodeOccurrencesUnique source)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)) context ⟨initial, packet⟩)

include slots related agrees nativeTyped complete globals prefixZero wellFormed runtime covers locals typed sameSource unique heaps admitted in
/-- Original lambda inversion selects the actual Source closure and same heap;
proved formation and genuine Source preservation supply its admitted post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment heap id outcome after) :
    ∃ result finalStore, ResultAt (actual := actual) (ξ := ξ) head profile owner initial packet outcome after result finalStore := by
  let code := actualCode head environment
  rw [sameSource] at unique trace
  cases trace.sound with
  | value evaluated =>
    rename_i sourceValue
    have original : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        (formed head environment).context (formed head environment).evidence (formed head environment).source
        (formed head environment).captured heap code.id sourceValue after := by
      simpa only [code, actualCode, recaptureCode, formed, CallableIndexedLambdaGeneration.closure, head.identifier] using evaluated
    obtain ⟨sourceCaptured, rfl, copy⟩ := source_value_of_code (values := .initial compiled.compatible.checked)
      (indexed := compiled.indexed) (program := Program.ofChecked compiled.sourceProgram) code unique head.coercions original
    obtain ⟨value, formedCaptured, finalHeap, finalStore, finalMap, finalWorld, sourceTrace, formedCopy, native,
        represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      formation head profile complete globals slots owner prefixZero initial packet related agrees nativeTyped heaps
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formedCopy
    have sourceTrace' : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence source
        environment heap id (.closure (formed head sourceCaptured)) after := by simpa only [sameSource] using sourceTrace
    obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
      ⟨initial, packet⟩ maps worlds frame metadata
    have post := after_expression
      (bridge := CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (context := context) (program := Program.ofChecked compiled.sourceProgram)
      ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
      (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace') frame
    exact ⟨.inRight .word value, finalStore, native, finalMap, finalWorld, .value represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩
  | fault failed =>
    rename_i reason
    have original : Dynamic.ExpressionFaults (Program.ofChecked compiled.sourceProgram)
        (formed head environment).context (formed head environment).evidence (formed head environment).source
        (formed head environment).captured heap code.id reason after := by
      simpa only [code, actualCode, recaptureCode, formed, CallableIndexedLambdaGeneration.closure, head.identifier] using failed
    exact False.elim (excludes_fault_of_code (values := .initial compiled.compatible.checked)
      (indexed := compiled.indexed) (program := Program.ofChecked compiled.sourceProgram) code unique head.coercions original)

include slots related agrees nativeTyped complete globals prefixZero wellFormed runtime covers locals typed sameSource unique heaps admitted in
/-- Determinism identifies the actual native completion. The constructed
Source formation keeps its independently measured grade and same post packet. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment heap id outcome after ∧
      ResultAt (actual := actual) (ξ := ξ) head profile owner initial packet outcome after result finalStore := by
  obtain ⟨value, formedCaptured, finalHeap, formedStore, _finalMap, _finalWorld, sourceTrace, _copy, native,
      _represented, _finalHeaps, _maps, _worlds, _frame, _metadata⟩ :=
    formation head profile complete globals slots owner prefixZero initial packet related agrees nativeTyped heaps
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic completed.sound native
  have original : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compiled.sourceProgram) context evidence source
      environment heap id (.value (.closure (formed head formedCaptured))) finalHeap := by
    simpa only [sameSource] using (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size original
  obtain ⟨actualResult, actualStore, resultAt⟩ := preserves_at head profile complete globals slots owner prefixZero
    initial packet related agrees nativeTyped wellFormed runtime covers locals typed sameSource unique heaps admitted sized
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic resultAt.1 native
  exact ⟨sourceSize, _, finalHeap, sized, resultAt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedOrdinaryLambdaFormation
end
