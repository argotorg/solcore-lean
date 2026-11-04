import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectNativePrefix
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedCallBoundaryReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceTypeRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingFirstCallGateRejection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedStagedCallFaults
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageBoundary
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallCodebookReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionPosts
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservationSupport

/-!
# Staged bounds: indirect calls

Indirect calls in staged bodies: callee and argument prefixes, the two gates, fault dispatch and the application suffix.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionExclusion
/-! Existing compiler receipts exclude output coercions at their original node.
The raw-form shape receipt covers only the explicitly supported raw forms. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionExclusion
open Frontend SourceInference Staging.Recursive

theorem empty_at {source : TypedSource} {id : ExpressionId} {node actual : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (empty : node.coercions = []) (contains : ContainsExpression source id actual) :
    actual.coercions = [] := by
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact (congrArg ExpressionNode.coercions same).trans empty

theorem raw_shape {program : Program} {registry : Registry} {size : Nat} {invocation : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {form : ExpressionForm} {requirements : List RequirementId} {coercions : List SourceInference.CoercionStep}
    {outcome : Outcome}
    (trace : Size.RawForm program registry size invocation context environment before form requirements coercions outcome after) :
    AtomicForm form ∨ ∃ callee ids instantiation, form = .call callee ids (.declaration instantiation) := by
  cases trace with
  | rawAtomicValue atomic _ | rawAtomicFault atomic _ => exact .inl atomic
  | rawDirectArgumentsFault _ _ | rawDirectApplied _ _ _ _ _ => exact .inr ⟨_,_,_,rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionExclusion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds
/-! A semantic or nested stage fault in the actual callee stops the original
indirect parent before any gate or argument runs.
The strict staged child IH supplies the computation and its actual post once;
no full staged meaning or body/application law is a premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functionModel
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel

/-- One failure receipt carries its exact tag, failing Scope and token through
the original sum bind. Actual transient effects remain in after/finalStore. -/
def ResultAt (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) (token : Word)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
  RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type lowered.type
    faults (.fault failure) (.inLeft lowered.type (.word token)) ∧
  GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context compiler.original.type (.fault failure) reached

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The genuine staged parent grade makes the executed callee strictly smaller.
Both semantic and nested stage failures propagate by the same original rule. -/
theorem preserves_callee_fault (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow bridge context model stages invocation certificate faults budget)
    {childSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages childSize
      invocation context environment before callee (.fault failure) after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [childSize]) invocation context environment before id (.fault failure) after ∧
    ∃ token finalStore finalMap finalWorld,
      ResultAt (registry := registry) (faults := faults) (context := context)
        (actual := actual) (ξ := ξ) bridge functionModel compiler initial
        failure after token finalStore finalMap finalWorld := by
  have smaller : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize) (children := [childSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children childSize smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted child
  cases represented with
  | fault matched =>
    have whole := CallableContract.call_callee_failure (result := compiler.resultType)
      (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
      prepared.site.gates native.diagnostics.unknown evaluated
    rw [← prepared.lowered_rename compiler ξ] at whole
    have loweredType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    rw [← loweredType] at whole
    exact ⟨.calleeFault occurrence child, _, finalStore, finalMap, finalWorld, whole, .fault matched,
      finalHeaps, maps, worlds, frame, metadata, reached, related,
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_fault_type post⟩

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The supplied first-bind child is the original strict native computation.
Its independently returned staged Source grade grows by one parent step; the
failure tag/scope, token and exact reached caller state are unchanged. -/
theorem reflects_callee_fault (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow bridge context model stages invocation certificate faults budget)
    {size : Nat} {token : Word} {finalStore : Store}
    (completed : EvaluationSize size actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore)
    (smaller : size < budget) :
    ∃ sourceSize failure after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id (.fault failure) after ∧
      ResultAt (registry := registry) (faults := faults) (context := context)
        (actual := actual) (ξ := ξ) bridge functionModel compiler initial
        failure after token finalStore finalMap finalWorld := by
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children size smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted completed
  cases represented with
  | fault matched =>
    have whole := CallableContract.call_callee_failure (result := compiler.resultType)
      (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
      prepared.site.gates native.diagnostics.unknown completed.sound
    rw [← prepared.lowered_rename compiler ξ] at whole
    have loweredType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    rw [← loweredType] at whole
    exact ⟨Staging.Recursive.Size.stepSize [sourceSize], _, after, finalMap, finalWorld,
      .calleeFault occurrence trace, whole, .fault matched, finalHeaps, maps, worlds, frame, metadata,
      reached, related, CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_fault_type post⟩

end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectNativePrefix
/-! Whole-parent finite native inversion with the strict staged callee IH.
A semantic or nested stage callee fault produces the original parent. A value
retains its original gate and strict suffix for actual argument/application
producers. Source and native grades and the actual reached state remain
independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectNativePrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functionModel
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel

/-- A successful callee keeps the original full receiving-model payload and
its actual reached state. The following guard reads at that same store. -/
def CalleePost (sourceValue : Dynamic.Value) (after : Dynamic.Heap) (carrier : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) finalStore ∧
  GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type sourceValue carrier compiler.calleeCode.type ∧
  GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates initial reached ∧
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context calleeNode.type (.value sourceValue) reached

/-- A callee fault records the actual strict native child and independent
staged Source grade, and constructs the original parent at the same endpoint. -/
def FaultPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize failure token after finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore ∧ nativeSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before callee (.fault failure) after ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [sourceSize]) invocation context environment before id (.fault failure) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
      (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
      bridge functionModel compiler initial failure after token finalStore finalMap finalWorld

/-- A successful callee retains its actual staged trace/post and the original
second bind. Its suffix remains measured at the original strict native budget. -/
def ValuePrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before callee (.value sourceValue) after ∧
    CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functionModel compiler initial
      sourceValue after carrier calleeStore finalMap finalWorld ∧
    CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The actual whole-parent completion yields its strict callee child. That
child uses the staged reflection IH once. Faults keep both exact failure tags;
values keep the original guard/suffix computation and the same reached state. -/
theorem reflects_prefix (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow bridge context model stages invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    FaultPrefix (registry := registry) (faults := faults) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge functionModel compiler initial budget value finalStore ∨
    ValuePrefix (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      bridge functionModel compiler prepared initial budget value finalStore := by
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  have full := completed
  rw [prepared.lowered_rename compiler ξ] at full
  cases CallableIndirectCallBounds.bind_completed full within with
  | failed child childStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
      children _ childStrict certified actualFound actualTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | @fault failure token matched =>
      have whole := CallableContract.call_callee_failure (result := compiler.resultType)
        (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
        prepared.site.gates native.diagnostics.unknown child.sound
      rw [← prepared.lowered_rename compiler ξ] at whole
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      rw [← loweredType] at whole
      left
      refine ⟨_, sourceSize, failure, token, after, finalMap, finalWorld, child, childStrict,
        trace, .calleeFault occurrence trace, ?_, whole, .fault matched, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related,
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_fault_type post⟩
      rw [loweredType]
  | continued child remaining childStrict remainingStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
      children _ childStrict certified actualFound actualTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | value represented =>
      right
      refine ⟨_, sourceSize, _, after, _, _, finalMap, finalWorld, child, childStrict, trace,
        ⟨child.sound, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩, ?_⟩
      cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
      | failed gate gateStrict => exact .failed gate gateStrict
      | continued gate suffixTrace gateStrict suffixStrict => exact .passed gate suffixTrace gateStrict suffixStrict

end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectNativePrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix
/-! The actual staged callee post constructs its original scoped boundary.
The first gate either constructs the exact staged rejection, retaining the
selected original row and exact token, or exposes the real argument helper.
That helper uses the ordered staged argument producer at the same reached
caller state. Application and diagnostic receiver transport follow separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open GenericExpressionMeaning (agree_prefix rename_prefix)

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

include sourceEq found sourceParent tree unique parentTyped in
/-- Original parent typing and the actual ordered compiler tree determine the
raw callee and argument rows. The SourceParent requirements, output coercions
and physical-count cuts remain explicit for this exact compiler receipt. -/
theorem source_rows :
    ∃ rawParameter rawResult,
      calleeNode.type = .function rawParameter rawResult ∧
      ExpressionsHaveTypes invocation.source context ids sourceTypes ∧
      TypeSystem.Ty.productMany sourceTypes = rawParameter ∧
      compiler.original.type = rawResult := by
  have rawTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have rawUnique : NodeOccurrencesUnique source := by
    simpa only [sourceEq] using unique
  have rawParentTyped : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨rawParameter, rawResult, calleeFunction, argumentsTyped, bundle, originalResult⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent rawTree rawUnique rawParentTyped found
  exact ⟨rawParameter, rawResult, calleeFunction,
    by simpa only [sourceEq] using argumentsTyped, bundle, originalResult⟩

private theorem foldlApplication_ne_function
    (head : TypeSystem.Ty) (arguments : List TypeSystem.Ty)
    (head_ne : ∀ parameter result, head ≠ .function parameter result)
    (parameter result : TypeSystem.Ty) :
    arguments.foldl TypeSystem.Ty.application head ≠ .function parameter result := by
  induction arguments generalizing head with
  | nil => exact head_ne parameter result
  | cons argument arguments induction =>
      exact induction (.application head argument)
        (by intro candidateParameter candidateResult equality; cases equality)

private theorem nominal_ne_function
    (declaration : Resolved.DeclarationId) (arguments : List TypeSystem.Ty)
    (parameter result : TypeSystem.Ty) :
    TypeSystem.Ty.nominal declaration arguments ≠ .function parameter result :=
  foldlApplication_ne_function (.constructor (.declaration declaration)) arguments
    (by intro candidateParameter candidateResult equality; cases equality) parameter result

private theorem value_is_function {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {value : Dynamic.Value} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap value (.function parameter result)) : IsFunction value := by
  cases value with
  | closure function => exact .closure function
  | global function => exact .global function
  | builtin function => exact .builtin function
  | constructed instantiation arguments =>
    rcases Dynamic.ValueHasType.constructed_inv typed with
      ⟨same, valid, _⟩ | ⟨_inner, impossible, _⟩
    · cases valid with
      | intro dataType signature dataType_mem signature_mem signature_owner constructor_eq
          substitution_exact substitution_range payloadTypes_eq resultType_eq =>
        have impossible := same.trans resultType_eq
        exact False.elim ((nominal_ne_function dataType.id
          (ParameterSubstitution.orderedArguments instantiation.parameterSubstitution dataType.parameters)
          parameter result) impossible.symm)
    · cases impossible
  | unit | bool | word | integer | product | proxy | mapping => cases typed

include positive caller view originalUnique sourceEq found sourceParent tree unique parentTyped in
/-- The actual callee payload comes from the positive receiving model. Its
Source function type and reached admission supply genuine callable shape;
the original scoped boundary factory then runs at that same payload. -/
theorem scoped_boundary {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (post : CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial
      sourceValue after carrier calleeStore finalMap finalWorld) :
    ∃ before originalMetadata, ContainsExpression sidecar.source prepared.site.call before ∧
      before.form = .call callee ids (.indirect originalMetadata) ∧
      CallView before compiler.original originalMetadata metadata ∧
      BoundaryAt sidecar prepared.site callee ids originalMetadata before sourceValue carrier := by
  obtain ⟨_rawParameter, _rawResult, calleeFunction, _argumentsTyped, _bundle, _originalResult⟩ :=
    source_rows (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  obtain ⟨reached, _related, admitted⟩ := post.2.2.2.2.2.2.2
  have typedSource := CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value admitted |>.1
  rw [calleeFunction] at typedSource
  have actualOrigin := SelectedCompilationCallableOrigins.Origins.origin
    (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
    (faults := semanticFaults) (profile := profile) post.2.1 (value_is_function typedSource)
  exact CallableIndexedOwnedPreparedScopedCallBoundaryReceipts.boundary_at_source_view compiler prepared
    caller view originalUnique actualOrigin

/-- The stage branch retains its actual invocation and occurrence, exact
selected original row/metadata and native word. Its diagnostic representation
is identified later by the receiving codebook, not by changing the failure. -/
def StageRejectedPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld originalNode originalMetadata reason,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before callee (.value sourceValue) after ∧
    CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial
      sourceValue after carrier calleeStore finalMap finalWorld ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    ∃ dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue carrier,
      CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids originalMetadata originalNode dispatch.row ∧
      Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason ∧
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
        (Staging.Recursive.Size.stepSize [sourceSize]) invocation context environment before id
        (.fault (.stage invocation id reason)) after ∧
      value = .inLeft lowered.type (.word (dispatch.reason reason)) ∧ finalStore = calleeStore

/-- A real argument failure retains the cumulative reached state and full
receiving-model relation, with neither semantic nor nested stage tag changed. -/
def ArgumentFaultPrefix (value : Value) (finalStore : Store) : Prop :=
  ∃ calleeSize argumentsSize sourceValue calleeHeap failure after token finalMap finalWorld,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.fault failure) after ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize]) invocation context environment before id (.fault failure) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
      (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
      bridge functions compiler initial failure after token finalStore finalMap finalWorld

/-- Successful arguments retain their independent Source grade and actual
packed payload, raw callee/bundle/original-result rows, reached caller state
and strict original second-gate/application computation. No application trace
or body result is asserted here. -/
def ApplicationPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧
    compiler.original.type = rawResult ∧
  ∃ calleeSize argumentsSize sourceValue calleeHeap sources values carrier argumentsHeap argumentsStore finalMap finalWorld originalNode originalMetadata,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type sourceValue carrier compiler.calleeCode.type ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
    ∃ size, EvaluationSize size (DataPatternValues.packValues values :: .unit :: carrier :: actual) argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ size < budget

private theorem argument_fault_post {failure : Staging.Recursive.Failure} {type : TypeSystem.Ty}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : CallableIndexedOwnedAdmittedStagedExpressionSequence.PostAdmission bridge
      (context := context) (.fault failure) reached) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context type (.fault failure) reached := by
  cases failure with
  | semantic reason => exact ⟨post.rows, by intro _ impossible; cases impossible⟩
  | stage origin call reason => exact post.rows

include positive prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Whole-parent native reflection uses the strict staged callee IH once and
the actual scoped boundary. An accepted gate then invokes the concrete staged
argument fold at its genuine callee endpoint, preserving all transient effects. -/
theorem reflects_arguments (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    CallableIndexedOwnedPreparedStagedIndirectNativePrefix.FaultPrefix
      (registry := registry) (faults := faults) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge functions compiler initial budget value finalStore ∨
    StageRejectedPrefix (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore ∨
    ArgumentFaultPrefix (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (faults := faults) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge profile compiler initial value finalStore ∨
    ApplicationPrefix (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  obtain ⟨rawParameter, rawResult, calleeFunction, argumentsTyped, bundle, originalResult⟩ :=
    source_rows (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  cases CallableIndexedOwnedPreparedStagedIndirectNativePrefix.reflects_prefix bridge functions compiler prepared
      sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed initial admitted
      budget children completed within with
  | inl fault => exact .inl fault
  | inr positive =>
    obtain ⟨nativeSize, calleeSize, sourceValue, calleeHeap, carrier, calleeStore, calleeMap, calleeWorld,
      calleeNative, calleeStrict, calleeTrace, calleePost, gate⟩ := positive
    obtain ⟨original, originalMetadata, _contained, _form, callView, boundary⟩ :=
      scoped_boundary (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
        (tree := tree) (unique := unique) (parentTyped := parentTyped)
        bridge profile compiler prepared initial caller view originalUnique calleePost
    have gateResult :
        (∃ reason, Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason ∧
          ∃ dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue carrier,
            CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids originalMetadata original dispatch.row ∧
            value = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧ finalStore = calleeStore) ∨
        (Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
          ∃ suffixSize, EvaluationSize suffixSize (.unit :: carrier :: actual) calleeStore
            (CallableIndexedOwnedStoredIndirectNativePrefix.suffix prepared.site
              compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
              ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore ∧ suffixSize < budget) := by
      cases boundary with
      | user dispatch selected =>
          cases gate.resolve dispatch with
          | inl rejected =>
              obtain ⟨reason, rejected, valueEq, storeEq, _represented⟩ := rejected
              left
              refine ⟨reason, ?_, dispatch, selected, valueEq, storeEq⟩
              simpa only [guardFrame, prepared.call] using rejected
          | inr accepted =>
              right
              simpa only [guardFrame, prepared.call] using accepted
      | builtin receipt =>
          right
          simpa only [guardFrame, prepared.call] using receipt.resolve_prefix gate
    cases gateResult with
    | inl rejected =>
        obtain ⟨reason, rejected, dispatch, selected, valueEq, storeEq⟩ := rejected
        right; left
        refine ⟨nativeSize, calleeSize, sourceValue, calleeHeap, carrier, calleeStore, calleeMap, calleeWorld,
          original, originalMetadata, reason, calleeNative, calleeStrict, calleeTrace, calleePost, callView,
          dispatch, selected, rejected, .rejected occurrence calleeTrace rejected, ?_, storeEq⟩
        simpa only [loweredType] using valueEq
    | inr accepted =>
        obtain ⟨accepted, suffixSize, suffixTrace, suffixStrict⟩ := accepted
        obtain ⟨_calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ := calleePost
        have argumentLayout : EnvironmentsAgree
            (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
            canonical (Value.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
        have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
          (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
        cases CallableIndirectCallBounds.bind_completed suffixTrace (Nat.le_of_lt suffixStrict) with
        | failed arguments argumentsStrict =>
            have argumentNative := arguments
            rw [← rename_prefix, ← rename_prefix] at argumentNative
            obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, argumentsTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              CallableIndexedOwnedAdmittedStagedExpressionSequence.reflects bridge budget tree unique argumentsTyped children
                (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
                argumentTyped calleeState calleeAdmission.at_value.2 argumentNative argumentsStrict
            cases represented with
            | @fault failure token matched =>
                right; right; left
                refine ⟨calleeSize, argumentsSize, sourceValue, calleeHeap, failure, after, token, finalMap, finalWorld,
                  calleeTrace, accepted, argumentsTrace, .argumentsFault occurrence calleeTrace accepted argumentsTrace,
                  ?_, (by simpa only [loweredType] using completed.sound), .fault matched, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
                  calleeFrame.trans frame, calleeMetadata.trans heapMetadata,
                  reached, callerProtocol.trans calleeRelated related, argument_fault_post bridge post⟩
                simp only [loweredType]
        | continued arguments remaining argumentsStrict remainingStrict =>
            have argumentNative := arguments
            rw [← rename_prefix, ← rename_prefix] at argumentNative
            obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, argumentsTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              CallableIndexedOwnedAdmittedStagedExpressionSequence.reflects bridge budget tree unique argumentsTyped children
                (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
                argumentTyped calleeState calleeAdmission.at_value.2 argumentNative argumentsStrict
            cases represented with
            | @values sources values relatedValues =>
                right; right; right
                exact ⟨rawParameter, rawResult, calleeFunction, bundle, originalResult,
                  calleeSize, argumentsSize, sourceValue, calleeHeap, sources, values, carrier, after, _, finalMap, finalWorld,
                  original, originalMetadata, calleeTrace, accepted, argumentsTrace, relatedValues,
                  GenericHeap.PayloadModel.extend model payload maps worlds, callView, boundary, finalHeaps,
                  calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
                  calleeMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans calleeRelated related, post.at_values⟩,
                  _, remaining, remainingStrict⟩

end Calls
/-- Source function typing excludes data-valued callees before direct dispatch. -/
theorem callable_shape {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {value : Dynamic.Value} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap value (.function parameter result)) : IsFunction value :=
  value_is_function typed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds
/-! Actual first-gate rejection combines the original native failure producer
with the exact receiving stage diagnostic. The callee's concrete reached state
supplies the parent stage post. A strict child proof and the actual reflected
argument prefix feed this constructor; broader dispatch remains separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section Constructor
variable
  (functionModel : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functionModel
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include receiver prepared stagePrepared sourceEq occurrence view guardFrame in
/-- Both the Source parent and native parent stop at the actual callee endpoint.
The literal selected token and receiver lookup establish the stage relation;
the same reached child witness supplies stable rows for the parent. -/
theorem result_at_rejected
    {childSize : Nat} {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (child : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages childSize
      invocation context environment before callee (.value sourceValue) after)
    (post : CalleePost (registry := completion.result.context.registry) (context := context)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      bridge functionModel compiler initial sourceValue after carrier calleeStore finalMap finalWorld)
    {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
    (callView : CallView originalNode compiler.original originalMetadata metadata)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      prepared.site prepared.site.call ids sourceValue carrier)
    (selected : Selected sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
    {reason : Staging.CallGuard.Fault}
    (rejected : Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [childSize]) invocation context environment before id
      (.fault (.stage invocation id reason)) after ∧
    CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
      (registry := completion.result.context.registry) (faults := callFaults) (context := context)
      (actual := actual) (ξ := ξ) bridge functionModel compiler initial
      (.stage invocation id reason) after (dispatch.reason reason) calleeStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, _payload, calleeHeaps, maps, worlds, frame, heapMetadata,
    reached, related, calleeAdmission⟩ := post
  have actualRejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar)
      prepared.site.call ids sourceValue reason := by
    simpa only [guardFrame, prepared.call] using rejected
  have shaped := calleeEvaluation
  rw [dispatch.shape] at shaped
  have whole := prepared.site.lower_stage_failure (result := compiler.resultType)
    (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.row
    (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason)
    dispatch.found (dispatch.rejected actualRejected) shaped
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  have evaluated : Evaluates actual store (lowered.expression.rename ξ)
      (.inLeft lowered.type (.word (dispatch.reason reason))) calleeStore := by
    simpa only [SourceCoreCallableContracts.Callsite.lower, CallStageBoundary.Dispatch.reason,
      prepared.lowered_rename compiler ξ, loweredType] using whole
  have receiving :=
    CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.receiving_staged_post
      (sourceResult := compiler.original.type) (resultCore := lowered.type)
      compiler prepared stagePrepared dispatch selected receiver sourceEq view callView guardFrame
      (by simpa only [prepared.call] using rejected) initial functionModel reached related calleeHeaps
  have represented : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults
      (.fault (.stage invocation id reason)) (.inLeft lowered.type (.word (dispatch.reason reason))) := by
    have common := CallableIndexedOwnedPublicDecodedStagedCallFaults.first_gate_result model receiving.1
    simpa only [prepared.call] using common
  have parentAdmission : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      bridge context compiler.original.type (.fault (.stage invocation id reason)) reached :=
    calleeAdmission.rows
  exact ⟨.rejected occurrence child rejected, evaluated, represented, calleeHeaps,
    maps, worlds, frame, heapMetadata, reached, related, parentAdmission⟩

end Constructor

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include positive receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped in
/-- Strict Source descent supplies the actual successful callee post. Positive
payload and original Source rows construct its scoped boundary. A genuine
rejection excludes the builtin branch and invokes the concrete parent once. -/
theorem preserves_rejected (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate faults budget)
    {childSize : Nat} {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages childSize
      invocation context environment before callee (.value sourceValue) after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget)
    {reason : Staging.CallGuard.Fault}
    (rejected : Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [childSize]) invocation context environment before id
      (.fault (.stage invocation id reason)) after ∧
    ∃ token finalStore finalMap finalWorld,
      CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (context := context)
        (actual := actual) (ξ := ξ) bridge functions compiler initial
        (.stage invocation id reason) after token finalStore finalMap finalWorld := by
  have smaller : childSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := childSize) (children := [childSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by
    rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by
    rw [sourceEq]; exact sourceTyped
  obtain ⟨value, calleeStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, calleeAdmission⟩ :=
    children childSize smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted child
  cases represented with
  | value payload =>
      have actualPost : ∃ carrier, CalleePost (registry := completion.result.context.registry) (context := context)
          (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
          bridge functions compiler initial sourceValue after carrier calleeStore finalMap finalWorld :=
        ⟨_, evaluated, payload, finalHeaps, maps, worlds, frame, heapMetadata,
          reached, related, calleeAdmission⟩
      obtain ⟨carrier, post⟩ := actualPost
      obtain ⟨originalNode, originalMetadata, _contains, _form, callView, boundary⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial caller view originalUnique post
      cases boundary with
      | user dispatch selected =>
          obtain ⟨trace, result⟩ := result_at_rejected bridge receiver compiler prepared stagePrepared
            sourceEq occurrence initial view guardFrame functions child post callView dispatch selected rejected
          exact ⟨trace, dispatch.reason reason, calleeStore, finalMap, finalWorld, result⟩
      | @builtin function carrier row receipt =>
          exact False.elim (Staging.CallBoundary.GuardAccepts.not_rejects
            (.builtin function) rejected)

include receiver prepared stagePrepared sourceEq occurrence view guardFrame in
omit positive in
/-- The real reflected first-gate prefix already retains its strict native
callee and independent Source grade. Its literal selected row supplies the
receiving token, completing this branch at the same final store and witness. -/
theorem reflects_rejected_prefix (budget : Nat) {value : Value} {finalStore : Store}
    (rejectedPrefix : CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.StageRejectedPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial
      budget value finalStore) :
    ∃ sourceSize reason after token finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id (.fault (.stage invocation id reason)) after ∧
      value = .inLeft lowered.type (.word token) ∧
      CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (context := context)
        (actual := actual) (ξ := ξ) bridge functions compiler initial
        (.stage invocation id reason) after token finalStore finalMap finalWorld := by
  obtain ⟨_nativeSize, childSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
    originalNode, originalMetadata, reason, _native, _strict, child, post, callView,
    dispatch, selected, rejected, _trace, valueEq, storeEq⟩ := rejectedPrefix
  subst finalStore
  obtain ⟨trace, result⟩ := result_at_rejected bridge receiver compiler prepared stagePrepared
    sourceEq occurrence initial view guardFrame functions child post callView dispatch selected rejected
  exact ⟨Staging.Recursive.Size.stepSize [childSize], reason, after, dispatch.reason reason,
    finalMap, finalWorld, trace, valueEq, result⟩

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectFaultDispatch
/-! Whole-parent reflection joins the genuine callee, first-gate and ordered-argument fault prefixes. The authentic successful argument suffix remains available for its concrete application producer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectFaultDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual
    headers keys bodyRegistry semanticFaults profile functionModel]
  {certificate : GenericExpressionMeaning.Certificate}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

/-- A fault branch of the actual native parent, with its independently sized
Source derivation and the exact token, reached state and failure tag. -/
def FaultResult (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize failure after token finalMap finalWorld,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before id (.fault failure) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
      (registry := completion.result.context.registry) (faults := callFaults) (context := context)
      (actual := actual) (ξ := ξ) bridge functions compiler initial
      failure after token finalStore finalMap finalWorld

include positive receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped in
/-- The actual whole parent is inverted once. Every reached callee, first-gate
or ordered-argument failure becomes its exact parent result. Successful
arguments retain the authentic application suffix for its concrete producer. -/
theorem reflects_fault_or_application (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    FaultResult (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ)
      bridge compiler initial profile value finalStore ∨
    CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  rcases CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.reflects_arguments
      bridge profile compiler prepared sourceEq occurrence certified found sourceTyped
      environments heaps locals agrees typed initial admitted caller view originalUnique
      guardFrame sourceParent tree unique parentTyped budget children completed within with
    calleeFault | stageRejected | argumentFault | application
  · obtain ⟨_nativeSize, sourceSize, failure, token, after, finalMap, finalWorld,
      _native, _strict, _child, parentTrace, valueEq, post⟩ := calleeFault
    exact .inl ⟨Staging.Recursive.Size.stepSize [sourceSize], failure, after, token,
      finalMap, finalWorld, parentTrace, valueEq, post⟩
  · obtain ⟨sourceSize, reason, after, token, finalMap, finalWorld,
      parentTrace, valueEq, post⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds.reflects_rejected_prefix
        bridge receiver compiler prepared stagePrepared sourceEq occurrence initial
        view guardFrame profile budget stageRejected
    exact .inl ⟨sourceSize, .stage invocation id reason, after, token,
      finalMap, finalWorld, parentTrace, valueEq, post⟩
  · obtain ⟨calleeSize, argumentsSize, sourceValue, calleeHeap, failure, after,
      token, finalMap, finalWorld, _callee, _accepted, _arguments,
      parentTrace, valueEq, post⟩ := argumentFault
    exact .inl ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize],
      failure, after, token, finalMap, finalWorld, parentTrace, valueEq, post⟩
  · exact .inr application

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectFaultDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix
/-! Successful ordered arguments retain the actual successful callee post and Source value typing from the same strict child proof. The authentic original fault branches and reached argument state stay unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open GenericExpressionMeaning (agree_prefix rename_prefix)

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)


open CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix (StageRejectedPrefix ArgumentFaultPrefix)

/-- Successful arguments retain the literal successful callee receipt before the original producer erases it. -/
def ApplicationPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧
    compiler.original.type = rawResult ∧
  ∃ calleeSize argumentsSize sourceValue calleeHeap calleeStore calleeMap calleeWorld sources values carrier argumentsHeap argumentsStore finalMap finalWorld originalNode originalMetadata,
    CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial
      sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld ∧
    Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type sourceValue carrier compiler.calleeCode.type ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
    ∃ size, EvaluationSize size (DataPatternValues.packValues values :: .unit :: carrier :: actual) argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ size < budget

omit positive in
/-- The original application suffix is recovered by forgetting only the additional callee receipt. -/
theorem ApplicationPrefix.to_original {budget : Nat} {value : Value} {finalStore : Store}
    (retained : ApplicationPrefix (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore) :
    CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry)
      (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  obtain ⟨rawParameter, rawResult, functionType, bundle, resultType,
    calleeSize, argumentsSize, sourceValue, calleeHeap, _calleeStore, _calleeMap, _calleeWorld,
    sources, values, carrier, argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode,
    originalMetadata, _calleePost, _valueTyped, tail⟩ := retained
  exact ⟨rawParameter, rawResult, functionType, bundle, resultType,
    calleeSize, argumentsSize, sourceValue, calleeHeap, sources, values, carrier, argumentsHeap,
    argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩

private theorem argument_fault_post {failure : Staging.Recursive.Failure} {type : TypeSystem.Ty}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : CallableIndexedOwnedAdmittedStagedExpressionSequence.PostAdmission bridge
      (context := context) (.fault failure) reached) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context type (.fault failure) reached := by
  cases failure with
  | semantic reason => exact ⟨post.rows, by intro _ impossible; cases impossible⟩
  | stage origin call reason => exact post.rows

include positive prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Whole-parent native reflection uses the strict staged callee IH once and
the actual scoped boundary. An accepted gate then invokes the concrete staged
argument fold at its genuine callee endpoint, preserving all transient effects. -/
theorem reflects_arguments (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    CallableIndexedOwnedPreparedStagedIndirectNativePrefix.FaultPrefix
      (registry := registry) (faults := faults) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge functions compiler initial budget value finalStore ∨
    StageRejectedPrefix (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore ∨
    ArgumentFaultPrefix (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (faults := faults) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge profile compiler initial value finalStore ∨
    ApplicationPrefix (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  obtain ⟨rawParameter, rawResult, calleeFunction, argumentsTyped, bundle, originalResult⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.source_rows (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  cases CallableIndexedOwnedPreparedStagedIndirectNativePrefix.reflects_prefix bridge functions compiler prepared
      sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed initial admitted
      budget children completed within with
  | inl fault => exact .inl fault
  | inr positive =>
    obtain ⟨nativeSize, calleeSize, sourceValue, calleeHeap, carrier, calleeStore, calleeMap, calleeWorld,
      calleeNative, calleeStrict, calleeTrace, calleePost, gate⟩ := positive
    obtain ⟨original, originalMetadata, _contained, _form, callView, boundary⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
        (tree := tree) (unique := unique) (parentTyped := parentTyped)
        bridge profile compiler prepared initial caller view originalUnique calleePost
    have gateResult :
        (∃ reason, Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason ∧
          ∃ dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue carrier,
            CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids originalMetadata original dispatch.row ∧
            value = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧ finalStore = calleeStore) ∨
        (Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
          ∃ suffixSize, EvaluationSize suffixSize (.unit :: carrier :: actual) calleeStore
            (CallableIndexedOwnedStoredIndirectNativePrefix.suffix prepared.site
              compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
              ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore ∧ suffixSize < budget) := by
      cases boundary with
      | user dispatch selected =>
          cases gate.resolve dispatch with
          | inl rejected =>
              obtain ⟨reason, rejected, valueEq, storeEq, _represented⟩ := rejected
              left
              refine ⟨reason, ?_, dispatch, selected, valueEq, storeEq⟩
              simpa only [guardFrame, prepared.call] using rejected
          | inr accepted =>
              right
              simpa only [guardFrame, prepared.call] using accepted
      | builtin receipt =>
          right
          simpa only [guardFrame, prepared.call] using receipt.resolve_prefix gate
    cases gateResult with
    | inl rejected =>
        obtain ⟨reason, rejected, dispatch, selected, valueEq, storeEq⟩ := rejected
        right; left
        refine ⟨nativeSize, calleeSize, sourceValue, calleeHeap, carrier, calleeStore, calleeMap, calleeWorld,
          original, originalMetadata, reason, calleeNative, calleeStrict, calleeTrace, calleePost, callView,
          dispatch, selected, rejected, .rejected occurrence calleeTrace rejected, ?_, storeEq⟩
        simpa only [loweredType] using valueEq
    | inr accepted =>
        obtain ⟨accepted, suffixSize, suffixTrace, suffixStrict⟩ := accepted
        have retainedCalleePost := calleePost
        obtain ⟨_calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ := calleePost
        have argumentLayout : EnvironmentsAgree
            (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
            canonical (Value.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
        have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
          (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
        cases CallableIndirectCallBounds.bind_completed suffixTrace (Nat.le_of_lt suffixStrict) with
        | failed arguments argumentsStrict =>
            have argumentNative := arguments
            rw [← rename_prefix, ← rename_prefix] at argumentNative
            obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, argumentsTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              CallableIndexedOwnedAdmittedStagedExpressionSequence.reflects bridge budget tree unique argumentsTyped children
                (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
                argumentTyped calleeState calleeAdmission.at_value.2 argumentNative argumentsStrict
            cases represented with
            | @fault failure token matched =>
                right; right; left
                refine ⟨calleeSize, argumentsSize, sourceValue, calleeHeap, failure, after, token, finalMap, finalWorld,
                  calleeTrace, accepted, argumentsTrace, .argumentsFault occurrence calleeTrace accepted argumentsTrace,
                  ?_, (by simpa only [loweredType] using completed.sound), .fault matched, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
                  calleeFrame.trans frame, calleeMetadata.trans heapMetadata,
                  reached, callerProtocol.trans calleeRelated related, argument_fault_post bridge post⟩
                simp only [loweredType]
        | continued arguments remaining argumentsStrict remainingStrict =>
            have argumentNative := arguments
            rw [← rename_prefix, ← rename_prefix] at argumentNative
            obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, argumentsTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              CallableIndexedOwnedAdmittedStagedExpressionSequence.reflects bridge budget tree unique argumentsTyped children
                (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
                argumentTyped calleeState calleeAdmission.at_value.2 argumentNative argumentsStrict
            cases represented with
            | @values sources values relatedValues =>
                right; right; right
                exact ⟨rawParameter, rawResult, calleeFunction, bundle, originalResult,
                  calleeSize, argumentsSize, sourceValue, calleeHeap, calleeStore, calleeMap, calleeWorld,
                  sources, values, carrier, after, _, finalMap, finalWorld,
                  original, originalMetadata, retainedCalleePost, calleeAdmission.at_value.1,
                  calleeTrace, accepted, argumentsTrace, relatedValues,
                  GenericHeap.PayloadModel.extend model payload maps worlds, callView, boundary, finalHeaps,
                  calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
                  calleeMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans calleeRelated related, post.at_values⟩,
                  _, remaining, remainingStrict⟩

end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeFaultDispatch
/-! The actual whole native parent retains its successful callee receipt through ordered arguments. Fault branches preserve the original result; the successful branch exposes the same reached suffix and callee typing to its application producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeFaultDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedIndirectFaultDispatch (FaultResult)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual
    headers keys bodyRegistry semanticFaults profile functionModel]
  {certificate : GenericExpressionMeaning.Certificate}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include positive receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped in
/-- The actual whole parent is inverted once. Every reached callee, first-gate
or ordered-argument failure becomes its exact parent result. Successful
arguments retain the authentic application suffix for its concrete producer. -/
theorem reflects_fault_or_application (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    FaultResult (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ)
      bridge compiler initial profile value finalStore ∨
    CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  rcases CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix.reflects_arguments
      bridge profile compiler prepared sourceEq occurrence certified found sourceTyped
      environments heaps locals agrees typed initial admitted caller view originalUnique
      guardFrame sourceParent tree unique parentTyped budget children completed within with
    calleeFault | stageRejected | argumentFault | application
  · obtain ⟨_nativeSize, sourceSize, failure, token, after, finalMap, finalWorld,
      _native, _strict, _child, parentTrace, valueEq, post⟩ := calleeFault
    exact .inl ⟨Staging.Recursive.Size.stepSize [sourceSize], failure, after, token,
      finalMap, finalWorld, parentTrace, valueEq, post⟩
  · obtain ⟨sourceSize, reason, after, token, finalMap, finalWorld,
      parentTrace, valueEq, post⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds.reflects_rejected_prefix
        bridge receiver compiler prepared stagePrepared sourceEq occurrence initial
        view guardFrame profile budget stageRejected
    exact .inl ⟨sourceSize, .stage invocation id reason, after, token,
      finalMap, finalWorld, parentTrace, valueEq, post⟩
  · obtain ⟨calleeSize, argumentsSize, sourceValue, calleeHeap, failure, after,
      token, finalMap, finalWorld, _callee, _accepted, _arguments,
      parentTrace, valueEq, post⟩ := argumentFault
    exact .inl ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize],
      failure, after, token, finalMap, finalWorld, parentTrace, valueEq, post⟩
  · exact .inr application

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeFaultDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix
/-! The original accepted second gate exposes the actual application child.
Pure variable and projection reads normalize its environment without changing
the child's grade, store, closure body or captured values. The same literal
application can be inserted back into the original suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix
open Core Frontend SourceInference CoreProof
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)

/-- Only the pure caller prefix is changed; the body is the supplied original
native child and keeps exactly the same grade and reached store. -/
theorem application_to_payload {size : Nat} {carrier packed value : Value}
    {actual : Environment} {before after : Store}
    (completed : EvaluationSize size (.unit :: packed :: .unit :: carrier :: actual) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after) :
    EvaluationSize size [carrier, packed] before CallableIndexedLambdaCalls.applyPayload value after := by
  cases completed with
  | apply selected argument body =>
      cases selected with
      | second tagged =>
          cases tagged with
          | first lookup =>
              cases lookup with
              | var found =>
                  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at found
                  cases Option.some.inj found
                  cases argument with
                  | var read =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at read
                      cases Option.some.inj read
                      exact .apply (.second (.first (.var rfl))) (.var rfl) body

/-- The physical prefix can be restored around the same application child. -/
theorem application_from_payload {size : Nat} {carrier packed value : Value}
    {actual : Environment} {before after : Store}
    (completed : EvaluationSize size [carrier, packed] before
      CallableIndexedLambdaCalls.applyPayload value after) :
    EvaluationSize size (.unit :: packed :: .unit :: carrier :: actual) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after := by
  cases completed with
  | apply selected argument body =>
      cases selected with
      | second tagged =>
          cases tagged with
          | first lookup =>
              cases lookup with
              | var found =>
                  simp only [List.getElem?_cons_zero] at found
                  cases Option.some.inj found
                  cases argument with
                  | var read =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at read
                      cases Option.some.inj read
                      exact .apply (.second (.first (.var rfl))) (.var rfl) body

section Gate
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : SourceInference.IndirectCallResolution}
  {node : SourceInference.ExpressionNode} {row : SourceCoreStageCodebook.Decision}
  {raw carrier packed : Value} {tag unknown : Word} {actual : Environment} {store : Store}
  (shape : carrier = .pair raw (.word tag))
  (selected : Selected sidecar site callee ids metadata node row)
  (found : site.rowAt? tag = some row)
  (count : row.entry.parameterCount = ids.length)

include shape selected found count in
/-- The selected physical count determines the original second decision. -/
theorem accepted_gate :
    Evaluates (packed :: .unit :: carrier :: actual) store
      (CallableContract.dispatch site.gates .beforeApplication unknown (.second (.var 2)))
      (.inRight .word .unit) store := by
  have read : Evaluates (packed :: .unit :: carrier :: actual) store
      (.second (.var 2)) (.word tag) store := by
    rw [shape]
    exact .second (.var rfl)
  have gate := site.dispatch_known .beforeApplication unknown tag row found read
  rw [SourceCoreCallableContracts.reason_accepted row site.reasonAt .beforeApplication
    (row.afterArguments_ok (count.trans selected.argument_count.symm))] at gate
  simpa only [CallableContract.resultValue] using gate

include shape selected found count in
/-- A genuine suffix completion has a strictly smaller payload application.
The accepted guard runs at the actual argument store and changes no state. -/
theorem reflects_suffix {budget size : Nat} {result : Ty} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (packed :: .unit :: carrier :: actual) store
      (LanguageResult.bind result
        (CallableContract.dispatch site.gates .beforeApplication unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : size ≤ budget) :
    ∃ applicationSize, applicationSize < budget ∧
      EvaluationSize applicationSize [carrier, packed] store
        CallableIndexedLambdaCalls.applyPayload value finalStore := by
  have gate := accepted_gate (packed := packed) (actual := actual) (store := store)
    (unknown := unknown) shape selected found count
  cases CallableIndirectCallBounds.bind_completed completed within with
  | failed failed strict =>
      have same := (evaluation_deterministic failed.sound gate).1
      cases same
  | continued guard application guardStrict applicationStrict =>
      obtain ⟨same, sameStore⟩ := evaluation_deterministic guard.sound gate
      cases same
      cases sameStore
      exact ⟨_, applicationStrict, application_to_payload application⟩

include shape selected found count in
/-- The concrete payload application plugs into the original accepted suffix
once, at the unchanged argument store. No body law is a static premise. -/
theorem preserves_suffix {result : Ty} {value : Value} {finalStore : Store}
    (application : Evaluates [carrier, packed] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    Evaluates (packed :: .unit :: carrier :: actual) store
      (LanguageResult.bind result
        (CallableContract.dispatch site.gates .beforeApplication unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore := by
  obtain ⟨size, sized⟩ := evaluation_has_size application
  exact LanguageResult.bind_success result
    (accepted_gate (packed := packed) (actual := actual) (store := store)
      (unknown := unknown) shape selected found count)
    (application_from_payload (actual := actual) sized).sound

end Gate
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds
/-! The physical second decision follows the actual successful ordered argument
prefix. A count mismatch invokes the existing semantic application-arity rule;
the first guard's scoped stage failure is unchanged and handled separately.
The original Selected row determines the word, while genuine receiving issuance
interprets it at the same reached argument state. This construction is separate
from the integrated NEW12 group. NamedOrigin is only authentic Header/SourceAt provenance, not a
count equality, application result, body trace or completed meaning law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

/-- The genuine global branch retains the same original BodyInstance. -/
def NamedOrigin (compiled : SourceCoreUnifiedCompilation.Compiled)
    (sourceValue : Dynamic.Value) : Prop :=
  ∀ function, sourceValue = .global function →
    ∃ (header : Header compiled (Program.ofChecked compiled.sourceProgram))
      (rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment), NamedSourceAt header rawD function

section SourceBoundary
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before calleeHeap argumentsHeap : Dynamic.Heap}
  {call callee : ExpressionId} {ids : List ExpressionId}
  {metadata originalMetadata : IndirectCallResolution} {originalNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {sourceValue : Dynamic.Value} {carrier : Value} {sources : List Dynamic.Value}
  {calleeSize argumentsSize : Nat}

/-- Real closure, global and builtin bindings supply each physical parameter
list. The conditional conclusion is constructed from the actual two Source
prefixes; no trace is retained in a static compiler certificate. -/
theorem source_at_boundary
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (occurrence : Staging.Recursive.Occurrence invocation call (.call callee ids (.indirect metadata)))
    (uncoerced : metadata.argumentCoercions = [])
    (sourceArity : ids.length = metadata.argumentCount)
    (child : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      calleeSize invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids sourceValue)
    (arguments : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages
      argumentsSize invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (boundary : BoundaryAt sidecar site callee ids originalMetadata originalNode sourceValue carrier)
    (named : NamedOrigin compiled sourceValue) :
    ∃ raw tag row, carrier = .pair raw (.word tag) ∧
      Selected sidecar site callee ids originalMetadata originalNode row ∧ site.rowAt? tag = some row ∧
      ∀ (_different : row.entry.parameterCount ≠ ids.length),
        Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
          (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []])
          invocation context environment before call
          (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length))) argumentsHeap := by
  cases boundary with
  | user dispatch selected =>
    cases (CallableLedger.frame sidecar).userCallable dispatch.bound with
    | closure function =>
      have physical := CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected
      refine ⟨dispatch.function, dispatch.contract, dispatch.row, dispatch.shape, selected, dispatch.found, ?_⟩
      intro different
      have mismatch : function.parameters.length ≠ ids.length := by
        simpa only [physical] using different
      simpa only [physical] using
        CallableIndexedOwnedPreparedSecondCallGateRejection.closure_source
          occurrence uncoerced sourceArity arguments child accepted mismatch
    | global function =>
      obtain ⟨header, rawD, sourceAt⟩ := named function rfl
      have physical := CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count
        sourceAt caller dispatch selected
      refine ⟨dispatch.function, dispatch.contract, dispatch.row, dispatch.shape, selected, dispatch.found, ?_⟩
      intro different
      have mismatch : header.function.parameters.length ≠ ids.length := by
        simpa only [physical] using different
      simpa only [physical] using
        CallableIndexedOwnedPreparedSecondCallGateRejection.named_source
          occurrence uncoerced sourceArity arguments sourceAt child accepted mismatch
  | builtin receipt =>
    rename_i function row
    obtain ⟨raw, shape⟩ := receipt.shape
    refine ⟨raw, _, _, shape, receipt.selected, receipt.selected.found, ?_⟩
    intro different
    have physical := receipt.parameter_count
    have mismatch : function.id.parameterTypes.length ≠ ids.length := by simpa only [physical] using different
    simpa only [physical] using
      CallableIndexedOwnedPreparedSecondCallGateRejection.builtin_source
        occurrence uncoerced sourceArity arguments child mismatch
end SourceBoundary

section NativeSuffix
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {node : ExpressionNode} {row : SourceCoreStageCodebook.Decision}
  {raw carrier packed : Value} {tag unknown : Word} {actual : Environment}
  {argumentsStore finalStore : Store} {result : Ty} {size : Nat} {value : Value}

/-- Pure second dispatch fixes its original word and retains the argument
store. There is no application evaluation in this rejection branch. -/
theorem rejected_suffix
    (shape : carrier = .pair raw (.word tag))
    (selected : Selected sidecar site callee ids metadata node row)
    (found : site.rowAt? tag = some row)
    (different : row.entry.parameterCount ≠ ids.length)
    (completed : EvaluationSize size (packed :: .unit :: carrier :: actual) argumentsStore
      (LanguageResult.bind result (CallableContract.dispatch site.gates .beforeApplication unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore) :
    value = .inLeft result (.word (site.reasonAt row.caller row.call row.entry.id .beforeApplication
      (.argumentArityMismatch row.entry.parameterCount ids.length))) ∧ finalStore = argumentsStore := by
  have read : Evaluates (packed :: .unit :: carrier :: actual) argumentsStore
      (.second (.var 2)) (.word tag) argumentsStore := by
    rw [shape]
    exact .second (.var rfl)
  have gate := CallableContract.dispatch_evaluates site.gates .beforeApplication unknown tag read
  rw [CallableIndexedOwnedPreparedSecondCallGateRejection.rejected_gate selected found different unknown,
    CallableContract.resultValue] at gate
  exact evaluation_deterministic completed.sound (LanguageResult.bind_failure result gate)
end NativeSuffix

section WholeParent
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (sourceParent : SourceParent compiler)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "publicFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include caller occurrence sourceParent preparedStages receiver in
omit positive in
/-- The actual selected count decides the branch internally. Successful
arguments already carry their real independent grades and reached admission.
The mismatch constructs Source arity, its literal receiver lookup and the same
whole-parent fault post. The equal-count alternative retains only that actual
row fact for the separate application producer. -/
theorem classify_application_prefix {budget size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    («prefix» : CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore)
    (namedOrigins : ∀ {sourceValue carrier finalMap finalWorld},
      GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
        sourceValue carrier compiler.calleeCode.type → NamedOrigin compiled sourceValue) :
    ∃ originalNode originalMetadata row,
      Selected sidecar prepared.site callee ids originalMetadata originalNode row ∧
      (row.entry.parameterCount = ids.length ∨
        ∃ sourceSize after token finalMap finalWorld,
          Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
            invocation context environment before id
            (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length))) after ∧
          value = .inLeft lowered.type (.word token) ∧
          CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
            (registry := completion.result.context.registry) (faults := publicFaults) (context := context)
            (actual := actual) (ξ := ξ) bridge functions compiler initial
            (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)) after token finalStore finalMap finalWorld) := by
  obtain ⟨rawParameter, rawResult, _calleeType, _bundle, _originalResult,
    calleeSize, argumentsSize, sourceValue, calleeHeap, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    child, accepted, arguments, _representedValues, representedCallee, _callView, boundary,
    finalHeaps, maps, worlds, frame, metadataExtension, ⟨reached, related, admitted⟩,
    suffixSize, suffix, _strict⟩ := «prefix»
  obtain ⟨raw, tag, row, shape, selected, found, sourceFault⟩ :=
    source_at_boundary caller occurrence compiler.argumentCoercions sourceParent.arity
      child accepted arguments boundary (namedOrigins representedCallee)
  refine ⟨originalNode, originalMetadata, row, selected, ?_⟩
  by_cases same : row.entry.parameterCount = ids.length
  · exact .inl same
  · have lowerType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    obtain ⟨sameValue, sameStore⟩ := rejected_suffix shape selected found same suffix
    cases sameStore
    obtain ⟨represented, keptHeaps, keptState, sameState, keptRelated⟩ :=
      CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
        compiler prepared preparedStages selected receiver initial functions reached related finalHeaps
        (sourceResult := compiler.original.type) (resultCore := lowered.type) same
    cases sameState
    refine .inr ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
      argumentsHeap, prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount ids.length),
      finalMap, finalWorld, sourceFault same, ?_, ?_⟩
    · simpa only [lowerType] using sameValue
    · refine ⟨?_, CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model represented,
        keptHeaps, maps, worlds, frame, metadataExtension, reached, keptRelated, ?_⟩
      · simpa only [sameValue, lowerType] using completed.sound
      · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
        exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩
end WholeParent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentFaultBounds
/-! The original indirect parent stops at a real argument failure. Its strict
callee and ordered argument hypotheses run at their actual reached states.
The first gate is reconstructed from the authentic scoped boundary; semantic
and nested stage failures retain the same tag, token and transient effects. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include guardFrame in
omit positive in
/-- The real original row supplies first-gate success at the callee store.
No native acceptance or verdict is added to a compiler certificate. -/
theorem first_gate {sourceValue : Dynamic.Value} {carrier : Value}
    {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
    (boundary : BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (calleeStore : Store) :
    Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore := by
  cases boundary with
  | user dispatch selected =>
      have passed := dispatch.accepted (by simpa only [guardFrame, prepared.call] using accepted)
      have read : Evaluates (carrier :: actual) calleeStore (.second (.var 0))
          (.word dispatch.contract) calleeStore := by
        exact .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
      have gate := prepared.site.dispatch_known .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
        dispatch.contract dispatch.row dispatch.found read
      rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeArguments passed] at gate
      simpa only [CallableContract.resultValue] using gate
  | builtin receipt =>
      exact receipt.first_gate compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown actual calleeStore

include positive prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Strict Source descent constructs the callee and argument computations.
The argument fold runs after the accepted first gate and its actual effects
are the parent post; the second gate and application are never evaluated. -/
theorem preserves_argument_fault (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate faults budget)
    {calleeSize argumentsSize : Nat} {sourceValue : Dynamic.Value} {calleeHeap after : Dynamic.Heap}
    {failure : Staging.Recursive.Failure}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.fault failure) after)
    (within : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize]) invocation context environment before id
      (.fault failure) after ∧
    ∃ token finalStore finalMap finalWorld,
      CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
        (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
        bridge functions compiler initial failure after token finalStore finalMap finalWorld := by
  have calleeStrict : calleeSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := calleeSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have argumentsStrict : argumentsSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := argumentsSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, calleeStore, calleeMap, calleeWorld, calleeEvaluated, representation, calleeHeaps,
    calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ :=
    children calleeSize calleeStrict certified actualFound actualTyped environments heaps locals agrees typed initial admitted calleeTrace
  cases representation with
  | value payload =>
      have calleePost : ∃ carrier, CalleePost (registry := registry) (context := context)
          (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
          bridge functions compiler initial sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld :=
        ⟨_, calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩
      obtain ⟨carrier, post⟩ := calleePost
      obtain ⟨calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
        calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ := post
      obtain ⟨originalNode, originalMetadata, _contains, _form, _callView, boundary⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial caller view originalUnique
          ⟨calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
            calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩
      obtain ⟨_rawParameter, _rawResult, _functionType, argumentsTyped, _bundle, _result⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.source_rows
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
      have argumentLayout : EnvironmentsAgree
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
          canonical (.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
      have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
        (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
      obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, postAdmission⟩ :=
        CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_fault bridge budget tree unique argumentsTyped children
          (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
          argumentTyped calleeState calleeAdmission.at_value.2 argumentsTrace (Nat.le_of_lt argumentsStrict)
      have gate := first_gate (actual := actual) compiler prepared guardFrame boundary accepted calleeStore
      have whole : Evaluates actual store
          (CallableContract.call prepared.site.gates
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
            (compiler.calleeCode.expression.rename ξ)
            ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ))
          (.inLeft compiler.resultType (.word token)) finalStore := by
        apply LanguageResult.bind_success compiler.resultType calleeEvaluated
        apply LanguageResult.bind_success compiler.resultType gate
        apply LanguageResult.bind_failure compiler.resultType
        simpa only [← rename_prefix, ← rename_prefix] using argumentsEvaluated
      rw [← prepared.lowered_rename compiler ξ] at whole
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      rw [← loweredType] at whole
      have parentAdmission : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge context compiler.original.type (.fault failure) reached := by
        cases failure with
        | semantic reason => exact ⟨postAdmission.rows, by intro _ impossible; cases impossible⟩
        | stage origin call reason => exact postAdmission.rows
      exact ⟨.argumentsFault occurrence calleeTrace accepted argumentsTrace,
        token, finalStore, finalMap, finalWorld, whole, .fault matched, finalHeaps,
        calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
        calleeMetadata.trans heapMetadata, reached, callerProtocol.trans calleeRelated related, parentAdmission⟩

omit positive in
/-- The constructive whole argument-prefix reflection already contains the
actual parent trace and reached failure receipt. This branch exposes the
independent Source grade without rebuilding or relabeling the child failure. -/
theorem reflects_argument_fault_prefix {value : Value} {finalStore : Store}
    (reflected : CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.ArgumentFaultPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry)
      (faults := faults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore) :
    ∃ sourceSize failure after token finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id (.fault failure) after ∧
      value = .inLeft lowered.type (.word token) ∧
      CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
        (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
        bridge functions compiler initial failure after token finalStore finalMap finalWorld := by
  obtain ⟨calleeSize, argumentsSize, _sourceValue, _calleeHeap, failure, after, token, finalMap, finalWorld,
    _callee, _accepted, _arguments, parent, sameValue, result⟩ := reflected
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize], failure, after, token,
    finalMap, finalWorld, parent, sameValue, result⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectValuesPrefix
/-! Source preservation constructs the callee and ordered argument prefix
at their actual reached states. It retains callee typing and its complete
post for builtin and user application. The application itself follows later. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectValuesPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


/-- Both native prefix actions use the same represented callee and argument
packet. The callee post is retained before the argument effects are composed. -/
def ValuesPrefix (sourceValue : Dynamic.Value) (calleeHeap argumentsHeap : Dynamic.Heap)
    (sources : List Dynamic.Value) : Prop :=
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧ compiler.original.type = rawResult ∧
  ∃ calleeStore calleeMap calleeWorld carrier values argumentsStore finalMap finalWorld
      originalNode originalMetadata,
    CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial
      sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld ∧
    Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type ∧
    Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore ∧
    Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes
      (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
      sourceValue carrier compiler.calleeCode.type ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached

include positive prepared sourceEq certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Strict callee preservation and the real ordered argument fold construct
the full prefix once. The returned admission belongs to the argument endpoint. -/
theorem preserves_values (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate faults budget)
    {calleeSize argumentsSize : Nat} {sourceValue : Dynamic.Value}
    {calleeHeap argumentsHeap : Dynamic.Heap} {sources : List Dynamic.Value}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (within : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget) :
    ValuesPrefix (functionModel := functionModel) (registry := registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources := by
  have calleeStrict : calleeSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := calleeSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have argumentsStrict : argumentsSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := argumentsSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, calleeStore, calleeMap, calleeWorld, calleeEvaluated, representation, calleeHeaps,
    calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ :=
    children calleeSize calleeStrict certified actualFound actualTyped environments heaps locals agrees typed initial admitted calleeTrace
  cases representation with
  | value payload =>
      rename_i carrier
      have post : CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
          (calleeNode := calleeNode) bridge functions compiler initial
          sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld :=
        ⟨calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩
      have sourceValueTyped : Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type :=
        calleeAdmission.at_value.1
      obtain ⟨originalNode, originalMetadata, _contains, _form, callView, boundary⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial caller view originalUnique post
      obtain ⟨rawParameter, rawResult, functionType, argumentsTyped, bundle, resultType⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.source_rows
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
      have argumentLayout : EnvironmentsAgree
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
          canonical (.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
      have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
        (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
      obtain ⟨values, argumentsStore, finalMap, finalWorld, argumentsEvaluated, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, postAdmission⟩ :=
        CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_values bridge budget tree unique argumentsTyped children
          (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
          argumentTyped calleeState calleeAdmission.at_value.2 argumentsTrace (Nat.le_of_lt argumentsStrict)
      have gate := CallableIndexedOwnedPreparedStagedIndirectArgumentFaultBounds.first_gate
        (actual := actual) compiler prepared guardFrame boundary accepted calleeStore
      exact ⟨rawParameter, rawResult, functionType, bundle, resultType, calleeStore, calleeMap, calleeWorld,
        carrier, values, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
        post, sourceValueTyped, gate, argumentsEvaluated, represented,
        GenericHeap.PayloadModel.extend model payload maps worlds, callView, boundary, finalHeaps,
        calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
        calleeMetadata.trans heapMetadata, reached, callerProtocol.trans calleeRelated related,
        postAdmission.at_values⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectValuesPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSourcePrefixDispatch
/-! The original recursively staged indirect parent selects its actual executed
prefix. Faults construct full native parent results from strict child hypotheses;
successful arguments retain the original application trace and real native
prefix. No application execution law is supplied to the classifier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSourcePrefixDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

private inductive SourcePrefix (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (call callee : ExpressionId) (ids : List ExpressionId) (metadata : IndirectCallResolution) :
    Nat → Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | calleeFault {childSize failure after}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.fault failure) after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault failure) after
  | notCallable {childSize value after}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) after)
      (invalid : ¬ Dynamic.CallableValue value) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault (.semantic .notCallable)) after
  | rejected {childSize value after reason}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) after)
      (rejected : Staging.CallBoundary.GuardRejects invocation.guards call ids value reason) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault (.stage invocation call reason)) after
  | argumentsFault {childSize argumentsSize value middle after failure}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) middle)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment middle ids (.fault failure) after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize]) (.fault failure) after
  | sourceArity {childSize argumentsSize value middle after values}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) middle)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment middle ids (.values values) after)
      (mismatch : ids.length ≠ metadata.argumentCount) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize])
        (.fault (.semantic (.argumentArityMismatch metadata.argumentCount ids.length))) after
  | applied {childSize argumentsSize applicationSize value calleeHeap argumentsHeap after values outcome}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) calleeHeap)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment calleeHeap ids (.values values) argumentsHeap)
      (called : Staging.Recursive.Size.Applies program stages applicationSize invocation context
        argumentsHeap value values outcome after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize, applicationSize]) outcome after

private theorem source_prefix
    {program : Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {size : Nat} {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (trace : Staging.Recursive.Size.Expression program stages size invocation context
      environment before id outcome after) :
    SourcePrefix program stages invocation context environment before id callee ids metadata size outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm requirements}, Staging.Recursive.Occurrence invocation id actualForm requirements →
      actualForm = .call callee ids (.indirect metadata) := by
    intro actualForm requirements occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have actual := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actual] at actualForm
      cases actualForm
  | calleeFault occurrence child =>
      cases occurrence_form occurrence
      exact .calleeFault child
  | notCallable occurrence child invalid =>
      cases occurrence_form occurrence
      exact .notCallable child invalid
  | rejected occurrence child rejected =>
      cases occurrence_form occurrence
      exact .rejected child rejected
  | argumentsFault occurrence child accepted arguments =>
      cases occurrence_form occurrence
      exact .argumentsFault child accepted arguments
  | sourceArity occurrence child accepted arguments mismatch =>
      cases occurrence_form occurrence
      exact .sourceArity child accepted arguments mismatch
  | applied occurrence _uncoerced child accepted arguments _arity called =>
      cases occurrence_form occurrence
      exact .applied child accepted arguments called
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _ => cases occurrence_form occurrence

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

/-- The actual failed Source parent already supplies its original grade,
outcome and heap. This is the native result and complete caller post at that
same endpoint, constructed by strict child preservation. -/
def NativeResultAt (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ value finalStore finalMap finalWorld,
    Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type
      lowered.type callFaults outcome value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context compiler.original.type outcome reached

/-- The successful prefix keeps the actual Source application and its strict
grade, together with the constructed original native callee/arguments and
complete reached admission. It contains no native application law. -/
def ApplicationAt (budget size : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap sources,
    size = Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize] ∧
    applicationSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after ∧
    CallableIndexedOwnedPreparedStagedIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial
      sourceValue calleeHeap argumentsHeap sources

include positive prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver in
/-- The literal original Source trace selects a branch once. Its three prefix
failure constructors produce the complete native parent. The actual successful
argument endpoint is retained for the independent application producer. -/
theorem preserves_fault_or_application (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate callFaults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    NativeResultAt (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) bridge profile compiler initial outcome after ∨
    ApplicationAt (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget size outcome after := by
  have parentFound : invocation.source.lookupExpression? id = some compiler.original := by
    rw [sourceEq]
    exact compiler.found
  have selected := source_prefix unique parentFound compiler.originalForm trace
  cases selected with
  | calleeFault child =>
    obtain ⟨_parent, token, finalStore, finalMap, finalWorld, result⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.preserves_callee_fault
        bridge functions compiler prepared sourceEq occurrence certified found sourceTyped
        environments heaps locals agrees typed initial admitted budget children child within
    exact .inl ⟨.inLeft lowered.type (.word token), finalStore, finalMap, finalWorld, result⟩
  | @notCallable childSize sourceValue after child invalid =>
    have smaller : childSize < budget := Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize
      (child := childSize) (children := [childSize]) (by simp)) within
    have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
    have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
      children _ smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | value payload =>
      obtain ⟨_originalNode, _originalMetadata, _contains, _form, _view, boundary⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial caller view originalUnique
          ⟨evaluated, payload, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
      cases boundary with
      | user dispatch _ =>
        have callable := (CallableLedger.frame sidecar).userCallable dispatch.bound
        cases callable <;> exact False.elim (invalid trivial)
      | builtin _ => exact False.elim (invalid trivial)
  | rejected child rejected =>
    obtain ⟨_parent, token, finalStore, finalMap, finalWorld, result⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds.preserves_rejected
        bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame
        profile certified found sourceTyped environments heaps locals agrees typed admitted
        caller originalUnique sourceParent tree unique parentTyped budget children child within rejected
    exact .inl ⟨.inLeft lowered.type (.word token), finalStore, finalMap, finalWorld, result⟩
  | argumentsFault child accepted arguments =>
    obtain ⟨_parent, token, finalStore, finalMap, finalWorld, result⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectArgumentFaultBounds.preserves_argument_fault
        bridge profile compiler prepared sourceEq occurrence certified found sourceTyped environments heaps locals
        agrees typed initial admitted caller view originalUnique guardFrame sourceParent tree unique parentTyped
        budget children child accepted arguments within
    exact .inl ⟨.inLeft lowered.type (.word token), finalStore, finalMap, finalWorld, result⟩
  | sourceArity _ _ _ mismatch => exact False.elim (mismatch sourceParent.arity)
  | @applied calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap after sources outcome child accepted arguments called =>
    have prefixBound : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget := by
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within ⊢
      omega
    have strict : applicationSize < budget := Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize
      (child := applicationSize) (children := [calleeSize, argumentsSize, applicationSize]) (by simp)) within
    have constructedPrefix := CallableIndexedOwnedPreparedStagedIndirectValuesPrefix.preserves_values
      bridge profile compiler prepared sourceEq certified found sourceTyped environments heaps locals agrees
      typed initial admitted caller view originalUnique guardFrame sourceParent tree unique parentTyped
      budget children child accepted arguments prefixBound
    exact .inr ⟨_, _, _, _, _, _, _, rfl, strict, child, accepted, arguments, called, constructedPrefix⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSourcePrefixDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedExpressionSource
/-! A nonempty original output path determines the staged raw-form and suffix
branches. Successful raw evaluation supplies genuine reached Source typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedExpressionSource
open Core Frontend SourceInference

variable {program : Program} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  {id : ExpressionId} {node : ExpressionNode}
  (found : invocation.source.lookupExpression? id = some node)
  (unique : NodeOccurrencesUnique invocation.source)

include found unique

private theorem same {other : ExpressionNode}
    (contains : ContainsExpression invocation.source id other) : other = node :=
  Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)

private theorem excludes (nonempty : node.coercions ≠ []) {other : ExpressionNode}
    (contains : ContainsExpression invocation.source id other) (empty : other.coercions = []) : False :=
  nonempty ((congrArg ExpressionNode.coercions (same found unique contains)).symm.trans empty)

private theorem excludes_occurrence (nonempty : node.coercions ≠ [])
    {form : ExpressionForm} {requirements : List RequirementId}
    (occurrence : Staging.Recursive.Occurrence invocation id form requirements) : False := by
  obtain ⟨other, contains, _form, _requirements, empty⟩ := occurrence
  exact excludes found unique nonempty contains empty

/-- A generalized read selects its actual descriptor before the original
coercion path. Its requirement failure retains the unchanged Source heap. -/
inductive GeneralizedBranch (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (node : ExpressionNode) :
    Nat → Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | value {pathSize : Nat} {name : String} {binder : Resolved.LocalId}
      {owned : List RequirementId} {location : Dynamic.Location} {cell : Dynamic.Cell}
      {function : Dynamic.GeneralizedClosure} {substitution : TypeSystem.Substitution}
      {produced : Dynamic.EvidenceEnvironment} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
      (form : node.form = .reference name (.local binder))
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned)
      (lookup : Dynamic.Environment.LooksUp environment binder location)
      (read : Dynamic.Heap.Reads before location cell)
      (descriptor : cell.generalized = some function)
      (fields : Dynamic.RuntimeContextFields function.definitionContext context)
      (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context invocation.evidence
        function.binder node.rawType owned substitution produced)
      (path : Staging.Recursive.Size.CoercionPath program stages pathSize invocation context before node.coercions
        (.closure (function.instantiate substitution (produced ++ invocation.evidence.applySubstitution substitution)))
        outcome after) :
      GeneralizedBranch program stages invocation context environment before node
        (Staging.Recursive.Size.stepSize [pathSize]) outcome after
  | requirement {name : String} {binder : Resolved.LocalId} {owned : List RequirementId}
      {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
      {substitution : TypeSystem.Substitution} {failed : RequirementId}
      (form : node.form = .reference name (.local binder))
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned)
      (lookup : Dynamic.Environment.LooksUp environment binder location)
      (read : Dynamic.Heap.Reads before location cell)
      (descriptor : cell.generalized = some function)
      (fields : Dynamic.RuntimeContextFields function.definitionContext context)
      (selection : Dynamic.LocalSchemeRuntimeSelection context function.binder node.rawType owned substitution)
      (fault : Dynamic.RequirementsFault context invocation.evidence owned
        (instantiateLocalSchemePredicates substitution function.binder) failed) :
      GeneralizedBranch program stages invocation context environment before node
        (Staging.Recursive.Size.stepSize []) (.fault (.semantic (.unsatisfiedRequirement failed))) before

omit found unique in
theorem GeneralizedBranch.form {size : Nat} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Staging.Recursive.Outcome}
    (branch : GeneralizedBranch program stages invocation context environment before node size outcome after) :
    ∃ name binder, node.form = .reference name (.local binder) := by
  cases branch with
  | value form _ _ _ _ _ _ _ | requirement form _ _ _ _ _ _ _ => exact ⟨_, _, form⟩

theorem branches (nonempty : node.coercions ≠ [])
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before id outcome after) :
    ((∃ rawSize pathSize value middle,
      size = Staging.Recursive.Size.stepSize [rawSize, pathSize] ∧
      Staging.Recursive.Size.RawForm program stages rawSize invocation context environment before
        node.form node.requirements node.coercions (.value value) middle ∧
      Staging.Recursive.Size.CoercionPath program stages pathSize invocation context middle
        node.coercions value outcome after) ∨
    (∃ rawSize failure, size = Staging.Recursive.Size.stepSize [rawSize] ∧ outcome = .fault failure ∧
      Staging.Recursive.Size.RawForm program stages rawSize invocation context environment before
        node.form node.requirements node.coercions (.fault failure) after)) ∨
      GeneralizedBranch program stages invocation context environment before node size outcome after := by
  cases trace with
  | coercedValue contains _ raw path =>
      cases same found unique contains
      exact .inl (.inl ⟨_, _, _, _, rfl, raw, path⟩)
  | coercedFault contains _ raw =>
      cases same found unique contains
      exact .inl (.inr ⟨_, _, rfl, rfl, raw⟩)
  | generalizedLocal contains form layout lookup read descriptor fields instantiation path =>
      cases same found unique contains
      exact .inr (.value form layout lookup read descriptor fields instantiation path)
  | generalizedLocalRequirement contains form layout lookup read descriptor fields selection fault =>
      cases same found unique contains
      exact .inr (.requirement form layout lookup read descriptor fields selection fault)
  | _ =>
      first
      | exact False.elim (excludes_occurrence found unique nonempty (by assumption))
      | exact False.elim (excludes found unique nonempty (by assumption) (by assumption))

theorem ordinary_branches (nonempty : node.coercions ≠ [])
    (nonlocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before id outcome after) :
    (∃ rawSize pathSize value middle,
      size = Staging.Recursive.Size.stepSize [rawSize, pathSize] ∧
      Staging.Recursive.Size.RawForm program stages rawSize invocation context environment before
        node.form node.requirements node.coercions (.value value) middle ∧
      Staging.Recursive.Size.CoercionPath program stages pathSize invocation context middle
        node.coercions value outcome after) ∨
    (∃ rawSize failure, size = Staging.Recursive.Size.stepSize [rawSize] ∧ outcome = .fault failure ∧
      Staging.Recursive.Size.RawForm program stages rawSize invocation context environment before
        node.form node.requirements node.coercions (.fault failure) after) := by
  rcases branches found unique nonempty trace with ordinary | generalized
  · exact ordinary
  · obtain ⟨name, binder, form⟩ := generalized.form
    exact False.elim (nonlocal name binder form)

theorem raw_value
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {size : Nat} {value : Dynamic.Value}
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heap : Dynamic.HeapWellTyped context before)
    (typed : ExpressionHasType invocation.source context id node.type)
    (trace : Staging.Recursive.Size.RawForm program stages size invocation context environment before
      node.form node.requirements node.coercions (.value value) after) :
    Dynamic.ValueHasType context after value node.rawType ∧ Dynamic.HeapWellTyped context after ∧
      Dynamic.HeapTypesExtend before after := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | @intro _ _ actual rawType plan contains raw rawEq _ _ valid =>
      cases same found unique contains
      rw [← rawEq] at raw
      exact Staging.Recursive.FaultPreservation.raw_form_value wellFormed runtime covers locals heap
        ⟨id, node, lookupExpression?_sound found, rfl, rfl⟩ raw (rawEq ▸ valid) trace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedExpressionSource
end
