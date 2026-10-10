import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectNativePrefix

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
