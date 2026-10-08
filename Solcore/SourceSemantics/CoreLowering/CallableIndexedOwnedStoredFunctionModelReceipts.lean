import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence

/-! The actual stored-call witnesses retain an explicit function model.
These receipts contain the original value, heap, owned-state and intermediate
effects. Gate and application-prefix certificates remain in their original
modules. No closure classifier or execution producer is asserted here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredFunctionModelReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap : LocationMap} {firstWorld : StoreTyping} {before : Dynamic.Heap} {firstStore : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeHeap : Dynamic.Heap} {calleeStore : Store}
  {calleeNative : Value} {calleeMap : LocationMap} {calleeWorld : StoreTyping}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel

/-- The original full parent post at its actual returned owned state. -/
def ParentResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  GenericExpressionMeaning.ResultRepresents model finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functionModel finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧ PostAdmission bridge context compiler.original.type outcome reached

/-- One actual successful callee child, with its full representation. -/
def ValuePost (sourceValue : Dynamic.Value) (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word value) finalStore ∧
  ValueRep compiled.compatible.checked registry functionModel finalMap finalWorld calleeNode.type sourceValue value compiler.calleeCode.type ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functionModel finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧ PostAdmission bridge context calleeNode.type (.value sourceValue) reached

/-- Actual argument success keeps both intermediate and cumulative effects,
beside the whole fourth-bind trace and its strict grade. -/
def SuccessStep (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sources values after argumentStore finalMap finalWorld,
    EvaluationSize nativeSize (.unit :: calleeNative :: actual) calleeStore
      ((((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0).weakenAt 0)
      (.inRight .word (DataPatternValues.packValues values)) argumentStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment calleeHeap ids sources after ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functionModel finalMap finalWorld after argumentStore ∧
    LocationMap.Extends calleeMap finalMap ∧ WorldExtends calleeWorld finalWorld ∧
    AdministrativePreserved calleeMap calleeStore finalMap argumentStore ∧ Dynamic.HeapMetadataExtend calleeHeap after ∧
    LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
    AdministrativePreserved firstMap firstStore finalMap argumentStore ∧ Dynamic.HeapMetadataExtend before after ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, argumentStore, canonical⟩,
      callerProtocol.Relates first reached ∧ Admission bridge context reached) ∧
    (∃ remainingSize,
      EvaluationSize remainingSize (DataPatternValues.packValues values :: .unit :: calleeNative :: actual) argumentStore
        (LanguageResult.bind compiler.resultType
          (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
          (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧
      remainingSize < budget)

/-- A token relation is kept only at the actual fault post. The caller chooses
the genuine relation for child faults or selected physical arity rejection. -/
def FaultPost (tokens : Dynamic.SemanticFault → Word → Prop)
    (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) (token : Word) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  tokens reason token ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functionModel finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧ PostAdmission bridge context compiler.original.type (.fault reason) reached

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredFunctionModelReceipts
