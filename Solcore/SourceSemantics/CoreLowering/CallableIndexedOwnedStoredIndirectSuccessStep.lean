import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectNativePrefix

/-! The exact successful ordered argument witness keeps both the actual
callee-to-argument map/world effects and the cumulative caller effects. Its
complete fourth-bind trace and strict grade remain attached to that same
argument store. This receipt adds no execution producer or classifier. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectSuccessStep
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
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)

variable {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value} {sourceValue : Dynamic.Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  {sourceTypes : List TypeSystem.Ty}

/-- The actual intermediate effects are retained beside the complete argument
post and entire original fourth-bind receipt. No cumulative extension is
inverted to reconstruct them. -/
def SuccessStep (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sources values after argumentStore finalMap finalWorld,
    EvaluationSize nativeSize (.unit :: calleeNative :: actual) calleeStore
      ((((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0).weakenAt 0)
      (.inRight .word (DataPatternValues.packValues values)) argumentStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment calleeHeap ids sources after ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after argumentStore ∧
    LocationMap.Extends calleeMap finalMap ∧ WorldExtends calleeWorld finalWorld ∧
    AdministrativePreserved calleeMap calleeStore finalMap argumentStore ∧ Dynamic.HeapMetadataExtend calleeHeap after ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentStore ∧ Dynamic.HeapMetadataExtend before after ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, argumentStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
    (∃ remainingSize,
      EvaluationSize remainingSize (DataPatternValues.packValues values :: .unit :: calleeNative :: actual) argumentStore
        (LanguageResult.bind compiler.resultType
          (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
          (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧
      remainingSize < budget)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectSuccessStep
