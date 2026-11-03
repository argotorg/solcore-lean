import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticCalls

/-! Ordinary closure calls combine concrete lexical builtin bodies with the
actual indexed frame and marked parameter prefix. The lambda's generation
receipt and caller history remain semantic inputs. Completed native execution
constructs the independent source call; no body execution is an input. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaViewInvocation
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

abbrev represented_closure := @CallableIndexedLambdaCalls.represented_closure
abbrev applyPayload := CallableIndexedLambdaCalls.applyPayload

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))

include extension uninitialized missing in
theorem Entry.preserves
    (entry : Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost)
    {copies environment : Dynamic.Environment} {copied bound after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copied)
    (allocated : Dynamic.BindersAllocate copies copied function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact CallableIndexedLambdaSemanticCalls.Entry.preserves captured code history body.semantic profile extension uninitialized missing entry copy allocated trace

include extension uninitialized missing in
theorem Entry.reflects
    (entry : Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost)
    {result : Value} {finalStore : Store}
    (evaluated : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result finalStore) :
    ∃ copies copied environment bound outcome after finalMap finalWorld,
      Dynamic.EnvironmentCopies function.source function.captured before copies copied ∧
      Dynamic.BindersAllocate copies copied function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function body.context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact CallableIndexedLambdaSemanticCalls.Entry.reflects captured code history body.semantic profile extension uninitialized missing entry evaluated

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem reflects {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {result : Value} {finalStore : Store}
    (evaluated : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact CallableIndexedLambdaSemanticCalls.reflects captured code history body.semantic profile extension represented heaps locals reference read currentCarried unmapped allowed uninitialized missing evaluated

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem preserves {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact CallableIndexedLambdaSemanticCalls.preserves captured code history body.semantic profile extension represented heaps locals reference read currentCarried unmapped allowed uninitialized missing executed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewCalls
