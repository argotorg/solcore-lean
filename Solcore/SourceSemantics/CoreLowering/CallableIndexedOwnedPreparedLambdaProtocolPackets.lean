import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaProtocolContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaEntries

/-! Actual ordinary and selected-method supports supply canonical protocol
packets at the genuine parameter Entry/Prefix. Their original captured globals,
physical bundle prefix and full Source metadata authenticate the same reached
row's own ghost. The body is the retained JointBody's literal typed projection;
no body-registry equality, escaped row or base-pool inverse is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaProtocolPackets
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedTypedLambdaProtocolContinuations (Packets)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

namespace Ordinary
variable (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (origin : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.SourceOrigin support history)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)

include origin observed prefixContext in
/-- Both actual original producers derive their packet at this receiving
registry directly from the true parameter spine/read. The support's base
CatalogSites and any equality of independent registries play no role. -/
def packets : Packets (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
    captured code history support.body.toBody functions
    (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller) owner caller where
  source := by
    intro entry added length spine reached
    exact ⟨⟨reached, CallableIndexedOwnedLambdaNestedEntries.source_packet
      captured code history support.body.toBody.toContext functions owner support.caller
      observed prefixContext origin.metadata caller entry added length spine reached⟩, rfl⟩
  native := by
    intro entry reached
    exact ⟨⟨reached, CallableIndexedOwnedLambdaNestedEntries.native_packet
      captured code history support.body.toBody.toContext functions owner support.caller
      observed prefixContext origin.metadata caller entry reached⟩, rfl⟩

end Ordinary
namespace Principal
variable (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (origin : CallableIndexedOwnedPreparedPrincipalLambdaSupport.SourceOrigin support history)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)

include origin observed leading in
/-- The Principal branch uses its actual Named and dictionary, with its own
bundle and metadata seed. It never constructs an ordinary Header. The exact
Entry/Prefix environments and reads manufacture the full canonical packet. -/
def packets : Packets (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
    captured code history support.body.toBody functions
    (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) owner caller where
  source := by
    intro entry added length spine reached
    refine ⟨⟨reached, ?_⟩, rfl⟩
    apply CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner support.principal.named reached
    · exact ⟨CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix captured code owner 1 observed added length spine,
        entry.entry.reference⟩
    · exact entry.entry.environments
    · exact leading
    · exact origin.metadata ▸ entry.nextHistory
    · exact entry.entry.read
  native := by
    intro entry reached
    refine ⟨⟨reached, ?_⟩, rfl⟩
    obtain ⟨added, length, spine⟩ := entry.spine
    apply CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner support.principal.named reached
    · exact ⟨CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix captured code owner 1 observed added length spine,
        entry.reference⟩
    · exact entry.environments
    · exact leading
    · exact origin.metadata ▸ entry.nextHistory
    · exact entry.read

end Principal
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaProtocolPackets
