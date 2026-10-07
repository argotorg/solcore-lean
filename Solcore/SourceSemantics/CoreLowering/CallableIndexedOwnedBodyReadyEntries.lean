import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyTypedFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness

/-! Genuine parameter Source receipts and every original row authenticate the
same actual body entry. Independent compiler syntax supplies its static facts;
the ready origin wrapper forwards the complete entry without rebuilding it. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {condition : Location → NativeFrame → Prop}
  {origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}

def entry
    (original : CallableIndexedOwnedAdmittedBodyEntries.Entry bridge
      (condition := condition) (origin := origin) (functions := functions))
    (syntaxTree : GenericImperativeMatch.Syntax origin.function.source origin.expressionSyntax origin.context
      (.statements true origin.function.body) origin.function.resultType) :
    CallableRuntimeBodyReadyOrigins.Entry callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      condition (ProtectedStateImperativeTypedSourceSites.Facts origin.function.source origin.expressionSyntax)
      origin functions :=
  ⟨original.original, CallableIndexedOwnedBodyTypedFacts.facts original.source syntaxTree, original.admission⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyEntries
