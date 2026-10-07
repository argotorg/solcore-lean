import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyReadyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceOrigin

/-! Source runtime validity strengthens the compiler origin's visited domain.
The completed shared body proof still describes the original actual entry,
code and returned pool. These finite adapters expose that original contract. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceBodyReadyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)
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
  (runtime : Dynamic.SourceRuntimeValid program origin.context origin.function.source)
  (wellFormed : ProgramWellFormed program)
  (syntaxTree : GenericImperativeMatch.Syntax origin.function.source origin.expressionSyntax
    origin.context (.statements true origin.function.body) origin.function.resultType)

include wellFormed syntaxTree in
/-- Reindexing the genuine Source domain retains the exact preservation
witness at the original parameter entry and returned state. -/
theorem preserves_at {size : Nat}
    (meaning : CallableRuntimeBodyReadyOrigins.PreservesAt callerProtocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts origin.function.source origin.expressionSyntax)
      functions program (source_origin origin runtime) size) :
    CallableIndexedOwnedAdmittedBodyEntries.PreservesAt bridge
      (condition := condition) (origin := origin) (functions := functions) size := by
  intro entry outcome after trace
  exact CallableIndexedOwnedAdmittedBodyReadyBounds.preserves_at
    (origin := source_origin origin runtime) (size := size) bridge wellFormed syntaxTree meaning
    (CallableIndexedOwnedBodySourceOrigin.admitted_entry bridge entry) trace

include wellFormed syntaxTree in
/-- The same original native completion is reflected with an independent
Source grade and admission at its actual returned state. -/
theorem reflects_at {size : Nat}
    (meaning : CallableRuntimeBodyReadyOrigins.ReflectsAt callerProtocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts origin.function.source origin.expressionSyntax)
      functions program (source_origin origin runtime) size) :
    CallableIndexedOwnedAdmittedBodyEntries.ReflectsAt bridge
      (condition := condition) (origin := origin) (functions := functions) size := by
  intro entry value finalStore completed
  exact CallableIndexedOwnedAdmittedBodyReadyBounds.reflects_at
    (origin := source_origin origin runtime) (size := size) bridge wellFormed syntaxTree meaning
    (CallableIndexedOwnedBodySourceOrigin.admitted_entry bridge entry) completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceBodyReadyBounds
