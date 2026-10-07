import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyEntries

/-! The shared ready body result supplies the actual returned state. Genuine
Source body execution establishes successful value typing at that same state;
faults keep all-row stable history. These finite adapters add no body fold. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyReadyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
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
  (wellFormed : ProgramWellFormed program)
  (syntaxTree : GenericImperativeMatch.Syntax origin.function.source origin.expressionSyntax
    origin.context (.statements true origin.function.body) origin.function.resultType)

include wellFormed syntaxTree in
/-- A genuine body trace adds successful Source typing to the same actual
ready finish witness supplied by the shared callee proof. -/
theorem preserves_at {size : Nat}
    (meaning : CallableRuntimeBodyReadyOrigins.PreservesAt callerProtocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts origin.function.source origin.expressionSyntax)
      functions program origin size) :
    CallableIndexedOwnedAdmittedBodyEntries.PreservesAt bridge
      (condition := condition) (origin := origin) (functions := functions) size := by
  intro entry outcome after trace
  let readyEntry := CallableIndexedOwnedBodyReadyEntries.entry bridge entry syntaxTree
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, _ready⟩ := meaning readyEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related,
    CallableIndexedOwnedAdmittedBodyEntries.after_body bridge wellFormed entry reached trace frame⟩

include wellFormed syntaxTree in
/-- The original native completion yields an independently graded Source
trace, which authenticates admission at the exact returned state. -/
theorem reflects_at {size : Nat}
    (meaning : CallableRuntimeBodyReadyOrigins.ReflectsAt callerProtocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts origin.function.source origin.expressionSyntax)
      functions program origin size) :
    CallableIndexedOwnedAdmittedBodyEntries.ReflectsAt bridge
      (condition := condition) (origin := origin) (functions := functions) size := by
  intro entry value finalStore completed
  let readyEntry := CallableIndexedOwnedBodyReadyEntries.entry bridge entry syntaxTree
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, _ready⟩ := meaning readyEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related,
    CallableIndexedOwnedAdmittedBodyEntries.after_body bridge wellFormed entry reached trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyReadyBounds
