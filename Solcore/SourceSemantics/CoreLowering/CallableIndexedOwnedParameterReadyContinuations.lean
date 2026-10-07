import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceBodyReadyBounds

/-! A strict shared-family child is selected by the complete authentic Source
origin of one actual parameter entry. Only the extra post proof is forgotten;
the original semantic fields and returned ordered pool remain identical. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedParameterReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults}

/-- This bridge keeps the same complete base pool and its real return operation. -/
def bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True)
    (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy (CallableIndexedOwnedCallerProtocol.base (headers := headers) (keys := keys))

variable (entry : CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) (keys := keys))
    (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := origin) (functions := functions))
  (wellFormed : ProgramWellFormed program)
  (syntaxTree : GenericImperativeMatch.Syntax origin.function.source origin.expressionSyntax
    origin.context (.statements true origin.function.body) origin.function.resultType)
  {ι : Type} (origins : ι → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)
  (selected : ι)
  (sameOrigin : origins selected = source_origin origin entry.source.runtime)

include wellFormed syntaxTree sameOrigin in
/-- The strict Source child applies at this actual parameter entry. -/
theorem source_at (budget : Nat)
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.PreservesAt (protocol headers keys)
        (readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i) child)) :
    RecursiveNamedCatalogInvocationBounds.Below budget
      (CallableRuntimeBodyEntryContracts.PreservesAt (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := protocol headers keys) (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (origin := origin) functions program entry.original) := by
  intro child strict outcome after trace
  have ready := below child strict selected
  rw [sameOrigin] at ready
  have meaning := CallableIndexedOwnedSourceBodyReadyBounds.preserves_at
    (bridge (headers := headers) (keys := keys)) entry.source.runtime wellFormed syntaxTree ready
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, _post⟩ := meaning entry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related⟩

include wellFormed syntaxTree sameOrigin in
/-- Native reflection retains the independent Source grade and same post. -/
theorem native_at (budget : Nat)
    (below : RecursiveNamedCatalogInvocationBounds.Below budget (fun child => ∀ i,
      CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol headers keys)
        (readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i) child)) :
    RecursiveNamedCatalogInvocationBounds.Below budget
      (CallableRuntimeBodyEntryContracts.ReflectsAt (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := protocol headers keys) (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (origin := origin) functions program entry.original) := by
  intro child strict value finalStore completed
  have ready := below child strict selected
  rw [sameOrigin] at ready
  have meaning := CallableIndexedOwnedSourceBodyReadyBounds.reflects_at
    (bridge (headers := headers) (keys := keys)) entry.source.runtime wellFormed syntaxTree ready
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, _post⟩ := meaning entry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedParameterReadyContinuations
