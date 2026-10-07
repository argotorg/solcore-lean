import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedNamedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceBodyReadyBounds

/-! A complete static origin association selects the actual strict callee
contract at one genuine named parameter receipt. These finite adapters retain
the original entry and returned pool; the shared measured family supplies the
callee proof. No body closer or expression fold is added here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open CallableIndexedOwnedAdmittedNamedExpressionHeads
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (runtime : Bool)
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled program → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}

private abbrev bridge := CallableIndexedOwnedIndirectCallerProtocol.of_legacy
  (CallableIndexedOwnedCallerProtocol.base (headers := headers) (keys := keys))

variable {ι : Type}
  (origins : ι → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)
  {initial : Index} {argumentsPool : State headers keys initial}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {arguments : List Dynamic.Value}
  (receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    (runtime := runtime) argumentsPool header arguments)
  (wellFormed : ProgramWellFormed program)

/-- Equality authenticates the whole compiler origin, including the raw Source
body, evidence dictionary, code, context, output, certificates and profile.
Syntax is an independent genuine Source receipt for that same body. -/
structure Association where
  index : ι
  sameOrigin : origins index = source_origin
    (CallableRuntimeBodyStaticOrigins.named runtime receipt.profile receipt.escaped)
    (receipt.admitted_entry wellFormed).source.runtime
  syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
    (.statements true header.function.body) header.function.resultType

/-- Every field refers to this receipt's exact original parameter entry and
one actual body post. Successful Source admission remains beside that post. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  let entry := (receipt.admitted_entry wellFormed).original
  let origin := CallableRuntimeBodyStaticOrigins.named runtime receipt.profile receipt.escaped
  Evaluates entry.actual entry.store (origin.code.rename entry.embedding) value finalStore ∧
  FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
  AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
  TypedMixedNamedBody.ReachedExit compiled.compatible.checked (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
    finalMap finalWorld origin.administrative program origin.function origin.context origin.scope
    entry.environment entry.heap after outcome ∧
  ∃ reached : State headers keys ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.canonical⟩,
    Relates receipt.reached reached ∧
    CallableIndexedOwnedSourceAdmission.PostAdmission (bridge (headers := headers) (keys := keys))
      origin.context origin.function.resultType outcome reached

variable {budget : Nat}

include wellFormed in
/-- The real strict Source callee IH specializes at the exact associated
origin and the same complete admitted parameter entry. -/
theorem parameter_preserves
    (association : Association functions owner runtime origins receipt wellFormed)
    (below : ∀ i, RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyReadyOrigins.PreservesAt (protocol headers keys)
        (readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i)))
    {size : Nat} (smaller : size < budget)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context
      receipt.body.environment receipt.body.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      ResultAt functions owner runtime receipt wellFormed outcome after value finalStore finalMap finalWorld := by
  have meaning := below association.index size smaller
  rw [association.sameOrigin] at meaning
  exact CallableIndexedOwnedSourceBodyReadyBounds.preserves_at
    (origin := CallableRuntimeBodyStaticOrigins.named runtime receipt.profile receipt.escaped)
    (size := size) (bridge (headers := headers) (keys := keys))
    (receipt.admitted_entry wellFormed).source.runtime wellFormed association.syntaxTree meaning
    (receipt.admitted_entry wellFormed) trace

include wellFormed in
/-- The original native body completion keeps its strict budget and yields an
independently graded Source trace at the identical actual parameter entry. -/
theorem parameter_reflects
    (association : Association functions owner runtime origins receipt wellFormed)
    (below : ∀ i, RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol headers keys)
        (readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i)))
    {size : Nat} (smaller : size < budget) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size receipt.body.actualBody receipt.body.store
      (header.body.rename receipt.body.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context
        receipt.body.environment receipt.body.heap outcome after ∧
      ResultAt functions owner runtime receipt wellFormed outcome after value finalStore finalMap finalWorld := by
  have meaning := below association.index size smaller
  rw [association.sameOrigin] at meaning
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at
      (origin := CallableRuntimeBodyStaticOrigins.named runtime receipt.profile receipt.escaped)
      (size := size) (bridge (headers := headers) (keys := keys))
      (receipt.admitted_entry wellFormed).source.runtime wellFormed association.syntaxTree meaning
      (receipt.admitted_entry wellFormed) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, completed.sound, represented, heaps,
    maps, worlds, frame, metadata, exit, reached, related, post⟩

section Continuations
variable {functions owner runtime origins receipt}

include wellFormed in
/-- The Source callback keeps its original continuation agreement and selects
only the family's strict associated callee proof at this actual receipt. -/
theorem source_bodies
    (associations : ∀ {initial : Index} {argumentsPool : State headers keys initial} {arguments : List Dynamic.Value},
      ∀ receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
        (runtime := runtime) argumentsPool header arguments,
      Association functions owner runtime origins receipt wellFormed)
    (below : ∀ i, RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyReadyOrigins.PreservesAt (protocol headers keys)
        (readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i))) :
    SourceBodiesFor (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt _agreement size smaller outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, _post⟩ :=
    parameter_preserves functions owner runtime origins actualReceipt wellFormed (associations actualReceipt) below smaller trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related⟩

include wellFormed in
/-- Native callback inversion retains the measured parameter prefix and saved
caller write; only the strict body contract comes from the associated family. -/
theorem native_bodies
    (associations : ∀ {initial : Index} {argumentsPool : State headers keys initial} {arguments : List Dynamic.Value},
      ∀ receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
        (runtime := runtime) argumentsPool header arguments,
      Association functions owner runtime origins receipt wellFormed)
    (below : ∀ i, RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol headers keys)
        (readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i))) :
    NativeBodiesFor (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt prefixSize bodyStore value finalStore
    _prefixRun _prefixWithin _restored size smaller bodyValue actualFinal completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, _post⟩ :=
    parameter_reflects functions owner runtime origins actualReceipt wellFormed (associations actualReceipt) below smaller completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related⟩

end Continuations
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedReadyContinuations
