import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.ExpressionTrees
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CallEvidence
import Solcore.SourceSemantics.Instantiation
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.ReachedNamedFaultPaths
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeControl
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCatalog

/-!
# Owned callables: ready continuations

Ready continuations and family receipts of parameters and named bodies, and faults of sequential bodies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedParameterReadyContinuations
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedReadyContinuations
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedReadyFamilyReceipts
/-! A genuine named compiler profile and its original Source syntax select a
shared-family index. Real parameter receipts supply canonical slots beside the
same actual pool. Strict family children then return that pool through the
original pointwise named continuation, retaining successful Source admission. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedReadyFamilyReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedNamedExpressionHeads
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled program → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (runtime : Bool)

/-- The member, profile and Syntax are original static receipts. Runtime
validity authenticates the same raw Source body, independently of Core types. -/
structure Index where
  header : CallableIndexedOwnedFunctionValues.Header compiled program
  member : header ∈ headers
  administrative : Core.Context
  profile : Profile (registry := registry) (faults := faults) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) runtime header administrative
  syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
    (.statements true header.function.body) header.function.resultType
  sourceRuntime : Dynamic.SourceRuntimeValid program header.context header.function.source
  escaped : faults .controlEscapedFunction header.escaped

/-- The full indexed origin retains the actual body, dictionary, compiler
tree and code. Only its visited Source validity domain is strengthened. -/
def origin (index : Index (headers := headers) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    (registry := registry) (faults := faults) runtime) :
    CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults :=
  source_origin (CallableRuntimeBodyStaticOrigins.named (header := index.header)
    (certificates := certificates index.header) (expressionSyntax := expressionSyntax index.header)
    (diagnosticPolicy := diagnosticPolicy) runtime index.profile index.escaped) index.sourceRuntime

/-- Original compiler inputs already retain Syntax. No Syntax is recovered
from the erased compiled Tree, and the exact supplied profile is kept. -/
def of_inputs {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (member : header ∈ headers) {administrative : Core.Context} {tracked : Bool}
    (profile : Profile (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) runtime header administrative)
    (inputs : RecursiveNamedCatalogRuntimeProfileFactory.InputsFor
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (certificates header) tracked diagnosticPolicy
      header (expressionSyntax header) (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (sourceRuntime : Dynamic.SourceRuntimeValid program header.context header.function.source)
    (escaped : faults .controlEscapedFunction header.escaped) :
    Index (headers := headers) (certificates := certificates) (expressionSyntax := expressionSyntax)
      (diagnosticPolicy := diagnosticPolicy) (registry := registry) (faults := faults) runtime :=
  ⟨header, member, administrative, profile, inputs.syntaxTree, sourceRuntime, escaped⟩

/-- This protocol retains the genuine global slots at the original body
prefix alongside the entire actual ordered pool. -/
def body_protocol (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) :=
  CallableIndexedOwnedExpressionHeads.argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1)

/-- Returning forgets only the slot proof; its full pool remains the same. -/
def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy
    (CallableIndexedOwnedCallerProtocol.canonical (headers := headers) owner (owner.key.capturePrefix + 1))

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {arguments : List Dynamic.Value}
  (receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    (runtime := runtime) argumentsPool header arguments)
  (wellFormed : ProgramWellFormed program)

/-- Selecting the actual receipt profile avoids any Tree or profile uniqueness
assumption. Source admission supplies its genuine runtime proof. -/
def of_receipt (member : header ∈ headers)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
      (.statements true header.function.body) header.function.resultType) :
    Index (headers := headers) (certificates := certificates) (expressionSyntax := expressionSyntax)
      (diagnosticPolicy := diagnosticPolicy) (registry := registry) (faults := faults) runtime :=
  ⟨header, member, receipt.administrative, receipt.profile, syntaxTree,
    (receipt.admitted_entry wellFormed).source.runtime, receipt.escaped⟩

/-- The indexed origin is the complete origin of this actual parameter entry. -/
theorem receipt_origin (member : header ∈ headers)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
      (.statements true header.function.body) header.function.resultType) :
    origin runtime (of_receipt runtime functions owner receipt wellFormed member syntaxTree) =
      source_origin (CallableRuntimeBodyStaticOrigins.named runtime receipt.profile receipt.escaped)
        (receipt.canonical_entry wellFormed).source.runtime := rfl

variable {budget : Nat}

include wellFormed in
/-- The actual canonical parameter entry consumes the strict family child;
the rich result retains Source admission at the same returned base pool. -/
theorem parameter_preserves (member : header ∈ headers)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
      (.statements true header.function.body) header.function.resultType)
    (below : ∀ index : Index (headers := headers) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (registry := registry) (faults := faults) runtime,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol (headers := headers) owner)
          (readiness (bridge (headers := headers) owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin runtime index).function.source (origin runtime index).expressionSyntax)
          functions program (origin runtime index)))
    {size : Nat} (smaller : size < budget) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context
      receipt.body.environment receipt.body.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedNamedReadyContinuations.ResultAt functions owner runtime receipt wellFormed
        outcome after value finalStore finalMap finalWorld := by
  have meaning := below (of_receipt runtime functions owner receipt wellFormed member syntaxTree) size smaller
  rw [receipt_origin runtime functions owner receipt wellFormed member syntaxTree] at meaning
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at (bridge (headers := headers) owner)
      (receipt.canonical_entry wellFormed).source.runtime wellFormed syntaxTree meaning
      (receipt.canonical_entry wellFormed) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached.val, related, ⟨post.rows, post.successful⟩⟩

include wellFormed in
/-- Reflection keeps the same wrapped native parameter entry and returns the
independent Source grade beside its exact reached pool and admission. -/
theorem parameter_reflects (member : header ∈ headers)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
      (.statements true header.function.body) header.function.resultType)
    (below : ∀ index : Index (headers := headers) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (registry := registry) (faults := faults) runtime,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol (headers := headers) owner)
          (readiness (bridge (headers := headers) owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin runtime index).function.source (origin runtime index).expressionSyntax)
          functions program (origin runtime index)))
    {size : Nat} (smaller : size < budget) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size receipt.body.actualBody receipt.body.store
      (header.body.rename receipt.body.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context
        receipt.body.environment receipt.body.heap outcome after ∧
      CallableIndexedOwnedNamedReadyContinuations.ResultAt functions owner runtime receipt wellFormed
        outcome after value finalStore finalMap finalWorld := by
  have meaning := below (of_receipt runtime functions owner receipt wellFormed member syntaxTree) size smaller
  rw [receipt_origin runtime functions owner receipt wellFormed member syntaxTree] at meaning
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at (bridge (headers := headers) owner)
      (receipt.canonical_entry wellFormed).source.runtime wellFormed syntaxTree meaning
      (receipt.canonical_entry wellFormed) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, completed.sound, represented, heaps,
    maps, worlds, frame, metadata, exit, reached.val, related, ⟨post.rows, post.successful⟩⟩

section Continuations
variable {runtime functions owner receipt}

include wellFormed in
/-- The actual static member and Syntax construct every receipt association
internally. The only dynamic body input is the strict shared-family IH. -/
theorem source_bodies (member : header ∈ headers)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
      (.statements true header.function.body) header.function.resultType)
    (below : ∀ index : Index (headers := headers) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (registry := registry) (faults := faults) runtime,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol (headers := headers) owner)
          (readiness (bridge (headers := headers) owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin runtime index).function.source (origin runtime index).expressionSyntax)
          functions program (origin runtime index))) :
    SourceBodiesFor (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt _agreement size smaller outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, _post⟩ :=
    parameter_preserves runtime functions owner actualReceipt wellFormed member syntaxTree below smaller trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related⟩

include wellFormed in
/-- The measured parameter prefix and saved caller write stay original.
Only the proof beside the same returned pool is forgotten for this callback. -/
theorem native_bodies (member : header ∈ headers)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
      (.statements true header.function.body) header.function.resultType)
    (below : ∀ index : Index (headers := headers) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (registry := registry) (faults := faults) runtime,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol (headers := headers) owner)
          (readiness (bridge (headers := headers) owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin runtime index).function.source (origin runtime index).expressionSyntax)
          functions program (origin runtime index))) :
    NativeBodiesFor (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt prefixSize bodyStore value finalStore
    _prefixRun _prefixWithin _restored size smaller bodyValue actualFinal completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, _evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, _post⟩ :=
    parameter_reflects runtime functions owner actualReceipt wellFormed member syntaxTree below smaller completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related⟩

end Continuations
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedReadyFamilyReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedNestedReadyFamilyReceipts
/-! Actual named parameter receipts retain a complete principal packet for
nested formation. The dependent family index preserves the genuine Source seed,
bundle, frame and global count at the same pool; its strict child uses that
exact stronger protocol without introducing a new family closer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedNestedReadyFamilyReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedNamedExpressionHeads
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled program → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (runtime : Bool)

/-- The authentic original named receipt stays complete. Honest ordinary
prefix and global-count receipts accompany its actual physical principal. -/
structure Index where
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  receipt : CallableIndexedOwnedNamedReadyFamilyReceipts.Index (headers := headers)
    (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    (registry := registry) (faults := faults) runtime
  prefixZero : owner.key.capturePrefix = 0
  globals : receipt.header.globals = compiled.indexed.base.globals.length

/-- The complete same original Source origin is unchanged by packet wrapping. -/
def origin (index : Index (headers := headers) (keys := keys) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    (registry := registry) (faults := faults) runtime) :=
  CallableIndexedOwnedNamedReadyFamilyReceipts.origin runtime index.receipt

/-- The actual selected header is the complete nested packet's principal. -/
def body_protocol (index : Index (headers := headers) (keys := keys) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    (registry := registry) (faults := faults) runtime) :=
  CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) index.owner index.receipt.header

/-- The complete packet accompanies the identical actual ordered pool. -/
def bridge (index : Index (headers := headers) (keys := keys) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    (registry := registry) (faults := faults) runtime) :=
  CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) index.owner index.receipt.header)

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {arguments : List Dynamic.Value}
  (receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    (runtime := runtime) argumentsPool header arguments)
  (wellFormed : ProgramWellFormed program)
  (prefixZero : owner.key.capturePrefix = 0)
  (globals : header.globals = compiled.indexed.base.globals.length)

/-- Selecting the actual receipt profile avoids any Tree or profile uniqueness
assumption. Source admission supplies its genuine runtime proof. -/
def of_receipt (member : header ∈ headers)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
      (.statements true header.function.body) header.function.resultType) :
    Index (headers := headers) (keys := keys) (certificates := certificates) (expressionSyntax := expressionSyntax)
      (diagnosticPolicy := diagnosticPolicy) (registry := registry) (faults := faults) runtime :=
  ⟨owner, CallableIndexedOwnedNamedReadyFamilyReceipts.of_receipt runtime functions owner receipt wellFormed member syntaxTree, prefixZero, globals⟩

/-- The indexed origin is the complete origin of this actual parameter entry. -/
theorem receipt_origin (member : header ∈ headers)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
      (.statements true header.function.body) header.function.resultType) :
    origin runtime (of_receipt runtime functions owner receipt wellFormed prefixZero globals member syntaxTree) =
      source_origin (CallableRuntimeBodyStaticOrigins.named runtime receipt.profile receipt.escaped)
        (receipt.nested_entry wellFormed prefixZero globals).source.runtime := rfl

variable {budget : Nat}

include wellFormed prefixZero globals in
/-- The actual complete nested parameter entry consumes the strict family child;
the rich result retains Source admission at the same returned base pool. -/
theorem parameter_preserves (member : header ∈ headers)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
      (.statements true header.function.body) header.function.resultType)
    (below : ∀ index : Index (headers := headers) (keys := keys) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (registry := registry) (faults := faults) runtime,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol runtime index)
          (readiness (bridge runtime index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin runtime index).function.source (origin runtime index).expressionSyntax)
          functions program (origin runtime index)))
    {size : Nat} (smaller : size < budget) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context
      receipt.body.environment receipt.body.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedNamedReadyContinuations.ResultAt functions owner runtime receipt wellFormed
        outcome after value finalStore finalMap finalWorld := by
  have meaning := below (of_receipt runtime functions owner receipt wellFormed prefixZero globals member syntaxTree) size smaller
  rw [receipt_origin runtime functions owner receipt wellFormed prefixZero globals member syntaxTree] at meaning
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at
      (bridge runtime (of_receipt runtime functions owner receipt wellFormed prefixZero globals member syntaxTree))
      (receipt.nested_entry wellFormed prefixZero globals).source.runtime wellFormed syntaxTree meaning
      (receipt.nested_entry wellFormed prefixZero globals) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached.val, related, ⟨post.rows, post.successful⟩⟩

include wellFormed prefixZero globals in
/-- Reflection keeps the same complete wrapped native parameter entry and returns the
independent Source grade beside its exact reached pool and admission. -/
theorem parameter_reflects (member : header ∈ headers)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
      (.statements true header.function.body) header.function.resultType)
    (below : ∀ index : Index (headers := headers) (keys := keys) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (registry := registry) (faults := faults) runtime,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol runtime index)
          (readiness (bridge runtime index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin runtime index).function.source (origin runtime index).expressionSyntax)
          functions program (origin runtime index)))
    {size : Nat} (smaller : size < budget) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size receipt.body.actualBody receipt.body.store
      (header.body.rename receipt.body.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context
        receipt.body.environment receipt.body.heap outcome after ∧
      CallableIndexedOwnedNamedReadyContinuations.ResultAt functions owner runtime receipt wellFormed
        outcome after value finalStore finalMap finalWorld := by
  have meaning := below (of_receipt runtime functions owner receipt wellFormed prefixZero globals member syntaxTree) size smaller
  rw [receipt_origin runtime functions owner receipt wellFormed prefixZero globals member syntaxTree] at meaning
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at
      (bridge runtime (of_receipt runtime functions owner receipt wellFormed prefixZero globals member syntaxTree))
      (receipt.nested_entry wellFormed prefixZero globals).source.runtime wellFormed syntaxTree meaning
      (receipt.nested_entry wellFormed prefixZero globals) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, completed.sound, represented, heaps,
    maps, worlds, frame, metadata, exit, reached.val, related, ⟨post.rows, post.successful⟩⟩

section Continuations
variable {runtime functions owner receipt}

include wellFormed prefixZero globals in
/-- The actual static member and Syntax construct every receipt association
internally. The only dynamic body input is the strict shared-family IH. -/
theorem source_bodies (member : header ∈ headers)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
      (.statements true header.function.body) header.function.resultType)
    (below : ∀ index : Index (headers := headers) (keys := keys) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (registry := registry) (faults := faults) runtime,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol runtime index)
          (readiness (bridge runtime index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin runtime index).function.source (origin runtime index).expressionSyntax)
          functions program (origin runtime index))) :
    SourceBodiesFor (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt _agreement size smaller outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, _post⟩ :=
    parameter_preserves runtime functions owner actualReceipt wellFormed prefixZero globals member syntaxTree below smaller trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related⟩

include wellFormed prefixZero globals in
/-- The measured parameter prefix and saved caller write stay original.
Only the proof beside the same returned pool is forgotten for this callback. -/
theorem native_bodies (member : header ∈ headers)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
      (.statements true header.function.body) header.function.resultType)
    (below : ∀ index : Index (headers := headers) (keys := keys) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (registry := registry) (faults := faults) runtime,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol runtime index)
          (readiness (bridge runtime index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin runtime index).function.source (origin runtime index).expressionSyntax)
          functions program (origin runtime index))) :
    NativeBodiesFor (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt prefixSize bodyStore value finalStore
    _prefixRun _prefixWithin _restored size smaller bodyValue actualFinal completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, _evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, _post⟩ :=
    parameter_reflects runtime functions owner actualReceipt wellFormed prefixZero globals member syntaxTree below smaller completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related⟩

end Continuations
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedNestedReadyFamilyReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallCodebookReceipts
/-! The exact selected decision keeps its original codebook request, argument
count, ledger entry and guard provenance. Public preparation supplies the actual
original sidecar list and generated rows. Source occurrence uniqueness identifies
the same call and ordered arguments. These are static receipts; no child
execution, stage verdict, native type inference or invocation law is supplied. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallCodebookReceipts
open Core Frontend SourceInference SourceCoreStageCodebook
open DataPatternValues CallCodebookCertificates

private theorem output_requested {α β : Type} {relation : α → β → Prop}
    {inputs : List α} {outputs : List β} (related : ListRel relation inputs outputs)
    {output : β} (member : output ∈ outputs) :
    ∃ input, input ∈ inputs ∧ relation input output := by
  induction related with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨input, requested, generated⟩ := ih member
      exact ⟨input, List.mem_cons_of_mem _ requested, generated⟩

private theorem request_source {sidecars : List Sidecar} {entries : List Entry}
    {request : Request} (member : request ∈ requests sidecars entries) :
    request.sidecar ∈ sidecars ∧ request.entry ∈ entries ∧ ∃ node callee metadata,
      ContainsExpression request.sidecar.source request.call node ∧
      node.form = .call callee request.arguments (.indirect metadata) := by
  obtain ⟨sidecar, present, inSource⟩ := List.mem_flatMap.mp member
  obtain ⟨sourceNode, nodePresent, requested⟩ := List.mem_flatMap.mp inSource
  cases sourceNode with
  | statement => cases requested
  | expression node =>
    cases node with
    | mk id span type form requirements coercions localStart =>
      cases form <;> try cases requested
      rename_i callee arguments resolution
      cases resolution <;> try cases requested
      obtain ⟨entry, entryPresent, same⟩ := List.mem_map.mp requested
      cases same
      exact ⟨present, entryPresent, _, _, _, ⟨nodePresent, rfl⟩, rfl⟩

/-- The full original Generated receipt retains the same selected ledger entry,
prepared guard or builtin branch, and the physical argument count. -/
structure Selected (sidecar : Sidecar) (site : SourceCoreCallableContracts.Callsite)
    (callee : ExpressionId) (arguments : List ExpressionId)
    (metadata : IndirectCallResolution) (node : ExpressionNode) (row : Decision) : Prop where
  contains : ContainsExpression sidecar.source site.call node
  form : node.form = .call callee arguments (.indirect metadata)
  found : site.rowAt? row.entry.id = some row
  member : row.entry ∈ site.table.entries
  generated : Generated ⟨sidecar, site.call, arguments, row.entry⟩ row
  authenticated : CallEntryCertificates.Authenticated sidecar.plan row.entry

/-- The actual public codebook and actual selected row construct all fields.
No independently supplied row count or arbitrary accepted guard is needed. -/
theorem selected_at {program : CheckedProgram} {plan : Plan}
    {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {site : SourceCoreCallableContracts.Callsite}
    {sidecar : Sidecar} {node : ExpressionNode} {callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {descriptor : Word} {row : Decision}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok site.table)
    (caller : SourceCoreStageContracts.prepareSidecar plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (unique : NodeOccurrencesUnique sidecar.source)
    (selected : site.rowAt? descriptor = some row) :
    Selected sidecar site callee arguments metadata node row := by
  obtain ⟨inTable, atSite⟩ := List.mem_filter.mp (List.mem_of_find?_eq_some selected)
  have sites : row.caller = site.caller ∧ row.call = site.call := of_decide_eq_true atSite
  obtain ⟨sidecars, original, collected⟩ := prepareWithProjection_collects accepted
  obtain ⟨request, requested, generated⟩ :=
    output_requested (collectDecisions_certifies collected) inTable
  obtain ⟨sidecarMember, entryMember, actualNode, actualCallee, actualMetadata, actualContains, actualForm⟩ :=
    request_source requested
  have key : request.sidecar.caller.key = site.caller := generated.caller.symm.trans sites.1
  have actualCaller := original request.sidecar sidecarMember
  rw [key] at actualCaller
  have sameSidecar := Except.ok.inj (actualCaller.symm.trans caller)
  have actualContains : ContainsExpression sidecar.source site.call actualNode := by
    rw [sameSidecar, ← generated.call, sites.2] at actualContains
    exact actualContains
  have sameNode := Option.some.inj
    ((lookupExpression?_complete unique actualContains).symm.trans (lookupExpression?_complete unique contains))
  have sameArguments : request.arguments = arguments := by
    have shapes := actualForm.symm.trans ((congrArg ExpressionNode.form sameNode).trans form)
    exact (ExpressionForm.call.inj shapes).2.1
  have exactRequest : request = ⟨sidecar, site.call, arguments, row.entry⟩ := by
    cases request
    simp only at sameSidecar generated sameArguments
    cases sameSidecar
    cases generated.call.symm.trans sites.2
    cases sameArguments
    cases generated.entry
    rfl
  have authentic := CallEntryCertificates.prepareWithProjection_authenticates accepted
    row.entry (generated.entry.symm ▸ entryMember)
  have samePlan := (CallContractCertificates.sidecar_of_accepted caller).1
  have descriptorEq : descriptor = row.entry.id :=
    beq_iff_eq.mp (List.find?_some (p := fun decision : Decision => descriptor == decision.entry.id) selected)
  exact ⟨contains, form, descriptorEq ▸ selected, generated.entry.symm ▸ entryMember,
    exactRequest ▸ generated, samePlan.symm ▸ authentic⟩

/-- The existing actual compiled preparation supplies the public factory
receipt; the selected original caller source remains explicit. -/
theorem selected_at_prepared {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (prepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    {site : SourceCoreCallableContracts.Callsite} {sidecar : Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution} {descriptor : Word} {row : Decision}
    (table : site.table = native.table)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (unique : NodeOccurrencesUnique sidecar.source)
    (selected : site.rowAt? descriptor = some row) :
    Selected sidecar site callee arguments metadata node row := by
  have accepted := prepared.accepted
  rw [← table] at accepted
  exact selected_at accepted caller contains form unique selected

/-- The projected ledger keeps the exact selected guard/builtin receipts. -/
theorem Selected.ledger {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {row : Decision}
    (receipt : Selected sidecar site callee arguments metadata node row) :
    Nonempty (CallableLedger.Row sidecar site site.call arguments row.entry) :=
  ⟨⟨row, receipt.found, rfl, receipt.generated.user, receipt.generated.builtin⟩⟩

/-- This physical list length is the original generated request count. -/
theorem Selected.argument_count {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {row : Decision}
    (receipt : Selected sidecar site callee arguments metadata node row) :
    row.argumentCount = arguments.length := receipt.generated.argumentCount

/-- Authentication keeps the original user contract's full parameter count. -/
theorem Selected.parameter_count {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {row : Decision} {contract : Contract}
    (receipt : Selected sidecar site callee arguments metadata node row)
    (retained : row.entry.contract = some contract) :
    row.entry.parameterCount = contract.parameters.length := by
  have authenticated := receipt.authenticated
  unfold CallEntryCertificates.Authenticated at authenticated
  generalize origin : row.entry.origin = actualOrigin at authenticated
  generalize count : row.entry.parameterCount = actualCount at authenticated
  generalize attached : row.entry.contract = actualContract at authenticated
  cases authenticated <;> rw [retained] at attached <;> cases attached <;> rfl

/-- Genuine selected entry arity closes only the independent second gate.
The first guard's stage decision is unchanged and remains separate. -/
theorem Selected.before_application {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {row : Decision}
    (receipt : Selected sidecar site callee arguments metadata node row)
    (count : row.entry.parameterCount = arguments.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown row.entry.id = none := by
  rw [site.decision_known .beforeApplication unknown row.entry.id row receipt.found]
  exact SourceCoreCallableContracts.reason_accepted row site.reasonAt .beforeApplication
    (row.afterArguments_ok (count.trans receipt.argument_count.symm))

/-- Original closure contract binding and real arity close the second gate;
no Source parameter count is inferred from a packed native type. -/
theorem Selected.before_application_for_closure {sidecar : Sidecar}
    {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {row : Decision} {contract : Contract}
    {function : Dynamic.Closure}
    (receipt : Selected sidecar site callee arguments metadata node row)
    (retained : row.entry.contract = some contract)
    (bound : CallableLedger.Binds sidecar.plan (.closure function)
      (CallContractCertificates.semanticContract contract))
    (arity : function.parameters.length = arguments.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown row.entry.id = none := by
  cases bound with
  | closure parameters _ =>
    exact receipt.before_application
      ((receipt.parameter_count retained).trans ((congrArg List.length parameters).trans arity)) unknown

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallCodebookReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedRangeReceipts
/-! Full raw replacement formation transfers through the actual compiler
matcher. Every retained replacement is located in the genuine source
substitution; order and native erasure play no role. Source validity remains
independent of executable seed acceptance. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedRangeReceipts
open Frontend SourceInference TypeSystem

private theorem binding_member {substitution : TypeSystem.ParameterSubstitution}
    {parameter : TypeParameterId} {type : Ty}
    (found : SourceCompilationPlan.exactParameterBinding? substitution parameter = some type) :
    (parameter, type) ∈ substitution := by
  unfold SourceCompilationPlan.exactParameterBinding? at found
  split at found
  · rename_i selected filtered
    have member : selected ∈ substitution.filter (fun item => item.1 == parameter) := by
      rw [filtered]
      exact List.mem_singleton_self _
    obtain ⟨member, key⟩ := List.mem_filter.mp member
    have keyEq : selected.1 = parameter := LawfulBEq.eq_of_beq key
    have typeEq : selected.2 = type := Option.some.inj found
    have same : selected = (parameter, type) := Prod.ext keyEq typeEq
    rwa [same] at member
  · cases found

theorem range_of_equivalent {context : SourceSemantics.Context}
    {left right : TypeSystem.ParameterSubstitution}
    (equivalent : SourceCompilationPlan.parameterSubstitutionsEquivalent left right = true)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed context right) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed context left := by
  have each : ∀ entry ∈ left,
      SourceCompilationPlan.exactParameterBinding? right entry.1 = some entry.2 := by
    simp only [SourceCompilationPlan.parameterSubstitutionsEquivalent, Bool.and_eq_true,
      List.all_eq_true, beq_iff_eq] at equivalent
    exact equivalent.1.2
  intro parameter type member
  exact range parameter type (binding_member (each (parameter, type) member))

theorem range_of_valid_match {context : SourceSemantics.Context}
    {specialized : SourceSpecialization.SpecializedFunction} {instantiation : DeclarationInstantiation}
    (matched : CallableNamedMetadata.Matches specialized instantiation)
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed context specialized.parameterSubstitution := by
  cases valid with
  | intro _ _ _ _ range => exact range_of_equivalent matched.substitution range

theorem range_of_selected {context : SourceSemantics.Context}
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    {specialized : SourceSpecialization.SpecializedFunction}
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (selected : SourceCoreFunctions.selectedSignature policy compilation source node instantiation isReference =
      .ok (index, signature))
    (record : SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed context specialized.parameterSubstitution :=
  range_of_valid_match
    (CallableNamedMetadata.matches_of_exact (NamedCalls.selected_signature_target selected).1 record) valid

private theorem scoped_at_catalog {context : SourceSemantics.Context} {type : Ty}
    (parameters : context.typeParameters = []) (scopedType : TypeWellScoped context [] type) :
    TypeWellScoped (SourceSemantics.Context.ofSignatures context.signatures) [] type := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => TypeWellScoped (.ofSignatures context.signatures) [] type)
    (motive_2 := fun types _ => TypesWellScoped (.ofSignatures context.signatures) [] types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ scopedType
  · intro metavariable member
    cases member
  · intro parameter member _
    rw [parameters] at member
    cases member
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments member arity _ argumentsTyping
    exact .nominal dataType arguments member arity argumentsTyping
  · intro contract arguments member arity _ argumentsTyping
    exact .contractNominal contract arguments member arity argumentsTyping
  · intro parameter result _ _ left right
    exact .function left right
  · intro left right _ _ leftTyping rightTyping
    exact .product leftTyping rightTyping
  · intro key value _ _ keyTyping valueTyping
    exact .mapping keyTyping valueTyping
  · intro inner _ innerTyping
    exact .proxy innerTyping
  · intro inner _ innerTyping
    exact .comptime innerTyping
  · exact .nil
  · intro head tail _ _ headTyping tailTyping
    exact .cons headTyping tailTyping

theorem range_at_catalog {context : SourceSemantics.Context}
    {substitution : TypeSystem.ParameterSubstitution}
    (parameters : context.typeParameters = [])
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed context substitution) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures context.signatures) substitution := by
  intro parameter type member
  exact ⟨TypeParameterBindersWellFormed.ofSignatures context.signatures,
    scoped_at_catalog parameters (range parameter type member).typeWellScoped⟩

theorem catalog_range_of_selected {context : SourceSemantics.Context}
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    {specialized : SourceSpecialization.SpecializedFunction}
    (parameters : context.typeParameters = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (selected : SourceCoreFunctions.selectedSignature policy compilation source node instantiation isReference =
      .ok (index, signature))
    (record : SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures context.signatures) specialized.parameterSubstitution :=
  range_at_catalog parameters (range_of_selected valid selected record)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedRangeReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSequentialNamedBodyFaultBounds
/-! Actual discard and singleton suffix children run the admitted builtin
producer once each. The reached middle State supplies the next admission. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSequentialNamedBodyFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts
open ReachedNamedSequentialBodyFaultPaths

private def poolBridge {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)} :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

private def returnedControl : Dynamic.ExpressionOutcome → Dynamic.ControlOutcome
  | .value value => .returned value
  | .fault reason => .fault reason

section Finite
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {program : Program}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {statement last : StatementId} {node lastNode : StatementNode} {expression lastExpression : ExpressionId}
  {expressionNode lastExpressionNode : ExpressionNode} {fuel lastFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {lowered lastLowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {fellThrough escaped : Word}
  (sequential : SequentialAt (.initial checked) function context scope statement node expression expressionNode fuel
    last lastNode lastExpression lastExpressionNode lastFuel solved reasonAt lowered lastLowered body fellThrough escaped)

include sequential in
private theorem emitted_rename (ξ : Renaming) :
    body.rename ξ = CompatibleStatements.finish lastLowered.type
      (LocalSequence.discard (LocalLoop.controlType lastLowered.type) (lowered.expression.rename ξ)
        (LocalLoop.returnValue lastLowered.type (lastLowered.expression.rename ξ))) fellThrough escaped := by
  rw [sequential.emitted, ImperativeFunctionFinish.rename, LoopRenaming.discard, LoopRenaming.returnValue]

include sequential in
private theorem finished_head {actual : Environment} {initialStore bodyStore : Store} {ξ : Renaming}
    {token : Word}
    (first : Evaluates actual initialStore (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) bodyStore) :
    Evaluates actual initialStore (body.rename ξ) (.inLeft lastLowered.type (.word token)) bodyStore := by
  rw [emitted_rename sequential]
  exact LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped
    (LocalSequence.discard_failure _ first))

include sequential in
private theorem finish_tail {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {sourceValue : Dynamic.Value} {payload value : Value} {outcome : Dynamic.ExpressionOutcome}
    {actual : Environment} {initialStore middleStore bodyStore : Store} {ξ : Renaming}
    {initialMap middleMap finalMap : LocationMap} {initialWorld middleWorld finalWorld : StoreTyping}
    (sourceFirst : Dynamic.ExpressionEvaluates program context function.evidence function.source environment before expression sourceValue middle)
    (first : Evaluates actual initialStore (lowered.expression.rename ξ) (.inRight .word payload) middleStore)
    (middleHeaps : CompatibleAmbientHeap.HeapRepresents checked registry functions middleMap middleWorld middle middleStore)
    (firstMaps : LocationMap.Extends initialMap middleMap) (firstWorlds : WorldExtends initialWorld middleWorld)
    (firstFrame : AdministrativePreserved initialMap initialStore middleMap middleStore)
    (firstMetadata : Dynamic.HeapMetadataExtend before middle)
    (maps : LocationMap.Extends middleMap finalMap) (worlds : WorldExtends middleWorld finalWorld)
    (frame : AdministrativePreserved middleMap middleStore finalMap bodyStore) (metadata : Dynamic.HeapMetadataExtend middle after)
    (sourceLast : Dynamic.ExpressionEvaluatesOutcome program context function.evidence function.source environment middle lastExpression outcome after)
    (second : Evaluates (payload :: actual) middleStore
      (lastLowered.expression.rename (Renaming.comp (Renaming.insertion 0) ξ)) value bodyStore)
    (represented : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
      finalMap finalWorld lastExpressionNode.type lastLowered.type faults outcome value)
    (retained : ExpressionFailurePostContracts.OutcomePost
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry)
      program context function.evidence function.source environment middle lastExpression lastLowered.type
      outcome after value finalMap finalWorld bodyStore) :
    ∃ result,
      Evaluates actual initialStore (body.rename ξ) result bodyStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        finalMap finalWorld function.resultType lastLowered.type faults outcome result ∧
      OutcomePost (model_bodyPost checked functions registry) program function context environment before
        actual initialStore (body.rename ξ) lastLowered.type outcome after result finalMap finalWorld bodyStore := by
  have rawUnit : ∀ next, returnedControl outcome = Dynamic.ControlOutcome.fallthrough next → function.resultType = .unit := by
    cases outcome <;> intro next same <;> cases same
  have transfers : ImperativeFunctionFinish.TransferFaults faults escaped (returnedControl outcome) := by
    cases outcome <;> constructor <;> intro next same <;> cases same
  obtain ⟨flowValue, returnEvaluation, flowRelated⟩ : ∃ flowValue,
      Evaluates (payload :: actual) middleStore
        (LocalLoop.returnValue lastLowered.type (lastLowered.expression.rename (Renaming.comp (Renaming.insertion 0) ξ))) flowValue bodyStore ∧
      TypedLexicalWhile.FlowRep (values := .initial checked) (ambient := ambient) (registry := registry)
        functions finalMap finalWorld faults function.resultType lastLowered.type (returnedControl outcome) flowValue := by
    cases represented with
    | value related => exact ⟨_, LocalLoop.returnValue_success _ second, .returned (sequential.final.resultType ▸ related)⟩
    | fault matched => exact ⟨_, LocalLoop.returnValue_failure _ second, .fault matched⟩
  have suffixEvaluation : Evaluates (payload :: actual) middleStore
      ((LocalLoop.returnValue lastLowered.type (lastLowered.expression.rename ξ)).weakenAt 0) flowValue bodyStore := by
    rw [← LoopRenaming.returnValue, ← GenericExpressionMeaning.rename_prefix, LoopRenaming.returnValue]
    exact returnEvaluation
  have flowEvaluation := LocalSequence.discard_success (LocalLoop.controlType lastLowered.type) first suffixEvaluation
  obtain ⟨result, completed, finished⟩ := ImperativeFunctionFinish.from_flow_with_transfers
    (values := .initial checked) (ambient := ambient) (mapping := finalMap) (world := finalWorld)
    (faults := faults) (outcome := returnedControl outcome)
    functions rawUnit sequential.final.projection fellThrough escaped transfers flowRelated flowEvaluation
  have bodyEvaluation : Evaluates actual initialStore (body.rename ξ) result bodyStore := by
    rw [emitted_rename sequential]
    exact completed
  refine ⟨result, bodyEvaluation, ?_, ?_⟩
  · cases outcome with
    | value source => exact ImperativeFunctionFinish.result finished (CompatibleNamedBody.Exit.returned source)
    | fault reason => exact ImperativeFunctionFinish.result finished (CompatibleNamedBody.Exit.fault reason)
  · cases outcome with
    | value source => trivial
    | fault reason =>
      cases sourceLast with | fault failed =>
        obtain ⟨token, sameValue, origin⟩ := retained
        have faultChild : Evaluates (payload :: actual) middleStore
            (lastLowered.expression.rename (Renaming.comp (Renaming.insertion 0) ξ))
            (.inLeft lastLowered.type (.word token)) bodyStore := sameValue ▸ second
        have faultSuffix := LocalLoop.returnValue_failure _ faultChild
        have faultDiscard : Evaluates actual initialStore
            (LocalSequence.discard (LocalLoop.controlType lastLowered.type) (lowered.expression.rename ξ)
              (LocalLoop.returnValue lastLowered.type (lastLowered.expression.rename ξ)))
            (.inLeft (LocalLoop.controlType lastLowered.type) (.word token)) bodyStore := by
          apply LocalSequence.discard_success _ first
          rw [← LoopRenaming.returnValue, ← GenericExpressionMeaning.rename_prefix, LoopRenaming.returnValue]
          exact faultSuffix
        have faultBody : Evaluates actual initialStore (body.rename ξ) (.inLeft lastLowered.type (.word token)) bodyStore := by
          rw [emitted_rename sequential]
          exact LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped faultDiscard)
        exact ⟨token, (evaluation_deterministic bodyEvaluation faultBody).1,
          model_bodyPost.of_tail sequential sourceFirst first middleHeaps firstMaps firstWorlds firstFrame firstMetadata
            maps worlds frame metadata failed origin faultChild faultBody⟩
include sequential in
private theorem trace_head {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {childSize : Nat} {reason : Dynamic.SemanticFault}
    (failed : SourceExecutionSize.ExpressionFaults program childSize context function.evidence function.source
      environment before expression reason after) :
    ∃ size, RecursiveNamedCallBounds.BodyTrace program size function context environment before (.fault reason) after := by
  refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [childSize]], .fault (finalContext := context) ?_⟩
  rw [sequential.statements]
  exact .head (.expression (lookupStatement?_sound sequential.found) sequential.form failed)

include sequential in
private theorem trace_tail {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {sourceValue : Dynamic.Value} {firstSize lastSize : Nat} {outcome : Dynamic.ExpressionOutcome}
    (first : SourceExecutionSize.ExpressionEvaluates program firstSize context function.evidence function.source
      environment before expression sourceValue middle)
    (second : RecursiveNamedCallBounds.ExpressionOutcome program lastSize context function.evidence function.source
      environment middle lastExpression outcome after) :
    ∃ size, RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after := by
  have sourceHead : SourceExecutionSize.StatementExecutes program (SourceExecutionSize.stepSize [firstSize])
      context function.evidence function.source environment before statement context (.fallthrough environment) middle :=
    .expression (lookupStatement?_sound sequential.found) sequential.form first
  cases outcome with
  | value sourceValue =>
    cases second with | value child =>
      rcases sequential.final.form with tail | returning
      · refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [firstSize], SourceExecutionSize.stepSize [lastSize]],
          .returned (finalContext := context) ?_⟩
        rw [sequential.statements]
        exact .cons sourceHead (.tailExpression (lookupStatement?_sound sequential.final.found) tail child)
      · refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [firstSize],
          SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [lastSize]]], .returned (finalContext := context) ?_⟩
        rw [sequential.statements]
        exact .cons sourceHead (.singleton (lookupStatement?_sound sequential.final.found)
          (by intro expression; simp [returning]) (.returnValue (lookupStatement?_sound sequential.final.found) returning child))
  | fault reason =>
    cases second with | fault child =>
      rcases sequential.final.form with tail | returning
      · refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [firstSize], SourceExecutionSize.stepSize [lastSize]],
          .fault (finalContext := context) ?_⟩
        rw [sequential.statements]
        exact .tail sourceHead (.tailExpression (lookupStatement?_sound sequential.final.found) tail child)
      · refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [firstSize],
          SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [lastSize]]], .fault (finalContext := context) ?_⟩
        rw [sequential.statements]
        exact .tail sourceHead (.singleton (.returnValue (lookupStatement?_sound sequential.final.found) returning child))

end Finite

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {locations : CallableIndexedOwnedFunctionValues.Header compiled program → Location} {capturePrefix : Nat}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  {statement last : StatementId} {node lastNode : StatementNode} {expression lastExpression : ExpressionId}
  {expressionNode lastExpressionNode : ExpressionNode} {fuel lastFuel : Nat}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {lowered lastLowered : SourceCoreBasic.LoweredExpr} {fellThrough escaped : Word}
  (sequential : SequentialAt (.initial compiled.compatible.checked) header.function header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) statement node expression expressionNode fuel
    last lastNode lastExpression lastExpressionNode lastFuel solved reasonAt lowered lastLowered header.body fellThrough escaped)
  (nativeType : lastLowered.type = header.output)
  (source : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (valid : CompatibleExpressionLiterals.ContextValid solved header.context header.function.evidence)
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults)
  (lastReads : ReachedLoweredReadOutcomePorts.ReadPolicies lastFuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked)
    header.function.source functions registry program header.context header.function.evidence reasonAt faults)
  (unique : NodeOccurrencesUnique header.function.source) (wellFormed : ProgramWellFormed program)

include sequential nativeType source rows extension faithful observations functionTypes valid reads lastReads missing unique wellFormed in
/-- The original sized Source discard selects the real first child and actual
middle State before the admitted suffix producer is called. -/
theorem source_body_with_post [FunctionCalls.FaultTokens faults] (size : Nat) :
    SourceBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
  intro outcome after bodyTrace
  obtain ⟨finalContext, control, flowTrace, exit⟩ := RecursiveNamedFunctionFinishBounds.trace_flow bodyTrace
  rw [sequential.statements] at flowTrace
  have admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context reached :=
    ⟨source.heapTyped, rows⟩
  rcases RecursiveNamedLexicalTreeSourceBounds.discard unique sequential.found sequential.form
      (by simp) flowTrace with
    ⟨childSize, reason, rfl, rfl, failed, _strict⟩ |
    ⟨childSize, tailSize, sourceValue, middle, firstTrace, tailTrace, _firstStrict, _tailStrict⟩
  · cases exit
    obtain ⟨value, bodyStore, finalMap, finalWorld, first, represented, finalHeaps,
        maps, worlds, frame, metadata, finalState, related, _postAdmission, retained⟩ :=
      CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
        functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
        valid reads missing unique wellFormed source.runtime source.covers sequential.tree sequential.expressionFound sequential.expressionTyped
        entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted (.fault failed)
    cases represented with | @fault _ oldToken matched =>
      obtain ⟨token, sameValue, origin⟩ := CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained first
      have tokenSame : oldToken = token := by simpa using sameValue
      subst token
      have bodyEvaluation := finished_head sequential first
      refine ⟨_, bodyStore, finalMap, finalWorld, bodyEvaluation, ?_, finalHeaps, maps, worlds, frame,
        metadata, ⟨finalState, related⟩, ?_⟩
      · simpa only [nativeType] using (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (mapping := finalMap) (world := finalWorld) (sourceType := header.function.resultType) (type := lastLowered.type) matched)
      · exact ⟨oldToken, by simp [nativeType], model_bodyPost.of_head sequential failed.sound origin first bodyEvaluation⟩
  · have selected : finalContext = header.context ∧ ∃ finalSize finalOutcome,
        RecursiveNamedCallBounds.ExpressionOutcome program finalSize header.context header.function.evidence
          header.function.source entry.environment middle lastExpression finalOutcome after ∧
        control = returnedControl finalOutcome ∧ finalSize < tailSize := by
      rcases sequential.final.form with tail | returning
      · exact RecursiveNamedStatementSourceBounds.tail_inv unique (lookupStatement?_sound sequential.final.found) tail tailTrace
      · exact RecursiveNamedLexicalTreeSourceBounds.returning unique sequential.final.found returning tailTrace
    obtain ⟨rfl, finalSize, finalOutcome, finalTrace, rfl, _strict⟩ := selected
    obtain ⟨firstValue, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstAdmission, _retained⟩ :=
      CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
        functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
        valid reads missing unique wellFormed source.runtime source.covers sequential.tree sequential.expressionFound sequential.expressionTyped
        entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted (.value firstTrace)
    cases represented with | @value _ payload representedFirst =>
      obtain ⟨_sourceTyped, middleAdmission⟩ := firstAdmission.at_value
      obtain ⟨value, bodyStore, finalMap, finalWorld, second, represented, finalHeaps,
          maps, worlds, frame, metadata, finalState, finalRelated, _postAdmission, retained⟩ :=
        CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves (poolBridge (headers := headers) (keys := keys))
          functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
          valid lastReads missing unique wellFormed source.runtime source.covers sequential.final.tree
          sequential.final.expressionFound sequential.final.expressionTyped
          (entry.environments.extend firstMaps firstWorlds) middleHeaps (source.locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix entry.lookups payload)
          (.cons representedFirst.runtime_hasType (entry.actualTyped.weaken firstWorlds)) middleState middleAdmission finalTrace
      have retainedAt : ExpressionFailurePostContracts.OutcomePost
          (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
          program header.context header.function.evidence header.function.source entry.environment middle
          lastExpression lastLowered.type finalOutcome after value finalMap finalWorld bodyStore := by
        cases finalOutcome with
        | value v => trivial
        | fault reason => exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained second
      obtain ⟨result, bodyEvaluation, finished, retainedBody⟩ := finish_tail sequential firstTrace.sound first
        middleHeaps firstMaps firstWorlds firstFrame firstMetadata maps worlds frame metadata
        finalTrace.sound second represented retainedAt
      refine ⟨result, bodyStore, finalMap, finalWorld, bodyEvaluation, ?_, finalHeaps,
        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
        ⟨finalState, (protocol headers keys).trans firstRelated finalRelated⟩, ?_⟩
      · cases finalOutcome <;> cases exit <;> simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using finished
      · cases finalOutcome <;> cases exit <;> simpa only [nativeType] using retainedBody

include sequential nativeType source rows extension faithful observations functionTypes valid reads lastReads missing unique wellFormed in
/-- Actual finish/discard/returnValue children select genuine native completions;
Source grades come independently from the two admitted expression producers. -/
theorem native_body_with_post [FunctionCalls.FaultTokens faults] (size : Nat) :
    NativeBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
      (faults := faults) entry reached size := by
  intro value finalStore bodyCompletion
  have nativeFinish : EvaluationSize size entry.actualBody entry.store
      (CompatibleStatements.finish lastLowered.type
        (LocalSequence.discard (LocalLoop.controlType lastLowered.type) (lowered.expression.rename entry.embedding)
          (LocalLoop.returnValue lastLowered.type (lastLowered.expression.rename entry.embedding)))
        fellThrough escaped) value finalStore := by
    rw [← emitted_rename sequential]
    exact bodyCompletion
  obtain ⟨flowSize, flowValue, flowStore, _flowStrict, flowCompletion⟩ := RecursiveNamedCallBounds.finish_flow nativeFinish
  obtain ⟨firstSize, middleStore, firstValue, _firstStrict, firstCompletion⟩ := flowCompletion.bind_computation
  have admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context reached :=
    ⟨source.heapTyped, rows⟩
  obtain ⟨sourceSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, firstRepresented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstAdmission, retained⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects (poolBridge (headers := headers) (keys := keys))
      functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
      valid reads missing unique wellFormed source.runtime source.covers sequential.tree sequential.expressionFound sequential.expressionTyped
      entry.environments entry.heaps source.locals entry.lookups entry.actualTyped reached admitted firstCompletion
  cases firstRepresented with
  | @fault reason oldToken matched =>
    cases firstTrace with | fault failed =>
      obtain ⟨token, sameValue, origin⟩ := CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained firstCompletion.sound
      have tokenSame : oldToken = token := by simpa using sameValue
      subst token
      have bodyEvaluation := finished_head sequential firstCompletion.sound
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyCompletion.sound bodyEvaluation
      obtain ⟨bodySize, sourceTrace⟩ := trace_head sequential failed
      refine ⟨bodySize, .fault reason, middle, middleMap, middleWorld, sourceTrace, ?_, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, ⟨middleState, firstRelated⟩, ?_⟩
      · simpa only [nativeType] using (FunctionCalls.ResultRepresents.fault
          (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (mapping := middleMap) (world := middleWorld) (sourceType := header.function.resultType)
          (type := lastLowered.type) matched)
      · exact ⟨oldToken, by simp [nativeType],
          model_bodyPost.of_head sequential failed.sound origin firstCompletion.sound bodyEvaluation⟩
  | @value sourceValue payload representedFirst =>
    cases firstTrace with | value sourceFirst =>
      obtain ⟨_sourceTyped, middleAdmission⟩ := firstAdmission.at_value
      obtain ⟨suffixSize, _suffixStrict, suffixCompletion⟩ := flowCompletion.bind_success firstCompletion.sound
      have returnCompletion : EvaluationSize suffixSize (payload :: entry.actualBody) middleStore
          (LocalLoop.returnValue lastLowered.type
            (lastLowered.expression.rename (Renaming.comp (Renaming.insertion 0) entry.embedding)))
          flowValue flowStore := by
        rw [← LoopRenaming.returnValue, GenericExpressionMeaning.rename_prefix, LoopRenaming.returnValue]
        exact suffixCompletion
      obtain ⟨lastSize, bodyStore, lastValue, _lastStrict, lastCompletion⟩ := returnCompletion.bind_computation
      obtain ⟨lastSourceSize, lastOutcome, after, finalMap, finalWorld, lastTrace, represented, finalHeaps,
          maps, worlds, frame, metadata, finalState, finalRelated, _postAdmission, retained⟩ :=
        CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects (poolBridge (headers := headers) (keys := keys))
          functions header.function.evidence (administrativeTransport headers keys) extension faithful observations functionTypes
          valid lastReads missing unique wellFormed source.runtime source.covers sequential.final.tree
          sequential.final.expressionFound sequential.final.expressionTyped
          (entry.environments.extend firstMaps firstWorlds) middleHeaps (source.locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix entry.lookups payload)
          (.cons representedFirst.runtime_hasType (entry.actualTyped.weaken firstWorlds)) middleState middleAdmission lastCompletion
      have retainedAt : ExpressionFailurePostContracts.OutcomePost
          (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
          program header.context header.function.evidence header.function.source entry.environment middle
          lastExpression lastLowered.type lastOutcome after lastValue finalMap finalWorld bodyStore := by
        cases lastOutcome with
        | value v => trivial
        | fault reason => exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained lastCompletion.sound
      obtain ⟨result, bodyEvaluation, finished, retainedBody⟩ := finish_tail sequential sourceFirst.sound firstCompletion.sound
        middleHeaps firstMaps firstWorlds firstFrame firstMetadata maps worlds frame metadata
        lastTrace.sound lastCompletion.sound represented retainedAt
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyCompletion.sound bodyEvaluation
      obtain ⟨bodySize, sourceTrace⟩ := trace_tail sequential sourceFirst lastTrace
      refine ⟨bodySize, lastOutcome, after, finalMap, finalWorld, sourceTrace, ?_, finalHeaps,
        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
        ⟨finalState, (protocol headers keys).trans firstRelated finalRelated⟩, ?_⟩
      · simpa only [nativeType, SourceCoreCompatibleValues.Context.initial] using finished
      · simpa only [nativeType] using retainedBody

include sequential nativeType source rows extension faithful observations functionTypes valid reads lastReads missing unique wellFormed in
/-- Every strict Source member is derived by the same concrete sequential theorem. -/
theorem source_below [FunctionCalls.FaultTokens faults] (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact source_body_with_post functions entry reached sequential nativeType source rows extension faithful
    observations functionTypes valid reads lastReads missing unique wellFormed child

include sequential nativeType source rows extension faithful observations functionTypes valid reads lastReads missing unique wellFormed in
/-- The native strict member uses its actual whole body completion. -/
theorem native_below [FunctionCalls.FaultTokens faults] (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (model_bodyPost compiled.compatible.checked functions registry)
        (faults := faults) entry reached) := by
  intro child _strict
  exact native_body_with_post functions entry reached sequential nativeType source rows extension faithful
    observations functionTypes valid reads lastReads missing unique wellFormed child

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSequentialNamedBodyFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBodyPostProviders
/-! The actual successful argument and parameter receipts supply concrete
singleton/sequential body posts. The outer named/direct core consumes them
once and retains its full call route at the same returned caller tuple. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBodyPostProviders
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts
open RecursiveNamedBoundedContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The exact singleton emission and pointwise primitive diagnostic receipts. -/
structure PrimitiveInputs (header : CallableIndexedOwnedFunctionValues.Header compiled program) where
  statement : StatementId
  node : StatementNode
  expression : ExpressionId
  expressionNode : ExpressionNode
  fuel : Nat
  solved : List SolvedRequirement
  reasonAt : ExpressionId → Word
  lowered : SourceCoreBasic.LoweredExpr
  fellThrough : Word
  escaped : Word
  singleton : ReachedNamedPrimitiveBodyFaultPaths.SingletonAt (.initial compiled.compatible.checked)
    header.function header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    statement node expression expressionNode fuel solved reasonAt lowered header.body fellThrough escaped
  output : lowered.type = header.output
  valid : CompatibleExpressionLiterals.ContextValid solved header.context header.function.evidence
  reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults
  missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked)
    header.function.source functions registry program header.context header.function.evidence reasonAt faults
  unique : NodeOccurrencesUnique header.function.source

/-- The actual first discard and its literal singleton suffix at the same Header. -/
structure SequentialInputs (header : CallableIndexedOwnedFunctionValues.Header compiled program) where
  statement : StatementId
  node : StatementNode
  expression : ExpressionId
  expressionNode : ExpressionNode
  fuel : Nat
  last : StatementId
  lastNode : StatementNode
  lastExpression : ExpressionId
  lastExpressionNode : ExpressionNode
  lastFuel : Nat
  solved : List SolvedRequirement
  reasonAt : ExpressionId → Word
  lowered : SourceCoreBasic.LoweredExpr
  lastLowered : SourceCoreBasic.LoweredExpr
  fellThrough : Word
  escaped : Word
  sequential : ReachedNamedSequentialBodyFaultPaths.SequentialAt (.initial compiled.compatible.checked)
    header.function header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    statement node expression expressionNode fuel last lastNode lastExpression lastExpressionNode lastFuel
    solved reasonAt lowered lastLowered header.body fellThrough escaped
  output : lastLowered.type = header.output
  valid : CompatibleExpressionLiterals.ContextValid solved header.context header.function.evidence
  reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults
  lastReads : ReachedLoweredReadOutcomePorts.ReadPolicies lastFuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults
  missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked)
    header.function.source functions registry program header.context header.function.evidence reasonAt faults
  unique : NodeOccurrencesUnique header.function.source

/-- A genuine static domain selects a concrete producer, never a completed body law. -/
inductive BodyInputs (header : CallableIndexedOwnedFunctionValues.Header compiled program) : Prop where
  | primitive (inputs : PrimitiveInputs (program := program) (registry := registry) (faults := faults) functions header) : BodyInputs header
  | sequential (inputs : SequentialInputs (program := program) (registry := registry) (faults := faults) functions header) : BodyInputs header

/-- Both concrete paths retain their original complete literal body post. -/
def FaultPost : BodyFaultPost := fun program function context environment before actual initialStore body
    reason after token mapping world store =>
  ReachedNamedPrimitiveBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry
    program function context environment before actual initialStore body reason after token mapping world store ∨
  ReachedNamedSequentialBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry
    program function context environment before actual initialStore body reason after token mapping world store

section Body
variable {functions}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {locations : RecursiveNamedCatalog.Locations} {capturePrefix : Nat}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (source : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed program)

include source rows extension faithful observations functionTypes wellFormed in
/-- The concrete source child runs its selected existing producer once. -/
theorem BodyInputs.source_below [FunctionCalls.FaultTokens faults] (inputs : BodyInputs (program := program) (registry := registry) (faults := faults) functions header)
    (budget : Nat) : RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (FaultPost functions (registry := registry)) (faults := faults) entry reached) := by
  cases inputs with
  | primitive inputs =>
    intro child _strict
    intro outcome after trace
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, result, finalHeaps,
      maps, worlds, frame, metadata, returned, retained⟩ :=
      CallableIndexedOwnedPrimitiveNamedBodyFaultBounds.source_body_with_post
        functions entry reached inputs.singleton inputs.output source rows extension faithful observations functionTypes
        inputs.valid inputs.reads inputs.missing inputs.unique wellFormed child trace
    refine ⟨value, finalStore, finalMap, finalWorld, completed, result, finalHeaps,
      maps, worlds, frame, metadata, returned, ?_⟩
    cases outcome with
    | value value => trivial
    | fault reason =>
      obtain ⟨token, same, post⟩ := retained
      exact ⟨token, same, Or.inl post⟩

  | sequential inputs =>
    intro child _strict
    intro outcome after trace
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, result, finalHeaps,
      maps, worlds, frame, metadata, returned, retained⟩ :=
      CallableIndexedOwnedSequentialNamedBodyFaultBounds.source_body_with_post
        functions entry reached inputs.sequential inputs.output source rows extension faithful observations functionTypes
        inputs.valid inputs.reads inputs.lastReads inputs.missing inputs.unique wellFormed child trace
    refine ⟨value, finalStore, finalMap, finalWorld, completed, result, finalHeaps,
      maps, worlds, frame, metadata, returned, ?_⟩
    cases outcome with
    | value value => trivial
    | fault reason =>
      obtain ⟨token, same, post⟩ := retained
      exact ⟨token, same, Or.inr post⟩

include source rows extension faithful observations functionTypes wellFormed in
/-- The concrete native child runs its selected existing producer once. -/
theorem BodyInputs.native_below [FunctionCalls.FaultTokens faults] (inputs : BodyInputs (program := program) (registry := registry) (faults := faults) functions header)
    (budget : Nat) : RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (FaultPost functions (registry := registry)) (faults := faults) entry reached) := by
  cases inputs with
  | primitive inputs =>
    intro child _strict
    intro value finalStore completed
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
      maps, worlds, frame, metadata, returned, retained⟩ :=
      CallableIndexedOwnedPrimitiveNamedBodyFaultBounds.native_body_with_post
        functions entry reached inputs.singleton inputs.output source rows extension faithful observations functionTypes
        inputs.valid inputs.reads inputs.missing inputs.unique wellFormed child completed
    refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
      maps, worlds, frame, metadata, returned, ?_⟩
    cases outcome with
    | value value => trivial
    | fault reason =>
      obtain ⟨token, same, post⟩ := retained
      exact ⟨token, same, Or.inl post⟩

  | sequential inputs =>
    intro child _strict
    intro value finalStore completed
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
      maps, worlds, frame, metadata, returned, retained⟩ :=
      CallableIndexedOwnedSequentialNamedBodyFaultBounds.native_body_with_post
        functions entry reached inputs.sequential inputs.output source rows extension faithful observations functionTypes
        inputs.valid inputs.reads inputs.lastReads inputs.missing inputs.unique wellFormed child completed
    refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
      maps, worlds, frame, metadata, returned, ?_⟩
    cases outcome with
    | value value => trivial
    | fault reason =>
      obtain ⟨token, same, post⟩ := retained
      exact ⟨token, same, Or.inr post⟩

end Body

section Providers
variable {functions}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {callerPrefix : Nat} {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner callerPrefix index.scope index.canonical) callerProtocol)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical : Environment} {environment : Dynamic.Environment}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge) context initial)
  {originalTypes : List TypeSystem.Ty} {rawResult : TypeSystem.Ty} {predicates : List ProgramPredicate}
  (wellFormed : ProgramWellFormed program)
  (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (argumentTypes : ExpressionsHaveTypes source context ids originalTypes)
  (application : SourceSemantics.DeclarationApplicationValid context header.instantiation originalTypes rawResult predicates)
  (inputs : BodyInputs (program := program) (registry := registry) (faults := faults) functions header)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include admitted wellFormed sourceRuntime covers locals argumentTypes application inputs extension faithful observations functionTypes in
/-- The original successful arguments supply the exact parameter receipt;
only the concrete strict body producer is invoked. -/
theorem source_invocations [FunctionCalls.FaultTokens faults] (budget : Nat) :
    CallableIndexedOwnedExpressionHeads.SourceInvocationsForWithPost (post := FaultPost functions (registry := registry)) (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
    origin index metadata administrative actualContext actual ξ frameLocation physical selected history emitted
    entry agreement parameterPool parameterRelated _allowed child strict outcome after trace
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner (bridge.pool argumentState) header arguments :=
    { origin := origin, index := index, metadata := metadata, administrative := administrative,
      actualContext := actualContext, actual := actual, embedding := ξ, frameLocation := frameLocation,
      physical := physical, selected := selected, history := history, emitted := emitted,
      body := entry, reached := parameterPool, related := parameterRelated, stable := stable,
      heapTyped := sourceAdmission.1, argumentsTyped := sourceAdmission.2 }
  exact inputs.source_below receipt.body receipt.reached (receipt.source wellFormed) receipt.rows
    extension faithful observations functionTypes wellFormed budget child strict trace


include admitted wellFormed sourceRuntime covers locals argumentTypes application inputs extension faithful observations functionTypes in
/-- The original successful arguments supply the exact parameter receipt;
only the concrete strict body producer is invoked. -/
theorem native_invocations [FunctionCalls.FaultTokens faults] (budget : Nat) :
    CallableIndexedOwnedExpressionHeads.NativeInvocationsForWithPost (post := FaultPost functions (registry := registry)) (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
    origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical selected history emitted prefixRun prefixWithin restored entry parameterPool parameterRelated _allowed child strict
    bodyValue bodyFinalStore completed
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner (bridge.pool argumentState) header arguments :=
    { origin := origin, index := index, metadata := metadata, administrative := administrative,
      actualContext := actualContext, actual := actual, embedding := ξ, frameLocation := frameLocation,
      physical := physical, selected := selected, history := history, emitted := emitted,
      body := entry, reached := parameterPool, related := parameterRelated, stable := stable,
      heapTyped := sourceAdmission.1, argumentsTyped := sourceAdmission.2 }
  exact inputs.native_below receipt.body receipt.reached (receipt.source wellFormed) receipt.rows
    extension faithful observations functionTypes wellFormed budget child strict completed


end Providers

section Heads
variable {functions}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {compilation : SourceCoreFunctions.Context}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (caller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
    callerProtocol)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate}
  (wellFormed : ProgramWellFormed program) (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

/-- The admitted outer tuple also retains the exact selected low route. -/
def PreservesHeadAtWithPost (size : Nat) : Prop :=
  ∀ {scope id lowered}, RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers compilation source context evidence certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) context initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) context node.type outcome reached ∧
        NamedExpressionBodyFaultPostContracts.OuterCallRouteAt
          (functions := functions) (registry := registry) (source := source) (context := context)
          (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
          (FaultPost functions (registry := registry)) owner caller initial
          compilation.administrativePrefix compilation.internalReason size none
          id node lowered outcome after value finalMap finalWorld finalStore

/-- The admitted outer tuple also retains the exact selected low route. -/
def ReflectsHeadAtWithPost (size : Nat) : Prop :=
  ∀ {scope id lowered}, RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers compilation source context evidence certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) context node.type outcome reached ∧
        NamedExpressionBodyFaultPostContracts.OuterCallRouteAt
          (functions := functions) (registry := registry) (source := source) (context := context)
          (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
          (FaultPost functions (registry := registry)) owner caller initial
          compilation.administrativePrefix compilation.internalReason sourceSize (some size)
          id node lowered outcome after value finalMap finalWorld finalStore

include wellFormed sourceRuntime covers unique sameLayouts extension faithful observations functionTypes owners idsUnique in
/-- Strict actual argument children and a genuine selected static body domain
derive both providers internally, then retain the original reached admission. -/
theorem preserves_head_with_body_post [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (inputs : ∀ {id node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      ∀ header, header ∈ headers → ∀ {callee ids}, node.form = .call callee ids (.declaration header.instantiation) →
      BodyInputs (program := program) (registry := registry) (faults := faults) functions header) :
    PreservesHeadAtWithPost (functions := functions) (registry := registry) (faults := faults)
      (source := source) (context := context) (certificate := certificate) owner caller evidence size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, ⟨reached, related⟩, route⟩ :=
    CallableIndexedOwnedExpressionHeads.preserves_at_with_sequence_with_body_post functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      caller budget size within idsUnique unique owners head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.preserves
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (FaultPost functions (registry := registry))
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact source_invocations
          (owner := owner) (functions := functions) caller initial admitted wellFormed sourceRuntime covers locals
          argumentTypes application (inputs found sourceTyped header member form) extension faithful observations functionTypes budget) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame, route⟩


include wellFormed sourceRuntime covers unique sameLayouts extension faithful observations functionTypes in
/-- Strict actual argument children and a genuine selected static body domain
derive both providers internally, then retain the original reached admission. -/
theorem reflects_head_with_body_post [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (inputs : ∀ {id node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      ∀ header, header ∈ headers → ∀ {callee ids}, node.form = .call callee ids (.declaration header.instantiation) →
      BodyInputs (program := program) (registry := registry) (faults := faults) functions header) :
    ReflectsHeadAtWithPost (functions := functions) (registry := registry) (faults := faults)
      (source := source) (context := context) (certificate := certificate) owner caller evidence size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, ⟨reached, related⟩, route⟩ :=
    CallableIndexedOwnedExpressionHeads.reflects_at_with_sequence_with_body_post functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      caller budget size within head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.reflects
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (FaultPost functions (registry := registry))
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact native_invocations
          (owner := owner) (functions := functions) caller initial admitted wellFormed sourceRuntime covers locals
          argumentTypes application (inputs found sourceTyped header member form) extension faithful observations functionTypes budget) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame, route⟩


end Heads

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBodyPostProviders
end
