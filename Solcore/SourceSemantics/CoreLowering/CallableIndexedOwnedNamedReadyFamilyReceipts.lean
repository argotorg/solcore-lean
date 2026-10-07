import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedReadyContinuations
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory

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
