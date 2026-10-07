import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedReadyFamilyReceipts

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
