import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestorationAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries

/-! Named child laws retain the authentic nested packet when a body forms a
closure. Existing pool-only children remain a separate supported branch. The
actual parameter receipt chooses and supplies the runtime input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedChildBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header OwnedKey)
open CallableIndexedOwnedAdmittedStagedExpressionBounds

section Definitions
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (child : Staging.Recursive.Scope)
  (certificate : GenericExpressionMeaning.Certificate) (faults : RecursiveStageMeaning.FaultRep)

abbrev poolBridge := CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
abbrev nestedBridge (owner : OwnedKey keys) := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner header

inductive PreservesBelow (budget : Nat) : Prop where
  | pool (meaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      (poolBridge (headers := headers) (keys := keys)) header.context model stages child certificate faults budget)
  | nested (globals : header.globals = compiled.indexed.base.globals.length)
      (zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0)
      (meaning : ∀ owner : OwnedKey keys, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
        (nestedBridge (headers := headers) header owner) header.context model stages child certificate faults budget)

inductive ReflectsBelow (budget : Nat) : Prop where
  | pool (meaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (poolBridge (headers := headers) (keys := keys)) header.context model stages child certificate faults budget)
  | nested (globals : header.globals = compiled.indexed.base.globals.length)
      (zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0)
      (meaning : ∀ owner : OwnedKey keys, CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
        (nestedBridge (headers := headers) header owner) header.context model stages child certificate faults budget)

end Definitions
section Bodies
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)} {expression : ExpressionId}
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure header.function child)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (certifies : ∀ lowered,
    header.policy.lowerExpression terminal.childFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
    certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before header.context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : State headers keys
    ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, before, store, canonical⟩)
  (admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context initial)
  (owner : OwnedKey keys)
  (packet : owner.key.capturePrefix = 0 → header.globals = compiled.indexed.base.globals.length →
    CallableIndexedOwnedNestedCanonicalState.Packet owner header _ initial)

include selected wellFormed terminal certifies environments heaps locals agrees typed admitted packet in
/-- The original named body Source typing and genuine selected child scope
construct preservation from the used strict expression hypothesis. The body
trace and nested failure scope remain recursively staged. -/
theorem preserves_body (budget : Nat)
    (children : PreservesBelow (headers := headers) (keys := keys) header model stages child certificate faults budget)
    {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages size child
      header.context environment before header.function.body finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult header.function.resultType bodyOutcome outcome)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (header.body.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (poolBridge (headers := headers) (keys := keys)) header.context header.function.resultType outcome reached := by
  cases children with
  | pool meaning =>
    exact CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds.preserves_body
      (bridge := poolBridge) selected wellFormed terminal certifies environments heaps locals agrees typed
      initial admitted budget meaning trace matched within
  | nested globals zero meaning =>
    let wrapped : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header).State _ :=
      ⟨initial, packet (zero owner) globals⟩
    have nestedAdmitted : Admission (nestedBridge header owner) header.context wrapped := ⟨admitted.heap, admitted.rows⟩
    obtain ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps, maps, worlds,
      frame, metadata, reached, related, post⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds.preserves_body
        (bridge := nestedBridge header owner) selected wellFormed terminal certifies environments heaps locals agrees typed
        wrapped nestedAdmitted budget (meaning owner) trace matched within
    refine ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps, maps, worlds,
      frame, metadata, reached.val, related, ?_⟩
    cases outcome with
    | value => exact ⟨post.rows, post.successful⟩
    | fault failure =>
      cases failure with
      | semantic => exact ⟨post.rows, post.successful⟩
      | stage => exact post

include selected wellFormed terminal certifies environments heaps locals agrees typed admitted packet in
/-- Literal native body completion reflects to an independently graded staged
Source body, using the same accepted Header code and actual parameter state.
The complete returned pool and successful Source post are retained. -/
theorem reflects_body (budget : Nat)
    (children : ReflectsBelow (headers := headers) (keys := keys) header model stages child certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (header.body.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize child
        header.context environment before header.function.body header.context
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome) after ∧
      Staging.Recursive.BodyResult header.function.resultType
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (poolBridge (headers := headers) (keys := keys)) header.context header.function.resultType outcome reached := by
  cases children with
  | pool meaning =>
    exact CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds.reflects_body
      (bridge := poolBridge) selected wellFormed terminal certifies environments heaps locals agrees typed
      initial admitted budget meaning completed within
  | nested globals zero meaning =>
    let wrapped : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header).State _ :=
      ⟨initial, packet (zero owner) globals⟩
    have nestedAdmitted : Admission (nestedBridge header owner) header.context wrapped := ⟨admitted.heap, admitted.rows⟩
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds.reflects_body
        (bridge := nestedBridge header owner) selected wellFormed terminal certifies environments heaps locals agrees typed
        wrapped nestedAdmitted budget (meaning owner) completed within
    refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, represented, finalHeaps,
      maps, worlds, frame, metadata, reached.val, related, ?_⟩
    cases outcome with
    | value => exact ⟨post.rows, post.successful⟩
    | fault failure =>
      cases failure with
      | semantic => exact ⟨post.rows, post.successful⟩
      | stage => exact post

end Bodies
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedChildBounds
