import Solcore.Frontend.RustHull.AccountCallHandlersCorrespondence
import Solcore.Frontend.RustHull.CallTransportValues

/-! Account dispatch captures the four actual shared cells before it checks
funds. The saved expressions retain their lexical bindings through the body. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

def checkpointRestore (shared : AccountRuntime.References) (depth : Nat) : Code :=
  bind (store (AccountRuntime.reference shared "balances") (fun here => .var (here - (depth + 3) - 1))) fun _ =>
  bind (store (AccountRuntime.reference shared "logSize") (fun here => .var (here - (depth + 2) - 1))) fun _ =>
  bind (store (AccountRuntime.reference shared "logs") (fun here => .var (here - (depth + 1) - 1))) fun _ =>
  bind (store (AccountRuntime.reference shared "world") (fun here => .var (here - depth - 1))) fun _ => unit

theorem checkpoint_evaluates {depth : Nat} {environment : Core.Environment} {initial final : Core.Store}
    {shared : AccountRuntime.References} {locations : SharedLocations} {continuation : Code → Code}
    {world logs logSize balances result : Core.Value}
    (references : SharedReferences depth environment shared locations)
    (worldRead : initial.read? locations.world = some world)
    (logsRead : initial.read? locations.logs = some logs)
    (sizeRead : initial.read? locations.logSize = some logSize)
    (balancesRead : initial.read? locations.balances = some balances)
    (continued : Core.Evaluates ([balances, logSize, logs, world] ++ environment) initial
      (continuation (checkpointRestore shared depth) (depth + 4)) result final) :
    Core.Evaluates environment initial (AccountRuntime.checkpoint shared continuation depth) result final := by
  apply Core.Evaluates.letE (.loadCell (references.world.evaluates initial) worldRead)
  apply Core.Evaluates.letE (.loadCell ((references.logs.prepend [world]).evaluates initial) logsRead)
  apply Core.Evaluates.letE (.loadCell ((references.logSize.prepend [logs, world]).evaluates initial) sizeRead)
  apply Core.Evaluates.letE (.loadCell ((references.balances.prepend [logSize, logs, world]).evaluates initial) balancesRead)
  exact continued

theorem SharedStateRel.retained {locations : SharedLocations} {state : AccountCallSemantics.Shared}
    {initial final : Core.Store} (related : SharedStateRel locations state initial)
    (retained : StoreRetains initial final) : SharedStateRel locations state final := by
  have keep {location : Nat} {value : Core.Value} (found : initial.read? location = some value) :
      final.read? location = some value :=
    (retained.read location (List.getElem?_eq_some_iff.mp found).1).trans found
  obtain ⟨accounts, same, found⟩ := related.world
  exact ⟨⟨accounts, same, keep found⟩, keep related.logs, keep related.logSize, keep related.balances,
    keep related.complete, related.distinct⟩

theorem lookup_preserves {environment : Core.Environment} {initial : Core.Store}
    {mapping keyExpr : Core.Expr} {entries : StorageSemantics.Words} {key : Core.Word}
    (mappingEvaluated : Core.Evaluates environment initial mapping (Core.WordMapping.encode entries) initial)
    (keyEvaluated : Core.Evaluates environment initial keyExpr (.word key) initial) :
    ∃ final, Core.Evaluates environment initial (Core.WordMapping.lookup mapping keyExpr)
      (.inRight .word (.word (StorageSemantics.readWord key entries))) final ∧ StoreRetains initial final := by
  have evaluated := WordMapping.lookup_evaluates entries key mappingEvaluated keyEvaluated
  rw [← StorageCorrespondence.readWord_eq] at evaluated
  exact ⟨_, evaluated, StoreRetains.append _ _⟩

end Solcore.Frontend.RustHull.AccountCallCorrespondence
