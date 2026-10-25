import Solcore.Frontend.RustHull.AccountCallSharedCorrespondence
import Solcore.Frontend.RustHull.AccountCallDispatchCorrespondence

/-! The child interface describes the actual selected frame call under its
captured bindings. Public execution supplies it from compilation and fresh
frame initialization. Empty accounts continue to use the existing runtime path. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

def childRequest (extended : Code) : Code :=
  let request := part 0 3 extended
  packet [choose (binary .wordEq (part 1 3 extended) (number 0))
    (part 0 8 request) (part 2 3 extended),
    part 1 8 request, part 2 8 request, part 3 8 request, part 4 8 request,
    part 5 8 request, part 6 8 request, part 7 8 request]

def dispatchRun (shared : AccountRuntime.References) (runFrame : Code → Code → Code)
    (extended precompiled : Code) : Code :=
  accountRun shared (part 0 8 (part 0 3 extended)) precompiled
    (fun record => runFrame record (childRequest extended))

theorem childRequest_evaluates {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {extended : Code} {source : Core.Word} {request : AccountCallSemantics.Request}
    (argument : CodeValue depth environment extended (extendedValue source request)) :
    Core.Evaluates environment store (childRequest extended depth) (requestValue request) store := by
  have requestCode := argument.part (index := 0) rfl
  apply Core.Evaluates.pair
  · exact .ifTrue (.binary ((argument.part (index := 1) rfl).evaluates store) .word rfl)
      ((requestCode.part (index := 0) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 1) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 2) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 3) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 4) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 5) rfl).evaluates store)
  exact .pair ((requestCode.part (index := 6) rfl).evaluates store)
    ((requestCode.part (index := 7) rfl).evaluates store)

theorem childRequest_value {depth : Nat} {environment : Core.Environment} {extended : Code}
    {source : Core.Word} {request : AccountCallSemantics.Request}
    (argument : CodeValue depth environment extended (extendedValue source request)) :
    CodeValue depth environment (childRequest extended) (requestValue request) := by
  intro extra store
  simpa only [List.length_append, Nat.add_assoc] using childRequest_evaluates (argument.prepend extra) (store := store)

def ChildRunPreservation (anchors : List CatalogWorldCorrespondence.Anchor) (locations : SharedLocations)
    (shared : AccountRuntime.References) (runFrame : Code → Code → Code)
    (children : AccountCallSemantics.Children) (valid : Core.Store → Prop)
    (baseDepth : Nat) (captured : Core.Environment) : Prop :=
  ∀ {source request state result finalState}, children .ordinary source request state result finalState →
  ∀ (extra : Core.Environment) {store : Core.Store} {extended precompiled : Code},
    SharedReferences (baseDepth + extra.length) (extra ++ captured) shared locations →
    CodeValue (baseDepth + extra.length) (extra ++ captured) extended (extendedValue source request) →
    LinkedSharedStateRel anchors locations state store → valid store →
    ∃ target final, Core.Evaluates (extra ++ captured) store
      (dispatchRun shared runFrame extended precompiled (baseDepth + extra.length)) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations store final

theorem ChildRunPreservation.prepend {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {baseDepth : Nat} {captured : Core.Environment}
    (preserved : ChildRunPreservation anchors locations shared runFrame children valid baseDepth captured)
    (front : Core.Environment) :
    ChildRunPreservation anchors locations shared runFrame children valid (baseDepth + front.length) (front ++ captured) := by
  intro source request state result finalState computed extra store extended precompiled references argument related ready
  have references' : SharedReferences (baseDepth + (extra ++ front).length) ((extra ++ front) ++ captured) shared locations := by
    simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using references
  have argument' : CodeValue (baseDepth + (extra ++ front).length) ((extra ++ front) ++ captured) extended (extendedValue source request) := by
    simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using argument
  simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    preserved computed (extra ++ front) references' argument' related ready (precompiled := precompiled)

/-- A selected nonzero identity reaches the actual frame continuation. The
lookup's helper allocation is retained and exposed to the continuation. -/
theorem accountRun_child_evaluates {depth : Nat} {environment : Core.Environment} {initial final : Core.Store}
    {shared : AccountRuntime.References} {targetCode precompiled : Code} {child : Code → Code}
    {locations : SharedLocations} {target : Core.Word} {accounts : StorageCorrespondence.Accounts}
    {account : AccountState.Account} {identity : Nat} {complete : Bool} {result : Core.Value}
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment targetCode (.word target))
    (worldRead : initial.read? locations.world = some (StorageCorrespondence.world accounts))
    (completeRead : initial.read? locations.complete = some (.bool complete))
    (ordinary : AccountCallSemantics.isPrecompile target = false)
    (selected : StorageCorrespondence.lookup target accounts = some (account, identity))
    (nonzero : Core.Word.ofNatModulo identity ≠ Core.Word.zero)
    (continued : Core.Evaluates (StorageCorrespondence.record account identity :: environment)
      (StorageCorrespondence.getStore accounts target complete environment initial)
      (child (fun here => .var (here - depth - 1)) (depth + 1)) result final) :
    Core.Evaluates environment initial (accountRun shared targetCode precompiled child depth) result final := by
  have fetched := StorageCorrespondence.get_evaluates accounts target complete
    (.loadCell (references.world.evaluates initial) worldRead) (argument.evaluates initial)
    (.loadCell (references.complete.evaluates initial) completeRead)
  simp only [StorageCorrespondence.get, selected, StorageCorrespondence.getValue] at fetched
  apply Core.Evaluates.ifFalse (by simpa only [ordinary] using isPrecompile_evaluates argument)
  apply LanguageResult.bind_success Calls.responseType fetched
  have recordValue := CodeValue.bound depth environment (StorageCorrespondence.record account identity)
  apply Core.Evaluates.ifFalse (.binary ((recordValue.part (index := 3) rfl).evaluates _) .word ?_) continued
  change some (Core.Value.bool (Word.ofNatModulo identity == Word.zero)) = some (Core.Value.bool false)
  simp only [beq_eq_false_iff_ne.mpr nonzero]

end Solcore.Frontend.RustHull.AccountCallCorrespondence
