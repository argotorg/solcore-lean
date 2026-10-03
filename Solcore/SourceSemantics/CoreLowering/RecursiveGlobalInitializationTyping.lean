import Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedContextFrames
import Solcore.Frontend.SourceCoreIndexedSession

/-! The real recipe supplies native typing for its actual bootstrap. Combining
that static receipt with the closed initialization trace gives typed stored
closures and their actual captured environments. Source attribution, heaps and
execution history are constructed separately; runtime type tags do not supply
them. No source function body is evaluated in this module. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationTyping
open Core Frontend
open RecursiveGlobalInitializationMeaning

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

/-- Accepted preparation owns this exact compiled program and this actual
frame/global/cache expression, before any runtime execution. -/
theorem recipe_emitted {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe) :
    recipe.compiled = compiled ∧ recipe.bootstrap =
      SourceCoreCallableIndexedFrames.allocate compiled.indexed.ancestry.layout.frame
        (SourceCoreRecursiveEntry.allocateGlobals compiled.indexed.base.globals.reverse
          (SourceCoreRecursiveEntry.installFunctions compiled.indexed.secondPass.closures (LanguageResult.success .unit))) := by
  unfold SourceCoreIndexedSession.Recipe.prepare at accepted
  obtain ⟨roots, _, accepted⟩ := bind_ok accepted
  obtain ⟨templates, _, accepted⟩ := bind_ok accepted
  obtain ⟨named, _, accepted⟩ := bind_ok accepted
  obtain ⟨builtins, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
    exact ⟨rfl, rfl⟩
  · cases accepted

def initialEnvironment (signatures : List Signature) (layout : SourceCoreCallableIndexedFrames.Layout) : Environment :=
  (reserve signatures.reverse [SourceCoreCallableIndexedFrames.encode layout .empty] [.cellRef layout.type 0]).2

def initialStore (signatures : List Signature) (rows : List LambdaRow)
    (layout : SourceCoreCallableIndexedFrames.Layout) : Store :=
  installStore rows (fun index => 1 + (signatures.length - 1 - index))
    (initialEnvironment signatures layout)
    (reserve signatures.reverse [SourceCoreCallableIndexedFrames.encode layout .empty] [.cellRef layout.type 0]).1 0

/-- Frame allocation is part of the actual original native trace. The history
attached to its empty value is established later from the empty constructor. -/
theorem framed_bootstrap (signatures : List Signature) (rows : List LambdaRow)
    (layout : SourceCoreCallableIndexedFrames.Layout)
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      signatures[i]? = some signature ∧ signature.functionType = .function row.parameter row.result) :
    Evaluates [] [] (SourceCoreCallableIndexedFrames.allocate layout
      (SourceCoreRecursiveEntry.allocateGlobals signatures.reverse
        (SourceCoreRecursiveEntry.installFunctions (rows.map LambdaRow.expression) (LanguageResult.success .unit))))
      (.inRight .word .unit) (initialStore signatures rows layout) := by
  refine .letE (.newCell (CallableIndexedContextFrames.literal_evaluates layout .empty [] [])) ?_
  simpa only [initialStore, initialEnvironment, List.length_singleton, List.length_nil, List.nil_append,
    List.reverse_reverse, List.length_reverse] using
    ordered_bootstrap_evaluates signatures.reverse rows [.cellRef layout.type 0]
      [SourceCoreCallableIndexedFrames.encode layout .empty] (by simpa using ordered)

theorem stored {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (rows : List LambdaRow) (cached : compiled.indexed.secondPass.closures = rows.map LambdaRow.expression)
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      compiled.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result) :
    ∃ world, RuntimeStoreHasTypes world
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)
      compiled.indexed.layouts.definitions := by
  obtain ⟨owned, emitted⟩ := recipe_emitted accepted
  have typed := recipe.bootstrapTyped
  rw [emitted, owned, cached] at typed
  obtain ⟨world, _, stored, _⟩ := evaluation_preserves_type
    (framed_bootstrap compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame ordered)
    typed .nil (.nil compiled.indexed.layouts.definitions)
  exact ⟨world, stored⟩

/-- This inversion concerns the full stored closure, including its exact
renamed code and captured values. It does not reconstruct source identity. -/
theorem stored_closure {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typed : RuntimeStoreHasTypes world store definitions)
    {location : Location} {parameter result : Ty} {body : Expr} {captured : Environment}
    (read : store.read? location = some (.inRight .unit (.closure parameter result body captured))) :
    ∃ context, RuntimeEnvironmentHasTypes world captured context definitions ∧
      HasType (parameter :: context) body result definitions := by
  change store[location]? = some (.inRight .unit (.closure parameter result body captured)) at read
  have found : world[location]? = some (.sum .unit (.function parameter result)) := by
    rw [typed.world_eq, List.getElem?_map, read]
    rfl
  obtain ⟨value, actual, related⟩ := typed.lookup found
  have same := Option.some.inj (actual.symm.trans read)
  subst value
  cases related with
  | inRight closure =>
    cases closure with
    | closure environment code => exact ⟨_, environment, code⟩

/-- Removing the real installer Unit prefix only exposes the original
canonical environment. No captured values or closure code are changed. -/
theorem drop_installer_units {definitions : DataEnvironment} {world : StoreTyping} {environment : Environment}
    {context : Core.Context} (count : Nat)
    (typed : RuntimeEnvironmentHasTypes world (List.replicate count .unit ++ environment) context definitions) :
    ∃ canonicalContext, RuntimeEnvironmentHasTypes world environment canonicalContext definitions := by
  induction count generalizing context with
  | zero => exact ⟨_, typed⟩
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append] at typed
    cases typed with
    | cons _ tail => exact ih tail

end Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationTyping
