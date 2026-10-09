import Solcore.Test.SourceCoreChosenOrdinaryAcceptedFixture
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization

/-! This executable receipt retains one original public preparation and one
bootstrap completion for the unchanged accepted fixture. It identifies the
actual initialized store without asserting Source body or Session semantics. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
open Solcore Frontend Core SourceSemantics.CoreLowering

/-- The actual Recipe and its acceptance belong to this same fixture packet.
Only the finite list length is checked executably. -/
structure PublicRecipeReceipt (fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture) where
  recipe : SourceCoreIndexedSession.Recipe
  accepted : SourceCoreIndexedSession.Recipe.prepare fixture.packet.compiled = .ok recipe
  one_named : fixture.packet.compiled.indexed.base.functions.length = 1

def prepare_public (fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture) :
    Except String (PublicRecipeReceipt fixture) := do
  let prepared ← match accepted : SourceCoreIndexedSession.Recipe.prepare fixture.packet.compiled with
    | .error error => throw s!"public Recipe.prepare: {reprStr error}"
    | .ok recipe => pure (⟨recipe, accepted⟩ :
        {r // SourceCoreIndexedSession.Recipe.prepare fixture.packet.compiled = .ok r})
  if one : fixture.packet.compiled.indexed.base.functions.length = 1 then
    pure ⟨prepared.val, prepared.property, one⟩
  else throw "the actual accepted fixture has more than one named row"

theorem compiled_eq {fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture} (prepared : PublicRecipeReceipt fixture) :
    prepared.recipe.compiled = fixture.packet.compiled :=
  SourceCoreIndexedSession.Recipe.prepare_compiled prepared.accepted

/-- The authentic selected row and length check identify the whole list; no
executable equality of proof-bearing named records is used. -/
theorem functions_singleton {fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture}
    (prepared : PublicRecipeReceipt fixture) :
    fixture.packet.compiled.indexed.base.functions = [fixture.packet.named] := by
  have one := prepared.one_named
  have selected := fixture.packet.namedSelected
  cases rows : fixture.packet.compiled.indexed.base.functions with
  | nil => simp [rows] at one
  | cons named rest =>
    cases rest with
    | nil =>
      simp [rows] at selected
      simp [selected]
    | cons next tail => simp [rows] at one

/-- A successful original machine completion, at precisely this Recipe. -/
structure CompletedBootstrap {fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture}
    (prepared : PublicRecipeReceipt fixture) (fuel : Nat) where
  value : Value
  store : Store
  completed : runStateful fuel (.initial prepared.recipe.bootstrap [] []) = .done value store

def complete_bootstrap {fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture}
    (prepared : PublicRecipeReceipt fixture) (fuel : Nat) :
    Except String (CompletedBootstrap prepared fuel) :=
  match completed : runStateful fuel (.initial prepared.recipe.bootstrap [] []) with
  | .done value store => .ok ⟨value, store, completed⟩
  | .outOfFuel _ => .error s!"public bootstrap exhausted fuel {fuel}"
  | .fault error _ => .error s!"public bootstrap fault: {reprStr error}"

/-- The observed completion is the original exact initialization; this uses
its retained preparation equation and never runs either producer again. -/
theorem completed_store {fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture}
    {prepared : PublicRecipeReceipt fixture} {fuel : Nat}
    (completed : CompletedBootstrap prepared fuel) :
    completed.value = .inRight .word .unit ∧
      completed.store = RecursiveNamedCatalogPreparedInitialization.store fixture.packet.compiled :=
  RecursiveNamedCatalogPreparedInitialization.completed_store prepared.accepted completed.completed

def bootstrapFuel : Nat := 10000

structure PublicBootstrapFixture where
  fixture : SourceCoreChosenOrdinaryAcceptedFixture.AcceptedFixture
  prepared : PublicRecipeReceipt fixture
  completed : CompletedBootstrap prepared bootstrapFuel

/-- Runs the unchanged fixture once, public preparation once and the original
bootstrap machine once. Failed actions retain their actual error. -/
def accepted_public_fixture : Except String PublicBootstrapFixture := do
  let fixture ← SourceCoreChosenOrdinaryAcceptedFixture.acceptedFixture
  let prepared ← prepare_public fixture
  let completed ← complete_bootstrap prepared bootstrapFuel
  pure ⟨fixture, prepared, completed⟩

def run : IO Unit := do
  match accepted_public_fixture with
  | .error error => throw (IO.userError error)
  | .ok actual =>
    IO.println s!"accepted public bootstrap: one original Recipe, one named row, original machine completed at fuel {bootstrapFuel}; initialized store has {actual.completed.store.length} cells"

end Tests.SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
