import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootArguments
import Solcore.Test.SourceCoreRecursiveNamedPublicRootFactory

/-! Actual public root preparation and typed native inputs close the pure
argument premise. Arbitrary closure payloads keep their complete captures. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicRootArguments
open Solcore Core Frontend SourceSemantics.CoreLowering
open RecursiveNamedPublicRootArguments SourceCoreIndexedSession

abbrev argument_fuel := @arguments_have_sufficient_fuel
abbrev completed_payload := @completed_arguments

theorem prepared_call_arguments {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (accepted : Recipe.prepare compiled = .ok recipe) {root : Root recipe.compiled}
    (member : root ∈ recipe.roots) {world : StoreTyping} {values : Environment} (store : Store)
    (typed : RuntimeEnvironmentHasTypes world values root.types recipe.compiled.indexed.layouts.definitions) :
    ∃ entry, entry ∈ recipe.compiled.indexed.entries ∧
      ∃ (function : SourceCoreGeneralFunctions.Function) (index : Nat),
        function.signature.key = root.key ∧
        root.body = SourceCoreCalls.call function.signature (index + root.types.length)
          (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
            ⟨type, LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression Word.zero ∧
        Evaluates (values.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) store
          (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
            ⟨type, LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression
          (.inRight .word (DataPatternValues.packValues values)) store := by
  obtain ⟨entry, entryMember, issued⟩ := Recipe.prepare_roots accepted member
  exact ⟨entry, entryMember, factory_call_arguments issued store typed⟩

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (value : Nat) : Core.Value := .word (Word.ofNatModulo value)

def run : IO Unit := do
  let captured := Core.Value.closure .word .word (.var 0)
    [.cellRef (OptionalCell.cellType .word) 0, word 109]
  let carried := Core.Value.pair captured (.cellRef (OptionalCell.cellType .word) 0)
  let store : Store := [.inRight .unit (word 107), captured, carried]
  let globals : Environment := [.cellRef (OptionalCell.cellType .word) 0, carried, word 997]
  let inputs : List Environment := [[], [word 5], [word 7, word 11, word 13],
    [.bool true, .integer (-17), .pair (word 19) .unit], [captured],
    [carried, .integer 23, captured, .cellRef (OptionalCell.cellType .word) 0]]
  for payloads in inputs do
    let types := payloads.map Core.Value.type
    let expression := (SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
      ⟨type, LanguageResult.success (.var (types.length - 1 - index))⟩)).expression
    let native := payloads.reverse ++ globals
    let expected := Core.Value.inRight .word (DataPatternValues.packValues payloads)
    for fuel in [0, 1, 7, 10000] do
      let observed := runStateful fuel (.initial expression native store)
      let completed := match observed with
        | .outOfFuel checkpoint => runStateful 10000 checkpoint
        | result => result
      match completed with
      | .done actual after =>
        require (decide (actual = expected)) "public root argument bundle changed order or closure capture"
        require (decide (after = store)) "public root argument bundle changed complete native store"
      | other => throw (IO.userError s!"public root arguments did not finish: {reprStr other}")
  IO.println "public root arguments: exact ordered reads, arbitrary captured payloads, complete store and native resume GREEN"
end Tests.SourceCoreRecursiveNamedPublicRootArguments
