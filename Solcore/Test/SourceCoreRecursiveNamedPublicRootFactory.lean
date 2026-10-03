import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Successful public preparation retains the exact indexed entry, function,
argument slots and emitted call. These consumers use factory provenance. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicRootFactory
open Solcore Frontend SourceCoreIndexedSession

abbrev factory_issued := @Recipe.prepare_roots

theorem actual_entry_and_call {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (accepted : Recipe.prepare compiled = .ok recipe) {root : Root recipe.compiled}
    (member : root ∈ recipe.roots) :
    ∃ entry function index,
      entry ∈ recipe.compiled.indexed.entries ∧
      recipe.compiled.indexed.base.functions.zipIdx.find?
        (fun item => decide (item.1.signature.key = entry.key)) = some (function, index) ∧
      function.signature.key = root.key ∧
      root.inputs = entry.inputs.map (·.scheme.body) ∧
      root.result = entry.sourceResultType ∧
      root.body = SourceCoreCalls.call function.signature (index + root.types.length)
        (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
          ⟨type, Core.LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression Core.Word.zero := by
  obtain ⟨entry, entryMember, function, index, selected, key, rootKey, inputs,
    _, result, _, _, body, _⟩ := Recipe.prepare_roots accepted member
  exact ⟨entry, function, index, entryMember, selected, key.trans rootKey.symm, inputs, result, body⟩

private def require := SourceCoreUnifiedCorpusSupport.assertTrue

def run : IO Unit := do
  let content := String.intercalate "\n" [
    "function zero() returns (Word) { return 0; }",
    "function one(n: Word) returns (Word) { return n + 1; }",
    "function ordered(a: Word, b: Word, c: Word) returns (Word) { return a - b + c; }",
    "function truth(value: Bool) returns (Bool) { return value; }",
    "function unit() { }"
  ]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "public root factory" content
    ["zero", "one", "ordered", "truth", "unit"]
  let recipe ← SourceCoreUnifiedCorpusSupport.get "public root recipe" (Recipe.prepare compiled)
  require (recipe.roots.length == 5) "public root factory lost requested roots"
  for root in recipe.roots do
    let some entry := recipe.compiled.indexed.entries.find? (fun entry => decide (entry.key = root.key))
      | throw (IO.userError "public root has no actual indexed entry")
    let some (function, index) := recipe.compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = entry.key))
      | throw (IO.userError "public root has no actual selected function")
    let types := function.inputs.map Prod.snd
    let arguments := SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
      ⟨type, Core.LanguageResult.success (.var (types.length - 1 - index))⟩)
    let expected := SourceCoreCalls.call function.signature (index + types.length) arguments.expression Core.Word.zero
    require (decide (root.inputs = entry.inputs.map (·.scheme.body))) "public root changed full raw source input types"
    require (decide (root.result = entry.sourceResultType)) "public root changed raw source result type"
    require (decide (root.types = types)) "public root changed ordered native input types"
    require (decide (root.type = function.signature.resultType)) "public root changed selected result type"
    require (decide (root.body = expected)) "public root changed selected call, reversed input slots or shifted global index"
    require (decide (Core.infer? (types.reverse ++
      (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed).map Core.Value.type)
      root.body recipe.compiled.indexed.layouts.definitions = some (Core.LanguageResult.resultType root.type)))
      "public root lost its actual native checker equation"
  IO.println "actual public root factory GREEN"
end Tests.SourceCoreRecursiveNamedPublicRootFactory
