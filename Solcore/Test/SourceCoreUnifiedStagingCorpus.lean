import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Checked staging boundaries execute through the cached Core artifact.
Compile-time preparation remains the existing separate phase. Native fuel
cutoffs retain the language guard's source occurrence and prior effects. -/
set_option autoImplicit false
namespace Tests.SourceCoreUnifiedStagingCorpus
open Solcore Solcore.Frontend SourceInference
open SourceCoreUnifiedCorpusSupport

private def source : String := String.intercalate "\n" [
  "type StagedWord = comptime<Word>;",
  "type DeepStage = (StagedWord, (Word, StagedWord));",
  "function nestedComptime(value: DeepStage) returns (DeepStage) { return value; }",
  "function markedEffects(comptime seed: Word) returns (comptime<Word>) {",
  "  let total: Word = seed; let table: mapping(Word => Word);",
  "  let bump = lam(comptime delta: Word) -> Word { total += delta; table[0] = total; return table[0]; };",
  "  return bump(3);",
  "}",
  "function markedClosureClosed() returns (Word) { let f = lam(comptime value: Word) -> Word { return value; }; return f(21); }",
  "function markedClosureRuntime(value: Word) returns (Word) { let f = lam(comptime item: Word) -> Word { return item; }; return f(value); }",
  "function markedGlobal(comptime value: Word) returns (Word) { return value; }",
  "function markedGlobalClosed() returns (Word) { let f = markedGlobal; return f(22); }",
  "function markedGlobalRuntime(value: Word) returns (Word) { let f = markedGlobal; return f(value); }",
  "function markedResult(comptime value: Word) returns (comptime<Word>) { return value; }",
  "function markedResultIndirectBlocked() returns (Word) { let f = markedResult; return f(23); }",
  "function markedResultIndirectStaged() returns (comptime<Word>) { let f = markedResult; return f(24); }"
]

private def indirectOccurrence (compiled : Compiled) (name : String) : IO ExpressionId := do
  let owner ← key compiled.sourceProgram name
  let specialized ← get "staging source occurrence" (SourceCompilationPlan.exactSpecialization compiled.validationPlan owner)
  match specialized.function.typedBody.nodes.filterMap (fun
    | .expression {id, form := .call _ _ (.indirect _), ..} => some id
    | _ => none) with
  | [id] => pure id
  | ids => throw (IO.userError s!"{name} retained {ids.length} indirect calls")

def run : IO Unit := do
  let compiled ← prepare "staging guards" source ["nestedComptime", "markedEffects", "markedClosureClosed",
    "markedClosureRuntime", "markedGlobalClosed", "markedGlobalRuntime", "markedResultIndirectBlocked",
    "markedResultIndirectStaged"]
  let deep : Value := .product (.word (word 4)) (.product (.word (word 5)) (.word (word 6)))
  for spent in [0, 43, 300000] do
    discard <| expect compiled "nestedComptime" [deep] deep spent
    let effects ← expect compiled "markedEffects" [.word (word 9)] (.word (word 12)) spent
    assertTrue (hasWord effects 12 && effects.heap.any (fun cell => match cell.value with
      | some (.mapping _ _ entries) => entries.any (fun entry => match entry with
        | (.word key, .word value) => key == word 0 && value == word 12
        | _ => false)
      | _ => false)) "marked call lost its captured writes and mapping update"
    for (name, expected) in [("markedClosureClosed", 21), ("markedGlobalClosed", 22),
        ("markedResultIndirectStaged", 24)] do
      discard <| expect compiled name [] (.word (word expected)) spent
  for name in ["markedClosureRuntime", "markedGlobalRuntime", "markedResultIndirectBlocked"] do
    let owner ← key compiled.sourceProgram name
    let occurrence ← indirectOccurrence compiled name
    let arguments := if name == "markedResultIndirectBlocked" then [] else [.word (word 21)]
    for spent in [0, 43, 300000] do
      let first ← execute compiled name arguments spent
      let final ← get "staging guard native resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
      match final.observation with
      | .fault (.comptimeArgumentStageMismatch caller id 0 _ .runtime) state =>
        assertTrue (name != "markedResultIndirectBlocked" && caller == owner && id == occurrence &&
          state.heap.length == 2 && hasWord state 21)
          "marked argument guard lost its source site or allocated the guarded parameter"
      | .fault (.comptimeResultStageMismatch caller id _ .deferred) state =>
        assertTrue (name == "markedResultIndirectBlocked" && caller == owner && id == occurrence &&
          state.heap.length == 1 && !hasWord state 23)
          "marked result guard lost its source site or allocated the guarded parameter"
      | other => throw (IO.userError s!"{name} guard changed: {reprStr other}")
  IO.println "Core-only checked staging metadata, captured effects, exact guard sites and resume corpus GREEN"

end Tests.SourceCoreUnifiedStagingCorpus
