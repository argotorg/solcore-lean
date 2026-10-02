import Solcore.SourceSemantics.CoreLowering.CallableIndexedCachedNativeTyping
import Solcore.Test.SourceCompilerFeatureSupport

/-! Cached native roots type their actual second-pass closures. Both global
slots and wrapper input types are retained; native typing grants no source
closure authority. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedCachedNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open CallableIndexedCachedNativeTyping

theorem actual_cached_closure (cached : SourceCoreUnifiedCompilation.Compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
    (member : entry ∈ cached.indexed.entries)
    {index : Nat} {closure : Expr} {signature : SourceCoreCalls.Signature}
    (selected : cached.indexed.secondPass.closures[index]? = some closure)
    (global : cached.indexed.base.globals[index]? = some signature) :
    HasType (cached.indexed.base.globals.map (·.referenceType) ++ .cell cached.indexed.ancestry.layout.frame.type ::
      SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      closure signature.functionType cached.indexed.layouts.definitions :=
  prepared_native_closure cached.indexedPrepared member selected global

theorem actual_cached_named_output (cached : SourceCoreUnifiedCompilation.Compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
    (member : entry ∈ cached.indexed.entries)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : cached.indexed.base.functions[index]? = some named)
    (global : cached.indexed.base.globals[index]? = some named.signature) :
    ∃ diagnostics code,
      ∃ compiled : CallableIndexedNamedGeneration.Compilation cached.indexed named diagnostics code,
      cached.indexed.secondPass.closures[index]? = some code ∧
      HasType (named.signature.parameterType :: cached.indexed.base.globals.map (·.referenceType) ++
        .cell cached.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.output (LanguageResult.resultType named.signature.resultType) cached.indexed.layouts.definitions :=
  prepared_named_output cached.indexedPrepared member selected global

/-- A later installer Unit binder is removed syntactically, including from a
lambda's lifted body renaming. The original context can have hidden entries. -/
theorem second_slot {definitions : DataEnvironment} {context : Core.Context}
    {first second continuation : Expr} {type functionType : Ty}
    (typed : HasType context (SourceCoreRecursiveEntry.installFunctions [first, second] continuation) type definitions)
    (reference : context[1]? = some (OptionalCell.referenceType functionType)) :
    HasType context second functionType definitions :=
  installed_closure typed rfl reference

theorem invalid_installer_rejected (tail : Expr) :
    ¬ HasType [OptionalCell.referenceType (.function .unit .unit)]
      (SourceCoreRecursiveEntry.installFunctions [.word Word.zero] tail) .unit [] := by
  intro typed
  have invalid := installed_closure typed (index := 0) (closure := .word Word.zero) rfl rfl
  cases invalid

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function step(value: Word) returns (Word) { return value + 1; }",
    "function recursive(value: Word) returns (Word) { if (value == 0) { return 1; } return step(recursive(value - 1)); }",
    "function even(value: Word) returns (Bool) { if (value == 0) { return true; } return odd(value - 1); }",
    "function odd(value: Word) returns (Bool) { if (value == 0) { return false; } return even(value - 1); }",
    "function mixed(flag: Bool, seed: Word) returns (Word) { let value = seed; for (let i = 0; i < 3; i = step(i)) { value = step(value); } if (flag) { return recursive(value); } return value; }",
    "function captured(seed: Word) returns (Word) { let value = seed; let increase = lam(item: Word) -> Word { let i = 0; while (i < 2) { value = step(value); i = step(i); } return value + item; }; return increase(3); }"
  ]}] }

open Tests.SourceCompilerFeatureSupport in
private def checkCached (entry : Entry) : IO Unit := do
  let prepared := entry.cached.indexed
  require (!prepared.entries.isEmpty) "actual native root missing"
  require (prepared.base.globals.length == prepared.secondPass.closures.length) "closure/global inventory mismatch"
  for root in prepared.entries do
    let context := prepared.base.globals.map (·.referenceType) ++ .cell prepared.ancestry.layout.frame.type ::
      SourceCoreGeneralEntry.nativeInputContext root.native.inputTypes
    for (closure, index) in prepared.secondPass.closures.zipIdx do
      let signature ← match prepared.base.globals[index]? with
        | some signature => pure signature | none => throw (IO.userError "cached global slot missing")
      require (Core.infer? context closure prepared.layouts.definitions == some signature.functionType)
        "cached checked root did not type its original closure"
      match closure with
      | .lambda parameter result body =>
        require (parameter == signature.parameterType && result == LanguageResult.resultType signature.resultType)
          "actual named closure signature changed"
        require (Core.infer? (parameter :: context) body prepared.layouts.definitions == some result)
          "actual named output lost body typing"
      | _ => throw (IO.userError "cached named compiler did not emit a lambda")

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let checked ← get "cached native source checker" (checkProgram workspace)
  for (name, arguments, expected) in [
      ("recursive", [scalar 3], scalar 4),
      ("even", [scalar 4], (.bool true : SourceCoreExecution.Value)),
      ("mixed", [(.bool true : SourceCoreExecution.Value), scalar 2], scalar 6),
      ("captured", [scalar 2], scalar 7)] do
    let entry ← compileNamed checked name
    checkCached entry
    require ((← entry.run arguments) == expected) "cached native source result changed"
    entry.checkResume arguments expected 1
  IO.println "cached native typing: actual prepared roots, all installed global slots, exact named outputs, recursive/mutual/loop/lambda bodies and resume GREEN"

end Tests.SourceCoreCallableIndexedCachedNativeTyping
