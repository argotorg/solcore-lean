import Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Frontend.SourceCoreIndexedSession

/-! The real compiler-owned cache supplies every lambda row. Formal consumers
close the actual success-Unit continuation and reflect exact bootstrap values
and stores. Native IO checks all full cached templates, captured environments,
physical slot reads, initial prefix and complete machine resumption. No source
body correspondence or initial catalog Authority is inferred from these facts. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveGlobalInitializationMeaning
open Solcore Core Frontend SourceSemantics.CoreLowering
open RecursiveGlobalInitializationMeaning

variable {checked : SourceCoreCompatibleCatalog.Checked}
  (compiled : SourceCoreCallableIndexedPrograms.Prepared checked)
  (rows : List LambdaRow)
  (cached : compiled.secondPass.closures = rows.map LambdaRow.expression)
  (environment : Environment) (store : Store) (locations : Nat → Location)
  (references : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row →
    (reserve compiled.base.globals.reverse store environment).2[i]? =
      some (.cellRef (OptionalCell.cellType (.function row.parameter row.result)) (locations i)))
  (bounds : ∀ i, i < rows.length → locations i < (reserve compiled.base.globals.reverse store environment).1.length)

include cached references bounds in
/-- The cache's exact equation supplies the installed code. No native or
source function-body execution law is an input to initialization. -/
theorem actual_cached_bootstrap :
    Evaluates environment store (SourceCoreRecursiveEntry.allocateGlobals compiled.base.globals.reverse
      (SourceCoreRecursiveEntry.installFunctions compiled.secondPass.closures (LanguageResult.success .unit)))
      (.inRight .word .unit)
      (installStore rows locations (reserve compiled.base.globals.reverse store environment).2
        (reserve compiled.base.globals.reverse store environment).1 0) := by
  rw [cached]
  exact bootstrap_evaluates compiled.base.globals.reverse rows environment store locations references bounds

include cached references bounds in
/-- Any actual native completion is precisely the closed bootstrap result and
store. The saved closure environments come from the real emitted Unit binders. -/
theorem actual_cached_bootstrap_reflects {value : Value} {finalStore : Store}
    (completed : Evaluates environment store (SourceCoreRecursiveEntry.allocateGlobals compiled.base.globals.reverse
      (SourceCoreRecursiveEntry.installFunctions compiled.secondPass.closures (LanguageResult.success .unit))) value finalStore) :
    value = .inRight .word .unit ∧ finalStore =
      installStore rows locations (reserve compiled.base.globals.reverse store environment).2
        (reserve compiled.base.globals.reverse store environment).1 0 :=
  evaluation_deterministic completed (actual_cached_bootstrap compiled rows cached environment store locations references bounds)

include cached in
/-- With an ordered static cache receipt, even the physical references and
bounds are derived from real allocation. No runtime law is part of the receipt. -/
theorem actual_ordered_cached_bootstrap
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      compiled.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result) :
    Evaluates environment store (SourceCoreRecursiveEntry.allocateGlobals compiled.base.globals.reverse
      (SourceCoreRecursiveEntry.installFunctions compiled.secondPass.closures (LanguageResult.success .unit)))
      (.inRight .word .unit)
      (installStore rows (fun index => store.length + (compiled.base.globals.length - 1 - index))
        (reserve compiled.base.globals.reverse store environment).2
        (reserve compiled.base.globals.reverse store environment).1 0) := by
  rw [cached]
  simpa only [List.reverse_reverse, List.length_reverse] using
    ordered_bootstrap_evaluates compiled.base.globals.reverse rows environment store (by simpa using ordered)

private def content : String := String.intercalate "\n" [
  "function self(n: Word) returns (Word) { if (n == 0) { return 2; } return self(n - 1); }",
  "function left(n: Word) returns (Bool) { if (n == 0) { return true; } return right(n - 1); }",
  "function right(n: Word) returns (Bool) { let current = n; while (current != 0) { current -= 1; return left(current); } return false; }",
  "function closure(n: Word) returns (Word) { let shared = n; let f = lam(step: Word) -> Word { shared += step; return shared; }; return f(3); }",
  "function empty() {}"
]
private def rowsOf (closures : List Expr) : IO (List LambdaRow) := closures.mapM fun expression =>
  match expression with
  | .lambda parameter result body => pure ⟨parameter, result, body⟩
  | _ => throw (IO.userError "initialization cache contains a non-lambda")
private def completed (state : State) : IO (Value × Store) :=
  match runStateful 300000 state with
  | .done value store => pure (value, store)
  | other => throw (IO.userError s!"initialization machine did not complete: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive global initialization" content
    ["self", "left", "right", "closure", "empty"]
  let indexed := compiled.indexed
  let rows ← rowsOf indexed.secondPass.closures
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (rows.map LambdaRow.expression) == reprStr indexed.secondPass.closures)
    "initialization full cached row reconstruction changed"
  SourceCoreUnifiedCorpusSupport.assertTrue (rows.length == indexed.base.globals.length)
    "initialization cache/global inventory length changed"
  for (row, index) in rows.zipIdx do
    let signature ← match indexed.base.globals[index]? with
      | some signature => pure signature
      | none => throw (IO.userError "initialization ordered signature missing")
    SourceCoreUnifiedCorpusSupport.assertTrue (signature.functionType == .function row.parameter row.result)
      s!"initialization static cache-to-signature receipt changed {index}"
  let recipe ← SourceCoreUnifiedCorpusSupport.get "actual initialization recipe" (SourceCoreIndexedSession.Recipe.prepare compiled)
  let cache ← SourceCoreUnifiedCorpusSupport.get "actual installed cache" (SourceCoreCallableIndexedTemplates.prepare indexed)
  let emitted := SourceCoreCallableIndexedFrames.allocate indexed.ancestry.layout.frame
    (SourceCoreRecursiveEntry.allocateGlobals indexed.base.globals.reverse
      (SourceCoreRecursiveEntry.installFunctions indexed.secondPass.closures (LanguageResult.success .unit)))
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr emitted == reprStr recipe.bootstrap)
    "initialization actual recipe emission changed"
  let prefixes : List Store := [[], [.word (Word.ofNatModulo 859), .inRight .unit (.bool false)]]
  for oldStore in prefixes do
    let frame := SourceCoreCallableIndexedFrames.encode indexed.ancestry.layout.frame .empty
    let reserved := reserve indexed.base.globals.reverse (oldStore ++ [frame]) [.cellRef indexed.ancestry.layout.frame.type oldStore.length]
    let locations := fun index => oldStore.length + 1 + rows.length - 1 - index
    let expected := installStore rows locations reserved.2 reserved.1 0
    let (value, actual) ← completed (.initial recipe.bootstrap [] oldStore)
    SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr (Value.inRight .word .unit))
      "initialization bootstrap result changed"
    SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected)
      "initialization all ordered writes/code/captured environments changed"
    SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (actual.take oldStore.length) == reprStr oldStore)
      "initialization old native prefix changed"
    SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (actual[oldStore.length]?) == reprStr (some frame))
      "initialization overwritten initial frame"
    for (row, index) in rows.zipIdx do
      let expectedValue := Value.inRight .unit (installedValue reserved.2 index row)
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (actual[locations index]?) == reprStr (some expectedValue))
        s!"initialization exact cached slot changed {index}"
    if oldStore.isEmpty then
      SourceCoreUnifiedCorpusSupport.assertTrue
        (SourceCoreCallableNativeSlots.checkPreparedGlobals cache.nativeGlobals cache.nativeGlobalsGenerated actual).isOk
        "initialization actual cache authentication failed"
    for fuel in [0, 1, 43, 300000] do
      let observed := runStateful fuel (.initial recipe.bootstrap [] oldStore)
      let final ← match observed with
        | .done value store => pure (value, store)
        | .outOfFuel state => completed state
        | other => throw (IO.userError s!"initialization internal fault {reprStr other}")
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr final == reprStr (value, actual))
        s!"initialization complete native resume changed {fuel}"
  IO.println "recursive global initialization: actual reserved slots, full cached code/captures, protected prefix/frame and complete bootstrap resume GREEN"

end Tests.SourceCoreRecursiveGlobalInitializationMeaning
