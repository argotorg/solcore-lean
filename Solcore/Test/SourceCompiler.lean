import Solcore.Frontend.SourceCoreExecution
import Solcore.Frontend.SourceCoreRootDiscovery
import Solcore.Test.SourceCompilerRetainedBoundary

#check_failure Solcore.Frontend.SourceCoreExecution.Options.backendPreference
#check_failure Solcore.Frontend.SourceCoreExecution.Backend
#check_failure Solcore.Frontend.SourceCoreExecution.Invocation
#check_failure Solcore.Frontend.SourceCoreExecution.Compiled.backend
#check_failure Solcore.Frontend.SourceCoreExecution.Session.runCore
#check_failure Solcore.Frontend.SourceCoreExecution.Session.runTyped
#check_failure Solcore.Frontend.SourceCoreExecution.Value.closure
#check_failure Solcore.Frontend.SourceCoreExecution.Value.cellRef
#check_failure Solcore.Frontend.SourceCoreExecution.Session.state
#check_failure Solcore.Frontend.SourceCoreExecution.Session.store
#check_failure Solcore.Frontend.SourceCoreExecution.Checkpoint.state
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! The public source compiler has one Core/value/session boundary. Root
metadata, source behavior, ABI discovery and validation are preserved; there is
no backend choice or native/source invocation mismatch in this API. -/
set_option autoImplicit false
namespace Tests.SourceCompiler
open Solcore Solcore.Frontend Solcore.TypeSystem SourceCoreExecution
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Value := .word (word value)
private def moduleId (path : String) : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse path with
  | none => throw (IO.userError s!"invalid test module path `{path}`")
  | some canonical => pure { library := .main, path := canonical.modulePath }
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    {
      path := "main.solc"
      content := String.intercalate "\n" [
        "import {Ticket, WordTicket} from provider;",
        "function direct(value: Word) returns (Word) { return value * 2; }",
        "function recurse(value: Word) returns (Word) { return value == 0 ? 31 : recurse(value - 1); }",
        "function visibleAlias(value: (Word, Word)) returns (Word) {",
        "  let ticket: WordTicket = .Open(7);",
        "  match (ticket) {",
        "    case .Open(inner) {",
        "      let result: Word = inner;",
        "      result += 5;",
        "      return result;",
        "    }",
        "    default { return 0; }",
        "  }",
        "}",
        "function globalIdentity<T>(value: T) returns (T) { return value; }",
        "trait Eq<T> {}",
        "impl Eq<Word> {}",
        "trait Coerce<From, To> {",
        "  function coerce(value: From) returns (To);",
        "}",
        "function coercionSeed(value: Bool) returns (Word) {",
        "  return value ? 40 : 6;",
        "}",
        "impl Coerce<Bool, Word> {",
        "  function coerce(value: Bool) returns (Word) {",
        "    let scratch: mapping(Word => Word);",
        "    scratch[0] = coercionSeed(value);",
        "    scratch[0] += 2;",
        "    return scratch[0];",
        "  }",
        "}",
        "type WordFunction = function(Word) returns (Word);",
        "function returnedIdentity(value: Word) returns (Word) { return value; }",
        "impl Coerce<Word, WordFunction> {",
        "  function coerce(value: Word) returns (WordFunction) {",
        "    return returnedIdentity;",
        "  }",
        "}",
        "function functionFromCoercion(value: Word) returns (WordFunction) {",
        "  return value;",
        "}",
        "function keepAs<T, U>(guard: T, value: U) returns (U) where T: Eq { return value; }",
        "function localProof(flag: Bool) returns (Word, Bool) {",
        "  let f = lam(value) { return keepAs(1, value); };",
        "  return (f(2), f(flag));",
        "}",
        "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
        "function relay<T>(value: T) returns (T) where T: Eq { return keep(value); }",
        "function typedEvidence(value: Word) returns (Word) {",
        "  let table: mapping(Word => Word);",
        "  table[0] = relay(value);",
        "  return table[0];",
        "}",
        "function typedCoercion(value: Bool) returns (Word) {",
        "  let table: mapping(Word => Word);",
        "  table[0] = value;",
        "  return table[0];",
        "}",
        "function polymorphicLocal(flag: Bool) returns (Word, Bool) {",
        "  let id = lam(value) { return globalIdentity(value); };",
        "  return (id(11), id(flag));",
        "}",
        "function nestedPolymorphicLocal(flag: Bool) returns (Word, Bool) {",
        "  let outer = lam(value) {",
        "    let inner = lam(innerValue) { return globalIdentity(innerValue); };",
        "    return inner(value);",
        "  };",
        "  return (outer(13), outer(flag));",
        "}",
        "function recursiveContextPolymorphicLocal(flag: Bool) returns (Word, Bool) {",
        "  let outer = lam(value) {",
        "    let middle = lam(item) {",
        "      let inner = lam(innerValue) { return globalIdentity(innerValue); };",
        "      return inner(item);",
        "    };",
        "    return middle(value);",
        "  };",
        "  return (outer(15), outer(flag));",
        "}"
      ]
    },
    {
      path := "provider.solc"
      content := String.intercalate "\n" [
        "enum Ticket<T> { Open(T), Closed }",
        "type WordTicket = Ticket<Word>;",
        "export {Ticket(Open), WordTicket};"
      ]
    },
    {
      path := "blocked.solc"
      content := String.intercalate "\n" [
        "trait Coerce<From, To> {}",
        "enum Box { Only }",
        "impl Coerce<Word, Box> {}",
        "function accept(value: Box) returns (Box) { return value; }",
        "function blockedHelper(value: Word) returns (Box) { return accept(value); }",
        "function blocked(value: Word) returns (Box) { return blockedHelper(value); }",
        "trait Marker<T> {}",
        "impl Marker<Word> {}",
        "function constrained(value: Word) returns (Word) where Word: Marker {",
        "  let table: mapping(Word => Word);",
        "  table[0] = value;",
        "  return table[0];",
        "}",
        "function staged(comptime value: Word) returns (Word) { return value; }",
        "type StagedWord = comptime<Word>;",
        "type PairWithStage = (Word, StagedWord);",
        "type DeepStage = (StagedWord, (Word, StagedWord));",
        "function stagedType(value: StagedWord) returns (Word) { return 1; }",
        "function integerResult() returns (integer) { return 1; }",
        "function nestedStaged(value: PairWithStage) returns (Word) { return 1; }",
        "function dependent(flag: Bool) returns (Word) { return wordFromInteger(flag ? 1 : 2); }",
        "function nestedComptime(value: DeepStage) returns (DeepStage) { return value; }",
        "function integerBitAnd() returns (integer) { return 5 & 3; }",
        "function integerBitXor() returns (integer) { return 5 ^ 3; }",
        "function integerBitOr() returns (integer) { return 5 | 3; }",
        "function integerBitNot() returns (integer) { return ~5; }",
        "function markedEffects(comptime seed: Word) returns (comptime<Word>) {",
        "  let total: Word = seed;",
        "  let table: mapping(Word => Word);",
        "  let bump = lam(comptime delta: Word) -> Word {",
        "    total += delta;",
        "    table[0] = total;",
        "    return table[0];",
        "  };",
        "  return bump(3);",
        "}",
        "function markedEffectsEntry() returns (Word) {",
        "  return markedEffects(9);",
        "}"
      ]
    }
  ]
  externalLibraries := []
}

/-- A compact raw-workspace fixture for automatic entry discovery, exported
ABI discovery, re-export aliases, and shared-graph multi-root compilation. -/
private def orchestrationWorkspace : Workspace.RawWorkspace := {
  entry := "api.solc"
  mainSources := [
    {
      path := "api.solc"
      content := String.intercalate "\n" [
        "import {twice as doubled, recursive} from provider;",
        "function main() returns (Word) { return 17; }",
        "function local(value: Word) returns (Word) { return value + 1; }",
        "function hidden(value: Word) returns (Word) { return value; }",
        "export {doubled, local, recursive};"
      ]
    },
    {
      path := "provider.solc"
      content := String.intercalate "\n" [
        "function twice(value: Word) returns (Word) { return value * 2; }",
        "function recursive(value: Word) returns (Word) {",
        "  return value == 0 ? 31 : recursive(value - 1);",
        "}",
        "function providerOnly(value: Word) returns (Word) { return value; }",
        "export {twice, recursive, providerOnly};"
      ]
    }
  ]
  externalLibraries := []
}
private def compilerOptions : Options :=
  { specializationBudget := 128, compilationFuel := 1000 }
private def runtimeOptions : RunOptions :=
  { inputValidationFuel := 128, executionFuel := 300000, outputValidationFuel := 128 }
private def boot (artifact : Artifact) : IO (Session artifact) := do
  let bootstrap ← artifact.bootstrap
  match bootstrap.resume 300000 with
  | .ready session => pure session
  | .error error => throw (IO.userError s!"compiler bootstrap rejected: {reprStr error}")
  | .outOfFuel _ => throw (IO.userError "compiler bootstrap exhausted")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value) :
    IO (Completion artifact) := do
  match ← session.run key arguments runtimeOptions with
  | .ok (.succeeded completion) => pure completion
  | .error error => throw (IO.userError s!"public inputs rejected: {reprStr error}")
  | .ok (.exportError error _) => throw (IO.userError s!"public output rejected: {reprStr error}")
  | .ok (.failed token _) => throw (IO.userError s!"unexpected language failure: {reprStr token}")
  | .ok (.outOfFuel _) => throw (IO.userError "public execution exhausted")
private structure Entry where
  compiled : Compiled
  root : SourceCoreCompiler.Root compiled.plan
private def Entry.key (entry : Entry) : Key := entry.root.key
private def Entry.inputTypes (entry : Entry) : List Ty := entry.root.inputTypes
private def Entry.resultType (entry : Entry) : Ty := entry.root.resultType
private def entry (compiled : Compiled) (index : Nat := 0) : IO Entry :=
  match compiled.root? index with
  | some root => pure ⟨compiled, root⟩
  | none => throw (IO.userError s!"compiled root missing at {index}")
private def compileNamed (program : CheckedProgram) (path name : String) : IO Entry := do
  let selectedModule ← moduleId path
  entry (← get s!"compile {path}.{name}" (compileChecked program [SourceCoreCompiler.Seed.named selectedModule name] compilerOptions))
private def Entry.run (entry : Entry) (arguments : List Value) : IO Value := do
  let artifact ← entry.compiled.open
  let session ← boot artifact
  pure (← execute session entry.key arguments).value
private def expectWord (label : String) (expected : Nat) (actual : IO Value) : IO Unit := do
  assertTrue ((← actual) == scalar expected) s!"{label} returned the wrong Word"

private structure PreparedSet where
  checked : CheckedProgram
  direct : Entry
  recursive : Entry
  pair : Entry

private def testCheckedReuse : IO PreparedSet := do
  let checked ← get "compiler checking" (checkProgram workspace)
  let direct ← compileNamed checked "main.solc" "direct"
  let recursive ← compileNamed checked "main.solc" "recurse"
  let pair ← compileNamed checked "main.solc" "visibleAlias"
  let main ← moduleId "main.solc"
  assertTrue (decide (direct.key.declaration.moduleId = main ∧ recursive.key.declaration.moduleId = main ∧
      pair.key.declaration.moduleId = main ∧ direct.key.arguments = [] ∧ recursive.key.arguments = [] ∧ pair.key.arguments = []))
    "compiled roots lost canonical module or ground arguments"
  assertTrue (decide (direct.inputTypes = [.word] ∧ direct.resultType = .word ∧
      recursive.inputTypes = [.word] ∧ recursive.resultType = .word ∧
      pair.inputTypes = [.product .word .word] ∧ pair.resultType = .word))
    "compiled roots lost source signature metadata"
  assertTrue (direct.compiled.plan.specializations.length == 1 && recursive.compiled.plan.specializations.length == 1 &&
    pair.compiled.plan.specializations.length == 1) "single-function plan gained specializations"
  let artifact ← direct.compiled.open
  let session ← boot artifact
  let first ← execute session direct.key [scalar 7]
  let second ← execute first.session direct.key [scalar 9]
  assertTrue (first.value == scalar 14 && second.value == scalar 18)
    "reusing one cached artifact/session changed direct results"
  expectWord "recursive source root" 31 (recursive.run [scalar 3])
  expectWord "imported nominal alias" 12 (pair.run [.product (scalar 7) (scalar 8)])
  for (name, expected) in [("polymorphicLocal", 11), ("nestedPolymorphicLocal", 13), ("recursiveContextPolymorphicLocal", 15)] do
    let compiled ← compileNamed checked "main.solc" name
    assertTrue (compiled.compiled.plan.specializations.length == 3) s!"{name}: local generic instances changed"
    let edges := compiled.compiled.plan.callEdges.filter (fun edge => decide (edge.caller = compiled.key))
    assertTrue (compiled.compiled.plan.callEdges.length == 2 && edges.length == 2 &&
      (edges.map (·.occurrence)).eraseDups.length == 1 &&
      (edges.map (·.callee.arguments)).contains [.word] && (edges.map (·.callee.arguments)).contains [.bool])
      s!"{name}: contextual Word/Bool calls disappeared"
    assertTrue ((← compiled.run [.bool true]) == .product (scalar expected) (.bool true))
      s!"{name}: local instantiation result changed"
  let proof ← compileNamed checked "main.solc" "localProof"
  assertTrue (proof.compiled.plan.specializations.length == 3 &&
    (← proof.run [.bool true]) == .product (scalar 2) (.bool true)) "local evidence specialization changed"
  let evidence ← compileNamed checked "main.solc" "typedEvidence"
  assertTrue (evidence.compiled.plan.specializations.length == 3) "evidence frontier lost root/relay/callee"
  expectWord "evidence forwarding" 73 (evidence.run [scalar 73])
  let coercion ← compileNamed checked "main.solc" "typedCoercion"
  expectWord "stateful coercion true" 42 (coercion.run [.bool true])
  expectWord "stateful coercion false" 8 (coercion.run [.bool false])
  let returned ← compileNamed checked "main.solc" "functionFromCoercion"
  match ← returned.run [scalar 1] with
  | .function handle => assertTrue (handle.sourceType == .function .word .word) "coercion lost returned function type"
  | _ => throw (IO.userError "method-discovered function was not exported as an owned handle")
  pure ⟨checked, direct, recursive, pair⟩

private def testInputBoundary (prepared : PreparedSet) : IO Unit := do
  let artifact ← prepared.pair.compiled.open
  let session ← boot artifact
  match session.start prepared.pair.key [.bool true] 128 with
  | .error {code := .compatible {code := .sourceTypeMismatch (.product .word .word) .bool, ..}, ..} => pure ()
  | _ => throw (IO.userError "public value mismatch lost exact expected/actual types")
  let pair : Value := .product (scalar 7) (scalar 8)
  for fuel in [0, 1] do
    match session.start prepared.pair.key [pair] fuel with
    | .error {code := .compatible {code := .exhausted, ..}, ..} => pure ()
    | _ => throw (IO.userError "public deep input validation ignored its budget")
  match session.start prepared.pair.key [] 128 with
  | .error {code := .argumentCountMismatch 1 0, ..} => pure ()
  | _ => throw (IO.userError "public input arity mismatch was accepted")
  let checkpoint ← get "public typed checkpoint" (session.start prepared.pair.key [pair] 128)
  let paused ← match ← checkpoint.resume 0 128 with
    | .outOfFuel paused => pure paused | _ => throw (IO.userError "execution fuel was not independent of validation")
  match ← paused.resume 300000 128 with
  | .succeeded completion => assertTrue (completion.value == scalar 12) "resume changed nominal source result"
  | _ => throw (IO.userError "validated public checkpoint failed to resume")
  -- Rejection never changes the caller's persistent session.
  assertTrue ((← execute session prepared.pair.key [pair]).value == scalar 12)
    "input rejection changed reusable session state"

private def testCapabilities (checked : CheckedProgram) : IO Unit := do
  let cases : List (String × List Ty × Ty × List Value × Value) := [
      ("constrained", [.word], .word, [scalar 19], scalar 19),
      ("staged", [.word], .word, [scalar 23], scalar 23),
      ("stagedType", [.comptime .word], .word, [scalar 29], scalar 1),
      ("integerResult", [], .integer, [], .integer 1),
      ("nestedStaged", [.product .word (.comptime .word)], .word, [.product (scalar 2) (scalar 3)], scalar 1),
      ("nestedComptime", [.product (.comptime .word) (.product .word (.comptime .word))],
        .product (.comptime .word) (.product .word (.comptime .word)),
        [.product (scalar 4) (.product (scalar 5) (scalar 6))], .product (scalar 4) (.product (scalar 5) (scalar 6))),
      ("integerBitAnd", [], .integer, [], .integer 1),
      ("integerBitXor", [], .integer, [], .integer 6),
      ("integerBitOr", [], .integer, [], .integer 7),
      ("integerBitNot", [], .integer, [], .integer (-6)),
      ("markedEffects", [.word], .word, [scalar 9], scalar 12),
      ("markedEffectsEntry", [], .word, [], scalar 12)]
  for (name, inputTypes, resultType, arguments, expected) in cases do
    let compiled ← compileNamed checked "blocked.solc" name
    assertTrue (compiled.inputTypes == inputTypes && compiled.resultType == resultType)
      s!"{name}: raw public source signature metadata changed"
    assertTrue ((← compiled.run arguments) == expected) s!"{name}: staged/evidence/Integer behavior changed"

private def testCompilationErrors (checked : CheckedProgram) : IO Unit := do
  let main ← moduleId "main.solc"
  let missing := SourceCoreCompiler.Seed.named main "missing"
  match compileChecked checked [missing] compilerOptions with
  | .error (.compilation (.seed 0 actual (.unknownName owner "missing"))) =>
      assertTrue (decide (actual = missing ∧ owner = main)) "seed rejection lost its original request"
  | _ => throw (IO.userError "unknown public root did not report its seed error")
  match compileChecked checked [SourceCoreCompiler.Seed.named main "direct"]
      {compilerOptions with specializationBudget := 0} with
  | .error (.compilation (.specializationBudgetExhausted next pending)) =>
      assertTrue (next.declaration.moduleId == main && pending > 0) "shared specialization budget lost its frontier"
  | _ => throw (IO.userError "zero shared specialization budget was accepted")
  let blocked ← moduleId "blocked.solc"
  match compileChecked checked [SourceCoreCompiler.Seed.named blocked "blocked"] compilerOptions with
  | .error (.compilation (.planEvidence (.executableCoercionMethod _ _ _ (.missingTraitMethod _ "coerce")))) => pure ()
  | _ => throw (IO.userError "unavailable coercion method escaped the one compiler's plan validation")
  match compileChecked checked [SourceCoreCompiler.Seed.named blocked "dependent"] compilerOptions with
  | .error (.compilation (.planEvidence (.stagedExpressionType _ .integer))) => pure ()
  | _ => throw (IO.userError "dependent staged Integer escaped plan validation")
  let invalid : Workspace.RawWorkspace := {
    entry := "broken.solc", externalLibraries := [],
    mainSources := [{path := "broken.solc", content := "function broken(value: Word returns (Word) { return value; }"}] }
  match compile invalid [SourceCoreCompiler.Seed.named (← moduleId "broken.solc") "broken"] compilerOptions with
  | .error (.compilation (.checking (_ :: _))) => pure ()
  | _ => throw (IO.userError "malformed source escaped checking precedence")
  match compile invalid [] compilerOptions with
  | .error (.compilation (.checking (_ :: _))) => pure ()
  | _ => throw (IO.userError "empty roots bypassed raw source checking")

private def abiRootNamed (abi : StaticWordProgram) (name : String) : IO (StaticWordRoot abi.compiled) :=
  match abi.roots.find? (fun root => root.metadata.name.text == name) with
  | some root => pure root
  | none => throw (IO.userError s!"missing compiled ABI root {name}")

/-- Roots share one graph budget; public order and duplicates remain observable.
ABI discovery still uses exported source names and canonical declarations. -/
private def testProgramOrchestration : IO Unit := do
  let api ← moduleId "api.solc"
  let provider ← moduleId "provider.solc"
  let main ← entry (← get "conventional main" (compileEntry orchestrationWorkspace compilerOptions))
  assertTrue (main.inputTypes.isEmpty && main.resultType == .word && main.key.declaration.moduleId == api)
    "main discovery lost its entry module or signature"
  expectWord "conventional workspace main" 17 (main.run [])
  let checked ← get "orchestration checking" (checkProgram orchestrationWorkspace)
  let requested := [SourceCoreCompiler.Seed.named provider "twice", .named provider "recursive", .named provider "twice"]
  let many ← get "checked shared roots" (compileChecked checked requested compilerOptions)
  match many.roots with
  | [first, second, third] =>
      assertTrue (many.rootCount == 3 && first.key == third.key && first.key != second.key &&
        decide (many.roots.map (·.seed) = requested)) "root order or duplicate requests changed"
  | _ => throw (IO.userError "shared compilation changed root count")
  match compileChecked checked [SourceCoreCompiler.Seed.named provider "twice", .named provider "missing"] compilerOptions with
  | .error (.compilation (.seed 1 actual (.unknownName owner "missing"))) =>
      assertTrue (decide (actual = SourceCoreCompiler.Seed.named provider "missing" ∧ owner = provider))
        "missing second root lost request position or metadata"
  | _ => throw (IO.userError "missing second root changed its seed diagnostic")
  let rawMany ← get "raw shared roots" (compile orchestrationWorkspace requested compilerOptions)
  assertTrue (rawMany.keys == many.keys) "raw compilation changed ordered canonical roots"
  let one : Options := {compilerOptions with specializationBudget := 1}
  match compileChecked checked [SourceCoreCompiler.Seed.named provider "twice", .named api "local"] one with
  | .error (.compilation (.specializationBudgetExhausted _ pending)) =>
      assertTrue (pending > 0) "shared budget failure lost the unfinished frontier"
  | _ => throw (IO.userError "two distinct roots incorrectly received independent graph budgets")
  let duplicate ← get "duplicate root shared budget" (compileChecked checked
    [SourceCoreCompiler.Seed.named provider "twice", .named provider "twice"] one)
  assertTrue (duplicate.rootCount == 2 && duplicate.plan.specializations.length == 1)
    "duplicate requests consumed separate specialization budgets"

  let abi ← get "Static Word roots" (compileStaticWord orchestrationWorkspace compilerOptions)
  assertTrue (abi.count == 3) "ABI discovery lost an exported root"
  let doubled ← abiRootNamed abi "doubled"
  let localRoot ← abiRootNamed abi "local"
  let recursive ← abiRootNamed abi "recursive"
  assertTrue (doubled.root.key.declaration.moduleId == provider &&
    localRoot.root.key.declaration.moduleId == api && recursive.root.key.declaration.moduleId == provider &&
    (abi.roots.find? (fun root => root.metadata.name.text == "hidden")).isNone &&
    (abi.roots.find? (fun root => root.metadata.name.text == "providerOnly")).isNone)
    "ABI alias/module/export filtering changed"
  let discovered ← get "independent ABI discovery" (SourceCoreRootDiscovery.discoverStaticWordRoots checked api)
  assertTrue (abi.roots.map (·.metadata.name.text) == discovered.map (·.metadata.name.text))
    "compilation reordered discovered ABI roots"
  match abi.rootForSelector? doubled.metadata.selector with
  | some selected => assertTrue (selected.metadata.name.text == "doubled") "selector lookup chose another root"
  | none => throw (IO.userError "selector lookup lost an admitted root")
  let artifact ← abi.compiled.open
  let session ← boot artifact
  let first ← execute session doubled.root.key [scalar 7]
  let second ← execute first.session localRoot.root.key [scalar 7]
  let third ← execute second.session recursive.root.key [scalar 3]
  assertTrue (first.value == scalar 14 && second.value == scalar 8 && third.value == scalar 31)
    "ABI alias/local/recursive results changed in the shared session"
  let missingMain : Workspace.RawWorkspace := {
    entry := "missing.solc"
    mainSources := [{
      path := "missing.solc"
      content := "function helper() returns (Word) { return 0; }"
    }]
    externalLibraries := []
  }
  let missingModule ← moduleId "missing.solc"
  match compileEntry missingMain with
  | .error (.compilation (.seed 0 _ (.unknownName actual "main"))) =>
      assertTrue (actual == missingModule)
        "automatic entry failure lost its canonical module"
  | .error error => throw (IO.userError
      s!"missing main changed diagnostic: {reprStr error}")
  | .ok _ => throw (IO.userError "workspace without main compiled as an entry")

  let invalidAbi : Workspace.RawWorkspace := {
    entry := "bad.solc"
    mainSources := [{
      path := "bad.solc"
      content := String.intercalate "\n" [
        "function bad(value: Bool) returns (Word) { return value ? 1 : 0; }",
        "export {bad};"
      ]
    }]
    externalLibraries := []
  }
  match compileStaticWord invalidAbi with
  | .error (.discovery (.unsupportedParameters _ "bad" [.bool] [false])) =>
      pure ()
  | .error error => throw (IO.userError
      s!"unsupported ABI signature changed diagnostic: {reprStr error}")
  | .ok _ => throw (IO.userError
      "unsupported Bool ABI parameter was silently accepted")

  let duplicateAbi : Workspace.RawWorkspace := {
    entry := "duplicate.solc"
    mainSources := [{
      path := "duplicate.solc"
      content := String.intercalate "\n" [
        "function same(value: Word) returns (Word) { return value; }",
        "function same(value: Word) returns (Word) { return value + 1; }",
        "export {same};"
      ]
    }]
    externalLibraries := []
  }
  match compileStaticWord duplicateAbi with
  | .error (.discovery
      (.duplicateSignature "same" "same" "same(uint256)")) => pure ()
  | .error error => throw (IO.userError
      s!"duplicate ABI signature changed diagnostic: {reprStr error}")
  | .ok _ => throw (IO.userError
      "duplicate ABI signatures were silently accepted")

  let collisionAbi : Workspace.RawWorkspace := {
    entry := "collision.solc"
    mainSources := [{
      path := "collision.solc"
      content := String.intercalate "\n" [
        "function f116643(value: Word) returns (Word) { return value; }",
        "function f38491(value: Word) returns (Word) { return value; }",
        "export {f38491, f116643};"
      ]
    }]
    externalLibraries := []
  }
  match compileStaticWord collisionAbi with
  | .error (.discovery (.selectorCollision
      "f116643" "f38491" "f116643(uint256)" "f38491(uint256)" selector)) =>
      assertTrue (selector.toUInt32.toNat == 0x77dbd42e)
        "ABI collision diagnostic lost its canonical selector"
  | .error error => throw (IO.userError
      s!"ABI selector collision changed diagnostic: {reprStr error}")
  | .ok _ => throw (IO.userError
      "colliding ABI selectors were silently accepted")

/-- Checking, graph preparation, bootstrap, input validation and execution use
separate budgets. Suspension retains an opaque, reusable checkpoint. -/
private def testOneShotLimits : IO Unit := do
  let main ← moduleId "main.solc"
  let compiled ← get "limited raw preparation" (compile workspace [SourceCoreCompiler.Seed.named main "visibleAlias"]
    {checkingFuel := 1024, specializationBudget := 32, compilationFuel := 128})
  let root ← entry compiled
  let artifact ← compiled.open
  let bootstrap ← artifact.bootstrap
  let bootstrap ← match bootstrap.resume 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | _ => throw (IO.userError "zero bootstrap budget failed to suspend")
  let session ← match bootstrap.resume 300000 with
    | .ready session => pure session
    | _ => throw (IO.userError "bootstrap did not resume")
  match ← session.run root.key [.product (scalar 7) (scalar 8)]
      {inputValidationFuel := 64, executionFuel := 1, outputValidationFuel := 128} with
  | .ok (.outOfFuel checkpoint) =>
      match ← checkpoint.resume 300000 128 with
      | .succeeded done => assertTrue (done.value == scalar 12) "limited invocation changed resumed result"
      | _ => throw (IO.userError "limited invocation did not resume")
  | _ => throw (IO.userError "execution budget was conflated with validation or preparation")

/-- Durable runtime, root, ABI, evidence, staging and boundary regressions use
one compiler and one owned-value session API. -/
def testSourceCompiler : IO Unit := do
  let prepared ← testCheckedReuse
  testProgramOrchestration
  testInputBoundary prepared
  testOneShotLimits
  testCapabilities prepared.checked
  testCompilationErrors prepared.checked
  let main ← moduleId "main.solc"
  let blocked ← moduleId "blocked.solc"
  SourceCompilerRetainedBoundary.run prepared.checked
    (SourceCoreCompiler.Seed.named main "visibleAlias") (SourceCoreCompiler.Seed.named main "direct")
    (SourceCoreCompiler.Seed.named blocked "blocked") (SourceCoreCompiler.Seed.named blocked "dependent")
  IO.println "public source compiler integration GREEN"
end Tests.SourceCompiler
