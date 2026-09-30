import Solcore
/-! End-to-end regressions for the public source compiler boundary. -/
set_option autoImplicit false
namespace Tests.SourceCompiler
open Solcore Solcore.Frontend Solcore.TypeSystem
open Solcore.Frontend.SourceCompiler
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
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
ABI discovery, re-export aliases, and mixed-backend multi-root compilation. -/
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
private def compilerOptions : CompileOptions :=
  { specializationBudget := 32, stagingFuel := 128 }
private def runtimeOptions : RunOptions :=
  { inputValidationFuel := 64, executionFuel := 4096 }
private def checkedWorkspace : IO CheckedProgram := do
  match checkProgram workspace with
  | .ok checked => pure checked
  | .error errors => throw (IO.userError
      s!"compiler fixture failed checking: {reprStr errors}")
private def compileNamed (checked : CheckedProgram) (path name : String) :
    IO CompiledEntry := do
  let selectedModule ← moduleId path
  match compileChecked checked (Seed.named selectedModule name) compilerOptions with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError
      s!"`{path}.{name}` failed compilation: {reprStr error}")
private def compileNamedWithBackend (checked : CheckedProgram)
    (path name : String) (preference : BackendPreference) :
    IO CompiledEntry := do
  let selectedModule ← moduleId path
  let options := { compilerOptions with backendPreference := preference }
  match compileChecked checked (Seed.named selectedModule name) options with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError
      (s!"`{path}.{name}` failed compilation for {reprStr preference}: " ++
        reprStr error))
private def expectCoreWord (label : String) (expected : Nat) :
    Except RunError ExecutionResult → IO Unit
  | .ok (.core (.done (.word actual) [])) =>
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")
private def expectTypedWord (label : String) (expected : Nat) :
    Except RunError ExecutionResult → IO Unit
  | .ok (.typedSource (.done (.word actual) _)) =>
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")
private def expectCoreLanguageWord (label : String) (expected : Nat) :
    Except RunError ExecutionResult → IO Unit
  | .ok (.coreLanguageResult (.succeeded (.word actual) _)) =>
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")
private def expectCoreInteger (label : String) (expected : Int) :
    Except RunError ExecutionResult → IO Unit
  | .ok (.coreLanguageResult (.succeeded (.integer actual) _)) =>
      assertTrue (actual == expected) s!"{label} returned the wrong integer"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")
private def expectTypedGlobal (label : String) :
    Except RunError ExecutionResult → IO Unit
  | .ok (.typedSource (.done (.global _ _) _)) => pure ()
  | result => throw (IO.userError s!"{label} returned {reprStr result}")
private def expectCoreDeepStage (label : String)
    (expectedLeft expectedMiddle expectedRight : Nat) :
    Except RunError ExecutionResult → IO Unit
  | .ok (.coreLanguageResult (.succeeded
      (.pair (.word actualLeft)
        (.pair (.word actualMiddle) (.word actualRight))) _)) =>
      assertTrue (actualLeft == word expectedLeft &&
          actualMiddle == word expectedMiddle &&
          actualRight == word expectedRight)
        s!"{label} returned the wrong nested staged product"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private structure PreparedSet where
  checked : CheckedProgram
  direct : CompiledEntry
  recursive : CompiledEntry
  typed : CompiledEntry

private def testCheckedReuseAndPrecedence : IO PreparedSet := do
  let checked ← checkedWorkspace
  let direct ← compileNamed checked "main.solc" "direct"
  let recursive ← compileNamed checked "main.solc" "recurse"
  let typed ← compileNamed checked "main.solc" "visibleAlias"
  let polymorphicLocal ← compileNamed checked "main.solc" "polymorphicLocal"
  let nestedPolymorphicLocal ←
    compileNamed checked "main.solc" "nestedPolymorphicLocal"
  let recursiveContextPolymorphicLocal ←
    compileNamed checked "main.solc" "recursiveContextPolymorphicLocal"
  let localProof ← compileNamed checked "main.solc" "localProof"
  let typedEvidence ← compileNamed checked "main.solc" "typedEvidence"
  let typedCoercion ← compileNamed checked "main.solc" "typedCoercion"
  let functionFromCoercion ←
    compileNamed checked "main.solc" "functionFromCoercion"
  let main ← moduleId "main.solc"
  assertTrue (decide (
      direct.backend = .core ∧
      recursive.backend = .core ∧
      typed.backend = .typedSource ∧
      polymorphicLocal.backend = .typedSource ∧
      nestedPolymorphicLocal.backend = .typedSource ∧
      recursiveContextPolymorphicLocal.backend = .typedSource ∧
      localProof.backend = .typedSource ∧
      typedEvidence.backend = .typedSource ∧
      typedCoercion.backend = .typedSource ∧
      functionFromCoercion.backend = .typedSource))
    "automatic backend precedence changed"
  assertTrue (decide (
      direct.key.declaration.moduleId = main ∧
      recursive.key.declaration.moduleId = main ∧
      typed.key.declaration.moduleId = main ∧
      direct.key.arguments = [] ∧ recursive.key.arguments = [] ∧
      typed.key.arguments = []))
    "compiled roots lost their canonical module or ground arguments"
  assertTrue (decide (
      direct.inputTypes = [.word] ∧ direct.resultType = .word ∧
      recursive.inputTypes = [.word] ∧ recursive.resultType = .word ∧
      typed.inputTypes = [.product .word .word] ∧ typed.resultType = .word))
    "backend-independent source signature metadata changed"
  assertTrue (direct.specializationCount == 1 &&
      recursive.specializationCount == 1 && typed.specializationCount == 1)
    "a single-function fixture retained an unexpected specialization plan"
  assertTrue (polymorphicLocal.specializationCount == 3)
    "local polymorphism did not retain its root and two generic helper instances"
  assertTrue (nestedPolymorphicLocal.specializationCount == 3)
    "depth-2 local polymorphism did not retain its root and two generic helper instances"
  assertTrue (recursiveContextPolymorphicLocal.specializationCount == 3)
    "recursive local contexts did not retain their root and two generic helper instances"
  assertTrue (localProof.specializationCount == 3)
    "local proof calls did not retain their root and two constrained helper instances"
  assertTrue (typedEvidence.specializationCount == 3)
    "typed evidence forwarding did not retain root, relay, and callee"
  let polymorphicRequest ←
    match SourceProgramExecution.resolveSeed checked
        (Seed.named main "polymorphicLocal") with
    | .ok request => pure request
    | .error error => throw (IO.userError
        s!"polymorphic-local seed resolution failed: {reprStr error}")
  match SourceSpecializationWorklist.run checked [polymorphicRequest]
      compilerOptions.specializationBudget with
  | .ok (.complete plan) =>
      assertTrue (plan.specializations.length == 3 && plan.callEdges.length == 2)
        "local polymorphism did not discover both contextual generic calls"
  | result => throw (IO.userError
      s!"polymorphic-local plan reconstruction failed: {reprStr result}")
  let nestedPolymorphicRequest ←
    match SourceProgramExecution.resolveSeed checked
        (Seed.named main "nestedPolymorphicLocal") with
    | .ok request => pure request
    | .error error => throw (IO.userError
        s!"depth-2 polymorphic-local seed resolution failed: {reprStr error}")
  match SourceSpecializationWorklist.run checked [nestedPolymorphicRequest]
      compilerOptions.specializationBudget with
  | .ok (.complete plan) =>
      let edges := plan.callEdges.filter fun edge =>
        decide (edge.caller = nestedPolymorphicLocal.key)
      assertTrue (decide (
          plan.specializations.length = 3 ∧
          plan.callEdges.length = 2 ∧
          edges.length = 2 ∧
          (edges.map (·.occurrence)).eraseDups.length = 1 ∧
          (edges.map (·.callee.arguments)).contains [.word] ∧
          (edges.map (·.callee.arguments)).contains [.bool]))
        "depth-2 local polymorphism did not discover two contextual generic calls"
  | result => throw (IO.userError
      s!"depth-2 polymorphic-local plan reconstruction failed: {reprStr result}")
  let recursiveContextRequest ←
    match SourceProgramExecution.resolveSeed checked
        (Seed.named main "recursiveContextPolymorphicLocal") with
    | .ok request => pure request
    | .error error => throw (IO.userError
        s!"recursive-context seed resolution failed: {reprStr error}")
  match SourceSpecializationWorklist.run checked [recursiveContextRequest]
      compilerOptions.specializationBudget with
  | .ok (.complete plan) =>
      let edges := plan.callEdges.filter fun edge =>
        decide (edge.caller = recursiveContextPolymorphicLocal.key)
      assertTrue (decide (
          plan.specializations.length = 3 ∧
          plan.callEdges.length = 2 ∧
          edges.length = 2 ∧
          (edges.map (·.occurrence)).eraseDups.length = 1 ∧
          (edges.map (·.callee.arguments)).contains [.word] ∧
          (edges.map (·.callee.arguments)).contains [.bool]))
        "recursive local contexts did not discover two contextual generic calls"
  | result => throw (IO.userError
      s!"recursive-context plan reconstruction failed: {reprStr result}")
  expectCoreWord "direct Core root" 14 <|
    direct.runCore [.word (word 7)] runtimeOptions
  expectCoreWord "reused direct Core root" 18 <|
    direct.runCore [.word (word 9)] runtimeOptions
  match direct.runCore [.word (word 4)] runtimeOptions [.bool true] with
  | .ok (.core (.done (.word actual) [.bool retained])) =>
      assertTrue (actual == word 8 && retained)
        "direct Core execution did not retain its supplied store"
  | result => throw (IO.userError
      s!"direct Core execution changed its exact state: {reprStr result}")
  expectCoreLanguageWord "automatic recursive Core root" 31 <|
    recursive.runCore [.word (word 3)] runtimeOptions
  let explicitTypedRecursive ← compileNamedWithBackend checked "main.solc" "recurse" .typedSource
  expectTypedWord "explicit recursive typed root" 31 <|
    explicitTypedRecursive.runTyped [.word (word 3)] runtimeOptions
  expectTypedWord "imported alias typed root" 12 <|
    typed.runTyped [.product (.word (word 7)) (.word (word 8))] runtimeOptions
  match polymorphicLocal.runTyped [.bool true] runtimeOptions with
  | .ok (.typedSource (.done
      (.product (.word actualWord) (.bool actualBool)) _)) =>
      assertTrue (actualWord == word 11 && actualBool)
        "runtime let-polymorphism did not independently instantiate Word and Bool"
  | result => throw (IO.userError
      s!"runtime let-polymorphism returned {reprStr result}")
  match nestedPolymorphicLocal.runTyped [.bool true] runtimeOptions with
  | .ok (.typedSource (.done
      (.product (.word actualWord) (.bool actualBool)) _)) =>
      assertTrue (actualWord == word 13 && actualBool)
        "runtime depth-2 let-polymorphism did not independently instantiate Word and Bool"
  | result => throw (IO.userError
      s!"runtime depth-2 let-polymorphism returned {reprStr result}")
  match recursiveContextPolymorphicLocal.runTyped [.bool true] runtimeOptions with
  | .ok (.typedSource (.done
      (.product (.word actualWord) (.bool actualBool)) _)) =>
      assertTrue (actualWord == word 15 && actualBool)
        "runtime recursive local contexts did not instantiate Word and Bool"
  | result => throw (IO.userError
      s!"runtime recursive local contexts returned {reprStr result}")
  match localProof.runTyped [.bool true] runtimeOptions with
  | .ok (.typedSource (.done
      (.product (.word actualWord) (.bool actualBool)) _)) =>
      assertTrue (actualWord == word 2 && actualBool)
        "runtime local proof calls did not retain Word/Bool results"
  | result => throw (IO.userError
      s!"runtime local proof calls returned {reprStr result}")
  expectTypedWord "public typed evidence forwarding" 73 <|
    typedEvidence.runTyped [.word (word 73)] runtimeOptions
  expectTypedWord "public stateful coercion (true)" 42 <|
    typedCoercion.runTyped [.bool true] runtimeOptions
  expectTypedWord "public stateful coercion (false)" 8 <|
    typedCoercion.runTyped [.bool false] runtimeOptions
  expectTypedGlobal "public method-discovered function result" <|
    functionFromCoercion.runTyped [.word (word 1)] runtimeOptions
  pure { checked, direct, recursive, typed }

/-- An explicit preference selects exactly the requested runtime, while all
public backends agree on the same closed source computation. -/
private def testExplicitBackendAgreement (checked : CheckedProgram) : IO Unit := do
  let core ← compileNamedWithBackend checked "main.solc" "direct" .core
  let typed ← compileNamedWithBackend checked "main.solc" "direct" .typedSource
  assertTrue (decide (core.backend = .core ∧ typed.backend = .typedSource))
    "an explicit backend preference selected a different runtime"
  expectCoreWord "explicit direct-Core agreement" 14 <|
    core.runCore [.word (word 7)] runtimeOptions
  expectTypedWord "explicit typed-source agreement" 14 <|
    typed.runTyped [.word (word 7)] runtimeOptions

private def abiRootNamed (compiled : CompiledStaticWordProgram)
    (name : String) : IO CompiledStaticWordRoot :=
  match compiled.roots.find? fun root => root.metadata.name.text == name with
  | some root => pure root
  | none => throw (IO.userError s!"missing compiled ABI root `{name}`")

/-- Exercise raw entry discovery, ordered/duplicate multi-root artifacts,
mixed automatic backend selection, exported ABI aliases, and selector lookup. -/
private def testProgramOrchestration : IO Unit := do
  let api ← moduleId "api.solc"
  let provider ← moduleId "provider.solc"
  let entry ← match compileEntry orchestrationWorkspace with
    | .ok entry => pure entry
    | .error error => throw (IO.userError
        s!"automatic main compilation failed: {reprStr error}")
  assertTrue (entry.backend == .core && entry.inputTypes.isEmpty &&
      entry.resultType == .word && entry.key.declaration.moduleId == api)
    "automatic main discovery lost its entry module, signature, or backend"
  expectCoreWord "automatic workspace main" 17 <|
    entry.runCore [] runtimeOptions

  let checked ← match checkProgram orchestrationWorkspace with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"orchestration fixture failed checking: {reprStr errors}")
  let requested := [
    Seed.named provider "twice",
    Seed.named provider "recursive",
    Seed.named provider "twice"
  ]
  let many ← match compileManyChecked checked requested compilerOptions with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError
        s!"checked multi-root compilation failed: {reprStr error}")
  match many.entries with
  | [first, second, third] =>
      assertTrue (decide (many.count = 3 ∧
          many.backends = [.core, .core, .core] ∧
          many.usesMixedBackends = false ∧
          first.key = third.key ∧ first.key ≠ second.key))
        "multi-root order, duplicates, or Core backend selection changed"
  | entries => throw (IO.userError
      s!"multi-root compilation returned {entries.length} entries")
  match compileManyChecked checked
      [Seed.named provider "twice", Seed.named provider "missing"]
      compilerOptions with
  | .error failure =>
      assertTrue (decide (failure.index = 1 ∧
          failure.seed = Seed.named provider "missing"))
        "multi-root failure lost its exact request position or seed"
  | .ok _ => throw (IO.userError "missing second root compiled successfully")

  let rawMany ← match compileMany orchestrationWorkspace requested with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError
        s!"raw multi-root compilation failed: {reprStr error}")
  assertTrue (rawMany.backends == [.core, .core, .core] &&
      !rawMany.usesMixedBackends)
    "raw compile-many did not preserve Core per-root selection"

  let abi ← match compileStaticWord orchestrationWorkspace with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError
        s!"Static Word root compilation failed: {reprStr error}")
  assertTrue (abi.count == 3 && !abi.usesMixedBackends)
    "Static Word discovery lost an exported root or Core backend"
  let doubled ← abiRootNamed abi "doubled"
  let localRoot ← abiRootNamed abi "local"
  let recursive ← abiRootNamed abi "recursive"
  assertTrue (decide (
      doubled.entry.key.declaration.moduleId = provider ∧
      localRoot.entry.key.declaration.moduleId = api ∧
      recursive.entry.key.declaration.moduleId = provider ∧
      doubled.entry.backend = .core ∧ localRoot.entry.backend = .core ∧
      recursive.entry.backend = .core ∧
      (abi.roots.find? fun root =>
        root.metadata.name.text == "hidden").isNone ∧
      (abi.roots.find? fun root =>
        root.metadata.name.text == "providerOnly").isNone))
    "ABI export/alias/module filtering or backend selection changed"
  match abi.rootForSelector? doubled.metadata.selector with
  | some selected =>
      assertTrue (selected.metadata.name.text == "doubled")
        "selector lookup returned a different ABI root"
  | none => throw (IO.userError "selector lookup lost an admitted ABI root")
  expectCoreWord "exported ABI alias" 14 <|
    doubled.entry.runCore [.word (word 7)] runtimeOptions
  expectCoreWord "exported local ABI root" 8 <|
    localRoot.entry.runCore [.word (word 7)] runtimeOptions
  expectCoreLanguageWord "exported recursive ABI root" 31 <|
    recursive.entry.runCore [.word (word 3)] runtimeOptions

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
  | .error (.seed (.unknownName actual "main")) =>
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

private def testTypedBoundary (prepared : PreparedSet) : IO Unit := do
  let pair : SourceTypedRuntime.Value :=
    .product (.word (word 7)) (.word (word 8))
  match prepared.typed.runTyped [.bool true] runtimeOptions with
  | .ok (.typedSource (.fault (.typeMismatch expected actual) state)) =>
      assertTrue (decide (
          expected = Ty.product .word .word ∧ actual = some Ty.bool) &&
          state.heap.isEmpty)
        "typed input rejection changed its type or mutated the heap"
  | result => throw (IO.userError
      s!"ill-typed public source input was accepted: {reprStr result}")
  let shallowValidation : RunOptions :=
    { inputValidationFuel := 1, executionFuel := 4096 }
  match prepared.typed.runTyped [pair] shallowValidation with
  | .ok (.typedSource (.fault
      (.inputValidationFuelExhausted expected 1) state)) =>
      assertTrue (decide (expected = Ty.product .word .word) &&
          state.heap.isEmpty)
        "typed validation exhaustion lost its expected type or initial heap"
  | result => throw (IO.userError
      s!"typed input validation exhaustion was misclassified: {reprStr result}")
  let malformedInitial : SourceTypedRuntime.RuntimeState := {
    heap := [{ type := .word, value := some (.bool true) }]
  }
  match prepared.typed.runTyped [pair] runtimeOptions malformedInitial with
  | .ok (.typedSource (.fault
      .deepSafetyInitialStateRejected finalState)) =>
      match finalState.heap with
      | [{ type := .word, value := some (.bool retained) }] =>
          assertTrue retained
            "deep initial-state rejection changed the supplied heap"
      | heap => throw (IO.userError
          s!"deep initial-state rejection mutated the supplied heap: {reprStr heap}")
  | result => throw (IO.userError
      s!"malformed initial heap crossed the deep boundary: {reprStr result}")
  let shallowExecution : RunOptions :=
    { inputValidationFuel := 64, executionFuel := 1 }
  match prepared.typed.runTyped [pair] shallowExecution with
  | .ok (.typedSource (.outOfFuel state)) =>
      assertTrue (state.heap.length == 1)
        "typed exhaustion did not retain the bound parameter cell"
  | result => throw (IO.userError
      s!"typed execution fuel was not independent: {reprStr result}")
  match prepared.typed.runCore [.word (word 7)] runtimeOptions with
  | .error (.invocationKindMismatch .typedSource .coreValues) => pure ()
  | result => throw (IO.userError
      s!"a Core-domain invocation crossed the typed backend: {reprStr result}")
  match prepared.direct.runTyped [] runtimeOptions with
  | .error (.invocationKindMismatch .core .typedValues) => pure ()
  | result => throw (IO.userError
      s!"a typed invocation crossed the direct Core backend: {reprStr result}")
  match prepared.direct.runCore [.bool true] runtimeOptions with
  | .error (.coreInputTypesMismatch [.word] [.bool]) => pure ()
  | result => throw (IO.userError
      s!"direct Core input mismatch lost its public category: {reprStr result}")
  let retainedState : SourceTypedRuntime.RuntimeState := {
    heap := [{ type := .word, value := some (.word (word 99)) }]
  }
  match prepared.typed.runTyped [pair] runtimeOptions retainedState with
  | .ok (.typedSource (.done (.word actual) finalState)) =>
      match finalState.heap with
      | { type := .word, value := some (.word retained) } :: _ =>
          assertTrue (actual == word 12 && retained == word 99)
            "deep execution changed a pre-existing cell or the source result"
      | heap => throw (IO.userError
          s!"deep execution did not preserve the initial type layout: {reprStr heap}")
  | result => throw (IO.userError
      s!"valid nonempty initial heap failed the deep boundary: {reprStr result}")
  let zeroValidation : RunOptions := {
    inputValidationFuel := 0
    executionFuel := 4096
  }
  match prepared.typed.runTyped [pair] zeroValidation retainedState with
  | .ok (.typedSource (.fault
      (.inputValidationFuelExhausted expected 0) finalState)) =>
      match finalState.heap with
      | [{ type := .word, value := some (.word retained) }] =>
          assertTrue (decide (expected = Ty.product .word .word) &&
              retained == word 99)
            "zero validation fuel changed the expected type or initial heap"
      | heap => throw (IO.userError
          s!"validation rejection mutated the supplied heap: {reprStr heap}")
  | result => throw (IO.userError
      s!"zero validation fuel changed public behavior: {reprStr result}")

private def testOneShotLimits : IO Unit := do
  let main ← moduleId "main.solc"
  let limits : Limits := {
    checkingFuel := 1024
    specializationBudget := 32
    stagingFuel := 128
    inputValidationFuel := 64
    executionFuel := 1
  }
  match SourceCompiler.run workspace (Seed.named main "visibleAlias")
      (Invocation.typedFresh [
        .product (.word (word 7)) (.word (word 8))]) limits with
  | .ok (.typedSource (.outOfFuel state)) =>
      assertTrue (state.heap.length == 1)
        "one-shot limits did not reach the selected typed runtime"
  | result => throw (IO.userError
      s!"one-shot compiler boundary returned {reprStr result}")

private def testBackendDiagnostics (checked : CheckedProgram) : IO Unit := do
  let blocked ← moduleId "blocked.solc"
  let main ← moduleId "main.solc"
  let coreOptions := {
    compilerOptions with backendPreference := .core
  }
  let recursive ← compileNamedWithBackend checked "main.solc" "recurse" .core
  expectCoreLanguageWord "forced recursive Core root" 31 <|
    recursive.runCore [.word (word 3)] runtimeOptions
  match compileChecked checked (Seed.named main "visibleAlias") coreOptions with
  | .error (.backendRejected (.core _)) => pure ()
  | .error error => throw (IO.userError
      s!"forced Core rejection changed category: {reprStr error}")
  | .ok compiled => throw (IO.userError
      s!"forced Core silently fell through to {reprStr compiled.backend}")
  match compileChecked checked (Seed.named blocked "blocked") compilerOptions with
  | .error (.noBackend [
      .core directError,
      .typedSource typedSourceError
    ]) =>
      match directError with
      | .sourceCore _ => pure ()
      | error => throw (IO.userError
          s!"direct rejection lost its source-Core category: {reprStr error}")
      match typedSourceError with
      | .executableCoercionMethod _ _ _
          (.missingTraitMethod _ "coerce") => pure ()
      | error => throw (IO.userError
          s!"typed rejection lost its evidence diagnostic: {reprStr error}")
  | .error error => throw (IO.userError
      s!"automatic backend rejection changed category: {reprStr error}")
  | .ok compiled => throw (IO.userError
      s!"an unsupported root selected {reprStr compiled.backend}")
private def typedRejection (checked : CheckedProgram) (name : String) :
    IO SourceTypedRuntime.RuntimeError := do
  let blocked ← moduleId "blocked.solc"
  let typedOptions := {
    compilerOptions with backendPreference := .typedSource
  }
  match compileChecked checked (Seed.named blocked name) typedOptions with
  | .error (.backendRejected (.typedSource error)) => pure error
  | .error error => throw (IO.userError
      s!"`{name}` changed rejection stage: {reprStr error}")
  | .ok compiled => throw (IO.userError
      s!"`{name}` bypassed staging through {reprStr compiled.backend}")

private def testTypedCapabilityBoundary (checked : CheckedProgram) : IO Unit := do
  let constrained ← compileNamed checked "blocked.solc" "constrained"
  let staged ← compileNamed checked "blocked.solc" "staged"
  let stagedTyped ← compileNamedWithBackend checked "blocked.solc" "staged" .typedSource
  let stagedType ← compileNamed checked "blocked.solc" "stagedType"
  let integerResult ← compileNamed checked "blocked.solc" "integerResult"
  let nestedStaged ← compileNamed checked "blocked.solc" "nestedStaged"
  let nestedComptime ←
    compileNamed checked "blocked.solc" "nestedComptime"
  let integerBitAnd ← compileNamed checked "blocked.solc" "integerBitAnd"
  let integerBitXor ← compileNamed checked "blocked.solc" "integerBitXor"
  let integerBitOr ← compileNamed checked "blocked.solc" "integerBitOr"
  let integerBitNot ← compileNamed checked "blocked.solc" "integerBitNot"
  let markedEffects ←
    compileNamed checked "blocked.solc" "markedEffects"
  let markedEffectsEntry ←
    compileNamed checked "blocked.solc" "markedEffectsEntry"
  assertTrue (decide (
      constrained.backend = .typedSource ∧
      staged.backend = .core ∧
      stagedTyped.backend = .typedSource ∧
      stagedType.backend = .core ∧
      integerResult.backend = .core ∧
      nestedStaged.backend = .core ∧
      nestedComptime.backend = .core ∧
      integerBitAnd.backend = .core ∧
      integerBitXor.backend = .core ∧
      integerBitOr.backend = .core ∧
      integerBitNot.backend = .core ∧
      markedEffects.backend = .typedSource ∧
      markedEffectsEntry.backend = .typedSource))
    "staged capability cases selected an unexpected backend"
  assertTrue (decide (
      constrained.inputTypes = [.word] ∧ constrained.resultType = .word ∧
      staged.inputTypes = [.word] ∧ staged.resultType = .word ∧
      stagedType.inputTypes = [.comptime .word] ∧
      stagedType.resultType = .word ∧
      integerResult.inputTypes = [] ∧
      integerResult.resultType = .integer ∧
      nestedStaged.inputTypes = [.product .word (.comptime .word)] ∧
      nestedStaged.resultType = .word ∧
      nestedComptime.inputTypes = [
        .product (.comptime .word)
          (.product .word (.comptime .word))] ∧
      nestedComptime.resultType =
        .product (.comptime .word)
          (.product .word (.comptime .word)) ∧
      integerBitAnd.inputTypes = [] ∧ integerBitAnd.resultType = .integer ∧
      integerBitXor.inputTypes = [] ∧ integerBitXor.resultType = .integer ∧
      integerBitOr.inputTypes = [] ∧ integerBitOr.resultType = .integer ∧
      integerBitNot.inputTypes = [] ∧ integerBitNot.resultType = .integer ∧
      markedEffects.inputTypes = [.word] ∧
      markedEffects.resultType = .word ∧
      markedEffectsEntry.inputTypes = [] ∧
      markedEffectsEntry.resultType = .word))
    "staged capability cases lost their source signature metadata"
  expectTypedWord "ground constrained public root" 19 <|
    constrained.runTyped [.word (word 19)] runtimeOptions
  match staged.runCore [.word (word 23)] runtimeOptions with
  | .ok (.coreLanguageResult (.succeeded (.word actual) [.inRight .unit (.word stored)])) =>
      assertTrue (actual == word 23 && stored == word 23)
        "marked public Core input lost its exact value or input cell"
  | result => throw (IO.userError s!"marked public input did not use prepared Core: {reprStr result}")
  expectTypedWord "explicit typed-source marked public input" 23 <|
    stagedTyped.runTyped [.word (word 23)] runtimeOptions
  expectCoreLanguageWord "structural comptime input" 1 <|
    stagedType.runCore [.word (word 29)] runtimeOptions
  expectCoreInteger "integer result" 1 <|
    integerResult.runCore [] runtimeOptions
  expectCoreLanguageWord "nested comptime input" 1 <|
    nestedStaged.runCore
      [.pair (.word (word 2)) (.word (word 3))] runtimeOptions
  match ← typedRejection checked "dependent" with
  | .stagedExpressionType _ type =>
      assertTrue (decide (type = Ty.integer))
        "runtime-dependent staged expression lost its Integer type"
  | error => throw (IO.userError
      s!"runtime-dependent staged expression changed rejection: {reprStr error}")
  expectCoreDeepStage "recursively erased comptime product" 4 5 6 <|
    nestedComptime.runCore [
      .pair (.word (word 4))
        (.pair (.word (word 5)) (.word (word 6)))] runtimeOptions
  expectCoreInteger "integer bitwise and" 1 <|
    integerBitAnd.runCore [] runtimeOptions
  expectCoreInteger "integer bitwise xor" 6 <|
    integerBitXor.runCore [] runtimeOptions
  expectCoreInteger "integer bitwise or" 7 <|
    integerBitOr.runCore [] runtimeOptions
  expectCoreInteger "integer bitwise not" (-6) <|
    integerBitNot.runCore [] runtimeOptions
  expectTypedWord "marked closure/mutation/mapping" 12 <|
    markedEffects.runTyped [.word (word 9)] runtimeOptions
  expectTypedWord "effectful staged call" 12 <|
    markedEffectsEntry.runTyped [] runtimeOptions

private def testPublicCompilationErrors (checked : CheckedProgram) : IO Unit := do
  let main ← moduleId "main.solc"
  match compileChecked checked (Seed.named main "missing") compilerOptions with
  | .error (.seed (.unknownName actual "missing")) =>
      assertTrue (decide (actual = main))
        "unknown-name compilation error lost its module"
  | .error error => throw (IO.userError
      s!"unknown public root changed error category: {reprStr error}")
  | .ok compiled => throw (IO.userError
      s!"unknown public root selected {reprStr compiled.backend}")
  let noSpecializations : CompileOptions :=
    { specializationBudget := 0, stagingFuel := 128 }
  match compileChecked checked (Seed.named main "direct") noSpecializations with
  | .error (.specializationBudgetExhausted next pendingCount) =>
      assertTrue (decide (next.declaration.moduleId = main) && pendingCount > 0)
        "specialization exhaustion lost its frontier"
  | .error error => throw (IO.userError
      s!"specialization budget changed error category: {reprStr error}")
  | .ok compiled => throw (IO.userError
      s!"zero specialization budget selected {reprStr compiled.backend}")

private def testCheckingFailurePrecedence : IO Unit := do
  let invalid : Workspace.RawWorkspace := {
    entry := "broken.solc"
    mainSources := [{
      path := "broken.solc"
      content := "function broken(value: Word returns (Word) { return value; }"
    }]
    externalLibraries := []
  }
  let brokenModule ← moduleId "broken.solc"
  match compile invalid (Seed.named brokenModule "broken") with
  | .error (.checking (_ :: _)) => pure ()
  | .error error => throw (IO.userError
      s!"malformed source escaped the checking phase: {reprStr error}")
  | .ok compiled => throw (IO.userError
      s!"malformed source selected {reprStr compiled.backend}")

/-- Exercise compile-once reuse, exact backend selection, whole-program root
discovery, exact results, staged execution, and public-boundary hardening. -/
def testSourceCompiler : IO Unit := do
  let prepared ← testCheckedReuseAndPrecedence
  testExplicitBackendAgreement prepared.checked
  testProgramOrchestration
  testTypedBoundary prepared
  testOneShotLimits
  testBackendDiagnostics prepared.checked
  testTypedCapabilityBoundary prepared.checked
  testPublicCompilationErrors prepared.checked
  testCheckingFailurePrecedence
  IO.println "public source compiler integration GREEN"

end Tests.SourceCompiler
