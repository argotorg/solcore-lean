import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.Frontend.Current
import Solcore.Frontend.SourceCoreUnified
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceCore.RawMetadata
import Solcore.Frontend.SourceCore.Compatible

/-!
# Unified corpus tests

The unified runtime on canonical checked programs: control, evidence, staging and the import boundary.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreUnifiedControlCorpus
/-! Checker-produced control, assignment order and native scalar programs,
ported from the executable typed-runtime corpus. Trusted IR rewrites are absent. -/
set_option autoImplicit false
namespace Tests.SourceCoreUnifiedControlCorpus
open Solcore Solcore.Frontend SourceInference
open SourceCoreUnifiedCorpusSupport

private def source : String := String.intercalate "\n" [
  "function assignments() returns (Word) { let local: Word = 5; local += 3; local ~=; return local; }",
  "function mappings() returns (Word) { let table: mapping(Word => Word); let before: Word = table[7]; table[7] = 4; table[7] += 3; let nested: mapping(Word => mapping(Word => Word)); nested[1][2] = 9; return before + table[7] + nested[1][2]; }",
  "function loops() returns (Word) { let total: Word = 0; let i: Word = 0; while (i < 5) { i += 1; if (i == 2) { continue; } if (i == 4) { break; } total += i; } for (let j: Word = 0; j < 4; j += 1) { if (j == 1) { continue; } if (j == 3) { break; } total += j; } return total; }",
  "function assignmentOrder() returns (Word) { let order: Word = 0; let table: mapping(Word => Word); let indexer = lam() -> Word { order = order * 10 + 1; return 5; }; let rhs = lam() -> Word { order = order * 10 + 2; return 7; }; table[indexer()] = rhs(); return order * 100 + table[5]; }",
  "function compoundSnapshot() returns (Word) { let value: Word = 5; let rhs = lam() -> Word { value = 20; return 3; }; value += rhs(); return value; }",
  "function targetFailure() returns (Word) { let order: Word = 0; let table: mapping(Word => Word); let indexer = lam() -> Word { order = 1; let absent: Word; return absent; }; let rhs = lam() -> Word { order = 2; return 7; }; table[indexer()] = rhs(); return order; }",
  "function rhsFailure() returns (Word) { let target: Word; let rhs = lam() -> Word { let absent: Word; return absent; }; target += rhs(); return 0; }",
  "function unaryAbsent() returns (Word) { let target: Word; target ~=; return 0; }",
  "function integerBitNot() returns (integer) { return ~5; }",
  "function integerBitAndNegative() returns (integer) { return integerSub(0, 5) & 3; }",
  "function integerBitOrNegative() returns (integer) { return 2 | integerSub(0, 5); }",
  "function integerBitXorNegative() returns (integer) { return integerSub(0, 5) ^ 2; }",
  "function descend(value: Word) returns (Word) { return value == 0 ? 9 : descend(value - 1); }",
  "function even(value: Word) returns (Bool) { return value == 0 ? true : odd(value - 1); }",
  "function odd(value: Word) returns (Bool) { return value == 0 ? false : even(value - 1); }",
  "function implicitTail() returns (Word) { 40 + 2 }",
  "function spin(value: Word) returns (Word) { return spin(value); }"
]

private def binder (compiled : Compiled) (name localName : String) : IO Resolved.LocalId := do
  let owner ← key compiled.sourceProgram name
  let function ← get "fault binder specialization" (SourceCompilationPlan.exactSpecialization compiled.validationPlan owner)
  match (SourceCoreDataPlaces.declaredBinders function.function.typedBody).filter (·.name == localName) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"{name} exact fault binder missing")

def run : IO Unit := do
  let compiled ← prepare "control/order" source ["assignments", "mappings", "loops", "assignmentOrder",
    "compoundSnapshot", "targetFailure", "rhsFailure", "unaryAbsent", "integerBitNot",
    "integerBitAndNegative", "integerBitOrNegative", "integerBitXorNegative", "descend", "even", "implicitTail", "spin"]
  let assignments ← expect compiled "assignments" [] (.word (Core.Word.maximum.sub (word 8)))
  assertTrue (assignments.heap.length == 1) "bit-not source allocation changed"
  let mappings ← expect compiled "mappings" [] (.word (word 16))
  assertTrue (mappings.heap.length == 3 && hasWord mappings 0) "nested/default mapping source allocations changed"
  for spent in [0, 43, 300000] do
    discard <| expect compiled "loops" [] (.word (word 6)) spent
  /- Closures capture by value. Each closure call writes only its own copy of
  `order`, which stays 0, so this result no longer tells the index call from
  the RHS call; the calls' copies hold 1 and 2. -/
  let ordered ← expect compiled "assignmentOrder" [] (.word (word 7))
  assertTrue (hasWord ordered 1 && hasWord ordered 2) "index/RHS closure calls lost the writes to their copies"
  /- `rhs` writes 20 only to its own copy of `value`, so the target still holds
  5 when it is read and this result no longer shows whether that read precedes
  the RHS. -/
  let snapshot ← expect compiled "compoundSnapshot" [] (.word (word 8))
  assertTrue (hasWord snapshot 8 && hasWord snapshot 20) "compound assignment or the RHS call's copy changed"
  for (name, expected) in [("integerBitNot", -6), ("integerBitAndNegative", 3),
      ("integerBitOrNegative", -5), ("integerBitXorNegative", -7)] do
    let state ← expect compiled name [] (.integer expected)
    assertTrue state.heap.isEmpty s!"{name} unexpectedly allocated source cells"
  discard <| expect compiled "descend" [.word (word 5)] (.word (word 9)) 41
  discard <| expect compiled "even" [.word (word 6)] (.bool true) 41
  discard <| expect compiled "even" [.word (word 5)] (.bool false)
  discard <| expect compiled "implicitTail" [] (.word (word 42))
  for name in ["targetFailure", "rhsFailure"] do
    let absent ← binder compiled name "absent"
    let result ← execute compiled name
    match result.observation with
    | .fault error state =>
      assertTrue (error == .uninitializedLocal absent) s!"{name} source fault priority or binder changed"
      if name == "targetFailure" then
        assertTrue (hasWord state 1 && !hasWord state 2) "RHS ran after target fault"
    | other => throw (IO.userError s!"{name} source fault changed: {reprStr other}")
  let unary ← execute compiled "unaryAbsent"
  match unary.observation with
  | .fault error _ => assertTrue (error == .invalidUnaryOperand .bitNot none) "bit-not absence diagnostic changed"
  | other => throw (IO.userError s!"missing unary operand returned {reprStr other}")
  let first ← execute compiled "spin" [.word (word 3)] 1200
  let second ← get "recursive spin native resume" (SourceCoreUnifiedCompilation.Result.resume first 1200)
  for result in [first, second] do
    match result.observation with
    | .outOfFuel state => assertTrue (!state.heap.isEmpty) "recursive spin lost source parameter cells"
    | other => throw (IO.userError s!"recursive spin falsely terminated: {reprStr other}")
  IO.println "Core-only checked control, scalar operators, target/RHS order, faults and recursion corpus GREEN"

end Tests.SourceCoreUnifiedControlCorpus
end

section
-- leanmerge: from Solcore.Test.SourceCoreUnifiedEvidenceCorpus
/-! Canonical checked first-class evidence and stateful method interactions,
ported from FirstClassEvidence and StateInteractions. No trusted plan rewrites. -/
set_option autoImplicit false
namespace Tests.SourceCoreUnifiedEvidenceCorpus
open Solcore Solcore.Frontend SourceInference
open SourceCoreUnifiedCorpusSupport

private def source : String := String.intercalate "\n" [
  "trait Eq<T> {}",
  "impl Eq<Word> {}",
  "trait Mark<T> {}",
  "impl Mark<Word> {}",
  "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
  "function keepBoth<T>(value: T) returns (T) where T: Eq, T: Mark { return value; }",
  "function globalValue() returns (function(Word) returns (Word)) {",
  "  return keep;",
  "}",
  "function globalAliasCall(value: Word) returns (Word) {",
  "  let alias: function(Word) returns(Word) = keep;",
  "  return alias(value);",
  "}",
  "function orderedFactory<T>(witness: T) returns (function(T) returns (T)) where T: Mark, T: Eq {",
  "  return keepBoth;",
  "}",
  "function orderedAliasCall(value: Word) returns (Word) {",
  "  let alias = orderedFactory(value);",
  "  return alias(value);",
  "}",
  "function localFactory<T>(witness: T) returns (function(T) returns (T)) where T: Eq {",
  "  let f = lam(value) { return keep(value); };",
  "  let alias: function(T) returns(T) = f;",
  "  return alias;",
  "}",
  "function qualifiedLocalAliasCall(value: Word) returns (Word) {",
  "  let alias = localFactory(value);",
  "  return alias(value);",
  "}",
  "function repeat<T>(value: T, count: Word) returns (T) where T: Eq {",
  "  return count == 0 ? value : repeat(value, count - 1);",
  "}",
  "function recursiveClosure<T>(witness: T) returns (function(T, Word) returns (T)) where T: Eq {",
  "  let invoke = lam(value: T, count: Word) -> T { return repeat(value, count); };",
  "  return invoke;",
  "}",
  "function genericRecursiveClosureCall(value: Word) returns (Word) {",
  "  let invoke = recursiveClosure(value);",
  "  return invoke(value, 3);",
  "}",
  "function applyStored(f: function(Word) returns(Word), value: Word) returns (Word) {",
  "  let retained: function(Word) returns(Word) = keep;",
  "  return f(value);",
  "}",
  "trait Witness<T> {}",
  "impl Witness<Word> {}",
  "function retain<T>(value: T) returns (T) where T: Witness {",
  "  return value;",
  "}",
  "function mutateCaptured<T>(value: T, key: Word) returns (Word)",
  "    where T: Witness {",
  "  let total: Word = 1;",
  "  let table: mapping(Word => Word);",
  "  let mutate = lam(item: T) -> Word {",
  "    let checked: T = retain(item);",
  "    total += 2;",
  "    table[key] = total;",
  "    return table[key];",
  "  };",
  "  let fromCall: Word = mutate(value);",
  "  return fromCall + total + table[key];",
  "}",
  "function capturedStateEntry(value: Word) returns (Word) {",
  "  return mutateCaptured(value, 7);",
  "}",
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(value: Bool) returns (Word) {",
  "    let scratch: mapping(Word => Word);",
  "    scratch[0] = value ? 40 : 6;",
  "    scratch[0] += 2;",
  "    return scratch[0];",
  "  }",
  "}",
  "impl Coerce<Bool, function() returns(Word)> {",
  "  function coerce(value: Bool) returns (function() returns(Word)) {",
  "    let scratch: mapping(Word => Word);",
  "    scratch[0] = value ? 40 : 6;",
  "    return lam() -> Word {",
  "      scratch[0] += 2;",
  "      return scratch[0];",
  "    };",
  "  }",
  "}",
  "function coercionMapping(value: Bool) returns (Word) {",
  "  let output: mapping(Word => Word);",
  "  output[3] = value;",
  "  return output[3];",
  "}",
  "function coercionResult(value: Bool) returns (Word) {",
  "  return value;",
  "}",
  "function coercionCapturedState(value: Bool) returns (Word) {",
  "  let next: function() returns(Word) = value;",
  "  return next() + next();",
  "}",
  "function genericProxyKey<T>(value: T) returns (Word) {",
  "  let table: mapping(@T => Word);",
  "  table[@T] = 73;",
  "  return table[@T];",
  "}",
  "function proxyKeyEntry(value: Word) returns (Word) {",
  "  return genericProxyKey(value);",
  "}",
  "function recurseClosure<T>(value: T, count: Word) returns (T)",
  "    where T: Witness {",
  "  let loop: function(T, Word) returns (T);",
  "  loop = lam(current: T, remaining: Word) -> T {",
  "    return remaining == 0 ? retain(current) :",
  "      loop(current, remaining - 1);",
  "  };",
  "  return loop(value, count);",
  "}",
  "function recursiveClosureEntry(value: Word) returns (Word) {",
  "  return recurseClosure(value, 3);",
  "}"
]

/-- The binder of the local `name` declared in the checked source of
`function`. -/
private def localBinder (compiled : Compiled) (function name : String) : IO Resolved.LocalId := do
  let owner ← key compiled.sourceProgram function
  match compiled.sourceProgram.functions.find? (·.declaration == owner.declaration) with
  | some checked =>
      match checked.typedBody.nodes.filterMap (fun
          | .statement { form := .letDecl binder _, .. } => if binder.name == name then some binder.id else none
          | _ => none) with
      | [binder] => pure binder
      | _ => throw (IO.userError s!"{function} lost its local {name}")
  | none => throw (IO.userError s!"{function} source missing")

def run : IO Unit := do
  let compiled ← prepare "first-class evidence/state" source ["globalValue", "globalAliasCall", "orderedAliasCall",
    "qualifiedLocalAliasCall", "genericRecursiveClosureCall", "applyStored", "capturedStateEntry",
    "coercionMapping", "coercionCapturedState", "proxyKeyEntry", "recursiveClosureEntry"]
  let targetSignature ← match compiled.sourceProgram.signatures.functions.filter (·.name == "keep") with
    | [signature] => pure signature | _ => throw (IO.userError "keep signature missing")
  let target ← match compiled.indexed.base.plan.specializations.filter (·.declaration == targetSignature.id) with
    | [target] => pure target | _ => throw (IO.userError "keep ground target missing")
  let expectedEvidence ← get "ground constrained input evidence" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment
    compiled.indexed.base.sourceProgram target.key target.assumptions)
  let (global, _) ← completed compiled "globalValue"
  match global with
  | .global actual evidence =>
    assertTrue (actual == target.key && evidence.goals == target.assumptions && evidence.length == 1 &&
      reprStr evidence == reprStr expectedEvidence) "constrained function value lost ordered evidence"
  | other => throw (IO.userError s!"constrained global value changed: {reprStr other}")
  discard <| expect compiled "globalAliasCall" [.word (word 41)] (.word (word 41))
  discard <| expect compiled "orderedAliasCall" [.word (word 43)] (.word (word 43))
  discard <| expect compiled "qualifiedLocalAliasCall" [.word (word 45)] (.word (word 45)) 37
  discard <| expect compiled "genericRecursiveClosureCall" [.word (word 47)] (.word (word 47)) 37
  discard <| expect compiled "applyStored" [global, .word (word 49)] (.word (word 49))
  let rejected ← execute compiled "applyStored" [.global target.key [], .word (word 49)]
  match rejected.observation with
  | .fault (.typeMismatch _ _) state => assertTrue state.heap.isEmpty "missing evidence was rejected after allocation"
  | other => throw (IO.userError s!"missing constrained function evidence was accepted: {reprStr other}")
  /- Closures capture by value. `mutate` writes its own copies of `total` and
  `table`: the call returns 3, while the enclosing `total` stays 1 and
  `table[7]` stays 0. -/
  let mutated ← expect compiled "capturedStateEntry" [.word (word 19)] (.word (word 4))
  assertTrue (hasWord mutated 3) "generic constrained closure call lost the write to its copy of total"
  /- The coerced closure keeps the method's `scratch` as it was when the
  closure was created, and each call starts again from it. -/
  for (input, expected, capturedExpected) in [(true, 42, 84), (false, 8, 16)] do
    let state ← expect compiled "coercionMapping" [.bool input] (.word (word expected))
    assertTrue (state.heap.any fun cell => match cell.value with
      | some (.mapping _ _ entries) => entries.any fun entry => match entry.2 with
        | .word value => value == word expected | _ => false
      | _ => false) "coercion method mapping write was not exported"
    discard <| expect compiled "coercionCapturedState" [.bool input] (.word (word capturedExpected)) 37
  discard <| expect compiled "proxyKeyEntry" [.word (word 5)] (.word (word 73))
  /- `loop` is assigned after the closure is created, so the closure's copy of
  `loop` is uninitialized and the first recursive call faults on it. -/
  let loop ← localBinder compiled "recurseClosure" "loop"
  let first ← execute compiled "recursiveClosureEntry" [.word (word 67)] 37
  let final ← get "recursive closure native resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
  match final.observation with
  | .fault (.uninitializedLocal binder) state =>
    assertTrue (binder == loop &&
        state.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
      "recursive closure self-cell faulted on another binder or left an unsafe source heap"
  | other => throw (IO.userError s!"recursive closure self-cell did not fault on its uninitialized copy: {reprStr other}")
  IO.println "Core-only constrained named/local/helper evidence and stateful coercion corpus GREEN"

end Tests.SourceCoreUnifiedEvidenceCorpus
end

section
-- leanmerge: from Solcore.Test.SourceCoreUnifiedImportBoundary
/-! The current public frontend exposes one Core execution API and pure source
boundary certificates. The conventional compiler namespace re-exports the same
definitions; backend selection and the historical source evaluator are absent. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runTrusted
#check_failure Solcore.Frontend.SourceTypedRuntime.runWithValidationFuel
#check_failure Solcore.Frontend.SourceTypedRuntime.runDeepCertifiedWithValidationFuel
#check_failure Solcore.Frontend.SourceTypedRuntime.run?
#check_failure Solcore.Frontend.SourceTypedRuntime.ExpressionResult
#check_failure Solcore.Frontend.SourceTypedRuntime.FlowOutcome
#check_failure Solcore.Frontend.SourceTypedRuntime.ResolvedPlace
#check_failure Solcore.Frontend.SourceTypedRuntime.updateResolvedValue
#check_failure Solcore.Frontend.SourceTypedRuntime.writeResolvedPlace

#check Solcore.Frontend.SourceCoreUnifiedCompilation.prepare
#check Solcore.Frontend.SourceCoreUnifiedCompilation.Compiled.run
#check Solcore.Frontend.SourceCompiler.compileChecked
#check Solcore.Frontend.SourceCompiler.compileEntry
#check Solcore.Frontend.SourceCompiler.compileStaticWord
#check Solcore.Frontend.SourceCompiler.Compiled.open
#check Solcore.Frontend.SourceCompiler.Session.run
#check Solcore.Frontend.SourceCompiler.Session.invokePacked
#check Solcore.Frontend.SourceCompiler.Session.authenticate
#check Solcore.Frontend.SourceCompiler.Checkpoint.resume
#check Solcore.Frontend.SourceCompiler.Artifact.preparePrefix
#check Solcore.Frontend.SourceCompiler.Session.snapshot
#check Solcore.Frontend.SourceCompiler.Snapshot.exportPrefix
#check Solcore.Frontend.SourceCompiler.Options.compilationFuel
#check Solcore.Frontend.SourceCompiler.RunOptions.executionFuel
#check Solcore.Frontend.SourceCompiler.Authentication.typed
#check_failure Solcore.Frontend.SourceCompiler.Backend
#check_failure Solcore.Frontend.SourceCompiler.BackendPreference
#check_failure Solcore.Frontend.SourceCompiler.BackendRejection
#check_failure Solcore.Frontend.SourceCompiler.Invocation
#check_failure Solcore.Frontend.SourceCompiler.InvocationKind
#check_failure Solcore.Frontend.SourceCompiler.ExecutionResult
#check_failure Solcore.Frontend.SourceCompiler.CompileOptions
#check_failure Solcore.Frontend.SourceCompiler.Options.backendPreference
#check_failure Solcore.Frontend.SourceCompiler.CompiledEntry
#check_failure Solcore.Frontend.SourceCompiler.CompiledEntry.runTypedWithCheckpoint
#check_failure Solcore.Frontend.SourceCompiler.CompiledEntry.TypedCheckpoint.resume
#check_failure Solcore.Frontend.SourceCompiler.TypedCheckpoint
#check_failure Solcore.Frontend.SourceCompiler.Value.cellRef
#check_failure Solcore.Frontend.SourceCompiler.Value.closure
#check_failure Solcore.Frontend.SourceCompiler.Value.global
#check_failure Solcore.Frontend.SourceCompiler.Value.builtin
#check_failure Solcore.Frontend.SourceCompiler.Session.payload
#check_failure Solcore.Frontend.SourceCompiler.Checkpoint.payload
#check_failure Solcore.Frontend.SourceCompilerSession.Compiled
#check_failure Solcore.Frontend.SourceCompiler.Legacy.preparePrefix
#check_failure Solcore.Frontend.SourceCoreExecution.Legacy.preparePrefix
#check_failure Solcore.Frontend.SourceCoreLegacyHeapImport.preparePrefix
#check Solcore.Frontend.SourceTypedRuntime.Value.HasPreparedType
#check Solcore.Frontend.SourceTypedRuntime.PreparedDeepExecution
#check Solcore.Frontend.SourceTypedRuntime.checkedLambdaNode_provenance
#check Solcore.Frontend.SourceTypedRuntime.closure_hasPlanCode_checkedLambdaNode
#check Solcore.Frontend.SourceTypedRuntime.exactSpecialization
#check Solcore.Frontend.SourceTypedRuntime.validateExecutablePlan
#check Solcore.Frontend.SourceTypedRuntime.prepareExecutablePlanEvidence

namespace Tests.SourceCoreUnifiedImportBoundary
open Solcore Solcore.Frontend

example : SourceCompiler.Compiled = SourceCoreExecution.Compiled := rfl
example : SourceCompiler.Value = SourceCoreExecution.Value := rfl
example : SourceCompiler.Handle = SourceCoreExecution.Handle := rfl
example : SourceCompiler.Artifact = SourceCoreExecution.Artifact := rfl
example (artifact : SourceCompiler.Artifact) :
    SourceCompiler.Session artifact = SourceCoreExecution.Session artifact := rfl
example (artifact : SourceCompiler.Artifact) :
    SourceCompiler.Checkpoint artifact = SourceCoreExecution.Checkpoint artifact := rfl
example (artifact : SourceCompiler.Artifact) :
    SourceCompiler.Snapshot artifact = SourceCoreExecution.Snapshot artifact := rfl
example (artifact : SourceCompiler.Artifact) :
    SourceCompiler.PrefixSnapshot artifact = SourceCoreExecution.PrefixSnapshot artifact := rfl
example : @SourceCompiler.prepare = @SourceCoreExecution.prepare := rfl
example : @SourceCompiler.compileChecked = @SourceCoreExecution.compileChecked := rfl
example : @SourceCompiler.compileEntry = @SourceCoreExecution.compileEntry := rfl
example : @SourceCompiler.compileStaticWord = @SourceCoreExecution.compileStaticWord := rfl
example : @SourceCompiler.Session.run = @SourceCoreExecution.Session.run := rfl
example : @SourceCompiler.Session.invokePacked = @SourceCoreExecution.Session.invokePacked := rfl
example : @SourceCompiler.Checkpoint.resume = @SourceCoreExecution.Checkpoint.resume := rfl
example : @SourceCompiler.Artifact.preparePrefix = @SourceCoreExecution.Artifact.preparePrefix := rfl
example : @SourceCompiler.Session.snapshot = @SourceCoreExecution.Session.snapshot := rfl
example : @SourceCompiler.Snapshot.exportPrefix = @SourceCoreExecution.Snapshot.exportPrefix := rfl
example : @SourceCompiler.Seed.declaration = @SourceCoreCompiler.Seed.declaration := rfl
example : @SourceCompiler.Seed.named = @SourceCoreCompiler.Seed.named := rfl
example (word : Core.Word) : SourceCompiler.Value.word word = SourceCorePublicValues.Value.word word := rfl
example {artifact : SourceCompiler.Artifact} (completion : SourceCompiler.Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value :=
  SourceCompiler.Completion.typed completion

end Tests.SourceCoreUnifiedImportBoundary
end

section
-- leanmerge: from Solcore.Test.SourceCoreUnifiedRuntimeCertificates
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runDeepCertifiedWithValidationFuel

/-! Actual-request certificates use public run/resume equations. Neither source
execution witnesses nor caller-supplied plan equality/BEq assumptions are used. -/
set_option autoImplicit false
namespace Tests.SourceCoreUnifiedRuntimeCertificates
open Solcore Solcore.Frontend SourceInference SourceCoreUnifiedRuntime

example {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {key : Key} {arguments : List SourceValue} {validationFuel executionFuel : Nat}
    {initial : SourceState} {result : Result prepared} {execution : Execution prepared}
    (ran : SourceCoreUnifiedRuntime.run prepared key arguments validationFuel executionFuel initial = .ok result)
    (produced : result.execution = some execution) :
    execution.root.entry.key = key ∧ execution.arguments = arguments ∧
      execution.validationFuel = validationFuel ∧ execution.initial = initial :=
  run_execution_request ran produced

example {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {key : Key} {arguments : List SourceValue} {validationFuel executionFuel : Nat}
    {initial : SourceState} {result : Result prepared} {value : SourceValue} {final : SourceState}
    {specialized : SourceSpecialization.SpecializedFunction}
    (ran : SourceCoreUnifiedRuntime.run prepared key arguments validationFuel executionFuel initial = .ok result)
    (selected : SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized)
    (done : result.observation = .done value final) :
    SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
      (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
      arguments initial value final :=
  run_done_certificate ran selected done

example {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {key : Key} {arguments : List SourceValue} {validationFuel executionFuel resumeFuel : Nat}
    {initial : SourceState} {result resumed : Result prepared} {value : SourceValue} {final : SourceState}
    {specialized : SourceSpecialization.SpecializedFunction}
    (ran : SourceCoreUnifiedRuntime.run prepared key arguments validationFuel executionFuel initial = .ok result)
    (continued : result.resume resumeFuel = .ok resumed)
    (selected : SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized)
    (done : resumed.observation = .done value final) :
    SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
      (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
      arguments initial value final :=
  run_resume_done_certificate ran continued selected done

end Tests.SourceCoreUnifiedRuntimeCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreUnifiedRuntime
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runDeepCertifiedWithValidationFuel
#check_failure Solcore.Frontend.SourceCoreUnifiedRuntime.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreUnifiedRuntime.Execution.mk
#check_failure Solcore.Frontend.SourceCoreUnifiedRuntime.Result.mk

/-! Cached public source observations use Core only. Pure old validators retain
preflight/final rejection priority. The opaque heap can contain authentic cyclic
source closures, but none is imported into the native world or public arguments.
Partial observations sweep administrative allocation phases and resume native
checkpoints; numeric source/Core fuel costs are intentionally not equated. -/
set_option autoImplicit false
namespace Tests.SourceCoreUnifiedRuntime
open Solcore Solcore.Frontend SourceInference
open SourceCoreUnifiedRuntime
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"unified fixture missing {name}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "enum Holder { Hold(F) }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function consume(f: F, value: Word) returns (Word) { return f(value); }",
    "function global() returns (F) { return inc; }",
    "function builtin(f: function(Word) returns (integer), value: Word) returns (integer) { return f(value); }",
    "function tuple(value: (Word, F)) returns (Word) { match (value) { case (n, f) { return f(n); } } }",
    "function nominal(value: Holder, n: Word) returns (Word) { match (value) { case .Hold(f) { return f(n); } } }",
    "function mapping(values: mapping(Word => F), n: Word) returns (Word) { return values[7](n); }",
    "function wide(values: mapping(Word => Word)) returns (mapping(Word => Word)) { return values; }",
    "function missing(values: mapping(Word => F)) returns (F) { return values[999]; }",
    "function closures(seed: Word) returns (F, F) { let f = lam(item) { seed += 1; return seed; }; return (f, f); }",
    "function recursive() returns (F) { let f: F; f = lam(n: Word) -> Word { return n == 0 ? 0 : f(n - 1); }; return f; }",
    "function absent(seed: Word) returns (Word) { seed += 1; let absent: Word; return absent; }",
    "function partial(seed: Word) returns (Word) { let f: F = lam(item: Word) -> Word { seed += item; return seed; }; let copied: F = f; return copied(1); }",
    "function spin() returns (Word) { while (true) {} return 0; }"
  ]}] }
private def initialPrefix {checked : Checked} (native : Program checked) (recursive : Key) : IO SourceState := do
  let function ← get "prefix specialization" (SourceCompilationPlan.exactSpecialization native.base.validationPlan recursive)
  let node ← match function.function.typedBody.nodes.findSome? (fun node => match node with
      | .expression expression => match expression.form with
        | .lambda parameters result body => some (parameters, result, body)
        | _ => none
      | _ => none) with
    | some node => pure node | none => throw (IO.userError "prefix lambda metadata missing")
  let binder ← match (SourceCoreDataPlaces.declaredBinders function.function.typedBody).find? (·.name == "f") with
    | some binder => pure binder | none => throw (IO.userError "prefix recursive binder missing")
  let value : SourceValue := .closure node.1 node.2.1 node.2.2 function.function.typedBody recursive [(binder.id, ⟨0⟩)] []
  pure ⟨[⟨.function .word .word, some value⟩, ⟨.error, none⟩, ⟨.comptime .word, some (.word (w 99))⟩]⟩

private def expectWord {checked : Checked} {native : Program checked} (prepared : Prepared native)
    (owner : Key) (arguments : List SourceValue) (initial : SourceState) (expected : Nat)
    (budget : Nat := 100000) : IO Unit := do
  let first ← get "unified word start" (Solcore.Frontend.SourceCoreUnifiedRuntime.run prepared owner arguments 500 budget initial)
  let completed ← get "unified word resume" (first.resume 100000)
  match completed.observation with
  | .done (.word value) state =>
    assertTrue (value == w expected) "unified Core/source word projection changed"
    assertTrue (reprStr (state.heap.take initial.heap.length) == reprStr initial.heap) "unified runner changed opaque initial prefix"
  | other => throw (IO.userError s!"unified word did not complete: {reprStr other}")

private def expectRejected {checked : Checked} {native : Program checked} (prepared : Prepared native)
    (owner : Key) (arguments : List SourceValue) (validationFuel : Nat) (initial : SourceState) (error : RuntimeError) : IO Unit := do
  let result ← get "unified preflight" (Solcore.Frontend.SourceCoreUnifiedRuntime.run prepared owner arguments validationFuel 100000 initial)
  match result.observation with
  | .fault actual state =>
    assertTrue (actual == error) s!"unified validation priority changed: {reprStr actual}"
    assertTrue (reprStr state == reprStr initial && result.execution.isNone) "preflight fault allocated or imported heap cells"
    let resumed ← get "rejected resume" (result.resume 100000)
    assertTrue (reprStr resumed.observation == reprStr result.observation) "rejected call became executable during resume"
  | other => throw (IO.userError s!"expected preflight rejection: {reprStr other}")

example {checked : Checked} {native : Program checked} {prepared : Prepared native}
    (execution : Execution prepared) {value : SourceValue} {state : SourceState}
    (done : execution.finalize value state = .done value state) :
    SourceTypedRuntime.PreparedDeepExecution native.base.sourceProgram native.base.validationPlan
      execution.root.argumentTypes execution.root.expected execution.arguments execution.initial value state :=
  execution.finalize_done_certificate done

example {checked : Checked} {native : Program checked} {prepared : Prepared native}
    (result : Result prepared) {value : SourceValue} {state : SourceState}
    (done : result.observation = .done value state) :
    ∃ execution, result.execution = some execution ∧
      SourceTypedRuntime.PreparedDeepExecution native.base.sourceProgram native.base.validationPlan
        execution.root.argumentTypes execution.root.expected execution.arguments execution.initial value state :=
  result.done_certificate done

private def actualFault {checked : Checked} {native : Program checked} (prepared : Prepared native)
    (owner : Key) (arguments : List SourceValue) (initial : SourceState) (check : RuntimeError → SourceState → Bool) : IO Unit := do
  let result ← get "unified language fault" (Solcore.Frontend.SourceCoreUnifiedRuntime.run prepared owner arguments 500 100000 initial)
  match result.observation with
  | .fault error state => assertTrue (check error state) s!"unified source fault changed: {reprStr error}"
  | other => throw (IO.userError s!"expected genuine source language fault: {reprStr other}")

def run : IO Unit := do
  let source ← get "unified checked source" (checkProgram workspace)
  let names := ["inc", "consume", "global", "builtin", "tuple", "nominal", "mapping", "wide", "missing", "closures", "recursive", "absent", "partial", "spin"]
  let keys ← names.mapM (key source)
  let plan ← match SourceSpecializationWorklist.run source (keys.map (fun key => ⟨key.declaration, []⟩)) 500 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"unified plan did not complete: {reprStr other}")
  let automatic ← get "unified compatible artifact" (SourceCoreCompatibleFunctions.prepare source plan 700)
  let native ← get "unified indexed pipeline" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 700)
  let prepared ← get "unified cached observations" (prepare native)
  let initial ← initialPrefix native (← key source "recursive")
  assertTrue (initial.isDeeplySafe 500 source.signatures native.base.plan) "authentic cyclic prefix was rejected"
  let consume ← key source "consume"
  let inc ← key source "inc"
  for fuel in [0, 41, 100000] do
    expectWord prepared consume [.global inc [], .word (w 8)] initial 9 fuel
    expectWord prepared (← key source "tuple") [.product (.word (w 8)) (.global inc [])] initial 9 fuel
    expectWord prepared (← key source "mapping") [.mapping .word (.comptime (.function .word .word)) [(.word (w 7), .global inc [])], .word (w 8)] initial 9 fuel
  let data ← match source.signatures.dataTypes.filter (·.name == "Holder") with
    | [data] => pure data | _ => throw (IO.userError "Holder signature missing")
  let constructor ← match data.constructors with
    | [constructor] => pure constructor | _ => throw (IO.userError "Hold signature missing")
  let ctor : DataConstructorInstantiation := {
    constructor := constructor.id, parameterSubstitution := [],
    payloadTypes := constructor.payloadTypes, resultType := .nominal data.id [] }

  expectWord prepared (← key source "nominal") [.constructed ctor [.global inc []], .word (w 8)] initial 9
  let builtin ← get "unified builtin" (Solcore.Frontend.SourceCoreUnifiedRuntime.run prepared (← key source "builtin") [.builtin .wordToInteger, .word (w 9)] 500 100000 initial)
  match builtin.observation with
  | .done (.integer 9) _ => pure () | other => throw (IO.userError s!"unified builtin changed: {reprStr other}")
  let named ← get "unified global output" (Solcore.Frontend.SourceCoreUnifiedRuntime.run prepared (← key source "global") [] 500 100000 initial)
  match named.observation with
  | .done (.global actual []) _ => assertTrue (actual == inc) "unified named identity/evidence changed"
  | other => throw (IO.userError s!"unified named output changed: {reprStr other}")
  let wideInput : SourceValue := .mapping (.comptime .word) (.comptime .word)
    ((List.range 1025).map fun n => (.word (w (n % 7)), .word (w n)))
  let wide ← get "unified wide raw mapping" (Solcore.Frontend.SourceCoreUnifiedRuntime.run prepared (← key source "wide") [wideInput] 3 100000 initial)
  match wide.observation with
  | .done (.mapping rawKey rawValue entries) _ =>
    assertTrue (rawKey == .comptime .word && rawValue == .comptime .word && entries.length == 1025) "unified mapping order/raw metadata or width changed"
  | other => throw (IO.userError s!"unified wide mapping failed: {reprStr other}")
  let bad : SourceState := ⟨[⟨.word, some (.bool true)⟩]⟩
  expectRejected prepared consume [.bool true, .word (w 1)] 500 bad (.typeMismatch (.function .word .word) (some .bool))
  expectRejected prepared consume [.global inc [], .word (w 1)] 0 bad (.inputValidationFuelExhausted (.function .word .word) 0)
  expectRejected prepared consume [.global inc [], .word (w 1)] 500 bad .deepSafetyInitialStateRejected
  match initial.heap.head?.bind (·.value) with
  | some closure => expectRejected prepared consume [closure, .word (w 1)] 500 initial (.typeMismatch (.function .word .word) (some (.function .word .word)))
  | _ => throw (IO.userError "cyclic prefix closure missing")
  actualFault prepared (← key source "missing") [.mapping .word (.comptime (.function .word .word)) []] initial
    (fun error _ => error == .typeMismatch (.comptime (.function .word .word)) none)
  actualFault prepared (← key source "absent") [.word (w 3)] initial
    (fun error state => match error with
      | .uninitializedLocal _ => state.heap.drop initial.heap.length |>.any (fun cell => match cell.value with | some (.word value) => value == w 4 | _ => false)
      | _ => false)
  let captured ← get "unified instantiated outputs" (Solcore.Frontend.SourceCoreUnifiedRuntime.run prepared (← key source "closures") [.word (w 3)] 500 100000 initial)
  match captured.observation with
  | .done (.product (.instantiated leftSub leftReq (.closure _ _ _ _ _ leftEnv _))
      (.instantiated rightSub rightReq (.closure _ _ _ _ _ rightEnv _))) _ =>
    assertTrue (!leftSub.isEmpty && !rightSub.isEmpty && leftReq.isEmpty && rightReq.isEmpty && leftEnv == rightEnv)
      "unified generalized reads collapsed their wrappers or shared captures"
    assertTrue (leftEnv.all (fun binding => initial.heap.length ≤ binding.2.index)) "unified capture referenced inert prefix"
  | other => throw (IO.userError s!"unified generalized output rejected: {reprStr other}")
  let partialKey ← key source "partial"
  let partialPlan ← match SourceSpecializationWorklist.run source [⟨partialKey.declaration, []⟩] 500 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"partial plan incomplete: {reprStr other}")
  let partialAutomatic ← get "partial compatible cache" (SourceCoreCompatibleFunctions.prepare source partialPlan 700)
  let partialNative ← get "partial indexed cache" (SourceCoreCallableIndexedPrograms.prepare partialAutomatic.prepared 700)
  let partialPrepared ← get "partial observations cache" (prepare partialNative)
  let partialInitial : SourceState := ⟨[⟨.error, none⟩, ⟨.word, some (.word (w 99))⟩]⟩
  let mut reachedPartialAllocation := false
  let mut reachedPartialSuccess := false
  for fuel in List.range 2000 do
    if !reachedPartialSuccess then
      let result ← get s!"partial Core phase {fuel}" (Solcore.Frontend.SourceCoreUnifiedRuntime.run partialPrepared partialKey [.word (w 3)] 500 fuel partialInitial)
      match result.observation with
      | .outOfFuel state =>
        assertTrue (reprStr (state.heap.take partialInitial.heap.length) == reprStr partialInitial.heap) "partial heap changed prefix"
        reachedPartialAllocation := reachedPartialAllocation || partialInitial.heap.length < state.heap.length
      | .done (.word value) _ =>
        assertTrue (value == w 4) "partial success changed result"
        reachedPartialSuccess := true
      | other => throw (IO.userError s!"partial administrative phase failed: {reprStr other}")
  assertTrue reachedPartialAllocation "fuel sweep did not reach source allocation phases"
  assertTrue reachedPartialSuccess "fuel sweep did not reach completed closure invocation"
  let spin ← get "unified nontermination" (Solcore.Frontend.SourceCoreUnifiedRuntime.run prepared (← key source "spin") [] 500 900 initial)
  let spin ← get "unified native resume" (spin.resume 900)
  match spin.observation with
  | .outOfFuel state => assertTrue (initial.heap.length ≤ state.heap.length) "spin lost source prefix"
  | other => throw (IO.userError s!"native resume falsely completed spin: {reprStr other}")
  IO.println "unified Core-only preflight, old diagnostics/raw values/heaps, function inputs/outputs and checkpoint resume GREEN"

end Tests.SourceCoreUnifiedRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreUnifiedSourceBoundaryObservations
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runDeepCertifiedWithValidationFuel

/-! Concrete observations of the existing public source-value boundary.
These checked source fixtures exercise the cached Core compatibility
adapter with the same accepted raw metadata and rejection priorities.
The initial prefix is validated and inert;
public captured-closure arguments remain rejected. -/

set_option autoImplicit false

namespace Tests.SourceCoreUnifiedSourceBoundaryObservations

open Solcore Solcore.Frontend SourceInference
open SourceCoreUnifiedCompilation

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function proxyEcho(value: @Word) returns (@Word) { return value; }",
    "function proxyLookup(table: mapping(@Word => Word)) returns (Word) { return table[@Word]; }",
    "function proxyMissing(table: mapping(Word => @Word)) returns (@Word) { return table[9]; }",
    "function mappingEcho(value: mapping(Word => Word)) returns (mapping(Word => Word)) { return value; }",
    "function boxEcho(value: Box<Word>) returns (Box<Word>) { return value; }",
    "function boxMatch(value: Box<Word>) returns (Word) { match (value) { case .Box(inner) { return inner; } default { return 99; } } }",
    "function scalar(value: Word) returns (Word) { return value; }",
    "function returnClosure() returns (function() returns (Word)) { let captured: Word = 7; return lam() -> Word { return captured; }; }",
    "function unusedPoly(captured: Word) returns (Word) { let f = lam(value) { return (value, captured); }; return captured; }",
    "function apply(f: function(Word) returns (Word), value: Word) returns (Word) { let retained: function(Word) returns (Word) = scalar; return f(value); }",
    "function applyUnselected(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
    "function invokeUnit(f: function() returns (Word)) returns (Word) { return f(); }",
    "function applyInteger(f: function(Word) returns (integer), value: Word) returns (integer) { return f(value); }"
  ] }] }

private def compile (program : CheckedProgram) (name : String) : IO Compiled := do
  let function ← match program.signatures.functions.filter (·.name == name) with
    | [function] => pure function
    | _ => throw (IO.userError s!"source boundary fixture missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program [⟨function.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"source boundary plan incomplete: {reprStr other}")
  match prepare program plan 700 with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError s!"source boundary fixture rejected: {reprStr error}")

private def execute (compiled : Compiled) (arguments : List SourceTypedRuntime.Value)
    (state : SourceTypedRuntime.RuntimeState := {}) : Except String (Result compiled) := do
  let key ← match compiled.keys with
    | [key] => pure key
    | _ => throw "source boundary fixture must have exactly one cached root"
  (compiled.run key arguments 128 100000 state).mapError reprStr

private def completed (compiled : Compiled) (arguments : List SourceTypedRuntime.Value)
    (state : SourceTypedRuntime.RuntimeState := {}) : IO (SourceTypedRuntime.Value × SourceTypedRuntime.RuntimeState) :=
  match execute compiled arguments state with
  | .ok result => match result.observation with
    | .done value state => pure (value, state)
    | other => throw (IO.userError s!"source boundary observation failed: {reprStr other}")
  | .error error => throw (IO.userError s!"source boundary execution failed: {reprStr error}")

private def wordResult (compiled : Compiled) (arguments : List SourceTypedRuntime.Value) (expected : Nat)
    (state : SourceTypedRuntime.RuntimeState := {}) : IO SourceTypedRuntime.RuntimeState := do
  let (value, state) ← completed compiled arguments state
  match value with
  | .word actual => assertTrue (actual == word expected) "source boundary Word result changed"; pure state
  | _ => throw (IO.userError "source boundary result was not Word")

example (type : TypeSystem.Ty) : SourceCoreRawMetadata.runtimeType type = SourceTypedRuntime.runtimeType type := by
  exact SourceCoreRawMetadata.runtimeType_sourceValues type

example (signatures : ProgramSignatures) (instantiation : DataConstructorInstantiation) :
    SourceCoreRawMetadata.constructorAuthentic signatures instantiation =
      SourceTypedRuntime.validConstructorInstantiation signatures instantiation := rfl

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"source boundary checking failed: {reprStr error}")
  let proxy ← compile program "proxyEcho"
  match (← completed proxy [.proxy (.comptime .word)]).1 with
  | .proxy (.comptime .word) => pure ()
  | _ => throw (IO.userError "accepted proxy metadata was erased")
  let lookup ← compile program "proxyLookup"
  let rawProxyMap : SourceTypedRuntime.Value := .mapping (.proxy .word) .word
    [(.proxy (.comptime .word), .word (word 7))]
  discard <| wordResult lookup [rawProxyMap] 0
  discard <| wordResult lookup [.mapping (.proxy .word) .word [(.proxy .word, .word (word 7))]] 7
  let missing ← compile program "proxyMissing"
  match (← completed missing [.mapping .word (.proxy (.comptime .word)) []]).1 with
  | .proxy (.comptime .word) => pure ()
  | _ => throw (IO.userError "mapping default ignored the actual raw value header")
  let mapping ← compile program "mappingEcho"
  let rawMap : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(.word (word 3), .word (word 7)), (.word (word 3), .word (word 9))]
  assertTrue (reprStr (← completed mapping [rawMap]).1 == reprStr rawMap)
    "mapping raw header or duplicate entry order changed"
  let box ← match program.signatures.dataTypes.filter (·.name == "Box") with
    | [signature] => pure signature
    | _ => throw (IO.userError "source boundary Box signature missing")
  let (parameter, constructor) ← match box.parameters, box.constructors with
    | [parameter], [constructor] => pure (parameter, constructor)
    | _, _ => throw (IO.userError "source boundary Box signature malformed")
  let stagedMetadata : DataConstructorInstantiation := {
    constructor := constructor.id, parameterSubstitution := [(parameter, .comptime .word)]
    payloadTypes := [.comptime .word], resultType := .nominal box.id [.comptime .word] }
  let ordinaryMetadata : DataConstructorInstantiation := {
    constructor := constructor.id, parameterSubstitution := [(parameter, .word)]
    payloadTypes := [.word], resultType := .nominal box.id [.word] }
  let echo ← compile program "boxEcho"
  match (← completed echo [.constructed stagedMetadata [.word (word 7)]]).1 with
  | .constructed actual _ => assertTrue (actual == stagedMetadata) "authenticated nominal metadata changed"
  | _ => throw (IO.userError "source boundary nominal result changed shape")
  let matchBox ← compile program "boxMatch"
  let noMatch ← wordResult matchBox [.constructed stagedMetadata [.word (word 7)]] 99
  let matched ← wordResult matchBox [.constructed ordinaryMetadata [.word (word 7)]] 7
  assertTrue (noMatch.heap.length == 2 && matched.heap.length == 3)
    "hidden scrutinee or successful pattern binder source allocation changed"
  let factory ← compile program "returnClosure"
  let (closure, initial) ← completed factory []
  let withClosure : SourceTypedRuntime.RuntimeState := {
    heap := initial.heap ++ [{type := .function .unit .word, value := some closure}] }
  let (_, reused) ← completed factory [] withClosure
  /- Each run allocates `captured` and the returned closure's snapshot copy of
  it, after the given prefix. -/
  assertTrue (reprStr (reused.heap.take withClosure.heap.length) == reprStr withClosure.heap && reused.heap.length == 5)
    "accepted existing closure heap prefix changed"
  /- Old code validation checks capture readability, not lexical type alignment.
  This prefix cannot be reached by any accepted public function input. -/
  let readablePrefix : SourceTypedRuntime.RuntimeState := { heap := [
    {type := .bool, value := some (.bool true)},
    {type := .function .unit .word, value := some closure}] }
  let (_, reusedReadable) ← completed factory [] readablePrefix
  assertTrue (reprStr (reusedReadable.heap.take 2) == reprStr readablePrefix.heap)
    "accepted inert readable closure prefix changed"
  let scalar ← compile program "scalar"
  let openPrefix : SourceTypedRuntime.RuntimeState := { heap := [
    {type := .error, value := none}, {type := .word, value := some (.word (word 99))}] }
  let scalarState ← wordResult scalar [.word (word 8)] 8 openPrefix
  assertTrue (reprStr (scalarState.heap.take 2) == reprStr openPrefix.heap && scalarState.heap.length == 3)
    "uninitialized open source prefix was rejected or changed"
  let unused ← compile program "unusedPoly"
  let unusedState ← wordResult unused [.word (word 8)] 8
  /- The generalized `let` copies `captured` before its principal, which
  captures the copy. -/
  match unusedState.heap with
  | [_, _, {type := .function _ _, value := some (.closure _ _ _ _ _ captures _)}] =>
      assertTrue (captures.map (fun capture => capture.2.index) == [1])
        "unused principal closure did not capture its snapshot copy"
  | _ => throw (IO.userError "unused generalized source binding did not retain its principal closure heap cell")
  let key : SourceSpecialization.SpecializationKey ← match program.signatures.functions.filter (·.name == "scalar") with
    | [signature] => pure ⟨signature.id, []⟩
    | _ => throw (IO.userError "source boundary selected global key missing")
  let apply ← compile program "apply"
  let globalState ← wordResult apply [.global key [], .word (word 8)] 8
  assertTrue (globalState.heap.length == 4) "global input/callee parameter allocation changed"
  let unselected ← compile program "applyUnselected"
  match execute unselected [.global key [], .word (word 8)] with
  | .ok result => match result.observation with
    | .fault (.typeMismatch _ _) _ => pure ()
    | _ => throw (IO.userError "a global outside the selected plan was accepted")
  | _ => throw (IO.userError "unselected global failed outside source validation")
  let invoke ← compile program "invokeUnit"
  match execute invoke [closure] with
  | .ok result => match result.observation with
    | .fault (.typeMismatch _ _) _ => pure ()
    | _ => throw (IO.userError "public raw captured closure argument was accepted")
  | _ => throw (IO.userError "raw closure failed outside source validation")
  let builtin ← compile program "applyInteger"
  match (← completed builtin [.builtin .wordToInteger, .word (word 8)]).1 with
  | .integer 8 => pure ()
  | _ => throw (IO.userError "public builtin function input changed")
  let malformedPrefix : SourceTypedRuntime.RuntimeState := {
    heap := [{type := .word, value := some (.bool true)}] }
  match execute scalar [.bool true] malformedPrefix with
  | .ok result => match result.observation with
    | .fault (.typeMismatch .word (some .bool)) _ => pure ()
    | _ => throw (IO.userError "public input failure did not precede initial heap rejection")
  | _ => throw (IO.userError "input failure escaped source validation")
  IO.println "Core-only public raw metadata, function inputs and inert source heap observations GREEN"

end Tests.SourceCoreUnifiedSourceBoundaryObservations
end

section
-- leanmerge: from Solcore.Test.SourceCoreUnifiedCompilation
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreUnifiedCompilation.Compiled.mk

/-! Checked source programs exercise the prepared public Core adapter through
its complete result and source heap export, including genuine suspension and
resumption. Expected results come from the source fixture's visible behavior. -/
set_option autoImplicit false
namespace Tests.SourceCoreUnifiedCompilation
open Solcore Solcore.Frontend SourceInference
abbrev Compiled := Solcore.Frontend.SourceCoreUnifiedCompilation.Compiled
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Key := SourceSpecialization.SpecializationKey

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "trait Marker<T> {}", "impl Marker<mapping(Word => Word)> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function local(table: mapping(Word => Word)) returns (mapping(Word => Word)) { let f = lam(item) { return keep(item); }; return f(table); }",
    "function lazy() returns (mapping(Word => Word)) { let table: mapping(Word => Word); table[1] = 7; return table; }",
    "function choose(value: Box<Word>) returns (Word) { match (value) { case .Box(bound) { return bound; } default { return 99; } } }",
    "function capture(start: Word) returns (Word) { let value = start; let f = lam(step: Word) { value += step; return value; }; f(3); return f(4); }",
    "function recursive(n: Word) returns (Word) { let f: function(Word) returns (Word); f = lam(left: Word) { return left == 0 ? 0 : f(left - 1) + 1; }; return f(n); }",
    "function unused() returns (Word) { let unused = lam(item) { return item; }; return 7; }",
    "function tuple(value: (Word, Bool)) returns (Word) { match (value) { case ((left, flag)) { return flag ? left : 99; } default { return 77; } } }",
    "function looping(limit: Word) returns (Word) { let total = 0; for (let i = 0; i < limit; i += 1) { total += i; } return total; }",
    "function absent() returns (Word) { let absent: Word; return absent; }",
    "function getLocal(start: Word) returns (function(Word) returns (Word)) { let value = start; let f = lam(item) { value += 1; return item; }; return f; }",
    "function useReturned(start: Word) returns (Word) { let f = getLocal(start); return f(9); }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, Word> { function coerce(value: Bool) returns (Word) { let table: mapping(Word => Word); table[0] = value ? 40 : 6; table[0] += 2; return table[0]; } }",
    "function converted(value: Bool) returns (Word) { return value; }",
    "function integerValue(value: integer) returns (integer) { return value + 1; }",
    "function failAfterWrite() returns (Word) { let captured: Word = 1; let fail = lam() -> Word { captured += 2; let missing: Word; return missing; }; return fail(); }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"unified fixture missing {name}")

private def initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, none⟩]}

private def checkFinal (compiled : Compiled) (owner : Key) (arguments : List SourceValue)
    (accept : SourceTypedRuntime.RunResult → IO Unit) : IO Unit := do
  for spent in [0, 37, 150000] do
    let first ← get "unified Core run" (compiled.run owner arguments 500 spent initial)
    assertTrue first.execution.isSome "valid unified invocation omitted its native receipt"
    if spent == 0 then
      match first.observation with
      | .outOfFuel state => assertTrue (reprStr state == reprStr initial) "zero fuel changed initial source prefix"
      | result => throw (IO.userError s!"zero fuel did not suspend: {reprStr result}")
    let final ← get "unified Core resume" (Solcore.Frontend.SourceCoreUnifiedCompilation.Result.resume first 150000)
    accept final.observation

private def check (compiled : Compiled) (owner : Key) (arguments : List SourceValue)
    (expected : SourceValue) : IO Unit :=
  checkFinal compiled owner arguments fun
    | .done actual state => do
      assertTrue (reprStr actual == reprStr expected) s!"unified result changed: {reprStr actual}"
      assertTrue (reprStr (state.heap.take initial.heap.length) == reprStr initial.heap)
        "unified execution changed the inert source prefix"
    | result => throw (IO.userError s!"unified execution did not complete: {reprStr result}")

/-- The binder of the local `name` declared in the checked source of
`function`. -/
private def localBinder (program : CheckedProgram) (function name : String) : IO Resolved.LocalId := do
  let owner ← key program function
  match program.functions.find? (·.declaration == owner.declaration) with
  | some checked =>
      match checked.typedBody.nodes.filterMap (fun
          | .statement { form := .letDecl binder _, .. } => if binder.name == name then some binder.id else none
          | _ => none) with
      | [binder] => pure binder
      | _ => throw (IO.userError s!"unified fixture {function} lost its local {name}")
  | none => throw (IO.userError s!"unified fixture {function} source missing")

example (compiled : Compiled) :
    SourceCoreCompatibleFunctions.prepare compiled.sourceProgram compiled.validationPlan compiled.compilationFuel =
      .ok compiled.compatible := compiled.compatiblePrepared
example (compiled : Compiled) : SourceCoreUnifiedRuntime.prepare compiled.indexed = .ok compiled.runtime :=
  compiled.runtimePrepared

def run : IO Unit := do
  let program ← get "unified checking" (checkProgram workspace)
  let names := ["local", "lazy", "choose", "capture", "recursive", "unused", "tuple", "looping",
    "absent", "getLocal", "useReturned", "converted", "integerValue", "failAfterWrite"]
  let roots ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (roots.map fun root => ⟨root.declaration, []⟩) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"unified worklist failed: {reprStr other}")
  let compiled ← get "unified preparation" (Solcore.Frontend.SourceCoreUnifiedCompilation.prepare program plan 500)
  assertTrue (compiled.keys == roots) "unified factory changed root order"
  let mapping : SourceValue := .mapping .word .word [(.word (w 1), .word (w 9))]
  check compiled (← key program "local") [mapping] mapping
  check compiled (← key program "lazy") [] (.mapping .word .word [(.word (w 1), .word (w 7))])
  /- Closures capture by value: each call of `f` starts again from the
  captured `value`, so `f(4)` returns 14. -/
  check compiled (← key program "capture") [.word (w 10)] (.word (w 14))
  /- `f` is assigned after the closure is created, so the closure's copy of
  `f` is uninitialized and its first recursive read faults. -/
  let recursiveSelf ← localBinder program "recursive" "f"
  checkFinal compiled (← key program "recursive") [.word (w 4)] fun
    | .fault (.uninitializedLocal binder) state =>
      assertTrue (binder == recursiveSelf && reprStr (state.heap.take initial.heap.length) == reprStr initial.heap)
        "recursive closure did not fault on its uninitialized copy of its self cell"
    | result => throw (IO.userError s!"recursive self-cell read changed: {reprStr result}")
  check compiled (← key program "unused") [] (.word (w 7))
  check compiled (← key program "tuple") [.product (.word (w 13)) (.bool true)] (.word (w 13))
  check compiled (← key program "looping") [.word (w 4)] (.word (w 6))
  check compiled (← key program "useReturned") [.word (w 4)] (.word (w 9))
  check compiled (← key program "converted") [.bool true] (.word (w 42))
  check compiled (← key program "converted") [.bool false] (.word (w 8))
  check compiled (← key program "integerValue") [.integer (-3)] (.integer (-2))
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "unified Box missing")
  let constructor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "unified constructor missing")
  let instantiation : DataConstructorInstantiation := ⟨constructor.id, box.parameters.zip [.word], [.word], .nominal box.id [.word]⟩
  check compiled (← key program "choose") [.constructed instantiation [.word (w 7)]] (.word (w 7))
  for name in ["absent", "failAfterWrite"] do
    let result ← get "unified language failure" (compiled.run (← key program name) [] 500 150000 initial)
    match result.observation with
    | .fault (.uninitializedLocal _) state =>
      assertTrue (initial.heap.length < state.heap.length) "language failure lost its source allocations"
      if name == "failAfterWrite" then
        assertTrue (state.heap.any fun cell => match cell.value with
          | some (.word value) => value == w 3 | _ => false) "language failure lost the closure call's write to its copy"
    | other => throw (IO.userError s!"unified language failure changed: {reprStr other}")
  IO.println "cached unified Core artifact, complete source observations and resumptions GREEN"

end Tests.SourceCoreUnifiedCompilation
end

section
-- leanmerge: from Solcore.Test.SourceCoreUnifiedStagingCorpus
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
    /- Closures capture by value: `bump` writes its call's copies of `total`
    and `table`. -/
    let effects ← expect compiled "markedEffects" [.word (word 9)] (.word (word 12)) spent
    assertTrue (hasWord effects 12 && effects.heap.any (fun cell => match cell.value with
      | some (.mapping _ _ entries) => entries.any (fun entry => match entry with
        | (.word key, .word value) => key == word 0 && value == word 12
        | _ => false)
      | _ => false)) "marked call lost the writes and mapping update in its captured copies"
    for (name, expected) in [("markedClosureClosed", 21), ("markedGlobalClosed", 22),
        ("markedResultIndirectStaged", 24)] do
      discard <| expect compiled name [] (.word (word expected)) spent
  for name in ["markedClosureRuntime", "markedGlobalRuntime", "markedResultIndirectBlocked"] do
    let owner ← key compiled.sourceProgram name
    let occurrence ← indirectOccurrence compiled name
    let arguments := if name == "markedResultIndirectBlocked" then [] else [.word (word 21)]
    -- The closure of `markedClosureRuntime` also holds its snapshot copy of `value`.
    let argumentCells := if name == "markedClosureRuntime" then 3 else 2
    for spent in [0, 43, 300000] do
      let first ← execute compiled name arguments spent
      let final ← get "staging guard native resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
      match final.observation with
      | .fault (.comptimeArgumentStageMismatch caller id 0 _ .runtime) state =>
        assertTrue (name != "markedResultIndirectBlocked" && caller == owner && id == occurrence &&
          state.heap.length == argumentCells && hasWord state 21)
          "marked argument guard lost its source site or allocated the guarded parameter"
      | .fault (.comptimeResultStageMismatch caller id _ .deferred) state =>
        assertTrue (name == "markedResultIndirectBlocked" && caller == owner && id == occurrence &&
          state.heap.length == 1 && !hasWord state 23)
          "marked result guard lost its source site or allocated the guarded parameter"
      | other => throw (IO.userError s!"{name} guard changed: {reprStr other}")
  IO.println "Core-only checked staging metadata, captured effects, exact guard sites and resume corpus GREEN"

end Tests.SourceCoreUnifiedStagingCorpus
end
