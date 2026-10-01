import Solcore.Frontend.SourceCoreUnifiedRuntime
import Solcore.Frontend.ProgramChecking

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
