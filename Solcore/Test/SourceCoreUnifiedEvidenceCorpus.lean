import Solcore.Test.SourceCoreUnifiedCorpusSupport

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
