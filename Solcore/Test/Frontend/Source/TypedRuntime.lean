import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.Test.Frontend.Source.CompilerFeatureSupport

/-!
# Typed runtime tests

Source-compatible Core execution through the typed runtime: first-class evidence, operators and state
interactions.
-/

section
-- leanmerge: from Solcore.Test.SourceTypedRuntime
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runTrusted

/-!
End-to-end regressions for source-compatible Core execution.

Executable fixtures cross raw-workspace checking and finite specialization,
then cache the actual Core artifact. Rewritten metadata is tested through pure
plan validation; retained implicit-tail IR has a separate Core fragment test.
-/

set_option autoImplicit false

namespace Tests.SourceTypedRuntime

open Solcore Solcore.Frontend Solcore.TypeSystem

namespace Runtime

open Solcore.Frontend.SourceTypedRuntime

/-- A forged occurrence view of a non-callable value cannot claim executable
plan provenance merely because its principal value has trivial provenance. -/
private theorem nonClosureInstantiationHasNoPlanCode
    (plan : SourceSpecializationWorklist.Plan)
    (substitution : TypeSystem.Substitution) :
    ¬ (Value.instantiated substitution [] .unit).HasPlanCode plan := by
  intro code
  exact (Value.HasPlanCode.instantiated_origin code).2

/-- The public constructor theorem for an occurrence view also exposes the
exact substituted-source provenance required by indirect execution. -/
private theorem closureInstantiationExposesSubstitutedOrigin
    (plan : SourceSpecializationWorklist.Plan)
    (parameters : List SourceInference.TypedBinder) (resultType : Ty)
    (body : List SourceInference.StatementId)
    (source : SourceInference.TypedSource)
    (owner : SourceSpecialization.SpecializationKey)
    (captured : SourceTypedRuntime.Environment)
    (evidence : SourceTypedRuntime.RuntimeEvidenceEnvironment)
    (substitution : TypeSystem.Substitution)
    (code : Value.HasPlanCode
      (.closure parameters resultType body source owner captured evidence) plan) :
    Value.HasInstantiatedPlanCode
      (.closure parameters resultType body source owner captured evidence)
      substitution plan := by
  exact (Value.HasPlanCode.instantiated_origin
    (Value.HasPlanCode.instantiated substitution code)).2

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"typed-runtime fixture failed checking: {reprStr errors}")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature :=
  match program.signatures.functions.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one signature named `{name}`, found {signatures.length}")

private structure ValidationFixture where
  program : CheckedProgram
  plan : SourceSpecializationWorklist.Plan
  key : SourceSpecialization.SpecializationKey

private structure Prepared extends ValidationFixture where
  compiled : SourceCoreUnifiedCompilation.Compiled

private def prepareNamed (program : CheckedProgram) (name : String)
    (budget : Nat := 32) : IO Prepared := do
  let signature ← signatureNamed program name
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] budget with
  | .ok (.complete plan) =>
      match plan.seedKeys with
      | [key] => do
          let compiled ← SourceCoreUnifiedCorpusSupport.preparePlan name program plan key
          pure { program, plan, key, compiled }
      | keys => throw (IO.userError
          s!"`{name}` retained {keys.length} seed keys")
  | .ok outcome => throw (IO.userError
      s!"`{name}` specialization did not complete: {reprStr outcome}")
  | .error error => throw (IO.userError
      s!"`{name}` specialization failed: {reprStr error}")

private def runPrepared (prepared : Prepared)
    (arguments : List Value := []) (fuel : Nat := 300000)
    (initial : RuntimeState := {}) : IO RunResult :=
  SourceCoreUnifiedCorpusSupport.observe prepared.compiled prepared.key arguments fuel initial

/-- Rewritten plans have no executable authority. Validation returns its actual
error and retains the unexecuted caller state as separate inert data. -/
private def validateTampered (prepared : ValidationFixture)
    (initial : RuntimeState := {}) : Except RuntimeError Unit × RuntimeState :=
  (SourceCompilationPlan.validateExecutablePlanEvidence prepared.program prepared.plan,
    initial)

private def rewriteEntryNodes (prepared : Prepared)
    (rewrite : List SourceInference.Node → List SourceInference.Node) : ValidationFixture :=
  let specializations := prepared.plan.specializations.map fun specialized =>
    if specialized.key = prepared.key then
      { specialized with
        function := {
          specialized.function with
          typedBody := {
            specialized.function.typedBody with
            nodes := rewrite specialized.function.typedBody.nodes
          }
        }
      }
    else
      specialized
  { program := prepared.program, key := prepared.key,
    plan := { prepared.plan with specializations } }

private def rewriteEntryFunction (prepared : Prepared)
    (rewrite : SourceInference.CheckedFunction →
      SourceInference.CheckedFunction) : ValidationFixture :=
  let specializations := prepared.plan.specializations.map fun specialized =>
    if specialized.key = prepared.key then
      { specialized with function := rewrite specialized.function }
    else
      specialized
  { program := prepared.program, key := prepared.key,
    plan := { prepared.plan with specializations } }

private def rewriteFirstExpression
    (rewrite : SourceInference.ExpressionNode → SourceInference.ExpressionNode) :
    List SourceInference.Node → List SourceInference.Node
  | [] => []
  | .expression node :: rest => .expression (rewrite node) :: rest
  | node :: rest => node :: rewriteFirstExpression rewrite rest

private def rewriteFirstIndirectCall
    (rewrite : SourceInference.IndirectCallResolution →
      SourceInference.IndirectCallResolution) :
    List SourceInference.Node → List SourceInference.Node
  | [] => []
  | .expression node :: rest =>
      match node.form with
      | .call callee arguments (.indirect metadata) =>
          .expression {
            node with
            form := .call callee arguments (.indirect (rewrite metadata))
          } :: rest
      | _ => .expression node :: rewriteFirstIndirectCall rewrite rest
  | node :: rest => node :: rewriteFirstIndirectCall rewrite rest

private def rewriteFirstIndirectCallNode
    (rewrite : SourceInference.ExpressionNode →
      SourceInference.ExpressionNode) :
    List SourceInference.Node → List SourceInference.Node
  | [] => []
  | .expression node :: rest =>
      match node.form with
      | .call _ _ (.indirect _) => .expression (rewrite node) :: rest
      | _ => .expression node :: rewriteFirstIndirectCallNode rewrite rest
  | node :: rest => node :: rewriteFirstIndirectCallNode rewrite rest

private def firstSingletonLambdaTail? :
    List SourceInference.Node → Option SourceInference.StatementId
  | [] => none
  | .expression node :: rest =>
      match node.form with
      | .lambda _ _ [statement] => some statement
      | _ => firstSingletonLambdaTail? rest
  | _ :: rest => firstSingletonLambdaTail? rest

/-- The surface parser intentionally requires semicolons inside lambda blocks.
This test-only rewrite starts from a checked lambda with an explicit return and
retains the equivalent tail-expression IR for a standalone typed Core fragment
test. It claims no checker receipt for the rewritten plan. -/
private def rewriteFirstLambdaReturnAsImplicitTail
    (nodes : List SourceInference.Node) : List SourceInference.Node :=
  match firstSingletonLambdaTail? nodes with
  | none => nodes
  | some tail => nodes.map fun node =>
      match node with
      | .statement statement =>
          if statement.id = tail then
            match statement.form with
            | .returnStmt (some expression) =>
                .statement {
                  statement with
                  form := .expression expression false
                }
            | _ => node
          else
            node
      | _ => node

/-- The edited IR is a fragment, not a checked executable plan. Its actual
implicit lambda tail is lowered and checked in the parameter-cell context. -/
private def testRetainedLambdaTail (prepared : ValidationFixture) : IO Unit := do
  let specialized ← SourceCoreUnifiedCorpusSupport.get "retained lambda specialization"
    (SourceCompilationPlan.exactSpecialization prepared.plan prepared.key)
  let source := specialized.function.typedBody
  let (parameter, statements) ← match source.nodes.findSome? fun
      | .expression { form := .lambda [parameter] .word statements, .. } =>
          some (parameter, statements)
      | _ => none with
    | some lambda => pure lambda
    | none => throw (IO.userError "retained implicit tail lost its Word lambda")
  let scope : SourceCoreLocalCell.Scope := [(parameter.id, .word)]
  let body ← SourceCoreUnifiedCorpusSupport.get "retained implicit lambda tail lowering"
    (SourceCoreLoops.lowerStatements 100
      { solvedRequirements := specialized.function.solvedRequirements }
      source scope statements .word Core.Word.zero Core.Word.zero Core.Word.zero)
  assertTrue (Core.infer? (SourceCoreLocalCell.coreContext scope) body ==
      some (Core.LanguageResult.resultType .word))
    "retained implicit lambda tail failed Core checking"
  let store : Core.Store := [.inRight .unit (.word (word 41))]
  let initial := Core.State.initial body
    [.cellRef (Core.OptionalCell.cellType .word) 0] store
  let expected := Core.StatefulRunResult.done (.inRight .word (.word (word 42))) store
  assertTrue (Core.runStateful 2000 initial == expected)
    "retained implicit lambda tail changed its result or parameter cell"
  match Core.runStateful 2 initial with
  | .outOfFuel checkpoint =>
      assertTrue (Core.runStateful 2000 checkpoint == expected)
        "retained implicit lambda tail changed after resuming Core"
  | result => throw (IO.userError
      s!"retained implicit lambda tail expected a native checkpoint: {reprStr result}")

private def expectWord (label : String) (expected : Nat) : RunResult → IO Unit
  | .done (.word actual) _ =>
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def expectProxyWord (label : String) : RunResult → IO Unit
  | .done (.proxy type) _ =>
      assertTrue (decide (type = Ty.word)) s!"{label} returned the wrong proxy"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def expectShallowHeap (label : String)
    (plan : SourceSpecializationWorklist.Plan) : RunResult → IO Unit
  | .done _ state => do
      for cell in state.heap do
        match cell.value with
        | none => pure ()
        | some value =>
            assertTrue (decide (
                value.type? plan = some (runtimeType cell.type)))
              s!"{label} left an initialized cell with a mismatched type"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def source : String := String.intercalate "\n" [
  "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
  "enum StagedBox { Open(integer) }",
  "type StagedWord = comptime<Word>;",
  "type DeepStage = (StagedWord, (Word, StagedWord));",
  "function sumTree(tree: Tree<Word>) returns (Word) {",
  "  match (tree) {",
  "    case .Leaf(value) { return value; }",
  "    case .Pair(.Leaf(left), .Leaf(right)) { return left + right; }",
  "    default { return 0; }",
  "  }",
  "}",
  "function descend(value: Word) returns (Tree<Word>) {",
  "  return value == 0 ? .Leaf(9) : descend(value - 1);",
  "}",
  "function makeNested() returns (Tree<Word>) {",
  "  return Tree.Pair(.Leaf(11), .Leaf(22));",
  "}",
  "function nominalCall() returns (Word) {",
  "  let nested: Tree<Word> = makeNested();",
  "  return sumTree(nested) + sumTree(descend(3));",
  "}",
  "function acceptTree(tree: Tree<Word>) returns (Word) {",
  "  return 13;",
  "}",
  "function acceptStagedBox(value: StagedBox) returns (Word) {",
  "  return 17;",
  "}",
  "function nestedComptime(value: DeepStage) returns (DeepStage) {",
  "  return value;",
  "}",
  "function integerBitAnd() returns (integer) { return 5 & 3; }",
  "function integerBitXor() returns (integer) { return 5 ^ 3; }",
  "function integerBitOr() returns (integer) { return 5 | 3; }",
  "function integerBitNot() returns (integer) { return ~5; }",
  "function integerBitAndNegative() returns (integer) {",
  "  return integerSub(0, 5) & 3;",
  "}",
  "function integerBitOrNegative() returns (integer) {",
  "  return 2 | integerSub(0, 5);",
  "}",
  "function integerBitXorNegative() returns (integer) {",
  "  return integerSub(0, 5) ^ 2;",
  "}",
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
  "function markedClosureClosed() returns (Word) {",
  "  let f = lam(comptime value: Word) -> Word { return value; };",
  "  return f(21);",
  "}",
  "function markedClosureRuntime(value: Word) returns (Word) {",
  "  let f = lam(comptime item: Word) -> Word { return item; };",
  "  return f(value);",
  "}",
  "function markedGlobal(comptime value: Word) returns (Word) { return value; }",
  "function markedGlobalClosed() returns (Word) {",
  "  let f = markedGlobal;",
  "  return f(22);",
  "}",
  "function markedGlobalRuntime(value: Word) returns (Word) {",
  "  let f = markedGlobal;",
  "  return f(value);",
  "}",
  "function markedResult(comptime value: Word) returns (comptime<Word>) {",
  "  return value;",
  "}",
  "function markedResultIndirectBlocked() returns (Word) {",
  "  let f = markedResult;",
  "  return f(23);",
  "}",
  "function markedResultIndirectStaged() returns (comptime<Word>) {",
  "  let f = markedResult;",
  "  return f(24);",
  "}",
  "function tupleMatch() returns (Word) {",
  "  let tree: Tree<Word> = .Leaf(7);",
  "  match (tree, true) {",
  "    case (.Leaf(value), flag) { return flag ? value : 0; }",
  "    default { return 1; }",
  "  }",
  "}",
  "function assignments() returns (Word) {",
  "  let local: Word = 5;",
  "  local += 3;",
  "  local ~=;",
  "  return local;",
  "}",
  "function mappings() returns (Word) {",
  "  let table: mapping(Word => Word);",
  "  let before: Word = table[7];",
  "  table[7] = 4;",
  "  table[7] += 3;",
  "  let nested: mapping(Word => mapping(Word => Word));",
  "  nested[1][2] = 9;",
  "  return before + table[7] + nested[1][2];",
  "}",
  "function loops() returns (Word) {",
  "  let total: Word = 0;",
  "  let i: Word = 0;",
  "  while (i < 5) {",
  "    i += 1;",
  "    if (i == 2) { continue; }",
  "    if (i == 4) { break; }",
  "    total += i;",
  "  }",
  "  for (let j: Word = 0; j < 4; j += 1) {",
  "    if (j == 1) { continue; }",
  "    if (j == 3) { break; }",
  "    total += j;",
  "  }",
  "  return total;",
  "}",
  "function sharedCapture() returns (Word) {",
  "  let captured: Word = 1;",
  "  let read = lam() -> Word { return captured; };",
  "  captured = 9;",
  "  return read();",
  "}",
  "function assignmentOrder() returns (Word) {",
  "  let order: Word = 0;",
  "  let table: mapping(Word => Word);",
  "  let indexer = lam() -> Word { order = order * 10 + 1; return 5; };",
  "  let rhs = lam() -> Word { order = order * 10 + 2; return 7; };",
  "  table[indexer()] = rhs();",
  "  return order * 100 + table[5];",
  "}",
  "function proxyValue() returns (@Word) { return @Word; }",
  "function callProduct() returns (Word) {",
  "  let f = lam(pair: (Word, Bool)) -> Word { return 1; };",
  "  return f((2, true));",
  "}",
  "function callSplit() returns (Word) {",
  "  let f = lam(left: Word, right: Bool) -> Word { return left; };",
  "  return f(2, true);",
  "}",
  "function implicitTail() returns (Word) { 40 + 2 }",
  "function closureImplicitTail() returns (Word) {",
  "  let f = lam(value: Word) -> Word { return value + 1; };",
  "  return f(41);",
  "}",
  "function localPolymorphism(flag: Bool) returns (Word, Bool) {",
  "  let identity = lam(value) { return flag ? value : value; };",
  "  return (identity(41), identity(flag));",
  "}",
  "function genericIdentity<T>(value: T) returns (T) { return value; }",
  "trait Proof<T> {}",
  "impl Proof<Word> {}",
  "trait Eq<T> {}",
  "impl Eq<Word> where Word: Proof {}",
  "impl Eq<Bool> {}",
  "function constrainedRoot(value: Word) returns (Word) where Word: Eq {",
  "  let table: mapping(Word => Word);",
  "  table[0] = value;",
  "  return table[0];",
  "}",
  "trait Mark<T> {}",
  "impl Mark<Word> {}",
  "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
  "function relay<T>(value: T) returns (T) where T: Eq { return keep(value); }",
  "function nestedConstrained(value: Word) returns (Word) { return relay(value); }",
  "function repeat<T>(value: T, count: Word) returns (T) where T: Eq {",
  "  return count == 0 ? value : repeat(value, count - 1);",
  "}",
  "function recursiveConstrained(value: Word) returns (Word) {",
  "  return repeat(value, 3);",
  "}",
  "function closureRelay<T>(value: T) returns (T) where T: Eq {",
  "  let invoke = lam(inner: T) -> T { return keep(inner); };",
  "  return invoke(value);",
  "}",
  "function closureConstrained(value: Word) returns (Word) {",
  "  return closureRelay(value);",
  "}",
  "function keepBoth<T>(value: T) returns (T) where T: Eq, T: Mark {",
  "  return value;",
  "}",
  "function relayBoth<T>(value: T) returns (T) where T: Mark, T: Eq {",
  "  return keepBoth(value);",
  "}",
  "function orderedConstrained(value: Word) returns (Word) {",
  "  return relayBoth(value);",
  "}",
  "function qualifiedLocalProof(flag: Bool) returns (Word, Bool) {",
  "  let f = lam(value) { return keep(value); };",
  "  return (f(53), f(flag));",
  "}",
  "function keepAs<T, U>(guard: T, value: U) returns (U) where T: Eq { return value; }",
  "function localProof(flag: Bool) returns (Word, Bool) {",
  "  let f = lam(value) { return keepAs(1, value); };",
  "  return (f(2), f(flag));",
  "}",
  "function localGenericCalls(flag: Bool) returns (Word, Bool) {",
  "  let applyIdentity = lam(value) { return genericIdentity(value); };",
  "  return (applyIdentity(43), applyIdentity(flag));",
  "}",
  "function localGenericAliasEscape(flag: Bool) returns (Word, Bool) {",
  "  let applyIdentity = lam(value) { return genericIdentity(value); };",
  "  let asWord: function(Word) returns(Word) = applyIdentity;",
  "  let asBool: function(Bool) returns(Bool) = applyIdentity;",
  "  return (asWord(47), asBool(flag));",
  "}",
  "impl Mark<Bool> {}",
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To)",
  "      where From: Eq, From: Mark;",
  "}",
  "function boolToWord(value: Bool) returns (Word) {",
  "  return value ? 41 : 7;",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(value: Bool) returns (Word)",
  "      where Bool: Eq, Bool: Mark {",
  "    return boolToWord(value);",
  "  }",
  "}",
  "impl Coerce<Word, (Word, Word)> {",
  "  function coerce(value: Word) returns ((Word, Word))",
  "      where Word: Eq, Word: Mark {",
  "    return (value, value);",
  "  }",
  "}",
  "type WordFunction = function(Word) returns (Word);",
  "function returnedIdentity(value: Word) returns (Word) { return value; }",
  "impl Coerce<Word, WordFunction> {",
  "  function coerce(value: Word) returns (WordFunction)",
  "      where Word: Eq, Word: Mark {",
  "    return returnedIdentity;",
  "  }",
  "}",
  "function functionFromCoercion(value: Word) returns (WordFunction) {",
  "  return value;",
  "}",
  "function acceptWord(value: Word) returns (Word) { return value; }",
  "function acceptWordPair(value: (Word, Word)) returns ((Word, Word)) {",
  "  return value;",
  "}",
  "function coercionChain(value: Bool) returns ((Word, Word)) {",
  "  return acceptWordPair(value);",
  "}",
  "function coercionRelay<T>(value: T) returns (Word)",
  "    where T: Coerce<Word>, T: Eq, T: Mark {",
  "  return acceptWord(value);",
  "}",
  "function genericCoercion(value: Bool) returns (Word) {",
  "  return coercionRelay(value);",
  "}",
  "function resultCoercion(value: Bool) returns (Word) { return value; }",
  "function indirectCoercion(value: Bool) returns (Word) {",
  "  let apply = lam(inner: Word) -> Word { return inner; };",
  "  return apply(value);",
  "}",
  "function spin(value: Word) returns (Word) { return spin(value); }"
]

private def testNominalConstructionAndRecursiveCalls
    (program : CheckedProgram) : IO Unit := do
  let nested ← prepareNamed program "makeNested"
  match ← runPrepared nested with
  | .done (.constructed _ [
        .constructed _ [.word left],
        .constructed _ [.word right]]) _ =>
      assertTrue (left == word 11 && right == word 22)
        "recursive generic enum construction changed its payloads"
  | result => throw (IO.userError
      s!"recursive generic enum construction returned {reprStr result}")
  let descend ← prepareNamed program "descend"
  match ← runPrepared descend [.word (word 3)] with
  | .done (.constructed _ [.word actual]) _ =>
      assertTrue (actual == word 9)
        "direct recursive call changed its nominal result"
  | result => throw (IO.userError
      s!"direct recursive nominal call returned {reprStr result}")

private def testNestedMatchingAndCalls (program : CheckedProgram) : IO Unit := do
  let nominal ← prepareNamed program "nominalCall"
  expectWord "recursive nominal call" 42 (← runPrepared nominal)
  let tuple ← prepareNamed program "tupleMatch"
  expectWord "tuple/constructor/binder match" 7 (← runPrepared tuple)

private def testAssignmentsMappingsAndControl
    (program : CheckedProgram) : IO Unit := do
  let assignments ← prepareNamed program "assignments"
  let expected := Core.Word.maximum.sub (word 8) |>.val
  let assignmentResult ← runPrepared assignments
  expectWord "compound and bit-not assignment" expected
    assignmentResult
  expectShallowHeap "compound and bit-not assignment" assignments.plan
    assignmentResult
  let mappings ← prepareNamed program "mappings"
  let mappingResult ← runPrepared mappings
  expectWord "empty and nested mapping" 16 mappingResult
  expectShallowHeap "empty and nested mapping" mappings.plan mappingResult
  let loops ← prepareNamed program "loops"
  expectWord "for/while break/continue" 6 (← runPrepared loops  [] 300000)

private def testClosuresOrderProxyAndFuel
    (program : CheckedProgram) : IO Unit := do
  /- Closures capture by value: `read` keeps the 1 it captured, and the later
  assignment of 9 does not reach it. -/
  let capture ← prepareNamed program "sharedCapture"
  expectWord "creation-time closure capture" 1 (← runPrepared capture)
  /- Each closure call writes only its own copy of `order`, which stays 0, so
  this result no longer tells the index call from the RHS call. -/
  let order ← prepareNamed program "assignmentOrder"
  expectWord "assignment through index and RHS closure calls" 7
    (← runPrepared order [] 300000)
  let proxy ← prepareNamed program "proxyValue"
  expectProxyWord "proxy value" (← runPrepared proxy)
  let implicitTail ← prepareNamed program "implicitTail"
  expectWord "top-level implicit tail return" 42 (← runPrepared implicitTail)
  let closureImplicitTail ← prepareNamed program "closureImplicitTail"
  let closureImplicitTail := rewriteEntryNodes closureImplicitTail
    rewriteFirstLambdaReturnAsImplicitTail
  /- The canonical validator rejects this test-only plan. The retained tail is
  covered by an independently checked Core fragment below. -/
  match (validateTampered closureImplicitTail).1 with
  | .error .nonCanonicalInputPlan => pure ()
  | result => throw (IO.userError
      s!"forged closure tail escaped plan validation: {reprStr result}")
  testRetainedLambdaTail closureImplicitTail
  let spin ← prepareNamed program "spin"
  match ← runPrepared spin [.word (word 1)] 3 with
  | .outOfFuel _ => pure ()
  | result => throw (IO.userError
      s!"recursive low-fuel call did not exhaust: {reprStr result}")

private def testLocalLetPolymorphism (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "localPolymorphism"
  let result ← runPrepared prepared [.bool true]
  match result with
  | .done (.product (.word actual) (.bool selected)) _ =>
      assertTrue (actual == word 41 && selected)
        "one principal local lambda was not instantiated at Word and Bool"
  | other => throw (IO.userError
      s!"local let-polymorphism returned {reprStr other}")
  expectShallowHeap "local let-polymorphism" prepared.plan result

private def testQualifiedLocalLetPolymorphism
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "qualifiedLocalProof"
  let result ← runPrepared prepared [.bool true]
  match result with
  | .done (.product (.word actual) (.bool selected)) _ =>
      assertTrue (actual == word 53 && selected)
        "qualified local scheme did not select independent Word/Bool evidence"
  | other => throw (IO.userError
      s!"qualified local let-polymorphism returned {reprStr other}")
  expectShallowHeap "qualified local let-polymorphism" prepared.plan result

private def expectWordBool (label : String) (expectedWord : Nat)
    (expectedBool : Bool) : RunResult → IO Unit
  | .done (.product (.word actualWord) (.bool actualBool)) _ =>
      assertTrue (actualWord == word expectedWord && actualBool == expectedBool)
        s!"{label} returned the wrong Word/Bool pair"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def assertContextualGenericPlan (label : String)
    (prepared : Prepared) : IO Unit := do
  assertTrue (prepared.plan.specializations.length == 3)
    s!"{label} did not retain entry plus two identity specializations"
  let edges := prepared.plan.callEdges.filter fun edge =>
    decide (edge.caller = prepared.key)
  assertTrue (edges.length == 2)
    s!"{label} did not retain two concrete edges for the local lambda call"
  match edges with
  | [wordEdge, boolEdge] =>
      assertTrue (wordEdge.occurrence == boolEdge.occurrence)
        s!"{label} split one contextual call across different occurrences"
      assertTrue (wordEdge.callee != boolEdge.callee)
        s!"{label} collapsed Word and Bool calls to one specialization"
      let arguments := edges.map (fun edge => edge.callee.arguments)
      assertTrue (arguments.contains [.word] && arguments.contains [.bool])
        s!"{label} did not retain Word and Bool specialization keys"
  | _ => throw (IO.userError s!"{label} retained an impossible edge shape")

private def expectRuntimeFault (label : String)
    (accept : RuntimeError → Bool) : Except RuntimeError Unit → IO Unit
  | .error error =>
      assertTrue (accept error) s!"{label} reported {reprStr error}"
  | .ok () => throw (IO.userError
      s!"{label} did not reject tampered metadata")

private def testContextualGenericEdgeTampering
    (prepared : Prepared) : IO Unit := do
  let wordEdges := prepared.plan.callEdges.filter fun edge =>
    decide (edge.caller = prepared.key ∧ edge.callee.arguments = [.word])
  let wordEdge ← match wordEdges with
    | [edge] => pure edge
    | edges => throw (IO.userError
        s!"contextual generic plan retained {edges.length} Word edges")

  let duplicate : ValidationFixture := {
    prepared.toValidationFixture with
    plan := {
      prepared.plan with
      callEdges := wordEdge :: prepared.plan.callEdges
    }
  }
  expectRuntimeFault "duplicate contextual generic edge"
    (fun error => match error with
      | .nonCanonicalInputPlan => true
      | _ => false)
    (validateTampered duplicate).1
  expectRuntimeFault "exact duplicate contextual generic edge"
    (fun error => match error with
      | .duplicateCallEdge caller occurrence 2 =>
          decide (caller = prepared.key ∧ occurrence = wordEdge.occurrence)
      | _ => false)
    ((SourceCompilationPlan.exactCallKey duplicate.plan duplicate.key
      wordEdge.occurrence wordEdge.callee).map fun _ => ())

  let missing : ValidationFixture := {
    prepared.toValidationFixture with
    plan := {
      prepared.plan with
      callEdges := prepared.plan.callEdges.filter fun edge =>
        decide (edge != wordEdge)
    }
  }
  expectRuntimeFault "missing contextual generic edge"
    (fun error => match error with
      | .nonCanonicalInputPlan => true
      | _ => false)
    (validateTampered missing).1
  expectRuntimeFault "exact missing contextual generic edge"
    (fun error => match error with
      | .missingCallEdge caller occurrence =>
          decide (caller = prepared.key ∧ occurrence = wordEdge.occurrence)
      | _ => false)
    ((SourceCompilationPlan.exactCallKey missing.plan missing.key
      wordEdge.occurrence wordEdge.callee).map fun _ => ())

private def testContextualLocalGenericCalls
    (program : CheckedProgram) : IO Unit := do
  let direct ← prepareNamed program "localGenericCalls"
  assertContextualGenericPlan "contextual local generic call" direct
  let directResult ← runPrepared direct [.bool true]
  expectWordBool "contextual local generic call" 43 true directResult
  expectShallowHeap "contextual local generic call" direct.plan directResult
  testContextualGenericEdgeTampering direct

  let escaped ← prepareNamed program "localGenericAliasEscape"
  assertContextualGenericPlan "ground alias escape" escaped
  let escapedResult ← runPrepared escaped [.bool false]
  expectWordBool "ground alias escape" 47 false escapedResult
  expectShallowHeap "ground alias escape" escaped.plan escapedResult

private def treeData (program : CheckedProgram) : IO ProgramDataSignature :=
  match program.signatures.dataTypes.filter fun dataType =>
      dataType.name == "Tree" with
  | [dataType] => pure dataType
  | dataTypes => throw (IO.userError
      s!"expected one Tree signature, found {dataTypes.length}")

private def leafConstructor (dataType : ProgramDataSignature) :
    IO ProgramDataConstructorSignature :=
  match dataType.constructors.filter fun constructor =>
      constructor.name == "Leaf" with
  | [constructor] => pure constructor
  | constructors => throw (IO.userError
      s!"expected one Leaf constructor, found {constructors.length}")

private def stagedBoxData (program : CheckedProgram) :
    IO ProgramDataSignature :=
  match program.signatures.dataTypes.filter fun dataType =>
      dataType.name == "StagedBox" with
  | [dataType] => pure dataType
  | dataTypes => throw (IO.userError
      s!"expected one StagedBox signature, found {dataTypes.length}")

private def stagedBoxConstructor (dataType : ProgramDataSignature) :
    IO ProgramDataConstructorSignature :=
  match dataType.constructors.filter fun constructor =>
      constructor.name == "Open" with
  | [constructor] => pure constructor
  | constructors => throw (IO.userError
      s!"expected one StagedBox.Open constructor, found {constructors.length}")

private def testNominalInputValidation (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "acceptTree"
  let dataType ← treeData program
  let leaf ← leafConstructor dataType
  let parameter ← match dataType.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"Tree retained {parameters.length} type parameters")
  let substitution : ParameterSubstitution := [(parameter, .word)]
  let resultType := Ty.nominal dataType.id [.word]
  let legitimate : SourceInference.DataConstructorInstantiation := {
    constructor := leaf.id
    parameterSubstitution := substitution
    payloadTypes := [.word]
    resultType
  }
  expectWord "validated nominal input" 13 <| (← runPrepared prepared
    [.constructed legitimate [.word (word 13)]])
  let forged := {
    legitimate with
    constructor := {
      dataType := dataType.id
      constructorIndex := leaf.id.constructorIndex + 100
    }
  }
  match ← runPrepared prepared [.constructed forged [.word (word 13)]] with
  | .fault (.typeMismatch expected actual) _ =>
      assertTrue (decide (expected = resultType ∧ actual = some resultType))
        "forged constructor failed for an unrelated input type"
  | result => throw (IO.userError
      s!"forged constructor input was not rejected: {reprStr result}")

  let stagedPrepared ← prepareNamed program "acceptStagedBox"
  let stagedData ← stagedBoxData program
  let stagedConstructor ← stagedBoxConstructor stagedData
  let stagedResultType := Ty.nominal stagedData.id []
  let stagedInstantiation : SourceInference.DataConstructorInstantiation := {
    constructor := stagedConstructor.id
    parameterSubstitution := []
    payloadTypes := stagedConstructor.payloadTypes
    resultType := stagedResultType
  }
  let stagedResult ← runPrepared stagedPrepared
    [.constructed stagedInstantiation [.integer 13]]
  expectWord "validated staged nominal input" 17 stagedResult
  expectShallowHeap "validated staged nominal input" stagedPrepared.plan
    stagedResult

private def testStagedRuntimeTypesAndEffects
    (program : CheckedProgram) : IO Unit := do
  let nested ← prepareNamed program "nestedComptime"
  let nestedResult ← runPrepared nested [
    .product (.word (word 4))
      (.product (.word (word 5)) (.word (word 6)))]
  match nestedResult with
  | .done (.product (.word left)
      (.product (.word middle) (.word right))) _ =>
      assertTrue (left == word 4 && middle == word 5 && right == word 6)
        "recursively erased comptime product changed its payload"
  | result => throw (IO.userError
      s!"recursively erased comptime product returned {reprStr result}")
  expectShallowHeap "recursively erased comptime product" nested.plan
    nestedResult

  for (name, expected) in [
      ("integerBitAnd", 1), ("integerBitXor", 6),
      ("integerBitOr", 7), ("integerBitNot", -6),
      ("integerBitAndNegative", 3), ("integerBitOrNegative", -5),
      ("integerBitXorNegative", -7)] do
    let prepared ← prepareNamed program name
    match ← runPrepared prepared with
    | .done (.integer actual) state =>
        assertTrue (actual == expected)
          s!"{name} returned the wrong integer"
        assertTrue state.heap.isEmpty
          s!"{name} unexpectedly allocated a cell"
    | result => throw (IO.userError s!"{name} returned {reprStr result}")

  let effects ← prepareNamed program "markedEffects"
  let effectsResult ← runPrepared effects [.word (word 9)]
  expectWord "marked closure/mutation/mapping" 12 effectsResult
  expectShallowHeap "marked closure/mutation/mapping" effects.plan
    effectsResult

  let closureClosed ← prepareNamed program "markedClosureClosed"
  expectWord "closed marked closure call" 21 (← runPrepared closureClosed)
  let closureRuntime ← prepareNamed program "markedClosureRuntime"
  match ← runPrepared closureRuntime [.word (word 21)] with
  | .fault (.comptimeArgumentStageMismatch _ _ 0 _ .runtime) _ => pure ()
  | result => throw (IO.userError
      s!"runtime marked closure argument returned {reprStr result}")

  let globalClosed ← prepareNamed program "markedGlobalClosed"
  expectWord "closed marked global call" 22 (← runPrepared globalClosed)
  let globalRuntime ← prepareNamed program "markedGlobalRuntime"
  match ← runPrepared globalRuntime [.word (word 22)] with
  | .fault (.comptimeArgumentStageMismatch _ _ 0 _ .runtime) _ => pure ()
  | result => throw (IO.userError
      s!"runtime marked global argument returned {reprStr result}")

  let blockedResult ← prepareNamed program "markedResultIndirectBlocked"
  match ← runPrepared blockedResult with
  | .fault (.comptimeResultStageMismatch _ _ _ .deferred) _ => pure ()
  | result => throw (IO.userError
      s!"ordinary indirect staged result returned {reprStr result}")
  let stagedResult ← prepareNamed program "markedResultIndirectStaged"
  expectWord "staged indirect marked result" 24 (← runPrepared stagedResult)

  let functionResult ← prepareNamed program "functionFromCoercion"
  match ← runPrepared functionResult [.word (word 1)] with
  | .done (.global _ _) _ => pure ()
  | result => throw (IO.userError
      s!"method-discovered first-class global returned {reprStr result}")

private def expectPreExecutionFault (label : String)
    (accept : RuntimeError → Bool) :
    Except RuntimeError Unit × RuntimeState → IO Unit
  | (.error error, { heap := [] }) =>
      assertTrue (accept error) s!"{label} reported {reprStr error}"
  | (.error error, state) => throw (IO.userError
      s!"{label} mutated state before rejecting metadata: {reprStr error}, {reprStr state}")
  | (.ok (), _) => throw (IO.userError
      s!"{label} did not reject tampered plan metadata")

private def expectPreExecutionFaultPreservingSentinel (label : String)
    (accept : RuntimeError → Bool) :
    Except RuntimeError Unit × RuntimeState → IO Unit
  | (.error error, { heap := [{ type := actualType, value := none }] }) => do
      assertTrue (accept error) s!"{label} reported {reprStr error}"
      assertTrue (actualType == .word)
        s!"{label} changed the sentinel cell type to {reprStr actualType}"
  | (.error error, state) => throw (IO.userError
      s!"{label} changed the initial state before rejecting metadata: {reprStr error}, {reprStr state}")
  | (.ok (), _) => throw (IO.userError
      s!"{label} did not reject tampered plan metadata")

private def expectPlanValidationFault (label : String)
    (accept : RuntimeError → Bool) : Except RuntimeError Unit → IO Unit
  | .error error =>
      assertTrue (accept error) s!"{label} reported {reprStr error}"
  | .ok () => throw (IO.userError
      s!"{label} did not reject tampered plan metadata")

private def testTamperedExecutableMetadata
    (program : CheckedProgram) : IO Unit := do
  let original ← prepareNamed program "implicitTail"
  let impostor ← prepareNamed program "loops"
  let impostorFunction ←
    match impostor.plan.specializations.filter fun specialized =>
        decide (specialized.key = impostor.key) with
    | [specialized] => pure specialized.function
    | specializations => throw (IO.userError
        s!"impostor plan retained {specializations.length} entry specializations")
  let withImpostorBody := rewriteEntryFunction original fun _ =>
    impostorFunction
  expectPreExecutionFault "specialization ownership mismatch"
    (fun error => match error with
      | .specializationOwnershipMismatch key declaration
          functionDeclaration typedBodyOwner =>
          decide (key = original.key ∧
            declaration = original.key.declaration ∧
            functionDeclaration = impostor.key.declaration ∧
            typedBodyOwner = impostor.key.declaration)
      | _ => false)
    (validateTampered withImpostorBody)

  let fakeRequirement : SourceInference.RequirementId := { index := 1000000 }
  let proxy ← prepareNamed program "proxyValue"
  let withRequirement := rewriteEntryNodes proxy <| rewriteFirstExpression
    fun node => { node with requirements := [fakeRequirement] }
  expectPreExecutionFault "unsupported expression requirement"
    (fun error => error == .unsupportedRequirements [fakeRequirement])
    (validateTampered withRequirement)

  let fakeCoercion : SourceInference.CoercionStep := {
    requirement := fakeRequirement
    source := .word
    target := .word
  }
  let withResultCoercion := rewriteEntryNodes proxy <| rewriteFirstExpression
    fun node => { node with coercions := [fakeCoercion] }
  expectPreExecutionFault "invalid result coercion"
    (fun error => error matches .invalidExpressionCoercionPath _ _ _)
    (validateTampered withResultCoercion)

  let capture ← prepareNamed program "sharedCapture"
  let withArgumentCoercion := rewriteEntryNodes capture <|
    rewriteFirstIndirectCall fun metadata => {
      metadata with argumentCoercions := [fakeCoercion]
    }
  expectPreExecutionFault "invalid indirect argument coercion"
    (fun error => error matches .invalidIndirectArgumentCoercionPath _)
    (validateTampered withArgumentCoercion)

  let inconsistentResult := rewriteEntryFunction proxy fun function =>
    { function with inferredBodyType := .bool }
  expectPreExecutionFault "inconsistent inferred result type"
    (fun error => match error with
      | .inferredResultTypeMismatch key declared inferred =>
          decide (key = proxy.key ∧ declared = .proxy .word ∧ inferred = .bool)
      | _ => false)
    (validateTampered inconsistentResult)

private def testIndirectArgumentCountMetadata
    (program : CheckedProgram) : IO Unit := do
  let product ← prepareNamed program "callProduct"
  let forgedProduct := rewriteEntryNodes product <|
    rewriteFirstIndirectCall fun metadata => {
      metadata with argumentCount := 2
    }
  expectPreExecutionFault "single product argument count"
    (fun error => match error with
      | .argumentArityMismatch 2 1 => true
      | _ => false)
    (validateTampered forgedProduct)

  let split ← prepareNamed program "callSplit"
  let forgedSplit := rewriteEntryNodes split <|
    rewriteFirstIndirectCall fun metadata => {
      metadata with argumentCount := 1
    }
  expectPreExecutionFault "multiple argument count"
    (fun error => match error with
      | .argumentArityMismatch 1 2 => true
      | _ => false)
    (validateTampered forgedSplit)

private def testIndirectEndpointMetadata
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "indirectCoercion"
  let initialState : RuntimeState := {
    heap := [{ type := .word, value := none }]
  }
  let validateWithSentinel (tampered : ValidationFixture) :=
    validateTampered tampered initialState

  let beforeMismatch := rewriteEntryNodes prepared <|
    rewriteFirstIndirectCall fun metadata => {
      metadata with
      argumentTypeBeforeCoercion := metadata.argumentTypeAfterCoercion
      argumentCoercions := match metadata.argumentCoercions with
        | [] => []
        | step :: rest =>
            { step with source := metadata.argumentTypeAfterCoercion } :: rest
    }
  expectPreExecutionFaultPreservingSentinel
    "indirect before-coercion endpoint mismatch"
    (fun error => match error with
      | .indirectArgumentBundleMismatch _ expected actual =>
          decide (expected = .bool ∧ actual = .word)
      | _ => false)
    (validateWithSentinel beforeMismatch)

  let afterMismatch := rewriteEntryNodes prepared <|
    rewriteFirstIndirectCall fun metadata => {
      metadata with
      argumentTypeAfterCoercion := metadata.argumentTypeBeforeCoercion
      argumentCoercions := match metadata.argumentCoercions.reverse with
        | [] => []
        | step :: rest =>
            ({ step with target := metadata.argumentTypeBeforeCoercion } :: rest).reverse
    }
  expectPreExecutionFaultPreservingSentinel
    "indirect after-coercion endpoint mismatch"
    (fun error => match error with
      | .indirectParameterTypeMismatch _ expected actual =>
          decide (expected = .word ∧ actual = .bool)
      | _ => false)
    (validateWithSentinel afterMismatch)

  let resultMismatch := rewriteEntryNodes prepared <|
    rewriteFirstIndirectCallNode fun node =>
      let fakeRequirement : SourceInference.RequirementId := { index := 1000001 }
      { node with
        coercions := [{
          requirement := fakeRequirement
          source := .bool
          target := node.type
        }]
      }
  expectPreExecutionFaultPreservingSentinel
    "indirect result endpoint mismatch"
    (fun error => match error with
      | .indirectResultTypeMismatch _ expected actual =>
          decide (expected = .word ∧ actual = .bool)
      | _ => false)
    (validateWithSentinel resultMismatch)

private def letBinderNamed
    (specialized : SourceSpecialization.SpecializedFunction) (name : String) :
    IO SourceInference.TypedBinder :=
  match specialized.function.typedBody.nodes.filterMap fun
      | .statement { form := .letDecl binder _, .. } =>
          if binder.name == name then some binder else none
      | _ => none with
  | [binder] => pure binder
  | binders => throw (IO.userError
      s!"expected one let binder named `{name}`, found {binders.length}")

private def entrySpecialization (prepared : Prepared) :
    IO SourceSpecialization.SpecializedFunction :=
  match prepared.plan.specializations.filter fun specialized =>
      decide (specialized.key = prepared.key) with
  | [specialized] => pure specialized
  | specializations => throw (IO.userError
      s!"entry retained {specializations.length} specializations")

private def rewriteEntryExpressionAt (prepared : Prepared)
    (target : SourceInference.ExpressionId)
    (rewrite : SourceInference.ExpressionNode →
      SourceInference.ExpressionNode) : ValidationFixture :=
  rewriteEntryNodes prepared fun nodes => nodes.map fun node =>
    match node with
    | .expression expression =>
        if expression.id == target then .expression (rewrite expression)
        else node
    | _ => node

private def rewriteEntryLetBinder (prepared : Prepared)
    (target : Resolved.LocalId)
    (rewrite : SourceInference.TypedBinder → SourceInference.TypedBinder) :
    ValidationFixture :=
  rewriteEntryNodes prepared fun nodes => nodes.map fun node =>
    match node with
    | .statement statement@{ form := .letDecl binder initializer, .. } =>
        if binder.id == target then
          .statement { statement with
            form := .letDecl (rewrite binder) initializer }
        else
          node
    | _ => node

private structure QualifiedLocalFixture where
  prepared : Prepared
  binder : SourceInference.TypedBinder
  initializer : SourceInference.ExpressionId
  template : SourceInference.LocalSchemeRequirement
  templateSolved : SourceInference.SolvedRequirement
  call : SourceInference.ExpressionNode
  callee : SourceInference.ExpressionId
  reference : SourceInference.ExpressionNode
  actualRequirement : SourceInference.RequirementId
  actualSolved : SourceInference.SolvedRequirement

private def qualifiedLocalFixture
    (program : CheckedProgram) : IO QualifiedLocalFixture := do
  let prepared ← prepareNamed program "qualifiedLocalProof"
  let specialized ← entrySpecialization prepared
  let binder ← letBinderNamed specialized "f"
  let initializer ← match specialized.function.typedBody.nodes.filterMap fun
      | .statement { form := .letDecl candidate (some initializer), .. } =>
          if candidate.id == binder.id then some initializer else none
      | _ => none with
    | [initializer] => pure initializer
    | initializers => throw (IO.userError
        s!"qualified f retained {initializers.length} initializers")
  let template ← match binder.schemeRequirements with
    | [template] => pure template
    | requirements => throw (IO.userError
        s!"qualified f retained {requirements.length} template requirements")
  let templateSolved ← match specialized.function.solvedRequirements.filter
      fun solved => solved.id == template.templateRequirement with
    | [solved] => pure solved
    | solved => throw (IO.userError
        s!"qualified f retained {solved.length} template solutions")
  let call ← match specialized.function.typedBody.nodes.filterMap fun
      | .expression node@{ form := .call _ _ (.declaration _), .. } =>
          if node.requirements.contains template.templateRequirement then
            some node
          else
            none
      | _ => none with
    | [call] => pure call
    | calls => throw (IO.userError
        s!"qualified f retained {calls.length} template call uses")
  let callee ← match call.form with
    | .call callee _ (.declaration _) => pure callee
    | _ => throw (IO.userError "qualified template call changed form")
  let references := specialized.function.typedBody.nodes.filterMap fun
    | .expression node@{ form := .reference _ (.local id), .. } =>
        if id == binder.id then some node else none
    | _ => none
  let reference ← match references.find? fun node =>
      decide (node.rawType = .function .word .word) with
    | some reference => pure reference
    | none => throw (IO.userError "qualified f lost its Word reference")
  let actualRequirement ← match reference.requirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"qualified Word reference retained {requirements.length} requirements")
  let actualSolved ← match specialized.function.solvedRequirements.filter
      fun solved => solved.id == actualRequirement with
    | [solved] => pure solved
    | solved => throw (IO.userError
        s!"qualified Word reference retained {solved.length} solutions")
  pure {
    prepared, binder, initializer, template, templateSolved, call, callee, reference,
    actualRequirement, actualSolved
  }

private structure ConstrainedCallFixture where
  prepared : Prepared
  occurrence : SourceInference.ExpressionId
  requirement : SourceInference.RequirementId
  predicate : ProgramPredicate
  solved : SourceInference.SolvedRequirement
  callee : SourceSpecialization.SpecializationKey

private def constrainedCallFixture
    (program : CheckedProgram) : IO ConstrainedCallFixture := do
  let prepared ← prepareNamed program "localProof"
  let specialized ← entrySpecialization prepared
  let edges := prepared.plan.callEdges.filter fun edge =>
    decide (edge.caller = prepared.key)
  let (firstEdge, secondEdge) ← match edges with
    | [first, second] => pure (first, second)
    | edges => throw (IO.userError
        s!"localProof retained {edges.length} contextual call edges")
  assertTrue (firstEdge.occurrence == secondEdge.occurrence &&
      firstEdge.callee != secondEdge.callee &&
      edges.eraseDups.length == 2)
    "localProof did not retain two distinct edges for one call occurrence"
  let arguments := edges.map (fun edge => edge.callee.arguments)
  assertTrue (arguments.contains [.word, .word] &&
      arguments.contains [.word, .bool])
    "localProof lost its keepAs<Word, Word/Bool> specializations"
  let occurrence := firstEdge.occurrence
  let (node, instantiation) ← match
      specialized.function.typedBody.lookupExpression? occurrence with
    | some node@{ form := .call _ _ (.declaration instantiation), .. } =>
        pure (node, instantiation)
    | some node => throw (IO.userError
        s!"localProof contextual occurrence changed form: {reprStr node.form}")
    | none => throw (IO.userError
        "localProof contextual call occurrence was absent")
  let requirement ← match node.requirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"localProof call retained {requirements.length} requirements")
  let predicate ← match instantiation.predicates with
    | [predicate] => pure predicate
    | predicates => throw (IO.userError
        s!"localProof call retained {predicates.length} predicates")
  let solved ← match specialized.function.solvedRequirements.filter fun row =>
      row.id == requirement with
    | [solved] => pure solved
    | rows => throw (IO.userError
        s!"localProof retained {rows.length} solved rows for its call")
  let implementationEvidence := match solved.evidence with
    | .implementation _ => true
    | .assumption _ => false
  assertTrue (decide (solved.predicate = predicate) && implementationEvidence)
    "localProof did not retain solved implementation evidence"
  for edge in edges do
    let callee ← match prepared.plan.specializations.filter fun candidate =>
        decide (candidate.key = edge.callee) with
      | [callee] => pure callee
      | callees => throw (IO.userError
          s!"localProof retained {callees.length} copies of a constrained callee")
    assertTrue (decide (callee.assumptions = [predicate]))
      "localProof constrained callee lost its Eq<Word> assumption"
  pure {
    prepared
    occurrence
    requirement
    predicate
    solved
    callee := firstEdge.callee
  }

private def rewriteEntrySolvedEvidence (prepared : Prepared)
    (requirement : SourceInference.RequirementId)
    (evidence : SourceInference.PredicateEvidence) : ValidationFixture :=
  rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.map fun solved =>
      if solved.id == requirement then { solved with evidence }
      else solved
  }

private def testContextualCallRequirementValidation
    (program : CheckedProgram) : IO Unit := do
  let fixture ← constrainedCallFixture program
  let prepared := fixture.prepared
  let result ← runPrepared prepared [.bool true]
  expectWordBool "contextual constrained local call" 2 true result
  expectShallowHeap "contextual constrained local call" prepared.plan result

  let missingCallRequirement := rewriteEntryExpressionAt prepared
    fixture.occurrence fun node => { node with requirements := [] }
  expectPreExecutionFault "missing direct-call requirement"
    (fun error => match error with
      | .callRequirementCountMismatch caller occurrence 1 0 =>
          decide (caller = prepared.key ∧ occurrence = fixture.occurrence)
      | .invalidDirectCallRequirementLayout caller occurrence [] =>
          decide (caller = prepared.key ∧ occurrence = fixture.occurrence)
      | _ => false)
    (validateTampered missingCallRequirement)

  let duplicateCallRequirement := rewriteEntryExpressionAt prepared
    fixture.occurrence fun node =>
      match node.form with
      | .call callee arguments (.declaration instantiation) => {
          node with
          requirements := [fixture.requirement, fixture.requirement]
          form := .call callee arguments (.declaration {
            instantiation with
            predicates := [fixture.predicate, fixture.predicate]
          })
        }
      | _ => node
  expectPreExecutionFault "duplicate direct-call requirement"
    (fun error => match error with
      | .duplicateCallRequirement caller occurrence requirement =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement)
      | _ => false)
    (validateTampered duplicateCallRequirement)

  let missingSolved := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.filter fun solved =>
      solved.id != fixture.requirement
  }
  expectPreExecutionFault "missing direct-call solution"
    (fun error => match error with
      | .missingSolvedRequirement caller occurrence requirement =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement)
      | _ => false)
    (validateTampered missingSolved)

  let duplicateSolved := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := fixture.solved :: function.solvedRequirements
  }
  expectPreExecutionFault "duplicate direct-call solutions"
    (fun error => match error with
      | .duplicateSolvedRequirements caller occurrence requirement 2 =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement)
      | _ => false)
    (validateTampered duplicateSolved)

  let wrongPredicate : ProgramPredicate := {
    fixture.predicate with subject := .bool
  }
  let predicateMismatch := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.map fun solved =>
      if solved.id == fixture.requirement then
        { solved with predicate := wrongPredicate }
      else
        solved
  }
  expectPreExecutionFault "direct-call predicate mismatch"
    (fun error => match error with
      | .callRequirementPredicateMismatch caller occurrence requirement
          expected actual =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            expected = fixture.predicate ∧ actual = wrongPredicate)
      | _ => false)
    (validateTampered predicateMismatch)

  let goalMismatch := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.map fun solved =>
      if solved.id == fixture.requirement then
        { solved with evidence := .assumption wrongPredicate }
      else
        solved
  }
  expectPreExecutionFault "direct-call evidence-goal mismatch"
    (fun error => match error with
      | .callRequirementEvidenceGoalMismatch caller occurrence requirement
          expected actual =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            expected = fixture.predicate ∧ actual = wrongPredicate)
      | _ => false)
    (validateTampered goalMismatch)

  let assumptionEvidence := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.map fun solved =>
      if solved.id == fixture.requirement then
        { solved with evidence := .assumption fixture.predicate }
      else
        solved
  }
  expectPreExecutionFault "direct-call assumption evidence"
    (fun error => match error with
      | .unsupportedCallAssumptionEvidence caller occurrence requirement
          predicate =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            predicate = fixture.predicate)
      | _ => false)
    (validateTampered assumptionEvidence)

  let (implementation, premise) ← match fixture.solved.evidence with
    | .implementation (.byImpl goal implementation [premise]) => do
        assertTrue (decide (goal = fixture.predicate))
          "localProof outer evidence lost its Eq<Word> goal"
        pure (implementation, premise)
    | evidence => throw (IO.userError
        s!"localProof expected one nested implementation premise, found {reprStr evidence}")
  let (premiseGoal, premiseImplementation) ← match premise with
    | .byImpl goal implementation [] => pure (goal, implementation)
    | premise => throw (IO.userError
        s!"localProof expected one premise-free Proof<Word> evidence, found {reprStr premise}")
  assertTrue (implementation != premiseImplementation &&
      decide (premiseGoal != fixture.predicate))
    "localProof did not retain distinct Eq and Proof implementation evidence"

  let wrongImplementationEvidence : SourceInference.PredicateEvidence :=
    .implementation (.byImpl fixture.predicate premiseImplementation [premise])
  let wrongImplementation := rewriteEntrySolvedEvidence prepared
    fixture.requirement wrongImplementationEvidence
  expectPreExecutionFault "unselected direct-call implementation"
    (fun error => match error with
      | .callEvidenceNotSelected caller occurrence requirement goal actual =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            goal = fixture.predicate ∧ actual = premiseImplementation)
      | _ => false)
    (validateTampered wrongImplementation)

  let missingPremiseEvidence : SourceInference.PredicateEvidence :=
    .implementation (.byImpl fixture.predicate implementation [])
  let missingPremise := rewriteEntrySolvedEvidence prepared
    fixture.requirement missingPremiseEvidence
  expectPreExecutionFault "missing direct-call evidence premise"
    (fun error => match error with
      | .callEvidenceNotSelected caller occurrence requirement goal actual =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            goal = fixture.predicate ∧ actual = implementation)
      | _ => false)
    (validateTampered missingPremise)

  let wrongPremiseGoal : TypedTraitResolution.Evidence :=
    .byImpl fixture.predicate premiseImplementation []
  let wrongPremiseGoalEvidence : SourceInference.PredicateEvidence :=
    .implementation (.byImpl fixture.predicate implementation
      [wrongPremiseGoal])
  let wrongPremiseGoal := rewriteEntrySolvedEvidence prepared
    fixture.requirement wrongPremiseGoalEvidence
  expectPreExecutionFault "direct-call evidence premise goal"
    (fun error => match error with
      | .callEvidenceNotSelected caller occurrence requirement goal actual =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            goal = fixture.predicate ∧ actual = implementation)
      | _ => false)
    (validateTampered wrongPremiseGoal)

  let wrongPremiseImplementation : TypedTraitResolution.Evidence :=
    .byImpl premiseGoal implementation []
  let wrongPremiseImplementationEvidence :
      SourceInference.PredicateEvidence :=
    .implementation (.byImpl fixture.predicate implementation
      [wrongPremiseImplementation])
  let wrongPremiseImplementation := rewriteEntrySolvedEvidence prepared
    fixture.requirement wrongPremiseImplementationEvidence
  expectPreExecutionFault "direct-call evidence premise implementation"
    (fun error => match error with
      | .callEvidenceNotSelected caller occurrence requirement goal actual =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            goal = fixture.predicate ∧ actual = implementation)
      | _ => false)
    (validateTampered wrongPremiseImplementation)

  let constrainedSeed : ValidationFixture := {
    prepared.toValidationFixture with
    plan := {
      prepared.plan with
      seedKeys := fixture.callee :: prepared.plan.seedKeys
    }
  }
  expectPlanValidationFault "constrained public seed"
    (fun error => match error with
      | .unresolvedAssumptions key assumptions =>
          decide (key = fixture.callee ∧ assumptions = [fixture.predicate])
      | _ => false)
    (SourceTypedRuntime.validateExecutablePlan constrainedSeed.plan)

  let constrainedReference : ValidationFixture := {
    prepared.toValidationFixture with
    plan := {
      prepared.plan with
      referenceEdges := {
        caller := prepared.key
        occurrence := fixture.occurrence
        callee := fixture.callee
      } :: prepared.plan.referenceEdges
    }
  }
  match SourceTypedRuntime.validateExecutablePlan constrainedReference.plan with
  | .ok () => pure ()
  | .error error => throw (IO.userError
      s!"constrained first-class reference was rejected: {reprStr error}")

private def specializationNamedInPlan (program : CheckedProgram)
    (prepared : Prepared) (name : String) :
    IO SourceSpecialization.SpecializedFunction := do
  let signature ← signatureNamed program name
  match prepared.plan.specializations.filter fun specialized =>
      specialized.declaration == signature.id with
  | [specialized] => pure specialized
  | specializations => throw (IO.userError
      s!"`{name}` retained {specializations.length} specializations")

private def hasImplementationEvidence
    (specialized : SourceSpecialization.SpecializedFunction) : Bool :=
  specialized.function.solvedRequirements.any fun solved =>
    solved.evidence matches .implementation _

private def hasAssumptionEvidence
    (specialized : SourceSpecialization.SpecializedFunction) : Bool :=
  specialized.function.solvedRequirements.any fun solved =>
    solved.evidence matches .assumption _

/-- A closed root supplies implementation evidence to a generic relay, which
then forwards its own assumption to a second generic callee.  The recursive
case verifies that the same closed dictionary survives a self edge, and the
closure case verifies that deferred code captures the dictionary at creation
rather than borrowing it from its eventual invoker. -/
private def testRuntimeEvidenceForwarding
    (program : CheckedProgram) : IO Unit := do
  let constrainedRoot ← prepareNamed program "constrainedRoot"
  let rootSpecialized ← entrySpecialization constrainedRoot
  assertTrue (rootSpecialized.assumptions.length == 1)
    "ground constrained root lost its retained predicate"
  expectWord "ground constrained root evidence" 59
    (← runPrepared constrainedRoot [.word (word 59)])

  let nested ← prepareNamed program "nestedConstrained"
  let nestedRoot ← entrySpecialization nested
  let relay ← specializationNamedInPlan program nested "relay"
  let keep ← specializationNamedInPlan program nested "keep"
  assertTrue (hasImplementationEvidence nestedRoot &&
      hasAssumptionEvidence relay && relay.assumptions.length == 1 &&
      keep.assumptions.length == 1)
    "nested constrained calls lost their implementation/assumption chain"
  expectWord "nested runtime evidence forwarding" 61
    (← runPrepared nested [.word (word 61)])

  let recursive ← prepareNamed program "recursiveConstrained"
  let repeated ← specializationNamedInPlan program recursive "repeat"
  let selfEdges := recursive.plan.callEdges.filter fun edge =>
    decide (edge.caller = repeated.key ∧ edge.callee = repeated.key)
  assertTrue (selfEdges.length == 1 && hasAssumptionEvidence repeated &&
      repeated.assumptions.length == 1)
    "constrained recursion lost its self edge or caller assumption"
  expectWord "recursive runtime evidence forwarding" 67
    (← runPrepared recursive [.word (word 67)])
  match ← runPrepared recursive [.word (word 67)] 1 with
  | .outOfFuel _ => pure ()
  | result => throw (IO.userError
      s!"constrained recursion ignored its fuel boundary: {reprStr result}")

  let closure ← prepareNamed program "closureConstrained"
  let closureRelay ← specializationNamedInPlan program closure "closureRelay"
  assertTrue (hasAssumptionEvidence closureRelay &&
      closureRelay.assumptions.length == 1)
    "constrained closure lost its retained caller assumption"
  expectWord "captured runtime evidence forwarding" 71
    (← runPrepared closure [.word (word 71)])

  let ordered ← prepareNamed program "orderedConstrained"
  let relayBoth ← specializationNamedInPlan program ordered "relayBoth"
  let keepBoth ← specializationNamedInPlan program ordered "keepBoth"
  assertTrue (relayBoth.assumptions.length == 2 &&
      keepBoth.assumptions.length == 2 &&
      decide (relayBoth.assumptions.reverse = keepBoth.assumptions) &&
      hasAssumptionEvidence relayBoth)
    "callee-ordered runtime evidence lost or reused caller predicate order"
  expectWord "callee-ordered runtime evidence forwarding" 79
    (← runPrepared ordered [.word (word 79)])

private def testQualifiedLocalRequirementValidation
    (program : CheckedProgram) : IO Unit := do
  let fixture ← qualifiedLocalFixture program
  let prepared := fixture.prepared

  let missingActual := rewriteEntryExpressionAt prepared fixture.reference.id
    fun node => { node with requirements := [] }
  expectPreExecutionFault "missing qualified-local actual requirement"
    (fun error => match error with
      | .localSchemeRequirementCountMismatch caller occurrence binder 1 0 =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            binder = fixture.binder.id)
      | _ => false)
    (validateTampered missingActual)

  let missingSolved := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.filter fun solved =>
      solved.id != fixture.actualRequirement
  }
  expectPreExecutionFault "missing qualified-local actual solution"
    (fun error => match error with
      | .missingSolvedRequirement caller occurrence requirement =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            requirement = fixture.actualRequirement)
      | _ => false)
    (validateTampered missingSolved)

  let duplicateSolved := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := fixture.actualSolved :: function.solvedRequirements
  }
  expectPreExecutionFault "duplicate qualified-local actual solutions"
    (fun error => match error with
      | .duplicateSolvedRequirements caller occurrence requirement 2 =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            requirement = fixture.actualRequirement)
      | _ => false)
    (validateTampered duplicateSolved)

  let wrongPredicate : ProgramPredicate := {
    fixture.actualSolved.predicate with subject := .bool
  }
  let predicateMismatch := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.map fun solved =>
      if solved.id == fixture.actualRequirement then
        { solved with predicate := wrongPredicate }
      else
        solved
  }
  expectPreExecutionFault "qualified-local actual predicate mismatch"
    (fun error => match error with
      | .callRequirementPredicateMismatch caller occurrence requirement _ actual =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            requirement = fixture.actualRequirement ∧ actual = wrongPredicate)
      | _ => false)
    (validateTampered predicateMismatch)

  let assumption := rewriteEntrySolvedEvidence prepared
    fixture.actualRequirement (.assumption fixture.actualSolved.predicate)
  expectPreExecutionFault "qualified-local actual assumption evidence"
    (fun error => match error with
      | .missingRuntimeAssumptionEvidence caller occurrence requirement _ =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            requirement = fixture.actualRequirement)
      | _ => false)
    (validateTampered assumption)

  let forgedEvidence : SourceInference.PredicateEvidence :=
    .implementation (.byImpl fixture.actualSolved.predicate
      (.builtin .intWord) [])
  let forged := rewriteEntrySolvedEvidence prepared fixture.actualRequirement
    forgedEvidence
  expectPreExecutionFault "forged qualified-local implementation evidence"
    (fun error => match error with
      | .callEvidenceNotSelected caller occurrence requirement goal _ =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            requirement = fixture.actualRequirement ∧
            goal = fixture.actualSolved.predicate)
      | _ => false)
    (validateTampered forged)

  let duplicateTemplate := rewriteEntryLetBinder prepared fixture.binder.id
    fun binder => {
      binder with
      schemeRequirements := binder.schemeRequirements ++ [fixture.template]
    }
  expectPreExecutionFault "duplicate qualified-local template"
    (fun error => match error with
      | .duplicateLocalSchemeTemplateRequirement caller occurrence binder
          requirement =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            binder = fixture.binder.id ∧
            requirement = fixture.template.templateRequirement)
      | _ => false)
    (validateTampered duplicateTemplate)

  let unusedId : SourceInference.RequirementId := {
    index := fixture.template.templateRequirement.index + 1000000
  }
  let unusedTemplate := rewriteEntryLetBinder prepared fixture.binder.id
    fun binder => {
      binder with
      schemeRequirements := binder.schemeRequirements ++ [{
        fixture.template with templateRequirement := unusedId
      }]
    }
  expectPreExecutionFault "unused qualified-local template"
    (fun error => match error with
      | .unsupportedLocalSchemeTemplateUse caller binder requirement =>
          decide (caller = prepared.key ∧ binder = fixture.binder.id ∧
            requirement = unusedId)
      | _ => false)
    (validateTampered unusedTemplate)

  let escapedCallee := rewriteEntryFunction prepared fun function => {
    function with
    typedBody := {
      function.typedBody with
      roots := .expression fixture.callee :: function.typedBody.roots
    }
  }
  expectPreExecutionFault "escaped constrained declaration reference"
    (fun error => match error with
      | .unsupportedConstrainedDeclarationReference caller call callee =>
          decide (caller = prepared.key ∧ call = fixture.call.id ∧
            callee = fixture.callee)
      | _ => false)
    (validateTampered escapedCallee)

  let escapedInitializer := rewriteEntryFunction prepared fun function => {
    function with
    typedBody := {
      function.typedBody with
      roots := .expression fixture.initializer :: function.typedBody.roots
    }
  }
  expectPreExecutionFault "escaped qualified-local initializer"
    (fun error => match error with
      | .unsupportedQualifiedLocalInitializer caller binder initializer =>
          decide (caller = prepared.key ∧ binder = fixture.binder.id ∧
            initializer = fixture.initializer)
      | _ => false)
    (validateTampered escapedInitializer)

private def testAssignmentRootsAreDeferred
    (program : CheckedProgram) : IO Unit := do
  let assignments ← prepareNamed program "assignments"
  let specialized ← entrySpecialization assignments
  let localBinder ← letBinderNamed specialized "local"
  assertTrue
    (specialized.stageAnalysis.binderStage? localBinder.id ==
      some SourceStageAnalysis.Stage.deferred)
    "a directly assigned local retained a non-deferred stage"

  let capture ← prepareNamed program "sharedCapture"
  let specialized ← entrySpecialization capture
  let captured ← letBinderNamed specialized "captured"
  assertTrue
    (specialized.stageAnalysis.binderStage? captured.id ==
      some SourceStageAnalysis.Stage.deferred)
    "a closure-captured assignment root retained a non-deferred stage"

private def testOperatorMethodNestedInCoercion : IO Unit := do
  let program ← checkedProgram (String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "enum RuntimeBox { Only }",
    "impl Add<RuntimeBox> {",
    "  function add(left: RuntimeBox, right: RuntimeBox) returns (RuntimeBox) {",
    "    return left;",
    "  }",
    "}",
    "trait Coerce<From, To> {",
    "  function coerce(value: From) returns (To);",
    "}",
    "impl Coerce<Bool, RuntimeBox> {",
    "  function coerce(value: Bool) returns (RuntimeBox) {",
    "    let touched: Word = 0;",
    "    touched += 1;",
    "    let box: RuntimeBox = .Only;",
    "    return box + box;",
    "  }",
    "}",
    "function operatorMethodCoercion(value: Bool) returns (RuntimeBox) {",
    "  return value;",
    "}"
  ])
  let prepared ← prepareNamed program "operatorMethodCoercion"
  let initialState : RuntimeState := {
    heap := [{ type := .word, value := none }]
  }
  match ← runPrepared prepared [.bool true] 300000 initialState with
  | .done (.constructed _ []) finalState =>
      match finalState.heap with
      | { type := type, value := none } :: _ =>
          assertTrue (type == Ty.word)
            "nested operator execution changed the sentinel cell type"
          assertTrue (finalState.heap.length > initialState.heap.length)
            "nested operator execution did not share the coercion-method heap"
      | _ => throw (IO.userError
          "nested operator execution changed the sentinel cell")
  | result => throw (IO.userError
      s!"operator method nested in coercion returned {reprStr result}")

private def testRuntimeCoercions (program : CheckedProgram) : IO Unit := do
  let chain ← prepareNamed program "coercionChain"
  match ← runPrepared chain [.bool true] 300000 with
  | .done (.product (.word left) (.word right)) _ =>
      assertTrue (left == word 41 && right == word 41)
        "typed runtime did not compose both selected coercion methods"
  | result => throw (IO.userError
      s!"typed multi-step coercion returned {reprStr result}")
  match ← runPrepared chain [.bool false] 300000 with
  | .done (.product (.word left) (.word right)) _ =>
      assertTrue (left == word 7 && right == word 7)
        "typed runtime changed the false coercion branch"
  | result => throw (IO.userError
      s!"typed multi-step coercion false branch returned {reprStr result}")
  let generic ← prepareNamed program "genericCoercion"
  expectWord "generic caller coercion evidence" 41
    (← runPrepared generic [.bool true] 300000)
  let result ← prepareNamed program "resultCoercion"
  expectWord "expression result coercion" 7
    (← runPrepared result [.bool false] 300000)
  let indirect ← prepareNamed program "indirectCoercion"
  expectWord "indirect argument coercion" 41
    (← runPrepared indirect [.bool true] 300000)

  let specialized ← entrySpecialization chain
  let coercedNode ← match specialized.function.typedBody.nodes.findSome? fun
      | .expression node =>
          if node.coercions.isEmpty then none else some node
      | .statement _ => none with
    | some node => pure node
    | none => throw (IO.userError "coercionChain lost its coercion path")
  let firstStep ← match coercedNode.coercions with
    | step :: _ => pure step
    | [] => throw (IO.userError "coercionChain retained an empty path")
  let reversedMethodRequirements ← match firstStep.methodRequirements with
    | [left, right] => pure [right, left]
    | requirements => throw (IO.userError
        s!"coercionChain retained {requirements.length} method requirements")
  let reordered := rewriteEntryExpressionAt chain coercedNode.id fun node =>
    let coercions := match node.coercions with
      | step :: rest =>
          { step with methodRequirements := reversedMethodRequirements } :: rest
      | [] => []
    { node with
      coercions
      requirements := coercions.flatMap (·.requirements)
    }
  expectPreExecutionFault "reordered coercion method evidence"
    (fun error => match error with
      | .callRequirementPredicateMismatch caller occurrence _ _ _ =>
          decide (caller = chain.key ∧ occurrence = coercedNode.id)
      | _ => false)
    (validateTampered reordered)

  let duplicated := rewriteEntryExpressionAt chain coercedNode.id fun node =>
    let coercions := match node.coercions with
      | step :: rest =>
          match step.methodRequirements with
          | requirement :: requirements =>
              { step with
                methodRequirements := requirement :: requirement :: requirements
              } :: rest
          | [] => step :: rest
      | [] => []
    { node with
      coercions
      requirements := coercions.flatMap (·.requirements)
    }
  expectPreExecutionFault "duplicate coercion method evidence"
    (fun error => match error with
      | .duplicateCoercionRequirement caller occurrence _ =>
          decide (caller = chain.key ∧ occurrence = coercedNode.id)
      | _ => false)
    (validateTampered duplicated)

private def testAll : IO Unit := do
  let program ← checkedProgram source
  testNominalConstructionAndRecursiveCalls program
  testNestedMatchingAndCalls program
  testAssignmentsMappingsAndControl program
  testClosuresOrderProxyAndFuel program
  testLocalLetPolymorphism program
  testQualifiedLocalLetPolymorphism program
  testContextualLocalGenericCalls program
  testContextualCallRequirementValidation program
  testRuntimeEvidenceForwarding program
  testQualifiedLocalRequirementValidation program
  testNominalInputValidation program
  testStagedRuntimeTypesAndEffects program
  testTamperedExecutableMetadata program
  testIndirectArgumentCountMetadata program
  testIndirectEndpointMetadata program
  testAssignmentRootsAreDeferred program
  testOperatorMethodNestedInCoercion
  testRuntimeCoercions program
  IO.println "phase-7 typed-source runtime GREEN"

end Runtime

/-- Exercise the phase-7 execution surface through its real frontend and
specialization plan. -/
def testSourceTypedRuntime : IO Unit :=
  Runtime.testAll

end Tests.SourceTypedRuntime
end

section
-- leanmerge: from Solcore.Test.SourceTypedRuntimeFirstClassEvidence
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Checked-source regressions for evidence-bearing first-class functions,
executed through a cached source-compatible Core artifact. -/

set_option autoImplicit false

namespace Tests.SourceTypedRuntimeFirstClassEvidence

open Solcore Solcore.Frontend Solcore.TypeSystem
open Solcore.Frontend.SourceTypedRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{
    path := "main.solc"
    content := String.intercalate "\n" [
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
      "}"
    ]
  }]
  externalLibraries := []
}

private def checkedProgram : IO CheckedProgram := do
  match checkProgram workspace with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"first-class evidence fixture failed checking: {reprStr errors}")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature :=
  match program.signatures.functions.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one signature named `{name}`, found {signatures.length}")

private structure Prepared where
  program : CheckedProgram
  plan : SourceSpecializationWorklist.Plan
  key : SourceSpecialization.SpecializationKey
  compiled : SourceCoreUnifiedCompilation.Compiled

private def prepareNamed (program : CheckedProgram) (name : String) :
    IO Prepared := do
  let signature ← signatureNamed program name
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 32 with
  | .ok (.complete plan) =>
      match plan.seedKeys with
      | [key] => do
          let compiled ← SourceCoreUnifiedCorpusSupport.preparePlan name program plan key
          pure { program, plan, key, compiled }
      | keys => throw (IO.userError
          s!"`{name}` retained {keys.length} seed keys")
  | .ok outcome => throw (IO.userError
      s!"`{name}` specialization did not complete: {reprStr outcome}")
  | .error error => throw (IO.userError
      s!"`{name}` specialization failed: {reprStr error}")

private def runPrepared (prepared : Prepared)
    (arguments : List Value := []) : IO RunResult :=
  SourceCoreUnifiedCorpusSupport.observe prepared.compiled prepared.key arguments

private def expectWord (label : String) (expected : Nat) : RunResult → IO Unit
  | .done (.word actual) _ =>
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def specializationNamed (prepared : Prepared) (name : String) :
    IO SourceSpecialization.SpecializedFunction := do
  let signature ← signatureNamed prepared.program name
  match prepared.plan.specializations.filter fun specialized =>
      specialized.declaration == signature.id with
  | [specialized] => pure specialized
  | specializations => throw (IO.userError
      s!"`{name}` retained {specializations.length} specializations")

private def testConstrainedGlobalValue (program : CheckedProgram) : IO Unit := do
  let valueFactory ← prepareNamed program "globalValue"
  assertTrue (valueFactory.plan.referenceEdges.length == 1)
    "constrained declaration value lost its reference edge"
  let (key, evidence) ← match ← runPrepared valueFactory with
    | .done (.global key evidence) _ => pure (key, evidence)
    | result => throw (IO.userError
        s!"globalValue returned {reprStr result}")
  let target ← match valueFactory.plan.specializations.filter fun specialized =>
      decide (specialized.key = key) with
    | [specialized] => pure specialized
    | specializations => throw (IO.userError
        s!"globalValue retained {specializations.length} reference targets")
  assertTrue (decide (evidence.goals = target.assumptions) &&
      evidence.length == 1)
    "constrained declaration value did not retain its ordered evidence"

  let aliasCall ← prepareNamed program "globalAliasCall"
  expectWord "constrained global alias" 41
    (← runPrepared aliasCall [.word (word 41)])

  let applyStored ← prepareNamed program "applyStored"
  expectWord "evidence-bearing global input" 49
    (← runPrepared applyStored [.global key evidence, .word (word 49)])
  match ← runPrepared applyStored [.global key [], .word (word 49)] with
  | .fault (.typeMismatch _ _) _ => pure ()
  | result => throw (IO.userError
      s!"global input with missing evidence was accepted: {reprStr result}")

private def testPredicateReordering (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "orderedAliasCall"
  let factory ← specializationNamed prepared "orderedFactory"
  let target ← specializationNamed prepared "keepBoth"
  assertTrue (factory.assumptions.length == 2 &&
      target.assumptions.length == 2 &&
      decide (factory.assumptions.reverse = target.assumptions))
    "predicate-reordering fixture lost its opposite declaration orders"
  expectWord "predicate-reordered declaration value" 43
    (← runPrepared prepared [.word (word 43)])

private def testQualifiedLocalAliasEscape
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "qualifiedLocalAliasCall"
  let factory ← specializationNamed prepared "localFactory"
  let forwarded := prepared.plan.callEdges.filter fun edge =>
    decide (edge.caller = factory.key)
  assertTrue (factory.assumptions.length == 1 &&
      forwarded.length == 1)
    "qualified local escape lost its caller assumption or forwarded call"
  expectWord "qualified local alias escape" 45
    (← runPrepared prepared [.word (word 45)])

private def testGenericRecursiveClosure
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "genericRecursiveClosureCall"
  let recursive ← specializationNamed prepared "repeat"
  let selfEdges := prepared.plan.callEdges.filter fun edge =>
    decide (edge.caller = recursive.key ∧ edge.callee = recursive.key)
  assertTrue (recursive.assumptions.length == 1 && selfEdges.length == 1)
    "escaped generic closure lost recursive evidence forwarding"
  expectWord "generic recursive closure" 47
    (← runPrepared prepared [.word (word 47)])

def testSourceTypedRuntimeFirstClassEvidence : IO Unit := do
  let program ← checkedProgram
  testConstrainedGlobalValue program
  testPredicateReordering program
  testQualifiedLocalAliasEscape program
  testGenericRecursiveClosure program

end Tests.SourceTypedRuntimeFirstClassEvidence
end

section
-- leanmerge: from Solcore.Test.SourceTypedRuntimeOperators
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runWithValidationFuel

/-!
Focused end-to-end regressions for evidence-selected unary and binary methods
in cached source-compatible Core code.

The fixtures cross raw workspace checking and finite specialization before
execution.  They also exercise method-local mutation, helper closure, caller-
owned method predicates, result coercion, and rejection before heap mutation.
-/

set_option autoImplicit false

namespace Tests.SourceTypedRuntimeOperators

open Solcore Solcore.Frontend Solcore.TypeSystem

namespace Runtime

open Solcore.Frontend.SourceTypedRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError "invalid typed-runtime operator module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"typed-runtime operator fixture failed checking: {reprStr errors}")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature :=
  match program.signatures.functions.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one signature named `{name}`, found {signatures.length}")

private structure ValidationFixture where
  program : CheckedProgram
  plan : SourceSpecializationWorklist.Plan
  key : SourceSpecialization.SpecializationKey

private structure Prepared extends ValidationFixture where
  compiled : SourceCoreUnifiedCompilation.Compiled

private def prepareNamed (program : CheckedProgram) (name : String) :
    IO Prepared := do
  let signature ← signatureNamed program name
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 64 with
  | .ok (.complete plan) =>
      match plan.seedKeys with
      | [key] => do
          let compiled ← SourceCoreUnifiedCorpusSupport.preparePlan name program plan key
          pure { program, plan, key, compiled }
      | keys => throw (IO.userError
          s!"`{name}` retained {keys.length} seed keys")
  | .ok outcome => throw (IO.userError
      s!"`{name}` specialization did not complete: {reprStr outcome}")
  | .error error => throw (IO.userError
      s!"`{name}` specialization failed: {reprStr error}")

private def runPrepared (prepared : Prepared) : IO RunResult :=
  SourceCoreUnifiedCorpusSupport.observe prepared.compiled prepared.key

private def expectWordAndShallowHeap (label : String) (expected : Nat)
    (plan : SourceSpecializationWorklist.Plan) : RunResult → IO Unit
  | .done (.word actual) state => do
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
      for cell in state.heap do
        match cell.value with
        | none => pure ()
        | some value =>
            assertTrue (decide (value.type? plan = some cell.type))
              s!"{label} left an initialized cell with a mismatched type"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def expectBoolAndShallowHeap (label : String) (expected : Bool)
    (plan : SourceSpecializationWorklist.Plan) : RunResult → IO Unit
  | .done (.bool actual) state => do
      assertTrue (actual == expected) s!"{label} returned the wrong Bool"
      for cell in state.heap do
        match cell.value with
        | none => pure ()
        | some value =>
            assertTrue (decide (value.type? plan = some cell.type))
              s!"{label} left an initialized cell with a mismatched type"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def source : String := String.intercalate "\n" [
  "trait Witness<T> {}",
  "trait Add<T> {",
  "  function add(left: T, right: T) returns (T) where T: Witness;",
  "}",
  "trait BitNot<T> {",
  "  function bnot(value: T) returns (T) where T: Witness;",
  "}",
  "trait Eq<T> {",
  "  function eq(left: T, right: T) returns (Bool) where T: Witness;",
  "}",
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "enum Token { A, B, C }",
  "impl Witness<Token> {}",
  "impl Witness<Word> {}",
  "function rotate(value: Token) returns (Token) {",
  "  match (value) {",
  "    case .A { return .B; }",
  "    case .B { return .C; }",
  "    default { return .A; }",
  "  }",
  "}",
  "impl Add<Token> {",
  "  function add(left: Token, right: Token) returns (Token)",
  "      where Token: Witness {",
  "    let scratch: mapping(Word => Bool);",
  "    scratch[0] = false;",
  "    scratch[0] = true;",
  "    return scratch[0] ? rotate(right) : left;",
  "  }",
  "}",
  "impl BitNot<Token> {",
  "  function bnot(value: Token) returns (Token)",
  "      where Token: Witness {",
  "    let result: Token = value;",
  "    result = rotate(result);",
  "    return result;",
  "  }",
  "}",
  "impl Eq<Token> {",
  "  function eq(left: Token, right: Token) returns (Bool)",
  "      where Token: Witness {",
  "    return true;",
  "  }",
  "}",
  "impl Eq<Word> {",
  "  function eq(left: Word, right: Word) returns (Bool)",
  "      where Word: Witness {",
  "    return false;",
  "  }",
  "}",
  "impl Coerce<Token, Word> {",
  "  function coerce(value: Token) returns (Word) {",
  "    match (value) {",
  "      case .C { return 59; }",
  "      default { return 0; }",
  "    }",
  "  }",
  "}",
  "function viaAdd<T>(left: T, right: T) returns (T)",
  "    where T: Add, T: Witness {",
  "  return left + right;",
  "}",
  "function viaBitNot<T>(value: T) returns (T)",
  "    where T: BitNot, T: Witness {",
  "  return ~value;",
  "}",
  "function viaEq<T>(left: T, right: T) returns (Bool)",
  "    where T: Eq, T: Witness {",
  "  return left == right;",
  "}",
  "function binaryEntry() returns (Word) {",
  "  let left: Token = .A;",
  "  let right: Token = .B;",
  "  let result: Token = viaAdd(left, right);",
  "  match (result) {",
  "    case .C { return 31; }",
  "    default { return 0; }",
  "  }",
  "}",
  "function unaryEntry() returns (Word) {",
  "  let value: Token = .C;",
  "  let result: Token = viaBitNot(value);",
  "  match (result) {",
  "    case .A { return 41; }",
  "    default { return 0; }",
  "  }",
  "}",
  "function equalityEntry() returns (Bool) {",
  "  let left: Token = .A;",
  "  let right: Token = .B;",
  "  return viaEq(left, right);",
  "}",
  "function wordEqualityEntry() returns (Bool) {",
  "  let left: Word = 7;",
  "  let right: Word = 7;",
  "  return viaEq(left, right);",
  "}",
  "function coercedOperatorEntry() returns (Word) {",
  "  let left: Token = .A;",
  "  let right: Token = .B;",
  "  return left + right;",
  "}"
]

private def specializationNamed (prepared : Prepared) (name : String) :
    IO SourceSpecialization.SpecializedFunction := do
  let signature ← signatureNamed prepared.program name
  match prepared.plan.specializations.filter fun specialized =>
      decide (specialized.key.declaration = signature.id) with
  | [specialized] => pure specialized
  | specializations => throw (IO.userError
      s!"expected one `{name}` specialization, found {specializations.length}")

private def addNode
    (specialized : SourceSpecialization.SpecializedFunction) :
    IO SourceInference.ExpressionNode :=
  match specialized.function.typedBody.nodes.filterMap fun
      | .expression node@{ form := .binary _ .add _, .. } => some node
      | _ => none with
  | [node] => pure node
  | nodes => throw (IO.userError
      s!"expected one selected addition, found {nodes.length}")

private def equalityNode
    (specialized : SourceSpecialization.SpecializedFunction) :
    IO SourceInference.ExpressionNode :=
  match specialized.function.typedBody.nodes.filterMap fun
      | .expression node@{ form := .binary _ .equal _, .. } => some node
      | _ => none with
  | [node] => pure node
  | nodes => throw (IO.userError
      s!"expected one selected equality, found {nodes.length}")

private def exactSolved (specialized : SourceSpecialization.SpecializedFunction)
    (requirement : SourceInference.RequirementId) :
    IO SourceInference.SolvedRequirement :=
  match specialized.function.solvedRequirements.filter fun solved =>
      solved.id == requirement with
  | [solved] => pure solved
  | solved => throw (IO.userError
      s!"expected one solved requirement, found {solved.length}")

private def predicateTraitName? (program : CheckedProgram)
    (predicate : ProgramPredicate) : Option String :=
  match predicate.trait with
  | .builtin _ => none
  | .declaration id =>
      (program.signatures.traits.find? fun trait =>
        decide (trait.id = id)).map (fun trait => trait.name)

private structure AddAssumptionFixture where
  prepared : Prepared
  specialized : SourceSpecialization.SpecializedFunction
  node : SourceInference.ExpressionNode
  primaryRequirement : SourceInference.RequirementId
  methodRequirement : SourceInference.RequirementId
  primarySolved : SourceInference.SolvedRequirement
  methodSolved : SourceInference.SolvedRequirement

private def addAssumptionFixture (program : CheckedProgram) :
    IO AddAssumptionFixture := do
  let prepared ← prepareNamed program "binaryEntry"
  let specialized ← specializationNamed prepared "viaAdd"
  let node ← addNode specialized
  let (primaryRequirement, methodRequirement) ← match node.requirements with
    | [primary, method] => pure (primary, method)
    | requirements => throw (IO.userError
        s!"selected addition retained {requirements.length} requirements")
  let primarySolved ← exactSolved specialized primaryRequirement
  let methodSolved ← exactSolved specialized methodRequirement
  let primaryAssumption := match primarySolved.evidence with
    | .assumption predicate => predicate == primarySolved.predicate
    | .implementation _ => false
  let methodAssumption := match methodSolved.evidence with
    | .assumption predicate => predicate == methodSolved.predicate
    | .implementation _ => false
  assertTrue (primaryAssumption && methodAssumption &&
      predicateTraitName? program primarySolved.predicate == some "Add" &&
      predicateTraitName? program methodSolved.predicate == some "Witness")
    "generic addition did not retain Add then Witness caller assumptions"
  pure {
    prepared
    specialized
    node
    primaryRequirement
    methodRequirement
    primarySolved
    methodSolved
  }

private def rewriteSpecializationFunction (prepared : Prepared)
    (key : SourceSpecialization.SpecializationKey)
    (rewrite : SourceInference.CheckedFunction → SourceInference.CheckedFunction) :
    ValidationFixture :=
  let specializations := prepared.plan.specializations.map fun specialized =>
    if specialized.key = key then
      { specialized with function := rewrite specialized.function }
    else
      specialized
  { program := prepared.program, key := prepared.key,
    plan := { prepared.plan with specializations } }

private def rewriteSpecializationExpression (prepared : Prepared)
    (key : SourceSpecialization.SpecializationKey)
    (target : SourceInference.ExpressionId)
    (rewrite : SourceInference.ExpressionNode →
      SourceInference.ExpressionNode) : ValidationFixture :=
  rewriteSpecializationFunction prepared key fun function => {
    function with
    typedBody := {
      function.typedBody with
      nodes := function.typedBody.nodes.map fun node =>
        match node with
        | .expression expression =>
            if expression.id == target then .expression (rewrite expression)
            else node
        | .statement _ => node
    }
  }

private def expectSentinelFault (label : String)
    (accept : RuntimeError → Bool) :
    Except RuntimeError Unit × RuntimeState → IO Unit
  | (.error error, { heap := [{ type := actualType, value := none }] }) => do
      assertTrue (accept error) s!"{label} reported {reprStr error}"
      assertTrue (actualType == Ty.word)
        s!"{label} changed the sentinel type to {reprStr actualType}"
  | (.error error, state) => throw (IO.userError
      s!"{label} changed the initial state: {reprStr error}, {reprStr state}")
  | (.ok (), _) => throw (IO.userError
      s!"{label} did not reject during pure plan validation")

/-- The validator returns an actual rejection; the caller's sentinel remains
inert data. No executable artifact or source execution is produced for the
rewritten plan. -/
private def validateTampered (prepared : ValidationFixture) :
    Except RuntimeError Unit × RuntimeState :=
  let initialState : RuntimeState := {
    heap := [{ type := .word, value := none }]
  }
  (SourceCompilationPlan.validateExecutablePlanEvidence prepared.program prepared.plan,
    initialState)

private def testSelectedOperatorMethods (program : CheckedProgram) : IO Unit := do
  let binary ← prepareNamed program "binaryEntry"
  expectWordAndShallowHeap "selected binary operator method" 31 binary.plan
    (← runPrepared binary)
  let unary ← prepareNamed program "unaryEntry"
  expectWordAndShallowHeap "selected unary operator method" 41 unary.plan
    (← runPrepared unary)
  let equality ← prepareNamed program "equalityEntry"
  expectBoolAndShallowHeap "selected Bool-result operator method" true
    equality.plan (← runPrepared equality)
  let wordEquality ← prepareNamed program "wordEqualityEntry"
  expectBoolAndShallowHeap "selected Word equality override" false
    wordEquality.plan (← runPrepared wordEquality)

private def testOperatorResultCoercion (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "coercedOperatorEntry"
  expectWordAndShallowHeap "operator raw result followed by Coerce" 59
    prepared.plan (← runPrepared prepared)

private def testPublicCompiler (program : CheckedProgram) : IO Unit := do
  let compiled ← SourceCompilerFeatureSupport.compileNamed program "binaryEntry" []
    {specializationBudget := 64, compilationFuel := 1000}
  let invoked ← compiled.invoke [] {inputValidationFuel := 64, executionFuel := 300000}
  match invoked.outcome with
  | .succeeded completion =>
      assertTrue (completion.value == .word (word 31) && completion.session.heapSize > invoked.initial.heapSize)
        "public stateful operator execution lost its result or heap effects"
  | _ => throw (IO.userError "public stateful operator execution did not succeed")
  compiled.checkResume [] (.word (word 31)) 0

private def testOperatorPreflight (program : CheckedProgram) : IO Unit := do
  let fixture ← addAssumptionFixture program
  let missingMethodRequirement := rewriteSpecializationExpression
    fixture.prepared fixture.specialized.key fixture.node.id fun node =>
      { node with requirements := [fixture.primaryRequirement] }
  expectSentinelFault "missing binary method requirement"
    (fun error => match error with
      | .binaryRequirementCountMismatch caller occurrence 2 1 =>
          decide (caller = fixture.specialized.key ∧
            occurrence = fixture.node.id)
      | _ => false)
    (validateTampered missingMethodRequirement)

  let mismatchedEvidence := rewriteSpecializationFunction fixture.prepared
    fixture.specialized.key fun function => {
      function with
      solvedRequirements := function.solvedRequirements.map fun solved =>
        if solved.id == fixture.methodRequirement then
          { solved with evidence := .assumption fixture.primarySolved.predicate }
        else
          solved
    }
  expectSentinelFault "mismatched binary method evidence"
    (fun error => match error with
      | .callRequirementEvidenceGoalMismatch caller occurrence requirement
          expected actual =>
          decide (caller = fixture.specialized.key ∧
            occurrence = fixture.node.id ∧
            requirement = fixture.methodRequirement ∧
            expected = fixture.methodSolved.predicate ∧
            actual = fixture.primarySolved.predicate)
      | _ => false)
    (validateTampered mismatchedEvidence)

  let equalityPrepared ← prepareNamed program "equalityEntry"
  let equalitySpecialized ← specializationNamed equalityPrepared "viaEq"
  let equality ← equalityNode equalitySpecialized
  let equalitySubject ← match equality.requirements with
    | primary :: _ => do
        let solved ← exactSolved equalitySpecialized primary
        pure solved.predicate.subject
    | [] => throw (IO.userError
        "selected equality retained no primary requirement")
  let strippedEquality := rewriteSpecializationExpression equalityPrepared
    equalitySpecialized.key equality.id fun node =>
      { node with requirements := [] }
  expectSentinelFault "stripped custom equality requirements"
    (fun error => match error with
      | .runtimeBinaryInputTypesMismatch caller occurrence expected actual =>
          decide (caller = equalitySpecialized.key ∧
            occurrence = equality.id ∧
            expected = [Ty.word, Ty.word] ∧
            actual = [equalitySubject, equalitySubject])
      | _ => false)
    (validateTampered strippedEquality)

  let wordEqualityPrepared ← prepareNamed program "wordEqualityEntry"
  let wordEqualitySpecialized ← specializationNamed wordEqualityPrepared "viaEq"
  let wordEquality ← equalityNode wordEqualitySpecialized
  let wordRequirement ← match wordEquality.requirements with
    | [primary, _method] => pure primary
    | requirements => throw (IO.userError
        s!"specialized Word equality retained {requirements.length} requirements")
  let wordSolved ← exactSolved wordEqualitySpecialized wordRequirement
  assertTrue (decide (wordSolved.predicate.subject = Ty.word))
    "generic equality did not specialize its trait requirement to Word"
  let strippedWordEquality := rewriteSpecializationExpression
    wordEqualityPrepared wordEqualitySpecialized.key wordEquality.id fun node =>
      { node with requirements := [] }
  expectSentinelFault "stripped specialized Word equality requirements"
    (fun error => match error with
      | .nonCanonicalInputPlan => true
      | _ => false)
    (validateTampered strippedWordEquality)

private def testAll : IO Unit := do
  let program ← checkedProgram source
  testSelectedOperatorMethods program
  testOperatorPreflight program
  testOperatorResultCoercion program
  testPublicCompiler program
  IO.println "cached Core operators and pure metadata preflight GREEN"

end Runtime

def testSourceTypedRuntimeOperators : IO Unit :=
  Runtime.testAll

end Tests.SourceTypedRuntimeOperators
end

section
-- leanmerge: from Solcore.Test.SourceTypedRuntimeStateInteractions
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-!
End-to-end regressions for interactions between typed source execution,
polymorphism, trait evidence, coercions, closures, mutable cells, mappings,
and proxies.

Each case enters through the raw-workspace checker, builds the finite
specialization plan, and caches its Core artifact before execution. The fixtures
use only source forms supported by the upstream Solcore frontend; in particular,
proxy values are used as mapping keys rather than treating enum payloads as
named fields.
-/

set_option autoImplicit false

namespace Tests.SourceTypedRuntimeStateInteractions

open Solcore Solcore.Frontend Solcore.TypeSystem

namespace Runtime

open Solcore.Frontend.SourceTypedRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"state-interaction fixture failed checking: {reprStr errors}")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature :=
  match program.signatures.functions.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one signature named `{name}`, found {signatures.length}")

private structure Prepared where
  program : CheckedProgram
  plan : SourceSpecializationWorklist.Plan
  key : SourceSpecialization.SpecializationKey
  compiled : SourceCoreUnifiedCompilation.Compiled

private def prepareNamed (program : CheckedProgram) (name : String)
    (budget : Nat := 64) : IO Prepared := do
  let signature ← signatureNamed program name
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] budget with
  | .ok (.complete plan) =>
      match plan.seedKeys with
      | [key] => do
          let compiled ← SourceCoreUnifiedCorpusSupport.preparePlan name program plan key
          pure { program, plan, key, compiled }
      | keys => throw (IO.userError
          s!"`{name}` retained {keys.length} seed keys")
  | .ok outcome => throw (IO.userError
      s!"`{name}` specialization did not complete: {reprStr outcome}")
  | .error error => throw (IO.userError
      s!"`{name}` specialization failed: {reprStr error}")

private def runPrepared (prepared : Prepared)
    (arguments : List Value := []) (fuel : Nat := 300000) : IO RunResult :=
  SourceCoreUnifiedCorpusSupport.observe prepared.compiled prepared.key arguments fuel

private def expectShallowHeap (label : String)
    (plan : SourceSpecializationWorklist.Plan) (state : RuntimeState) : IO Unit := do
  for cell in state.heap do
    match cell.value with
    | none => pure ()
    | some value =>
        assertTrue (decide (value.type? plan = some cell.type))
          s!"{label} left an initialized cell with a mismatched type"

private def expectWordAndShallowHeap (label : String) (expected : Nat)
    (plan : SourceSpecializationWorklist.Plan) : RunResult → IO Unit
  | .done (.word actual) state => do
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
      expectShallowHeap label plan state
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

/-- The binder of the local `name` declared in the checked source of
`function`. -/
private def localBinderNamed (program : CheckedProgram) (function name : String) :
    IO Resolved.LocalId := do
  let signature ← signatureNamed program function
  match program.functions.find? (·.declaration == signature.id) with
  | some checked =>
      match checked.typedBody.nodes.filterMap (fun
          | .statement { form := .letDecl binder _, .. } =>
              if binder.name == name then some binder.id else none
          | _ => none) with
      | [binder] => pure binder
      | binders => throw (IO.userError
          s!"expected one local `{name}` in `{function}`, found {binders.length}")
  | none => throw (IO.userError s!"checked source of `{function}` missing")

private def source : String := String.intercalate "\n" [
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

/-- `mutate` writes its own copies of `total` and `table`: the call returns 3,
while the enclosing `total` stays 1 and `table[7]` stays 0. -/
private def testGenericConstrainedCapturedState
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "capturedStateEntry"
  expectWordAndShallowHeap "generic constrained captured-copy mutation" 4
    prepared.plan (← runPrepared prepared [.word (word 19)])

private def testStatefulCoercionMethod
    (program : CheckedProgram) : IO Unit := do
  let mapping ← prepareNamed program "coercionMapping"
  expectWordAndShallowHeap "stateful coercion in mapping assignment (true)" 42
    mapping.plan (← runPrepared mapping [.bool true])
  expectWordAndShallowHeap "stateful coercion in mapping assignment (false)" 8
    mapping.plan (← runPrepared mapping [.bool false])

  let result ← prepareNamed program "coercionResult"
  expectWordAndShallowHeap "stateful coercion in function result (true)" 42
    result.plan (← runPrepared result [.bool true])
  expectWordAndShallowHeap "stateful coercion in function result (false)" 8
    result.plan (← runPrepared result [.bool false])

  /- The returned closure keeps the method's `scratch` as it was when the
  closure was created, and each call starts again from it. -/
  let captured ← prepareNamed program "coercionCapturedState"
  expectWordAndShallowHeap "coercion closure restarts from its method state (true)" 84
    captured.plan (← runPrepared captured [.bool true])
  expectWordAndShallowHeap "coercion closure restarts from its method state (false)" 16
    captured.plan (← runPrepared captured [.bool false])

private def testGenericProxyMappingKey
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "proxyKeyEntry"
  expectWordAndShallowHeap "generic proxy mapping key" 73
    prepared.plan (← runPrepared prepared [.word (word 5)])

/-- `loop` is assigned after the closure is created, so the closure's copy of
`loop` is uninitialized: the first recursive call faults on it before any call
reaches `retain`. -/
private def testRecursiveClosureSelfCellAndEvidence
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "recursiveClosureEntry"
  let loop ← localBinderNamed program "recurseClosure" "loop"
  match ← runPrepared prepared [.word (word 67)] with
  | .fault (.uninitializedLocal binder) state => do
      assertTrue (binder == loop)
        "recursive closure self-cell faulted on another binder"
      expectShallowHeap "recursive closure self-cell" prepared.plan state
  | result => throw (IO.userError
      s!"recursive closure self-cell did not fault on its uninitialized copy: {reprStr result}")

private def testAll : IO Unit := do
  let program ← checkedProgram source
  testGenericConstrainedCapturedState program
  testStatefulCoercionMethod program
  testGenericProxyMappingKey program
  testRecursiveClosureSelfCellAndEvidence program
  IO.println "cached Core source state interactions GREEN"

end Runtime

/-- Exercise stateful interactions through checked source-compatible Core code. -/
def testSourceTypedRuntimeStateInteractions : IO Unit :=
  Runtime.testAll

end Tests.SourceTypedRuntimeStateInteractions
end
