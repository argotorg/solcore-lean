import Solcore.Frontend.SourceCompiler
import Solcore.Frontend.SourceCore.Internal.DirectLinking
import Solcore.Test.Frontend.Source.CompilerFeatureSupport

/-!
# A trait method called by its name, compiled

No source produces `ExpressionForm.methodCall` yet, so each test checks a program and then rewrites
one node of a function's checked body into the form, keeping its children and type. The compiler
calls the implementation method that the node's first requirement selects: the native compiler as a
compiled function, the direct linker inline.

- **Both compilers, in generic code** (`testGeneric`): `left + right` under `T: Add` becomes
  `Add.add(left, right)` at the same requirement, and gives the operator's results; a direct call
  `probe(x, y, z)` under `a: Mix<b>` becomes `Mix.mix(x, y, z)`, a method of a trait of two
  parameters, which no operator reaches, at the function's own predicate, and gives the method's
  results. Each caller proves its requirement by an implementation.
- **A fault and the arguments' order** (`testFaults`, the native compiler): `Bad.D(a) + Bad.D(b)` as
  `Add.add`, whose body reads an uninitialized local, faults with the operator's token and
  diagnostic; of two faulting arguments the left one's fault is the call's, as it is the operator's;
  and `Mix.mix`'s three arguments run left to right, as a direct call's do: the first faulting one
  gives the call's diagnostic, at the first and at the second argument.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Tests.SourceCoreSelectedMethodCalls

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Tests.SourceCompilerFeatureSupport

private def maximum : Nat := 2 ^ 256 - 1

private def workspace (lines : List String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" ("pragma solcore;" :: lines) }]
  externalLibraries := []
}

private def check (label : String) (lines : List String) : IO CheckedProgram :=
  get s!"{label}: check" (Frontend.checkProgram (workspace lines) 1000)

private def signatureNamed (program : CheckedProgram) (name : String) : IO ProgramFunctionSignature :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure signature
  | _ => throw (IO.userError s!"{name}: declaration missing")

private def checkedNamed (program : CheckedProgram) (name : String) : IO CheckedFunction := do
  let signature ← signatureNamed program name
  match program.functions.find? (·.declaration == signature.id) with
  | some function => pure function
  | none => throw (IO.userError s!"{name}: checked body missing")

private def traitNamed (program : CheckedProgram) (name : String) : IO ProgramTraitSignature :=
  match program.signatures.traits.filter (·.name == name) with
  | [trait] => pure trait
  | _ => throw (IO.userError s!"trait {name} missing")

private def replaceFunction (program : CheckedProgram) (function : CheckedFunction) : CheckedProgram :=
  { program with functions := program.functions.map fun old =>
      if old.declaration == function.declaration then function else old }

/-- `function`'s one `+` with requirements, called instead as `Add.add` by its name: the same
node, children, requirements and type. -/
private def operatorAsMethodCall (program : CheckedProgram) (name : String) : IO CheckedProgram := do
  let function ← checkedNamed program name
  let trait ← traitNamed program "Add"
  let operators := function.typedBody.nodes.filter fun
    | .expression { form := .binary _ .add _, requirements := _ :: _, .. } => true
    | _ => false
  require (operators.length == 1) s!"{name}: not one required `+`"
  pure (replaceFunction program { function with
    typedBody := { function.typedBody with nodes := function.typedBody.nodes.map fun
      | .expression node => match node.form, node.requirements with
        | .binary left .add right, _ :: _ =>
            .expression { node with form := .methodCall trait.id "add" [left, right] }
        | _, _ => .expression node
      | other => other } })

/-- `function`'s direct call of `probe`, called instead as `Mix.mix` by its name at a new
requirement: the function's own `Mix` predicate where it declares one, or else `Mix` at the first
two arguments' types, resolved by the program's own rules. The callee's reference, no longer used,
leaves the body. -/
private def callAsMethodCall (program : CheckedProgram) (name : String) : IO CheckedProgram := do
  let signature ← signatureNamed program name
  let function ← checkedNamed program name
  let trait ← traitNamed program "Mix"
  let source := function.typedBody
  let (call, callee, arguments) ← match source.nodes.findSome? fun
      | .expression node => match node.form with
        | .call callee arguments (.declaration _) => match source.lookupExpression? callee with
          | some { form := .reference "probe" _, .. } => some (node, callee, arguments)
          | _ => none
        | _ => none
      | _ => none with
    | some found => pure found
    | none => throw (IO.userError s!"{name}: the call of probe is missing")
  let (goal, evidence) ← match signature.scheme.predicates.find? (·.trait == .declaration trait.id) with
    | some declared => pure (declared, PredicateEvidence.assumption declared)
    | none => do
        let types ← arguments.mapM fun argument => match source.lookupExpression? argument with
          | some node => pure node.type
          | none => throw (IO.userError s!"{name}: an argument of probe is missing")
        let (subject, second) ← match types with
          | subject :: second :: _ => pure (subject, second)
          | _ => throw (IO.userError s!"{name}: probe takes fewer than two arguments")
        let goal : ProgramPredicate := { trait := .declaration trait.id, subject, arguments := [second] }
        match (TypedTraitResolution.resolve program.signatures.resolutionRules 32 goal).outcome with
        | .success evidence => pure (goal, PredicateEvidence.implementation evidence)
        | _ => throw (IO.userError s!"{name}: Mix is not resolved at the arguments' types")
  let fresh : RequirementId := ⟨(function.solvedRequirements.map (·.id.index)).foldl max 0 + 1⟩
  let node := { call with form := .methodCall trait.id "mix" arguments, requirements := [fresh] }
  pure (replaceFunction program { function with
    solvedRequirements := function.solvedRequirements ++ [{ id := fresh, predicate := goal, evidence }]
    typedBody := { source with nodes := source.nodes.filterMap fun
      | .expression old =>
          if old.id == call.id then some (.expression node)
          else if old.id == callee then none
          else some (.expression old)
      | other => some other } })

/-- An input of a test row, a word or a flag. -/
private inductive Input where
  | word (value : Nat)
  | flag (value : Bool)

private def Input.value : Input → Value
  | .word value => scalar value
  | .flag value => .bool value

private def Input.coreValue : Input → Core.Value
  | .word value => .word (Core.Word.ofNatModulo value)
  | .flag value => .bool value

/-- The function's results at each input row, compiled natively. -/
private def native (program : CheckedProgram) (name : String) (rows : List (List Input)) :
    IO (List Value) := do
  let entry ← compileNamed program name
  rows.mapM fun row => entry.run (row.map Input.value)

/-- The function's word results at each input row, linked directly. -/
private def linked (program : CheckedProgram) (name : String) (rows : List (List Input)) :
    IO (List Value) := do
  let signature ← signatureNamed program name
  let request ← get s!"{name}: seed"
    (SourceProgramExecution.resolveSeed program (SourceProgramExecution.Seed.declaration signature.id))
  let plan ← match ← get s!"{name}: worklist" (SourceSpecializationWorklist.run program [request] 128) with
    | .complete plan => pure plan
    | .budgetExhausted _ _ _ => throw (IO.userError s!"{name}: worklist exhausted")
  let linked ← get s!"{name}: direct link"
    (SourceCoreDirectLinking.linkWithStagingFuel program (.complete plan) 128)
  let entry ← match linked.entries with
    | [entry] => pure entry
    | _ => throw (IO.userError s!"{name}: not one linked entry")
  rows.mapM fun row => match entry.run? (row.map Input.coreValue) 100000 with
    | some (.done (.word value) _) => pure (.word value)
    | _ => throw (IO.userError s!"{name}: the linked entry did not return a word")

/-- The function's fault at the input row, compiled natively: its token and diagnostic. -/
private def fault (program : CheckedProgram) (name : String) (row : List Nat) :
    IO (Core.Word × SourceCoreFaultSites.Diagnostic) := do
  let entry ← compileNamed program name
  let invocation ← entry.invoke (row.map scalar)
  match invocation.outcome with
  | .failed token _ =>
      match ← invocation.diagnostic token with
      | some diagnostic => pure (token, diagnostic)
      | none => throw (IO.userError s!"{name}: a fault without a diagnostic")
  | _ => throw (IO.userError s!"{name}: did not fault")

/-- The binder of the read of `localName` in `function`'s body. -/
private def readBinder (program : CheckedProgram) (function localName : String) : IO Resolved.LocalId := do
  let checked ← checkedNamed program function
  match checked.typedBody.nodes.findSome? fun
      | .expression { form := .reference name (.local binder), .. } =>
          if name == localName then some binder else none
      | _ => none with
  | some binder => pure binder
  | none => throw (IO.userError s!"{function}: no read of {localName}")

private def generic : List String := [
  "trait Add<T> { function add(left: T, right: T) returns (T); }",
  "trait Mix<a, b> { function mix(x: a, y: b, z: b) returns (b); }",
  "impl Add<word> { function add(left: word, right: word) returns (word) { return left * 10 - right; } }",
  "impl Mix<bool, word> { function mix(x: bool, y: word, z: word) returns (word) {",
  "  return x ? y * 100 - z : z * 100 - y;",
  "} }",
  "function viaAdd<T>(left: T, right: T) returns (T) where T: Add { return left + right; }",
  "function sum(a: word, b: word) returns (word) { return viaAdd(a, b); }",
  "function probe<a, b>(x: a, y: b, z: b) returns (b) { return y; }",
  "function viaMix<a, b>(x: a, y: b, z: b) returns (b) where a: Mix<b> { return probe(x, y, z); }",
  "function mixed(flag: bool, b: word, c: word) returns (word) { return viaMix(flag, b, c); }"
]

/-- In generic code, both compilers run `Add.add` as the operator and `Mix.mix` as the method. -/
private def testGeneric : IO Unit := do
  let program ← check "generic code" generic
  let addition ← operatorAsMethodCall program "viaAdd"
  let mixing ← callAsMethodCall program "viaMix"
  let sums := [[Input.word 5, .word 3], [.word 9, .word maximum]]
  let expectedSums := [scalar 47, scalar 91]
  let mixes := [[Input.flag true, .word 3, .word 4], [.flag false, .word 3, .word 4]]
  let expectedMixes := [scalar 296, scalar 397]
  for (route, compile) in [("native", native), ("linked", linked)] do
    let operator ← compile program "sum" sums
    let called ← compile addition "sum" sums
    require (operator == expectedSums && called == expectedSums)
      s!"{route}: Add.add by its name gave {reprStr called}, the operator {reprStr operator}"
    let mixed ← compile mixing "mixed" mixes
    require (mixed == expectedMixes) s!"{route}: Mix.mix by its name gave {reprStr mixed}"

private def operators : List String := [
  "enum Box { B(word) }",
  "enum Bad { D(word) }",
  "trait Add<T> { function add(left: T, right: T) returns (T); }",
  "trait Mix<a, b> { function mix(x: a, y: b, z: b) returns (b); }",
  "impl Add<Box> { function add(left: Box, right: Box) returns (Box) {",
  "  match (left) { case Box.B(x) { match (right) { case Box.B(y) { return Box.B(x * 10 + y); } } } }",
  "} }",
  "impl Add<Bad> { function add(left: Bad, right: Bad) returns (Bad) { let absent: Bad; return absent; } }",
  "impl Mix<Box, word> { function mix(x: Box, y: word, z: word) returns (word) {",
  "  match (x) { case Box.B(v) { return v * 100 + y * 10 + z; } }",
  "} }",
  "function unbox(b: Box) returns (word) { match (b) { case Box.B(v) { return v; } } }",
  "function unbad(b: Bad) returns (word) { match (b) { case Bad.D(v) { return v; } } }",
  "function failing(a: word, b: word) returns (word) { return unbad(Bad.D(a) + Bad.D(b)); }",
  "function early(a: word) returns (Box) { let first: Box; return first; }",
  "function late(a: word) returns (Box) { let second: Box; return second; }",
  "function ordered(a: word) returns (word) { return unbox(early(a) + late(a)); }",
  "function probe(x: Box, y: word, z: word) returns (word) { return 0; }",
  "function zero(a: word) returns (Box) { let nothing: Box; return nothing; }",
  "function one(a: word) returns (word) { let unset: word; return unset; }",
  "function two(a: word) returns (word) { let blank: word; return blank; }",
  "function secondFaults(a: word) returns (word) { return probe(Box.B(a), one(a), two(a)); }",
  "function firstFaults(a: word) returns (word) { return probe(zero(a), one(a), two(a)); }"
]

/-- A fault of the method's body, and the arguments' order, compiled natively. -/
private def testFaults : IO Unit := do
  let program ← check "faults" operators
  let (operatorToken, operatorDiagnostic) ← fault program "failing" [3, 4]
  let (calledToken, calledDiagnostic) ← fault (← operatorAsMethodCall program "failing") "failing" [3, 4]
  require (calledToken != Core.Word.zero && calledToken == operatorToken &&
      decide (calledDiagnostic = operatorDiagnostic))
    "the method's body faulted with another token or diagnostic than the operator's"
  require (match calledDiagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "the method's body did not fault at its uninitialized read"
  let first ← readBinder program "early" "first"
  let (operatorToken, operatorDiagnostic) ← fault program "ordered" [5]
  let (calledToken, calledDiagnostic) ← fault (← operatorAsMethodCall program "ordered") "ordered" [5]
  require (calledToken == operatorToken && decide (calledDiagnostic = operatorDiagnostic) &&
      decide (calledDiagnostic.error = SourceTypedRuntime.RuntimeError.uninitializedLocal first))
    "the left argument's fault is not the call's, as it is the operator's"
  for (name, function, localName) in [("secondFaults", "one", "unset"), ("firstFaults", "zero", "nothing")] do
    let binder ← readBinder program function localName
    let (_, direct) ← fault program name [4]
    let (_, called) ← fault (← callAsMethodCall program name) name [4]
    require (decide (called = direct) && decide (called.error = SourceTypedRuntime.RuntimeError.uninitializedLocal binder))
      s!"{name}: the first faulting argument is not the call's, as it is the direct call's"

def run : IO Unit := do
  testGeneric
  testFaults
  IO.println "SELECTED_METHOD_CALLS_PASS Add.add as +, Mix.mix of two parameters, natively and linked; a body's fault and the arguments' order"

end Tests.SourceCoreSelectedMethodCalls
