import Solcore.Frontend.SourceCoreFunctionEntry

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreAssignmentEntries

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value

def fixtures : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function operators(value: Word) returns (Word) {",
    " value += 3; value -= 1; value *= 2; value /= 3; value %= 5; value |= 8; value &= 15; value ^= 2; value ~=; return value; }",
    "function forOrder(limit: Word) returns (Word, Word) { let count: Word = 0;",
    " for (let i: Word = 0; limit > i; i += 1) { count += 1; if (i == 1) { continue; } count += 10; } return (count, limit); }",
    "function absent() returns (Word) { let target: Word; target += 3; return target; }",
    "function unaryAbsent() returns (Word) { let target: Word; target ~=; return target; }",
    "function headerAbsent() returns (Word) { let target: Word; for (target += 3; false; target += 1) { } return 0; }",
    "function postAbsent() returns (Word) { let target: Word; for (let i: Word = 0; true; target += 1) { continue; } return 0; }",
    "function unaryPostAbsent() returns (Word) { let target: Word; for (let i: Word = 0; true; target ~=) { continue; } return 0; }",
    "function rhsAbsent() returns (Word) { let target: Word; let absent: Word; target += absent; return target; }",
    "function failLeft() returns (Word) { let target: Word; target += 1; return target; }",
    "function failRight() returns (Word) { let target: Word; target -= 1; return target; }",
    "function choose(flag: Bool) returns (Word) { return flag ? failLeft() : failRight(); }",
    "function snapshot(value: Word) returns (Word) {",
    " let rhs: function() returns (Word) = lam() -> Word { value = 100; return 3; }; value += rhs(); return value; }",
    "function snapshotAbsent() returns (Word) { let target: Word;",
    " let rhs: function() returns (Word) = lam() -> Word { target = 100; return 3; }; target += rhs(); return target; }",
    "function failurePriority() returns (Word) { let target: Word; let absent: Word;",
    " let rhs: function() returns (Word) = lam() -> Word { target = 100; return absent; }; target += rhs(); return target; }",
    "function captured(value: Word) returns (Word, Word) {",
    " let f: function(Word) returns (Word) = lam(delta: Word) -> Word { value += delta; return value; }; return (f(2), f(3)); }",
    "function functionEqual() returns (Word) {",
    " let f: function() returns (Word) = lam() -> Word { return 1; };",
    " let g: function() returns (Word) = lam() -> Word { return 2; }; f = g; return f(); }"
  ] }]
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"assignment-entry fixture missing: {name}")

private def plan (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Plan := do
  match SourceSpecializationWorklist.run program [← request program name] 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"assignment-entry worklist failed: {reprStr result}")

private inductive Profile where
  | basic | recursive | functions

private def prepare (profile : Profile) (program : CheckedProgram) (name : String) :
    IO SourceCoreBasicEntry.PreparedProgram := do
  let input ← plan program name
  match profile with
  | .basic => match SourceCoreBasicEntry.prepare program input 100 Core.Word.zero with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"basic assignment entry rejected: {reprStr error}")
  | .recursive => match SourceCoreRecursiveEntry.prepare program input 100 Core.Word.zero with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"recursive assignment entry rejected: {reprStr error}")
  | .functions => match SourceCoreFunctionEntry.prepare program input 100 Core.Word.zero with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"function assignment entry rejected: {reprStr error}")

private def firstEntry (program : SourceCoreBasicEntry.PreparedProgram) : IO SourceCoreBasicEntry.Entry :=
  match program.entries with
  | [entry] => pure entry
  | _ => throw (IO.userError "assignment entry seed order changed")

private def execute (entry : SourceCoreBasicEntry.Entry) (arguments : List Core.Value)
    (fuel : Nat := 30000) : IO (SourceCoreBasicEntry.Result entry.resultType) := do
  match entry.run arguments fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"assignment entry invocation rejected: {reprStr error}")

private def success (entry : SourceCoreBasicEntry.Entry) (arguments : List Core.Value)
    (expected : Core.Value) : IO Core.Store := do
  let completed ← execute entry arguments
  let store ← match completed.observation with
    | .succeeded value store =>
        assertTrue (value == expected) "assignment entry changed its returned value"
        pure store
    | result => throw (IO.userError s!"assignment entry failed: {reprStr result}")
  let paused ← execute entry arguments 10
  let checkpoint ← match paused.checkpoint? with
    | some checkpoint => pure checkpoint
    | none => throw (IO.userError "assignment entry must retain a typed checkpoint")
  assertTrue ((checkpoint.resume 29990).observation == completed.observation)
    "assignment entry resume changed its captured snapshot or native heap"
  pure store

private def diagnosticSite (program : CheckedProgram) (name : String) :
    IO (SourceCoreElaboration.ErrorSite × Syntax.SourceSpan) := do
  let owner := (← request program name).declaration
  let function ← match program.functions.find? (·.declaration == owner) with
    | some function => pure function
    | none => throw (IO.userError "assignment diagnostic function missing")
  match function.typedBody.nodes.find? (fun
      | .statement node => match node.form with
        | .assignValue _ operator _ => operator != .equal
        | .assignBitNot _ | .forLoop .. => true
        | _ => false
      | _ => false) with
  | some (.statement node) => pure (.occurrence node.id.occurrence, node.span)
  | _ => throw (IO.userError "assignment diagnostic statement missing")

private def expectFailure (entry : SourceCoreBasicEntry.Entry) (arguments : List Core.Value)
    (diagnostic : SourceCoreFaultSites.Diagnostic) : IO (Core.Word × Core.Store) := do
  match (← execute entry arguments).observation with
  | .failed token store =>
      assertTrue (token != Core.Word.zero && decide (entry.failureDiagnostic? token = some diagnostic))
        "assignment failure lost its exact operator, site or span"
      pure (token, store)
  | result => throw (IO.userError s!"assignment entry did not retain its failure: {reprStr result}")

private def testProfiles (program : CheckedProgram) : IO Unit := do
  for profile in [Profile.basic, .recursive, .functions] do
    let operators ← firstEntry (← prepare profile program "operators")
    discard <| success operators [scalar 2] (.word (word 8).bitNot)
    discard <| success operators [scalar 5] (.word (word 14).bitNot)
    let forEntry ← firstEntry (← prepare profile program "forOrder")
    discard <| success forEntry [scalar 3] (.pair (scalar 23) (scalar 3))
    for (name, error) in ([
        ("absent", .invalidAssignmentOperands .add none (some .word)),
        ("unaryAbsent", .invalidUnaryOperand .bitNot none),
        ("headerAbsent", .invalidAssignmentOperands .add none (some .word)),
        ("postAbsent", .invalidAssignmentOperands .add none (some .word)),
        ("unaryPostAbsent", .invalidUnaryOperand .bitNot none)] :
        List (String × SourceTypedRuntime.RuntimeError)) do
      let entry ← firstEntry (← prepare profile program name)
      let (site, span) ← diagnosticSite program name
      discard <| expectFailure entry [] { error, site, span := some span }
    let entry ← firstEntry (← prepare profile program "rhsAbsent")
    let read ← match entry.faultSites.reads.find? (fun site =>
        match program.functions.find? (·.declaration == site.binder.owner) with
        | some function => function.typedBody.nodes.any fun
          | .expression node => node.id == site.expression &&
            match node.form with | .reference "absent" (.local _) => true | _ => false
          | _ => false
        | none => false) with
      | some read => pure read
      | none => throw (IO.userError "assignment RHS read diagnostic missing")
    discard <| expectFailure entry [] {
      error := .uninitializedLocal read.binder, site := .occurrence read.expression.occurrence,
      span := some read.span }

private def testCallees (program : CheckedProgram) : IO Unit := do
  let prepared ← prepare .recursive program "choose"
  let entry ← firstEntry prepared
  let catalog ← match SourceCoreProgramFaultSites.prepare prepared.plan entry.key with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"assignment codebook rejected: {reprStr error}")
  let tokens := catalog.functions.flatMap fun function =>
    function.table.reads.map (·.reason) ++ function.assignments.sites.map (·.reason) ++
      [function.fellThroughReason, function.table.escapedReason]
  assertTrue (tokens.eraseDups.length == tokens.length && tokens.all (· != Core.Word.zero))
    "program codebook reused a read, assignment or boundary reason"
  let mut failureTokens : List Core.Word := []
  for (flag, name, operator) in [(true, "failLeft", Syntax.ValueAssignOp.add), (false, "failRight", .subtract)] do
    let (site, span) ← diagnosticSite program name
    let (token, _) ← expectFailure entry [.bool flag] {
      error := .invalidAssignmentOperands operator none (some .word), site, span := some span }
    failureTokens := token :: failureTokens
  assertTrue (failureTokens[0]? != failureTokens[1]?) "callee assignment failures shared one token"

private def testCapturedRhs (program : CheckedProgram) : IO Unit := do
  let prepared ← prepare .functions program "snapshot"
  let entry ← firstEntry prepared
  let store ← success entry [scalar 2] (scalar 5)
  let index := entry.inputs.length + prepared.plan.specializations.length
  assertTrue (store[index]? == some (present (scalar 5)))
    "compound assignment used the RHS-mutated value instead of its selected snapshot"
  let prepared ← prepare .functions program "snapshotAbsent"
  let entry ← firstEntry prepared
  let (site, span) ← diagnosticSite program "snapshotAbsent"
  let (_, store) ← expectFailure entry [] {
    error := .invalidAssignmentOperands .add none (some .word), site, span := some span }
  assertTrue (store[prepared.plan.specializations.length]? == some (present (scalar 100)))
    "absent compound operand discarded a successful RHS's captured-cell write"
  let prepared ← prepare .functions program "failurePriority"
  let entry ← firstEntry prepared
  let read ← match entry.faultSites.reads.find? (fun site =>
      match program.functions.find? (·.declaration == site.binder.owner) with
      | some function => function.typedBody.nodes.any fun
        | .expression node => node.id == site.expression &&
          match node.form with | .reference "absent" (.local _) => true | _ => false
        | _ => false
      | none => false) with
    | some read => pure read
    | none => throw (IO.userError "captured RHS failure occurrence missing")
  let (_, store) ← expectFailure entry [] {
    error := .uninitializedLocal read.binder, site := .occurrence read.expression.occurrence,
    span := some read.span }
  assertTrue (store[prepared.plan.specializations.length]? == some (present (scalar 100)))
    "RHS failure priority discarded earlier shared mutation"
  discard <| success (← firstEntry (← prepare .functions program "captured")) [scalar 4]
    (.pair (scalar 6) (scalar 9))
  discard <| success (← firstEntry (← prepare .functions program "functionEqual")) [] (scalar 2)

def run : IO Unit := do
  let program ← match checkProgram fixtures with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"assignment entry fixtures failed checking: {reprStr errors}")
  testProfiles program
  testCallees program
  testCapturedRhs program

end Tests.SourceCoreAssignmentEntries
