import Solcore.Frontend.SourceCoreFunctionEntry
import Solcore.Frontend.SourceCoreAssignmentFaultSites
import Solcore.Frontend.SourceCoreAssignments
import Solcore.Frontend.SourceCorePrimitive
import Solcore.Frontend.SourceCoreBasic
import Solcore.Core.BoundedSafety
import Solcore.Frontend.SourceCoreBasicEntry
import Solcore.Frontend.SourceCoreCalls
import Solcore.Frontend.SourceCoreFaultSites
import Solcore.Frontend.SourceCoreControl
import Solcore.Frontend.SourceCoreDataCatalog
import Solcore.Frontend.SourceCoreDataValues
import Solcore.Frontend.SourceCoreFunctions
import Solcore.Frontend.SourceCoreRecursiveEntry
import Solcore.Frontend.SourceCoreGeneralEntry
import Solcore.Core.LocalSequence
import Solcore.Frontend.SourceCoreFunctionTypes
import Solcore.Frontend.SourceCoreAssignmentPolicy
import Solcore.Frontend.SourceCoreLocalPolymorphism
import Solcore.Core.ExactFuelProperties
import Solcore.Frontend.SourceCoreLoops
import Solcore.Frontend.SourceCoreSession

/-!
# Lowering entry point tests

The first lowering fragments: basic, control, assignment, loop, function and integer entries, and
sessions. These tests assert that the lowering stays independent of the source runtime values.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreAssignmentEntries
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

/-- Closures capture by value: an RHS closure call writes only its own copy of
the target, never the target itself. The copies follow the target in the
store: the closure's snapshot copies, the closure, then the call's copies. -/
private def testCapturedRhs (program : CheckedProgram) : IO Unit := do
  let prepared ← prepare .functions program "snapshot"
  let entry ← firstEntry prepared
  let store ← success entry [scalar 2] (scalar 5)
  let index := entry.inputs.length + prepared.plan.specializations.length
  /- `rhs` cannot change `value`, so this result no longer shows whether the
  target was read before the RHS. -/
  assertTrue (store[index]? == some (present (scalar 5)))
    "compound assignment changed its result or an RHS closure call reached its target"
  let prepared ← prepare .functions program "snapshotAbsent"
  let entry ← firstEntry prepared
  let (site, span) ← diagnosticSite program "snapshotAbsent"
  let (_, store) ← expectFailure entry [] {
    error := .invalidAssignmentOperands .add none (some .word), site, span := some span }
  let target := prepared.plan.specializations.length
  assertTrue (store[target]? == some (.inLeft .word .unit) &&
      store[target + 3]? == some (present (scalar 100)))
    "absent compound operand discarded the RHS call's write to its copy, or the write reached the target"
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
  let target := prepared.plan.specializations.length
  assertTrue (store[target]? == some (.inLeft .word .unit) &&
      store[target + 6]? == some (present (scalar 100)))
    "RHS failure priority discarded the call's earlier write to its copy, or the write reached the target"
  discard <| success (← firstEntry (← prepare .functions program "captured")) [scalar 4]
    (.pair (scalar 6) (scalar 7))
  discard <| success (← firstEntry (← prepare .functions program "functionEqual")) [] (scalar 2)

def run : IO Unit := do
  let program ← match checkProgram fixtures with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"assignment entry fixtures failed checking: {reprStr errors}")
  testProfiles program
  testCallees program
  testCapturedRhs program

end Tests.SourceCoreAssignmentEntries
end

section
-- leanmerge: from Solcore.Test.SourceCoreAssignmentFaultSites
/-! Assignment reasons preserve parsed statement/header metadata. Repeated
header operations deduplicate only when their parent, binder and kind match. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreAssignmentFaultSites

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceCoreAssignmentFaultSites

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function sites(value: Word, rhs: Word) returns (Word) {",
    "  value += rhs; value = rhs; value ~=;",
    "  for (value += rhs, rhs += value, value += rhs, value -= rhs; false;",
    "       value *= rhs, value ~=, value *= rhs) { value ^= rhs; }",
    "  return value;",
    "}",
    "function equalOnly(value: (Word, Bool), rhs: (Word, Bool)) returns (Word, Bool) { value = rhs; return value; }"
  ] }]
}

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction := do
  match program.functions.find? (fun function =>
    match program.environment.declaration? function.declaration with
    | some declaration => declaration.name == some name
    | none => false) with
  | some function => pure function
  | none => throw (IO.userError s!"assignment metadata fixture missing: {name}")

private def prepared (source : TypedSource) (firstReason : Nat) : IO Table := do
  match prepare source firstReason with
  | .ok table => pure table
  | .error error => throw (IO.userError s!"assignment metadata rejected: {reprStr error}")

private def testSites (function : CheckedFunction) : IO Unit := do
  let source := function.typedBody
  let table ← prepared source 100
  assertTrue (table.length == 8 && table.sites.map (·.reason.val) ==
      (List.range 8).map (100 + ·)) "assignment reasons wrapped, reordered or failed to deduplicate"
  let (value, rhs) ← match source.inputs with
    | [value, rhs] => pure (value.id, rhs.id)
    | _ => throw (IO.userError "assignment metadata input identity changed")
  let statements := source.nodes.filterMap fun
    | .statement node => some node
    | _ => none
  let ordinaryAdd ← match statements.find? (fun node => match node.form with
      | .assignValue _ .add _ => true | _ => false) with
    | some node => pure node
    | none => throw (IO.userError "ordinary assignment occurrence missing")
  let ordinaryUnary ← match statements.find? (fun node => match node.form with
      | .assignBitNot _ => true | _ => false) with
    | some node => pure node
    | none => throw (IO.userError "ordinary unary occurrence missing")
  let loop ← match statements.find? (fun node => match node.form with
      | .forLoop .. => true | _ => false) with
    | some node => pure node
    | none => throw (IO.userError "header assignment parent missing")
  let body ← match statements.find? (fun node => match node.form with
      | .assignValue _ .bitXor _ => true | _ => false) with
    | some node => pure node
    | none => throw (IO.userError "loop body assignment occurrence missing")
  let expected : List (StatementNode × Resolved.LocalId × Kind) := [
    (ordinaryAdd, value, .value .add), (ordinaryUnary, value, .bitNot),
    (loop, value, .value .add), (loop, rhs, .value .add), (loop, value, .value .subtract),
    (loop, value, .value .multiply), (loop, value, .bitNot), (body, value, .value .bitXor)]
  for (site, (node, binder, kind)) in table.sites.zip expected do
    let location := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
    assertTrue (decide (site.site = location ∧ site.binder = binder ∧ site.kind = kind ∧
        site.span = node.span)) "assignment reason changed its parent, binder, kind or span"
    assertTrue (table.reasonAt location binder kind == site.reason)
      "assignment provider failed to distinguish exact binder and kind"
    let diagnostic : SourceCoreFaultSites.Diagnostic := {
      error := match kind with
        | .value operator => .invalidAssignmentOperands operator none (some .word)
        | .bitNot => .invalidUnaryOperand .bitNot none
      site := location
      span := some node.span
    }
    assertTrue (decide (table.diagnostic? site.reason = some diagnostic))
      "assignment failure reason returned the wrong source error"
    assertTrue (decide ((site.reason, diagnostic) ∈ table.diagnostics))
      "assignment diagnostic export lost the classified reason"
  assertTrue (table.diagnostics.length == table.length)
    "assignment diagnostic export changed table length"
  assertTrue (decide (table.diagnostic? (word 999) = none)) "unknown assignment reason produced a diagnostic"
  assertTrue (table.reasonAt (.occurrence ordinaryAdd.id.occurrence) rhs (.value .add) == Core.Word.zero)
    "assignment lookup matched a different binder"
  assertTrue (table.reasonAt (.occurrence ordinaryAdd.id.occurrence) value (.value .equal) == Core.Word.zero)
    "equal assignment acquired an unused absent-target reason"
  let boundary ← prepared source (Core.wordModulus - 8)
  assertTrue (boundary.sites.map (·.reason.val) ==
      (List.range 8).map (Core.wordModulus - 8 + ·)) "assignment reason boundary wrapped modulo"
  for firstReason in [Core.wordModulus - 7, Core.wordModulus] do
    match prepare source firstReason with
    | .error .reasonSpaceExhausted => pure ()
    | result => throw (IO.userError s!"assignment reason overflow was accepted: {reprStr result}")

private def testOwners (function foreign : CheckedFunction) : IO Unit := do
  let source := function.typedBody
  let wrongStatement := { source with nodes := source.nodes.map fun
    | .statement node => .statement { node with
        id := { node.id with occurrence := { node.id.occurrence with owner := foreign.declaration } } }
    | node => node }
  match prepare wrongStatement 100 with
  | .error (.ownerMismatch expected actual) =>
      assertTrue (expected == source.owner && actual == foreign.declaration)
        "statement owner rejection changed"
  | result => throw (IO.userError s!"foreign statement metadata was accepted: {reprStr result}")
  let wrongBinder := { source with nodes := source.nodes.map fun
    | .statement node => match node.form with
      | .assignValue assignment .add rhs =>
          let assignment := { assignment with target := { assignment.target with
            root := { assignment.target.root with owner := foreign.declaration } } }
          .statement { node with form := .assignValue assignment .add rhs }
      | _ => .statement node
    | node => node }
  match prepare wrongBinder 100 with
  | .error (.ownerMismatch expected actual) =>
      assertTrue (expected == source.owner && actual == foreign.declaration)
        "assignment binder owner rejection changed"
  | result => throw (IO.userError s!"foreign assignment binder was accepted: {reprStr result}")
  let wrongHeader := { source with nodes := source.nodes.map fun
    | .statement node => match node.form with
      | .forLoop initializer condition post body =>
          let initializer := initializer.map fun
            | .assignValue assignment operator rhs =>
                let assignment := { assignment with target := { assignment.target with
                  root := { assignment.target.root with owner := foreign.declaration } } }
                ForItemForm.assignValue assignment operator rhs
            | item => item
          .statement { node with form := .forLoop initializer condition post body }
      | _ => .statement node
    | node => node }
  match prepare wrongHeader 100 with
  | .error (.ownerMismatch expected actual) =>
      assertTrue (expected == source.owner && actual == foreign.declaration)
        "header binder owner rejection changed"
  | result => throw (IO.userError s!"foreign header binder was accepted: {reprStr result}")

private def testProfiles (function : CheckedFunction) : IO Unit := do
  let empty ← prepared function.typedBody 100
  assertTrue (empty.length == 0 && empty.diagnostics.isEmpty)
    "equal product assignment must have no absent-operand diagnostic"

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"assignment metadata fixture checking failed: {reprStr errors}")
  let function ← named program "sites"
  let foreign ← named program "equalOnly"
  testSites function
  testOwners function foreign
  testProfiles foreign

end Tests.SourceCoreAssignmentFaultSites
end

section
-- leanmerge: from Solcore.Test.SourceCoreAssignments
/-! Real checked assignment metadata is passed through the standalone policy.
The public statement engine supplies assignment-site reasons separately. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreAssignments

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value
private def invalidReason : Core.Word := word 63
private def readReason : Core.Word := word 70

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function add(left: Word, right: Word) returns (Word) { left += right; return left; }",
    "function sub(left: Word, right: Word) returns (Word) { left -= right; return left; }",
    "function mul(left: Word, right: Word) returns (Word) { left *= right; return left; }",
    "function div(left: Word, right: Word) returns (Word) { left /= right; return left; }",
    "function mod(left: Word, right: Word) returns (Word) { left %= right; return left; }",
    "function band(left: Word, right: Word) returns (Word) { left &= right; return left; }",
    "function bor(left: Word, right: Word) returns (Word) { left |= right; return left; }",
    "function bxor(left: Word, right: Word) returns (Word) { left ^= right; return left; }",
    "function invert(left: Word) returns (Word) { left ~=; return left; }",
    "function pair(left: (Word, Bool), right: (Word, Bool)) returns (Word, Bool) { left = right; return left; }"
  ] }]
}

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction := do
  match program.functions.find? (fun function =>
    match program.environment.declaration? function.declaration with
    | some declaration => declaration.name == some name
    | none => false) with
  | some function => pure function
  | none => throw (IO.userError s!"assignment fixture missing: {name}")

private def inputScope (source : TypedSource) : IO SourceCoreAssignments.Scope :=
  source.inputs.foldlM (fun scope binder => do
    match SourceCoreBasic.lowerBinder source scope binder with
    | .ok type => pure ((binder.id, type) :: scope)
    | .error error => throw (IO.userError s!"assignment input rejected: {reprStr error}")) []

private def valueAssignment (function : CheckedFunction) :
    IO (AssignmentResolution × Syntax.ValueAssignOp × ExpressionId) := do
  match function.typedBody.nodes.filterMap (fun
      | .statement { form := .assignValue assignment operator rhs, .. } => some (assignment, operator, rhs)
      | _ => none) with
  | [assignment] => pure assignment
  | _ => throw (IO.userError "assignment fixture must contain exactly one value assignment")

private def unaryAssignment (function : CheckedFunction) : IO AssignmentResolution := do
  match function.typedBody.nodes.filterMap (fun
      | .statement { form := .assignBitNot assignment, .. } => some assignment
      | _ => none) with
  | [assignment] => pure assignment
  | _ => throw (IO.userError "assignment fixture must contain exactly one unary assignment")

private def expressionLowerer (function : CheckedFunction) : SourceCoreControl.ExpressionLowerer :=
  fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel
    ⟨function.solvedRequirements⟩ source scope id reasons

private def result (body : Core.Expr) (scope : SourceCoreAssignments.Scope)
    (type : Core.Ty) (arguments : List Core.Value) : IO Core.StatefulRunResult := do
  assertTrue (decide (Core.infer? (SourceCoreLocalCell.coreContext scope) body =
      some (Core.LanguageResult.resultType type))) "assignment policy failed Core type checking"
  let environment := (scope.reverse.zipIdx.map fun ((_, type), index) =>
    Core.Value.cellRef (Core.OptionalCell.cellType type) index).reverse
  pure (Core.runStateful 500 (.initial body environment arguments))

private def lower (function : CheckedFunction) (scope : SourceCoreAssignments.Scope)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (type : Core.Ty) : Except SourceCoreAssignments.Error Core.Expr := do
  let (index, _) ← SourceCoreAssignments.target function.typedBody scope assignment
  SourceCoreAssignments.assignValueWithReasons (expressionLowerer function) 100
    function.typedBody scope assignment operator rhs type
    (Core.OptionalCell.read type (.var index) readReason) invalidReason (fun _ => readReason)

private def testWords (program : CheckedProgram) : IO Unit := do
  for (name, operator) in ([
      ("add", .add), ("sub", .subtract), ("mul", .multiply), ("div", .divide),
      ("mod", .modulo), ("band", .bitAnd), ("bor", .bitOr), ("bxor", .bitXor)] :
      List (String × Core.LocalAssignment.Operator)) do
    let function ← named program name
    let scope ← inputScope function.typedBody
    let (assignment, sourceOperator, rhs) ← valueAssignment function
    let body ← match lower function scope assignment sourceOperator rhs .word with
      | .ok body => pure body
      | .error error => throw (IO.userError s!"Word assignment rejected: {reprStr error}")
    for right in [3, 0] do
      let expected : Core.Value := .word (operator.apply (word 2) (word right))
      assertTrue ((← result body scope .word [present (scalar 2), present (scalar right)]) ==
          .done (.inRight .word expected) [present expected, present (scalar right)])
        "source compound assignment changed builtin Word behavior"
    assertTrue ((← result body scope .word [.inLeft .word .unit, present (scalar 3)]) ==
        .done (.inLeft .word (.word invalidReason)) [.inLeft .word .unit, present (scalar 3)])
      "source compound assignment lost its absent-target reason"
    assertTrue ((← result body scope .word [.inLeft .word .unit, .inLeft .word .unit]) ==
        .done (.inLeft .word (.word readReason)) [.inLeft .word .unit, .inLeft .word .unit])
      "source compound assignment must report RHS absence before target absence"
  let function ← named program "invert"
  let scope ← inputScope function.typedBody
  let assignment ← unaryAssignment function
  let body ← match SourceCoreAssignments.assignBitNot function.typedBody scope assignment .word
      (Core.OptionalCell.read .word (.var 0) readReason) invalidReason with
    | .ok body => pure body
    | .error error => throw (IO.userError s!"Word unary assignment rejected: {reprStr error}")
  let expected : Core.Value := .word (word 2).bitNot
  assertTrue ((← result body scope .word [present (scalar 2)]) ==
      .done (.inRight .word expected) [present expected]) "source unary assignment changed"
  assertTrue ((← result body scope .word [.inLeft .word .unit]) ==
      .done (.inLeft .word (.word invalidReason)) [.inLeft .word .unit])
    "source unary assignment lost its absent-operand reason"

private def expectError {α : Type} (label : String) (outcome : Except SourceCoreAssignments.Error α)
    (accepts : SourceCoreAssignments.Error → Bool) : IO Unit := do
  match outcome with
  | .error error => assertTrue (accepts error) s!"{label}: wrong rejection {reprStr error}"
  | .ok _ => throw (IO.userError s!"{label}: invalid assignment metadata was accepted")

private def testBoundary (program : CheckedProgram) : IO Unit := do
  let pairFunction ← named program "pair"
  let pairScope ← inputScope pairFunction.typedBody
  let (pairAssignment, _, pairRhs) ← valueAssignment pairFunction
  let type := Core.Ty.product .word .bool
  let body ← match lower pairFunction pairScope pairAssignment .equal pairRhs type with
    | .ok body => pure body
    | .error error => throw (IO.userError s!"equal product assignment rejected: {reprStr error}")
  let left : Core.Value := .pair (scalar 2) (.bool false)
  let right : Core.Value := .pair (scalar 3) (.bool true)
  assertTrue ((← result body pairScope type [present left, present right]) ==
      .done (.inRight .word right) [present right, present right])
    "equal assignment lost the existing product profile"
  expectError "compound product" (lower pairFunction pairScope pairAssignment .add pairRhs type)
    fun error => error matches .typeMismatch _ .word (.product .word .bool)
  expectError "unary product" (SourceCoreAssignments.assignBitNot pairFunction.typedBody pairScope
      pairAssignment type (.unit) invalidReason)
    fun error => error matches .typeMismatch _ .word (.product .word .bool)
  let function ← named program "add"
  let scope ← inputScope function.typedBody
  let (assignment, operator, rhs) ← valueAssignment function
  let project := { assignment with target := { assignment.target with projections := [.member "field" 0] } }
  expectError "projection" (lower function scope project operator rhs .word)
    fun error => error matches .projectedAssignment _
  let requirements := { assignment with requirements := [⟨0⟩] }
  expectError "method evidence" (lower function scope requirements operator rhs .word)
    fun error => error matches .assignmentRequirementsPresent _
  let wrongOwner := { assignment with target := { assignment.target with
    root := { assignment.target.root with owner := pairFunction.declaration } } }
  expectError "target owner" (lower function scope wrongOwner operator rhs .word)
    fun error => error matches .ownerMismatch _ _
  let wrongType := { assignment with target := { assignment.target with type := .bool } }
  expectError "target type" (lower function scope wrongType operator rhs .word)
    fun error => error matches .typeMismatch _ .word .bool
  let wrongRhs := { rhs with occurrence := { rhs.occurrence with owner := pairFunction.declaration } }
  expectError "RHS owner" (lower function scope assignment operator wrongRhs .word)
    fun error => error matches .ownerMismatch _ _

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"assignment fixtures failed checking: {reprStr errors}")
  testWords program
  testBoundary program

end Tests.SourceCoreAssignments
end

section
-- leanmerge: from Solcore.Test.SourceCoreBasic
/-! Tests for the explicit basic compiler fragment. Parsed fixtures use typed
Word inputs so integer-literal evidence is not bypassed. Core argument literals
belong to the test harness, which allocates inputs as optional cells. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreBasic

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value
private def reason : Core.Word := word 77

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function sequence(flag: Bool, initial: Word, replacement: Word) returns (Word, Bool) {",
    "  let value: Word; value = initial; let copied: Word = value;",
    "  value = replacement; copied; return (copied, flag);",
    "}",
    "function early(initial: Word, replacement: Word) returns (Word) {",
    "  let value: Word = initial; return value; value = replacement;",
    "}",
    "function initializerFailure(input: Word) returns (Word) {",
    "  let absent: Word; let never: Word = absent; let later: Word = input; return later;",
    "}",
    "function assignmentFailure(input: Word, replacement: Word) returns (Word) {",
    "  let target: Word = input; let absent: Word; target = absent;",
    "  target = replacement; return target;",
    "}",
    "function discardFailure(input: Word) returns (Word) {",
    "  let absent: Word; absent; let later: Word = input; return later;",
    "}",
    "function pairFailure(flag: Bool) returns (Word, Bool) {",
    "  let absent: Word; return (absent, flag);",
    "}",
    "function tail(value: Word) returns (Word) { value }",
    "function empty() { return; }",
    "function fallthrough() { true; }",
    "function unit() { return (); }",
    "function bool() returns (Bool) { return (true); }",
    "function literalEvidence() returns (Word) { return 1; }",
    "function blocked(value: Word) returns (Word) { { return value; } }"
  ] }]
  externalLibraries := []
}

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction := do
  match program.functions.find? (fun function =>
    match program.environment.declaration? function.declaration with
    | some declaration => declaration.name == some name
    | none => false) with
  | some function => pure function
  | none => throw (IO.userError s!"missing basic compiler fixture {name}")

private def roots (source : TypedSource) : IO (List StatementId) :=
  source.roots.mapM fun
    | .statement id => pure id
    | _ => throw (IO.userError "expected statement roots")

private def inputScope (source : TypedSource) : IO Frontend.SourceCoreBasic.Scope := do
  source.inputs.foldlM (fun scope binder => do
    match Frontend.SourceCoreBasic.lowerBinder source scope binder with
    | .ok type => pure ((binder.id, type) :: scope)
    | .error error => throw (IO.userError s!"input shape rejected: {reprStr error}")) []

/-- Allocate inputs in source order. The newest input is first in the lexical
scope, while heap locations retain the original parameter order. -/
private def closeInputs (scope : Frontend.SourceCoreBasic.Scope)
    (arguments : List Core.Expr) (body : Core.Expr) : Core.Expr :=
  (scope.reverse.zip arguments).foldr (fun entry body =>
    .letE (Core.OptionalCell.allocateInitialized entry.1.2 entry.2) body) body

private def compile (function : CheckedFunction) (resultType : Core.Ty)
    (arguments : List Core.Expr) : IO Core.Program := do
  let source := function.typedBody
  let scope ← inputScope source
  assertTrue (scope.length == arguments.length) "fixture argument count mismatch"
  let statements ← roots source
  let expression ← match Frontend.SourceCoreBasic.lowerStatements 100 source scope statements resultType reason with
    | .ok expression => pure expression
    | .error error => throw (IO.userError s!"basic lowering failed: {reprStr error}")
  assertTrue (decide (Core.infer? (SourceCoreLocalCell.coreContext scope) expression =
      some (Core.LanguageResult.resultType resultType)))
    "the compiler emitted an ill-typed open Core expression"
  let program : Core.Program := {
    resultType := Core.LanguageResult.resultType resultType
    body := closeInputs scope arguments expression
  }
  assertTrue program.check "the closed compiler output failed the Core checker"
  pure program

private def expectRun (program : Core.Program) (value : Core.Value) (store : Core.Store)
    (message : String) : IO Unit :=
  assertTrue (program.runStateful 1000 == .done value store) message

private def expectSuccess (program : Core.Program) (value : Core.Value) (store : Core.Store)
    (message : String) : IO Unit := expectRun program (.inRight .word value) store message

private def expectFailure (program : Core.Program) (type : Core.Ty) (store : Core.Store)
    (message : String) : IO Unit := expectRun program (.inLeft type (.word reason)) store message

private def testExecution (program : CheckedProgram) : IO Unit := do
  let sequence ← compile (← named program "sequence") (.product .word .bool)
    [.bool true, literal 11, literal 29]
  let sequenceStore := [present (.bool true), present (scalar 11), present (scalar 29),
    present (scalar 29), present (scalar 11)]
  expectSuccess sequence (.pair (scalar 11) (.bool true)) sequenceStore
    "let/read/assignment/discard order or temporary binder weakening changed"
  match sequence.runStateful 30 with
  | .outOfFuel checkpoint =>
      assertTrue (Core.runStateful 970 checkpoint ==
          .done (.inRight .word (.pair (scalar 11) (.bool true))) sequenceStore)
        "resumption changed the lowered sequence's values or shared cells"
  | _ => throw (IO.userError "sequence fixture should retain a checkpoint at fuel 30")
  let early ← compile (← named program "early") .word [literal 11, literal 29]
  expectSuccess early (scalar 11) [present (scalar 11), present (scalar 29), present (scalar 11)]
    "return must skip the subsequent assignment"
  let initializerFailure ← compile (← named program "initializerFailure") .word [literal 11]
  expectFailure initializerFailure .word [present (scalar 11), .inLeft .word .unit]
    "failed initializer must not allocate its binding or run the tail"
  let assignmentFailure ← compile (← named program "assignmentFailure") .word [literal 11, literal 29]
  expectFailure assignmentFailure .word
    [present (scalar 11), present (scalar 29), present (scalar 11), .inLeft .word .unit]
    "failed RHS must preserve the assignment target and skip later writes"
  let discardFailure ← compile (← named program "discardFailure") .word [literal 11]
  expectFailure discardFailure .word [present (scalar 11), .inLeft .word .unit]
    "discarding a value must still propagate its language failure"
  let pairFailure ← compile (← named program "pairFailure") (.product .word .bool) [.bool true]
  expectFailure pairFailure (.product .word .bool) [present (.bool true), .inLeft .word .unit]
    "tuple failure must be retagged to the complete tuple result type"
  let tail ← compile (← named program "tail") .word [literal 17]
  expectSuccess tail (scalar 17) [present (scalar 17)] "final expression must return its value"
  for name in ["empty", "fallthrough", "unit"] do
    let unit ← compile (← named program name) .unit []
    expectSuccess unit .unit [] s!"{name}: Unit completion changed"
  let bool ← compile (← named program "bool") .bool []
  expectSuccess bool (.bool true) [] "builtin Boolean/group lowering changed"

private def replaceExpression (source : TypedSource) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : TypedSource := {
  source with nodes := source.nodes.map fun
    | .expression node => if node.id = id then .expression (change node) else .expression node
    | other => other
}

private def replaceStatement (source : TypedSource) (id : StatementId)
    (change : StatementNode → StatementNode) : TypedSource := {
  source with nodes := source.nodes.map fun
    | .statement node => if node.id = id then .statement (change node) else .statement node
    | other => other
}

private def expectError {α : Type} (label : String)
    (result : Except Frontend.SourceCoreBasic.Error α)
    (accept : Frontend.SourceCoreBasic.Error → Bool) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"{label}: unsupported carrier compiled")
  | .error error => assertTrue (accept error) s!"{label}: wrong error {reprStr error}"

private def testBoundaries (program : CheckedProgram) : IO Unit := do
  let function ← named program "tail"
  let source := function.typedBody
  let scope ← inputScope source
  let statements ← roots source
  let statement ← match statements with
    | [id] => pure id
    | _ => throw (IO.userError "tail fixture changed roots")
  let expression ← match source.lookupStatement? statement with
    | some { form := .expression id false, .. } => pure id
    | _ => throw (IO.userError "tail fixture changed final expression")
  let lowerExpr := fun source => Frontend.SourceCoreBasic.lowerExpression 20 source scope expression reason
  expectError "compile traversal fuel" (Frontend.SourceCoreBasic.lowerStatements 0 source scope statements .word reason)
    fun error => error matches .traversalExhausted _
  expectError "expression traversal fuel" (Frontend.SourceCoreBasic.lowerExpression 0 source scope expression reason)
    fun error => error matches .traversalExhausted _
  expectError "missing return" (Frontend.SourceCoreBasic.lowerStatements 0 source scope [] .word reason)
    fun error => error matches .missingReturn .word
  expectError "return type" (Frontend.SourceCoreBasic.lowerStatements 20 source scope statements .bool reason)
    fun error => error matches .typeMismatch _ .bool .word
  let required := replaceExpression source expression fun node => { node with requirements := [⟨0⟩] }
  expectError "expression requirements" (lowerExpr required)
    fun error => error matches .requirementsPresent _
  let coerced := replaceExpression source expression fun node =>
    { node with coercions := [{ requirement := ⟨0⟩, source := .word, target := .word }] }
  expectError "expression coercions" (lowerExpr coerced)
    fun error => error matches .coercionsPresent _
  let wrongType := replaceExpression source expression fun node => { node with type := .bool }
  expectError "local slot type" (lowerExpr wrongType)
    fun error => error matches .localRead (.slotTypeMismatch .bool .word)
  let wrongStatement := replaceStatement source statement fun node => { node with type := .bool }
  expectError "statement metadata" (Frontend.SourceCoreBasic.lowerStatements 20 wrongStatement scope statements .word reason)
    fun error => error matches .typeMismatch _ .word .bool
  expectError "nonfinal value statement"
    (Frontend.SourceCoreBasic.lowerStatements 20 source scope (statements ++ statements) .word reason)
    fun error => error matches .nonTailExpression _
  let literalSource := replaceExpression source expression fun node =>
    { node with form := .literal (.hexadecimal "0x2a") }
  match lowerExpr literalSource with
  | .ok lowered =>
      assertTrue (lowered.type == .word && Core.run 5 (.initial lowered.expression) == .done (.inRight .word (scalar 42)))
        "strict compatibility Word literal did not compile"
  | .error error => throw (IO.userError s!"strict literal rejected: {reprStr error}")
  let badLiteral := replaceExpression source expression fun node => { node with form := .literal (.decimal "x") }
  expectError "invalid Word literal" (lowerExpr badLiteral)
    fun error => error matches .invalidWordLiteral _ _
  let lambda := replaceExpression source expression fun node => { node with form := .lambda [] .word [] }
  expectError "unsupported lambda" (lowerExpr lambda)
    fun error => error matches .unsupportedExpression _ _
  let evidence ← named program "literalEvidence"
  expectError "integer-literal evidence remains explicit"
    (Frontend.SourceCoreBasic.lowerStatements 20 evidence.typedBody [] (← roots evidence.typedBody) .word reason)
    fun error => error matches .requirementsPresent _
  let blocked ← named program "blocked"
  expectError "unsupported block"
    (Frontend.SourceCoreBasic.lowerStatements 20 blocked.typedBody (← inputScope blocked.typedBody)
      (← roots blocked.typedBody) .word reason)
    fun error => error matches .unsupportedStatement _ (.block _)

private def testBindingAndAssignmentMetadata (program : CheckedProgram) : IO Unit := do
  let function ← named program "sequence"
  let source := function.typedBody
  let scope ← inputScope source
  let statements ← roots source
  let (letId, assignId, rest) ← match statements with
    | letId :: assignId :: rest => pure (letId, assignId, rest)
    | _ => throw (IO.userError "sequence fixture lost its declaration and assignment")
  let binder ← match source.lookupStatement? letId with
    | some { form := .letDecl binder none, .. } => pure binder
    | _ => throw (IO.userError "sequence fixture lost its absent local")
  let bindingCase := fun binder =>
    Frontend.SourceCoreBasic.lowerStatements 100
      (replaceStatement source letId fun node => { node with form := .letDecl binder none })
      scope statements (.product .word .bool) reason
  expectError "polymorphic binding" (bindingCase { binder with
    scheme := { binder.scheme with quantified := [⟨0⟩] } })
    fun error => error matches .polymorphicBinding _
  expectError "qualified binding" (bindingCase { binder with schemeRequirements := [{
    templateRequirement := ⟨0⟩, predicate := ProgramSignatures.builtinIntPredicate .word }] })
    fun error => error matches .bindingRequirementsPresent _
  expectError "comptime binding" (bindingCase { binder with comptime := true })
    fun error => error matches .comptimeBinding _
  let foreignOwner := { source.owner with declarationIndex := source.owner.declarationIndex + 100 }
  expectError "binding owner" (bindingCase { binder with id := { binder.id with owner := foreignOwner } })
    fun error => error matches .ownerMismatch _ _
  expectError "duplicate binding"
    (Frontend.SourceCoreBasic.lowerStatements 100 source ((binder.id, .word) :: scope)
      statements (.product .word .bool) reason)
    fun error => error matches .duplicateBinding _
  let (assignment, rhs) ← match source.lookupStatement? assignId with
    | some { form := .assignValue assignment .equal rhs, .. } => pure (assignment, rhs)
    | _ => throw (IO.userError "sequence fixture lost its plain assignment")
  let localScope := (binder.id, Core.Ty.word) :: scope
  let assignmentCase := fun assignment operator =>
    Frontend.SourceCoreBasic.lowerStatements 100
      (replaceStatement source assignId fun node => { node with form := .assignValue assignment operator rhs })
      localScope (assignId :: rest) (.product .word .bool) reason
  expectError "compound assignment" (assignmentCase assignment .add)
    fun error => error matches .unsupportedAssignmentOperator .add
  expectError "assignment requirements" (assignmentCase { assignment with requirements := [⟨0⟩] } .equal)
    fun error => error matches .assignmentRequirementsPresent _
  expectError "projected assignment" (assignmentCase { assignment with
    target := { assignment.target with projections := [.member "field" 0] } } .equal)
    fun error => error matches .projectedAssignment _
  expectError "assignment owner" (assignmentCase { assignment with
    target := { assignment.target with root := { binder.id with owner := foreignOwner } } } .equal)
    fun error => error matches .ownerMismatch _ _
  expectError "assignment missing binding" (assignmentCase { assignment with
    target := { assignment.target with root := { binder.id with binderIndex := 1000 } } } .equal)
    fun error => error matches .missingBinding _
  expectError "assignment target type" (assignmentCase { assignment with
    target := { assignment.target with type := .bool } } .equal)
    fun error => error matches .typeMismatch _ .word .bool
  let wrongRhs := replaceExpression source rhs fun node => {
    node with type := .bool, form := .reference "true" (.builtinBoolean true) }
  expectError "assignment RHS type"
    (Frontend.SourceCoreBasic.lowerStatements 100 wrongRhs localScope (assignId :: rest)
      (.product .word .bool) reason)
    fun error => error matches .typeMismatch _ .word .bool
  let wrongInitializer := replaceStatement wrongRhs letId fun node =>
    { node with form := .letDecl binder (some rhs) }
  expectError "initializer type"
    (Frontend.SourceCoreBasic.lowerStatements 100 wrongInitializer scope statements (.product .word .bool) reason)
    fun error => error matches .typeMismatch _ .word .bool
  let foreignStatement : StatementId := ⟨{ letId.occurrence with owner := foreignOwner }⟩
  expectError "statement occurrence owner"
    (Frontend.SourceCoreBasic.lowerStatements 100 source scope [foreignStatement] .unit reason)
    fun error => error matches .ownerMismatch _ _

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"basic source fixtures failed checking: {reprStr errors}")
  testExecution program
  testBoundaries program
  testBindingAndAssignmentMetadata program

end Tests.SourceCoreBasic
end

section
-- leanmerge: from Solcore.Test.SourceCoreBasicEntry
/-! Preparation consumes real canonical specialization plans. Invocation checks
Core values without importing the typed-source evaluator or recompiling code. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.Value
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCoreBasicEntry

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceCoreBasicEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value
private def reason : Core.Word := word 93

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function mutate(flag: Bool, first: Word, second: Word) returns (Word, Bool) {",
    "  let value: Word; value = first; value = second; return (value, flag);",
    "}",
    "function keep<T>(input: T) returns (T) { let stored: T = input; return stored; }",
    "function absent(input: Word) returns (Word) { let value: Word; return value; }",
    "function staged(comptime input: (Word, Bool)) returns (Word, Bool) {",
    "  let stored: (Word, Bool) = input; return stored;",
    "}",
    "function nested(input: (Word, (Bool, Word))) returns (Word, (Bool, Word)) { return input; }",
    "function blocked(input: Word) returns (Word) { { return input; } }",
    "function scoped(flag: Bool, initial: Word, replacement: Word) returns (Word) {",
    "  let value: Word = initial; { let value: Word = replacement; value = initial; }",
    "  if (flag) { value = replacement; } return value;",
    "}",
    "function branchFailure(flag: Bool) returns (Word) {",
    "  let absent: Word; return flag ? absent : absent;",
    "}",
    "function chooseFailure(flag: Bool, value: Word) returns (Word) {",
    "  let absent: Word; return flag ? value : absent;",
    "}",
    "function loop(flag: Bool) { while (flag) { break; } }",
    "function stagedResult(comptime input: Word) returns (comptime<Word>) { return input; }",
    "function literalEvidence() returns (Word) { return 1; }"
  ] }]
  externalLibraries := []
}

private def request (program : CheckedProgram) (name : String)
    (types : List TypeSystem.Ty := []) : IO SourceSpecializationWorklist.Request := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"entry fixture not found: {name}")
  assertTrue (signature.scheme.parameters.length == types.length) "specialization arity changed"
  pure { declaration := signature.id, parameterSubstitution := signature.scheme.parameters.zip types }

private def plan (program : CheckedProgram) (requests : List SourceSpecializationWorklist.Request) : IO Plan := do
  match SourceSpecializationWorklist.run program requests 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"entry worklist failed: {reprStr result}")

private def preparePlan (program : CheckedProgram) (plan : Plan) : IO PreparedProgram := do
  match prepare program plan 100 reason with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"entry preparation failed: {reprStr error}")

private def entryAt (prepared : PreparedProgram) (index : Nat) : IO Entry := do
  match prepared.entries[index]? with
  | some entry => pure entry
  | none => throw (IO.userError "prepared seed entry missing")

private def invoke (entry : Entry) (values : List Core.Value) (fuel : Nat := 1000) : IO (Result entry.resultType) := do
  match entry.run values fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"entry invocation rejected: {reprStr error}")

private def testPreparedRuns (program : CheckedProgram) : IO Unit := do
  let mutate ← request program "mutate"
  let keepWord ← request program "keep" [.word]
  let keepProduct ← request program "keep" [.product .word .bool]
  let absent ← request program "absent"
  let staged ← request program "staged"
  let nested ← request program "nested"
  let inputPlan ← plan program [mutate, keepWord, keepProduct, absent, staged, nested, mutate]
  let prepared ← preparePlan program inputPlan
  assertTrue (prepared.entries.map (·.key) == inputPlan.seedKeys)
    "preparation changed canonical seed order or removed duplicate roots"
  assertTrue (prepared.plan.seedKeys == inputPlan.seedKeys)
    "prepared plan changed the public seed catalog"
  let entry ← entryAt prepared 0
  assertTrue (entry.inputs.map (·.type) == [.bool, .word, .word])
    "entry inputs must retain original source parameter order"
  let arguments := [.bool true, scalar 11, scalar 29]
  let initial ← match entry.start arguments with
    | .ok checkpoint => pure checkpoint
    | .error error => throw (IO.userError s!"entry start failed: {reprStr error}")
  assertTrue (initial.state.store == arguments.map present)
    "input allocation must follow source order"
  assertTrue (initial.state.control == .eval entry.body [
      .cellRef (Core.OptionalCell.cellType .word) 2,
      .cellRef (Core.OptionalCell.cellType .word) 1,
      .cellRef (Core.OptionalCell.cellType .bool) 0])
    "prepared environment must use newest-first references without copying the input store"
  let result ← invoke entry arguments
  assertTrue (result.observation == .succeeded (.pair (scalar 29) (.bool true))
      [present (.bool true), present (scalar 11), present (scalar 29), present (scalar 29)])
    "prepared mutation result or shared local cell changed"
  let second ← invoke entry [.bool false, scalar 2, scalar 7]
  assertTrue (second.observation == .succeeded (.pair (scalar 7) (.bool false))
      [present (.bool false), present (scalar 2), present (scalar 7), present (scalar 7)])
    "reusing a cached entry must prepare a fresh input frame"
  let paused ← invoke entry arguments 10
  let checkpoint ← match paused.checkpoint? with
    | some checkpoint => pure checkpoint
    | none => throw (IO.userError "small execution fuel must return a typed checkpoint")
  assertTrue ((checkpoint.resume 990).observation == result.observation)
    "resuming a prepared entry must preserve its values and store"
  let kept ← invoke (← entryAt prepared 1) [scalar 8]
  assertTrue (kept.observation == .succeeded (scalar 8) [present (scalar 8), present (scalar 8)])
    "specialized generic Word input was not compiled through the plan"
  let pair : Core.Value := .pair (scalar 5) (.bool true)
  let keptPair ← invoke (← entryAt prepared 2) [pair]
  assertTrue (keptPair.observation == .succeeded pair [present pair, present pair])
    "specialized generic product input lost its complete structure"
  let absentEntry ← entryAt prepared 3
  let failed ← invoke absentEntry [scalar 3]
  let read ← match absentEntry.faultSites.reads with
    | [site] => pure site
    | _ => throw (IO.userError "uninitialized fixture lost its unique read site")
  assertTrue (read.reason != Core.Word.zero && failed.observation ==
      .failed read.reason [present (scalar 3), .inLeft .word .unit])
    "uninitialized entry local must return a typed language failure"
  assertTrue (decide (absentEntry.failureDiagnostic? read.reason = some {
      error := .uninitializedLocal read.binder, site := .occurrence read.expression.occurrence,
      span := some read.span })) "uninitialized diagnostic lost its source identity"
  let stagedEntry ← entryAt prepared 4
  assertTrue (stagedEntry.inputs.map (·.comptime) == [true]) "comptime input marker was discarded"
  let stagedResult ← invoke stagedEntry [pair]
  assertTrue (stagedResult.observation == .succeeded pair [present pair, present pair])
    "staged scalar/product input must retain its exact value"
  let nestedValue : Core.Value := .pair (scalar 6) (.pair (.bool false) (scalar 12))
  let nestedResult ← invoke (← entryAt prepared 5) [nestedValue]
  assertTrue (nestedResult.observation == .succeeded nestedValue [present nestedValue])
    "deep product input tree was flattened or reordered"
  match prepared.findEntry? entry.key with
  | some found => assertTrue (found.body == entry.body) "findEntry? returned a different prepared body"
  | none => throw (IO.userError "findEntry? lost a retained seed")

private def expectError {α : Type} (label : String) (result : Except Error α)
    (accept : Error → Bool) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"{label}: invalid boundary input was accepted")
  | .error error => assertTrue (accept error) s!"{label}: wrong error {reprStr error}"

private def testInputRejections (program : CheckedProgram) : IO Unit := do
  let inputPlan ← plan program [← request program "nested"]
  let entry ← entryAt (← preparePlan program inputPlan) 0
  expectError "input count" (entry.start [])
    fun error => error matches .argumentCountMismatch 1 0
  expectError "input structural type" (entry.start [.pair (scalar 1) (.pair (scalar 2) (.bool true))])
    fun error => error matches .inputTypeMismatch 0 _ _
  expectError "nested external cell" (entry.start [.pair (scalar 1) (.pair (.bool true) (.cellRef .word 0))])
    fun error => error matches .inputShape 0 _
  expectError "nested external closure" (entry.start [
    .pair (scalar 1) (.pair (.bool true) (.closure .unit .word (.word (word 0)) []))])
    fun error => error matches .inputShape 0 _
  expectError "sum payload" (entry.start [.inRight .unit (.pair (scalar 1) (.pair (.bool true) (scalar 2)))])
    fun error => error matches .inputShape 0 _
  let valid := [.pair (scalar 1) (.pair (.bool true) (scalar 2))]
  expectError "unsupported initial store" (entry.start valid [.word (word 4)])
    fun error => error matches .initialStoreUnsupported 1

private def testPreparationRejections (program : CheckedProgram) : IO Unit := do
  let valid ← plan program [← request program "mutate"]
  expectError "noncanonical plan" (prepare program { valid with seedKeys := [] } 100 reason)
    fun error => error matches .preparation .nonCanonicalInputPlan
  expectError "compilation fuel" (prepare program valid 0 reason)
    fun error => error matches .lowering (.traversalExhausted _)
  for (name, accepts) in ([
      ("stagedResult", fun error => error matches .stagedResultUnsupported _)] :
      List (String × (Error → Bool))) do
    let input ← plan program [← request program name]
    expectError name (prepare program input 100 reason) accepts

private def prepareNamed (program : CheckedProgram) (name : String) : IO (Plan × Entry) := do
  let input ← plan program [← request program name]
  pure (input, ← entryAt (← preparePlan program input) 0)

private def testControlAndDiagnostics (program : CheckedProgram) : IO Unit := do
  let (_, literal) ← prepareNamed program "literalEvidence"
  assertTrue ((← invoke literal []).observation == .succeeded (scalar 1) [])
    "prepared entry did not compile its authenticated Word integer literal"
  let (_, blocked) ← prepareNamed program "blocked"
  assertTrue ((← invoke blocked [scalar 5]).observation ==
      .succeeded (scalar 5) [present (scalar 5)]) "nested block return was not compiled"
  let (_, scopedEntry) ← prepareNamed program "scoped"
  for flag in [false, true] do
    let actual ← invoke scopedEntry [.bool flag, scalar 11, scalar 29]
    let expected := if flag then scalar 29 else scalar 11
    assertTrue (actual.observation == .succeeded expected
        [present (.bool flag), present (scalar 11), present (scalar 29), present expected, present (scalar 11)])
      "block scope or conditional mutation changed the outer shared cell"
  let (input, branch) ← prepareNamed program "branchFailure"
  let source ← match input.specializations with
    | [specialized] => pure specialized.function.typedBody
    | _ => throw (IO.userError "branch fixture plan should have one specialization")
  let expectedReads := source.nodes.filterMap fun
    | .expression node => match node.form with
      | .reference "absent" (.local binder) => some (node, binder)
      | _ => none
    | _ => none
  let (left, right) ← match expectedReads with
    | [left, right] => pure (left, right)
    | _ => throw (IO.userError "branch fixture must retain two distinct reads")
  assertTrue (decide (left.2 = right.2 ∧ left.1.id ≠ right.1.id ∧ left.1.span ≠ right.1.span))
    "branch fixture no longer tests two occurrences of the same binder"
  let leftReason := branch.faultSites.reasonAt left.1.id
  let rightReason := branch.faultSites.reasonAt right.1.id
  assertTrue (leftReason != Core.Word.zero && rightReason != Core.Word.zero && leftReason != rightReason)
    "distinct read occurrences must receive distinct nonzero reasons"
  for (flag, node, binder, token) in [
      (true, left.1, left.2, leftReason), (false, right.1, right.2, rightReason)] do
    let actual ← invoke branch [.bool flag]
    assertTrue (actual.observation == .failed token [present (.bool flag), .inLeft .word .unit])
      "conditional execution reported the untaken read occurrence"
    assertTrue (decide (branch.failureDiagnostic? token = some {
        error := .uninitializedLocal binder, site := .occurrence node.id.occurrence,
        span := some node.span })) "failure token lost its original binder, occurrence or span"
  assertTrue (decide (branch.failureDiagnostic? Core.Word.zero = some {
      error := .functionFellThrough .word, site := .declaration branch.key.declaration, span := none }))
    "reserved zero token must classify non-Unit function fallthrough"
  assertTrue (decide (branch.failureDiagnostic? (word 999) = none)) "unknown reason produced a diagnostic"
  let (_, choose) ← prepareNamed program "chooseFailure"
  assertTrue ((← invoke choose [.bool true, scalar 6]).observation == .succeeded (scalar 6)
      [present (.bool true), present (scalar 6), .inLeft .word .unit])
    "untaken uninitialized branch was evaluated"

example (entry : Entry) :
    SourceCoreScalar.lowerType (.declaration entry.key.declaration) entry.sourceResultType =
      .ok entry.resultType := entry.resultProjection

example (type : Core.Ty) (result : Result type) (value : Core.Value) (store : Core.Store)
    (succeeded : result.observation = .succeeded value store) :
    ∃ world, Core.RuntimeStoreHasTypes world store ∧ Core.RuntimeValueHasType world value type :=
  result.success_typed succeeded

example (type : Core.Ty) (result : Result type) (error : Core.MachineFault) (state : Core.State) :
    result.observation ≠ .internalFault error state := result.ne_internalFault error state

example (type : Core.Ty) (checkpoint next : Checkpoint type) (spent additional : Nat)
    (exhausted : Core.runStateful spent checkpoint.state = .outOfFuel next.state) :
    (next.resume additional).observation = (checkpoint.resume (spent + additional)).observation :=
  checkpoint.resume_after_exhaustion next spent additional exhausted

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"entry source fixtures failed checking: {reprStr errors}")
  testPreparedRuns program
  testInputRejections program
  testPreparationRejections program
  testControlAndDiagnostics program

end Tests.SourceCoreBasicEntry
end

section
-- leanmerge: from Solcore.Test.SourceCoreCalls
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreCalls

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreCalls

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value
private def reason : Core.Word := word 91
private def internalReason : Core.Word := word 99

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function zero() returns (Word) { return 7; }",
    "function increment(value: Word) returns (Word) { return value + 1; }",
    "function combine(a: Word, b: Word, c: Word) returns (Word) { return a + b + c; }",
    "function nested(value: Word) returns (Word) { return combine(zero(), increment(value), value) * 2; }",
    "function countdown(n: Word) returns (Word) { return n == 0 ? n : countdown(n - 1); }",
    "function even(n: Word) returns (Bool) { return n == 0 ? true : odd(n - 1); }",
    "function odd(n: Word) returns (Bool) { return n == 0 ? false : even(n - 1); }",
    "function conditional(flag: Bool, value: Word) returns (Word, Bool) { return ((flag ? increment(value) : zero()), (flag || increment(value) > 0)); }",
    "function echoProduct(value: (Word, Bool)) returns (Word, Bool) { return value; }",
    "function productCall(value: Word) returns (Word, Bool) { return echoProduct((value, true)); }",
    "function staged(comptime value: Word) returns (Word) { return value; }",
    "function stagedCall() returns (Word) { return staged(1); }"
  ] }]
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"missing call fixture {name}")

private def prepare (program : CheckedProgram) (name : String) : IO Plan := do
  let plan ← match SourceSpecializationWorklist.run program [← request program name] 100 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"call plan failed: {reprStr result}")
  match SourceCompilationPlan.prepareExecutablePlanEvidence program plan with
  | .ok plan => pure plan
  | .error error => throw (IO.userError s!"call plan preparation failed: {reprStr error}")

private def seed (plan : Plan) : IO Key :=
  match plan.seedKeys with
  | key :: _ => pure key
  | [] => throw (IO.userError "missing seed")

private def rejected {error value : Type} : Except error value → Bool
  | .error _ => true
  | .ok _ => false

private def signature (specialized : SourceSpecialization.SpecializedFunction) : IO Signature := do
  match specialized.function.type with
  | .function parameter result =>
      match SourceCoreBasic.projectType (.declaration specialized.key.declaration) parameter,
          SourceCoreBasic.projectType (.declaration specialized.key.declaration) result with
      | .ok parameterType, .ok resultType => pure { key := specialized.key, parameterType, resultType }
      | _, _ => throw (IO.userError "call signature projection failed")
  | _ => throw (IO.userError "call fixture does not have function type")

private def returned (source : TypedSource) : IO ExpressionId := do
  match source.nodes.findSome? fun
    | .statement node => match node.form with
      | .returnStmt (some id) => some id
      | _ => none
    | _ => none with
  | some id => pure id
  | none => throw (IO.userError "call fixture must return one expression")

private def inputScope (source : TypedSource) : IO Scope :=
  source.inputs.foldlM (fun scope binder => do
    match SourceCoreBasic.lowerBinder source scope binder with
    | .ok type => pure ((binder.id, type) :: scope)
    | .error error => throw (IO.userError s!"call input rejected: {reprStr error}")) []

private structure Compiled where
  context : SourceCoreCalls.Context
  source : TypedSource
  scope : Scope
  id : ExpressionId
  lowered : LoweredExpr

private def compile (plan : Plan) (owner : Key) (administrativeCount : Nat := 0) : IO Compiled := do
  let specialized ← match SourceCompilationPlan.exactSpecialization plan owner with
    | .ok specialized => pure specialized
    | .error error => throw (IO.userError s!"caller not found: {reprStr error}")
  let globals ← plan.specializations.reverse.mapM signature
  let source := specialized.function.typedBody
  let context : SourceCoreCalls.Context := {
    plan, owner, globals, administrativePrefix := administrativeCount
    solvedRequirements := specialized.function.solvedRequirements
    internalReason := internalReason }
  let scope ← inputScope source
  let id ← returned source
  let lowered ← match lowerExpressionWithReasons 100 context source scope id (fun _ => reason) with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError s!"call lowering rejected: {reprStr error}")
  let types := SourceCoreLocalCell.coreContext scope ++ List.replicate administrativeCount .unit ++ globals.map (·.referenceType)
  assertTrue (decide (Core.infer? types lowered.expression = some (Core.LanguageResult.resultType lowered.type)))
    "lowered call failed Core type checking"
  pure { context, source, scope, id, lowered }

/-- Test-only closures use the same public expression compiler, including
recursive calls. Allocate parameter cells in source order from one raw bundle. -/
private def closureBody (plan : Plan) (global : Signature) : IO Core.Expr := do
  let compiled ← compile plan global.key 1
  let inputs := compiled.scope.reverse
  let projection (index count : Nat) : Core.Expr :=
    let rec select (index count : Nat) (bundle : Core.Expr) : Core.Expr :=
      match count with
      | 0 => .unit
      | 1 => bundle
      | count + 2 => if index = 0 then .first bundle else select (index - 1) (count + 1) (.second bundle)
    select index count (.var index)
  let body := (inputs.zipIdx).foldr (fun ((_, type), index) body =>
    .letE (Core.OptionalCell.allocateInitialized type (projection index inputs.length)) body) compiled.lowered.expression
  assertTrue (decide (Core.infer? (global.parameterType :: compiled.context.globals.map (·.referenceType)) body =
    some (Core.LanguageResult.resultType global.resultType))) "compiled global closure body failed Core checker"
  pure body

private def execute (compiled : Compiled) (arguments : List (Option Core.Value)) (fuel : Nat := 5000) :
    IO Core.StatefulRunResult := do
  let globals := compiled.context.globals
  let references := globals.zipIdx.map fun (global, index) =>
    Core.Value.cellRef (Core.OptionalCell.cellType global.functionType) index
  let globalStore ← globals.mapM fun global => do
    pure (present (.closure global.parameterType (Core.LanguageResult.resultType global.resultType)
      (← closureBody compiled.context.plan global) references))
  let inputs := compiled.scope.reverse
  assertTrue (inputs.length == arguments.length) "call fixture input arity mismatch"
  let inputStore := (inputs.zip arguments).map fun ((_, type), value) =>
    match value with
    | some value => present value
    | none => Core.Value.inLeft type .unit
  let inputReferences := (inputs.zipIdx.map fun ((_, type), index) =>
    Core.Value.cellRef (Core.OptionalCell.cellType type) (globals.length + index)).reverse
  let environment := inputReferences ++ List.replicate compiled.context.administrativePrefix .unit ++ references
  pure (Core.runStateful fuel (.initial compiled.lowered.expression environment (globalStore ++ inputStore)))

private def testCompiledCalls (program : CheckedProgram) : IO Unit := do
  let nestedPlan ← prepare program "nested"
  let nested ← compile nestedPlan (← seed nestedPlan) 2
  match Core.LanguageResult.observeResult (← execute nested [some (scalar 4)]) with
  | .succeeded value store =>
      assertTrue (value == scalar 32) "nested/zero/three-argument calls changed their result"
      -- Four initial global cells, caller input, increment input, then combine's three inputs.
      assertTrue ((store.drop nested.context.globals.length) ==
        [present (scalar 4), present (scalar 4), present (scalar 7), present (scalar 5), present (scalar 4)])
        "calls did not allocate argument cells in source order"
  | result => throw (IO.userError s!"nested calls did not complete: {reprStr result}")
  match Core.LanguageResult.observeResult (← execute nested [none]) with
  | .failed token store =>
      assertTrue (token == reason) "nested call lost the failed argument's diagnostic"
      assertTrue (store.drop nested.context.globals.length == [.inLeft .word .unit])
        "failed argument allocated later function parameters"
  | result => throw (IO.userError s!"uninitialized call argument did not fail: {reprStr result}")
  let recursionPlan ← prepare program "countdown"
  let recursion ← compile recursionPlan (← seed recursionPlan) 1
  match Core.LanguageResult.observeResult (← execute recursion [some (scalar 4)]) with
  | .succeeded value store =>
      assertTrue (value == scalar 0) "self recursive call changed its result"
      assertTrue ((store.drop recursion.context.globals.length) ==
        [present (scalar 4), present (scalar 3), present (scalar 2), present (scalar 1), present (scalar 0)])
        "recursive calls did not retain shared store allocations"
  | result => throw (IO.userError s!"recursive call did not complete: {reprStr result}")
  match ← execute recursion [some (scalar 4)] 10 with
  | .outOfFuel checkpoint =>
      match Core.LanguageResult.observeResult (Core.runStateful 5000 checkpoint) with
      | .succeeded value _ => assertTrue (value == scalar 0) "resumed recursive call changed its result"
      | result => throw (IO.userError s!"recursive resume failed: {reprStr result}")
  | _ => throw (IO.userError "recursive call did not suspend with small fuel")
  let mutualPlan ← prepare program "even"
  let mutualCompiled ← compile mutualPlan (← seed mutualPlan)
  for (input, expected) in [(4, true), (3, false)] do
    match Core.LanguageResult.observeResult (← execute mutualCompiled [some (scalar input)]) with
    | .succeeded value store =>
        assertTrue (value == .bool expected) "mutual recursive call changed its result"
        assertTrue (store.length == mutualCompiled.context.globals.length + input + 1)
          "mutual recursion lost shared parameter allocations"
    | result => throw (IO.userError s!"mutual recursion did not complete: {reprStr result}")
  let conditionalPlan ← prepare program "conditional"
  let conditional ← compile conditionalPlan (← seed conditionalPlan)
  match Core.LanguageResult.observeResult (← execute conditional [some (.bool true), some (scalar 4)]) with
  | .succeeded value _ => assertTrue (value == .pair (scalar 5) (.bool true)) "nested conditional/tuple call failed"
  | result => throw (IO.userError s!"conditional call failed: {reprStr result}")

  let productPlan ← prepare program "productCall"
  let productEntry ← compile productPlan (← seed productPlan)
  match Core.LanguageResult.observeResult (← execute productEntry [some (scalar 8)]) with
  | .succeeded value store =>
      assertTrue (value == .pair (scalar 8) (.bool true)) "one product argument was unpacked as two parameters"
      assertTrue (store.drop productEntry.context.globals.length ==
        [present (scalar 8), present (.pair (scalar 8) (.bool true))])
        "product parameter did not retain its one-cell identity"
  | result => throw (IO.userError s!"product call failed: {reprStr result}")

private def testRejectedMetadata (program : CheckedProgram) : IO Unit := do
  let plan ← prepare program "nested"
  let compiled ← compile plan (← seed plan)
  let reject (context : SourceCoreCalls.Context) (source : TypedSource := compiled.source) : IO Unit := do
    assertTrue (rejected (lowerExpressionWithReasons 100 context source compiled.scope compiled.id (fun _ => reason)))
      "forged call metadata was accepted"
  reject { compiled.context with plan := { plan with callEdges := [] } }
  reject { compiled.context with plan := { plan with callEdges := plan.callEdges ++ plan.callEdges } }
  reject { compiled.context with globals := [] }
  reject { compiled.context with globals := compiled.context.globals ++ compiled.context.globals }
  reject { compiled.context with globals := compiled.context.globals.map fun global => { global with parameterType := .bool } }
  reject { compiled.context with globals := compiled.context.globals.map fun global => { global with resultType := .bool } }
  let altered (change : ExpressionNode → ExpressionNode) : TypedSource :=
    { compiled.source with nodes := compiled.source.nodes.map fun
      | .expression node => .expression (change node)
      | node => node }
  reject compiled.context (altered fun node => match node.form with
    | .call callee arguments target => { node with form := .call callee (arguments ++ arguments) target }
    | _ => node)
  reject compiled.context (altered fun node => match node.form with
    | .call _ _ _ => { node with requirements := [⟨999⟩] }
    | _ => node)
  reject compiled.context (altered fun node => match node.form with
    | .reference _ (.declaration _) => { node with requirements := [⟨999⟩] }
    | _ => node)
  reject compiled.context (altered fun node => match node.form with
    | .call _ _ _ => { node with coercions := [{ requirement := ⟨999⟩, source := .word, target := .word }] }
    | _ => node)
  reject compiled.context (altered fun node => match node.form with
    | .reference _ (.declaration _) =>
        { node with coercions := [{ requirement := ⟨999⟩, source := .word, target := .word }] }
    | _ => node)
  reject { compiled.context with plan := { plan with specializations := plan.specializations.map fun specialized =>
    if specialized.key = compiled.context.owner then
      { specialized with assumptions := [ProgramSignatures.builtinIntPredicate .word] }
    else specialized } }
  let stagedPlan ← prepare program "stagedCall"
  let globals ← stagedPlan.specializations.reverse.mapM signature
  let specialized ← match SourceCompilationPlan.exactSpecialization stagedPlan (← seed stagedPlan) with
    | .ok specialized => pure specialized
    | .error error => throw (IO.userError s!"staged caller missing: {reprStr error}")
  assertTrue (rejected (lowerExpressionWithReasons 100
    { plan := stagedPlan, owner := specialized.key, globals, administrativePrefix := 0,
      solvedRequirements := specialized.function.solvedRequirements, internalReason }
    specialized.function.typedBody [] (← returned specialized.function.typedBody) (fun _ => reason)))
    "staged call entered the ordinary monomorphic profile"

private def testCallOrder (key : Key) : IO Unit := do
  let signature : Signature := { key, parameterType := .word, resultType := .word }
  let fn := signature.functionType
  let reference := Core.Value.cellRef (Core.OptionalCell.cellType fn) 0
  let noFunction := Core.Value.inLeft fn .unit
  let body := Core.LanguageResult.success (.var 0)
  let closure := Core.Value.closure .word (Core.LanguageResult.resultType .word) body []
  let expression := call signature 0
    (Core.LanguageResult.failure .word (.word reason)) internalReason
  assertTrue (Core.LanguageResult.observeResult (Core.runStateful 100 (.initial expression [reference] [noFunction])) ==
    .failed reason [noFunction]) "failed argument did not skip the uninitialized global read"
  let install := Core.LanguageResult.success
    (.letE (.storeCell (.var 0) (.inRight .unit (.lambda .word (Core.LanguageResult.resultType .word) body)))
      (.word (word 12)))
  let installedExpression := call signature 0 install internalReason
  assertTrue (decide (Core.infer? [signature.referenceType] installedExpression =
    some (Core.LanguageResult.resultType .word))) "store-order fixture failed Core checker"
  let observed := Core.LanguageResult.observeResult
    (Core.runStateful 200 (.initial installedExpression [reference] [noFunction]))
  -- The installed closure captures the original global reference and sees the latest store.
  let capturedClosure := Core.Value.closure .word (Core.LanguageResult.resultType .word) body [reference]
  assertTrue (observed == .succeeded (scalar 12) [present capturedClosure])
    "global cell was read before the argument installed its closure"
  assertTrue (Core.LanguageResult.observeResult (Core.runStateful 100 (.initial
    (call signature 0 (Core.LanguageResult.success (.word (word 5))) internalReason)
    [reference] [present closure])) == .succeeded (scalar 5) [present closure])
    "direct call did not pass its argument payload"

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"call fixtures failed source checking: {reprStr error}")
  testCompiledCalls program
  testRejectedMetadata program
  testCallOrder (← seed (← prepare program "zero"))

end Tests.SourceCoreCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreControl
/-! Actual retained-source lowering for conditionals, blocks and early returns.
Parsed Word parameters avoid integer-literal evidence. The harness allocates
input cells in source order, then executes the generated Core body. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreControl

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value
private def reason : Core.Word := word 87
private def fellThrough : Core.Word := word 88

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function early(flag: Bool, initial: Word, replacement: Word) returns (Word) {",
    "  let value: Word = initial;",
    "  { let inner: Word = replacement; if (flag) { return value; } value = inner; }",
    "  value = replacement; return value;",
    "}",
    "function scoped(flag: Bool, initial: Word, replacement: Word) returns (Word) {",
    "  let value: Word = initial; { let value: Word = replacement; value = initial; }",
    "  if (flag) { value = replacement; } return value;",
    "}",
    "function choices(flag: Bool, left: Word, right: Word) returns (Word, Bool) {",
    "  return ((flag ? (flag ? left : right) : right), (flag ? true : false));",
    "}",
    "function chooseFailure(flag: Bool, value: Word) returns (Word) {",
    "  let absent: Word; return flag ? value : absent;",
    "}",
    "function conditionFailure(initial: Word, replacement: Word) returns (Word) {",
    "  let value: Word = initial; let absent: Bool;",
    "  if (absent) { value = replacement; } else { value = replacement; } return value;",
    "}",
    "function nestedTail(value: Word, replacement: Word) returns (Word) {",
    "  { value; } return replacement;",
    "}",
    "function nestedOnly(flag: Bool) { if (flag) { true; } else { false; } }",
    "function nonTail(value: Word, replacement: Word) returns (Word) { value; return replacement; }",
    "function direct(value: Word) returns (Word) { return value; return 1; }",
    "function loop(flag: Bool) { while (flag) { break; } }"
  ] }]
  externalLibraries := []
}

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction := do
  match program.functions.find? (fun function =>
    match program.environment.declaration? function.declaration with
    | some declaration => declaration.name == some name
    | none => false) with
  | some function => pure function
  | none => throw (IO.userError s!"missing control fixture {name}")

private def roots (source : TypedSource) : IO (List StatementId) :=
  source.roots.mapM fun
    | .statement id => pure id
    | _ => throw (IO.userError "expected statement roots")

private def inputScope (source : TypedSource) : IO SourceCoreControl.Scope :=
  source.inputs.foldlM (fun scope binder => do
    match SourceCoreBasic.lowerBinder source scope binder with
    | .ok type => pure ((binder.id, type) :: scope)
    | .error error => throw (IO.userError s!"control input rejected: {reprStr error}")) []

private def closeInputs (scope : SourceCoreControl.Scope)
    (arguments : List Core.Expr) (body : Core.Expr) : Core.Expr :=
  (scope.reverse.zip arguments).foldr (fun entry body =>
    .letE (Core.OptionalCell.allocateInitialized entry.1.2 entry.2) body) body

private def compileSource (source : TypedSource) (resultType : Core.Ty)
    (arguments : List Core.Expr) (reasonAt : ExpressionId → Core.Word := fun _ => reason) :
    IO Core.Program := do
  let scope ← inputScope source
  assertTrue (scope.length == arguments.length) "control argument count mismatch"
  let expression ← match SourceCoreControl.lowerStatementsWithReasons 100 source scope
      (← roots source) resultType reasonAt fellThrough with
    | .ok expression => pure expression
    | .error error => throw (IO.userError s!"control lowering rejected: {reprStr error}")
  assertTrue (decide (Core.infer? (SourceCoreLocalCell.coreContext scope) expression =
      some (Core.LanguageResult.resultType resultType))) "open control body is ill typed"
  let program : Core.Program := {
    resultType := Core.LanguageResult.resultType resultType
    body := closeInputs scope arguments expression
  }
  assertTrue program.check "closed control body is ill typed"
  pure program

private def compile (function : CheckedFunction) (resultType : Core.Ty)
    (arguments : List Core.Expr) : IO Core.Program :=
  compileSource function.typedBody resultType arguments

private def expect (program : Core.Program) (value : Core.Value) (store : Core.Store)
    (message : String) : IO Unit :=
  assertTrue (program.runStateful 2000 == .done value store) message

private def testExecution (checked : CheckedProgram) : IO Unit := do
  let early ← named checked "early"
  let taken ← compile early .word [.bool true, literal 11, literal 29]
  expect taken (.inRight .word (scalar 11))
    [present (.bool true), present (scalar 11), present (scalar 29), present (scalar 11), present (scalar 29)]
    "nested return evaluated trailing assignments or lost block locals"
  let continued ← compile early .word [.bool false, literal 11, literal 29]
  expect continued (.inRight .word (scalar 29))
    [present (.bool false), present (scalar 11), present (scalar 29), present (scalar 29), present (scalar 29)]
    "nested fallthrough failed to run outer assignments"
  let scopedFunction ← named checked "scoped"
  let outer ← compile scopedFunction .word [.bool false, literal 11, literal 29]
  expect outer (.inRight .word (scalar 11))
    [present (.bool false), present (scalar 11), present (scalar 29), present (scalar 11), present (scalar 11)]
    "shadowed block binding escaped its lexical scope"
  let shared ← compile scopedFunction .word [.bool true, literal 11, literal 29]
  expect shared (.inRight .word (scalar 29))
    [present (.bool true), present (scalar 11), present (scalar 29), present (scalar 29), present (scalar 11)]
    "conditional assignment did not update the outer shared cell"
  let choices ← named checked "choices"
  let selected ← compile choices (.product .word .bool) [.bool true, literal 11, literal 29]
  expect selected (.inRight .word (.pair (scalar 11) (.bool true)))
    [present (.bool true), present (scalar 11), present (scalar 29)]
    "conditional expression recursion inside groups and tuples changed"
  let alternative ← compile choices (.product .word .bool) [.bool false, literal 11, literal 29]
  expect alternative (.inRight .word (.pair (scalar 29) (.bool false)))
    [present (.bool false), present (scalar 11), present (scalar 29)]
    "conditional expression selected the wrong alternative"
  let chooseFailure ← named checked "chooseFailure"
  let success ← compile chooseFailure .word [.bool true, literal 11]
  expect success (.inRight .word (scalar 11))
    [present (.bool true), present (scalar 11), .inLeft .word .unit]
    "untaken conditional branch evaluated its uninitialized read"
  let failure ← compile chooseFailure .word [.bool false, literal 11]
  expect failure (.inLeft .word (.word reason))
    [present (.bool false), present (scalar 11), .inLeft .word .unit]
    "selected conditional failure was lost"
  let conditionFailure ← compile (← named checked "conditionFailure") .word [literal 11, literal 29]
  expect conditionFailure (.inLeft .word (.word reason))
    [present (scalar 11), present (scalar 29), present (scalar 11), .inLeft .bool .unit]
    "condition failure evaluated a branch or the tail"
  let nestedTail ← compile (← named checked "nestedTail") .word [literal 11, literal 29]
  expect nestedTail (.inRight .word (scalar 29)) [present (scalar 11), present (scalar 29)]
    "nested block tail expression became an implicit function return"
  let nestedOnly ← compile (← named checked "nestedOnly") .unit [.bool true]
  expect nestedOnly (.inRight .word .unit) [present (.bool true)]
    "nested conditional tail expression did not fall through as Unit"
  let direct ← compile (← named checked "direct") .word [literal 11]
  expect direct (.inRight .word (scalar 11)) [present (scalar 11)]
    "explicit return lowered its unsupported trailing integer-literal evidence"
  match taken.runStateful 10 with
  | .outOfFuel checkpoint =>
      assertTrue (Core.runStateful 1990 checkpoint == taken.runStateful 2000)
        "control resumption changed the final result or heap"
  | _ => throw (IO.userError "control fixture should suspend at fuel 10")

private def testReasonSites (checked : CheckedProgram) : IO Unit := do
  let function ← named checked "chooseFailure"
  let id ← match function.typedBody.nodes.findSome? fun
      | .expression node => match node.form with
          | .reference "absent" (.local _) => some node.id
          | _ => none
      | _ => none with
    | some id => pure id
    | none => throw (IO.userError "missing uninitialized-read site")
  let siteReason := word 123
  let program ← compileSource function.typedBody .word [.bool false, literal 11]
    (fun current => if current = id then siteReason else reason)
  expect program (.inLeft .word (.word siteReason))
    [present (.bool false), present (scalar 11), .inLeft .word .unit]
    "reason provider was replaced by the enclosing conditional's token"

private def testBoundaries (checked : CheckedProgram) : IO Unit := do
  let function ← named checked "nonTail"
  let changed : TypedSource := { function.typedBody with nodes := function.typedBody.nodes.map fun
    | .statement node => match node.form with
        | .expression id true => .statement { node with type := .word, form := .expression id false }
        | _ => .statement node
    | node => node }
  let program ← compileSource changed .word [literal 11, literal 29]
  expect program (.inRight .word (scalar 29)) [present (scalar 11), present (scalar 29)]
    "non-tail expression without semicolon was rejected or returned early"
  let loop ← named checked "loop"
  let source := loop.typedBody
  let scope ← inputScope source
  match SourceCoreControl.lowerStatements 100 source scope (← roots source) .unit reason fellThrough with
  | .error (.unsupportedStatement _ (.whileLoop ..)) => pure ()
  | result => throw (IO.userError s!"loop boundary changed: {reprStr result}")
  let empty : TypedSource := { source with inputs := [], roots := [], nodes := [] }
  let expression ← match SourceCoreControl.lowerStatements 0 empty [] [] .word reason fellThrough with
    | .ok expression => pure expression
    | .error error => throw (IO.userError s!"non-Unit fallthrough lowering rejected: {reprStr error}")
  expect { resultType := Core.LanguageResult.resultType .word, body := expression }
    (.inLeft .word (.word fellThrough)) [] "non-Unit fallthrough should be a language failure"

def run : IO Unit := do
  let checked ← match checkProgram workspace with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError s!"control fixtures failed checking: {reprStr errors}")
  testExecution checked
  testReasonSites checked
  testBoundaries checked

end Tests.SourceCoreControl
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataCatalog
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreDataCatalog

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreDataCatalog

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def rejected {α : Type} : Except SourceCoreDataCatalog.Error α → Bool
  | .error _ => true
  | .ok _ => false

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
    "enum Box { Only }",
    "function identity(value: Word) returns (Word) { return value; }"
  ] }]
}

private def expectIdentity (catalog : Catalog) (type : TypeSystem.Ty) : IO Core.DataTypeId :=
  match catalog.identity? type with
  | some identity => pure identity
  | none => throw (IO.userError s!"missing representation {reprStr type}")

private def expectProjection (checked : Checked) (type : TypeSystem.Ty) (expected : Core.Ty) : IO Unit := do
  match checked.project type with
  | .ok projected => assertTrue (projected.type == expected) "checked catalog projection changed"
  | .error error => throw (IO.userError s!"projection rejected {reprStr error}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"catalog fixture rejected {reprStr errors}")
  let tree ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some signature => pure signature
    | none => throw (IO.userError "missing Tree signature")
  let wordTree := TypeSystem.Ty.nominal tree.id [.word]
  let boolTree := TypeSystem.Ty.nominal tree.id [.bool]
  let functionKey := TypeSystem.Ty.function .word .word
  let nested := TypeSystem.Ty.mapping (.proxy .word) (.mapping functionKey wordTree)
  let checked ← match prepare program.signatures 64
      [wordTree, wordTree, boolTree, nested, .proxy .bool, .proxy (.comptime .word), .integer] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"catalog discovery rejected {reprStr error}")
  let catalog := checked.catalog
  let wordId ← expectIdentity catalog wordTree
  let boolId ← expectIdentity catalog boolTree
  let proxyWord ← expectIdentity catalog (.proxy .word)
  let proxyBool ← expectIdentity catalog (.proxy .bool)
  let proxyStaged ← expectIdentity catalog (.proxy (.comptime .word))
  assertTrue (wordId != boolId) "nominal specialization identities collapsed"
  assertTrue (proxyWord != proxyBool && proxyWord != proxyStaged)
    "observable proxy identities collapsed"
  assertTrue ((catalog.entries.filter (fun entry => decide (entry.sourceType = wordTree))).length == 1)
    "recursive nominal discovery duplicated its identity"
  assertTrue (catalog.definitions.lookupConstructorPayloadType? ⟨wordId, 0⟩ == some .word)
    "nominal Leaf payload changed"
  assertTrue (catalog.definitions.lookupConstructorPayloadType? ⟨wordId, 1⟩ ==
      some (.product (.namedData wordId) (.namedData wordId)))
    "recursive nominal payload references changed"
  let nestedId ← expectIdentity catalog nested
  let innerId ← expectIdentity catalog (.mapping functionKey wordTree)
  assertTrue (catalog.definitions.lookupConstructorPayloadType? ⟨nestedId, 1⟩ ==
      some (.product (.product (.namedData proxyWord) (.namedData innerId)) (.namedData nestedId)))
    "mapping entry or recursive tail layout changed"
  expectProjection checked .integer .integer
  expectProjection checked (.comptime wordTree) (.namedData wordId)
  expectProjection checked functionKey (Core.TaggedFunction.functionType .word .word)
  let leaf ← match tree.constructors.find? (·.name == "Leaf") with
    | some constructor => pure constructor
    | none => throw (IO.userError "missing Leaf constructor")
  let instantiation : DataConstructorInstantiation := {
    constructor := leaf.id
    parameterSubstitution := tree.parameters.zip [.word]
    payloadTypes := [.word]
    resultType := wordTree
  }
  assertTrue ((catalog.resolveConstructor program.signatures instantiation).toOption == some ⟨wordId, 0⟩)
    "authentic constructor rejected"
  for forged in [
      { instantiation with payloadTypes := [.bool] },
      { instantiation with resultType := boolTree },
      { instantiation with parameterSubstitution := [] }] do
    assertTrue (rejected (catalog.resolveConstructor program.signatures forged))
      "forged constructor metadata accepted"
  assertTrue (rejected (prepare program.signatures 2 [wordTree])) "catalog depth budget ignored"
  assertTrue (rejected (prepare program.signatures 64 [.«variable» ⟨0⟩])) "open source type accepted"
  assertTrue (rejected (prepare program.signatures 64 [TypeSystem.Ty.nominal tree.id []]))
    "nominal arity mismatch accepted"
  assertTrue (rejected (prepare { program.signatures with dataTypes := tree :: program.signatures.dataTypes }
    64 [wordTree])) "ambiguous nominal catalog accepted"
  assertTrue (catalog.emptyMapping? (.proxy .word) (.mapping functionKey wordTree) ==
    some (.constructed ⟨nestedId, 0⟩ .unit)) "empty mapping carrier changed"
  IO.println "source Core data catalog GREEN"

end Tests.SourceCoreDataCatalog
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataValues
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value
#check_failure Solcore.Frontend.RuntimeValue

set_option autoImplicit false

namespace Tests.SourceCoreDataValues

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceInference (DataConstructorInstantiation)
open SourceCoreDataValues

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
    "enum Packet<T> { Empty, Only(T), Many(T, Bool, Word) }",
    "function identity(value: Word) returns (Word) { return value; }"
  ] }] }

private def dataSignature (program : CheckedProgram) (name : String) : IO ProgramDataSignature :=
  match program.signatures.dataTypes.filter (·.name == name) with
  | [signature] => pure signature
  | _ => throw (IO.userError s!"data values signature missing: {name}")

private def instantiation (signature : ProgramDataSignature) (arguments : List TypeSystem.Ty) (name : String) :
    IO DataConstructorInstantiation := do
  let constructor ← match signature.constructors.filter (·.name == name) with
    | [constructor] => pure constructor
    | _ => throw (IO.userError s!"data values constructor missing: {name}")
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  pure {
    constructor := constructor.id
    parameterSubstitution := substitution
    payloadTypes := constructor.payloadTypes.map substitution.apply
    resultType := TypeSystem.Ty.nominal signature.id arguments
  }

private def encoded (context : Context) (type : TypeSystem.Ty) (value : Value) (fuel : Nat := 400) : IO Core.Value :=
  match encode fuel context type value with
  | .ok core => pure core
  | .error error => throw (IO.userError s!"source value encoding failed: {reprStr error}")
private def decoded (context : Context) (type : TypeSystem.Ty) (core : Core.Value) (fuel : Nat := 400) : IO Value :=
  match decode fuel context type core with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"source value decoding failed: {reprStr error}")
private def rejectedEncode (context : Context) (type : TypeSystem.Ty) (value : Value) (fuel : Nat := 400) : IO Error :=
  match encode fuel context type value with
  | .error error => pure error
  | .ok core => throw (IO.userError s!"forged source value accepted: {reprStr core}")
private def rejectedDecode (context : Context) (type : TypeSystem.Ty) (value : Core.Value) (fuel : Nat := 400) : IO Error :=
  match decode fuel context type value with
  | .error error => pure error
  | .ok source => throw (IO.userError s!"forged raw Core value accepted: {reprStr source}")
private def roundtrip (context : Context) (type : TypeSystem.Ty) (value : Value) : IO Core.Value := do
  let core ← encoded context type value
  assertTrue ((← decoded context type core) == value) "source roundtrip changed deep value or metadata"
  assertTrue ((← encoded context type (← decoded context type core)) == core) "Core roundtrip changed complete data tree"
  pure core

private def orderedCore (identity : Core.DataTypeId) : List (Core.Value × Core.Value) → Core.Value
  | [] => .constructed ⟨identity, 0⟩ .unit
  | (key, value) :: rest => .constructed ⟨identity, 1⟩ (.pair (.pair key value) (orderedCore identity rest))

private def recursiveTree (leaf pair : DataConstructorInstantiation) : Nat → Value
  | 0 => .constructed leaf [.integer 7]
  | depth + 1 => .constructed pair [recursiveTree leaf pair depth, .constructed leaf [.integer (-(Int.ofNat depth))]]

example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {value : Value} {core : Core.Value}
    (accepted : encode fuel context type value = .ok core) :
    decode fuel context type core = .ok value := decode_encode accepted
example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {value : Value} {core : Core.Value}
    (accepted : decode fuel context type core = .ok value) :
    encode fuel context type value = .ok core := encode_decode accepted
example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {value : Value} {core : Core.Value}
    (accepted : encode fuel context type value = .ok core) :
    ∃ projected, context.checked.catalog.project type = .ok projected ∧
      ∀ world, Core.RuntimeValueHasType world core projected context.checked.catalog.definitions := encode_typed accepted
example {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {metadata : DataConstructorInstantiation} {tag : Core.ConstructorId}
    (accepted : catalog.resolveConstructor signatures metadata = .ok tag) :
    catalog.constructor? metadata = some tag ∧
      ∃ payload, catalog.definitions.lookupConstructorPayloadType? tag = some payload := resolveConstructor_facts accepted

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"data values fixture failed: {reprStr errors}")
  let tree ← dataSignature program "Tree"
  let packet ← dataSignature program "Packet"
  let treeType := TypeSystem.Ty.nominal tree.id [.integer]
  let wordTree := TypeSystem.Ty.nominal tree.id [.word]
  let stagedTree := TypeSystem.Ty.nominal tree.id [.comptime .word]
  let packetType := TypeSystem.Ty.nominal packet.id [.integer]
  let mapType := TypeSystem.Ty.mapping .integer treeType
  let nestedMap := TypeSystem.Ty.mapping (.proxy (.comptime .word)) mapType
  let functionType := TypeSystem.Ty.function .word .word
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 160
      [treeType, wordTree, stagedTree, packetType, mapType, nestedMap,
        .proxy .word, .proxy (.comptime .word), .proxy functionType, .mapping functionType treeType] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"data values catalog failed: {reprStr error}")
  let context : Context := { checked, signatures := program.signatures }
  let leaf ← instantiation tree [.integer] "Leaf"
  let pair ← instantiation tree [.integer] "Pair"
  let wordLeaf ← instantiation tree [.word] "Leaf"
  let stagedLeaf ← instantiation tree [.comptime .word] "Leaf"
  let empty ← instantiation packet [.integer] "Empty"
  let only ← instantiation packet [.integer] "Only"
  let many ← instantiation packet [.integer] "Many"
  let leafTag ← match checked.catalog.resolveConstructor program.signatures leaf with
    | .ok tag => pure tag | .error error => throw (IO.userError s!"Leaf tag missing: {reprStr error}")
  let pairTag ← match checked.catalog.resolveConstructor program.signatures pair with
    | .ok tag => pure tag | .error error => throw (IO.userError s!"Pair tag missing: {reprStr error}")
  let mapIdentity := (checked.catalog.identity? mapType).getD ⟨999⟩
  let treeValue := Value.constructed pair [
    .constructed leaf [.integer (2 ^ 400)], .constructed leaf [.integer (-8)]]
  let treeCore := Core.Value.constructed pairTag (.pair
    (.constructed leafTag (.integer (2 ^ 400))) (.constructed leafTag (.integer (-8))))
  assertTrue ((← roundtrip context treeType treeValue) == treeCore) "nominal payload order or native Integer changed"
  discard <| roundtrip context packetType (.constructed empty [])
  discard <| roundtrip context packetType (.constructed only [.integer (-55)])
  let manyValue := Value.constructed many [.integer (-10), .bool true, .word Core.Word.zero]
  let manyCore ← roundtrip context packetType manyValue
  match manyCore with
  | .constructed _ (.pair (.integer (-10)) (.pair (.bool true) (.word value))) =>
      assertTrue (value == Core.Word.zero) "many payload Word changed"
  | _ => throw (IO.userError "zero/single/many nominal payload convention changed")
  discard <| roundtrip context wordTree (.constructed wordLeaf [.word Core.Word.zero])
  discard <| roundtrip context stagedTree (.constructed stagedLeaf [.word Core.Word.zero])
  assertTrue (checked.catalog.identity? wordTree != checked.catalog.identity? stagedTree)
    "nominal raw argument staging identity collapsed"

  let mapEntries : List (Value × Value) := [
    (.integer 9, treeValue), (.integer 9, .constructed leaf [.integer 2]),
    (.integer (-1), .constructed leaf [.integer 3])]
  let mapping := Value.mapping .integer treeType mapEntries
  let mappingCore ← roundtrip context mapType mapping
  assertTrue (mappingCore == orderedCore mapIdentity [
    (.integer 9, treeCore), (.integer 9, .constructed leafTag (.integer 2)),
    (.integer (-1), .constructed leafTag (.integer 3))]) "mapping keys were sorted, deduplicated, or reordered"
  let reversed ← encoded context mapType (.mapping .integer treeType mapEntries.reverse)
  assertTrue (mappingCore != reversed) "ordered mapping encoding lost list order"
  discard <| roundtrip context mapType (.mapping .integer treeType [])
  let proxy := Value.proxy (.comptime .word)
  discard <| roundtrip context nestedMap (.mapping (.proxy (.comptime .word)) mapType [(proxy, mapping)])
  let plainProxy ← roundtrip context (.proxy .word) (.proxy .word)
  let stagedProxy ← roundtrip context (.proxy (.comptime .word)) proxy
  assertTrue (plainProxy != stagedProxy) "proxy raw inner staging identity was erased"
  discard <| roundtrip context (.proxy functionType) (.proxy functionType)
  discard <| roundtrip context (.mapping functionType treeType) (.mapping functionType treeType [])

  let scalars := Value.product .unit (.product (.bool true) (.product (.word Core.Word.zero) (.integer (-(2 ^ 512)))))
  let scalarType : TypeSystem.Ty := .product .unit (.product .bool (.product .word .integer))
  discard <| roundtrip context scalarType scalars
  let stagedScalarType : TypeSystem.Ty := .comptime (.product (.comptime .unit)
    (.product .bool (.product (.comptime .word) (.comptime .integer))))
  assertTrue ((← roundtrip context stagedScalarType scalars) == (← encoded context scalarType scalars))
    "runtime staging wrapper projection changed scalar data"
  assertTrue ((← roundtrip context (.comptime treeType) treeValue) == treeCore)
    "outer nominal staging wrapper changed representation"
  let stagedMapType := TypeSystem.Ty.mapping (.comptime .integer) treeType
  assertTrue ((← roundtrip context stagedMapType (.mapping (.comptime .integer) treeType mapEntries)) == mappingCore)
    "mapping payload runtime projection changed"

  for forged in [
      { leaf with parameterSubstitution := [] },
      { leaf with parameterSubstitution := leaf.parameterSubstitution ++ leaf.parameterSubstitution },
      { leaf with parameterSubstitution := leaf.parameterSubstitution.map fun (id, _) => (id, TypeSystem.Ty.bool) },
      { leaf with payloadTypes := [.bool] },
      { leaf with payloadTypes := [] },
      { leaf with resultType := wordTree },
      { leaf with constructor := { leaf.constructor with constructorIndex := 99 } },
      { leaf with constructor := { leaf.constructor with dataType := packet.id } }] do
    discard <| rejectedEncode context treeType (.constructed forged [.integer 7])
  let arity ← rejectedEncode context treeType (.constructed leaf [.integer 1, .integer 2])
  assertTrue (decide (arity.code = .payloadCountMismatch 1 2)) "nominal payload arity error was hidden"
  let deep ← rejectedEncode context treeType (.constructed pair [
    .constructed leaf [.integer 1], .constructed leaf [.bool false]])
  assertTrue (decide (deep.path = [.constructorPayload 1, .constructorPayload 0]))
    "deep source payload path was lost"
  discard <| rejectedEncode context mapType (.mapping .word treeType [])
  discard <| rejectedEncode context mapType (.mapping .integer wordTree [])
  discard <| rejectedEncode context mapType (.mapping .integer treeType [(.bool false, treeValue)])
  discard <| rejectedEncode context (.proxy (.comptime .word)) (.proxy .word)
  discard <| rejectedDecode context (.proxy (.comptime .word)) plainProxy
  discard <| rejectedDecode context (.proxy .word) stagedProxy

  let foreignSignatures : Context := { context with
    signatures := { program.signatures with dataTypes := tree :: program.signatures.dataTypes } }
  discard <| rejectedEncode foreignSignatures treeType treeValue
  discard <| rejectedDecode foreignSignatures treeType treeCore
  let tamperedTree := { tree with constructors := tree.constructors.map fun constructor =>
    if constructor.id = leaf.constructor then { constructor with payloadTypes := [.bool] } else constructor }
  let altered : Context := { context with
    signatures := { program.signatures with dataTypes := tamperedTree :: program.signatures.dataTypes.filter (·.id != tree.id) } }
  discard <| rejectedEncode altered treeType (.constructed leaf [.integer 1])
  discard <| rejectedDecode altered treeType (.constructed leafTag (.integer 1))

  let capabilities : List Core.Value := [
    .closure .word .word (.var 0) [], .cellRef .integer 0,
    .cellRef .integer 999, .hostFunction .storageRead]
  for forbidden in capabilities do
    discard <| rejectedDecode context treeType (.constructed leafTag forbidden)
    discard <| rejectedDecode context (.product .unit treeType) (.pair .unit (.constructed leafTag forbidden))
  discard <| rejectedDecode context treeType (.constructed ⟨leafTag.owner, 999⟩ .unit)
  discard <| rejectedDecode context treeType (.constructed pairTag (.pair (.constructed leafTag (.integer 0)) plainProxy))
  discard <| rejectedDecode context treeType (.inRight .unit treeCore)
  discard <| rejectedDecode context mapType (.constructed ⟨mapIdentity, 1⟩
    (.pair (.pair (.integer 0) treeCore) treeCore))
  discard <| rejectedDecode context mapType (.constructed ⟨mapIdentity, 0⟩ (.integer 0))
  discard <| rejectedDecode context (.proxy .word) (.constructed ⟨(checked.catalog.identity? (.proxy .word)).getD ⟨999⟩, 0⟩
    (.hostFunction .storageRead))
  let functionError ← rejectedEncode context functionType .unit
  assertTrue (decide (functionError.code = .functionHandleRequired)) "source function handle rejection was not explicit"
  let rawFunction := Core.Value.pair (.inRight .unit (.word Core.Word.zero))
    (.closure .word (Core.LanguageResult.resultType .word) (Core.LanguageResult.success (.var 0)) [])
  let functionError ← rejectedDecode context functionType rawFunction
  assertTrue (decide (functionError.code = .functionHandleRequired)) "raw closure passed as a public function handle"
  let referenceError ← rejectedDecode context treeType (.constructed leafTag (.cellRef .integer 999))
  assertTrue (decide (referenceError.code = .externalReferenceUnsupported)) "forged reference category was lost"
  assertTrue (decide (referenceError.path = [.rawCore .constructorPayload])) "deep raw reference path was lost"

  let recursive := recursiveTree leaf pair 25
  discard <| roundtrip context treeType recursive
  discard <| rejectedEncode context treeType recursive 8
  let recursiveCore ← encoded context treeType recursive
  discard <| rejectedDecode context treeType recursiveCore 8
  discard <| rejectedEncode context .integer (.integer 0) 0
  discard <| rejectedDecode context .integer (.integer 0) 0
  IO.println "source Core data values GREEN"

end Tests.SourceCoreDataValues
end

section
-- leanmerge: from Solcore.Test.SourceCoreFunctionEntry
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreFunctionEntry

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreFunctionEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function consume(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
    "function named(value: Word) returns (Word) { let f: function(Word) returns (Word) = inc; return consume(f, value); }",
    "function makeAdder(value: Word) returns (function(Word) returns (Word)) {",
    " return lam(delta: Word) -> Word { value = value + delta; return value; }; }",
    "function useReturned(value: Word) returns (Word, Word) {",
    " let f: function(Word) returns (Word) = makeAdder(value); return (f(2), f(3)); }",
    "function shared(value: Word) returns (Word, Word) {",
    " let f: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; };",
    " let g: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; }; return (f(2), g(3)); }",
    "function selfCell(value: Word) returns (Word) {",
    " let loop: function(Word) returns (Word);",
    " loop = lam(n: Word) -> Word { return n == 0 ? value : loop(n - 1); }; return loop(3); }",
    "function nestedCapture(value: Word) returns (Word) {",
    " let outer: function(Word) returns (function() returns (Word)) = lam(delta: Word) -> function() returns (Word) {",
    "   return lam() -> Word { return inc(value + delta); }; };",
    " let inner: function() returns (Word) = outer(3); value = 9; return inner(); }",
    "function bounce(count: Word, f: function(Word) returns (Word)) returns (Word) {",
    " return count == 0 ? f(count) : bounce(count - 1, f); }",
    "function useBounce(value: Word) returns (Word) {",
    " let f: function(Word) returns (Word) = lam(n: Word) -> Word { return value + n; }; return bounce(3, f); }",
    "function closureLoop(value: Word) returns (Word) {",
    " let f: function(Word) returns (Word) = lam(n: Word) -> Word {",
    "   while (n > 0) { value = inc(value); n = n - 1; } return value; }; return f(3); }",
    "function failBeforeArgument() returns (Word) {",
    " let f: function(Word) returns (Word); let marker: Word = 0;",
    " let argument: function() returns (Word) = lam() -> Word { marker = 9; return marker; }; return f(argument()); }",
    "function makeFailure() returns (function() returns (Word)) {",
    " let absent: Word; return lam() -> Word { return absent; }; }",
    "function useFailure() returns (Word) { let f: function() returns (Word) = makeFailure(); return f(); }",
    "function pairInput(pair: (Word, Bool)) returns (Word, Bool) { return pair; }",
    "function rejectProduct(pair: (Word, function(Word) returns (Word))) returns (Word) { return 0; }",
    "function staged(comptime value: Word) returns (Word) { return value; }"
  ] }]
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"function-entry fixture missing: {name}")

private def plan (program : CheckedProgram) (names : List String) : IO Plan := do
  let requests ← names.mapM (request program)
  match SourceSpecializationWorklist.run program requests 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"function-entry worklist failed: {reprStr result}")

private def prepared (program : CheckedProgram) (names : List String) : IO PreparedProgram := do
  let input ← plan program names
  match prepare program input 100 Core.Word.zero with
  | .ok program => pure program
  | .error error => throw (IO.userError s!"function-entry preparation failed: {reprStr error}")

private def firstEntry (prepared : PreparedProgram) : IO Entry :=
  match prepared.entries with
  | entry :: _ => pure entry
  | [] => throw (IO.userError "function-entry seed missing")

private def execute (entry : Entry) (arguments : List Core.Value) (fuel : Nat := 30000) :
    IO (SourceCoreBasicEntry.Result entry.resultType) := do
  match entry.run arguments fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"function-entry invocation rejected: {reprStr error}")

private def success (entry : Entry) (arguments : List Core.Value) (expected : Core.Value) : IO Core.Store := do
  match (← execute entry arguments).observation with
  | .succeeded value store =>
      assertTrue (value == expected) "function-entry result mismatch"
      pure store
  | result => throw (IO.userError s!"function-entry did not succeed: {reprStr result}")

/-- Closures capture by value: every call starts from the closure's
creation-time copies, and assignments in a body write only that call's copies. -/
private def testCapturesAndCalls (program : CheckedProgram) : IO Unit := do
  let named ← firstEntry (← prepared program ["named"])
  discard <| success named [scalar 4] (scalar 5)
  discard <| success named [scalar 9] (scalar 10)
  let returnedProgram ← prepared program ["useReturned"]
  let returnedEntry ← firstEntry returnedProgram
  let store ← success returnedEntry [scalar 4] (.pair (scalar 6) (scalar 7))
  let firstSourceCell := returnedEntry.inputs.length + returnedProgram.plan.specializations.length
  assertTrue (store[firstSourceCell]? == some (present (scalar 4))) "returned closure mutated its caller's value copy"
  assertTrue (store[firstSourceCell + 1]? == some (present (scalar 4)))
    "returned closure call wrote its captured parameter instead of a per-call copy"
  let sharedProgram ← prepared program ["shared"]
  let sharedEntry ← firstEntry sharedProgram
  let store ← success sharedEntry [scalar 4] (.pair (scalar 6) (scalar 7))
  assertTrue (store[sharedEntry.inputs.length + sharedProgram.plan.specializations.length]? == some (present (scalar 4)))
    "a closure call wrote the enclosing parameter instead of its own copy"
  let nested ← firstEntry (← prepared program ["nestedCapture"])
  discard <| success nested [scalar 4] (scalar 8)
  let loop ← firstEntry (← prepared program ["closureLoop"])
  discard <| success loop [scalar 8] (scalar 11)

/-- `loop` is assigned after the closure is created, so the closure's copy of
`loop` is uninitialized and its first recursive read fails. -/
private def testRecursionAndResume (program : CheckedProgram) : IO Unit := do
  let compiled ← prepared program ["selfCell", "useBounce", "selfCell"]
  assertTrue (compiled.entries.length == 3) "function-entry duplicate seed order changed"
  let selfCell := (← request program "selfCell").declaration
  let function ← match program.functions.find? (·.declaration == selfCell) with
    | some function => pure function
    | none => throw (IO.userError "self-cell source missing")
  let (read, binder) ← match function.typedBody.nodes.findSome? fun
      | .expression node@{ form := .reference "loop" (.local binder), .. } => some (node, binder)
      | _ => none with
    | some read => pure read
    | none => throw (IO.userError "self-cell read in the closure body missing")
  for entry in compiled.entries do
    if entry.key.declaration == selfCell then
      match (← execute entry [scalar 7]).observation with
      | .failed reason _ =>
          assertTrue (decide (entry.failureDiagnostic? reason = some {
            error := .uninitializedLocal binder, site := .occurrence read.id.occurrence, span := some read.span }))
            "self-cell closure failure lost its uninitialized copy's binder, occurrence or span"
      | result => throw (IO.userError s!"self-cell closure read of its uninitialized copy did not fail: {reprStr result}")
    else
      discard <| success entry [scalar 7] (scalar 7)
  let entry ← firstEntry compiled
  let suspended ← execute entry [scalar 7] 15
  let checkpoint ← match suspended.checkpoint? with
    | some checkpoint => pure checkpoint
    | none => throw (IO.userError "self-cell closure call did not produce a typed checkpoint")
  let resumed := checkpoint.resume 30000
  let uninterrupted ← execute entry [scalar 7] 30015
  assertTrue (resumed.observation == uninterrupted.observation)
    "function-entry checkpoint resumption changed the exact result/store"

private def testFailures (program : CheckedProgram) : IO Unit := do
  let compiled ← prepared program ["failBeforeArgument"]
  let entry ← firstEntry compiled
  match (← execute entry []).observation with
  | .failed reason store =>
      let marker := entry.inputs.length + compiled.plan.specializations.length + 1
      /- The argument closure would write only its own copy of `marker`, so
      this cell no longer shows whether the argument was evaluated. -/
      assertTrue (store[marker]? == some (present (scalar 0))) "failed callee changed the enclosing marker"
      assertTrue (decide (entry.failureDiagnostic? reason ≠ none)) "failed function cell lost its diagnostic"
  | result => throw (IO.userError s!"uninitialized function cell did not fail: {reprStr result}")
  let compiled ← prepared program ["useFailure"]
  let entry ← firstEntry compiled
  let owner := (← request program "makeFailure").declaration
  let site ← match entry.faultSites.reads.find? (fun site => decide (site.binder.owner = owner)) with
    | some site => pure site
    | none => throw (IO.userError "returned lambda's captured read site missing")
  match (← execute entry []).observation with
  | .failed reason _ =>
      assertTrue (reason == site.reason) "returned lambda failure used the caller's source token"
      assertTrue (decide (entry.failureDiagnostic? reason = some {
        error := .uninitializedLocal site.binder
        site := .occurrence site.expression.occurrence
        span := some site.span
      })) "returned lambda failure lost its exact original binder/occurrence/span"
  | result => throw (IO.userError s!"returned failing closure did not fail: {reprStr result}")

private def testPublicBoundary (program : CheckedProgram) : IO Unit := do
  for name in ["consume", "rejectProduct"] do
    let input ← plan program [name]
    match prepare program input 100 Core.Word.zero with
    | .error (.entry (.lowering (.typeProjection { reason := .unsupportedType (.function _ _), .. }))) => pure ()
    | result => throw (IO.userError s!"function-valued public input did not receive the explicit projection rejection: {reprStr result}")
  for name in ["makeAdder", "makeFailure"] do
    let input ← plan program [name]
    match prepare program input 100 Core.Word.zero with
    | .error (.lowering (.typeProjection { reason := .unsupportedType (.function _ _), .. })) => pure ()
    | result => throw (IO.userError s!"function-valued public result did not receive the explicit projection rejection: {reprStr result}")
  let pair ← firstEntry (← prepared program ["pairInput"])
  discard <| success pair [.pair (scalar 8) (.bool true)] (.pair (scalar 8) (.bool true))
  match pair.run [.pair (scalar 8) (scalar 1)] 100 with
  | .error (.inputTypeMismatch _ _ _) => pure ()
  | _ => throw (IO.userError "public product input was not deeply validated")
  match pair.run [.pair (scalar 8) (.bool true)] 100 [scalar 2] with
  | .error (.initialStoreUnsupported 1) => pure ()
  | _ => throw (IO.userError "function-entry silently consumed an unsupported initial store")
  let staged ← firstEntry (← prepared program ["staged"])
  assertTrue (staged.inputs.map (·.comptime) == [true])
    "comptime scalar seed input marker was discarded"
  discard <| success staged [scalar 6] (scalar 6)
  let input ← plan program ["named"]
  match prepare program { input with referenceEdges := [] } 100 Core.Word.zero with
  | .error (.preparation _) => pure ()
  | _ => throw (IO.userError "forged named-reference plan escaped canonical preparation")
  match prepare program input 0 Core.Word.zero with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "function-entry ignored compile traversal exhaustion")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"function-entry source fixtures failed: {reprStr errors}")
  testCapturesAndCalls program
  testRecursionAndResume program
  testFailures program
  testPublicBoundary program

end Tests.SourceCoreFunctionEntry
end

section
-- leanmerge: from Solcore.Test.SourceCoreFunctions
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreFunctions

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function dec(value: Word) returns (Word) { return value - 1; }",
    "function consume(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
    "function named(value: Word) returns (Word) { let f: function(Word) returns (Word) = inc; return consume(f, value); }",
    "function shared(value: Word) returns (Word, Word) {",
    " let f: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; };",
    " let g: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; };",
    " return (f(2), g(3)); }",
    "function selfCell(value: Word) returns (Word) {",
    " let loop: function(Word) returns (Word);",
    " loop = lam(n: Word) -> Word { return n == 0 ? value : loop(n - 1); }; return loop(3); }",
    "function nestedCapture(value: Word) returns (Word) {",
    " let outer: function(Word) returns (function() returns (Word)) = lam(delta: Word) -> function() returns (Word) {",
    "   return lam() -> Word { return inc(value + delta); }; };",
    " let inner: function() returns (Word) = outer(3); value = 9; return inner(); }",
    "function failBeforeArgument() returns (Word) {",
    " let f: function(Word) returns (Word); let marker: Word = 0;",
    " let argument: function() returns (Word) = lam() -> Word { marker = 9; return marker; }; return f(argument()); }",
    "function argumentFailure() returns (Word) {",
    " let f: function(Word) returns (Word) = lam(value: Word) -> Word { return value; };",
    " let absent: Word; return f(absent); }",
    "function names() returns (function(Word) returns (Word), function(Word) returns (Word)) { return (inc, dec); }",
    "function sameName() returns (function(Word) returns (Word), function(Word) returns (Word)) { return (inc, inc); }",
    "function lambdaGlobal(value: Word) returns (Word) {",
    " let f: function(Word) returns (Word) = lam(n: Word) -> Word { return inc(n) + value; }; return f(2); }",
    "function closureLoop(value: Word) returns (Word) {",
    " let f: function(Word) returns (Word) = lam(n: Word) -> Word {",
    "   while (n > 0) { value = inc(value); n = n - 1; } return value; }; return f(3); }",
    "function principal() returns (Word) { let id = lam(value) { return value; }; return id(4); }"
  ] }]
}

private def bodyLowerer : SourceCoreFunctions.BodyLowerer :=
  fun expression fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy {
      lowerExpression := expression
      readStatement := SourceCoreFunctionTypes.readStatement
      lowerBinder := SourceCoreFunctionTypes.lowerBinder
      lowerAssignment := SourceCoreFunctionTypes.lowerAssignment
    } fuel source scope statements result reasonAt fellThrough escaped

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"function-value fixture missing: {name}")

private def preparePlan (program : CheckedProgram) (name : String) : IO SourceCoreCalls.Plan := do
  let plan ← match SourceSpecializationWorklist.run program [← request program name] 100 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"function-value worklist failed: {reprStr result}")
  match SourceCompilationPlan.prepareExecutablePlanEvidence program plan with
  | .ok plan => pure plan
  | .error error => throw (IO.userError s!"function-value plan preparation failed: {reprStr error}")

private def signature (function : SourceSpecialization.SpecializedFunction) : IO SourceCoreCalls.Signature := do
  match function.function.type with
  | .function parameter result =>
      match SourceCoreFunctionTypes.lowerType (.declaration function.key.declaration) parameter,
          SourceCoreFunctionTypes.lowerType (.declaration function.key.declaration) result with
      | .ok parameterType, .ok resultType => pure { key := function.key, parameterType, resultType }
      | _, _ => throw (IO.userError "function-value signature projection failed")
  | _ => throw (IO.userError "function-value fixture is not a function")

private def parameters (source : TypedSource) : IO (List (TypedBinder × Core.Ty) × SourceCoreBasic.Scope) := do
  source.inputs.foldlM (fun (parameters, scope) binder => do
    match SourceCoreFunctionTypes.lowerBinder source scope binder with
    | .ok type => pure (parameters ++ [(binder, type)], (binder.id, type) :: scope)
    | .error error => throw (IO.userError s!"function-value input rejected: {reprStr error}")) ([], [])

private structure Compiled where
  plan : SourceCoreCalls.Plan
  entry : SourceSpecialization.SpecializedFunction
  globals : List SourceCoreCalls.Signature
  diagnostics : SourceCoreProgramFaultSites.Program
  type : Core.Ty
  body : Core.Expr

/-- A closed test harness installs exactly the compiled raw globals and invokes
one root. Production entry/interface generalization is owned by its own module. -/
private def compile (program : CheckedProgram) (name : String) (arguments : List SourceCoreBasic.LoweredExpr) : IO Compiled := do
  let plan ← preparePlan program name
  let root ← match plan.seedKeys with
    | [root] => pure root
    | _ => throw (IO.userError "function-value fixture must have one seed")
  let ordered := plan.specializations.reverse
  let globals ← ordered.mapM signature
  let diagnostics ← match SourceCoreProgramFaultSites.prepare plan root with
    | .ok diagnostics => pure diagnostics
    | .error error => throw (IO.userError s!"function-value diagnostic preparation failed: {reprStr error}")
  let closures ← ordered.mapM fun function => do
    let signature ← signature function
    let sites ← match diagnostics.find? function.key with
      | some sites => pure sites
      | none => throw (IO.userError "function-value sites missing")
    let source := function.function.typedBody
    let (parameters, scope) ← parameters source
    let context : SourceCoreFunctions.Context := {
      plan, globals, owner := function.key, administrativePrefix := 1
      solvedRequirements := function.function.solvedRequirements
      internalReason := Core.Word.zero
    }
    let statements ← source.roots.mapM fun
      | .statement id => pure id
      | .expression _ => throw (IO.userError "function-value fixture has expression root")
    let body ← match bodyLowerer
        (fun fuel source scope id reasonAt =>
          SourceCoreFunctions.lowerExpressionWithReasons bodyLowerer fuel context source scope id reasonAt)
        100 source scope statements signature.resultType sites.table.reasonAt sites.fellThroughReason sites.table.escapedReason with
      | .ok body => pure body
      | .error error => throw (IO.userError s!"function-value body rejected: {reprStr error}")
    let body := SourceCoreFunctions.bindParameters parameters signature.resultType body
    pure (Core.Expr.lambda signature.parameterType (Core.LanguageResult.resultType signature.resultType) body)
  let (entry, index) ← match ordered.zipIdx.find? (fun item => decide (item.1.key = root)) with
    | some entry => pure entry
    | none => throw (IO.userError "function-value root missing")
  let signature ← signature entry
  let arguments := SourceCoreCalls.packArguments arguments
  assertTrue (decide (arguments.type = signature.parameterType)) "test argument bundle type mismatch"
  let body := SourceCoreRecursiveEntry.allocateGlobals globals.reverse
    (SourceCoreRecursiveEntry.installFunctions closures (SourceCoreCalls.call signature index arguments.expression Core.Word.zero))
  assertTrue (decide (Core.infer? [] body = some (Core.LanguageResult.resultType signature.resultType)))
    "function-value closed harness failed Core checker"
  pure { plan, entry, globals, diagnostics, type := signature.resultType, body }

private def argument (value : Nat) : SourceCoreBasic.LoweredExpr :=
  ⟨.word, Core.LanguageResult.success (.word (word value))⟩

private def execute (compiled : Compiled) (fuel : Nat := 20000) : Core.LanguageResult.Observation :=
  Core.LanguageResult.observeResult (Core.runStateful fuel (.initial compiled.body [] []))

private def success (compiled : Compiled) (expected : Core.Value) : IO Core.Store := do
  match execute compiled with
  | .succeeded actual store =>
      assertTrue (actual == expected) "function-value result mismatch"
      pure store
  | result => throw (IO.userError s!"function-value execution failed: {reprStr result}")

/-- Closures capture by value: every call starts from the closure's
creation-time copies, and assignments in a body write only that call's copies. -/
private def testFunctionValues (program : CheckedProgram) : IO Unit := do
  discard <| success (← compile program "named" [argument 4]) (scalar 5)
  let shared ← compile program "shared" [argument 4]
  let store ← success shared (.pair (scalar 6) (scalar 7))
  assertTrue (store[shared.globals.length]? == some (present (scalar 4)))
    "a closure call wrote the enclosing parameter instead of its own copy"
  /- `loop` is assigned after the closure is created, so the closure's copy of
  `loop` is uninitialized and the first recursive read in its body fails. -/
  let selfCell ← compile program "selfCell" [argument 7]
  let innerRead ← match selfCell.entry.function.typedBody.nodes.findSome? fun
      | .expression node@{ form := .reference "loop" (.local _), .. } => some node
      | _ => none with
    | some node => pure node
    | none => throw (IO.userError "self-cell read in the closure body missing")
  let sites ← match selfCell.diagnostics.find? selfCell.entry.key with
    | some sites => pure sites
    | none => throw (IO.userError "self-cell diagnostic table missing")
  match execute selfCell with
  | .failed reason store =>
      assertTrue (reason == sites.table.reasonAt innerRead.id)
        "self-cell closure failure lost its uninitialized copy's read site"
      assertTrue (store.length == selfCell.globals.length + 7)
        "self-cell call changed its snapshot, copy or parameter allocations"
  | result => throw (IO.userError s!"self-cell closure read of its uninitialized copy did not fail: {reprStr result}")
  match execute selfCell 15 with
  | .outOfFuel checkpoint =>
      assertTrue (Core.LanguageResult.observeResult (Core.runStateful 20000 checkpoint) == execute selfCell 20015)
        "capturing self-cell checkpoint did not resume consistently"
  | _ => throw (IO.userError "capturing self-cell execution did not suspend")
  discard <| success (← compile program "nestedCapture" [argument 4]) (scalar 8)
  discard <| success (← compile program "lambdaGlobal" [argument 8]) (scalar 11)
  discard <| success (← compile program "closureLoop" [argument 8]) (scalar 11)
  for (name, same) in [("sameName", true), ("names", false)] do
    let compiled ← compile program name []
    match execute compiled with
    | .succeeded (.pair (.pair (.inRight .unit (.word left)) _) (.pair (.inRight .unit (.word right)) _)) _ =>
        assertTrue ((left == right) == same) "named identities were not deterministic and distinct"
        assertTrue (left != Core.Word.zero && right != Core.Word.zero) "named identity used the reserved zero value"
    | result => throw (IO.userError s!"named reference did not return tagged functions: {reprStr result}")

private def testIndirectFailure (program : CheckedProgram) : IO Unit := do
  let compiled ← compile program "failBeforeArgument" []
  match execute compiled with
  | .failed reason store =>
      let node ← match compiled.entry.function.typedBody.nodes.findSome? fun
        | .expression node@{ form := .reference "f" (.local _), .. } => some node
        | _ => none with
      | some node => pure node
      | none => throw (IO.userError "uninitialized function read missing")
      let sites ← match compiled.diagnostics.find? compiled.entry.key with
        | some sites => pure sites
        | none => throw (IO.userError "root diagnostic table missing")
      assertTrue (reason == sites.table.reasonAt node.id) "indirect callee failure lost its source site"
      /- The argument closure would write only its own copy of `marker`, so
      this cell no longer shows whether the argument was evaluated. -/
      assertTrue (store[compiled.globals.length + 1]? == some (present (scalar 0)))
        "failed indirect callee changed the enclosing marker"
  | result => throw (IO.userError s!"uninitialized function did not fail: {reprStr result}")
  let compiled ← compile program "argumentFailure" []
  match execute compiled with
  | .failed _ store =>
      assertTrue (store.length == compiled.globals.length + 2)
        "failed indirect argument allocated the callee parameter"
  | result => throw (IO.userError s!"uninitialized indirect argument did not fail: {reprStr result}")

private def testTypesAndBoundaries (program : CheckedProgram) : IO Unit := do
  let namedRequest ← request program "named"
  let site := SourceCoreElaboration.ErrorSite.declaration namedRequest.declaration
  let higherOrder : TypeSystem.Ty := .function (.product (.function .word .bool) .word) (.function .unit .word)
  match SourceCoreFunctionTypes.lowerType site higherOrder with
  | .ok actual =>
      assertTrue (decide (actual = Core.TaggedFunction.functionType
        (.product (Core.TaggedFunction.functionType .word .bool) .word)
        (Core.TaggedFunction.functionType .unit .word))) "recursive function type projection changed shape"
  | .error error => throw (IO.userError s!"higher-order type projection failed: {reprStr error}")
  match SourceCoreFunctionTypes.lowerType site .integer with
  | .ok type => assertTrue (type == .integer) "native Integer projection changed"
  | .error error => throw (IO.userError s!"native Integer projection failed: {reprStr error}")
  match SourceCoreFunctionTypes.lowerType site (.comptime .word) with
  | .ok type => assertTrue (type == .word) "staged scalar payload projection changed"
  | .error error => throw (IO.userError s!"staged scalar projection failed: {reprStr error}")
  for type in ([.mapping .word .word, .proxy .word] : List TypeSystem.Ty) do
    match SourceCoreFunctionTypes.lowerType site type with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "unsupported general type entered the function profile")
  let principalPlan ← preparePlan program "principal"
  let principalRequest ← request program "principal"
  let principal ← match principalPlan.specializations.find? (fun function =>
      function.key = { declaration := principalRequest.declaration, arguments := [] }) with
    | some function => pure function
    | none => throw (IO.userError "principal fixture missing")
  let binder ← match principal.function.typedBody.nodes.findSome? fun
    | .statement { form := .letDecl binder _, .. } => some binder
    | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError "principal local binder missing")
  match SourceCoreFunctionTypes.lowerBinder principal.function.typedBody [] binder with
  | .error (.polymorphicBinding _) => pure ()
  | _ => throw (IO.userError "principal polymorphic binding entered the monomorphic profile")

private def testMetadata (program : CheckedProgram) : IO Unit := do
  let names ← compile program "names" []
  let source := names.entry.function.typedBody
  let reference ← match source.nodes.findSome? fun
    | .expression node@{ form := .reference _ (.declaration _), .. } => some node
    | _ => none with
    | some node => pure node
    | none => throw (IO.userError "named reference fixture missing")
  let context : SourceCoreFunctions.Context := {
    plan := names.plan, owner := names.entry.key, globals := names.globals
    administrativePrefix := 0, solvedRequirements := names.entry.function.solvedRequirements
    internalReason := Core.Word.zero
  }
  let checkReference (context : SourceCoreFunctions.Context) : IO Unit := do
    match SourceCoreFunctions.lowerExpressionWithReasons bodyLowerer 100 context source [] reference.id
        (fun _ => word 81) with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "forged named reference metadata was accepted")
  checkReference { context with plan := { names.plan with referenceEdges := [] } }
  checkReference { context with plan := { names.plan with referenceEdges := names.plan.referenceEdges ++ names.plan.referenceEdges } }
  checkReference { context with globals := [] }
  checkReference { context with globals := names.globals.map fun signature => { signature with resultType := .bool } }
  let indirectPlan ← preparePlan program "consume"
  let caller ← match indirectPlan.specializations with
    | [caller] => pure caller
    | _ => throw (IO.userError "indirect fixture plan changed")
  let source := caller.function.typedBody
  let (_, scope) ← parameters source
  let node ← match source.nodes.findSome? fun
    | .expression node@{ form := .call _ _ (.indirect _), .. } => some node
    | _ => none with
    | some node => pure node
    | none => throw (IO.userError "indirect fixture occurrence missing")
  let context : SourceCoreFunctions.Context := {
    plan := indirectPlan, owner := caller.key, globals := [← signature caller]
    administrativePrefix := 1, solvedRequirements := caller.function.solvedRequirements
    internalReason := Core.Word.zero
  }
  let lower (source : TypedSource) := SourceCoreFunctions.lowerExpressionWithReasons bodyLowerer 100 context
    source scope node.id (fun _ => word 82)
  match lower source with
  | .ok _ => pure ()
  | .error error => throw (IO.userError s!"unmodified indirect metadata rejected: {reprStr error}")
  let alter (update : IndirectCallResolution → IndirectCallResolution) : TypedSource :=
    { source with nodes := source.nodes.map fun
      | .expression expression => if expression.id = node.id then match expression.form with
        | .call callee arguments (.indirect metadata) =>
            .expression { expression with form := .call callee arguments (.indirect (update metadata)) }
        | _ => .expression expression
        else .expression expression
      | node => node }
  for source in [
      alter (fun metadata => { metadata with argumentCount := metadata.argumentCount + 1 }),
      alter (fun metadata => { metadata with argumentTypeBeforeCoercion := .bool }),
      alter (fun metadata => { metadata with argumentTypeAfterCoercion := .bool }),
      alter (fun metadata => { metadata with argumentCoercions := [{ requirement := ⟨888⟩, source := .word, target := .word }] })] do
    match lower source with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "forged indirect metadata was accepted")
  let badRecursiveInitializer : Workspace.RawWorkspace := {
    entry := "bad.solc", externalLibraries := []
    mainSources := [{ path := "bad.solc", content :=
      "function bad() returns (Word) { let f: function() returns (Word) = lam() -> Word { return f(); }; return f(); }" }]
  }
  match checkProgram badRecursiveInitializer with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "source scope unexpectedly made an initializer's binding recursive")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"function-value source fixtures failed: {reprStr errors}")
  testFunctionValues program
  testIndirectFailure program
  testTypesAndBoundaries program
  testMetadata program

end Tests.SourceCoreFunctions
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralEntry
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreGeneralEntry

open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceCoreGeneralEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree { Leaf(integer), Pair(Tree, Tree) }",
    "function keepTree(value: Tree) returns (Tree) { return value; }",
    "function keepMap(value: mapping(integer => Tree)) returns (mapping(integer => Tree)) { return value; }",
    "function keepProxy(value: @Word) returns (@Word) { return value; }",
    "function keepScalar(value: (integer, (Word, Bool))) returns (integer, (Word, Bool)) { return value; }",
    "function pack(first: Tree, second: mapping(integer => Tree), third: @Word) returns (Tree, (mapping(integer => Tree), @Word)) { return (first, (second, third)); }",
    "function absent(value: Tree) returns (Tree) { let missing: Tree; return missing; }",
    "function make(value: Tree) returns (function() returns (Tree)) { return lam() -> Tree { return value; }; }",
    "function keepFunction(value: function() returns (Tree)) returns (function() returns (Tree)) { return value; }",
    "function staged(comptime value: Word) returns (Word) { return value; }"
  ] }]
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"general entry function missing: {name}")

private def planFor (program : CheckedProgram) (names : List String) : IO Plan := do
  let requests ← names.mapM (request program)
  match SourceSpecializationWorklist.run program requests 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"general entry plan failed: {reprStr result}")

private def sites {checked : Checked} (request : BodyRequest checked) : Except String SourceCoreFaultSites.Table :=
  (SourceCoreFaultSites.prepare request.specialized.function.typedBody request.sourceResultType).mapError reprStr

/-- These small callbacks exercise the entry boundary. They are not an
alternative general source interpreter or a claim of full body lowering. -/
private def identityLowerer {checked : Checked} : BodyLowerer checked String := fun _ request => do
  pure ⟨OptionalCell.read request.result.type (.var 0) Word.zero, ← sites request⟩

private def packLowerer {checked : Checked} : BodyLowerer checked String := fun _ request => do
  let [first, second, third] := request.inputs | throw "expected three inputs"
  pure ⟨LocalSequence.pair first.type (.product second.type third.type)
    (OptionalCell.read first.type (.var 2) Word.zero)
    (LocalSequence.pair second.type third.type
      (OptionalCell.read second.type (.var 1) Word.zero)
      (OptionalCell.read third.type (.var 0) Word.zero)), ← sites request⟩

private def absentLowerer {checked : Checked} : BodyLowerer checked String := fun _ request => do
  let sites ← sites request
  let [site] := sites.reads | throw "expected one uninitialized read"
  pure ⟨.letE (OptionalCell.allocate request.result.type)
    (OptionalCell.read request.result.type (.var 0) site.reason), sites⟩

private def closureLowerer {checked : Checked} : BodyLowerer checked String := fun _ request => do
  let [input] := request.inputs | throw "expected one input"
  pure ⟨LanguageResult.success (TaggedFunction.anonymous
    (.lambda .unit (LanguageResult.resultType input.type)
      (OptionalCell.read input.type (.var 1) Word.zero))), ← sites request⟩

private def compilePlan (program : CheckedProgram) (checked : Checked) (names : List String)
    (lowerer : BodyLowerer checked String) : IO (PreparedProgram checked) := do
  let plan ← planFor program names
  match prepare program plan checked 100 lowerer with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"general entry preparation failed: {reprStr error}")

private def firstEntry {checked : Checked} (prepared : PreparedProgram checked) : IO (Entry checked) :=
  match prepared.entries with
  | first :: _ => pure first
  | [] => throw (IO.userError "general seed entry missing")

private def invoke {checked : Checked} (entry : Entry checked) (arguments : List Value) (fuel : Nat := 10000) :
    IO (Result (definitions checked) entry.resultType) :=
  match entry.run arguments fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"general entry input rejected: {reprStr error}")

private def rejectedInput {checked : Checked} (entry : Entry checked) (arguments : List Value) : IO RunError :=
  match entry.start arguments with
  | .error error => pure error
  | .ok _ => throw (IO.userError "invalid general entry input was accepted")

private def present (value : Value) : Value := .inRight .unit value

example (definitions : DataEnvironment) (world : StoreTyping) (value : Value) (type : Core.Ty)
    (accepted : ValidatedValue definitions value type) : RuntimeValueHasType world value type definitions :=
  accepted.typed world

example {checked : Checked} (entry : Entry checked) (result : Result (definitions checked) entry.resultType)
    {value : Value} {store : Store} (completed : result.observation = .succeeded value store) :
    ∃ world, RuntimeStoreHasTypes world store (definitions checked) ∧
      RuntimeValueHasType world value entry.resultType (definitions checked) :=
  result.success_typed completed

example {definitions : DataEnvironment} {type : Core.Ty}
    (checkpoint next : Checkpoint definitions type) (spent additional : Nat)
    (suspended : runStateful spent checkpoint.state = .outOfFuel next.state) :
    (next.resume additional).observation = (checkpoint.resume (spent + additional)).observation :=
  checkpoint.resume_after_exhaustion next spent additional suspended

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"general entry source fixture rejected: {reprStr errors}")
  let signature ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some signature => pure signature
    | none => throw (IO.userError "Tree signature missing")
  let treeType := TypeSystem.Ty.nominal signature.id []
  let mappingType := TypeSystem.Ty.mapping .integer treeType
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 100
      [treeType, mappingType, .proxy .word] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"general entry catalog failed: {reprStr error}")
  let treeId := (checked.catalog.identity? treeType).getD ⟨999⟩
  let mapId := (checked.catalog.identity? mappingType).getD ⟨999⟩
  let proxyId := (checked.catalog.identity? (.proxy .word)).getD ⟨999⟩
  let leaf := fun value => Value.constructed ⟨treeId, 0⟩ (.integer value)
  let tree := Value.constructed ⟨treeId, 1⟩ (.pair (leaf (-(2 ^ 300))) (leaf 7))
  let mapping := Value.constructed ⟨mapId, 1⟩
    (.pair (.pair (.integer (-8)) tree) (.constructed ⟨mapId, 0⟩ .unit))
  let proxy := Value.constructed ⟨proxyId, 0⟩ .unit
  let scalar := Value.pair (.integer (2 ^ 400)) (.pair (.word Word.zero) (.bool false))
  let prepared ← compilePlan program checked ["keepTree", "keepMap", "keepProxy", "keepScalar", "keepTree"] identityLowerer
  assertTrue (prepared.entries.map (·.key) == prepared.plan.seedKeys) "general entry changed seed order/duplicates"
  for (entry, argument) in prepared.entries.zip [tree, mapping, proxy, scalar, tree] do
    let result ← invoke entry [argument]
    assertTrue (result.observation == .succeeded argument [present argument]) "deep input/output carrier changed"
  let treeEntry ← firstEntry prepared
  let again ← invoke treeEntry [leaf 42]
  assertTrue (again.observation == .succeeded (leaf 42) [present (leaf 42)]) "cached entry reused input state"

  let packed ← firstEntry (← compilePlan program checked ["pack"] packLowerer)
  let arguments := [tree, mapping, proxy]
  let initial ← match packed.start arguments with
    | .ok initial => pure initial
    | .error error => throw (IO.userError s!"packed inputs rejected: {reprStr error}")
  assertTrue (initial.state.store == arguments.map present) "input allocation order changed"
  assertTrue (initial.state.control == .eval packed.body [
    .cellRef (OptionalCell.cellType (.namedData proxyId)) 2,
    .cellRef (OptionalCell.cellType (.namedData mapId)) 1,
    .cellRef (OptionalCell.cellType (.namedData treeId)) 0]) "input environment lost newest-first identity"
  let result ← invoke packed arguments
  assertTrue (result.observation == .succeeded (.pair tree (.pair mapping proxy)) (arguments.map present))
    "packed general outputs changed"
  let paused := initial.resume 5
  let next ← match paused.checkpoint? with
    | some next => pure next
    | none => throw (IO.userError "general execution did not retain a typed checkpoint")
  assertTrue ((next.resume 9995).observation == result.observation) "general checkpoint resume changed result/store"

  let malformed := Value.constructed ⟨treeId, 1⟩ (.pair (leaf 1) (.constructed ⟨treeId, 0⟩ (.bool true)))
  let rejected ← rejectedInput treeEntry [malformed]
  match rejected with
  | .input 0 error =>
    assertTrue (decide (error.path = [.constructorPayload, .pairRight, .constructorPayload]))
      "deep malformed payload path was lost"
  | _ => throw (IO.userError "deep malformed payload had wrong error")
  let mapEntry ← match prepared.entries[1]? with
    | some entry => pure entry
    | none => throw (IO.userError "mapping entry missing")
  discard <| rejectedInput mapEntry [.constructed ⟨mapId, 1⟩
    (.pair (.pair (.bool true) tree) (.constructed ⟨mapId, 0⟩ .unit))]
  discard <| rejectedInput mapEntry [.constructed ⟨mapId, 1⟩
    (.pair (.pair (.integer 5) tree) (leaf 0))]
  let proxyEntry ← match prepared.entries[2]? with
    | some entry => pure entry
    | none => throw (IO.userError "proxy entry missing")
  discard <| rejectedInput proxyEntry [.constructed ⟨proxyId, 0⟩ (.integer 0)]
  discard <| rejectedInput treeEntry [.constructed ⟨treeId, 9⟩ .unit]
  discard <| rejectedInput treeEntry [proxy]
  discard <| rejectedInput treeEntry []
  discard <| rejectedInput treeEntry [tree, tree]
  for forbidden in [Value.closure .unit .unit .unit [], .cellRef .integer 0, .hostFunction .storageRead] do
    discard <| rejectedInput treeEntry [.constructed ⟨treeId, 0⟩ forbidden]
  match treeEntry.start [tree] [.unit] with
  | .error (.initialStoreUnsupported 1) => pure ()
  | _ => throw (IO.userError "external initial store accepted")

  let failing ← firstEntry (← compilePlan program checked ["absent"] absentLowerer)
  let failed ← invoke failing [tree]
  let [site] := failing.faultSites.reads | throw (IO.userError "failure site missing")
  assertTrue (failed.observation == .failed site.reason [present tree, .inLeft (.namedData treeId) .unit])
    "general failure did not retain typed nominal store"
  assertTrue (failing.failureDiagnostic? site.reason |>.isSome) "general diagnostic lookup failed"
  assertTrue (!(failing.failureDiagnostic? (Word.ofNatModulo 9999)).isSome) "unknown diagnostic was accepted"

  let make ← firstEntry (← compilePlan program checked ["make"] closureLowerer)
  let returned ← invoke make [tree]
  let returnedValue ← match returned.observation with
    | .succeeded value _ => pure value
    | other => throw (IO.userError s!"internal closure result failed: {reprStr other}")
  let functionInput ← firstEntry (← compilePlan program checked ["keepFunction"] identityLowerer)
  match (← rejectedInput functionInput [returnedValue]) with
  | .input 0 error => assertTrue (decide (error.code = .functionHandleRequired)) "raw closure was not explicitly rejected"
  | _ => throw (IO.userError "raw closure input error changed")

  let badBody : BodyLowerer checked String := fun _ request => do
    pure ⟨LanguageResult.success .unit, ← sites request⟩
  let inputPlan ← planFor program ["keepTree"]
  match prepare program inputPlan checked 100 badBody with
  | .error (.coreCheckFailed _ _) => pure ()
  | _ => throw (IO.userError "uncertified callback body escaped checking")
  let stagedPlan ← planFor program ["staged"]
  match prepare program stagedPlan checked 100 identityLowerer with
  | .error (.stagedInputUnsupported _) => pure ()
  | _ => throw (IO.userError "unsupported staged input was not rejected")
  IO.println "source Core general entry GREEN"

end Tests.SourceCoreGeneralEntry
end

section
-- leanmerge: from Solcore.Test.SourceCoreIntegerAssignments
/-! Integer compound assignment support at the typed IR policy boundary.
The source checker retains its Word-only compound/unary admission policy;
these fixtures do not claim Integer compound syntax passes source inference. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreIntegerAssignments

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"integer_assignment", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def targetId : Resolved.LocalId := ⟨owner, 0⟩
private def rhsId : Resolved.LocalId := ⟨owner, 1⟩
private def expressionId : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statementId (index : Nat) : StatementId := ⟨⟨owner, index + 1⟩⟩
private def span (index : Nat) : Syntax.SourceSpan := {
  source := { origin := .main, path := "integer_assignment.solc" }
  startByte := index
  endByte := index + 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def invalidReason : Core.Word := word 63
private def readReason : Core.Word := word 70
private def present (value : Int) : Core.Value := .inRight .unit (.integer value)
private def absent : Core.Value := .inLeft .integer .unit
private def scope : SourceCoreBasic.Scope := [(rhsId, .integer), (targetId, .integer)]
private def assignment : AssignmentResolution := {
  target := { root := targetId, projections := [], type := .integer }
}
private def source (operator : Syntax.ValueAssignOp) : TypedSource := {
  owner
  inputs := [
    { id := targetId, name := "target", scheme := .mono .integer },
    { id := rhsId, name := "rhs", scheme := .mono .integer }
  ]
  roots := [.statement (statementId 0)]
  nodes := [
    .expression {
      id := expressionId
      span := span 0
      type := .integer
      form := .reference "rhs" (.local rhsId)
    },
    .statement {
      id := statementId 0
      span := span 1
      type := .unit
      form := .assignValue assignment operator expressionId
    }
  ]
}

private def expressionLowerer : SourceCoreControl.ExpressionLowerer :=
  fun _ source scope id reasons => do
    let (node, type) ← SourceCoreFunctionTypes.readExpression source id
    match node.form with
    | .reference _ (.builtinBoolean value) =>
        SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool type
        pure ⟨.bool, Core.LanguageResult.success (.bool value)⟩
    | _ =>
        let expression ← SourceCoreFunctionTypes.lowerRead source scope node.id (reasons id)
        pure ⟨type, expression⟩

private def lower (operator : Syntax.ValueAssignOp) : Except SourceCoreBasic.Error Core.Expr :=
  SourceCoreAssignments.assignValueWithReasons expressionLowerer 100 (source operator) scope
    assignment operator expressionId .integer
    (Core.OptionalCell.read .integer (.var 1) readReason) invalidReason (fun _ => readReason)

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expectError {α : Type} (result : Except SourceCoreBasic.Error α)
    (accepts : SourceCoreBasic.Error → Bool) : IO Unit := do
  match result with
  | .error error => assertTrue (accepts error) s!"wrong Integer assignment rejection: {reprStr error}"
  | .ok _ => throw (IO.userError "invalid Integer assignment metadata was accepted")

private def runCore (body : Core.Expr) (store : Core.Store) : IO Core.StatefulRunResult := do
  assertTrue (Core.infer? (SourceCoreLocalCell.coreContext scope) body ==
    some (Core.LanguageResult.resultType .integer)) "Integer policy failed Core checking"
  pure (Core.runStateful 500 (.initial body [
    .cellRef (Core.OptionalCell.cellType .integer) 1,
    .cellRef (Core.OptionalCell.cellType .integer) 0] store))

private def testOperations : IO Unit := do
  for (operator, expected) in ([
      (.add, -4), (.subtract, -10), (.multiply, -21), (.divide, -3), (.modulo, 2),
      (.bitAnd, 1), (.bitOr, -5), (.bitXor, -6)] : List (Syntax.ValueAssignOp × Int)) do
    let body ← match lower operator with
      | .ok body => pure body
      | .error error => throw (IO.userError s!"Integer compound policy rejected: {reprStr error}")
    assertTrue ((← runCore body [present (-7), present 3]) ==
      .done (.inRight .word (.integer expected)) [present expected, present 3])
      "Integer compound policy changed arithmetic or reference selection"
    assertTrue ((← runCore body [absent, present 3]) ==
      .done (.inLeft .integer (.word invalidReason)) [absent, present 3])
      "Integer absent snapshot lost its language failure reason"
    assertTrue ((← runCore body [absent, absent]) ==
      .done (.inLeft .integer (.word readReason)) [absent, absent])
      "Integer RHS read failure must precede absence of the snapshot"
  let unary ← match SourceCoreAssignments.assignBitNot (source .equal) scope assignment .integer
      (Core.OptionalCell.read .integer (.var 1) readReason) invalidReason with
    | .ok body => pure body
    | .error error => throw (IO.userError s!"Integer unary policy rejected: {reprStr error}")
  assertTrue ((← runCore unary [present (-7), present 3]) ==
    .done (.inRight .word (.integer 6)) [present 6, present 3])
    "Integer unary assignment lost infinite two's-complement semantics"
  assertTrue ((← runCore unary [absent, absent]) ==
    .done (.inLeft .integer (.word invalidReason)) [absent, absent])
    "Integer unary absence evaluated an irrelevant RHS or changed the heap"
  let equal ← match lower .equal with
    | .ok body => pure body
    | .error error => throw (IO.userError s!"Integer bare equal was rejected: {reprStr error}")
  assertTrue ((← runCore equal [absent, present 3]) ==
    .done (.inRight .word (.integer 3)) [present 3, present 3])
    "Integer equal assignment must initialize an absent target"

private def testMetadata : IO Unit := do
  let condition : ExpressionId := ⟨⟨owner, 3⟩⟩
  let forNode : StatementNode := {
    id := statementId 1, span := span 10, type := .unit
    form := .forLoop
      [.assignValue assignment .add expressionId, .assignValue assignment .add expressionId]
      condition [.assignBitNot assignment, .assignValue assignment .multiply expressionId] []
  }
  let source := { source .add with nodes := (source .add).nodes ++ [
    .expression {
      id := condition
      span := span 9
      type := .bool
      form := .reference "false" (.builtinBoolean false)
    }, .statement forNode] }
  let table ← match SourceCoreAssignmentFaultSites.prepare source 100 with
    | .ok table => pure table
    | .error error => throw (IO.userError s!"Integer assignment reasons rejected: {reprStr error}")
  assertTrue (table.length == 4 && table.sites.map (·.reason.val) == [100, 101, 102, 103])
    "Integer header assignment reasons changed order or deduplication"
  for site in table.sites do
    assertTrue (decide (site.rhsType = .integer)) "Integer diagnostic RHS type was narrowed to Word"
    let error := match site.kind with
      | .value operator => SourceTypedRuntime.RuntimeError.invalidAssignmentOperands operator none (some .integer)
      | .bitNot => SourceTypedRuntime.RuntimeError.invalidUnaryOperand .bitNot none
    assertTrue (decide (table.diagnostic? site.reason = some {
      error, site := site.site, span := some site.span }))
      "Integer absent-operand diagnostic lost its exact source type, site or span"
  let location := SourceCoreElaboration.ErrorSite.occurrence forNode.id.occurrence
  assertTrue (table.reasonAt location targetId (.value .add) == word 101 &&
    table.reasonAt location targetId .bitNot == word 102 &&
    table.reasonAt location targetId (.value .multiply) == word 103)
    "Integer header diagnostic provider did not use its parent occurrence"
  assertTrue (decide (table.diagnostic? (word 999) = none)) "unknown Integer reason produced a diagnostic"
  match SourceCoreAssignmentFaultSites.prepare source (Core.wordModulus - 3) with
  | .error .reasonSpaceExhausted => pure ()
  | _ => throw (IO.userError "Integer assignment reasons wrapped at the Word boundary")

private def testBoundaries : IO Unit := do
  let projected := { assignment with target := { assignment.target with projections := [.member "field" 0] } }
  expectError (SourceCoreAssignments.target (source .add) scope projected)
    fun error => error matches .projectedAssignment _
  expectError (SourceCoreAssignments.target (source .add) scope { assignment with requirements := [⟨0⟩] })
    fun error => error matches .assignmentRequirementsPresent _
  let foreign := { assignment with target := { assignment.target with root := ⟨⟨ownerModule, 1⟩, 0⟩ } }
  expectError (SourceCoreAssignments.target (source .add) scope foreign)
    fun error => error matches .ownerMismatch _ _
  let wrong := { assignment with target := { assignment.target with type := .bool } }
  expectError (SourceCoreAssignments.target (source .add) scope wrong)
    fun error => error matches .typeMismatch _ .integer .bool
  let wrongRhs := { source .add with nodes := (source .add).nodes.map fun
    | .expression node => .expression { node with type := .bool }
    | node => node }
  expectError (SourceCoreAssignments.assignValueWithReasons expressionLowerer 100 wrongRhs
    [(rhsId, .bool), (targetId, .integer)] assignment .add expressionId .integer .unit
    invalidReason (fun _ => readReason)) fun error => error matches .typeMismatch _ .integer .bool
  let tupleType := Core.Ty.product .integer .bool
  let tupleAssignment := { assignment with target := { assignment.target with type := .product .integer .bool } }
  expectError (SourceCoreAssignments.assignBitNot (source .equal) [(targetId, tupleType)]
    tupleAssignment tupleType .unit invalidReason)
    fun error => error matches .typeMismatch _ .word (.product .integer .bool)

private def testLoopPolicy : IO Unit := do
  let flagId : Resolved.LocalId := ⟨owner, 2⟩
  let flagExpression : ExpressionId := ⟨⟨owner, 10⟩⟩
  let falseExpression : ExpressionId := ⟨⟨owner, 11⟩⟩
  let resultExpression : ExpressionId := ⟨⟨owner, 12⟩⟩
  let loopId := statementId 20
  let continueId := statementId 21
  let skippedId := statementId 22
  let returnId := statementId 23
  let flagAssignment : AssignmentResolution := {
    target := { root := flagId, projections := [], type := .bool }
  }
  let loopScope : SourceCoreBasic.Scope := (flagId, .bool) :: scope
  for (operator, expected) in ([
      (some .add, -1), (some .subtract, -13), (some .multiply, -63),
      (some .divide, -1), (some .modulo, 2), (some .bitAnd, 1),
      (some .bitOr, -5), (some .bitXor, -7), (none, -7)] :
      List (Option Syntax.ValueAssignOp × Int)) do
    let update : ForItemForm := match operator with
      | some operator => .assignValue assignment operator expressionId
      | none => .assignBitNot assignment
    let loop : TypedSource := {
      (source .equal) with
      roots := [.statement loopId, .statement returnId]
      nodes := (source .equal).nodes.take 1 ++ [
        .expression {
          id := flagExpression
          span := span 10
          type := .bool
          form := .reference "flag" (.local flagId)
        },
        .expression {
          id := falseExpression
          span := span 11
          type := .bool
          form := .reference "false" (.builtinBoolean false)
        },
        .expression {
          id := resultExpression
          span := span 12
          type := .integer
          form := .reference "target" (.local targetId)
        },
        .statement {
          id := loopId
          span := span 20
          type := .unit
          form := .forLoop [update] flagExpression
            [update, .assignValue flagAssignment .equal falseExpression] [continueId, skippedId]
        },
        .statement { id := continueId, span := span 21, type := .unit, form := .continueStmt },
        .statement {
          id := skippedId
          span := span 22
          type := .unit
          form := .assignValue assignment .equal expressionId
        },
        .statement {
          id := returnId
          span := span 23
          type := .integer
          form := .returnStmt (some resultExpression)
        }
      ]
    }
    let sites ← match SourceCoreAssignmentFaultSites.prepare loop 100 with
      | .ok sites => pure sites
      | .error error => throw (IO.userError s!"Integer loop sites rejected: {reprStr error}")
    assertTrue (sites.length == 1) "matching Integer init/post sites did not deduplicate"
    let policy := SourceCoreAssignmentPolicy.attach {
      lowerExpression := expressionLowerer
      readStatement := SourceCoreFunctionTypes.readStatement
      lowerBinder := SourceCoreFunctionTypes.lowerBinder
      lowerAssignment := SourceCoreFunctionTypes.lowerAssignment
    } sites
    let body ← match SourceCoreLoops.lowerStatementsWithPolicy policy 100 loop loopScope
        [loopId, returnId] .integer (fun _ => readReason) Core.Word.zero (word 90) with
      | .ok body => pure body
      | .error error => throw (IO.userError s!"Integer for policy rejected: {reprStr error}")
    assertTrue (Core.infer? (SourceCoreLocalCell.coreContext loopScope) body ==
      some (Core.LanguageResult.resultType .integer)) "Integer for helper failed Core checking"
    let environment : Core.Environment := [
      .cellRef (Core.OptionalCell.cellType .bool) 2,
      .cellRef (Core.OptionalCell.cellType .integer) 1,
      .cellRef (Core.OptionalCell.cellType .integer) 0]
    match Core.runStateful 1000 (.initial body environment [present (-7), present 3, .inRight .unit (.bool true)]) with
    | .done (.inRight .word value) store =>
        assertTrue (value == .integer expected && store.take 3 ==
          [present expected, present 3, .inRight .unit (.bool false)])
          "Integer for initializer/post/continue order or shared heap changed"
        assertTrue (store.length == 4) "Integer for helper did not retain its administrative closure cell"
    | result => throw (IO.userError s!"Integer for helper did not finish: {reprStr result}")
    match Core.runStateful 1000 (.initial body environment [absent, present 3, .inRight .unit (.bool true)]) with
    | .done (.inLeft .integer (.word token)) store =>
        assertTrue (token == word 100 && store == [absent, present 3, .inRight .unit (.bool true)])
          "Integer absent initializer did not stop before condition/body/post allocation"
    | result => throw (IO.userError s!"Integer absent for initializer changed: {reprStr result}")
    let postSource := { loop with nodes := loop.nodes.map fun
      | .statement node =>
          if node.id = loopId then
            .statement { node with
              form := .forLoop [] flagExpression
                [update, .assignValue flagAssignment .equal falseExpression] [continueId, skippedId] }
          else .statement node
      | node => node }
    let postBody ← match SourceCoreLoops.lowerStatementsWithPolicy policy 100 postSource loopScope
        [loopId, returnId] .integer (fun _ => readReason) Core.Word.zero (word 90) with
      | .ok body => pure body
      | .error error => throw (IO.userError s!"Integer post policy rejected: {reprStr error}")
    assertTrue (Core.infer? (SourceCoreLocalCell.coreContext loopScope) postBody ==
      some (Core.LanguageResult.resultType .integer)) "Integer post helper failed Core checking"
    for right in [present 3, absent] do
      let expectedReason := if operator.isSome && right == absent then readReason else word 100
      match Core.runStateful 1000 (.initial postBody environment [absent, right, .inRight .unit (.bool true)]) with
      | .done (.inLeft .integer (.word token)) store =>
          assertTrue (token == expectedReason && store.take 3 == [absent, right, .inRight .unit (.bool true)] &&
            store.length == 4) "Integer post failure lost RHS priority, the heap or its administrative cell"
      | result => throw (IO.userError s!"Integer absent post did not fail after continue: {reprStr result}")

private def testSourceAdmission : IO Unit := do
  for update in ["+= rhs", "-= rhs", "*= rhs", "/= rhs", "%= rhs", "&= rhs", "|= rhs", "^= rhs", "~="] do
    let workspace : Workspace.RawWorkspace := {
      entry := "main.solc"
      externalLibraries := []
      mainSources := [{ path := "main.solc", content :=
        "function rejected(value: integer, rhs: integer) returns (integer) { value " ++ update ++ "; return value; }" }]
    }
    match checkProgram workspace with
    | .error [.inference _] => pure ()
    | result => throw (IO.userError s!"Integer compound checker admission changed: {reprStr result}")

def run : IO Unit := do
  testOperations
  testMetadata
  testBoundaries
  testLoopPolicy
  testSourceAdmission

end Tests.SourceCoreIntegerAssignments
end

section
-- leanmerge: from Solcore.Test.SourceCoreIntegerEntry
/-! The prepared Entry boundary validates complete Integer/product trees and
retains typed optional-cell reads and checkpoint resumption. The direct fixture
is a typed Entry; it does not claim the Basic source lowerer accepts Integer. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.Value
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCoreIntegerEntry

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceCoreBasicEntry

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"integer_entry", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reason : Core.Word := word 7

private def sourceType : TypeSystem.Ty :=
  .product .integer (.product .bool (.product .word .integer))
private def coreType : Core.Ty :=
  .product .integer (.product .bool (.product .word .integer))

private def inputs : List Input := [
  { id := binder 0, sourceType, type := coreType, comptime := false },
  { id := binder 1, sourceType := .integer, type := .integer, comptime := false },
  { id := binder 2, sourceType := .bool, type := .bool, comptime := false }
]

private def inputSource : TypedSource := {
  owner
  inputs := [
    { id := binder 0, name := "tree", scheme := .mono sourceType },
    { id := binder 1, name := "integer", scheme := .mono .integer },
    { id := binder 2, name := "flag", scheme := .mono .bool }
  ]
  roots := []
  nodes := []
}

private theorem projected :
    SourceCoreScalar.lowerType (.declaration owner) sourceType = .ok coreType := by rfl

private theorem coreTypeWF : Core.Ty.WellFormed [] coreType :=
  .product .integer (.product .bool (.product .word .integer))

private def entry : Entry := {
  key := { declaration := owner, arguments := [] }
  inputs
  sourceResultType := sourceType
  resultType := coreType
  resultProjection := projected
  faultSites := { owner, resultType := sourceType, reads := [], escapedReason := word 1 }
  body := Core.OptionalCell.read coreType (.var 2) reason
  bodyTyped := Core.OptionalCell.read_hasType reason coreTypeWF (.var rfl)
}

example : SourceCoreScalar.Value.ofCore?
    (.pair (.integer (-7)) (.pair (.bool true) (.pair (.word (word 3)) (.integer 9)))) =
    some (.product (.integer (-7)) (.product (.bool true) (.product (.word (word 3)) (.integer 9)))) := rfl

example (result : Result coreType) {value : Core.Value} {store : Core.Store}
    (success : result.observation = .succeeded value store) :
    ∃ world, Core.RuntimeStoreHasTypes world store ∧ Core.RuntimeValueHasType world value coreType :=
  result.success_typed success

example (checkpoint next : Checkpoint coreType) (spent additional : Nat)
    (exhausted : Core.runStateful spent checkpoint.state = .outOfFuel next.state) :
    (next.resume additional).observation = (checkpoint.resume (spent + additional)).observation :=
  checkpoint.resume_after_exhaustion next spent additional exhausted

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expectError {α : Type} (name : String) (result : Except SourceCoreBasicEntry.Error α)
    (accept : SourceCoreBasicEntry.Error → Bool) : IO Unit := do
  match result with
  | .error error => assertTrue (accept error) s!"{name}: wrong boundary error {reprStr error}"
  | .ok _ => throw (IO.userError s!"{name}: invalid boundary value was accepted")

private def huge : Int := (2 : Int) ^ 1024 + 17
private def deep (first last : Int) : Core.Value :=
  .pair (.integer first) (.pair (.bool true) (.pair (.word (word 11)) (.integer last)))
private def arguments : List Core.Value := [deep (-huge) huge, .integer (-3), .bool false]
private def present (value : Core.Value) : Core.Value := .inRight .unit value

private def start (values : List Core.Value) : IO (Checkpoint entry.resultType) := do
  match entry.start values with
  | .ok checkpoint => pure checkpoint
  | .error error => throw (IO.userError s!"Integer Entry.start failed: {reprStr error}")

def run : IO Unit := do
  let prepared ← match prepareInputs inputSource with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"Integer input metadata failed: {reprStr error}")
  assertTrue (prepared.map (·.id) == inputs.map (·.id) &&
    prepared.map (·.type) == [coreType, .integer, .bool])
    "Integer input projection lost source order or the deep product shape"
  let checkpoint ← start arguments
  assertTrue (checkpoint.state.store == arguments.map present)
    "Integer input cells must contain the exact arbitrary precision values"
  assertTrue (checkpoint.state.control == .eval entry.body [
    .cellRef (Core.OptionalCell.cellType .bool) 2,
    .cellRef (Core.OptionalCell.cellType .integer) 1,
    .cellRef (Core.OptionalCell.cellType coreType) 0])
    "Integer input environment lost newest-first references or payload types"
  let complete := checkpoint.resume 200
  assertTrue (complete.observation == .succeeded (deep (-huge) huge) (arguments.map present))
    "Integer optional-cell read changed its exact value or the shared store"
  let paused := checkpoint.resume 3
  let next ← match paused.checkpoint? with
    | some next => pure next
    | none => throw (IO.userError "Integer optional-cell read did not suspend at fuel three")
  assertTrue ((next.resume 197).observation == complete.observation)
    "typed Integer checkpoint/resume changed the result or store"
  let freshArguments := [deep 1 (-2), .integer huge, .bool true]
  let fresh := (← start freshArguments).resume 200
  assertTrue (fresh.observation == .succeeded (deep 1 (-2)) (freshArguments.map present))
    "reusing a prepared Integer entry reused an earlier input store"

  expectError "Integer count" (entry.start []) fun error => error matches .argumentCountMismatch 3 0
  expectError "Integer source type" (entry.start [deep 1 2, .word (word 3), .bool false])
    fun error => error matches .inputTypeMismatch 1 .integer .word
  expectError "Integer deep structural type" (entry.start [
      .pair (.integer 1) (.pair (.bool true) (.pair (.word (word 11)) (.bool false))),
      .integer 3, .bool false]) fun error => error matches .inputTypeMismatch 0 _ _
  let invalidLeaves : List Core.Value := [
    .cellRef .integer 0,
    .cellRef .integer 999999,
    .closure .unit .integer (.integer 1) [],
    .closure .unit .integer (.integer 1) [.cellRef .integer 999999],
    .hostFunction .storageRead,
    .inRight .unit (.integer 2),
    .constructed ⟨⟨0⟩, 0⟩ (.integer 2)
  ]
  for leaf in invalidLeaves do
    let forged : Core.Value := .pair (.integer 1) (.pair (.bool true) (.pair (.word (word 11)) leaf))
    expectError "deep Integer capability" (entry.start [forged, .integer 3, .bool false])
      fun error => error matches .inputShape 0 _
  expectError "Integer closure top-level" (entry.start [deep 1 2,
      .closure .unit .integer (.integer 1) [], .bool false])
    fun error => error matches .inputShape 1 .integer
  expectError "Integer supplied store" (entry.start arguments [.integer 99])
    fun error => error matches .initialStoreUnsupported 1

  let unsupported : TypedSource := { inputSource with inputs := [
    { id := binder 0, name := "function", scheme := .mono (.function .unit .integer) }
  ] }
  expectError "Integer public function parameter" (prepareInputs unsupported)
    fun error => error matches .lowering (.typeProjection { reason := .unsupportedType (.function _ _), .. })
  let foreign : TypedSource := { inputSource with inputs := [
    { id := ⟨⟨ownerModule, 1⟩, 0⟩, name := "foreign", scheme := .mono .integer }
  ] }
  expectError "Integer input metadata owner" (prepareInputs foreign)
    fun error => error matches .lowering (.ownerMismatch _ _)
  let duplicate : TypedSource := { inputSource with inputs := [
    { id := binder 0, name := "one", scheme := .mono .integer },
    { id := binder 0, name := "two", scheme := .mono .integer }
  ] }
  expectError "Integer duplicate input" (prepareInputs duplicate)
    fun error => error matches .lowering (.duplicateBinding _)

end Tests.SourceCoreIntegerEntry
end

section
-- leanmerge: from Solcore.Test.SourceCoreIntegerFunctionEntry
/-! Real source plans exercise native Integer inputs/results through the
function-value profile, independently of the public compiler adapter. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreIntegerFunctionEntry

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceCoreFunctionEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def huge : Int := (2 : Int) ^ 1024 + 17
private def deep (first last : Int) : Core.Value :=
  .pair (.integer first) (.pair (.bool true) (.pair (.word (word 11)) (.integer last)))
private def deepType : Core.Ty :=
  .product .integer (.product .bool (.product .word .integer))
private def present (value : Core.Value) : Core.Value := .inRight .unit value

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function echo(value: integer) returns (integer) { let copied: integer = value; return copied; }",
    "function tree(input: (integer, (Bool, (Word, integer)))) returns (integer, (Bool, (Word, integer))) { return input; }",
    "function replace(input: (integer, (Bool, (Word, integer))), replacement: (integer, (Bool, (Word, integer)))) returns (integer, (Bool, (Word, integer))) {",
    " let saved: (integer, (Bool, (Word, integer))) = input; saved = replacement; return saved; }",
    "function named(value: integer) returns (integer) { return echo(value); }",
    "function shared(value: integer) returns (integer) {",
    " let f: function(integer) returns (integer) = lam(n: integer) -> integer { value = integerAdd(value, n); return value; };",
    " let first: integer = f(2); return f(3); }",
    "function recurse(count: integer, value: integer) returns (integer) {",
    " return integerEq(count, 0) ? value : recurse(integerSub(count, 1), value); }",
    "function absent() returns (integer) { let missing: integer; return missing; }",
    "function calleeFailure() returns (integer) { return absent(); }",
    "function comptimeCompare(comptime value: integer) returns (Bool) { return integerLt(value, 0); }",
    "function stagedEcho(comptime value: integer) returns (integer) { return value; }",
    "function useStaged(value: integer) returns (integer) { return stagedEcho(value); }",
    "function publicFunction(f: function(integer) returns (integer)) returns (integer) { return f(0); }",
    "function make() returns (function(integer) returns (integer)) { return lam(n: integer) -> integer { return n; }; }"
  ] }]
  externalLibraries := []
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"Integer source fixture missing: {name}")

private def plan (program : CheckedProgram) (names : List String) : IO Plan := do
  let requests ← names.mapM (request program)
  match SourceSpecializationWorklist.run program requests 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"Integer source worklist failed: {reprStr result}")

private def prepared (program : CheckedProgram) (names : List String) : IO PreparedProgram := do
  let input ← plan program names
  match prepare program input 100 Core.Word.zero with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError s!"Integer source entry preparation failed: {reprStr error}")

private def firstEntry (compiled : PreparedProgram) : IO Entry :=
  match compiled.entries with
  | entry :: _ => pure entry
  | [] => throw (IO.userError "Integer prepared seed missing")

private def execute (entry : Entry) (arguments : List Core.Value) (fuel : Nat := 30000) :
    IO (SourceCoreBasicEntry.Result entry.resultType) := do
  match entry.run arguments fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"Integer source invocation rejected: {reprStr error}")

private def success (entry : Entry) (arguments : List Core.Value) (expected : Core.Value) : IO Core.Store := do
  match (← execute entry arguments).observation with
  | .succeeded value store =>
      assertTrue (value == expected) "Integer source result mismatch"
      pure store
  | result => throw (IO.userError s!"Integer source entry did not succeed: {reprStr result}")

private def testSources (program : CheckedProgram) : IO Unit := do
  let echoCompiled ← prepared program ["echo"]
  let echo ← firstEntry echoCompiled
  assertTrue (echo.resultType == .integer && echo.inputs.map (·.type) == [.integer])
    "integer seed signature was projected through the legacy Word carrier"
  let store ← success echo [.integer (-huge)] (.integer (-huge))
  assertTrue (store[0]? == some (present (.integer (-huge)))) "Integer public input cell changed precision"
  discard <| success echo [.integer huge] (.integer huge)

  let tree ← firstEntry (← prepared program ["tree"])
  assertTrue (tree.resultType == deepType && tree.inputs.map (·.type) == [deepType])
    "deep integer source signature shape changed"
  discard <| success tree [deep (-huge) huge] (deep (-huge) huge)
  let replace ← firstEntry (← prepared program ["replace"])
  let store ← success replace [deep (-huge) huge, deep 9 (-12)] (deep 9 (-12))
  assertTrue (store[0]? == some (present (deep (-huge) huge)))
    "deep integer assignment mutated the input value instead of the local reference"
  discard <| success (← firstEntry (← prepared program ["named"])) [.integer huge] (.integer huge)
  /- Each call of `f` starts again from the captured `value`, so the second
  call returns `value + 3`. -/
  let shared ← firstEntry (← prepared program ["shared"])
  discard <| success shared [.integer (-huge)]
    (.integer (-huge + 3))
  let recursive ← firstEntry (← prepared program ["recurse"])
  discard <| success recursive [.integer 3, .integer huge] (.integer huge)
  let paused ← execute recursive [.integer 3, .integer huge] 15
  let checkpoint ← match paused.checkpoint? with
    | some checkpoint => pure checkpoint
    | none => throw (IO.userError "Integer recursion did not produce a typed checkpoint")
  assertTrue ((checkpoint.resume 30000).observation ==
    (← execute recursive [.integer 3, .integer huge] 30015).observation)
    "integer source recursion checkpoint/resume changed its exact value or store"

private def testFailures (program : CheckedProgram) : IO Unit := do
  let compiled ← prepared program ["calleeFailure"]
  let entry ← firstEntry compiled
  let owner := (← request program "absent").declaration
  let site ← match entry.faultSites.reads.find? (fun site => decide (site.binder.owner = owner)) with
    | some site => pure site
    | none => throw (IO.userError "Integer callee's missing read diagnostic was lost")
  match (← execute entry []).observation with
  | .failed reason store =>
      assertTrue (reason == site.reason && store.any (· == .inLeft .integer .unit))
        "integer uninitialized failure changed its exact token or optional payload type"
      assertTrue (decide (entry.failureDiagnostic? reason = some {
        error := .uninitializedLocal site.binder
        site := .occurrence site.expression.occurrence
        span := some site.span
      })) "Integer callee diagnostic lost its owner, binder or source span"
  | result => throw (IO.userError s!"Integer uninitialized local did not fail: {reprStr result}")

private def testPublicBoundary (program : CheckedProgram) : IO Unit := do
  let staged ← firstEntry (← prepared program ["comptimeCompare"])
  assertTrue (staged.inputs.map (·.comptime) == [true])
    "comptime Integer public seed input marker was discarded"
  discard <| success staged [.integer (-huge)] (.bool true)
  discard <| success staged [.integer huge] (.bool false)
  let stagedCall ← plan program ["useStaged"]
  match prepare program stagedCall 100 Core.Word.zero with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "internal comptime Integer call was silently moved to runtime")
  let tree ← firstEntry (← prepared program ["tree"])
  match tree.start [deep 1 2] [.integer 3] with
  | .error (.initialStoreUnsupported 1) => pure ()
  | _ => throw (IO.userError "Integer source entry accepted a supplied initial store")
  match tree.start [.pair (.integer 1) (.pair (.bool true) (.pair (.word (word 11)) (.bool false)))] with
  | .error (.inputTypeMismatch 0 _ _) => pure ()
  | _ => throw (IO.userError "Integer source entry accepted the wrong deep leaf type")
  for leaf in ([
      .cellRef .integer 999999,
      .closure .unit .integer (.integer 0) [.cellRef .integer 999999],
      .hostFunction .storageRead] : List Core.Value) do
    let invalid : Core.Value := .pair (.integer 1) (.pair (.bool true) (.pair (.word (word 11)) leaf))
    match tree.start [invalid] with
    | .error (.inputShape 0 _) => pure ()
    | _ => throw (IO.userError "Integer source entry accepted a deep external capability")
  let input ← plan program ["publicFunction"]
  match prepare program input 100 Core.Word.zero with
  | .error (.entry (.lowering (.typeProjection { reason := .unsupportedType (.function _ _), .. }))) => pure ()
  | result => throw (IO.userError s!"Integer public function input was accepted: {reprStr result}")
  let input ← plan program ["make"]
  match prepare program input 100 Core.Word.zero with
  | .error (.lowering (.typeProjection { reason := .unsupportedType (.function _ _), .. })) => pure ()
  | result => throw (IO.userError s!"Integer public function output was accepted: {reprStr result}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"Integer source fixtures failed checking: {reprStr errors}")
  testSources program
  testFailures program
  testPublicBoundary program

end Tests.SourceCoreIntegerFunctionEntry
end

section
-- leanmerge: from Solcore.Test.SourceCoreLocalPolymorphism
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.RuntimeValue

/-! Discovery/projection tests use checked source metadata. Shared capture
execution uses an explicit typed Core bundle; this module does not claim that
the whole source compiler already routes generalized local lets through it. -/

set_option autoImplicit false

namespace Tests.SourceCoreLocalPolymorphism

open Solcore Solcore.Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function sameInnerType(flag: Bool) returns (Word, Word) {",
    " let outer = lam(value) { let inner = lam(item) { return item; }; return inner(1); };",
    " return (outer(1), outer(flag)); }",
    "function dependentInner(flag: Bool) returns ((Word, Word), (Bool, Bool)) {",
    " let outer = lam(value) { let inner = lam(item) { return (value, item); }; return inner(value); };",
    " return (outer(1), outer(flag)); }",
    "function sharedCapture(flag: Bool) returns (Word) {",
    " let total: Word = 0; let f = lam(item) { total += 1; return item; };",
    " f(1); f(flag); f(2); return total; }",
    "function qualified(flag: Bool) returns (Word, Bool) {",
    " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }",
    "function unused() returns (Word) {",
    " let outer = lam(value) { let inner = lam(item) { return item; }; return inner(value); }; return 9; }"
  ] }] }

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"local bundle fixture missing: {name}")
  pure ⟨signature.id, []⟩

private def plan (program : CheckedProgram) (requests : List SourceSpecializationWorklist.Request) :
    IO SourceSpecializationWorklist.Plan :=
  match SourceSpecializationWorklist.run program requests 64 with
  | .ok (.complete plan) => pure plan
  | other => throw (IO.userError s!"local bundle worklist failed: {reprStr other}")

private def binding (catalog : Catalog) (name : String) : IO Binding :=
  match catalog.bindings.filter (·.binder.name == name) with
  | [binding] => pure binding
  | _ => throw (IO.userError s!"local bundle binding missing: {name}")

private def references (binding : Binding) : List ExpressionId :=
  binding.source.nodes.filterMap fun
    | .expression { id, form := .reference _ (.local selected), .. } =>
        if selected == binding.binder.id then some id else none
    | _ => none

private def checkRead (binding : Binding) (catalog : Catalog) (active : Substitution)
    (id : ExpressionId) : IO SourceCoreBasic.LoweredExpr := do
  let source := binding.source.applySubstitution active
  let payload := binding.bundleType active
  match lowerRead catalog binding.caller active source [(binding.binder.id, payload)] id (word 31) with
  | .ok lowered =>
      assertTrue (Core.infer? [Core.OptionalCell.referenceType payload] lowered.expression ==
        some (Core.LanguageResult.resultType lowered.type)) "local bundle read did not type-check"
      pure lowered
  | .error error => throw (IO.userError s!"local bundle read rejected: {reprStr error}")

/-- Both instances capture the same reference at index zero. Their argument
types differ; both increment the same optional Word cell before returning it. -/
private def countingClosure (parameter : Core.Ty) : Core.Expr :=
  Core.TaggedFunction.anonymous (.lambda parameter (Core.LanguageResult.resultType parameter)
    (Core.LanguageResult.bind parameter (Core.OptionalCell.read .word (.var 1) (word 31))
      (.letE (.storeCell (.var 2) (.inRight .unit (.binary .wordAdd (.var 0) (literal 1))))
        (Core.LanguageResult.success (.var 2)))))

private def wordFunction : Core.Ty := Core.TaggedFunction.functionType .word .word
private def boolFunction : Core.Ty := Core.TaggedFunction.functionType .bool .bool
private def bundleType : Core.Ty := ProductBundle.type [wordFunction, boolFunction]
private def readWord : Core.Expr := read bundleType wordFunction (.var 0) (.first (.var 0)) (word 31)
private def readBool : Core.Expr := read bundleType boolFunction (.var 0) (.second (.var 0)) (word 31)
private def sharedProgram : Core.Program := {
  resultType := Core.LanguageResult.resultType .word
  body := Core.LocalSequence.letInitialized .word .word (Core.LanguageResult.success (literal 0))
    (Core.LocalSequence.letInitialized .word bundleType
      (Core.LanguageResult.success (ProductBundle.expression [countingClosure .word, countingClosure .bool]))
      (Core.LocalSequence.discard .word
        (Core.TaggedFunction.call .word readWord (Core.LanguageResult.success (literal 7)))
        (Core.LocalSequence.discard .word
          (Core.TaggedFunction.call .bool readBool (Core.LanguageResult.success (.bool true)))
          (Core.OptionalCell.read .word (.var 1) (word 31))))) }

example {definitions : Core.DataEnvironment} {context : Core.Context}
    {left right : Core.Expr}
    (leftTyped : Core.HasType context left wordFunction definitions)
    (rightTyped : Core.HasType context right boolFunction definitions) :
    Core.HasType context (ProductBundle.expression [left, right]) bundleType definitions :=
  ProductBundle.expression_hasType (.cons leftTyped (.cons rightTyped .nil))

example {definitions : Core.DataEnvironment} {context : Core.Context} {bundle : Core.Expr}
    (typed : Core.HasType context bundle bundleType definitions) :
    Core.HasType context (.second bundle) boolFunction definitions :=
  ProductBundle.project_hasType (types := [wordFunction, boolFunction]) (index := 1) rfl rfl typed

example {environment : Core.Environment} {store : Core.Store} :
    Core.Evaluates environment store
      (ProductBundle.expression [countingClosure .word, countingClosure .bool])
      (ProductBundle.value [
        .pair (.inLeft .word .unit) (.closure .word (Core.LanguageResult.resultType .word)
          (Core.LanguageResult.bind .word (Core.OptionalCell.read .word (.var 1) (word 31))
            (.letE (.storeCell (.var 2) (.inRight .unit (.binary .wordAdd (.var 0) (literal 1))))
              (Core.LanguageResult.success (.var 2)))) environment),
        .pair (.inLeft .word .unit) (.closure .bool (Core.LanguageResult.resultType .bool)
          (Core.LanguageResult.bind .bool (Core.OptionalCell.read .word (.var 1) (word 31))
            (.letE (.storeCell (.var 2) (.inRight .unit (.binary .wordAdd (.var 0) (literal 1))))
              (Core.LanguageResult.success (.var 2)))) environment)]) store :=
  ProductBundle.expression_evaluates (.cons (.pair (.inLeft .unit) .lambda)
    (.cons (.pair (.inLeft .unit) .lambda) .nil))

private theorem sharedProgram_checked : sharedProgram.check = true := by
  simp [sharedProgram, Core.LocalSequence.letInitialized, Core.LocalSequence.discard,
    Core.OptionalCell.read, Core.OptionalCell.allocateInitialized, SourceCoreLocalPolymorphism.read,
    ProductBundle.expression,
    ProductBundle.type, bundleType, wordFunction, boolFunction, Core.TaggedFunction.call,
    Core.TaggedFunction.anonymous, countingClosure, readWord, readBool,
    Core.LanguageResult.success, Core.LanguageResult.failure, Core.LanguageResult.bind, Core.Expr.weakenAt, literal]
  decide

example (fuel : Nat) : (sharedProgram.runStateful fuel).HasType sharedProgram.resultType :=
  Core.Program.checked_runStateful_has_type sharedProgram_checked fuel

example (fuel additional : Nat) (checkpoint : Core.State)
    (exhausted : sharedProgram.runStateful fuel = .outOfFuel checkpoint) :
    Core.runStateful additional checkpoint = sharedProgram.runStateful (fuel + additional) :=
  Core.runStateful_resume exhausted additional

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"local bundle source rejected: {reprStr error}")
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 128 [.word, .bool] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"local bundle scalar catalog failed: {reprStr error}")
  let samePlan ← plan program [← request program "sameInnerType"]
  let same ← match prepare checked samePlan with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"contextual local bundle discovery failed: {reprStr error}")
  let outer ← binding same "outer"
  let inner ← binding same "inner"
  assertTrue (outer.instances.length == 2 && inner.instances.length == 2)
    "nested local instances were lost"
  match inner.instances with
  | [first, second] =>
      assertTrue (first.type == second.type && first.origin.substitution != second.origin.substitution)
        "equal final function types merged different outer contexts"
  | _ => throw (IO.userError "expected two nested contexts")
  for candidate in outer.instances do
    let active := candidate.origin.substitution
    assertTrue ((inner.atContext active).length == 1) "nested bundle selected another outer context"
    assertTrue (inner.bundleType active == wordFunction) "singleton contextual bundle changed its type"
    for id in references inner do discard <| checkRead inner same active id
    match lowerBinder same inner.caller active (inner.source.applySubstitution active) []
      (inner.binder.applySubstitution active) with
    | .ok payload => assertTrue (payload == wordFunction) "contextual binder payload mismatch"
    | .error error => throw (IO.userError s!"contextual binder metadata rejected: {reprStr error}")

  let dependentPlan ← plan program [← request program "dependentInner"]
  let dependent ← match prepare checked dependentPlan with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"dependent nested local metadata failed: {reprStr error}")
  let dependentOuter ← binding dependent "outer"
  let dependentInner ← binding dependent "inner"
  for candidate in dependentOuter.instances do
    let active := candidate.origin.substitution
    assertTrue ((dependentInner.atContext active).length == 1) "dependent inner lost its enclosing context"
    for id in references dependentInner do discard <| checkRead dependentInner dependent active id

  let sharedPlan ← plan program [← request program "sharedCapture", ← request program "sharedCapture"]
  let shared ← match prepare checked sharedPlan with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"shared local bundle discovery failed: {reprStr error}")
  let f ← binding shared "f"
  assertTrue (f.instances.length == 2 && f.bundleType [] == bundleType)
    "repeated same-type uses or duplicate roots duplicated local closures"
  let types ← (references f).mapM fun id => return (← checkRead f shared [] id).type
  assertTrue (types == [wordFunction, boolFunction, wordFunction]) "local read selected the wrong bundle ordinal"
  match lowerBinder shared f.caller [] f.source [] { f.binder with name := "forged" } with
  | .error (.bindingMetadataMismatch _) => pure ()
  | _ => throw (IO.userError "tampered generalized binder metadata was accepted")
  match lowerBinder shared f.caller [] f.source [(f.binder.id, bundleType)] f.binder with
  | .error (.metadata (.duplicateBinding _)) => pure ()
  | _ => throw (IO.userError "duplicate generalized binder scope was accepted")
  let firstRead ← match references f with
    | id :: _ => pure id
    | [] => throw (IO.userError "shared local lost its read occurrences")
  let tampered := { f.source with nodes := f.source.nodes.map fun
    | .expression node => .expression (if node.id == firstRead then { node with type := .bool } else node)
    | .statement node => .statement node }
  match lowerRead shared f.caller [] tampered [(f.binder.id, bundleType)] firstRead (word 31) with
  | .error (.bindingMetadataMismatch _) => pure ()
  | _ => throw (IO.userError "tampered local read bypassed the original scheme metadata")
  let total ← match f.source.nodes.findSome? fun
      | .statement { form := .letDecl binder _, .. } => if binder.name == "total" then some binder.id else none
      | _ => none with
    | some total => pure total
    | none => throw (IO.userError "shared source capture disappeared")
  for candidate in f.instances do
    assertTrue (candidate.origin.instantiatedBodyNodes.filterMap (fun
      | .statement { form := .assignValue assignment _ _, .. } => some assignment.target.root
      | _ => none) == [total]) "local instantiation changed the shared source reference identity"

  let unusedPlan ← plan program [← request program "unused"]
  let unused ← match prepare checked unusedPlan with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"unused local bundle failed: {reprStr error}")
  for binding in unused.bindings do
    assertTrue (binding.instances.isEmpty && binding.bundleType [] == .unit) "unused local requires a dummy function"
    match lowerInitializer binding [] (fun candidate => .error (.openInstance binding.binder.id candidate.origin.binder.scheme.body)) with
    | .ok lowered =>
        assertTrue (lowered.type == .unit && lowered.expression == Core.LanguageResult.success .unit)
          "empty local initializer invoked its closure compiler"
    | .error _ => throw (IO.userError "unused bundle attempted to compile a nonexisting instance")

  let qualifiedPlan ← plan program [← request program "qualified"]
  let qualified ← match prepare checked qualifiedPlan with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"qualified local metadata discovery failed: {reprStr error}")
  let qualifiedF ← binding qualified "f"
  assertTrue (qualifiedF.instances.length == 2 && !qualifiedF.binder.schemeRequirements.isEmpty)
    "local catalog discarded qualified template metadata"
  for candidate in qualifiedF.instances do
    assertTrue (candidate.origin.solvedRequirements ==
      (qualifiedPlan.specializations.find? (fun function => function.key == candidate.origin.caller) |>.map
        (·.function.solvedRequirements) |>.getD [])) "local catalog substituted the original evidence ledger"
  match prepare checked samePlan (some 0) with
  | .error (.discovery (.localPolymorphicContextFuelExhausted _)) => pure ()
  | _ => throw (IO.userError "bounded local instance discovery bypassed exhaustion")
  match prepare checked { samePlan with specializations := samePlan.specializations ++ samePlan.specializations } with
  | .error (.discovery (.duplicatePlanSpecializations _ 2)) => pure ()
  | _ => throw (IO.userError "duplicate enclosing specialization was accepted")

  assertTrue sharedProgram.check "shared instance bundle did not pass the Core checker"
  match sharedProgram.runStateful 65536 with
  | .done (.inRight .word (.word result)) store =>
      assertTrue (result == word 2 && store[0]? == some (.inRight .unit (.word (word 2))))
        "two closures did not mutate the same captured optional cell"
  | _ => throw (IO.userError "shared instance bundle execution failed")
  match sharedProgram.runStateful 2 with
  | .outOfFuel checkpoint =>
      assertTrue (Core.runStateful 65536 checkpoint == sharedProgram.runStateful 65538)
        "shared local bundle checkpoint changed execution"
  | _ => throw (IO.userError "shared local bundle did not suspend")
  IO.println "local polymorphism catalog, exact contexts and typed shared bundles GREEN"

end Tests.SourceCoreLocalPolymorphism
end

section
-- leanmerge: from Solcore.Test.SourceCoreLoops
/-! Checked source while/for fixtures execute generated Core. Native stores are
checked with explicit administrative-cell positions; source heap correspondence
for those extra cells is not assumed. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreLoops

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function whileCount(start: Word) returns (Word, Word) {",
    "  let remaining: Word = start; let count: Word = 0;",
    "  while (remaining > 0) { let copy: Word = remaining; remaining = remaining - 1; count = count + 1; }",
    "  return (remaining, count);",
    "}",
    "function forOrder(limit: Word) returns (Word, Word) {",
    "  let count: Word = 0;",
    "  for (let i: Word = 0; limit > i; i = i + 1) {",
    "    count = count + 1; if (i == 1) { continue; } count = count + 10;",
    "  } return (count, limit);",
    "}",
    "function forBreak(limit: Word) returns (Word) {",
    "  let count: Word = 0; for (let i: Word = 0; limit > i; i = i + 1) { count = count + 1; break; }",
    "  return count;",
    "}",
    "function initializerScope(limit: Word) returns (Word) {",
    "  let i: Word = 17; for (let i: Word = 0; limit > i; i = i + 1) { } return i;",
    "}",
    "function postScope(limit: Word) returns (Word) {",
    "  let copy: Word = 99;",
    "  for (let i: Word = 0; limit > i; let copy: Word = i, i = copy + 1) { } return copy;",
    "}",
    "function nested() returns (Word, Word) {",
    "  let outer: Word = 2; let count: Word = 0; while (outer > 0) {",
    "    let inner: Word = 2; while (inner > 0) {",
    "      inner = inner - 1; if (inner == 1) { continue; } count = count + 1; break;",
    "    } outer = outer - 1;",
    "  } return (count, outer);",
    "}",
    "function returnInside(limit: Word) returns (Word) {",
    "  let remaining: Word = limit; while (remaining > 0) { return remaining; } return 0;",
    "}",
    "function absentCondition() returns (Word) { let missing: Bool; while (missing) { return 17; } return 0; }",
    "function absentPost() returns (Word) { let missing: Word; for (let i: Word = 0; true; i = missing) { continue; } return 0; }",
    "function absentInitializer() returns (Word) { let missing: Word; for (let i: Word = missing; true; i = i + 1) { break; } return 0; }",
    "function spin() { while (true) { continue; } }",
    "function compound(limit: Word) { for (let i: Word = 0; limit > i; i += 1) { } }"
  ] }]
}

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction := do
  match program.functions.find? (fun function =>
    match program.environment.declaration? function.declaration with
    | some declaration => declaration.name == some name
    | none => false) with
  | some function => pure function
  | none => throw (IO.userError s!"missing loop fixture {name}")

private def roots (source : TypedSource) : IO (List StatementId) :=
  source.roots.mapM fun
    | .statement id => pure id
    | _ => throw (IO.userError "expected loop statement roots")

private def inputScope (source : TypedSource) : IO SourceCoreLoops.Scope :=
  source.inputs.foldlM (fun scope binder => do
    match SourceCoreBasic.lowerBinder source scope binder with
    | .ok type => pure ((binder.id, type) :: scope)
    | .error error => throw (IO.userError s!"loop input rejected: {reprStr error}")) []

private structure Compiled where
  function : CheckedFunction
  scope : SourceCoreLoops.Scope
  type : Core.Ty
  body : Core.Expr
  sites : SourceCoreFaultSites.Table

private def compile (function : CheckedFunction) (type : Core.Ty) : IO Compiled := do
  let scope ← inputScope function.typedBody
  let sites ← match SourceCoreFaultSites.prepare function.typedBody function.inferredBodyType with
    | .ok sites => pure sites
    | .error error => throw (IO.userError s!"loop fault table rejected: {reprStr error}")
  let body ← match SourceCoreLoops.lowerStatementsWithReasons 100
      ⟨function.solvedRequirements⟩ function.typedBody scope (← roots function.typedBody)
      type sites.reasonAt Core.Word.zero sites.escapedReason with
    | .ok body => pure body
    | .error error => throw (IO.userError s!"loop lowering rejected: {reprStr error}")
  assertTrue (decide (Core.infer? (SourceCoreLocalCell.coreContext scope) body =
    some (Core.LanguageResult.resultType type))) "generated loop body failed Core type checking"
  pure { function, scope, type, body, sites }

private def start (compiled : Compiled) (arguments : List Core.Value) : IO Core.State := do
  let inputs := compiled.scope.reverse
  assertTrue (inputs.length == arguments.length) "loop input arity mismatch"
  let store := arguments.map present
  let environment := (inputs.zipIdx.map fun ((_, type), index) =>
    Core.Value.cellRef (Core.OptionalCell.cellType type) index).reverse
  pure (.initial compiled.body environment store)

private def checkStore (compiled : Compiled) (store : Core.Store)
    (ordinary : List (Nat × Core.Value)) (administrative : List Nat) (length : Nat) : IO Unit := do
  assertTrue (store.length == length) "loop allocation count changed"
  for (index, expected) in ordinary do
    assertTrue (store[index]? == some expected) s!"loop binding at {index} changed"
  for index in administrative do
    match store[index]? with
    | some (.inRight .unit (.closure .unit _ _ captured)) =>
        assertTrue (captured[0]? == some
          (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType compiled.type)) index))
          "administrative closure lost its self reference"
    | _ => throw (IO.userError "expected installed optional-function cell")

private def expectSuccess (compiled : Compiled) (arguments : List Core.Value) (expected : Core.Value)
    (ordinary : List (Nat × Core.Value)) (administrative : List Nat) (length : Nat) : IO Unit := do
  let initial ← start compiled arguments
  match Core.runStateful 12000 initial with
  | .done (.inRight .word value) store =>
      assertTrue (value == expected) "loop result or control transfer changed"
      checkStore compiled store ordinary administrative length
      match Core.runStateful 50 initial with
      | .outOfFuel checkpoint =>
          assertTrue (Core.runStateful 11950 checkpoint == .done (.inRight .word expected) store)
            "loop checkpoint resumption changed result or shared heap"
      | _ => throw (IO.userError "loop fixture must retain a checkpoint at fuel 50")
  | result => throw (IO.userError s!"loop did not complete successfully: {reprStr result}")

private def testExecution (program : CheckedProgram) : IO Unit := do
  expectSuccess (← compile (← named program "whileCount") (.product .word .word)) [scalar 3]
    (.pair (scalar 0) (scalar 3))
    [(0, present (scalar 3)), (1, present (scalar 0)), (2, present (scalar 3)),
      (4, present (scalar 3)), (5, present (scalar 2)), (6, present (scalar 1))] [3] 7
  expectSuccess (← compile (← named program "forOrder") (.product .word .word)) [scalar 3]
    (.pair (scalar 23) (scalar 3))
    [(0, present (scalar 3)), (1, present (scalar 23)), (2, present (scalar 3))] [3] 4
  expectSuccess (← compile (← named program "forBreak") .word) [scalar 3] (scalar 1)
    [(0, present (scalar 3)), (1, present (scalar 1)), (2, present (scalar 0))] [3] 4
  expectSuccess (← compile (← named program "initializerScope") .word) [scalar 2] (scalar 17)
    [(0, present (scalar 2)), (1, present (scalar 17)), (2, present (scalar 2))] [3] 4
  expectSuccess (← compile (← named program "postScope") .word) [scalar 3] (scalar 99)
    [(0, present (scalar 3)), (1, present (scalar 99)), (2, present (scalar 3)),
      (4, present (scalar 0)), (5, present (scalar 1)), (6, present (scalar 2))] [3] 7
  expectSuccess (← compile (← named program "nested") (.product .word .word)) []
    (.pair (scalar 2) (scalar 0))
    [(0, present (scalar 0)), (1, present (scalar 2)), (3, present (scalar 0)), (5, present (scalar 0))]
    [2, 4, 6] 7
  expectSuccess (← compile (← named program "returnInside") .word) [scalar 3] (scalar 3)
    [(0, present (scalar 3)), (1, present (scalar 3))] [2] 3

private def testFailure (program : CheckedProgram) (name : String)
    (ordinary : List (Nat × Core.Value)) (administrative : List Nat) (length : Nat) : IO Unit := do
  let compiled ← compile (← named program name) .word
  let missing ← match compiled.sites.reads.find? (fun site =>
      compiled.function.typedBody.nodes.any fun
        | .expression node => node.id == site.expression &&
          match node.form with
          | .reference "missing" (.local _) => true
          | _ => false
        | _ => false) with
    | some site => pure site
    | none => throw (IO.userError "missing precise loop read site")
  match Core.runStateful 12000 (← start compiled []) with
  | .done (.inLeft .word (.word code)) store =>
      assertTrue (code == missing.reason) "loop failure lost the exact read reason"
      match compiled.sites.diagnostic? code with
      | some diagnostic =>
          assertTrue (diagnostic.error == .uninitializedLocal missing.binder &&
            diagnostic.site == .occurrence missing.expression.occurrence &&
            diagnostic.span == some missing.span) "loop failure diagnostic changed"
      | none => throw (IO.userError "missing loop failure diagnostic")
      checkStore compiled store ordinary administrative length
  | result => throw (IO.userError s!"loop failure not retained: {reprStr result}")

private def testBoundaries (program : CheckedProgram) : IO Unit := do
  let spin ← compile (← named program "spin") .unit
  match Core.runStateful 500 (← start spin []) with
  | .outOfFuel checkpoint =>
      match Core.runStateful 500 checkpoint with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError "resumed source spin should still suspend")
  | _ => throw (IO.userError "source spin should suspend without a machine fault")
  let compound ← named program "compound"
  let scope ← inputScope compound.typedBody
  match SourceCoreLoops.lowerStatements 100 ⟨compound.solvedRequirements⟩ compound.typedBody scope
      (← roots compound.typedBody) .unit (word 1) Core.Word.zero (word 2) with
  | .error (.unsupportedAssignmentOperator .add) => pure ()
  | result => throw (IO.userError s!"compound assignment profile changed: {reprStr result}")

private def preparedEntry (program : CheckedProgram) (name : String) :
    IO SourceCoreBasicEntry.Entry := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"prepared loop fixture missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program
      [{ declaration := signature.id, parameterSubstitution := [] }] 100 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"prepared loop worklist failed: {reprStr result}")
  let prepared ← match SourceCoreBasicEntry.prepare program plan 100 (word 91) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"prepared loop lowering failed: {reprStr error}")
  match prepared.entries with
  | [entry] => pure entry
  | _ => throw (IO.userError "prepared loop seed order changed")

private def invoke (entry : SourceCoreBasicEntry.Entry) (arguments : List Core.Value)
    (fuel : Nat := 12000) : IO (SourceCoreBasicEntry.Result entry.resultType) := do
  match entry.run arguments fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"prepared loop invocation rejected: {reprStr error}")

private def testPreparedEntry (program : CheckedProgram) : IO Unit := do
  for (name, arguments, expected, length) in ([
      ("forOrder", [scalar 3], Core.Value.pair (scalar 23) (scalar 3), 4),
      ("initializerScope", [scalar 2], scalar 17, 4),
      ("nested", [], .pair (scalar 2) (scalar 0), 7)] :
      List (String × List Core.Value × Core.Value × Nat)) do
    let entry ← preparedEntry program name
    let completed ← invoke entry arguments
    match completed.observation with
    | .succeeded value store =>
        assertTrue (value == expected && store.length == length)
          "prepared loop changed scope, result or administrative allocations"
    | result => throw (IO.userError s!"prepared loop failed: {reprStr result}")
    let paused ← invoke entry arguments 50
    let checkpoint ← match paused.checkpoint? with
      | some checkpoint => pure checkpoint
      | none => throw (IO.userError "prepared loop must retain a typed checkpoint")
    assertTrue ((checkpoint.resume 11950).observation == completed.observation)
      "prepared loop resumption changed result or shared heap"
  let order ← preparedEntry program "forOrder"
  match (← invoke order [scalar 2]).observation with
  | .succeeded value store =>
      assertTrue (value == .pair (scalar 12) (scalar 2) &&
        store[0]? == some (present (scalar 2)) && store[2]? == some (present (scalar 2)))
        "reusing prepared loop code must allocate a fresh invocation frame"
  | result => throw (IO.userError s!"prepared loop reuse failed: {reprStr result}")
  for name in ["absentCondition", "absentPost", "absentInitializer"] do
    let entry ← preparedEntry program name
    let function ← named program name
    let missing ← match entry.faultSites.reads.find? (fun site =>
        function.typedBody.nodes.any fun
          | .expression node => node.id == site.expression &&
            match node.form with
            | .reference "missing" (.local _) => true
            | _ => false
          | _ => false) with
      | some site => pure site
      | none => throw (IO.userError "prepared loop lost its precise failing read")
    match (← invoke entry []).observation with
    | .failed token _ =>
        assertTrue (token == missing.reason) "prepared loop failure lost its reason"
        assertTrue (decide (entry.failureDiagnostic? token = some {
            error := .uninitializedLocal missing.binder,
            site := .occurrence missing.expression.occurrence, span := some missing.span }))
          "prepared loop failure lost its source binder, occurrence or span"
    | result => throw (IO.userError s!"prepared loop did not retain failure: {reprStr result}")
  let spin ← preparedEntry program "spin"
  let suspended ← invoke spin [] 500
  match suspended.checkpoint? with
  | some checkpoint =>
      match (checkpoint.resume 500).checkpoint? with
      | some _ => pure ()
      | none => throw (IO.userError "resumed prepared spin must still suspend")
  | none => throw (IO.userError "prepared spin must suspend without an internal fault")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"loop source fixtures failed checking: {reprStr errors}")
  testExecution program
  testFailure program "absentCondition" [(0, .inLeft .bool .unit)] [1] 2
  testFailure program "absentPost" [(0, .inLeft .word .unit), (1, present (scalar 0))] [2] 3
  testFailure program "absentInitializer" [(0, .inLeft .word .unit)] [] 1
  testBoundaries program
  testPreparedEntry program

end Tests.SourceCoreLoops
end

section
-- leanmerge: from Solcore.Test.SourceCorePrimitive
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCorePrimitive

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value

private def wordOperators : List (String × String) := [
  ("mul", "*"), ("divide", "/"), ("modulo", "%"), ("add", "+"), ("sub", "-"),
  ("band", "&"), ("bxor", "^"), ("bor", "|")]
private def comparisons : List (String × String) := [
  ("gt", ">"), ("eq", "==")]

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" (
    (wordOperators.map fun (name, operator) =>
      s!"function {name}(left: Word, right: Word) returns (Word)" ++ " { return left " ++ operator ++ " right; }") ++
    (comparisons.map fun (name, operator) =>
      s!"function {name}(left: Word, right: Word) returns (Bool)" ++ " { return left " ++ operator ++ " right; }") ++ [
    "function conjunction(left: Bool, right: Bool) returns (Bool) { return left && right; }",
    "function disjunction(left: Bool, right: Bool) returns (Bool) { return left || right; }",
    "function negation(input: Bool) returns (Bool) { return !input; }",
    "function complement(input: Word) returns (Word) { return ~input; }",
    "function literal() returns (Word) { return 17; }",
    "function hugeLiteral() returns (Word) { return " ++ toString (Core.wordModulus + 5) ++ "; }",
    "function nested(flag: Bool, value: Word) returns (Word, Bool) {",
    "  return ((flag ? value + 2 : value * 3), (!flag || (value > 0)));",
    "}",
    "function builtin() returns (Word) { return wordFromInteger(1); }",
    "function lt(left: Word, right: Word) returns (Bool) { return right > left; }",
    "function lessCall(left: Word, right: Word) returns (Bool) { return left < right; }"
  ]) }]
}

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction := do
  match program.functions.find? (fun function =>
      match program.environment.declaration? function.declaration with
      | some declaration => declaration.name == some name
      | none => false) with
  | some function => pure function
  | none => throw (IO.userError s!"missing primitive fixture {name}")

private def returned (source : TypedSource) : IO ExpressionId := do
  match source.nodes.findSome? fun
    | .statement node => match node.form with
      | .returnStmt (some expression) => some expression
      | _ => none
    | _ => none with
  | some id => pure id
  | none => throw (IO.userError "primitive fixture must return an expression")

private def inputScope (source : TypedSource) : IO SourceCoreBasic.Scope :=
  source.inputs.foldlM (fun scope binder => do
    match SourceCoreBasic.lowerBinder source scope binder with
    | .ok type => pure ((binder.id, type) :: scope)
    | .error error => throw (IO.userError s!"primitive input rejected: {reprStr error}")) []

private structure Compiled where
  function : CheckedFunction
  scope : SourceCoreBasic.Scope
  lowered : SourceCoreBasic.LoweredExpr
  sites : SourceCoreFaultSites.Table

private def compile (function : CheckedFunction) : IO Compiled := do
  let scope ← inputScope function.typedBody
  let sites ← match SourceCoreFaultSites.prepare function.typedBody function.inferredBodyType with
    | .ok sites => pure sites
    | .error error => throw (IO.userError s!"primitive diagnostic preparation rejected: {reprStr error}")
  let lowered ← match SourceCorePrimitive.lowerExpressionWithReasons 100
      { solvedRequirements := function.solvedRequirements } function.typedBody scope
      (← returned function.typedBody) sites.reasonAt with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError s!"primitive lowering rejected: {reprStr error}")
  assertTrue (decide (Core.infer? (SourceCoreLocalCell.coreContext scope) lowered.expression =
      some (Core.LanguageResult.resultType lowered.type))) "primitive body failed the Core checker"
  pure { function, scope, lowered, sites }

private def execute (compiled : Compiled) (arguments : List (Option Core.Value)) :
    IO Core.LanguageResult.Observation := do
  let inputs := compiled.scope.reverse
  assertTrue (inputs.length == arguments.length) "primitive fixture arity mismatch"
  let store := (inputs.zip arguments).map fun ((_, type), value) =>
    match value with
    | some value => present value
    | none => Core.Value.inLeft type .unit
  let environment := (inputs.zipIdx.map fun ((_, type), index) =>
    Core.Value.cellRef (Core.OptionalCell.cellType type) index).reverse
  pure (Core.LanguageResult.observeResult (Core.runStateful 1000
    (.initial compiled.lowered.expression environment store)))

private def expectSuccess (compiled : Compiled) (arguments : List Core.Value) (expected : Core.Value) : IO Unit := do
  assertTrue ((← execute compiled (arguments.map some)) == .succeeded expected (arguments.map present))
    "primitive execution changed its result or input store"

/-- Some comparison spellings elaborate to named calls. Exercise the primitive
IR constructors directly without reinterpreting those user-selected calls. -/
private def primitiveComparison (program : CheckedProgram) (operator : Syntax.BinaryOp) : IO Compiled := do
  let function ← named program "gt"
  let id ← returned function.typedBody
  let source := { function.typedBody with nodes := function.typedBody.nodes.map fun
    | .expression node =>
        if node.id = id then match node.form with
          | .binary left _ right => .expression { node with form := .binary left operator right }
          | _ => .expression node
        else .expression node
    | node => node }
  compile { function with typedBody := source }

private def testOperators (program : CheckedProgram) : IO Unit := do
  for (name, expected) in ([
      ("mul", 42), ("divide", 1), ("modulo", 1), ("add", 13), ("sub", 1),
      ("band", 6), ("bxor", 1), ("bor", 7)] : List (String × Nat)) do
    expectSuccess (← compile (← named program name)) [scalar 7, scalar 6] (scalar expected)
  for (name, expected) in [("gt", true), ("eq", false)] do
    expectSuccess (← compile (← named program name)) [scalar 7, scalar 6] (.bool expected)
  for (operator, different, equal) in ([
      (.greater, true, false), (.equal, false, true), (.less, false, false),
      (.lessEqual, false, true), (.greaterEqual, true, true), (.notEqual, true, false)] :
      List (Syntax.BinaryOp × Bool × Bool)) do
    let compiled ← primitiveComparison program operator
    expectSuccess compiled [scalar 7, scalar 6] (.bool different)
    expectSuccess compiled [scalar 6, scalar 6] (.bool equal)
  expectSuccess (← compile (← named program "add")) [scalar (Core.wordModulus - 1), scalar 1] (scalar 0)
  expectSuccess (← compile (← named program "sub")) [scalar 0, scalar 1] (scalar (Core.wordModulus - 1))
  for name in ["divide", "modulo"] do
    expectSuccess (← compile (← named program name)) [scalar 9, scalar 0] (scalar 0)
  expectSuccess (← compile (← named program "complement")) [scalar 0] (scalar (Core.wordModulus - 1))
  expectSuccess (← compile (← named program "negation")) [.bool true] (.bool false)
  expectSuccess (← compile (← named program "literal")) [] (scalar 17)
  expectSuccess (← compile (← named program "hugeLiteral")) [] (scalar 5)
  let nested ← compile (← named program "nested")
  expectSuccess nested [.bool true, scalar 4] (.pair (scalar 6) (.bool true))
  expectSuccess nested [.bool false, scalar 4] (.pair (scalar 12) (.bool true))

private def localSite (compiled : Compiled) (inputIndex : Nat) : IO SourceCoreFaultSites.ReadSite := do
  let binder ← match compiled.function.typedBody.inputs[inputIndex]? with
    | some binder => pure binder
    | none => throw (IO.userError "missing primitive input binder")
  match compiled.sites.reads.find? (fun site => decide (site.binder = binder.id)) with
  | some site => pure site
  | none => throw (IO.userError "missing primitive local-read reason")

private def testFailureOrder (program : CheckedProgram) : IO Unit := do
  let add ← compile (← named program "add")
  let left ← localSite add 0
  let right ← localSite add 1
  assertTrue ((← execute add [none, none]) ==
      .failed left.reason [.inLeft .word .unit, .inLeft .word .unit])
    "strict operator evaluated the right operand after left failure"
  assertTrue ((← execute add [some (scalar 3), none]) ==
      .failed right.reason [present (scalar 3), .inLeft .word .unit])
    "strict operator lost the right operand's failure site"
  for (name, shortValue, evaluatingValue) in [("conjunction", false, true), ("disjunction", true, false)] do
    let compiled ← compile (← named program name)
    let left ← localSite compiled 0
    let right ← localSite compiled 1
    assertTrue ((← execute compiled [some (.bool shortValue), none]) ==
        .succeeded (.bool shortValue) [present (.bool shortValue), .inLeft .bool .unit])
      "Boolean short circuit evaluated its uninitialized right operand"
    assertTrue ((← execute compiled [some (.bool evaluatingValue), none]) ==
        .failed right.reason [present (.bool evaluatingValue), .inLeft .bool .unit])
      "Boolean right operand failed without its occurrence reason"
    assertTrue ((← execute compiled [none, none]) ==
        .failed left.reason [.inLeft .bool .unit, .inLeft .bool .unit])
      "Boolean left failure did not stop the operator"

private def replaceNode (source : TypedSource) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : TypedSource := {
  source with nodes := source.nodes.map fun
    | .expression node => if node.id = id then .expression (change node) else .expression node
    | node => node
}

private def testBoundaries (program : CheckedProgram) : IO Unit := do
  let function ← named program "literal"
  let source := function.typedBody
  let id ← returned source
  let node ← match source.lookupExpression? id with
    | some node => pure node
    | none => throw (IO.userError "literal node missing")
  let (literal, resolution) ← match node.form with
    | .integerLiteral literal resolution => pure (literal, resolution)
    | _ => throw (IO.userError "parsed literal no longer carries evidence")
  let solved ← match function.solvedRequirements with
    | [solved] => pure solved
    | _ => throw (IO.userError "literal must retain exactly one solved obligation")
  let lower (source : TypedSource) (requirements : List SolvedRequirement) :=
    SourceCorePrimitive.lowerExpression 100 { solvedRequirements := requirements } source [] id Core.Word.zero
  let expectRejected (label : String) (source : TypedSource) (requirements : List SolvedRequirement)
      (accepts : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
    match lower source requirements with
    | .error (.literalEvidence error) =>
        assertTrue (accepts error.reason) s!"{label}: wrong evidence rejection {reprStr error}"
    | result => throw (IO.userError s!"{label}: forged literal metadata accepted or misclassified {reprStr result}")
  expectRejected "missing evidence" source [] fun error => error matches .missingIntegerLiteralRequirement _
  expectRejected "duplicate evidence" source [solved, solved] fun error => error matches .duplicateIntegerLiteralRequirements _ 2
  expectRejected "assumed evidence" source [{ solved with evidence := .assumption solved.predicate }]
    fun error => error matches .unresolvedIntegerLiteralEvidence _
  expectRejected "wrong implementation" source [{ solved with
      evidence := .implementation (.byImpl solved.predicate (.builtin .intInteger) []) }]
    fun error => error matches .integerLiteralImplementationMismatch _ _ _
  expectRejected "evidence premises" source [{ solved with
      evidence := .implementation (.byImpl solved.predicate (.builtin .intWord)
        [.byImpl solved.predicate (.builtin .intWord) []]) }]
    fun error => error matches .integerLiteralPremiseCountMismatch _ 0 1
  expectRejected "raw spelling mismatch" (replaceNode source id fun node => {
      node with form := .integerLiteral literal { resolution with rawValue := 18 } }) [solved]
    fun error => error matches .integerLiteralRawValueMismatch 17 18
  expectRejected "missing attachment" (replaceNode source id fun node => { node with requirements := [] }) [solved]
    fun error => error matches .integerLiteralRequirementsMismatch _ _
  expectRejected "changed target" (replaceNode source id fun node => {
      node with form := .integerLiteral literal { resolution with targetType := .bool } }) [solved]
    fun error => error matches .integerLiteralTargetTypeMismatch _ _
  expectRejected "malformed spelling" (replaceNode source id fun node => {
      node with form := .integerLiteral (.decimal "17x") resolution }) [solved]
    fun error => error matches .invalidIntegerLiteralSource _
  let wrongPredicate := ProgramSignatures.builtinIntPredicate .bool
  expectRejected "wrong predicate" source [{ solved with predicate := wrongPredicate }]
    fun error => error matches .integerLiteralPredicateMismatch _ _ _
  expectRejected "wrong evidence goal" source [{ solved with
      evidence := .implementation (.byImpl wrongPredicate (.builtin .intWord) []) }]
    fun error => error matches .integerLiteralEvidenceGoalMismatch _ _ _
  let strictOverflow := replaceNode source id fun node => {
    node with requirements := [], form := .literal (.decimal (toString (Core.wordModulus + 5)))
  }
  match lower strictOverflow [] with
  | .error (.invalidWordLiteral _ _) => pure ()
  | result => throw (IO.userError s!"strict compatibility Word literal silently used modulo: {reprStr result}")
  let add ← named program "add"
  let addId ← returned add.typedBody
  let scope ← inputScope add.typedBody
  let ordinary (source : TypedSource) := SourceCorePrimitive.lowerExpression 100
    { solvedRequirements := [] } source scope addId Core.Word.zero
  match ordinary (replaceNode add.typedBody addId fun node => { node with requirements := [resolution.requirement] }) with
  | .error (.requirementsPresent _) => pure ()
  | result => throw (IO.userError s!"required operator silently became a builtin: {reprStr result}")
  match ordinary (replaceNode add.typedBody addId fun node => { node with type := .bool }) with
  | .error (.typeMismatch _ .word .bool) => pure ()
  | result => throw (IO.userError s!"operator result profile was not checked: {reprStr result}")
  match ordinary (replaceNode add.typedBody addId fun node => match node.form with
      | .binary left _ right => { node with form := .binary left .logicalAnd right, type := .bool }
      | _ => node) with
  | .error (.typeMismatch _ .bool .word) => pure ()
  | result => throw (IO.userError s!"operator input profile was not checked: {reprStr result}")
  let builtin ← named program "builtin"
  match SourceCorePrimitive.lowerExpression 100 { solvedRequirements := builtin.solvedRequirements }
      builtin.typedBody [] (← returned builtin.typedBody) Core.Word.zero with
  | .error (.unsupportedExpression _ (.call ..)) => pure ()
  | result => throw (IO.userError s!"Integer builtin escaped the current primitive boundary: {reprStr result}")
  let call ← named program "lessCall"
  match SourceCorePrimitive.lowerExpression 100 { solvedRequirements := call.solvedRequirements }
      call.typedBody (← inputScope call.typedBody) (← returned call.typedBody) Core.Word.zero with
  | .error (.unsupportedExpression _ (.call _ _ (.declaration _))) => pure ()
  | result => throw (IO.userError s!"comparison spelling silently bypassed its selected function: {reprStr result}")

private def testHelperStores : IO Unit := do
  let writeThen (value : Nat) (result : Core.Expr) : Core.Expr :=
    .letE (.storeCell (.var 0) (.word (word value))) result
  let left := writeThen 1 (Core.LanguageResult.success (.word (word 7)))
  let right : Core.Expr := .letE (.loadCell (.var 0))
    (.letE (.storeCell (.var 1) (.word (word 2))) (Core.LanguageResult.success (.var 1)))
  let check (type : Core.Ty) (body : Core.Expr) (expected : Core.LanguageResult.Observation) : IO Unit := do
    let program : Core.Program := {
      resultType := Core.LanguageResult.resultType type
      body := .letE (.newCell .word (.word (word 0))) body
    }
    assertTrue program.check "primitive helper fixture did not typecheck"
    assertTrue (Core.LanguageResult.run program 1000 == expected)
      "primitive helper changed shared store evaluation order"
  check .word (Core.LocalPrimitiveResults.binary .wordAdd left right) (.succeeded (scalar 8) [scalar 2])
  let failLeft := writeThen 1 (Core.LanguageResult.failure .word (.word (word 31)))
  check .word (Core.LocalPrimitiveResults.binary .wordAdd failLeft right) (.failed (word 31) [scalar 1])
  let failRight := writeThen 2 (Core.LanguageResult.failure .word (.word (word 32)))
  check .word (Core.LocalPrimitiveResults.binary .wordAdd left failRight) (.failed (word 32) [scalar 2])
  let falseLeft := writeThen 1 (Core.LanguageResult.success (.bool false))
  let trueRight := writeThen 2 (Core.LanguageResult.success (.bool true))
  check .bool (Core.LocalPrimitiveResults.logicalAnd falseLeft trueRight) (.succeeded (.bool false) [scalar 1])
  let trueLeft := writeThen 1 (Core.LanguageResult.success (.bool true))
  check .bool (Core.LocalPrimitiveResults.logicalOr trueLeft trueRight) (.succeeded (.bool true) [scalar 1])

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"primitive source checking failed: {reprStr errors}")
  testOperators program
  testFailureOrder program
  testBoundaries program
  testHelperStores

end Tests.SourceCorePrimitive
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveEntry
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreRecursiveEntry

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreRecursiveEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function countdown(n: Word) returns (Word) { return n == 0 ? n : countdown(n - 1); }",
    "function even(n: Word) returns (Bool) { return n == 0 ? true : odd(n - 1); }",
    "function odd(n: Word) returns (Bool) { return n == 0 ? false : even(n - 1); }",
    "function positive(n: Word) returns (Bool) { return n > 0; }",
    "function decrement(n: Word) returns (Word) { return n - 1; }",
    "function spin() returns (Word) { return spin(); }",
    "function sumDown(n: Word) returns (Word) {",
    "  let total: Word = 0; while (positive(n)) { total = total + n; n = decrement(n); } return total;",
    "}",
    "function useLoop(n: Word) returns (Word) { return sumDown(n) + 1; }",
    "function zero() returns (Word) { return 7; }",
    "function increment(value: Word) returns (Word) { let next: Word = value + 1; return next; }",
    "function combine(a: Word, b: Word, c: Word) returns (Word) { return a + b + c; }",
    "function nested(value: Word) returns (Word) { return combine(zero(), increment(value), value) * 2; }",
    "function echoProduct(value: (Word, Bool)) returns (Word, Bool) { return value; }",
    "function productCall(value: Word) returns (Word, Bool) { return echoProduct((value, true)); }",
    "function failLeft() returns (Word) { let absent: Word; return absent; }",
    "function failRight() returns (Word) { let absent: Word; return absent; }",
    "function add(left: Word, right: Word) returns (Word) { return left + right; }",
    "function chooseFailure(flag: Bool) returns (Word) { return flag ? add(failLeft(), failRight()) : add(1, failRight()); }",
    "function leftValue() returns (Word) { let mark: Word = 31; return mark; }",
    "function rightValue() returns (Word) { let mark: Word = 47; return mark; }",
    "function ordered() returns (Word) { return add(leftValue(), rightValue()); }",
    "function empty() { }",
    "function staged(comptime value: Word) returns (Word) { return value; }",
    "function stagedResult(value: Word) returns (comptime<Word>) { return 1; }"
  ] }]
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"missing recursive-entry fixture {name}")

private def plan (program : CheckedProgram) (names : List String) : IO Plan := do
  let requests ← names.mapM (request program)
  match SourceSpecializationWorklist.run program requests 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"recursive-entry plan failed: {reprStr result}")

private def prepared (program : CheckedProgram) (names : List String) : IO PreparedProgram := do
  let input ← plan program names
  match prepare program input 100 Core.Word.zero with
  | .ok program => pure program
  | .error error => throw (IO.userError s!"recursive-entry preparation failed: {reprStr error}")

private def firstEntry (prepared : PreparedProgram) : IO Entry :=
  match prepared.entries with
  | entry :: _ => pure entry
  | [] => throw (IO.userError "missing prepared entry")

private def execute (entry : Entry) (arguments : List Core.Value) (fuel : Nat := 20000) :
    IO (SourceCoreBasicEntry.Result entry.resultType) := do
  match entry.run arguments fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"prepared invocation rejected: {reprStr error}")

private def success (entry : Entry) (arguments : List Core.Value) (expected : Core.Value) : IO Core.Store := do
  match (← execute entry arguments).observation with
  | .succeeded value store =>
      assertTrue (value == expected) "recursive entry changed its returned value"
      pure store
  | result => throw (IO.userError s!"recursive entry did not succeed: {reprStr result}")

private def testRecursion (program : CheckedProgram) : IO Unit := do
  let selfProgram ← prepared program ["countdown"]
  let selfEntry ← firstEntry selfProgram
  let store ← success selfEntry [scalar 4] (scalar 0)
  assertTrue (store.drop (selfEntry.inputs.length + selfProgram.plan.specializations.length) ==
      [present (scalar 4), present (scalar 3), present (scalar 2), present (scalar 1), present (scalar 0)])
    "recursive source parameters were not allocated in invocation order"
  -- The same checked code is reused for another invocation.
  discard <| success selfEntry [scalar 1] (scalar 0)
  let suspended ← execute selfEntry [scalar 6] 10
  let checkpoint ← match suspended.checkpoint? with
    | some checkpoint => pure checkpoint
    | none => throw (IO.userError "recursive entry did not suspend on small fuel")
  let resumed := checkpoint.resume 20000
  let uninterrupted ← execute selfEntry [scalar 6] 20010
  assertTrue (resumed.observation == uninterrupted.observation) "checkpoint resumption changed the exact result/store"
  let mutualProgram ← prepared program ["even", "odd", "even"]
  assertTrue (mutualProgram.entries.length == 3) "duplicate seed order was lost"
  for (index, input, expected) in [(0, 4, true), (1, 4, false), (2, 3, false)] do
    let entry ← match mutualProgram.entries[index]? with
      | some entry => pure entry
      | none => throw (IO.userError "mutual seed missing")
    let store ← success entry [scalar input] (.bool expected)
    assertTrue (store.length == entry.inputs.length + mutualProgram.plan.specializations.length + input + 1)
      "mutual recursion changed its shared parameter store"

  let diverging ← firstEntry (← prepared program ["spin"])
  let suspended ← execute diverging [] 100
  match suspended.checkpoint? with
  | some checkpoint =>
      match (checkpoint.resume 100).observation with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError "unbounded recursion was incorrectly completed")
  | none => throw (IO.userError "unbounded recursion was not represented by a typed checkpoint")

private def testCallsAndLoops (program : CheckedProgram) : IO Unit := do
  let loopEntry ← firstEntry (← prepared program ["useLoop"])
  discard <| success loopEntry [scalar 4] (scalar 11)
  discard <| success loopEntry [scalar 0] (scalar 1)
  let nestedProgram ← prepared program ["nested"]
  let nestedEntry ← firstEntry nestedProgram
  let store ← success nestedEntry [scalar 4] (scalar 32)
  assertTrue (store.drop (nestedEntry.inputs.length + nestedProgram.plan.specializations.length) ==
      [present (scalar 4), present (scalar 4), present (scalar 5),
       present (scalar 7), present (scalar 5), present (scalar 4)])
    "zero/one/three argument calls or mutable local allocation order changed"
  let productProgram ← prepared program ["productCall"]
  let productEntry ← firstEntry productProgram
  let store ← success productEntry [scalar 8] (.pair (scalar 8) (.bool true))
  assertTrue (store.drop (productEntry.inputs.length + productProgram.plan.specializations.length) ==
      [present (scalar 8), present (.pair (scalar 8) (.bool true))])
    "one product argument was split into two parameter cells"
  let orderedProgram ← prepared program ["ordered"]
  let orderedEntry ← firstEntry orderedProgram
  let store ← success orderedEntry [] (scalar 78)
  assertTrue (store.drop orderedProgram.plan.specializations.length ==
      [present (scalar 31), present (scalar 47), present (scalar 31), present (scalar 47)])
    "arguments or callee parameters were not evaluated/allocated in source order"
  let emptyEntry ← firstEntry (← prepared program ["empty"])
  discard <| success emptyEntry [] .unit

private def testDiagnostics (program : CheckedProgram) : IO Unit := do
  let compiled ← prepared program ["chooseFailure"]
  let entry ← firstEntry compiled
  let mut reasons : List Core.Word := []
  for (flag, name) in [(true, "failLeft"), (false, "failRight")] do
    let declaration := (← request program name).declaration
    match (← execute entry [.bool flag]).observation with
    | .failed reason store =>
        let site ← match entry.faultSites.reads.find? (fun site => decide (site.binder.owner = declaration)) with
          | some site => pure site
          | none => throw (IO.userError "callee diagnostic occurrence missing")
        assertTrue (reason == site.reason) "callee failure used another function's token"
        assertTrue (decide (entry.failureDiagnostic? reason = some {
          error := .uninitializedLocal site.binder
          site := .occurrence site.expression.occurrence
          span := some site.span
        })) "callee failure lost its exact binder, occurrence, or span"
        assertTrue (store.drop (entry.inputs.length + compiled.plan.specializations.length) ==
          [present (.bool flag), .inLeft .word .unit])
          "failed argument evaluated another callee or allocated add parameters"
        reasons := reason :: reasons
    | result => throw (IO.userError s!"callee uninitialized read did not fail: {reprStr result}")
  assertTrue (reasons.length == 2 && reasons[0]? != reasons[1]?) "distinct callee failures reused one diagnostic token"
  assertTrue (decide (entry.failureDiagnostic? (word 100000) = none)) "unknown failure token acquired a source location"

private def testBoundaries (program : CheckedProgram) : IO Unit := do
  for name in ["staged", "stagedResult"] do
    let input ← plan program [name]
    match prepare program input 100 Core.Word.zero with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "staged function entered the ordinary recursive profile")
  let input ← plan program ["countdown"]
  match prepare program { input with callEdges := [] } 100 Core.Word.zero with
  | .error (.preparation _) => pure ()
  | _ => throw (IO.userError "noncanonical recursive plan escaped preparation")
  match prepare program input 0 Core.Word.zero with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "compilation traversal fuel was ignored")
  let entry ← firstEntry (← prepared program ["countdown"])
  for arguments in [[], [.bool true]] do
    match entry.run arguments 100 with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "recursive entry accepted malformed inputs")
  match entry.run [scalar 1] 100 [scalar 9] with
  | .error (.initialStoreUnsupported 1) => pure ()
  | _ => throw (IO.userError "recursive entry silently consumed an unsupported initial store")
  let emptyPlan ← plan program []
  match prepare program emptyPlan 100 Core.Word.zero with
  | .ok prepared => assertTrue prepared.entries.isEmpty "empty seed plan created an entry"
  | .error error => throw (IO.userError s!"empty seed plan rejected: {reprStr error}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"recursive source fixtures failed: {reprStr errors}")
  testRecursion program
  testCallsAndLoops program
  testDiagnostics program
  testBoundaries program

end Tests.SourceCoreRecursiveEntry
end

section
-- leanmerge: from Solcore.Test.SourceCoreSession
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.RuntimeValue
#check_failure Solcore.Frontend.SourceCoreSession.Handle.mk
#check_failure Solcore.Frontend.SourceCoreSession.Session.mk
#check_failure Solcore.Frontend.SourceCoreSession.Recipe.mk
#check_failure Solcore.Frontend.SourceCoreSession.Session.store
#check_failure Solcore.Frontend.SourceCoreSession.Checkpoint.state
#check_failure Solcore.Frontend.SourceCoreSession.register
#check_failure Solcore.Frontend.SourceCoreSession.Value.closure
#check_failure Solcore.Frontend.SourceCoreSession.Value.cellRef
#check_failure Solcore.Frontend.SourceCoreSession.Handle.artifact

set_option autoImplicit false

namespace Tests.SourceCoreSession

open Solcore Solcore.Frontend SourceCoreSession

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Value := .word (Core.Word.ofNatModulo value)
private def functionType : TypeSystem.Ty := .function .word .word

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Holder { Put(function(Word) returns (Word)) }",
    "enum Branch { Leaf(function(Word) returns (Word)), Pair(Branch, Branch) }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function make(value: Word) returns (function(Word) returns (Word)) {",
    " return lam(delta: Word) -> Word { value = value + delta; return inc(value); }; }",
    "function twins(value: Word) returns (function(Word) returns (Word), function(Word) returns (Word)) {",
    " let f: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; };",
    " let g: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; }; return (f, g); }",
    "function use(f: function(Word) returns (Word), delta: Word) returns (Word) { return f(delta); }",
    "function mirror(f: function(Word) returns (Word)) returns (function(Word) returns (Word)) { return f; }",
    "function named() returns (function(Word) returns (Word)) { return inc; }",
    "function boxed(f: function(Word) returns (Word)) returns (Holder) { return .Put(f); }",
    "function echoBox(value: Holder) returns (Holder) { return value; }",
    "function unbox(value: Holder) returns (function(Word) returns (Word)) { match (value) { case .Put(f) { return f; } } }",
    "function echoMap(value: mapping(Word => function(Word) returns (Word))) returns (mapping(Word => function(Word) returns (Word))) { return value; }",
    "function fromMap(value: mapping(Word => function(Word) returns (Word)), key: Word) returns (function(Word) returns (Word)) { return value[key]; }",
    "function echoPair(value: (Word, function(Word) returns (Word))) returns (Word, function(Word) returns (Word)) { return value; }",
    "function failurePair(value: Word) returns (function(Word) returns (Word), function() returns (Word)) {",
    " let f: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; let absent: Word; return absent; };",
    " let g: function() returns (Word) = lam() -> Word { return value; }; return (f, g); }",
    "function get(f: function() returns (Word)) returns (Word) { return f(); }"
    , "function proxyWord() returns (@Word) { return @Word; }"
    , "function echoBranch(value: Branch) returns (Branch) { return value; }"
  ] }] }

private def plan (program : CheckedProgram) : IO SourceSpecializationWorklist.Plan :=
  match SourceSpecializationWorklist.run program
      (program.signatures.functions.map fun signature => { declaration := signature.id, parameterSubstitution := [] }) 256 with
  | .ok (.complete plan) => pure plan
  | other => throw (IO.userError s!"session specialization failed: {reprStr other}")

private def prepare (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan) : IO Artifact := do
  match ← Artifact.prepareAutomatic program plan 256 with
  | .ok artifact => pure artifact
  | .error error => throw (IO.userError s!"session automatic catalog compilation failed: {reprStr error}")

private def keyFor (artifact : Artifact) (program : CheckedProgram) (name : String) : IO Key := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"session fixture function missing: {name}")
  match artifact.keys.find? fun key => decide (key.declaration = signature.id) with
  | some key => pure key
  | none => throw (IO.userError s!"session artifact omitted root: {name}")

private def execute {artifact : Artifact} (session : Session artifact) (key : Key)
    (arguments : List Value) (fuel : Nat := 65536) : IO (Completion artifact) := do
  match ← session.run key arguments fuel with
  | .error error => throw (IO.userError s!"session input rejected: {reprStr error}")
  | .ok (.succeeded completion) => pure completion
  | .ok (.failed reason _) => throw (IO.userError s!"session language failure: {reprStr reason}")
  | .ok (.exportError error _) => throw (IO.userError s!"session export rejected: {reprStr error}")
  | .ok (.outOfFuel _) => throw (IO.userError "session fixture exhausted fuel")

private def reject {artifact : Artifact} (session : Session artifact) (type : TypeSystem.Ty)
    (value : Value) (fuel : Nat := 1024) : IO Error :=
  match session.authenticate fuel type value with
  | .error error => pure error
  | .ok _ => throw (IO.userError "session accepted a forged or foreign value")

example {artifact : Artifact} (completion : Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value := completion.typed
example {artifact : Artifact} {session : Session artifact} {fuel : Nat} {type : TypeSystem.Ty} {value : Value}
    (certificate : Authentication session fuel type value) : session.Authenticates fuel type value := certificate.typed
example {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat) : checkpoint.NativeSafe fuel :=
  checkpoint.native_safe fuel
example {artifact : Artifact} {checkpoint next : Checkpoint artifact} {spent : Nat}
    (exhausted : checkpoint.suspend? spent = some next) (additional : Nat) :
    checkpoint.NativeResumes next spent additional := Checkpoint.suspend?_fuel_resume exhausted additional

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"session source rejected: {reprStr error}")
  let plan ← plan program
  let recipe ← match Recipe.prepareAutomatic program plan 256 with
    | .ok recipe => pure recipe
    | .error error => throw (IO.userError s!"session recipe rejected: {reprStr error}")
  assertTrue (recipe.program.entries.length == program.signatures.functions.length) "cached recipe omitted roots"
  let artifact ← recipe.open
  let key := keyFor artifact program
  let initial ← artifact.newSession
  assertTrue (initial.heapSize == 0 && initial.functionCount == 0) "fresh session is not empty"
  let made ← execute initial (← key "make") [word 10]
  assertTrue (made.session.functionCount == 1 && made.session.heapSize > 0) "returned closure was not privately registered"
  let first ← execute made.session (← key "use") [made.value, word 2]
  assertTrue (first.value == word 13 && first.session.heapSize > made.session.heapSize)
    "owned closure lost its old global references or captured value during world extension"
  let second ← execute first.session (← key "use") [made.value, word 3]
  assertTrue (second.value == word 14) "reused closure did not restart from its captured value"
  let mirrored ← execute second.session (← key "mirror") [made.value]
  assertTrue (mirrored.value == made.value && mirrored.session.functionCount == 1)
    "function export did not reuse the exact existing handle"
  let identity : Session artifact → Value → Option FunctionIdentity := fun session value => match value with
    | .function handle => session.functionIdentity? handle
    | _ => none
  assertTrue (identity mirrored.session made.value == some .anonymous) "anonymous function identity tag changed"
  let named ← execute mirrored.session (← key "named") []
  let same ← execute named.session (← key "named") []
  assertTrue ((match identity named.session named.value with | some (.named _) => true | _ => false) &&
      identity same.session same.value == identity named.session named.value)
    "named function identity tag changed between exports"

  let otherSession ← artifact.newSession
  assertTrue ((← reject otherSession functionType made.value).code == .foreignSession)
    "another fresh session accepted an owned function"
  let otherArtifact ← recipe.open
  let other ← otherArtifact.newSession
  assertTrue ((← reject other functionType made.value).code == .foreignArtifact)
    "another artifact accepted an owned function"
  let branchA ← execute initial (← key "make") [word 1]
  let branchB ← execute initial (← key "make") [word 1]
  assertTrue (branchA.value != branchB.value) "branched immutable sessions reused an export token"
  assertTrue ((← reject branchB.session functionType branchA.value).code == .unknownHandle)
    "a branch accepted another branch's colliding slot"
  assertTrue ((← reject made.session (.function .unit .word) made.value).code ==
      .handleTypeMismatch (.function .unit .word) functionType) "wrong function type was accepted"
  let foreignPair := Value.product (word 7) made.value
  let error ← reject otherSession (.product .word functionType) foreignPair
  assertTrue (error.path == [.productRight] && error.code == .foreignSession) "deep handle ownership path changed"

  let twins ← execute same.session (← key "twins") [word 20]
  let (left, right) ← match twins.value with
    | .product left right => pure (left, right)
    | _ => throw (IO.userError "shared closure product changed shape")
  let leftResult ← execute twins.session (← key "use") [left, word 2]
  let rightResult ← execute leftResult.session (← key "use") [right, word 3]
  assertTrue (leftResult.value == word 22 && rightResult.value == word 23)
    "closures created together shared a captured cell instead of each keeping its own value"
  let paired := Value.product (word 9) right
  let pairEcho ← execute rightResult.session (← key "echoPair") [paired]
  assertTrue (pairEcho.value == paired) "deep function product roundtrip changed its handle"
  let boxed ← execute pairEcho.session (← key "boxed") [right]
  let boxEcho ← execute boxed.session (← key "echoBox") [boxed.value]
  assertTrue (boxEcho.value == boxed.value) "nominal function payload roundtrip changed metadata or handle"
  let unboxed ← execute boxEcho.session (← key "unbox") [boxEcho.value]
  assertTrue (unboxed.value == right) "nominal matcher changed the owned function"
  let (metadata, payloads) ← match boxed.value with
    | .constructed metadata payloads => pure (metadata, payloads)
    | _ => throw (IO.userError "nominal owned result changed shape")
  let forged := Value.constructed { metadata with payloadTypes := [.word] } payloads
  assertTrue ((← reject unboxed.session metadata.resultType forged).code != .unknownHandle)
    "forged constructor payload metadata was accepted"
  let forged := Value.constructed { metadata with parameterSubstitution := [(⟨metadata.constructor.dataType, 0⟩, .word)] } payloads
  let _ ← reject unboxed.session metadata.resultType forged
  let forged := Value.constructed { metadata with constructor := { metadata.constructor with constructorIndex := 99 } } payloads
  let _ ← reject unboxed.session metadata.resultType forged
  let foreignBox := Value.constructed metadata [made.value]
  let error ← reject otherSession metadata.resultType foreignBox
  assertTrue (error.path == [.constructorPayload 0] && error.code == .foreignSession)
    "nominal payload did not deeply authenticate its function owner"
  let branch ← match program.signatures.dataTypes.filter (·.name == "Branch") with
    | [branch] => pure branch
    | _ => throw (IO.userError "recursive session data signature missing")
  let branchType := TypeSystem.Ty.nominal branch.id []
  let leafMetadata : SourceInference.DataConstructorInstantiation := ⟨⟨branch.id, 0⟩, [], [functionType], branchType⟩
  let pairMetadata : SourceInference.DataConstructorInstantiation := ⟨⟨branch.id, 1⟩, [], [branchType, branchType], branchType⟩
  let leaf := Value.constructed leafMetadata [right]
  let nested := (List.range 20).foldl (fun value _ => .constructed pairMetadata [value, leaf]) leaf
  let recursive ← execute unboxed.session (← key "echoBranch") [nested]
  assertTrue (recursive.value == nested) "recursive nominal function payload roundtrip changed"
  let mapping := Value.mapping .word functionType [(word 7, left), (word 7, right), (word 2, named.value)]
  let mapEcho ← execute unboxed.session (← key "echoMap") [mapping]
  assertTrue (mapEcho.value == mapping) "ordered mapping function payloads were sorted or deduplicated"
  let selected ← execute mapEcho.session (← key "fromMap") [mapping, word 7]
  assertTrue (selected.value == left) "duplicate mapping keys changed first-match function identity"
  let error ← reject otherSession (.mapping .word functionType) mapping
  assertTrue (error.path == [.mappingValue 0] && error.code == .foreignSession) "mapping function owner was not checked"
  let error ← reject selected.session (.mapping .word functionType) (.mapping .integer functionType [])
  assertTrue (error.code == .data (.mappingMetadataMismatch .word functionType .integer functionType))
    "mapping source metadata forgery was accepted"
  assertTrue ((← reject selected.session (.proxy .word) (.proxy .integer)).code ==
      .data (.proxyIdentityMismatch .word .integer)) "proxy raw inner identity forgery was accepted"
  assertTrue ((← reject selected.session (.product .word functionType) paired 1).code == .data .exhausted)
    "deep validation ignored its fuel bound"

  let failedPair ← execute selected.session (← key "failurePair") [word 30]
  let (failing, getter) ← match failedPair.value with
    | .product failing getter => pure (failing, getter)
    | _ => throw (IO.userError "failure pair changed shape")
  let failedSession ← match ← failedPair.session.run (← key "use") [failing, word 4] 65536 with
    | .ok (.failed _ session) => pure session
    | _ => throw (IO.userError "language failure did not retain the owned heap")
  let afterFailure ← execute failedSession (← key "get") [getter]
  assertTrue (afterFailure.value == word 30) "a write before a language failure reached another closure's captured value"

  let checkpoint ← match afterFailure.session.start (← key "use") [right, word 1] with
    | .ok checkpoint => pure checkpoint
    | .error error => throw (IO.userError s!"typed session checkpoint rejected: {reprStr error}")
  let next ← match ← checkpoint.resume 2 with
    | .outOfFuel next => pure next
    | _ => throw (IO.userError "small fuel did not retain a typed session checkpoint")
  let resumed ← match ← next.resume 65536 with
    | .succeeded completion => pure completion
    | _ => throw (IO.userError "typed session resume failed")
  let direct ← match ← checkpoint.resume 65538 with
    | .succeeded completion => pure completion
    | _ => throw (IO.userError "typed session combined fuel failed")
  assertTrue (resumed.value == word 21 && direct.value == resumed.value && direct.session.heapSize == resumed.session.heapSize)
    "resume changed the captured value or heap extension"
  assertTrue ((resumed.session.authenticate 1024 functionType right).isOk)
    "checkpoint world extension invalidated an existing owned handle"
  let pureNext ← match checkpoint.suspend? 2 with
    | some next => pure next
    | none => throw (IO.userError "pure native checkpoint observation did not retain exhaustion")
  let pureResumed ← match ← pureNext.resume 65536 with
    | .succeeded completion => pure completion
    | _ => throw (IO.userError "pure suspension checkpoint failed to resume")
  assertTrue (pureResumed.value == resumed.value) "pure and IO checkpoint paths diverged"
  let exportSession ← match ← pureResumed.session.run (← key "named") [] 65536 0 with
    | .ok (.exportError error session) =>
        assertTrue (error.code == .data .exhausted) "bounded export changed its error"
        pure session
    | _ => throw (IO.userError "zero export fuel did not retain the certified native heap")
  let afterExportError ← execute exportSession (← key "use") [right, word 1]
  assertTrue (afterExportError.value == word 21) "export failure invalidated existing handles or their captured values"
  let factoryArtifact ← prepare program plan
  let factorySession ← factoryArtifact.newSession
  assertTrue ((← reject factorySession functionType right).code == .foreignArtifact)
    "automatic artifact factory reused an existing ownership token"
  IO.println "source Core owned function sessions GREEN"

end Tests.SourceCoreSession
end
