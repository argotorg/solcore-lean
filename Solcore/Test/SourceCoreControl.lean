import Solcore.Frontend.SourceCoreControl
import Solcore.Core.BoundedSafety

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
