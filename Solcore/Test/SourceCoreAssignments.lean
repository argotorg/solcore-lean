import Solcore.Frontend.SourceCoreAssignments
import Solcore.Frontend.SourceCorePrimitive

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
