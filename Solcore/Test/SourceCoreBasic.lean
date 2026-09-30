import Solcore.Frontend.SourceCoreBasic
import Solcore.Core.BoundedSafety

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
