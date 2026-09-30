import Solcore.Frontend.SourceCorePrimitive
import Solcore.Frontend.SourceCoreFaultSites

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
