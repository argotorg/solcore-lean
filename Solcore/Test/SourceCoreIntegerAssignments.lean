import Solcore.Frontend.SourceCoreAssignments
import Solcore.Frontend.SourceCoreFunctionTypes
import Solcore.Frontend.SourceCoreAssignmentFaultSites
import Solcore.Frontend.SourceCoreAssignmentPolicy

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
