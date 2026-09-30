import Solcore.SourceSemantics.CoreLowering.ForStatementCorrespondence

/-! An actual accepted nested for with continue and post yields an independent
source trace from Core completion alone. The numerical runner regression also
checks the post update and both allocated loop self cells. -/

set_option autoImplicit false

namespace Tests.SourceCoreForStatementReflection

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"for_loop_certificate", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def binder : TypedBinder := { id := ⟨owner, 0⟩, name := "flag", scheme := .mono .bool }
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "for_loop_certificate.solc" }, startByte := 0, endByte := 1 }
private def trueNode : ExpressionNode := { id := exprId 0, span := span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def falseNode : ExpressionNode := { id := exprId 1, span := span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def readNode : ExpressionNode := { id := exprId 2, span := span, type := .bool, form := .reference "flag" (.local binder.id) }
private def assignment : AssignmentResolution := { target := { root := binder.id, projections := [], type := .bool } }
private def outer : StatementNode := {
  id := stmtId 3, span := span, type := .unit,
  form := .forLoop [.letDecl binder (some (exprId 0))] (exprId 2)
    [.assignValue assignment .equal (exprId 1)] [stmtId 4, stmtId 5] }
private def inner : StatementNode := {
  id := stmtId 4, span := span, type := .unit,
  form := .forLoop [] (exprId 1) [] [] }
private def continuing : StatementNode := { id := stmtId 5, span := span, type := .unit, form := .continueStmt }
private def source : TypedSource := {
  owner := owner,
  nodes := [.expression trueNode, .expression falseNode, .expression readNode,
    .statement outer, .statement inner, .statement continuing],
  roots := [], inputs := [] }
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def context : SourceSemantics.Context := Context.ofSignatures signatures
private def reason : Core.Word := Core.Word.ofNatModulo 73

private def loopBody : Core.Expr := Core.LocalLoop.sequence .unit
  (Core.LocalLoop.iterate .unit (Core.LanguageResult.success (.bool false))
    (Core.LocalLoop.fallthrough .unit) (Core.LocalLoop.fallthrough .unit) reason)
  (Core.LocalLoop.continuing .unit)
private def post : Core.Expr := Core.LocalSequence.assign (Core.LocalLoop.controlType .unit)
  (.var 0) (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.fallthrough .unit)
private def flow : Core.Expr := Core.LocalLoop.sequence .unit
  (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType .unit) .bool
    (Core.LanguageResult.success (.bool true))
    (Core.LocalLoop.iterate .unit (Core.OptionalCell.read .bool (.var 0) reason) loopBody post reason))
  (Core.LocalLoop.fallthrough .unit)
private def code : Core.Expr := Core.LocalControl.finish .unit
  (Core.LocalLoop.toControl .unit flow reason) (Core.LanguageResult.success .unit)

private theorem accepted : SourceCoreLoops.lowerStatementsWithReasons 20 compilation source []
    [stmtId 3] .unit (fun _ => reason) reason reason = .ok code := by rfl

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- The successful compiler result determines the tree and all body, post,
initializer and nested-loop typing obligations. No execution is supplied. -/
example : ∃ loweredFlow,
    code = Core.LocalControl.finish .unit (Core.LocalLoop.toControl .unit loweredFlow reason)
      (Core.LanguageResult.success .unit) ∧
    LoopStatements.WithFor.Tree compilation source (fun _ => reason) reason [] context
      (.statements true [stmtId 3]) .unit loweredFlow ∧
    Core.HasType [] loweredFlow (Core.LocalLoop.resultType .unit) := by
  obtain ⟨loweredFlow, equation, tree⟩ := LoopStatements.WithFor.tree_of_lowerStatements
    (BasicStatements.ScopeContextAligned.empty signatures) unique accepted
  exact ⟨loweredFlow, equation, tree, tree.hasType .unit⟩

private theorem valid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.ofSignatures] at impossible

/-- No source execution or child execution premise is supplied. -/
example (program : Program) {fuel : Nat} {result : Core.Value} {finalStore : Core.Store}
    (completed : Core.runStateful fuel (.initial code [] []) = .done result finalStore) :
    LoopStatements.Reflection.FinishedResult program context [] source (fun _ => reason) reason reason
      [] ⟨[]⟩ [stmtId 3] .unit [] [] [] result finalStore :=
  LoopStatements.WithFor.lowerStatements_run_reflects
    (BasicStatements.ScopeContextAligned.empty signatures) unique accepted .unit valid
    (GeneralHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil)
    GeneralHeap.HeapRepresents.empty completed

/-- Both finite directions are available at the same actual compiler boundary. -/
example (program : Program) :
    (∃ fuel result finalStore, Core.runStateful fuel (.initial code [] []) = .done result finalStore) ↔
    (∃ finalContext outcome after, Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩
      [stmtId 3] finalContext outcome after) := by
  have covers : Dynamic.EvidenceEnvironment.Covers context [] := by
    constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [context, Context.ofSignatures] at member
  exact LoopStatements.WithFor.lowerStatements_finite_iff
    (BasicStatements.ScopeContextAligned.empty signatures) unique accepted .unit valid covers
    (GeneralHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil)
    GeneralHeap.HeapRepresents.empty

private def administrative : Core.Value := .closure .unit .unit .unit []
private theorem administrativeHeap : GeneralHeap.HeapRepresents [] [.function .unit .unit] ⟨[]⟩ [administrative] :=
  GeneralHeap.HeapRepresents.empty.allocate_administrative (Core.RuntimeValueHasType.closure .nil .unit)

/-- The first source allocation maps to Core location 1 when an unrelated
administrative closure already occupies location 0. -/
example (program : Program) {fuel : Nat} {result : Core.Value} {finalStore : Core.Store}
    (completed : Core.runStateful fuel (.initial code [] [administrative]) = .done result finalStore) :
    LoopStatements.Reflection.FinishedResult program context [] source (fun _ => reason) reason reason
      [] ⟨[]⟩ [stmtId 3] .unit [] [.function .unit .unit] [administrative] result finalStore :=
  LoopStatements.WithFor.lowerStatements_run_reflects
    (BasicStatements.ScopeContextAligned.empty signatures) unique accepted .unit valid
    (GeneralHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil) administrativeHeap completed

private def scenario (initializers : List ForItemForm) (condition : ExpressionId)
    (postItems : List ForItemForm) (bodyForm : StatementForm) : TypedSource := {
  source with nodes := [.expression trueNode, .expression falseNode, .expression readNode,
    .statement { outer with form := .forLoop initializers condition postItems [stmtId 5] },
    .statement inner, .statement { continuing with form := bodyForm }] }

private def checkScenario (label : String) (input : TypedSource) (expected : Core.Value)
    (cells : Nat) (firstCell : Core.Value) : IO Unit := do
  let lowered ← match SourceCoreLoops.lowerStatementsWithReasons 20 compilation input [] [stmtId 3]
      .unit (fun _ => reason) reason reason with
    | .ok code => pure code
    | .error _ => throw (IO.userError s!"{label}: lowering failed")
  match Core.runStateful 1000 (.initial lowered [] []) with
  | .done result store =>
      unless result == expected && store.length == cells && store[0]? == some firstCell do
        throw (IO.userError s!"{label}: wrong language outcome or cell effects")
  | _ => throw (IO.userError s!"{label}: did not complete")

def run : IO Unit := do
  match Core.runStateful 1000 (.initial code [] []) with
  | .done result store =>
      unless result == .inRight .word .unit do
        throw (IO.userError "nested for did not finish with Unit")
      unless store[0]? == some (.inRight .unit (.bool false)) && store.length == 3 do
        throw (IO.userError "for continue skipped post or nested loop self-cell allocation")
  | _ => throw (IO.userError "nested for did not complete")
  match Core.runStateful 1000 (.initial code [] [administrative]) with
  | .done result store =>
      unless result == .inRight .word .unit && store.length == 4 &&
          store[0]? == some administrative && store[1]? == some (.inRight .unit (.bool false)) do
        throw (IO.userError "for loop changed the administrative cell or used a source index as a Core index")
  | _ => throw (IO.userError "for loop with an administrative prefix did not complete")
  let initialized := [ForItemForm.letDecl binder (some (exprId 0))]
  let uninitialized := [ForItemForm.letDecl binder none]
  let update := [ForItemForm.assignValue assignment .equal (exprId 1)]
  let succeeds := Core.Value.inRight .word .unit
  let fails := Core.Value.inLeft .unit (.word reason)
  checkScenario "fallthrough executes post"
    (scenario initialized (exprId 2) update (.block [])) succeeds 2 (.inRight .unit (.bool false))
  checkScenario "break skips post"
    (scenario initialized (exprId 2) update .breakStmt) succeeds 2 (.inRight .unit (.bool true))
  checkScenario "return skips post"
    (scenario initialized (exprId 2) update (.returnStmt none)) succeeds 2 (.inRight .unit (.bool true))
  checkScenario "continue reaches post fault"
    (scenario uninitialized (exprId 0) [.expression (exprId 2)] .continueStmt) fails 2 (.inLeft .bool .unit)
  checkScenario "fallthrough reaches post fault"
    (scenario uninitialized (exprId 0) [.expression (exprId 2)] (.block [])) fails 2 (.inLeft .bool .unit)
  checkScenario "initializer fault precedes self installation"
    (scenario (uninitialized ++ [.expression (exprId 2)]) (exprId 0) [] .breakStmt) fails 1 (.inLeft .bool .unit)
  checkScenario "condition fault retains installed self"
    (scenario uninitialized (exprId 2) [] .breakStmt) fails 2 (.inLeft .bool .unit)

end Tests.SourceCoreForStatementReflection
