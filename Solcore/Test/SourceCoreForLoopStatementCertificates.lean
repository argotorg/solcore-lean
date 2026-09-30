import Solcore.SourceSemantics.CoreLowering.ForLoopStatementCertificates

/-! Actual nested `for` acceptance supplies the complete static tree without
the old `NoForLoops` restriction. This test checks extraction and Core typing;
the runner check is a regression, not a whole-loop source preservation proof. -/

set_option autoImplicit false

namespace Tests.SourceCoreForLoopStatementCertificates

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

def run : IO Unit := do
  match Core.runStateful 1000 (.initial code [] []) with
  | .done result store =>
      unless result == .inRight .word .unit do
        throw (IO.userError "nested for did not finish with Unit")
      unless store[0]? == some (.inRight .unit (.bool false)) && store.length == 3 do
        throw (IO.userError "for continue skipped post or nested loop self-cell allocation")
  | _ => throw (IO.userError "nested for did not complete")

end Tests.SourceCoreForLoopStatementCertificates
