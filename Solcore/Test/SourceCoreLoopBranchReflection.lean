import Solcore.SourceSemantics.CoreLowering.LoopBranchReflection

/-! Focused scoped-head reverse tests. Compiler acceptance supplies the guard
tree; child reconstruction uses primitive list helpers. The concrete tests
supply only Core executions and represented initial state. -/

set_option autoImplicit false

namespace Tests.SourceCoreLoopBranchReflection

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open LoopStatements LoopStatements.Reflection

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"branch_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId : ExpressionId := ⟨⟨owner, 0⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 1⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "branch_reflection.solc" }, startByte := 0, endByte := 1 }
private def guardNode (flag : Bool) : ExpressionNode := {
  id := exprId, span, type := .bool, form := .reference "flag" (.builtinBoolean flag) }
private def breakNode : StatementNode := { id := stmtId 1, span, type := .unit, form := .breakStmt }
private def continueNode : StatementNode := { id := stmtId 2, span, type := .unit, form := .continueStmt }
private def blockNode : StatementNode := { id := stmtId 3, span, type := .unit, form := .block [stmtId 1] }
private def ifNode (withElse : Bool) : StatementNode := {
  id := stmtId 0, span, type := .unit,
  form := .ifThen exprId [stmtId 1] (if withElse then some [stmtId 2] else none) }
private def source (flag withElse : Bool) : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0), .statement (stmtId 3)],
  nodes := [.expression (guardNode flag), .statement (ifNode withElse),
    .statement breakNode, .statement continueNode, .statement blockNode] }
private def reason : Core.Word := Core.Word.ofNatModulo 17
private def reasonAt (_ : ExpressionId) : Core.Word := reason
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def context : SourceSemantics.Context := Context.ofSignatures signatures
private def code (flag withElse : Bool) : Core.Expr :=
  Core.LocalLoop.conditional .unit (Core.LanguageResult.success (.bool flag))
    (Core.LocalLoop.breaking .unit)
    (if withElse then Core.LocalLoop.continuing .unit else Core.LocalLoop.fallthrough .unit)

private theorem contains_if (flag withElse : Bool) :
    ContainsStatement (source flag withElse) (stmtId 0) (ifNode withElse) := by
  simp [ContainsStatement, source, ifNode]
private theorem contains_break (flag withElse : Bool) :
    ContainsStatement (source flag withElse) (stmtId 1) breakNode := by
  simp [ContainsStatement, source, breakNode]
private theorem contains_continue (flag withElse : Bool) :
    ContainsStatement (source flag withElse) (stmtId 2) continueNode := by
  simp [ContainsStatement, source, continueNode]
private theorem contains_block (flag withElse : Bool) :
    ContainsStatement (source flag withElse) (stmtId 3) blockNode := by
  simp [ContainsStatement, source, blockNode]

private theorem if_reflects (flag withElse : Bool) (program : Program)
    (evidence : Dynamic.EvidenceEnvironment) :
    ScopedReflects compilation program evidence (source flag withElse) reasonAt [] context
      (stmtId 0) .unit (code flag withElse) := by
  have unique : NodeOccurrencesUnique (source flag withElse) := by
    unfold NodeOccurrencesUnique nodeOccurrenceIds
    cases flag <;> cases withElse <;> decide
  have accepted : SourceCorePrimitive.lowerExpressionWithReasons 1 compilation (source flag withElse)
      [] exprId reasonAt = .ok ⟨.bool, Core.LanguageResult.success (.bool flag)⟩ := by rfl
  obtain ⟨depth, _, guardTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique accepted
  have breaking : Reflects compilation program evidence (source flag withElse) reasonAt [] context
      false [stmtId 1] .unit (Core.LocalLoop.breaking .unit) :=
    reflects_breaking (contains_break flag withElse) (show breakNode.form = .breakStmt from rfl)
    (program := program) (evidence := evidence) (context := context) (compilation := compilation)
    (reasonAt := reasonAt) (scope := []) (mode := false) (rest := []) (type := .unit)
  cases withElse with
  | false =>
    change ScopedReflects _ _ _ _ _ _ _ _ _
      (Core.LocalLoop.conditional .unit (Core.LanguageResult.success (.bool flag))
        (Core.LocalLoop.breaking .unit) (Core.LocalLoop.fallthrough .unit))
    exact reflects_if_head (contains_if flag false) rfl guardTree breaking
      (reflects_nil compilation program evidence (source flag false) reasonAt [] context false .unit)
  | true =>
    change ScopedReflects _ _ _ _ _ _ _ _ _
      (Core.LocalLoop.conditional .unit (Core.LanguageResult.success (.bool flag))
        (Core.LocalLoop.breaking .unit) (Core.LocalLoop.continuing .unit))
    exact reflects_if_head (contains_if flag true) rfl guardTree breaking
      (reflects_continuing (contains_continue flag true) rfl)

/-- Block restoration uses the child list's reconstructed break outcome. -/
example (flag withElse : Bool) (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ScopedReflects compilation program evidence (source flag withElse) reasonAt [] context
      (stmtId 3) .unit (Core.LocalLoop.breaking .unit) :=
  reflects_block_head (contains_block flag withElse) rfl
    (reflects_breaking (contains_break flag withElse) rfl)

private theorem valid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.ofSignatures] at impossible
private theorem layout : Layout [] [] [] [] [] Core.Renaming.id := by
  refine ⟨?_, ?_, .nil⟩
  · intro index type found; cases found
  · intro index value found; cases found

private theorem reconstruct (flag withElse : Bool) (program : Program)
    (evidence : Dynamic.EvidenceEnvironment) {result : Core.Value}
    (evaluated : Core.Evaluates [] [] (code flag withElse) result []) :
    ScopedResult program context evidence (source flag withElse) reasonAt [] ⟨[]⟩ (stmtId 0)
      .unit [] [] [] result [] := by
  apply if_reflects flag withElse program evidence Core.Ty.WellFormed.unit valid
    (GeneralHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil)
    GeneralHeap.HeapRepresents.empty layout
  simpa only [Core.Expr.rename_id] using evaluated

/-- True chooses break even when an else branch exists. -/
example (withElse : Bool) (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ScopedResult program context evidence (source true withElse) reasonAt [] ⟨[]⟩ (stmtId 0)
      .unit [] [] [] (Core.LocalLoop.breakingValue .unit) [] := by
  apply reconstruct true withElse program evidence
  exact Core.LocalControl.choose_true (Core.LocalLoop.controlType .unit)
    (.inRight .bool) (by simp [Core.LocalLoop.breaking, Core.LanguageResult.success, Core.Expr.weakenAt]; exact .inRight (.inRight (.inLeft .unit)))

/-- An absent else reconstructs the source's false-without-else rule. -/
example (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ScopedResult program context evidence (source false false) reasonAt [] ⟨[]⟩ (stmtId 0)
      .unit [] [] [] (Core.LocalLoop.fallthroughValue .unit) [] := by
  apply reconstruct false false program evidence
  exact Core.LocalControl.choose_false (Core.LocalLoop.controlType .unit)
    (.inRight .bool) (by simp [Core.LocalLoop.fallthrough, Core.LanguageResult.success, Core.Expr.weakenAt]; exact .inRight (.inLeft (.inLeft .unit)))

/-- A present else reconstructs continue and restores the enclosing scope. -/
example (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ScopedResult program context evidence (source false true) reasonAt [] ⟨[]⟩ (stmtId 0)
      .unit [] [] [] (Core.LocalLoop.continuingValue .unit) [] := by
  apply reconstruct false true program evidence
  exact Core.LocalControl.choose_false (Core.LocalLoop.controlType .unit)
    (.inRight .bool) (by simp [Core.LocalLoop.continuing, Core.LanguageResult.success, Core.Expr.weakenAt]; exact .inRight (.inRight (.inRight .unit)))

end Tests.SourceCoreLoopBranchReflection
