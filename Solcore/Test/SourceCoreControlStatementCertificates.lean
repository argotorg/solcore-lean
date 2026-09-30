import Solcore.SourceSemantics.CoreLowering.ControlStatementCertificates

/-! Actual control compiler acceptance supplies the complete tree. These
fixtures cover both branch shapes, block scope, early return, and both tail
conventions without constructing or assuming any child Tree/evaluation. -/

set_option autoImplicit false

namespace Tests.SourceCoreControlStatementCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"control_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "local", scheme := .mono .word }
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "control_certificates.solc" }, startByte := 0, endByte := 1 }
private def expressionNode (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := exprId index, span, type, form }
private def statementNode (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : Node :=
  .statement { id := stmtId index, span, type, form }
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (id : ExpressionId) : Core.Word := word (id.occurrence.index + 50)
private def fellThrough : Core.Word := word 99
private def context : SourceSemantics.Context := .ofSignatures {
  functions := [], implRules := [], traits := [], implementations := [] }
private theorem aligned : BasicStatements.ScopeContextAligned [] context :=
  BasicStatements.ScopeContextAligned.empty _
private def statements : List StatementId := [stmtId 0, stmtId 1, stmtId 5]

/-- A branch can return the inner local; its scope is restored before the
outer implicit return. An absent else falls through. -/
private def source (flag withElse : Bool) : TypedSource := {
  owner, inputs := [], roots := statements.map .statement
  nodes := [
    expressionNode 0 .word (.literal (.decimal "7")),
    expressionNode 1 .word (.literal (.decimal "9")),
    expressionNode 2 .bool (.reference "flag" (.builtinBoolean flag)),
    expressionNode 3 .word (.reference "inner" (.local (binder 1).id)),
    expressionNode 4 .word (.reference "outer" (.local (binder 0).id)),
    expressionNode 5 .word (.reference "outer" (.local (binder 0).id)),
    statementNode 0 .unit (.letDecl (binder 0) (some (exprId 0))),
    statementNode 1 .word (.block [stmtId 2, stmtId 3]),
    statementNode 2 .unit (.letDecl (binder 1) (some (exprId 1))),
    statementNode 3 .word (.ifThen (exprId 2) [stmtId 4]
      (if withElse then some [stmtId 6] else none)),
    statementNode 4 .word (.returnStmt (some (exprId 3))),
    statementNode 5 .word (.expression (exprId 4) false),
    statementNode 6 .word (.returnStmt (some (exprId 5)))
  ]
}

private def flow (flag withElse : Bool) : Core.Expr :=
  Core.LocalSequence.letInitialized (Core.LocalControl.controlType .word) .word
    (Core.LanguageResult.success (.word (word 7)))
    (Core.LocalControl.sequence .word
      (Core.LocalSequence.letInitialized (Core.LocalControl.controlType .word) .word
        (Core.LanguageResult.success (.word (word 9)))
        (Core.LocalControl.sequence .word
          (Core.LocalControl.conditional .word (Core.LanguageResult.success (.bool flag))
            (Core.LocalControl.returnValue .word (Core.OptionalCell.read .word (.var 0) (reasonAt (exprId 3))))
            (if withElse then Core.LocalControl.returnValue .word
              (Core.OptionalCell.read .word (.var 1) (reasonAt (exprId 5)))
             else Core.LocalControl.fallthrough .word))
          (Core.LocalControl.fallthrough .word)))
      (Core.LocalControl.returnValue .word (Core.OptionalCell.read .word (.var 0) (reasonAt (exprId 4)))))

private theorem unique (flag withElse : Bool) : NodeOccurrencesUnique (source flag withElse) := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  cases flag <;> cases withElse <;> decide

private theorem accepted (flag withElse : Bool) :
    SourceCoreControl.lowerFlowStatementsWithReasons 20 (source flag withElse) [] statements .word
      reasonAt true = .ok (flow flag withElse) := by
  cases withElse <;> rfl

example (flag withElse : Bool) : ControlStatements.Tree (source flag withElse) reasonAt [] context true
    statements .word (flow flag withElse) :=
  ControlStatements.tree_of_lowerFlowStatements aligned (unique flag withElse) (accepted flag withElse)

example (flag withElse : Bool) : Core.HasType [] (flow flag withElse) (Core.LocalControl.resultType .word) :=
  (ControlStatements.tree_of_lowerFlowStatements aligned (unique flag withElse) (accepted flag withElse)).hasType .word

private def code (flag withElse : Bool) : Core.Expr :=
  Core.LocalControl.finish .word (flow flag withElse) (Core.LanguageResult.failure .word (.word fellThrough))

example (flag withElse : Bool) :
    ∃ compiledFlow, code flag withElse = Core.LocalControl.finish .word compiledFlow
      (Core.LanguageResult.failure .word (.word fellThrough)) ∧
      ControlStatements.Tree (source flag withElse) reasonAt [] context true statements .word compiledFlow := by
  apply ControlStatements.tree_of_lowerStatements aligned (unique flag withElse)
  change (do
    let compiledFlow ← SourceCoreControl.lowerFlowStatementsWithReasons 20 (source flag withElse) []
      statements .word reasonAt true
    pure (Core.LocalControl.finish .word compiledFlow (Core.LanguageResult.failure .word (.word fellThrough)))) = _
  rw [accepted]
  rfl

private def tailSource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [expressionNode 0 .word (.literal (.decimal "7")),
    statementNode 0 .word (.expression (exprId 0) false)] }
private theorem tailUnique : NodeOccurrencesUnique tailSource := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- A nested final expression is discarded; the function tail returns it. -/
example : ControlStatements.Tree tailSource reasonAt [] context false [stmtId 0] .word
    (Core.LocalSequence.discard (Core.LocalControl.controlType .word)
      (Core.LanguageResult.success (.word (word 7))) (Core.LocalControl.fallthrough .word)) :=
  ControlStatements.tree_of_lowerFlowStatements (fuel := 2) aligned tailUnique (by rfl)

example : ControlStatements.Tree tailSource reasonAt [] context true [stmtId 0] .word
    (Core.LocalControl.returnValue .word (Core.LanguageResult.success (.word (word 7)))) :=
  ControlStatements.tree_of_lowerFlowStatements (fuel := 2) aligned tailUnique (by rfl)

example : ControlStatements.Tree tailSource reasonAt [] context false [] .word
    (Core.LocalControl.fallthrough .word) :=
  ControlStatements.tree_of_lowerFlowStatements (fuel := 0) aligned tailUnique (by rfl)

private def earlySource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [statementNode 0 .unit (.returnStmt none)] }
example : ControlStatements.Tree earlySource reasonAt [] context true [stmtId 0, stmtId 99] .unit
    (Core.LocalControl.returned .unit) := by
  apply ControlStatements.tree_of_lowerFlowStatements (fuel := 1) aligned
    (show NodeOccurrencesUnique earlySource from by unfold NodeOccurrencesUnique nodeOccurrenceIds; decide)
  rfl

end Tests.SourceCoreControlStatementCertificates
