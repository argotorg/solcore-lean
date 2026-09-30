import Solcore.SourceSemantics.CoreLowering.BasicStatementCertificates

/-! Certificates are obtained from actual compiler success. No statement tree
or evaluation derivation is supplied by these tests. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicStatementCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"statement_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "local", scheme := .mono .word }
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "statement_certificates.solc" }
  startByte := 0
  endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reason : Core.Word := word 73
private def resultType : Core.Ty := .product .word .bool
private def expressionNode (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := exprId index, span, type, form }
private def statementNode (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : Node :=
  .statement { id := stmtId index, span, type, form }
private def assignment : AssignmentResolution :=
  { target := { root := (binder 0).id, projections := [], type := .word } }
private def statements : List StatementId := (List.range 6).map stmtId

/-- `let a: Word; let b = 7; a = b; b; return (a, true); { ... }`.
The unsupported final block is skipped by the actual explicit return branch. -/
private def source : TypedSource := {
  owner
  inputs := []
  roots := statements.map .statement
  nodes := [
    expressionNode 0 .word (.literal (.decimal "7")),
    expressionNode 1 .word (.reference "b" (.local (binder 1).id)),
    expressionNode 2 .word (.reference "a" (.local (binder 0).id)),
    expressionNode 3 .bool (.reference "true" (.builtinBoolean true)),
    expressionNode 4 (.product .word .bool) (.tuple [exprId 2, exprId 3]),
    statementNode 0 .unit (.letDecl (binder 0) none),
    statementNode 1 .unit (.letDecl (binder 1) (some (exprId 0))),
    statementNode 2 .unit (.assignValue assignment .equal (exprId 1)),
    statementNode 3 .unit (.expression (exprId 1) true),
    statementNode 4 (.product .word .bool) (.returnStmt (some (exprId 4))),
    statementNode 5 .unit (.block [])
  ]
}
private def code : Core.Expr :=
  Core.LocalSequence.letUninitialized .word
    (Core.LocalSequence.letInitialized resultType .word (Core.LanguageResult.success (.word (word 7)))
      (Core.LocalSequence.assign resultType (.var 1) (Core.OptionalCell.read .word (.var 0) reason)
        (Core.LocalSequence.discard resultType (Core.OptionalCell.read .word (.var 0) reason)
          (Core.LocalSequence.pair .word .bool (Core.OptionalCell.read .word (.var 1) reason)
            (Core.LanguageResult.success (.bool true))))))

private theorem accepted : SourceCoreBasic.lowerStatements 8 source [] statements resultType reason =
    .ok code := by rfl

example : Core.HasType [] code (Core.LanguageResult.resultType resultType) :=
  BasicStatements.lowerStatements_hasType accepted

example : Core.infer? [] code = some (Core.LanguageResult.resultType resultType) :=
  BasicStatements.lowerStatements_infer accepted

example : Core.CellPayload resultType :=
  (BasicStatements.lowerStatements_typing accepted).2

example : BasicStatements.BinderCertificate source [] (binder 0) .word :=
  BasicStatements.lowerBinder_certificate (by rfl)

example : BasicStatements.AssignmentCertificate source [((binder 1).id, .word), ((binder 0).id, .word)]
    assignment .equal 1 .word :=
  BasicStatements.lowerAssignment_certificate (by rfl)

/-- The three Unit/implicit completion branches use the same universal theorem. -/
private def returnUnit : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)], nodes := [statementNode 0 .unit (.returnStmt none)]
}
private def implicitReturn : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)], nodes := [expressionNode 0 .bool (.reference "true" (.builtinBoolean true)),
    statementNode 0 .bool (.expression (exprId 0) false)]
}
example : Core.HasType [] (Core.LanguageResult.success .unit) (Core.LanguageResult.resultType .unit) :=
  BasicStatements.lowerStatements_hasType
    (source := source) (scope := []) (fuel := 0) (statements := []) (reason := reason) (by rfl)
example : Core.HasType [] (Core.LanguageResult.success .unit) (Core.LanguageResult.resultType .unit) :=
  BasicStatements.lowerStatements_hasType
    (source := returnUnit) (scope := []) (fuel := 1) (statements := [stmtId 0]) (reason := reason) (by rfl)
example : Core.HasType [] (Core.LanguageResult.success (.bool true)) (Core.LanguageResult.resultType .bool) :=
  BasicStatements.lowerStatements_hasType
    (source := implicitReturn) (scope := []) (fuel := 2) (statements := [stmtId 0]) (reason := reason) (by rfl)

/-- Rejected scope and annotation cases cannot feed typing extraction. -/
example (output : Core.Expr) :
    SourceCoreBasic.lowerStatements 8 source [((binder 0).id, .word)] statements resultType reason ≠
      .ok output := by
  intro impossible
  cases impossible
example (output : Core.Expr) :
    SourceCoreBasic.lowerStatements 8 source [] statements .bool reason ≠ .ok output := by
  intro impossible
  cases impossible
example (output : Core.Expr) :
    SourceCoreBasic.lowerStatements 8 implicitReturn [] [stmtId 0, stmtId 0] .bool reason ≠
      .ok output := by
  intro impossible
  cases impossible
example (output : Core.Expr) :
    SourceCoreBasic.lowerStatements 0 source [] [] .word reason ≠ .ok output := by
  intro impossible
  cases impossible
example (output : Core.Expr) :
    SourceCoreBasic.lowerStatements 8 source [] [stmtId 5] .unit reason ≠ .ok output := by
  intro impossible
  cases impossible

end Tests.SourceCoreBasicStatementCertificates
