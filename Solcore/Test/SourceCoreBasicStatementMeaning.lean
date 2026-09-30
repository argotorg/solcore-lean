import Solcore.SourceSemantics.CoreLowering.BasicStatementMeaning

/-! A complete source/Core statement derivation is obtained from the structural
certificate. No child source or Core evaluation is provided. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicStatementMeaning

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

private def context : SourceSemantics.Context := .ofSignatures {
  functions := [], implRules := [], traits := [], implementations := []
}
private def firstContext : SourceSemantics.Context :=
  context.withLocal (binder 0).id (binder 0).scheme
private def secondContext : SourceSemantics.Context :=
  firstContext.withLocal (binder 1).id (binder 1).scheme

private theorem firstExtension : BinderExtends owner context (binder 0) firstContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .word
      }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl
    }
  · simp [LocalFresh, context, Context.ofSignatures]

private theorem secondExtension : BinderExtends owner firstContext (binder 1) secondContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, firstContext, context, Context.ofSignatures, Context.withLocal]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .word
      }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl
    }
  · simp [LocalFresh, firstContext, context, Context.ofSignatures, Context.withLocal, binder]

private def statement (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : StatementNode :=
  { id := stmtId index, span, type, form }
private def bothScope : SourceCoreBasic.Scope := [((binder 1).id, .word), ((binder 0).id, .word)]

private theorem certificate : ∃ depth, BasicStatements.Tree source reason [] context
    statements resultType code depth := by
  obtain ⟨initializerDepth, _, initializer⟩ := BasicExpressions.tree_of_lowerExpression
    (fuel := 1) (source := source) (scope := [((binder 0).id, .word)]) (id := exprId 0) (reason := reason)
    (lowered := ⟨.word, Core.LanguageResult.success (.word (word 7))⟩) (by rfl)
  obtain ⟨localDepth, _, localRead⟩ := BasicExpressions.tree_of_lowerExpression
    (fuel := 1) (source := source) (scope := bothScope) (id := exprId 1) (reason := reason)
    (lowered := ⟨.word, Core.OptionalCell.read .word (.var 0) reason⟩) (by rfl)
  obtain ⟨pairDepth, _, pair⟩ := BasicExpressions.tree_of_lowerExpression
    (fuel := 2) (source := source) (scope := bothScope) (id := exprId 4) (reason := reason)
    (lowered := ⟨resultType, Core.LocalSequence.pair .word .bool (Core.OptionalCell.read .word (.var 1) reason)
      (Core.LanguageResult.success (.bool true))⟩) (by rfl)
  have returned := BasicStatements.Tree.returnValue (context := secondContext) [stmtId 5]
    ((BasicStatements.readStatement_certificate
      (id := stmtId 4) (node := statement 4 (.product .word .bool) (.returnStmt (some (exprId 4)))) (by rfl)).2)
    (by rfl) pair
  have discarded := BasicStatements.Tree.discard
    ((BasicStatements.readStatement_certificate
      (id := stmtId 3) (node := statement 3 .unit (.expression (exprId 1) true)) (by rfl)).2)
    (by rfl) localRead returned
  have assigned := BasicStatements.Tree.assign
    ((BasicStatements.readStatement_certificate
      (id := stmtId 2) (node := statement 2 .unit (.assignValue assignment .equal (exprId 1))) (by rfl)).2)
    (by rfl) (BasicStatements.lowerAssignment_certificate (index := 1) (by rfl)) localRead discarded
  have initialized := BasicStatements.Tree.letInitialized
    ((BasicStatements.readStatement_certificate
      (id := stmtId 1) (node := statement 1 .unit (.letDecl (binder 1) (some (exprId 0)))) (by rfl)).2)
    (by rfl) (BasicStatements.lowerBinder_certificate (by rfl)) secondExtension initializer assigned
  exact ⟨_, BasicStatements.Tree.letUninitialized
    ((BasicStatements.readStatement_certificate
      (id := stmtId 0) (node := statement 0 .unit (.letDecl (binder 0) none)) (by rfl)).2)
    (by rfl) (BasicStatements.lowerBinder_certificate (by rfl)) firstExtension initialized⟩

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- The complete source result and final heap follow from the certificate,
including allocation, assignment and the inserted initializer payload. -/
example (program : Program) :
    ∃ finalContext outcome after result finalStore finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩
        statements finalContext outcome after ∧
      BasicStatements.OutcomeRepresents finalWorld reason resultType outcome result ∧
      Core.Evaluates [] [] code result finalStore ∧
      LocalCell.HeapRepresents after.cells finalStore finalWorld ∧ Core.WorldExtends [] finalWorld := by
  obtain ⟨depth, tree⟩ := certificate
  exact tree.preserves unique program [] .nil .nil

example (program : Program) :
    ∃ compilationFuel finalContext outcome after result finalStore finalWorld required,
      SourceCoreBasic.lowerStatements compilationFuel source [] statements resultType reason = .ok code ∧
      Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩
        statements finalContext outcome after ∧
      BasicStatements.OutcomeRepresents finalWorld reason resultType outcome result ∧
      LocalCell.HeapRepresents after.cells finalStore finalWorld ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code [] []) = .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code [] []) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  obtain ⟨depth, tree⟩ := certificate
  obtain ⟨lowered, _, finalContext, outcome, after, result, finalStore, finalWorld, required,
    sourceExecution, related, heaps, _, _, completes, reflects⟩ :=
    tree.lower_run_preserves unique depth (Nat.le_refl _) program [] .nil .nil
  exact ⟨_, _, _, _, _, _, _, _, lowered, sourceExecution, related, heaps, completes, reflects⟩

/-- A concrete kernel run fixes both mutable cells to the assigned value. -/
example : Core.runStateful 200 (.initial code [] []) =
    .done (.inRight .word (.pair (.word (word 7)) (.bool true)))
      [.inRight .unit (.word (word 7)), .inRight .unit (.word (word 7))] := by
  simp [code, resultType, Core.LocalSequence.letUninitialized, Core.LocalSequence.letInitialized,
    Core.LocalSequence.assign, Core.LocalSequence.discard, Core.LocalSequence.pair,
    Core.OptionalCell.allocate, Core.OptionalCell.allocateInitialized, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

/-- A failed initializer must leave only the first allocation and skip both
the second allocation and the return. The same general body theorem applies. -/
private def failedSource : TypedSource := {
  owner, inputs := [], roots := [stmtId 0, stmtId 1, stmtId 2].map .statement
  nodes := [expressionNode 0 .word (.reference "a" (.local (binder 0).id)),
    statementNode 0 .unit (.letDecl (binder 0) none),
    statementNode 1 .unit (.letDecl (binder 1) (some (exprId 0))),
    statementNode 2 .unit (.returnStmt none)]
}
private def failedCode : Core.Expr :=
  Core.LocalSequence.letUninitialized .word
    (Core.LocalSequence.letInitialized .unit .word (Core.OptionalCell.read .word (.var 0) reason)
      (Core.LanguageResult.success .unit))
private theorem failedCertificate : ∃ depth, BasicStatements.Tree failedSource reason [] context
    [stmtId 0, stmtId 1, stmtId 2] .unit failedCode depth := by
  obtain ⟨valueDepth, _, value⟩ := BasicExpressions.tree_of_lowerExpression
    (fuel := 1) (source := failedSource) (scope := [((binder 0).id, .word)]) (id := exprId 0) (reason := reason)
    (lowered := ⟨.word, Core.OptionalCell.read .word (.var 0) reason⟩) (by rfl)
  have returned := BasicStatements.Tree.returnUnit (source := failedSource) (reason := reason)
    (context := secondContext) (scope := bothScope) []
    ((BasicStatements.readStatement_certificate
      (id := stmtId 2) (node := statement 2 .unit (.returnStmt none)) (by rfl)).2) (by rfl)
  have initialized := BasicStatements.Tree.letInitialized
    ((BasicStatements.readStatement_certificate
      (id := stmtId 1) (node := statement 1 .unit (.letDecl (binder 1) (some (exprId 0)))) (by rfl)).2)
    (by rfl) (BasicStatements.lowerBinder_certificate (by rfl)) secondExtension value returned
  exact ⟨_, BasicStatements.Tree.letUninitialized
    ((BasicStatements.readStatement_certificate
      (id := stmtId 0) (node := statement 0 .unit (.letDecl (binder 0) none)) (by rfl)).2)
    (by rfl) (BasicStatements.lowerBinder_certificate (by rfl)) firstExtension initialized⟩

example (program : Program) :
    ∃ finalContext outcome after result finalStore finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context [] failedSource [] ⟨[]⟩
        [stmtId 0, stmtId 1, stmtId 2] finalContext outcome after ∧
      BasicStatements.OutcomeRepresents finalWorld reason .unit outcome result ∧
      Core.Evaluates [] [] failedCode result finalStore ∧
      LocalCell.HeapRepresents after.cells finalStore finalWorld ∧ Core.WorldExtends [] finalWorld := by
  obtain ⟨depth, tree⟩ := failedCertificate
  have unique : NodeOccurrencesUnique failedSource := by
    unfold NodeOccurrencesUnique nodeOccurrenceIds
    decide
  exact tree.preserves unique program [] .nil .nil

example : Core.runStateful 100 (.initial failedCode [] []) =
    .done (.inLeft .unit (.word reason)) [.inLeft .word .unit] := by
  simp [failedCode, Core.LocalSequence.letUninitialized, Core.LocalSequence.letInitialized,
    Core.OptionalCell.allocate, Core.OptionalCell.allocateInitialized, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

end Tests.SourceCoreBasicStatementMeaning
