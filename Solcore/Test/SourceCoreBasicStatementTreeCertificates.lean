import Solcore.SourceSemantics.CoreLowering.BasicStatementTreeCertificates

/-! Actual successful basic compilation supplies whole statement certificates,
including declarative binder extensions. No Tree is constructed by the tests. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicStatementTreeCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"general_statements", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "local", scheme := .mono .word }
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "general_statements.solc" }
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

private theorem aligned : BasicStatements.ScopeContextAligned [] context :=
  BasicStatements.ScopeContextAligned.empty _

private theorem accepted : SourceCoreBasic.lowerStatements 20 source [] statements resultType reason = .ok code := by
  rfl

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- Both declarations, assignment, discard and explicit return are recovered
from the compiler result. The unreachable unsupported block needs no Tree. -/
example : ∃ depth, depth ≤ 20 ∧ BasicStatements.Tree source reason [] context statements resultType code depth :=
  BasicStatements.tree_of_lowerStatements aligned accepted

/-- One typed administrative function cell forms a cycle through its captured
reference. It is not associated with any source heap location. -/
private def functionType : Core.Ty := .function .unit .unit
private def administrativeValue : Core.Value := .closure .unit .unit
  (.apply (.loadCell (.var 1)) (.var 0)) [.cellRef functionType 0]
private def initialWorld : Core.StoreTyping := [functionType]
private def initialStore : Core.Store := [administrativeValue]
private def initialEnvironment : Core.Environment := [.cellRef functionType 0]
private def administrativeContext : Core.Context := [.cell functionType]
private theorem administrativeTyped : Core.RuntimeValueHasType initialWorld administrativeValue functionType :=
  .closure (.cons (.cellRef rfl) .nil) (.apply (.loadCell (.var rfl)) (.var rfl))
private theorem initialHeaps : GeneralHeap.HeapRepresents [] initialWorld ⟨[]⟩ initialStore := by
  refine ⟨rfl, ?_, ⟨rfl, ?_⟩, ?_⟩
  · intro left right target impossible; simp at impossible
  · intro index type found
    cases index with
    | zero =>
        have same : functionType = type := by simpa [initialWorld] using found
        subst type
        exact ⟨administrativeValue, rfl, administrativeTyped⟩
    | succ index => simp [initialWorld] at found
  · intro source target impossible; simp at impossible
private theorem initialEnvironments : GeneralHeap.EnvRepresents [] initialWorld administrativeContext
    [] [] initialEnvironment := .nil (.cons (.cellRef rfl) .nil)


/-- Actual acceptance directly supplies the independent source execution and
Core runner correspondence with a cyclic administrative function installed. -/
example (program : Program) :
    ∃ finalContext outcome after result finalStore finalMapping finalWorld required,
      Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩
        statements finalContext outcome after ∧
      GeneralStatements.OutcomeRepresents finalMapping finalWorld administrativeContext reason resultType outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends [] finalMapping ∧ Core.WorldExtends initialWorld finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext [] [] initialEnvironment ∧
      GeneralHeap.AdministrativePreserved [] initialStore finalMapping finalStore ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code initialEnvironment initialStore) =
        .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code initialEnvironment initialStore) =
        .done actual actualStore → actual = result ∧ actualStore = finalStore) :=
  (BasicStatements.lowerStatements_run_preserves aligned unique accepted program [] initialEnvironments initialHeaps).2

/-- Initial ambient locals may be populated; the checked freshness condition
is transported across both paired source lexical tables. -/
example : BinderExtends owner
    (context.withLocal (binder 0).id (binder 0).scheme)
    (binder 1)
    ((context.withLocal (binder 0).id (binder 0).scheme).withLocal (binder 1).id (binder 1).scheme) := by
  exact (BasicStatements.lowerBinder_certificate
    (show SourceCoreBasic.lowerBinder source [((binder 0).id, .word)] (binder 1) = .ok .word from by rfl)).extends
      (aligned.bind (binder 0) .word)

/-- A compiler success cannot manufacture freshness for a malformed source
context containing an extra stale qualified-scheme entry. -/
example : ¬ BasicStatements.ScopeContextAligned []
    { context with localSchemeRequirements := [((binder 0).id, [])] } := by
  intro invalid
  have impossible := invalid.requirements
  simp at impossible

private def returnUnitSource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [statementNode 0 .unit (.returnStmt none)]
}
example : ∃ depth, depth ≤ 1 ∧ BasicStatements.Tree returnUnitSource reason [] context
    [stmtId 0, stmtId 99] .unit (Core.LanguageResult.success .unit) depth :=
  BasicStatements.tree_of_lowerStatements aligned (by rfl)

/-- Empty fallthrough is admitted even at zero traversal fuel. -/
example : ∃ depth, depth ≤ 0 ∧ BasicStatements.Tree source reason [] context [] .unit
    (Core.LanguageResult.success .unit) depth :=
  BasicStatements.tree_of_lowerStatements aligned (by rfl)

private def tailSource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [expressionNode 0 .word (.literal (.decimal "7")),
    statementNode 0 .word (.expression (exprId 0) false)]
}
example : ∃ depth, depth ≤ 2 ∧ BasicStatements.Tree tailSource reason [] context
    [stmtId 0] .word (Core.LanguageResult.success (.word (word 7))) depth :=
  BasicStatements.tree_of_lowerStatements aligned (by rfl)

/-- A non-final implicit return is rejected, rather than producing a Tree
which skips its remaining statements. -/
example : SourceCoreBasic.lowerStatements 2 tailSource [] [stmtId 0, stmtId 1] .word reason =
    .error (.nonTailExpression (stmtId 0)) := by rfl

/-- Duplicate binder identities are rejected before a second lexical extension. -/
example : SourceCoreBasic.lowerBinder source [((binder 0).id, .word)] (binder 0) =
    .error (.duplicateBinding (binder 0).id) := by rfl

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

/-- Extraction does not assume initialized locals or successful source values.
This admitted list fails in its initializer before the second allocation. -/
example : ∃ depth, depth ≤ 4 ∧ BasicStatements.Tree failedSource reason [] context
    [stmtId 0, stmtId 1, stmtId 2] .unit failedCode depth :=
  BasicStatements.tree_of_lowerStatements aligned (by rfl)

example : Core.runStateful 100 (.initial failedCode initialEnvironment initialStore) =
    .done (.inLeft .unit (.word reason)) [administrativeValue, .inLeft .word .unit] := by
  simp [failedCode, Core.LocalSequence.letUninitialized, Core.LocalSequence.letInitialized,
    Core.OptionalCell.allocate, Core.OptionalCell.allocateInitialized, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

end Tests.SourceCoreBasicStatementTreeCertificates
