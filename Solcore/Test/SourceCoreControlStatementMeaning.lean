import Solcore.SourceSemantics.CoreLowering.ControlStatementBridge

/-! Actual accepted scoped control preserves heap effects and lexical scope
with an installed administrative closure. These proofs construct no static
Tree or source child evaluation. -/

set_option autoImplicit false
set_option maxRecDepth 8000

namespace Tests.SourceCoreControlStatementMeaning

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"control_statement_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 20⟩⟩
private def binder (index : Nat) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "local", scheme := .mono .word }
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "control_statement_meaning.solc" }
  startByte := 0, endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (id : ExpressionId) : Core.Word := word (id.occurrence.index + 100)
private def fellThroughReason : Core.Word := word 777
private def expressionNode (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := exprId index, span, type, form }
private def statementNode (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : Node :=
  .statement { id := stmtId index, span, type, form }
private def assignment : AssignmentResolution :=
  { target := { root := (binder 0).id, projections := [], type := .word } }
private def context : SourceSemantics.Context := .ofSignatures {
  functions := [], implRules := [], traits := [], implementations := []
}
private theorem aligned : BasicStatements.ScopeContextAligned [] context :=
  BasicStatements.ScopeContextAligned.empty _

private def statements : List StatementId := [stmtId 0, stmtId 1, stmtId 5, stmtId 9, stmtId 10]

/-- The block assigns its local value to the outer cell and discards its last
expression. The conditional's local is also scoped. Its unselected branch and
the unsupported tail after the explicit return remain unexecuted. The block
and if occurrence types are Word, as admitted by the current compiler. -/
private def source : TypedSource := {
  owner, inputs := [], roots := statements.map .statement
  nodes := [
    expressionNode 0 .word (.literal (.decimal "1")),
    expressionNode 1 .word (.literal (.decimal "7")),
    expressionNode 2 .word (.reference "inner" (.local (binder 1).id)),
    expressionNode 3 .bool (.reference "true" (.builtinBoolean true)),
    expressionNode 4 .word (.literal (.decimal "8")),
    expressionNode 5 .word (.reference "branch" (.local (binder 2).id)),
    expressionNode 6 .word (.literal (.decimal "99")),
    expressionNode 7 .word (.reference "outer" (.local (binder 0).id)),
    statementNode 0 .unit (.letDecl (binder 0) (some (exprId 0))),
    statementNode 1 .word (.block [stmtId 2, stmtId 3, stmtId 4]),
    statementNode 2 .unit (.letDecl (binder 1) (some (exprId 1))),
    statementNode 3 .unit (.assignValue assignment .equal (exprId 2)),
    statementNode 4 .word (.expression (exprId 2) false),
    statementNode 5 .word (.ifThen (exprId 3) [stmtId 6, stmtId 7] (some [stmtId 8])),
    statementNode 6 .unit (.letDecl (binder 2) (some (exprId 4))),
    statementNode 7 .word (.expression (exprId 5) false),
    statementNode 8 .word (.returnStmt (some (exprId 6))),
    statementNode 9 .word (.returnStmt (some (exprId 7))),
    statementNode 10 .unit .breakStmt
  ]
}

private def compile (source : TypedSource) (statements : List StatementId) (type : Core.Ty) : Core.Expr :=
  match SourceCoreControl.lowerStatementsWithReasons 20 source [] statements type reasonAt fellThroughReason with
  | .ok code => code
  | .error _ => .unit

private def code : Core.Expr := compile source statements .word
private theorem accepted : SourceCoreControl.lowerStatementsWithReasons 20 source [] statements .word reasonAt fellThroughReason =
    .ok code := by rfl
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

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


/-- Acceptance is the only compiler-specific premise. This obtains the
independent source execution and enough runtime fuel, preserving installed
code and the captured outer environment across both scoped bodies. -/
example (program : Program) :
    ∃ finalContext outcome after result finalStore finalMapping finalWorld required,
      Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩ statements finalContext outcome after ∧
      ControlStatements.FinishedOutcomeRepresents program [] source finalMapping finalWorld administrativeContext reasonAt fellThroughReason
        .word outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends [] finalMapping ∧ Core.WorldExtends initialWorld finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext [] [] initialEnvironment ∧
      GeneralHeap.AdministrativePreserved [] initialStore finalMapping finalStore ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code initialEnvironment initialStore) = .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code initialEnvironment initialStore) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) :=
  (ControlStatements.lowerStatements_run_preserves aligned unique accepted .word program [] initialEnvironments initialHeaps).2

example (program : Program) : ∃ finalContext outcome after finalMapping finalWorld finalStore,
    Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩ statements finalContext outcome after ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    0 ∉ finalMapping ∧ finalStore.read? 0 = some administrativeValue := by
  obtain ⟨_, finalContext, outcome, after, result, finalStore, finalMapping, finalWorld, required,
    sourceExecution, related, heaps, maps, worlds, environments, frame, completes, reflects⟩ :=
    ControlStatements.lowerStatements_run_preserves aligned unique accepted .word program [] initialEnvironments initialHeaps
  obtain ⟨unmapped, same⟩ := frame 0 (by simp) (by decide)
  exact ⟨_, _, _, _, _, _, sourceExecution, heaps, unmapped, same⟩

private def failedSource : TypedSource := {
  owner, inputs := [], roots := [stmtId 0, stmtId 1, stmtId 4].map .statement
  nodes := [expressionNode 0 .bool (.reference "true" (.builtinBoolean true)),
    expressionNode 1 .word (.reference "empty" (.local (binder 0).id)),
    expressionNode 2 .word (.literal (.decimal "99")),
    statementNode 0 .unit (.letDecl (binder 0) none),
    statementNode 1 .word (.ifThen (exprId 0) [stmtId 2] (some [stmtId 3])),
    statementNode 2 .word (.returnStmt (some (exprId 1))),
    statementNode 3 .word (.returnStmt (some (exprId 2))),
    statementNode 4 .unit (.assignValue assignment .equal (exprId 2))]
}
private def failedStatements : List StatementId := [stmtId 0, stmtId 1, stmtId 4]
private def failedCode : Core.Expr := compile failedSource failedStatements .word

example (program : Program) : ∃ finalContext outcome after result finalStore finalMapping finalWorld,
    Dynamic.FunctionStatementsExecuteOutcome program context [] failedSource [] ⟨[]⟩ failedStatements finalContext outcome after ∧
    ControlStatements.FinishedOutcomeRepresents program [] failedSource finalMapping finalWorld administrativeContext reasonAt fellThroughReason
      .word outcome result ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore := by
  have accepted : SourceCoreControl.lowerStatementsWithReasons 20 failedSource [] failedStatements .word reasonAt fellThroughReason =
      .ok failedCode := by rfl
  have unique : NodeOccurrencesUnique failedSource := by unfold NodeOccurrencesUnique nodeOccurrenceIds; decide
  obtain ⟨_, finalContext, outcome, after, result, finalStore, finalMapping, finalWorld, required,
    sourceExecution, related, heaps, _⟩ :=
    ControlStatements.lowerStatements_run_preserves aligned unique accepted .word program [] initialEnvironments initialHeaps
  exact ⟨_, _, _, _, _, _, _, sourceExecution, related, heaps⟩

private def fallsThrough : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [expressionNode 0 .word (.literal (.decimal "7")),
    statementNode 0 .word (.block [stmtId 1]),
    statementNode 1 .word (.expression (exprId 0) false)]
}
/-- Concrete execution regressions are checked by the runner; the independent
source/Core correspondence above is a kernel theorem. -/
def run : IO Unit := do
  unless Core.runStateful 500 (.initial code initialEnvironment initialStore) ==
      .done (.inRight .word (.word (word 7)))
        [administrativeValue, .inRight .unit (.word (word 7)), .inRight .unit (.word (word 7)), .inRight .unit (.word (word 8))] do
    throw (IO.userError "scoped locals did not preserve outer write or administrative code")
  unless Core.runStateful 200 (.initial failedCode initialEnvironment initialStore) ==
      .done (.inLeft .word (.word (reasonAt (exprId 1)))) [administrativeValue, .inLeft .word .unit] do
    throw (IO.userError "fault provider or early exit did not survive scoped control")
  unless Core.runStateful 100 (.initial (compile fallsThrough [stmtId 0] .word) [] []) ==
      .done (.inLeft .word (.word fellThroughReason)) [] do
    throw (IO.userError "non-Unit nested tail should fall through to the missing-return token")
  unless Core.runStateful 100 (.initial (compile fallsThrough [stmtId 0] .unit) [] []) ==
      .done (.inRight .word .unit) [] do
    throw (IO.userError "Unit nested tail should finish with Unit")

end Tests.SourceCoreControlStatementMeaning
