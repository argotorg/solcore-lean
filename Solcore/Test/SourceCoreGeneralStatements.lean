import Solcore.SourceSemantics.CoreLowering.GeneralStatements

/-! Complete basic statement sequences execute over an administrative cyclic
closure heap. Source cells receive independent Core indices, writes preserve
installed code, and source initialization failures skip subsequent effects. -/

set_option autoImplicit false

namespace Tests.SourceCoreGeneralStatements

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

/-- The entire source list follows from a static certificate. Final mapping,
world, heap, original captures and administrative cells all remain related. -/
example (program : Program) :
    ∃ compilationFuel finalContext outcome after result finalStore finalMapping finalWorld required,
      SourceCoreBasic.lowerStatements compilationFuel source [] statements resultType reason = .ok code ∧
      Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩
        statements finalContext outcome after ∧
      GeneralStatements.OutcomeRepresents finalMapping finalWorld administrativeContext reason resultType outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends [] finalMapping ∧ Core.WorldExtends initialWorld finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext [] [] initialEnvironment ∧
      GeneralHeap.AdministrativePreserved [] initialStore finalMapping finalStore ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code initialEnvironment initialStore) = .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code initialEnvironment initialStore) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  obtain ⟨depth, tree⟩ := certificate
  obtain ⟨lowered, _, finalContext, outcome, after, result, finalStore, finalMapping, finalWorld, required,
    sourceExecution, related, heaps, mapsExtended, worldsExtended, captured, frame, completes, reflects⟩ :=
    GeneralStatements.lower_run_preserves tree unique depth (Nat.le_refl _) program [] initialEnvironments initialHeaps
  exact ⟨_, _, _, _, _, _, _, _, _, lowered, sourceExecution, related, heaps,
    mapsExtended, worldsExtended, captured, frame, completes, reflects⟩

private def finalStore : Core.Store := [administrativeValue,
  .inRight .unit (.word (word 7)), .inRight .unit (.word (word 7))]
private theorem executed : Core.runStateful 200 (.initial code initialEnvironment initialStore) =
    .done (.inRight .word (.pair (.word (word 7)) (.bool true))) finalStore := by
  simp [code, resultType, Core.LocalSequence.letUninitialized, Core.LocalSequence.letInitialized,
    Core.LocalSequence.assign, Core.LocalSequence.discard, Core.LocalSequence.pair,
    Core.OptionalCell.allocate, Core.OptionalCell.allocateInitialized, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

/-- Allocation and assignment under any inserted lexical binder produce the
same value and complete final store, including its captured closure. -/
example (cutoff : Nat) : Core.Evaluates
    (Core.Environment.insertAt initialEnvironment cutoff administrativeValue) initialStore (code.weakenAt cutoff)
    (.inRight .word (.pair (.word (word 7)) (.bool true))) finalStore := by
  obtain ⟨depth, tree⟩ := certificate
  exact (GeneralStatements.heapEffects tree).evaluation_weakenAt
    (Core.runStateful_evaluation_sound executed) cutoff administrativeValue

/-- The frame theorem exposes the unchanged installed function cell even
without knowing the concrete final mapping or final heap in advance. -/
example (program : Program) : ∃ outcome after finalMapping finalWorld finalContext finalStore,
    Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩ statements finalContext outcome after ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    0 ∉ finalMapping ∧ finalStore.read? 0 = some administrativeValue := by
  obtain ⟨depth, tree⟩ := certificate
  obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
    sourceExecution, related, coreExecution, heaps, mapsExtended, worldsExtended, frame⟩ :=
    GeneralStatements.preserves tree unique program [] initialEnvironments initialHeaps
  obtain ⟨unmapped, same⟩ := frame 0 (by simp) (by decide)
  exact ⟨outcome, after, finalMapping, finalWorld, finalContext, finalStore,
    sourceExecution, heaps, unmapped, same⟩

/-- Loading and storing an existing closure is admitted by the restricted
Core grammar. No lambda is evaluated, so renaming keeps that closure exact. -/
example (inserted : Core.Value) :
    Core.Evaluates (inserted :: initialEnvironment) initialStore
      ((Core.Expr.storeCell (.var 0) (.loadCell (.var 0))).weakenAt 0) .unit initialStore := by
  have evaluated : Core.Evaluates initialEnvironment initialStore
      (.storeCell (.var 0) (.loadCell (.var 0))) .unit initialStore :=
    .storeCell (.var rfl) rfl (.loadCell (.var rfl) rfl) rfl
  exact (Core.HeapEffects.Expression.storeCell .var (.loadCell .var)).evaluation_weakenAt_zero evaluated inserted

example : ¬ Core.HeapEffects.Expression (.lambda .unit .unit (.var 0)) := by intro impossible; cases impossible
example : ¬ Core.HeapEffects.Expression (.apply (.var 0) (.var 1)) := by intro impossible; cases impossible

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

/-- A failed initializer leaves the administrative closure and only the first
source allocation; the second allocation and return remain unexecuted. -/
example (program : Program) :
    ∃ finalContext outcome after result finalStore finalMapping finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context [] failedSource [] ⟨[]⟩
        [stmtId 0, stmtId 1, stmtId 2] finalContext outcome after ∧
      GeneralStatements.OutcomeRepresents finalMapping finalWorld administrativeContext reason .unit outcome result ∧
      Core.Evaluates initialEnvironment initialStore failedCode result finalStore ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends [] finalMapping ∧ Core.WorldExtends initialWorld finalWorld ∧
      GeneralHeap.AdministrativePreserved [] initialStore finalMapping finalStore := by
  obtain ⟨depth, tree⟩ := failedCertificate
  have unique : NodeOccurrencesUnique failedSource := by unfold NodeOccurrencesUnique nodeOccurrenceIds; decide
  exact GeneralStatements.preserves tree unique program [] initialEnvironments initialHeaps

example : Core.runStateful 100 (.initial failedCode initialEnvironment initialStore) =
    .done (.inLeft .unit (.word reason)) [administrativeValue, .inLeft .word .unit] := by
  simp [failedCode, Core.LocalSequence.letUninitialized, Core.LocalSequence.letInitialized,
    Core.OptionalCell.allocate, Core.OptionalCell.allocateInitialized, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

end Tests.SourceCoreGeneralStatements
