import Solcore.SourceSemantics.CoreLowering.BasicExpressionCertificates

/-! Proof consumers start from actual accepted lowering, not a hand-built Tree.
One nested expression exercises every currently accepted expression form. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicExpressionCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"expression_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : Resolved.LocalId := ⟨owner, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "expression_certificates.solc" }
  startByte := 0
  endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reason : Core.Word := word 71
private def scope : SourceCoreLocalCell.Scope := [(binder, .word)]
private def resultType : Core.Ty := .product (.product .word .bool) (.product .unit .word)
private def node (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : ExpressionNode :=
  { id := id index, span, type, form }

/-- `((7, true), ((), local))`, with a group node around the left pair. -/
private def source : TypedSource := {
  owner
  inputs := [{ id := binder, name := "local", scheme := .mono .word }]
  roots := [.expression (id 0)]
  nodes := [
    .expression (node 0 (.product (.product .word .bool) (.product .unit .word)) (.tuple [id 1, id 5])),
    .expression (node 1 (.product .word .bool) (.group (id 2))),
    .expression (node 2 (.product .word .bool) (.tuple [id 3, id 4])),
    .expression (node 3 .word (.literal (.decimal "7"))),
    .expression (node 4 .bool (.reference "true" (.builtinBoolean true))),
    .expression (node 5 (.product .unit .word) (.tuple [id 6, id 7])),
    .expression (node 6 .unit (.tuple [])),
    .expression (node 7 .word (.reference "local" (.local binder)))
  ]
}
private def code : Core.Expr :=
  Core.LocalSequence.pair (.product .word .bool) (.product .unit .word)
    (Core.LocalSequence.pair .word .bool
      (Core.LanguageResult.success (.word (word 7))) (Core.LanguageResult.success (.bool true)))
    (Core.LocalSequence.pair .unit .word (Core.LanguageResult.success .unit)
      (Core.OptionalCell.read .word (.var 0) reason))

private theorem accepted : SourceCoreBasic.lowerExpression 4 source scope (id 0) reason =
    .ok ⟨resultType, code⟩ := by rfl

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- The exact compiler result produces a bounded structural certificate. -/
example : ∃ depth, depth ≤ 4 ∧ BasicExpressions.Tree source scope reason (id 0) resultType code depth :=
  BasicExpressions.tree_of_lowerExpression accepted

example : Core.HasType (SourceCoreLocalCell.coreContext scope) code
    (Core.LanguageResult.resultType resultType) :=
  BasicExpressions.lowerExpression_hasType accepted

private def coreEnvironment : Core.Environment := [.cellRef (Core.OptionalCell.cellType .word) 0]
private def environment : Dynamic.Environment := [(binder, ⟨0⟩)]
private def world : Core.StoreTyping := [Core.OptionalCell.cellType .word]
private theorem environments : LocalCell.EnvRepresents world scope environment coreEnvironment :=
  .cons rfl .nil

private def initializedHeap : Dynamic.Heap := ⟨[{ type := .word, value := some (.word (word 13)) }]⟩
private def initializedStore : Core.Store := [.inRight .unit (.word (word 13))]
private theorem initialized : LocalCell.HeapRepresents initializedHeap.cells initializedStore world :=
  .cons (.initialized (.word (word 13))) .nil
private def absentHeap : Dynamic.Heap := ⟨[{ type := .word, value := none }]⟩
private def absentStore : Core.Store := [.inLeft .word .unit]
private theorem absent : LocalCell.HeapRepresents absentHeap.cells absentStore world :=
  .cons (.uninitialized .word) .nil

private def Correspondence (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (heap : Dynamic.Heap) (store : Core.Store) : Prop :=
  Core.infer? (SourceCoreLocalCell.coreContext scope) code = some (Core.LanguageResult.resultType resultType) ∧
  ∃ sourceOutcome coreValue required,
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap (id 0) sourceOutcome heap ∧
    BasicExpressions.OutcomeRepresents resultType reason sourceOutcome coreValue ∧
    (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment store) = .done coreValue store) ∧
    (∀ fuel result finalStore, Core.runStateful fuel (.initial code coreEnvironment store) = .done result finalStore →
      result = coreValue ∧ finalStore = store)

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Correspondence program context evidence initializedHeap initializedStore :=
  BasicExpressions.lowerExpression_run_preserves accepted unique program context evidence environments initialized

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Correspondence program context evidence absentHeap absentStore :=
  BasicExpressions.lowerExpression_run_preserves accepted unique program context evidence environments absent

example : Core.runStateful 100 (.initial code coreEnvironment initializedStore) =
    .done (.inRight .word (.pair (.pair (.word (word 7)) (.bool true)) (.pair .unit (.word (word 13)))))
      initializedStore := by
  simp [code, Core.LocalSequence.pair, Core.OptionalCell.read, Core.LanguageResult.bind,
    Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

example : Core.runStateful 100 (.initial code coreEnvironment absentStore) =
    .done (.inLeft resultType (.word reason)) absentStore := by
  simp [code, Core.LocalSequence.pair, Core.OptionalCell.read, Core.LanguageResult.bind,
    Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

/-- Missing and mismatched local slots cannot be turned into a certificate. -/
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreBasic.lowerExpression 4 source [] (id 0) reason ≠ .ok output := by
  intro impossible
  cases impossible

example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreBasic.lowerExpression 4 source [(binder, .bool)] (id 0) reason ≠ .ok output := by
  intro impossible
  cases impossible

private def only (expression : ExpressionNode) : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 0)], nodes := [.expression expression] }

example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreBasic.lowerExpression 4 (only (node 0 .word (.literal (.decimal "invalid"))))
      [] (id 0) reason ≠ .ok output := by
  intro impossible
  cases impossible

example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreBasic.lowerExpression 4
      (only { node 0 .bool (.reference "true" (.builtinBoolean true)) with requirements := [⟨0⟩] })
      [] (id 0) reason ≠ .ok output := by
  intro impossible
  cases impossible

example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreBasic.lowerExpression 4 (only (node 0 .word (.tuple [id 0])))
      [] (id 0) reason ≠ .ok output := by
  intro impossible
  cases impossible

/-- A cyclic occurrence edge exhausts compilation depth; it cannot forge Tree. -/
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreBasic.lowerExpression 4 (only (node 0 .word (.group (id 0))))
      [] (id 0) reason ≠ .ok output := by
  intro impossible
  cases impossible

end Tests.SourceCoreBasicExpressionCertificates
