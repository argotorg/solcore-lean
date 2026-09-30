import Solcore.SourceSemantics.CoreLowering.ControlExpressions

/-! Actual accepted conditional lowering supplies both independent evaluations.
Distinct read occurrences carry distinct test reasons, even at shared types. -/

set_option autoImplicit false

namespace Tests.SourceCoreControlExpressions

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"control_expressions", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "control_expressions.solc" }
  startByte := 0, endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (site : ExpressionId) : Core.Word := word (100 + site.occurrence.index)
private def scope : SourceCoreBasic.Scope := [(binder 0, .bool), (binder 1, .word), (binder 2, .word)]
private def node (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := id index, span, type, form }
private def source : TypedSource := {
  owner
  inputs := [{ id := binder 0, name := "flag", scheme := .mono .bool },
    { id := binder 1, name := "left", scheme := .mono .word },
    { id := binder 2, name := "right", scheme := .mono .word }]
  roots := [.expression (id 0)]
  nodes := [node 0 (.product .word .word) (.group (id 1)),
    node 1 (.product .word .word) (.tuple [id 2, id 6]),
    node 2 .word (.conditional (id 3) (id 4) (id 5)),
    node 3 .bool (.reference "flag" (.local (binder 0))),
    node 4 .word (.literal (.decimal "7")),
    node 5 .word (.reference "left" (.local (binder 1))),
    node 6 .word (.reference "right" (.local (binder 2)))]
}
private def code : Core.Expr :=
  Core.LocalSequence.pair .word .word
    (Core.LocalControl.choose .word
      (Core.OptionalCell.read .bool (.var 0) (reasonAt (id 3)))
      (Core.LanguageResult.success (.word (word 7)))
      (Core.OptionalCell.read .word (.var 1) (reasonAt (id 5))))
    (Core.OptionalCell.read .word (.var 2) (reasonAt (id 6)))
private theorem accepted : SourceCoreControl.lowerExpressionWithReasons 4 source scope (id 0) reasonAt =
    .ok ⟨.product .word .word, code⟩ := by rfl
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

example : Core.HasType (SourceCoreLocalCell.coreContext scope) code
    (Core.LanguageResult.resultType (.product .word .word)) :=
  ControlExpressions.lowerExpression_hasType unique accepted

example : ∃ node, SourceCoreBasic.readExpression source (id 0) = .ok (node, .product .word .word) ∧
    ControlExpressions.Metadata source (id 0) node (.product .word .word) :=
  ControlExpressions.lowerExpression_metadata unique accepted

private def boolCell (value : Option Bool) : Dynamic.Cell := { type := .bool, value := value.map .bool }
private def wordCell (value : Option Nat) : Dynamic.Cell := { type := .word, value := value.map fun n => .word (word n) }
private def boolStored : Option Bool → Core.Value
  | none => .inLeft .bool .unit
  | some value => .inRight .unit (.bool value)
private def wordStored : Option Nat → Core.Value
  | none => .inLeft .word .unit
  | some value => .inRight .unit (.word (word value))
private def heap (flag : Option Bool) (left right : Option Nat) : Dynamic.Heap :=
  ⟨[boolCell flag, wordCell left, wordCell right]⟩
private def store (flag : Option Bool) (left right : Option Nat) : Core.Store :=
  [boolStored flag, wordStored left, wordStored right]
private def world : Core.StoreTyping :=
  [Core.OptionalCell.cellType .bool, Core.OptionalCell.cellType .word, Core.OptionalCell.cellType .word]
private def environment : Dynamic.Environment := [(binder 0, ⟨0⟩), (binder 1, ⟨1⟩), (binder 2, ⟨2⟩)]
private def coreEnvironment : Core.Environment :=
  [.cellRef (Core.OptionalCell.cellType .bool) 0,
    .cellRef (Core.OptionalCell.cellType .word) 1, .cellRef (Core.OptionalCell.cellType .word) 2]
private theorem environments : LocalCell.EnvRepresents world scope environment coreEnvironment :=
  .cons rfl (.cons rfl (.cons rfl .nil))
private theorem boolRelated (value : Option Bool) : LocalCell.CellRepresents (boolCell value) (boolStored value) .bool := by
  cases value with
  | none => exact .uninitialized .bool
  | some value => exact .initialized (.bool value)
private theorem wordRelated (value : Option Nat) : LocalCell.CellRepresents (wordCell value) (wordStored value) .word := by
  cases value with
  | none => exact .uninitialized .word
  | some value => exact .initialized (.word (word value))
private theorem heaps (flag : Option Bool) (left right : Option Nat) :
    LocalCell.HeapRepresents (heap flag left right).cells (store flag left right) world :=
  .cons (boolRelated flag) (.cons (wordRelated left) (.cons (wordRelated right) .nil))

/-- One theorem covers initialized and absent inputs without manual trees or
child execution assumptions. Its failure case exposes the executed read site. -/
example (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (flag : Option Bool) (left right : Option Nat) :
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment
        (heap flag left right) (id 0) sourceOutcome (heap flag left right) ∧
      ControlExpressions.OutcomeRepresents program context evidence source environment
        (heap flag left right) reasonAt (id 0) (.product .word .word) sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment (store flag left right)) =
        .done coreValue (store flag left right)) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment (store flag left right)) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store flag left right) :=
  (ControlExpressions.lowerExpression_run_preserves unique accepted program context evidence environments
    (heaps flag left right)).2

private theorem run_true : Core.runStateful 200 (.initial code coreEnvironment (store (some true) none (some 13))) =
    .done (.inRight .word (.pair (.word (word 7)) (.word (word 13)))) (store (some true) none (some 13)) := by
  simp [code, Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_false : Core.runStateful 200 (.initial code coreEnvironment (store (some false) (some 11) (some 13))) =
    .done (.inRight .word (.pair (.word (word 11)) (.word (word 13)))) (store (some false) (some 11) (some 13)) := by
  simp [code, Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_conditionFault : Core.runStateful 200 (.initial code coreEnvironment (store none none (some 13))) =
    .done (.inLeft (.product .word .word) (.word (reasonAt (id 3)))) (store none none (some 13)) := by
  simp [code, Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_branchFault : Core.runStateful 200 (.initial code coreEnvironment (store (some false) none (some 13))) =
    .done (.inLeft (.product .word .word) (.word (reasonAt (id 5)))) (store (some false) none (some 13)) := by
  simp [code, Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_rightFault : Core.runStateful 200 (.initial code coreEnvironment (store (some true) none none)) =
    .done (.inLeft (.product .word .word) (.word (reasonAt (id 6)))) (store (some true) none none) := by
  simp [code, Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

private def thenFailedSource : TypedSource := {
  source with nodes := [node 0 (.product .word .word) (.group (id 1)),
    node 1 (.product .word .word) (.tuple [id 2, id 6]),
    node 2 .word (.conditional (id 3) (id 5) (id 4)),
    node 3 .bool (.reference "flag" (.local (binder 0))),
    node 4 .word (.literal (.decimal "7")),
    node 5 .word (.reference "left" (.local (binder 1))),
    node 6 .word (.reference "right" (.local (binder 2)))]
}
private def thenFailedCode : Core.Expr :=
  Core.LocalSequence.pair .word .word
    (Core.LocalControl.choose .word
      (Core.OptionalCell.read .bool (.var 0) (reasonAt (id 3)))
      (Core.OptionalCell.read .word (.var 1) (reasonAt (id 5)))
      (Core.LanguageResult.success (.word (word 7))))
    (Core.OptionalCell.read .word (.var 2) (reasonAt (id 6)))
private theorem thenAccepted : SourceCoreControl.lowerExpressionWithReasons 4 thenFailedSource scope (id 0) reasonAt =
    .ok ⟨.product .word .word, thenFailedCode⟩ := by rfl

example (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence thenFailedSource environment
        (heap (some true) none none) (id 0) sourceOutcome (heap (some true) none none) ∧
      ControlExpressions.OutcomeRepresents program context evidence thenFailedSource environment
        (heap (some true) none none) reasonAt (id 0) (.product .word .word) sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment (store (some true) none none) thenFailedCode coreValue
        (store (some true) none none) := by
  have unique : NodeOccurrencesUnique thenFailedSource := by
    unfold NodeOccurrencesUnique nodeOccurrenceIds
    decide
  exact ControlExpressions.lowerExpression_preserves unique thenAccepted program context evidence environments
    (heaps (some true) none none)

example : Core.runStateful 200 (.initial thenFailedCode coreEnvironment (store (some true) none none)) =
    .done (.inLeft (.product .word .word) (.word (reasonAt (id 5)))) (store (some true) none none) := by
  simp [thenFailedCode, Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

/-- Malformed conditional metadata and branch types are rejected by the real
compiler before any certificate or runtime result can be obtained. -/
private def badSource : TypedSource := {
  source with nodes := [node 0 .word (.conditional (id 3) (id 3) (id 4)),
    node 3 .bool (.reference "flag" (.local (binder 0))), node 4 .word (.literal (.decimal "7"))]
}
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreControl.lowerExpressionWithReasons 4 badSource scope (id 0) reasonAt ≠ .ok output := by
  intro impossible
  cases impossible
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreControl.lowerExpressionWithReasons 3 source scope (id 0) reasonAt ≠ .ok output := by
  intro impossible
  cases impossible

end Tests.SourceCoreControlExpressions
