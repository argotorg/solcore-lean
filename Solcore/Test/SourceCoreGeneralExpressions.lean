import Solcore.SourceSemantics.CoreLowering.GeneralExpressions

/-! Actual primitive compilation and independent semantics over a heap with
interleaved administrative recursive function cells and source locations.
Temporary lexical values must not alter captured closures or stored payloads. -/

set_option autoImplicit false

namespace Tests.SourceCoreGeneralExpressions

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"general_expressions", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "general_expressions.solc" }
  startByte := 0, endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (site : ExpressionId) : Core.Word := word (100 + site.occurrence.index)
private def scope : SourceCoreBasic.Scope := [(binder 0, .bool), (binder 1, .word), (binder 2, .bool)]
private def node (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := id index, span, type, form }
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def context : SourceSemantics.Context := Context.ofSignatures {
  functions := [], implRules := [], traits := [], implementations := []
}
private theorem contextValid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.ofSignatures] at impossible
private def source : TypedSource := {
  owner
  inputs := [{ id := binder 0, name := "flag", scheme := .mono .bool },
    { id := binder 1, name := "number", scheme := .mono .word },
    { id := binder 2, name := "right", scheme := .mono .bool }]
  roots := [.expression (id 0)]
  nodes := [node 0 (.product .word .bool) (.group (id 1)),
    node 1 (.product .word .bool) (.tuple [id 2, id 8]),
    node 2 .word (.conditional (id 3) (id 4) (id 7)),
    node 3 .bool (.reference "flag" (.local (binder 0))),
    node 4 .word (.binary (id 5) .add (id 6)),
    node 5 .word (.literal (.decimal "17")),
    node 6 .word (.reference "number" (.local (binder 1))),
    node 7 .word (.unary .bitNot (id 6)),
    node 8 .bool (.binary (id 9) .logicalAnd (id 10)),
    node 9 .bool (.unary .logicalNot (id 3)),
    node 10 .bool (.reference "right" (.local (binder 2)))]
}
private def code : Core.Expr :=
  Core.LocalSequence.pair .word .bool
    (Core.LocalControl.choose .word
      (Core.OptionalCell.read .bool (.var 0) (reasonAt (id 3)))
      (SourceCorePrimitive.binary .add
        (Core.LanguageResult.success (.word (word 17)))
        (Core.OptionalCell.read .word (.var 1) (reasonAt (id 6))))
      (Core.LocalPrimitiveResults.unary .wordNot
        (Core.OptionalCell.read .word (.var 1) (reasonAt (id 6)))))
    (Core.LocalPrimitiveResults.logicalAnd
      (Core.LocalPrimitiveResults.unary .boolNot
        (Core.OptionalCell.read .bool (.var 0) (reasonAt (id 3))))
      (Core.OptionalCell.read .bool (.var 2) (reasonAt (id 10))))
private theorem accepted : SourceCorePrimitive.lowerExpressionWithReasons 5 compilation source scope (id 0) reasonAt =
    .ok ⟨.product .word .bool, code⟩ := by rfl
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

private def boolCell (value : Option Bool) : Dynamic.Cell := { type := .bool, value := value.map .bool }
private def wordCell (value : Option Nat) : Dynamic.Cell := { type := .word, value := value.map fun n => .word (word n) }
private def boolStored : Option Bool → Core.Value
  | none => .inLeft .bool .unit
  | some value => .inRight .unit (.bool value)
private def wordStored : Option Nat → Core.Value
  | none => .inLeft .word .unit
  | some value => .inRight .unit (.word (word value))
private def heap (flag : Option Bool) (number : Option Nat) (right : Option Bool) : Dynamic.Heap :=
  ⟨[boolCell flag, wordCell number, boolCell right]⟩
private def functionType : Core.Ty := .function .unit .unit
private def optionalFunction : Core.Ty := Core.OptionalCell.cellType functionType
private def identityFunction : Core.Value := .closure .unit .unit (.var 0) []
private def recursiveFunction : Core.Value := .closure .unit .unit
  (.caseE (.loadCell (.var 1)) .unit (.apply (.var 0) (.var 1)))
  [.cellRef optionalFunction 0]
private def world : Core.StoreTyping := [optionalFunction, Core.OptionalCell.cellType .bool,
  functionType, Core.OptionalCell.cellType .word, Core.OptionalCell.cellType .bool]
private def mapping : GeneralHeap.LocationMap := [1, 3, 4]
private def store (flag : Option Bool) (number : Option Nat) (right : Option Bool) : Core.Store :=
  [.inRight .unit recursiveFunction, boolStored flag, recursiveFunction, wordStored number, boolStored right]
private def environment : Dynamic.Environment := [(binder 0, ⟨0⟩), (binder 1, ⟨1⟩), (binder 2, ⟨2⟩)]
private def administrativeContext : Core.Context := [.cell optionalFunction, .cell functionType]
private def coreEnvironment : Core.Environment := [
  .cellRef (Core.OptionalCell.cellType .bool) 1,
  .cellRef (Core.OptionalCell.cellType .word) 3,
  .cellRef (Core.OptionalCell.cellType .bool) 4,
  .cellRef optionalFunction 0, .cellRef functionType 2]
private theorem environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment :=
  .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil (.cons (.cellRef rfl) (.cons (.cellRef rfl) .nil)))))
private theorem boolRelated (value : Option Bool) : LocalCell.CellRepresents (boolCell value) (boolStored value) .bool := by
  cases value with
  | none => exact .uninitialized .bool
  | some value => exact .initialized (.bool value)
private theorem wordRelated (value : Option Nat) : LocalCell.CellRepresents (wordCell value) (wordStored value) .word := by
  cases value with
  | none => exact .uninitialized .word
  | some value => exact .initialized (.word (word value))
private theorem recursiveTyped : Core.RuntimeValueHasType world recursiveFunction functionType := by
  exact .closure (.cons (.cellRef rfl) .nil)
    (.caseE (.loadCell (.var rfl)) .unit (.apply (.var rfl) (.var rfl)))
private theorem heaps (flag : Option Bool) (number : Option Nat) (right : Option Bool) :
    GeneralHeap.HeapRepresents mapping world (heap flag number right) (store flag number right) := by
  have admin : GeneralHeap.HeapRepresents [] [optionalFunction] ⟨[]⟩ [.inLeft functionType .unit] :=
    GeneralHeap.HeapRepresents.empty.allocate_administrative (.inLeft .unit)
  have flagRelated := (admin.allocate (boolRelated flag) .append).1
  have extra := flagRelated.allocate_administrative
    (show Core.RuntimeValueHasType _ identityFunction functionType from .closure .nil (.var rfl))
  have numberRelated := (extra.allocate (wordRelated number) .append).1
  have original := (numberRelated.allocate (boolRelated right) .append).1
  have initial : GeneralHeap.HeapRepresents mapping world (heap flag number right)
      [.inLeft functionType .unit, boolStored flag, identityFunction, wordStored number, boolStored right] := original
  have installed : GeneralHeap.HeapRepresents mapping world (heap flag number right)
      [.inRight .unit recursiveFunction, boolStored flag, identityFunction, wordStored number, boolStored right] := by
    apply initial.write_administrative (location := 0) (type := optionalFunction)
    · intro index found
      have member := List.mem_of_getElem? found
      simp [mapping] at member
    · rfl
    · exact .inRight recursiveTyped
    · rfl
  apply installed.write_administrative (location := 2) (type := functionType)
  · intro index found
    have member := List.mem_of_getElem? found
    simp [mapping] at member
  · rfl
  · exact recursiveTyped
  · rfl

/-- Arbitrary ordinary input initialization is allowed alongside administrative
recursive functions. The derived source and Core results need no child
execution assumptions and no first-order invariant for the complete store. -/
example (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (flag : Option Bool) (number : Option Nat) (right : Option Bool) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code =
      some (Core.LanguageResult.resultType (.product .word .bool)) ∧
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment
        (heap flag number right) (id 0) sourceOutcome (heap flag number right) ∧
      PrimitiveExpressions.OutcomeRepresents program context evidence source environment
        (heap flag number right) reasonAt (id 0) (.product .word .bool) sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment (store flag number right)) =
        .done coreValue (store flag number right)) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment (store flag number right)) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store flag number right) :=
  GeneralExpressions.Primitive.lowerExpression_run_preserves unique accepted program context evidence contextValid
    environments (heaps flag number right)

private theorem readOnly : Core.ReadOnly.Expression code := by
  obtain ⟨_, _, tree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique accepted
  exact GeneralExpressions.Primitive.readOnly tree

private theorem run_shortCircuit : Core.runStateful 300
    (.initial code coreEnvironment (store (some true) (some 3) none)) =
    .done (.inRight .word (.pair (.word (word 20)) (.bool false))) (store (some true) (some 3) none) := by
  simp [code, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LocalPrimitiveResults.logicalAnd, Core.LocalPrimitiveResults.unary,
    Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_rightFault : Core.runStateful 300
    (.initial code coreEnvironment (store (some false) (some 3) none)) =
    .done (.inLeft (.product .word .bool) (.word (reasonAt (id 10)))) (store (some false) (some 3) none) := by
  simp [code, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LocalPrimitiveResults.logicalAnd, Core.LocalPrimitiveResults.unary,
    Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_arithmeticRightFault : Core.runStateful 300
    (.initial code coreEnvironment (store (some true) none none)) =
    .done (.inLeft (.product .word .bool) (.word (reasonAt (id 6)))) (store (some true) none none) := by
  simp [code, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LocalPrimitiveResults.logicalAnd, Core.LocalPrimitiveResults.unary,
    Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

/-- The same actual compiler output evaluates under a temporary binder at
an arbitrary cutoff. Even the inserted value can itself be a closure. -/
example (cutoff : Nat) :
    Core.Evaluates (Core.Environment.insertAt coreEnvironment cutoff recursiveFunction)
      (store (some true) (some 3) none) (code.weakenAt cutoff)
      (.inRight .word (.pair (.word (word 20)) (.bool false))) (store (some true) (some 3) none) :=
  readOnly.evaluation_weakenAt (Core.runStateful_evaluation_sound run_shortCircuit) cutoff recursiveFunction

/-- Administrative closure cells retain their exact values after a completed
expression, including after the short-circuit RHS is actually evaluated and
fails at its own source read occurrence. -/
example : (store (some false) (some 3) none).read? 0 = some (.inRight .unit recursiveFunction) := rfl
example : (store (some false) (some 3) none).read? 2 = some recursiveFunction := rfl

example (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ∃ sourceOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment
        (heap (some false) (some 3) none) (id 0) sourceOutcome (heap (some false) (some 3) none) ∧
      PrimitiveExpressions.OutcomeRepresents program context evidence source environment
        (heap (some false) (some 3) none) reasonAt (id 0) (.product .word .bool) sourceOutcome
        (.inLeft (.product .word .bool) (.word (reasonAt (id 10)))) := by
  obtain ⟨sourceOutcome, coreValue, sourceEvaluation, represented, coreEvaluation⟩ :=
    GeneralExpressions.Primitive.lowerExpression_preserves unique accepted program context evidence contextValid
      environments (heaps (some false) (some 3) none)
  have same := Core.evaluation_deterministic (Core.runStateful_evaluation_sound run_rightFault) coreEvaluation
  exact ⟨sourceOutcome, sourceEvaluation, same.1 ▸ represented⟩

/-- The restriction really excludes closure creation and calls. -/
example : ¬ Core.ReadOnly.Expression (.lambda .unit .unit (.var 0)) := by intro impossible; cases impossible
example : ¬ Core.ReadOnly.Expression (.apply (.var 0) (.var 1)) := by intro impossible; cases impossible

end Tests.SourceCoreGeneralExpressions
