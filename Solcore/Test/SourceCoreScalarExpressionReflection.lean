import Solcore.SourceSemantics.CoreLowering.ScalarExpressionReflection

/-! The supplied source execution, including a propagated read fault, is
reflected through actual primitive lowering in a store containing a cyclic
administrative closure. Source location zero is Core location one. -/

set_option autoImplicit false

namespace Tests.SourceCoreScalarExpressionReflection

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"scalar_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : Resolved.LocalId := ⟨owner, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "scalar_reflection.solc" }
  startByte := 0, endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (site : ExpressionId) : Core.Word := word (100 + site.occurrence.index)
private def scope : SourceCoreBasic.Scope := [(binder, .word)]
private def node (index : Nat) (form : ExpressionForm) : Node :=
  .expression { id := id index, span, type := .word, form }
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def context : SourceSemantics.Context := Context.ofSignatures {
  functions := [], implRules := [], traits := [], implementations := []
}
private theorem contextValid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.ofSignatures] at impossible
private theorem covers : Dynamic.EvidenceEnvironment.Covers context [] := by
  constructor
  · intro goal evidence found
    cases found
  · intro predicate member
    simp [context, Context.ofSignatures] at member
private def source : TypedSource := {
  owner, inputs := [{ id := binder, name := "number", scheme := .mono .word }]
  roots := [.expression (id 0)]
  nodes := [node 0 (.group (id 1)), node 1 (.binary (id 2) .add (id 3)),
    node 2 (.reference "number" (.local binder)), node 3 (.literal (.decimal "1"))]
}
private def code : Core.Expr := SourceCorePrimitive.binary .add
  (Core.OptionalCell.read .word (.var 0) (reasonAt (id 2)))
  (Core.LanguageResult.success (.word (word 1)))
private theorem accepted : SourceCorePrimitive.lowerExpressionWithReasons 4 compilation source scope (id 0) reasonAt =
    .ok ⟨.word, code⟩ := by rfl
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide
private def cell (value : Option Core.Word) : Dynamic.Cell := { type := .word, value := value.map .word }
private def stored : Option Core.Word → Core.Value
  | none => .inLeft .word .unit
  | some value => .inRight .unit (.word value)
private def heap (value : Option Core.Word) : Dynamic.Heap := ⟨[cell value]⟩
private def functionType : Core.Ty := .function .unit .unit
private def optionalFunction : Core.Ty := Core.OptionalCell.cellType functionType
private def recursiveFunction : Core.Value := .closure .unit .unit
  (.caseE (.loadCell (.var 1)) .unit (.apply (.var 0) (.var 1)))
  [.cellRef optionalFunction 0]
private def world : Core.StoreTyping := [optionalFunction, Core.OptionalCell.cellType .word]
private def mapping : GeneralHeap.LocationMap := [1]
private def store (value : Option Core.Word) : Core.Store := [.inRight .unit recursiveFunction, stored value]
private def environment : Dynamic.Environment := [(binder, ⟨0⟩)]
private def administrativeContext : Core.Context := [.cell optionalFunction]
private def coreEnvironment : Core.Environment := [.cellRef (Core.OptionalCell.cellType .word) 1, .cellRef optionalFunction 0]
private theorem environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment :=
  .cons ⟨rfl, rfl⟩ (.nil (.cons (.cellRef rfl) .nil))
private theorem cellRelated (value : Option Core.Word) : LocalCell.CellRepresents (cell value) (stored value) .word := by
  cases value with
  | none => exact .uninitialized .word
  | some value => exact .initialized (.word value)
private theorem recursiveTyped : Core.RuntimeValueHasType world recursiveFunction functionType := by
  exact .closure (.cons (.cellRef rfl) .nil)
    (.caseE (.loadCell (.var rfl)) .unit (.apply (.var rfl) (.var rfl)))
private theorem heaps (value : Option Core.Word) : GeneralHeap.HeapRepresents mapping world (heap value) (store value) := by
  have admin : GeneralHeap.HeapRepresents [] [optionalFunction] ⟨[]⟩ [.inLeft functionType .unit] :=
    GeneralHeap.HeapRepresents.empty.allocate_administrative (.inLeft .unit)
  have allocated := (admin.allocate (cellRelated value) .append).1
  apply allocated.write_administrative (location := 0) (type := optionalFunction)
  · intro index found
    have member := List.mem_of_getElem? found
    simp at member
  · rfl
  · exact .inRight recursiveTyped
  · rfl

/-- A caller supplies its actual source trace; no child evaluation or desired
Tree is assumed by the compile-to-run theorem. -/
example (program : Program) (value : Option Core.Word) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (execution : Dynamic.ExpressionEvaluatesOutcome program context [] source environment (heap value) (id 0) outcome after) :
    after = heap value ∧ ∃ result required,
      PrimitiveExpressions.OutcomeRepresents program context [] source environment (heap value) reasonAt (id 0) .word outcome result ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment (store value)) = .done result (store value)) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment (store value)) = .done actual actualStore →
        actual = result ∧ actualStore = store value) :=
  ScalarExpressionReflection.Primitive.lowerExpression_source_run_preserves unique accepted contextValid covers environments (heaps value) execution

/-- Reflection rules out two successful source values as well as success and
fault overlap, even with administrative recursive cells. -/
example (program : Program) (input : Option Core.Word) (left right : Dynamic.Value) (leftHeap rightHeap : Dynamic.Heap)
    (leftEvaluation : Dynamic.ExpressionEvaluates program context [] source environment (heap input) (id 0) left leftHeap)
    (rightEvaluation : Dynamic.ExpressionEvaluates program context [] source environment (heap input) (id 0) right rightHeap) :
    left = right ∧ leftHeap = heap input ∧ rightHeap = heap input := by
  obtain ⟨_, _, tree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique accepted
  exact ScalarExpressionReflection.Primitive.source_success_functional tree unique environments (heaps input) leftEvaluation rightEvaluation

example (program : Program) (input : Option Core.Word) (value : Dynamic.Value) (reason : Dynamic.SemanticFault)
    (valueHeap faultHeap : Dynamic.Heap)
    (evaluation : Dynamic.ExpressionEvaluates program context [] source environment (heap input) (id 0) value valueHeap)
    (fault : Dynamic.ExpressionFaults program context [] source environment (heap input) (id 0) reason faultHeap) : False := by
  obtain ⟨_, _, tree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique accepted
  exact ScalarExpressionReflection.Primitive.source_success_excludes_fault tree unique contextValid covers environments (heaps input) evaluation fault

private theorem readOnly : Core.ReadOnly.Expression code := by
  obtain ⟨_, _, tree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique accepted
  exact GeneralExpressions.Primitive.readOnly tree

private theorem core_failed : Core.Evaluates coreEnvironment (store none) code
    (.inLeft .word (.word (reasonAt (id 2)))) (store none) :=
  Core.LocalPrimitiveResults.binaryWith_left_failure
    (Core.OptionalCell.read_failure _ (.var rfl) rfl)

/-- The reason is the leaf read occurrence, not the enclosing group/binary. -/
example (program : Program) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (execution : Dynamic.ExpressionEvaluatesOutcome program context [] source environment (heap none) (id 0) outcome after) :
    after = heap none ∧ ∃ site location,
      outcome = .fault (.uninitializedLocation location) ∧
      reasonAt site = reasonAt (id 2) ∧
      PrimitiveExpressions.UninitializedAt program context [] source environment (heap none) (id 0) site location := by
  obtain ⟨_, _, tree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique accepted
  obtain ⟨same, result, related, core⟩ := ScalarExpressionReflection.Primitive.source_outcome
    tree unique contextValid covers environments (heaps none) execution
  have resultSame := (Core.evaluation_deterministic core core_failed).1
  cases related with
  | value staged typed => cases resultSame
  | uninitialized site location origin =>
      exact ⟨same, site, location, rfl, Core.Value.word.inj (Core.Value.inLeft.inj resultSame).2, origin⟩

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  assertTrue (Core.runStateful 100 (.initial code coreEnvironment (store (some (word 6)))) ==
    .done (.inRight .word (.word (word 7))) (store (some (word 6))))
    "reflected arithmetic changed the result or administrative closure"
  assertTrue (Core.runStateful 100 (.initial code coreEnvironment (store none)) ==
    .done (.inLeft .word (.word (reasonAt (id 2)))) (store none))
    "reflected read fault changed its leaf reason or administrative closure"

end Tests.SourceCoreScalarExpressionReflection
