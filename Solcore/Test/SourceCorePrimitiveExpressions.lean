import Solcore.SourceSemantics.CoreLowering.PrimitiveExpressions

/-! Kernel-checked regression examples use actual accepted compiler output.
The retained integer evidence is validated independently, and short-circuit
fault reasons are attached to the executed local read occurrence. -/

set_option autoImplicit false

namespace Tests.SourceCorePrimitiveExpressions

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"primitive_expressions", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "primitive_expressions.solc" }
  startByte := 0, endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (site : ExpressionId) : Core.Word := word (100 + site.occurrence.index)
private def scope : SourceCoreBasic.Scope := [(binder 0, .bool), (binder 1, .word), (binder 2, .bool)]
private def node (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := id index, span, type, form }
private def literalRequirement : SolvedRequirement := {
  id := ⟨0⟩, predicate := ProgramSignatures.builtinIntPredicate .word
  evidence := .implementation (.byImpl (ProgramSignatures.builtinIntPredicate .word) (.builtin .intWord) [])
}
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [literalRequirement] }
private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def context : SourceSemantics.Context :=
  (Context.ofSignatures signatures).withSolvedRequirements [literalRequirement]
private theorem contextValid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.withSolvedRequirements]
  · intro requirement member
    have same : requirement = literalRequirement := by simpa [context, Context.withSolvedRequirements] using member
    subst requirement
    apply SolvedRequirementValid.intro
    apply RetainedEvidenceValid.intro
    · exact .implementation (.byImpl .nil)
    · apply EvidenceValid.implementation (rule := ProgramSignatures.builtinIntWordRule)
      · simp [context, Context.withSolvedRequirements, Context.ofSignatures,
          ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]
      · rfl
      · refine .intro { parameters := [], variables := [] } ?_ rfl rfl
        exact ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩
      · exact .nil
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
    .expression {
      id := id 5, span, type := .word
      form := .integerLiteral (.decimal "17") { rawValue := 17, targetType := .word, requirement := ⟨0⟩ }
      requirements := [⟨0⟩] },
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

example : Core.HasType (SourceCoreLocalCell.coreContext scope) code
    (Core.LanguageResult.resultType (.product .word .bool)) :=
  PrimitiveExpressions.lowerExpression_hasType unique accepted

/-- Integer metadata retains its one requirement; it is not coerced to the
empty-requirement metadata used by ordinary primitive nodes. -/
example : ∃ literalNode, source.lookupExpression? (id 5) = some literalNode ∧
    PrimitiveExpressions.RootMetadata source (id 5) literalNode .word :=
  PrimitiveExpressions.lowerExpression_metadata unique (show
    SourceCorePrimitive.lowerExpressionWithReasons 1 compilation source scope (id 5) reasonAt =
      .ok ⟨.word, Core.LanguageResult.success (.word (word 17))⟩ from rfl)

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
private def store (flag : Option Bool) (number : Option Nat) (right : Option Bool) : Core.Store :=
  [boolStored flag, wordStored number, boolStored right]
private def world : Core.StoreTyping :=
  [Core.OptionalCell.cellType .bool, Core.OptionalCell.cellType .word, Core.OptionalCell.cellType .bool]
private def environment : Dynamic.Environment := [(binder 0, ⟨0⟩), (binder 1, ⟨1⟩), (binder 2, ⟨2⟩)]
private def coreEnvironment : Core.Environment :=
  [.cellRef (Core.OptionalCell.cellType .bool) 0,
    .cellRef (Core.OptionalCell.cellType .word) 1, .cellRef (Core.OptionalCell.cellType .bool) 2]
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
private theorem heaps (flag : Option Bool) (number : Option Nat) (right : Option Bool) :
    LocalCell.HeapRepresents (heap flag number right).cells (store flag number right) world :=
  .cons (boolRelated flag) (.cons (wordRelated number) (.cons (boolRelated right) .nil))

/-- Accepted lowering, ordinary input representation, and the independently
proved ledger validity suffice. No source or Core child execution is assumed. -/
example (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (flag : Option Bool) (number : Option Nat) (right : Option Bool) :
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment
        (heap flag number right) (id 0) sourceOutcome (heap flag number right) ∧
      PrimitiveExpressions.OutcomeRepresents program context evidence source environment
        (heap flag number right) reasonAt (id 0) (.product .word .bool) sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment (store flag number right)) =
        .done coreValue (store flag number right)) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment (store flag number right)) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store flag number right) :=
  (PrimitiveExpressions.lowerExpression_run_preserves unique accepted program context evidence contextValid
    environments (heaps flag number right)).2

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

/-- The concrete short-circuit machine observation also reflects to a related
independent source outcome, using the accepted compiler preservation theorem. -/
example (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ∃ sourceOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment
        (heap (some true) (some 3) none) (id 0) sourceOutcome (heap (some true) (some 3) none) ∧
      PrimitiveExpressions.OutcomeRepresents program context evidence source environment
        (heap (some true) (some 3) none) reasonAt (id 0) (.product .word .bool) sourceOutcome
        (.inRight .word (.pair (.word (word 20)) (.bool false))) := by
  obtain ⟨sourceOutcome, coreValue, evaluation, related, coreEvaluation⟩ :=
    PrimitiveExpressions.lowerExpression_preserves unique accepted program context evidence contextValid
      environments (heaps (some true) (some 3) none)
  have same := Core.evaluation_deterministic (Core.runStateful_evaluation_sound run_shortCircuit) coreEvaluation
  exact ⟨sourceOutcome, evaluation, same.1 ▸ related⟩

/-- Missing literal evidence and insufficient traversal fuel cannot yield a
certificate. The rejected branch is exercised by the actual compiler. -/
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCorePrimitive.lowerExpressionWithReasons 5 { solvedRequirements := [] } source scope (id 0) reasonAt ≠ .ok output := by
  intro impossible
  cases impossible
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCorePrimitive.lowerExpressionWithReasons 4 compilation source scope (id 0) reasonAt ≠ .ok output := by
  intro impossible
  cases impossible

private def sourceResultType : Syntax.BinaryOp → TypeSystem.Ty
  | .multiply | .divide | .modulo | .add | .subtract | .bitAnd | .bitXor | .bitOr => .word
  | _ => .bool
private def operatorSource (operator : Syntax.BinaryOp) : TypedSource := {
  owner, inputs := [], roots := [.expression (id 0)]
  nodes := [node 0 (sourceResultType operator) (.binary (id 1) operator (id 2)),
    node 1 .word (.literal (.decimal "7")), node 2 .word (.literal (.decimal "0"))]
}
private def operatorCode (operator : Syntax.BinaryOp) : Core.Expr :=
  SourceCorePrimitive.binary operator (Core.LanguageResult.success (.word (word 7)))
    (Core.LanguageResult.success (.word (word 0)))
private theorem operatorAccepted (operator : Syntax.BinaryOp) (strict : Dynamic.StrictBinaryOperator operator) :
    SourceCorePrimitive.lowerExpressionWithReasons 2 compilation (operatorSource operator) [] (id 0) reasonAt =
      .ok ⟨SourceCorePrimitive.binaryResultType operator, operatorCode operator⟩ := by
  cases strict <;> rfl
private theorem operatorUnique (operator : Syntax.BinaryOp) : NodeOccurrencesUnique (operatorSource operator) := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  cases operator <;> decide

/-- All fourteen strict Word operators pass through the real compiler and the
same independently proved semantic bridge, including swapped comparisons. -/
example (operator : Syntax.BinaryOp) (strict : Dynamic.StrictBinaryOperator operator)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence (operatorSource operator) [] ⟨[]⟩
        (id 0) sourceOutcome ⟨[]⟩ ∧
      PrimitiveExpressions.OutcomeRepresents program context evidence (operatorSource operator) [] ⟨[]⟩ reasonAt
        (id 0) (SourceCorePrimitive.binaryResultType operator) sourceOutcome coreValue ∧
      Core.Evaluates [] [] (operatorCode operator) coreValue [] :=
  PrimitiveExpressions.lowerExpression_preserves (operatorUnique operator) (operatorAccepted operator strict)
    program context evidence contextValid LocalCell.EnvRepresents.nil LocalCell.HeapRepresents.nil

/-- Word division and remainder by zero have defined Word results in both
semantics; these are successful language results, not missing-carrier faults. -/
example : Core.runStateful 80 (.initial (operatorCode .divide) [] []) =
    .done (.inRight .word (.word (word 0))) [] := by
  simp [operatorCode, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LanguageResult.bind, Core.LanguageResult.success, Core.Expr.weakenAt]
  rfl
example : Core.runStateful 80 (.initial (operatorCode .modulo) [] []) =
    .done (.inRight .word (.word (word 0))) [] := by
  simp [operatorCode, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LanguageResult.bind, Core.LanguageResult.success, Core.Expr.weakenAt]
  rfl
example : Core.runStateful 80 (.initial (operatorCode .lessEqual) [] []) =
    .done (.inRight .word (.bool false)) [] := by
  simp [operatorCode, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LanguageResult.bind, Core.LanguageResult.success, Core.Expr.weakenAt]
  rfl
example : Core.runStateful 80 (.initial (operatorCode .notEqual) [] []) =
    .done (.inRight .word (.bool true)) [] := by
  simp [operatorCode, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LanguageResult.bind, Core.LanguageResult.success, Core.Expr.weakenAt]
  rfl

private def wrongOperands : TypedSource := {
  owner, inputs := [], roots := [.expression (id 0)]
  nodes := [node 0 .word (.binary (id 1) .add (id 2)),
    node 1 .bool (.reference "true" (.builtinBoolean true)), node 2 .word (.literal (.decimal "0"))]
}
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCorePrimitive.lowerExpressionWithReasons 2 compilation wrongOperands [] (id 0) reasonAt ≠ .ok output := by
  intro impossible
  cases impossible

end Tests.SourceCorePrimitiveExpressions
