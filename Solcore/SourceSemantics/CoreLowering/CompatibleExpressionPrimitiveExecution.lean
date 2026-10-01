import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveSource

/-! Native helper composition consumes the actual shifted right environment.
The pure operator proof is independent of the heap; operand effects remain in
the supplied finite derivations, in their original order. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference GeneralHeap CompatiblePayload

def Mode.tail (mode : Mode) (operator : Syntax.BinaryOp) (right : Expr) : Expr :=
  match operator with
  | .logicalAnd => .ifE (.var 0) (right.weakenAt 0) (LanguageResult.success (.bool false))
  | .logicalOr => .ifE (.var 0) (LanguageResult.success (.bool true)) (right.weakenAt 0)
  | _ => LanguageResult.bind (mode.resultType operator) (right.weakenAt 0)
      (LanguageResult.success (mode.body operator))

theorem Mode.binary_eq (mode : Mode) (operator : Syntax.BinaryOp) (left right : Expr) :
    mode.binary operator left right = .caseE left
      (.inLeft (mode.resultType operator) (.var 0)) (mode.tail operator right) := by
  cases mode <;> cases operator <;> simp [Mode.binary, Mode.tail, Mode.resultType, Mode.body, SourceCorePrimitive.binaryResultType, SourceCoreInteger.binaryResultType, SourceCorePrimitive.binary, SourceCoreInteger.binary, LocalPrimitiveResults.logicalAnd, LocalPrimitiveResults.logicalOr, LocalPrimitiveResults.binaryWith, LocalControl.choose, LanguageResult.bind, LanguageResult.success, Expr.weakenAt]

theorem Mode.binary_rename (mode : Mode) (operator : Syntax.BinaryOp) (left right : Expr) (ξ : Renaming) :
    (mode.binary operator left right).rename ξ = mode.binary operator (left.rename ξ) (right.rename ξ) := by
  cases mode <;> cases operator <;>
    simp [Mode.binary, SourceCorePrimitive.binary, SourceCoreInteger.binary,
      LocalPrimitiveResults.binaryWith, LocalPrimitiveResults.logicalAnd, LocalPrimitiveResults.logicalOr,
      LocalControl.choose, LanguageResult.bind, LanguageResult.success, Expr.rename,
      Expr.weakenAt, SourceCorePrimitive.strictBinaryBody, SourceCoreInteger.strictBinaryBody, Renaming.lift]


variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping} {operator : Syntax.BinaryOp}
  {operand result : TypeSystem.Ty} {mode : Mode} {a b : Dynamic.Value} {x y : Value}

theorem BinaryProfile.left_progress (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked registry functions mapping world operand a x (mode.operandType operator)) :
    (∃ output, Dynamic.ShortCircuits operator a output) ∨ Dynamic.EvaluatesRightOperand operator a := by
  cases profile with
  | word strict => exact .inr (.strict strict)
  | integer strict => exact .inr (.strict strict)
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases boolean
    · exact .inl ⟨_, .andFalse⟩
    · exact .inr .andTrue
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases boolean
    · exact .inr .orFalse
    · exact .inl ⟨_, .orTrue⟩

theorem BinaryProfile.left_valid (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked registry functions mapping world operand a x (mode.operandType operator)) :
    ¬ Dynamic.BinaryLeftOperandInvalid operator a := by
  intro invalid
  cases profile with
  | word strict => cases invalid <;> cases strict
  | integer strict => cases invalid <;> cases strict
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases invalid with | logicalAnd invalid => exact invalid trivial
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases invalid with | logicalOr invalid => exact invalid trivial

theorem Mode.left_failure {environment : Environment} {before after : Store} {left right : Expr} {reason : Word}
    (mode : Mode) (operator : Syntax.BinaryOp)
    (evaluated : Evaluates environment before left (.inLeft (mode.operandType operator) (.word reason)) after) :
    Evaluates environment before (mode.binary operator left right) (.inLeft (mode.resultType operator) (.word reason)) after := by
  cases mode <;> cases operator <;> first
    | exact LocalPrimitiveResults.logicalAnd_failure evaluated
    | exact LocalPrimitiveResults.logicalOr_failure evaluated
    | exact LocalPrimitiveResults.binaryWith_left_failure evaluated

theorem BinaryProfile.short {environment : Environment} {before after : Store} {left right : Expr} {output : Dynamic.Value}
    (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked registry functions mapping world operand a x (mode.operandType operator))
    (circuit : Dynamic.ShortCircuits operator a output)
    (evaluated : Evaluates environment before left (.inRight .word x) after) :
    ∃ value, ValueRep checked registry functions mapping world result output value (mode.resultType operator) ∧
      Evaluates environment before (mode.binary operator left right) (.inRight .word value) after := by
  cases profile with
  | word strict => cases circuit <;> cases strict
  | integer strict => cases circuit <;> cases strict
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases circuit
    exact ⟨_, .bool false, LocalPrimitiveResults.logicalAnd_shortCircuit evaluated⟩
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases circuit
    exact ⟨_, .bool true, LocalPrimitiveResults.logicalOr_shortCircuit evaluated⟩

theorem BinaryProfile.right_failure {environment : Environment} {before middle after : Store}
    {left right : Expr} {reason : Word}
    (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked registry functions mapping world operand a x (mode.operandType operator))
    (continues : Dynamic.EvaluatesRightOperand operator a)
    (first : Evaluates environment before left (.inRight .word x) middle)
    (second : Evaluates (x :: environment) middle (right.weakenAt 0) (.inLeft (mode.operandType operator) (.word reason)) after) :
    Evaluates environment before (mode.binary operator left right) (.inLeft (mode.resultType operator) (.word reason)) after := by
  cases profile with
  | word strict => rw [Mode.binary_strict _ strict]; exact LocalPrimitiveResults.binaryWith_right_failure first second
  | integer strict => rw [Mode.binary_strict _ strict]; exact LocalPrimitiveResults.binaryWith_right_failure first second
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict => cases strict
    | andTrue => exact LocalPrimitiveResults.logicalAnd_right first second
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict => cases strict
    | orFalse => exact LocalPrimitiveResults.logicalOr_right first second

theorem BinaryProfile.right_success {environment : Environment} {before middle after : Store} {left right : Expr}
    (profile : BinaryProfile operator operand result mode)
    (leftRep : ValueRep checked registry functions mapping world operand a x (mode.operandType operator))
    (rightRep : ValueRep checked registry functions mapping world operand b y (mode.operandType operator))
    (continues : Dynamic.EvaluatesRightOperand operator a)
    (first : Evaluates environment before left (.inRight .word x) middle)
    (second : Evaluates (x :: environment) middle (right.weakenAt 0) (.inRight .word y) after) :
    ∃ sourceResult coreResult, Dynamic.BinaryPrimitiveApplies operator a b sourceResult ∧
      ValueRep checked registry functions mapping world result sourceResult coreResult (mode.resultType operator) ∧
      Evaluates environment before (mode.binary operator left right) (.inRight .word coreResult) after := by
  cases profile with
  | word strict =>
    have operandEq := PrimitiveExpressions.strict_operand_word strict
    obtain ⟨a, rfl, rfl⟩ := word_fields (by simpa only [Mode.operandType, operandEq] using leftRep)
    obtain ⟨b, rfl, rfl⟩ := word_fields (by simpa only [Mode.operandType, operandEq] using rightRep)
    obtain ⟨sourceResult, coreResult, applied, represented, body⟩ := word_body (functions := functions) (registry := registry)
      (mapping := mapping) (world := world) strict a b
    exact ⟨sourceResult, coreResult, applied, represented, by
      rw [Mode.binary_strict _ strict]
      exact LocalPrimitiveResults.binaryWith_success first second (body _ _)⟩
  | integer strict =>
    have operandEq : SourceCoreInteger.binaryOperandType operator = .integer := by cases strict <;> rfl
    obtain ⟨a, rfl, rfl⟩ := integer_fields (by simpa only [Mode.operandType, operandEq] using leftRep)
    obtain ⟨b, rfl, rfl⟩ := integer_fields (by simpa only [Mode.operandType, operandEq] using rightRep)
    obtain ⟨sourceResult, coreResult, applied, represented, body⟩ := integer_body (functions := functions) (registry := registry)
      (mapping := mapping) (world := world) strict a b
    exact ⟨sourceResult, coreResult, applied, represented, by
      rw [Mode.binary_strict _ strict]
      exact LocalPrimitiveResults.binaryWith_success first second (body _ _)⟩
  | logicalAnd =>
    obtain ⟨a, rfl, rfl⟩ := bool_fields leftRep
    obtain ⟨b, rfl, rfl⟩ := bool_fields rightRep
    cases continues with
    | strict strict => cases strict
    | andTrue => exact ⟨_, _, .logicalAnd true b, .bool b, LocalPrimitiveResults.logicalAnd_right first second⟩
  | logicalOr =>
    obtain ⟨a, rfl, rfl⟩ := bool_fields leftRep
    obtain ⟨b, rfl, rfl⟩ := bool_fields rightRep
    cases continues with
    | strict strict => cases strict
    | orFalse => exact ⟨_, _, .logicalOr false b, .bool b, LocalPrimitiveResults.logicalOr_right first second⟩


/-- In a branch selected by the independent left-value rule, native completion
contains a real right-operand derivation at the single inserted payload slot. -/
theorem BinaryProfile.right_evaluated {environment : Environment} {before after : Store} {right : Expr} {value : Value}
    (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked registry functions mapping world operand a x (mode.operandType operator))
    (continues : Dynamic.EvaluatesRightOperand operator a)
    (evaluated : Evaluates (x :: environment) before (mode.tail operator right) value after) :
    ∃ rightValue rightStore, Evaluates (x :: environment) before (right.weakenAt 0) rightValue rightStore := by
  cases profile with
  | word strict => cases strict <;> cases evaluated <;> exact ⟨_, _, by assumption⟩
  | integer strict => cases strict <;> cases evaluated <;> exact ⟨_, _, by assumption⟩
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict => cases strict
    | andTrue =>
      cases evaluated with
      | ifTrue condition right =>
        obtain ⟨_, rfl⟩ := evaluation_deterministic condition (Evaluates.var rfl)
        exact ⟨_, _, right⟩
      | ifFalse condition right =>
        have same := (evaluation_deterministic condition (Evaluates.var rfl)).1
        cases same
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict => cases strict
    | orFalse =>
      cases evaluated with
      | ifFalse condition right =>
        obtain ⟨_, rfl⟩ := evaluation_deterministic condition (Evaluates.var rfl)
        exact ⟨_, _, right⟩
      | ifTrue condition right =>
        have same := (evaluation_deterministic condition (Evaluates.var rfl)).1
        cases same

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
