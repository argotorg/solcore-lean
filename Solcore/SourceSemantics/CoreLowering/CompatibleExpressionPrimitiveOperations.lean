import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues

/-! Actual Word/Integer compiler bodies agree with independent scalar source
operations. Reversed comparisons reorder already evaluated values only. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference GeneralHeap CompatiblePayload

inductive Mode where
  | word
  | integer
  deriving DecidableEq

def Mode.operandType (mode : Mode) (operator : Syntax.BinaryOp) : Ty :=
  match mode with
  | .word => SourceCorePrimitive.binaryOperandType operator
  | .integer => SourceCoreInteger.binaryOperandType operator

def Mode.resultType (mode : Mode) (operator : Syntax.BinaryOp) : Ty :=
  match mode with
  | .word => SourceCorePrimitive.binaryResultType operator
  | .integer => SourceCoreInteger.binaryResultType operator

def Mode.body (mode : Mode) (operator : Syntax.BinaryOp) : Expr :=
  match mode with
  | .word => SourceCorePrimitive.strictBinaryBody operator
  | .integer => SourceCoreInteger.strictBinaryBody operator

def Mode.binary (mode : Mode) (operator : Syntax.BinaryOp) (left right : Expr) : Expr :=
  match mode with
  | .word => SourceCorePrimitive.binary operator left right
  | .integer => SourceCoreInteger.binary operator left right

def scalarSource : Ty → TypeSystem.Ty
  | .bool => .bool
  | .word => .word
  | .integer => .integer
  | _ => .unit

inductive BinaryProfile : Syntax.BinaryOp → TypeSystem.Ty → TypeSystem.Ty → Mode → Prop where
  | word {operator} (strict : Dynamic.StrictBinaryOperator operator) :
      BinaryProfile operator .word (scalarSource (SourceCorePrimitive.binaryResultType operator)) .word
  | integer {operator} (strict : Dynamic.StrictBinaryOperator operator) :
      BinaryProfile operator .integer (scalarSource (SourceCoreInteger.binaryResultType operator)) .integer
  | logicalAnd : BinaryProfile .logicalAnd .bool .bool .word
  | logicalOr : BinaryProfile .logicalOr .bool .bool .word

theorem BinaryProfile.of_typing {context : SourceSemantics.Context} {operator : Syntax.BinaryOp}
    {operand result : TypeSystem.Ty} (typed : BinaryOperatorHasType context operator operand operand result []) :
    ∃ mode, BinaryProfile operator operand result mode := by
  cases typed with
  | wordArithmetic kind => cases kind <;> exact ⟨_, .word (by constructor)⟩
  | wordComparison kind => cases kind <;> exact ⟨_, .word (by constructor)⟩
  | integerArithmetic kind => cases kind <;> exact ⟨_, .integer (by constructor)⟩
  | integerComparison kind => cases kind <;> exact ⟨_, .integer (by constructor)⟩
  | booleanAnd => exact ⟨_, .logicalAnd⟩
  | booleanOr => exact ⟨_, .logicalOr⟩
  | trait _ profile evidence => cases profile; cases evidence

theorem Mode.binary_strict {operator : Syntax.BinaryOp} (mode : Mode)
    (strict : Dynamic.StrictBinaryOperator operator) (left right : Expr) :
    mode.binary operator left right = LocalPrimitiveResults.binaryWith
      (mode.resultType operator) left right (mode.body operator) := by
  cases mode <;> cases strict <;> rfl

theorem Mode.body_rename (mode : Mode) (operator : Syntax.BinaryOp) (ξ : Renaming) :
    (mode.body operator).rename (Renaming.lift (Renaming.lift ξ)) = mode.body operator := by
  cases mode <;> cases operator <;> rfl

private theorem not_lt (left right : Int) :
    (!decide (left < right)) = decide (right ≤ left) := by
  rw [← decide_not]
  exact decide_eq_decide.mpr Int.not_lt

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

private theorem staged_payload (value : SourceStagedValue.Value) :
    ValueRep checked registry functions mapping world (SourceStagedValue.sourceType value)
      (StagedValue.toSource value) (SourceStagedValue.toCore value) (SourceStagedValue.coreType value) := by
  induction value with
  | unit => exact .unit
  | bool value => exact .bool value
  | word value => exact .word value
  | product _ _ first second => exact .product first second

private theorem staged_scalar_result {operator : Syntax.BinaryOp} {value : SourceStagedValue.Value}
    (typed : SourceStagedValue.coreType value = SourceCorePrimitive.binaryResultType operator) :
    SourceStagedValue.sourceType value = scalarSource (SourceCorePrimitive.binaryResultType operator) := by
  cases operator <;> cases value <;> simp_all [SourceStagedValue.coreType, SourceStagedValue.sourceType,
    SourceCorePrimitive.binaryResultType, scalarSource]

theorem word_body {operator : Syntax.BinaryOp} (strict : Dynamic.StrictBinaryOperator operator) (left right : Word) :
    ∃ sourceResult coreResult,
      Dynamic.BinaryPrimitiveApplies operator (.word left) (.word right) sourceResult ∧
      ValueRep checked registry functions mapping world (scalarSource (SourceCorePrimitive.binaryResultType operator))
        sourceResult coreResult (SourceCorePrimitive.binaryResultType operator) ∧
      ∀ environment store, Evaluates (.word right :: .word left :: environment) store
        (SourceCorePrimitive.strictBinaryBody operator) coreResult store := by
  obtain ⟨result, typed, applied, evaluated⟩ := PrimitiveExpressions.strict_binary_value strict left right
  refine ⟨_, _, applied, ?_, evaluated⟩
  simpa only [typed, staged_scalar_result typed] using (staged_payload (functions := functions) (registry := registry)
    (mapping := mapping) (world := world) result)

theorem integer_body {operator : Syntax.BinaryOp} (strict : Dynamic.StrictBinaryOperator operator) (left right : Int) :
    ∃ sourceResult coreResult,
      Dynamic.BinaryPrimitiveApplies operator (.integer left) (.integer right) sourceResult ∧
      ValueRep checked registry functions mapping world (scalarSource (SourceCoreInteger.binaryResultType operator))
        sourceResult coreResult (SourceCoreInteger.binaryResultType operator) ∧
      ∀ environment store, Evaluates (.integer right :: .integer left :: environment) store
        (SourceCoreInteger.strictBinaryBody operator) coreResult store := by
  cases strict with
  | multiply => exact ⟨_, _, .integerMultiply _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | divide => exact ⟨_, _, IntegerPrimitives.divide_source _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | modulo => exact ⟨_, _, IntegerPrimitives.modulo_source _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | add => exact ⟨_, _, .integerAdd _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | subtract => exact ⟨_, _, .integerSubtract _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | bitAnd => exact ⟨_, _, IntegerPrimitives.bitAnd_source _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | bitXor => exact ⟨_, _, IntegerPrimitives.bitXor_source _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | bitOr => exact ⟨_, _, IntegerPrimitives.bitOr_source _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | less => exact ⟨_, _, .integerLess _ _, .bool _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | greater => exact ⟨_, _, .integerGreater _ _, .bool _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | lessEqual =>
    refine ⟨_, _, .integerLessEqual _ _, .bool _, fun _ _ => .unary (.binary (.var rfl) (.var rfl) rfl) ?_⟩
    simp [UnaryOp.apply, not_lt]
  | greaterEqual =>
    refine ⟨_, _, .integerGreaterEqual _ _, .bool _, fun _ _ => .unary (.binary (.var rfl) (.var rfl) rfl) ?_⟩
    simp [UnaryOp.apply, not_lt]
  | equal =>
    by_cases same : left = right
    · subst right
      exact ⟨_, _, .equalTrue ⟨rfl, .integer _⟩, .bool true,
        fun _ _ => .binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply])⟩
    · exact ⟨_, _, .equalFalse (fun equivalent => same (Dynamic.Value.integer.inj equivalent.1)), .bool false,
        fun _ _ => .binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, beq_eq_false_iff_ne.mpr same])⟩
  | notEqual =>
    by_cases same : left = right
    · subst right
      exact ⟨_, _, .notEqualFalse ⟨rfl, .integer _⟩, .bool false,
        fun _ _ => .unary (.binary (result := .bool true) (.var rfl) (.var rfl) (by simp [BinaryOp.apply])) rfl⟩
    · exact ⟨_, _, .notEqualTrue (fun equivalent => same (Dynamic.Value.integer.inj equivalent.1)), .bool true,
        fun _ _ => .unary (.binary (result := .bool false) (.var rfl) (.var rfl)
          (by simp [BinaryOp.apply, beq_eq_false_iff_ne.mpr same])) rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
