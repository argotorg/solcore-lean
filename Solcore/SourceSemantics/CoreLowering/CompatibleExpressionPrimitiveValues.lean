import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductMeaning
import Solcore.SourceSemantics.CoreLowering.PrimitiveOperations
import Solcore.SourceSemantics.CoreLowering.IntegerPrimitives
import Solcore.Frontend.SourceCoreInteger

/-! Scalar inversion for the compatible payload relation and the exact pure
primitive bodies emitted by the ordinary compiler. Function authentication is
not an additional premise: its projected product carrier cannot be a scalar.
All typing refers to the actual ambient definitions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference GeneralHeap CompatiblePayload

private def ScalarFields (source : Dynamic.Value) (value : Value) : Ty → Prop
  | .bool => ∃ boolean, source = .bool boolean ∧ value = .bool boolean
  | .word => ∃ word, source = .word word ∧ value = .word word
  | .integer => ∃ integer, source = .integer integer ∧ value = .integer integer
  | _ => True

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
  {source : Dynamic.Value} {value : Value} {type : Ty}

private theorem scalar_fields (represented : ValueRep checked registry functions mapping world sourceType source value type) :
    ScalarFields source value type := by
  induction represented using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | product | proxy | constructed | mappingValue => trivial
  | bool boolean => exact ⟨boolean, rfl, rfl⟩
  | word word => exact ⟨word, rfl, rfl⟩
  | integer integer => exact ⟨integer, rfl, rfl⟩
  | @function parameter result source value type related =>
    have projected := functions.projection related
    simp only [SourceCoreCompatibleCatalog.Catalog.project] at projected
    cases parameterEq : checked.catalog.project parameter with
    | error error => simp [parameterEq, bind, Except.bind] at projected
    | ok parameter =>
      cases resultEq : checked.catalog.project result with
      | error error => simp [parameterEq, resultEq, bind, Except.bind] at projected
      | ok result =>
        simp only [parameterEq, resultEq, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at projected
        subst type
        unfold SourceCoreCompatibleCatalog.Catalog.functionType
        split <;> trivial
  | compatible _ _ ih => exact ih
  | nil | cons | empty | entry | absent | present => trivial

theorem bool_fields (represented : ValueRep checked registry functions mapping world sourceType source value .bool) :
    ∃ boolean, source = .bool boolean ∧ value = .bool boolean := scalar_fields represented

theorem word_fields (represented : ValueRep checked registry functions mapping world sourceType source value .word) :
    ∃ word, source = .word word ∧ value = .word word := scalar_fields represented

theorem integer_fields (represented : ValueRep checked registry functions mapping world sourceType source value .integer) :
    ∃ integer, source = .integer integer ∧ value = .integer integer := scalar_fields represented

/-- Empty evidence admits exactly these scalar unary profiles. -/
inductive UnaryProfile : Syntax.UnaryOp → TypeSystem.Ty → TypeSystem.Ty → UnaryOp → Prop where
  | logicalNot : UnaryProfile .logicalNot .bool .bool .boolNot
  | wordNot : UnaryProfile .bitNot .word .word .wordNot
  | integerNot : UnaryProfile .bitNot .integer .integer .integerNot

theorem UnaryProfile.of_typing {context : SourceSemantics.Context} {operator : Syntax.UnaryOp}
    {operand result : TypeSystem.Ty} (typed : UnaryOperatorHasType context operator operand result []) :
    ∃ core, UnaryProfile operator operand result core := by
  cases typed with
  | logicalNot => exact ⟨_, .logicalNot⟩
  | wordBitNot => exact ⟨_, .wordNot⟩
  | integerBitNot => exact ⟨_, .integerNot⟩
  | trait _ profile evidence => cases profile; cases evidence

theorem UnaryProfile.preserves {operator : Syntax.UnaryOp} {operand result : TypeSystem.Ty} {core : UnaryOp}
    (profile : UnaryProfile operator operand result core)
    (represented : ValueRep checked registry functions mapping world operand source value core.operandType) :
    ∃ sourceResult coreResult,
      Dynamic.UnaryPrimitiveApplies operator source sourceResult ∧ core.apply value = some coreResult ∧
      ValueRep checked registry functions mapping world result sourceResult coreResult core.resultType := by
  cases profile with
  | logicalNot =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    exact ⟨_, _, .logicalNot boolean, rfl, .bool _⟩
  | wordNot =>
    obtain ⟨word, rfl, rfl⟩ := word_fields represented
    exact ⟨_, _, .wordBitNot word, rfl, .word _⟩
  | integerNot =>
    obtain ⟨integer, rfl, rfl⟩ := integer_fields represented
    exact ⟨_, _, .integerBitNot integer, rfl, .integer _⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
