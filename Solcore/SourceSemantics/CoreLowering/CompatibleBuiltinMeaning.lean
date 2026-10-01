import Solcore.SourceSemantics.CoreLowering.BuiltinBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier

/-! The compatible argument payloads select the real packed input of every
builtin. Independent source primitive results enter the existing full payload
relation. Argument effects and callable gates remain the caller's boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBuiltinMeaning
open Core Frontend SourceInference GeneralHeap CompatiblePayload DataPatternValues
open BuiltinBodyMeaning

def argumentTypes : BuiltinFunctionId → List Ty
  | .wordToInteger => [.word]
  | .wordFromInteger => [.integer]
  | _ => [.integer, .integer]

theorem argumentTypes_project {checked : SourceCoreCompatibleCatalog.Checked}
    (function : BuiltinFunctionId) :
    function.parameterTypes.mapM checked.catalog.project = .ok (argumentTypes function) := by
  cases function <;> rfl

theorem argumentTypes_pack (function : BuiltinFunctionId) :
    SourceCoreCompatibleCatalog.packTypes (argumentTypes function) = SourceCoreInteger.builtinParameter function := by
  cases function <;> rfl

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping} {identities : Dynamic.Value → Word → Prop}

/-- Exact scalar values follow from the common compatible relation, including
its metadata compatibility constructor. No input codec or source evaluator is used. -/
theorem input_of_values
    (observations : CompatibleEquality.FunctionObservations checked.catalog functions identities)
    {function : BuiltinFunctionId} {arguments : List Dynamic.Value} {values : List Value}
    (represented : ValuesRep checked registry functions mapping world function.parameterTypes arguments values
      (argumentTypes function)) :
    InputRep function arguments (packValues values) := by
  cases function
  all_goals cases represented with
  | cons head tail =>
    first
    | obtain ⟨value, rfl, rfl⟩ := CompatiblePlaceModifier.word_fields observations head
      cases tail
      exact .wordToInteger value
    | obtain ⟨left, rfl, rfl⟩ := CompatiblePlaceModifier.integer_fields observations head
      cases tail with
      | nil => exact .wordFromInteger left
    | obtain ⟨left, rfl, rfl⟩ := CompatiblePlaceModifier.integer_fields observations head
      cases tail with
      | cons rightRep rest =>
        obtain ⟨right, rfl, rfl⟩ := CompatiblePlaceModifier.integer_fields observations rightRep
        cases rest
        first
        | exact .integerSub left right
        | exact .integerAdd left right
        | exact .integerEq left right
        | exact .integerLt left right
        | exact .integerMul left right

theorem result_represents {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (inputs : InputRep function arguments input)
    {sourceResult : Dynamic.Value} {nativeResult : Value}
    (applied : Dynamic.BuiltinApplies function arguments sourceResult)
    (represented : IntegerPrimitives.ResultRepresents sourceResult nativeResult) :
    ValueRep checked registry functions mapping world function.returnType sourceResult nativeResult
      (SourceCoreInteger.builtinResult function) := by
  cases inputs <;> cases applied <;> cases represented <;> first
    | exact .integer _
    | exact .bool _
    | exact .word _

/-- The actual compiler body preserves independent source application and
keeps the whole native store supplied after argument evaluation unchanged. -/
theorem preserves
    (observations : CompatibleEquality.FunctionObservations checked.catalog functions identities)
    {function : BuiltinFunctionId} {arguments : List Dynamic.Value} {values : List Value}
    (represented : ValuesRep checked registry functions mapping world function.parameterTypes arguments values
      (argumentTypes function))
    {sourceResult : Dynamic.Value} (application : Dynamic.BuiltinApplies function arguments sourceResult)
    (captured : Environment) (store : Store) :
    ∃ nativeResult,
      ValueRep checked registry functions mapping world function.returnType sourceResult nativeResult
        (SourceCoreInteger.builtinResult function) ∧
      Evaluates (packValues values :: captured) store
        (LanguageResult.success (SourceCoreInteger.builtinBody function))
        (.inRight .word nativeResult) store := by
  have inputs := input_of_values observations represented
  obtain ⟨actualSource, nativeResult, applied, related, evaluated⟩ := inputs.body_meaning captured store
  have same := applied.functional application
  subst actualSource
  exact ⟨nativeResult, result_represents inputs application related, evaluated⟩

/-- A completed actual builtin body constructs the independent source
application and its compatible result, without assuming a source execution. -/
theorem reflects
    (observations : CompatibleEquality.FunctionObservations checked.catalog functions identities)
    {function : BuiltinFunctionId} {arguments : List Dynamic.Value} {values : List Value}
    (represented : ValuesRep checked registry functions mapping world function.parameterTypes arguments values
      (argumentTypes function))
    {captured : Environment} {store finalStore : Store} {result : Value}
    (completed : Evaluates (packValues values :: captured) store
      (LanguageResult.success (SourceCoreInteger.builtinBody function)) result finalStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      ValueRep checked registry functions mapping world function.returnType sourceResult nativeResult
        (SourceCoreInteger.builtinResult function) ∧
      result = .inRight .word nativeResult ∧ finalStore = store := by
  have inputs := input_of_values observations represented
  obtain ⟨sourceResult, nativeResult, applied, related, resultEq, storeEq⟩ := inputs.body_reflects completed
  exact ⟨sourceResult, nativeResult, applied, result_represents inputs applied related, resultEq, storeEq⟩
end Solcore.SourceSemantics.CoreLowering.CompatibleBuiltinMeaning
