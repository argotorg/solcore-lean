import Solcore.Frontend.SourceRuntimeProperties
import Solcore.Frontend.SourceRuntimeStaticInversionProperties
import Solcore.Frontend.SourceRuntimeStaticOperatorProperties

/-! Deep typing bridges for graph values and lexical environments. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

/-- The graph relation extends Core deep typing without losing the original
Core closure and cell-world evidence. -/
theorem Value.GraphHasType.ofCore
    {program : Program} {world : Core.StoreTyping}
    {core : Core.Value} {expected : Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : Core.RuntimeValueHasType world core expected definitions) :
    Value.GraphHasType program world (Value.ofCore core) expected definitions := by
  apply Value.GraphHasType.core (Value.toCore?_ofCore core) typing
  have shallow := Value.hasType_of_toCore? program (Value.ofCore core) core
    (Value.toCore?_ofCore core)
  simpa [typing.type_eq] using shallow

/-- A successful Core projection of a deeply typed graph value is itself
deeply typed, including pairs and sums assembled by graph evaluation. -/
theorem Value.GraphHasType.toCore
    {program : Program} {world : Core.StoreTyping}
    {value : Value} {expected : Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : Value.GraphHasType program world value expected definitions) :
    ∀ {core : Core.Value}, value.toCore? = some core →
      Core.RuntimeValueHasType world core expected definitions := by
  induction typing using Value.GraphHasType.rec
      (motive_2 := fun _ _ _ _ => True) with
  | core projection coreTyping _ =>
      intro core projected
      rw [projection] at projected
      cases projected
      exact coreTyping
  | pair leftTyping rightTyping leftIH rightIH =>
      rename_i leftValue rightValue leftType rightType
      intro core projected
      cases leftProjection : leftValue.toCore? with
      | none => simp [Value.toCore?, leftProjection] at projected
      | some coreLeft =>
          cases rightProjection : rightValue.toCore? with
          | none =>
              simp [Value.toCore?, leftProjection, rightProjection] at projected
          | some coreRight =>
              simp [Value.toCore?, leftProjection, rightProjection] at projected
              cases projected
              exact .pair (leftIH leftProjection) (rightIH rightProjection)
  | inLeft payloadTyping payloadIH =>
      rename_i payloadValue leftType rightType
      intro core projected
      cases payloadProjection : payloadValue.toCore? with
      | none => simp [Value.toCore?, payloadProjection] at projected
      | some corePayload =>
          simp [Value.toCore?, payloadProjection] at projected
          cases projected
          exact .inLeft (payloadIH payloadProjection)
  | inRight payloadTyping payloadIH =>
      rename_i payloadValue leftType rightType
      intro core projected
      cases payloadProjection : payloadValue.toCore? with
      | none => simp [Value.toCore?, payloadProjection] at projected
      | some corePayload =>
          simp [Value.toCore?, payloadProjection] at projected
          cases projected
          exact .inRight (payloadIH payloadProjection)
  | sourceClosure =>
      intro core projected
      simp [Value.toCore?] at projected
  | global =>
      intro core projected
      simp [Value.toCore?] at projected
  | nil => trivial
  | cons => trivial

/-- Deep typing of a graph pair can always be inverted, even when the pair
entered through a single Core projection rather than the graph constructor. -/
theorem Value.GraphHasType.pairComponents
    {program : Program} {world : Core.StoreTyping}
    {left right : Value} {leftType rightType : Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : Value.GraphHasType program world (.pair left right)
      (.product leftType rightType) definitions) :
    Value.GraphHasType program world left leftType definitions ∧
    Value.GraphHasType program world right rightType definitions := by
  cases typing with
  | pair leftTyping rightTyping =>
      exact ⟨leftTyping, rightTyping⟩
  | core projection coreTyping _ =>
      cases leftProjection : left.toCore? with
      | none => simp [Value.toCore?, leftProjection] at projection
      | some coreLeft =>
          cases rightProjection : right.toCore? with
          | none =>
              simp [Value.toCore?, leftProjection, rightProjection]
                at projection
          | some coreRight =>
              simp [Value.toCore?, leftProjection, rightProjection]
                at projection
              cases projection
              cases coreTyping with
              | pair coreLeftTyping coreRightTyping =>
                  have leftShallow := Value.hasType_of_toCore? program left
                    coreLeft leftProjection
                  have rightShallow := Value.hasType_of_toCore? program right
                    coreRight rightProjection
                  exact ⟨.core leftProjection coreLeftTyping
                    (by simpa [coreLeftTyping.type_eq] using leftShallow),
                    .core rightProjection coreRightTyping
                    (by simpa [coreRightTyping.type_eq] using rightShallow)⟩

/-- Projecting a graph value accepted through the Core boundary recovers the
same deep Core judgement. -/
theorem Value.GraphHasType.coreProjection
    {program : Program} {world : Core.StoreTyping}
    {value : Value} {expected : Core.Ty}
    {definitions : Core.DataEnvironment}
    (projected : value.RuntimeHasType world expected definitions) :
    value.GraphHasType program world expected definitions := by
  obtain ⟨core, projection, coreTyping⟩ := projected
  exact .core projection coreTyping
    (Value.RuntimeHasType.hasType ⟨core, projection, coreTyping⟩ program)

inductive EnvironmentShallowMatches (program : Program) :
    Environment → StaticContext → Prop where
  | nil : EnvironmentShallowMatches program [] []
  | cons {id : Resolved.LocalId} {value : Value}
      {staticType : StaticType} {environment : Environment}
      {context : StaticContext} :
      Value.HasType program value staticType.erase →
      EnvironmentShallowMatches program environment context →
      EnvironmentShallowMatches program ((id, value) :: environment)
        ((id, staticType) :: context)

/-- Deep lexical-environment typing implies a pointwise shallow context
agreement, including the identity of every captured local. -/
theorem EnvironmentGraphHasTypes.shallow
    {program : Program} {world : Core.StoreTyping}
    {environment : Environment} {context : StaticContext}
    {definitions : Core.DataEnvironment}
    (typing : EnvironmentGraphHasTypes program world environment context
      definitions) :
    EnvironmentShallowMatches program environment context := by
  induction typing using EnvironmentGraphHasTypes.rec
      (motive_1 := fun _ _ _ _ => True) with
  | core | pair | inLeft | inRight | sourceClosure | global => trivial
  | nil => exact .nil
  | cons head _ _ tailIH =>
      exact .cons head.hasType tailIH

/-- Extending a well-typed heap cannot invalidate a graph value, including a
source closure with captured cell references. -/
theorem Value.GraphHasType.weaken
    {program : Program} {initial future : Core.StoreTyping}
    (extension : Core.WorldExtends initial future)
    {value : Value} {expected : Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : Value.GraphHasType program initial value expected definitions) :
    Value.GraphHasType program future value expected definitions := by
  apply Value.GraphHasType.rec
      (motive_1 := fun value expected definitions _ =>
        Value.GraphHasType program future value expected definitions)
      (motive_2 := fun environment context definitions _ =>
        EnvironmentGraphHasTypes program future environment context definitions)
      (t := typing)
  case core =>
    intro _ _ _ _ projection coreTyping shallow
    exact .core projection (coreTyping.weaken extension) shallow
  case pair =>
    intro _ _ _ _ _ _ _ leftIH rightIH
    exact .pair leftIH rightIH
  case inLeft =>
    intro _ _ _ _ _ payloadIH
    exact .inLeft payloadIH
  case inRight =>
    intro _ _ _ _ _ payloadIH
    exact .inRight payloadIH
  case sourceClosure =>
    intro _ _ _ _ _ _ _ bodyTyping environmentIH
    exact .sourceClosure environmentIH bodyTyping
  case global =>
    intro _ _ _ wellTyped found
    exact .global wellTyped found
  case nil =>
    intro _
    exact .nil
  case cons =>
    intro _ _ _ _ _ _ _ _ headIH tailIH
    exact .cons headIH tailIH

/-- Lexical environments captured by source closures remain valid when the
heap world grows during later evaluation. -/
theorem EnvironmentGraphHasTypes.weaken
    {program : Program} {initial future : Core.StoreTyping}
    (extension : Core.WorldExtends initial future)
    {environment : Environment} {context : StaticContext}
    {definitions : Core.DataEnvironment}
    (typing : EnvironmentGraphHasTypes program initial environment context
      definitions) :
    EnvironmentGraphHasTypes program future environment context definitions := by
  induction environment generalizing context with
  | nil =>
      cases typing
      exact .nil
  | cons entry rest ih =>
      cases typing with
      | cons head tail =>
          exact .cons (head.weaken extension) (ih tail)

theorem Value.GraphHasType.unit
    (program : Program) (world : Core.StoreTyping)
    (definitions : Core.DataEnvironment := []) :
    Value.GraphHasType program world .unit .unit definitions :=
  Value.GraphHasType.ofCore Core.RuntimeValueHasType.unit

theorem Value.GraphHasType.bool
    (program : Program) (world : Core.StoreTyping) (value : Bool)
    (definitions : Core.DataEnvironment := []) :
    Value.GraphHasType program world (.bool value) .bool definitions :=
  Value.GraphHasType.ofCore Core.RuntimeValueHasType.bool

theorem Value.GraphHasType.word
    (program : Program) (world : Core.StoreTyping) (value : Core.Word)
    (definitions : Core.DataEnvironment := []) :
    Value.GraphHasType program world (.word value) .word definitions :=
  Value.GraphHasType.ofCore Core.RuntimeValueHasType.word

/-- Primitive Core unary operations return deep primitive values, not just
values with matching shallow tags. -/
theorem unary_apply_result_graph_type
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {op : Core.UnaryOp} {operand result : Core.Value}
    (applied : op.apply operand = some result) :
    Value.GraphHasType program world (Value.ofCore result) op.resultType
      definitions := by
  have resultTyping : Core.RuntimeValueHasType world result op.resultType
      definitions := by
    have resultType := Core.UnaryOp.apply_result_type applied
    clear applied operand
    cases op <;> cases result <;>
      simp [Core.Value.type, Core.UnaryOp.resultType] at resultType
    all_goals constructor
  exact Value.GraphHasType.ofCore resultTyping

/-- Primitive Core binary operations likewise return deep primitive values. -/
theorem binary_apply_result_graph_type
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {op : Core.BinaryOp} {left right result : Core.Value}
    (applied : op.apply left right = some result) :
    Value.GraphHasType program world (Value.ofCore result) op.resultType
      definitions := by
  have resultTyping : Core.RuntimeValueHasType world result op.resultType
      definitions := by
    have resultType := Core.BinaryOp.apply_result_type applied
    clear applied left right
    cases op <;> cases result <;>
      simp [Core.Value.type, Core.BinaryOp.resultType] at resultType
    all_goals constructor
  exact Value.GraphHasType.ofCore resultTyping


end Solcore.Frontend.SourceRuntime
