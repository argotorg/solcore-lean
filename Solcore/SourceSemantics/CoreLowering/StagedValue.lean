import Solcore.Frontend.SourceStagedValue
import Solcore.SourceSemantics.Dynamic.Typing
import Solcore.Core.Correspondence

/-!
Independent source meaning and execution of reified staged values.

This is the value-embedding part of source-to-Core correctness. It connects
the existing `SourceStagedValue.toCoreExpr` implementation to mathematical
source values and to Core's declarative and executable semantics. It does not
assume or establish correctness of the staged evaluator that produced a value.
No typed-source runtime is imported or used as the source specification.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering

open Frontend

namespace StagedValue

/-- Interpret the closed staging carrier as an independent source value. -/
def toSource : SourceStagedValue.Value → Dynamic.Value
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .product left right => .product (toSource left) (toSource right)

/-- Scalar/product representation, independent of any staging computation. -/
inductive Represents : Dynamic.Value → Core.Value → Prop where
  | unit : Represents .unit .unit
  | bool (value : Bool) : Represents (.bool value) (.bool value)
  | word (value : Core.Word) : Represents (.word value) (.word value)
  | product {left right : Dynamic.Value} {coreLeft coreRight : Core.Value}
      (left_related : Represents left coreLeft)
      (right_related : Represents right coreRight) :
      Represents (.product left right) (.pair coreLeft coreRight)

theorem toCore_represents (value : SourceStagedValue.Value) :
    Represents (toSource value) (SourceStagedValue.toCore value) := by
  induction value with
  | unit => exact .unit
  | bool value => exact .bool value
  | word value => exact .word value
  | product _ _ left right => exact .product left right

/-- Reification does not require inspecting the source heap or its values. -/
theorem toSource_hasType (value : SourceStagedValue.Value)
    (context : Context) (heap : Dynamic.Heap) :
    Dynamic.ValueHasType context heap (toSource value)
      (SourceStagedValue.sourceType value) := by
  induction value with
  | unit => exact .unit
  | bool value => exact .bool value
  | word value => exact .word value
  | product _ _ left right => exact .product left right

/-- Reified constants are typed in any lexical and nominal context. -/
theorem toCoreExpr_hasType (value : SourceStagedValue.Value)
    (context : Core.Context) (definitions : Core.DataEnvironment) :
    Core.HasType context (SourceStagedValue.toCoreExpr value)
      (SourceStagedValue.coreType value) definitions := by
  induction value with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product _ _ left right => exact .pair left right

/-- The executable Core checker accepts the actual reification output. -/
theorem toCoreExpr_infers (value : SourceStagedValue.Value)
    (context : Core.Context) (definitions : Core.DataEnvironment) :
    Core.infer? context (SourceStagedValue.toCoreExpr value) definitions =
      some (SourceStagedValue.coreType value) :=
  Core.infer_complete (toCoreExpr_hasType value context definitions)

/-- Every related scalar/product value comes from the existing staging
carrier. This rules out an unconstrained representation relation. -/
theorem Represents.exists_staged
    {source : Dynamic.Value} {core : Core.Value}
    (related : Represents source core) :
    ∃ value : SourceStagedValue.Value,
      source = toSource value ∧ core = SourceStagedValue.toCore value := by
  induction related with
  | unit => exact ⟨.unit, rfl, rfl⟩
  | bool value => exact ⟨.bool value, rfl, rfl⟩
  | word value => exact ⟨.word value, rfl, rfl⟩
  | product _ _ left right =>
      obtain ⟨leftValue, rfl, rfl⟩ := left
      obtain ⟨rightValue, rfl, rfl⟩ := right
      exact ⟨.product leftValue rightValue, rfl, rfl⟩

theorem toSource_injective : Function.Injective toSource := by
  intro left
  induction left with
  | unit =>
      intro right equal
      cases right <;> cases equal
      rfl
  | bool value =>
      intro right equal
      cases right <;> cases equal
      rfl
  | word value =>
      intro right equal
      cases right <;> cases equal
      rfl
  | product left right leftInduction rightInduction =>
      intro other equal
      cases other with
      | unit | bool | word => cases equal
      | product otherLeft otherRight =>
          obtain ⟨leftEqual, rightEqual⟩ := Dynamic.Value.product.inj equal
          rw [leftInduction leftEqual, rightInduction rightEqual]

/-- The representation neither conflates source values nor admits several
different Core encodings of a single staged value. -/
theorem represents_toSource_iff (value : SourceStagedValue.Value)
    (core : Core.Value) :
    Represents (toSource value) core ↔ core = SourceStagedValue.toCore value := by
  constructor
  · intro related
    obtain ⟨other, sameSource, sameCore⟩ := related.exists_staged
    have equal := toSource_injective sameSource
    simpa only [← equal] using sameCore
  · intro equal
    rw [equal]
    exact toCore_represents value

/-- The actual Core constant expression returns the represented value and
leaves every surrounding store unchanged. -/
theorem toCoreExpr_evaluates (value : SourceStagedValue.Value)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (SourceStagedValue.toCoreExpr value)
      (SourceStagedValue.toCore value) store := by
  induction value with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product _ _ left right => exact .pair left right

/-- Reflection includes the final store, rather than only the returned value. -/
theorem toCoreExpr_evaluates_iff (value : SourceStagedValue.Value)
    (environment : Core.Environment) (initial : Core.Store)
    (result : Core.Value) (final : Core.Store) :
    Core.Evaluates environment initial (SourceStagedValue.toCoreExpr value)
        result final ↔
      Represents (toSource value) result ∧ final = initial := by
  constructor
  · intro evaluated
    obtain ⟨resultEqual, storeEqual⟩ := Core.evaluation_deterministic evaluated
      (toCoreExpr_evaluates value environment initial)
    exact ⟨(represents_toSource_iff value result).2 resultEqual, storeEqual⟩
  · rintro ⟨related, sameStore⟩
    subst final
    rw [(represents_toSource_iff value result).1 related]
    exact toCoreExpr_evaluates value environment initial

/-- Reification has a finite execution witness; no general source termination
claim or typed-source execution premise is needed. -/
theorem toCoreExpr_run_complete (value : SourceStagedValue.Value)
    (environment : Core.Environment) (store : Core.Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      Core.runStateful fuel
          (Core.State.initial (SourceStagedValue.toCoreExpr value)
            environment store) =
        .done (SourceStagedValue.toCore value) store :=
  Core.evaluation_runStateful_complete_with_sufficient_fuel
    (toCoreExpr_evaluates value environment store)

/-- Any completed execution of a reified constant reflects its independent
source value and has no store effects. -/
theorem toCoreExpr_run_sound (value : SourceStagedValue.Value)
    (environment : Core.Environment) (initial : Core.Store)
    {fuel : Nat} {result : Core.Value} {final : Core.Store}
    (executed : Core.runStateful fuel
      (Core.State.initial (SourceStagedValue.toCoreExpr value)
        environment initial) = .done result final) :
    Represents (toSource value) result ∧ final = initial :=
  (toCoreExpr_evaluates_iff value environment initial result final).1
    (Core.runStateful_evaluation_sound executed)

end StagedValue

end Solcore.SourceSemantics.CoreLowering
