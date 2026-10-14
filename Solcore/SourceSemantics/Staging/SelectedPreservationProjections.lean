import Solcore.SourceSemantics.Staging.SelectedPreservationComposition
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem ExpressionAt.fault {size : Nat} (sound : ExpressionAt program registry size) :
    FaultPreservation.ExpressionAt program registry size := by
  intro scope context environment before after id failure type runtime covers locals heap typed trace
  have post := sound runtime covers locals heap typed trace
  exact ⟨post.heap_typed, post.heap_extends⟩

theorem ExpressionsAt.fault {size : Nat} (sound : ExpressionsAt program registry size) :
    FaultPreservation.ExpressionsAt program registry size := by
  intro scope context environment before after ids failure types runtime covers locals heap typed trace
  have post := sound runtime covers locals heap typed trace
  exact ⟨post.heap_typed, post.heap_extends⟩

theorem AppliesAt.fault {size : Nat} (sound : AppliesAt program registry size) :
    FaultPreservation.AppliesAt program registry size := by
  intro scope context source before after callable arguments packed failure parameter result runtime heap typed packing argumentTyped trace
  have post := sound runtime heap typed packing argumentTyped trace
  exact ⟨post.heap_typed, post.heap_extends⟩

theorem RawFormAt.fault {size : Nat} (sound : RawFormAt program registry size) :
    FaultPreservation.RawFormAt program registry size := by
  intro scope context environment before after form requirements coercions failure rawType finalType plan runtime covers locals heap occurrence typed valid trace
  have post := sound runtime covers locals heap occurrence typed valid trace
  exact ⟨post.heap_typed, post.heap_extends⟩

theorem CoercionPathAt.fault {size : Nat} (sound : CoercionPathAt program registry size) :
    FaultPreservation.CoercionPathAt program registry size := by
  intro scope context before after steps input failure sourceType targetType runtime heap typed valid trace
  have post := sound runtime heap typed valid trace
  exact ⟨post.heap_typed, post.heap_extends⟩

theorem expression_value {size : Nat} (sound : ExpressionAt program registry size) {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {id : ExpressionId} {value : Value} {type : TypeSystem.Ty}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (typed : ExpressionHasType scope.source context id type)
    (trace : Size.Expression program registry size scope context environment before id (.value value) after) :
    ExpressionEvaluationPreserved context before after value type := by
  have post := sound runtime covers locals heap typed trace
  exact ⟨post.value_typed _ rfl, post.heap_typed, post.heap_extends⟩

theorem expressions_values {size : Nat} (sound : ExpressionsAt program registry size) {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {ids : List ExpressionId} {values : List Value} {types : List TypeSystem.Ty}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (typed : ExpressionsHaveTypes scope.source context ids types)
    (trace : Size.Expressions program registry size scope context environment before ids (.values values) after) :
    ValuesHaveTypes context after values types ∧ HeapWellTyped context after ∧ HeapTypesExtend before after := by
  have post := sound runtime covers locals heap typed trace
  exact ⟨post.values_typed _ rfl, post.heap_typed, post.heap_extends⟩

theorem raw_form_value {size : Nat} (sound : RawFormAt program registry size) {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {form : ExpressionForm} {requirements : List RequirementId}
    {coercions : List SourceInference.CoercionStep} {value : Value}
    {rawType finalType : TypeSystem.Ty} {plan : ExpressionRequirementPlan}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (occurrence : ∃ id node, ContainsExpression scope.source id node ∧ node.form = form ∧ node.rawType = rawType)
    (typed : ExpressionFormHasRawType scope.source context form rawType plan)
    (valid : ExpressionRequirementPlan.Valid context rawType finalType plan requirements coercions)
    (trace : Size.RawForm program registry size scope context environment before form requirements coercions (.value value) after) :
    ValueHasType context after value rawType ∧ HeapWellTyped context after ∧ HeapTypesExtend before after := by
  have post := sound runtime covers locals heap occurrence typed valid trace
  exact ⟨post.value_typed _ rfl, post.heap_typed, post.heap_extends⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
