import Solcore.SourceSemantics.Graph
import Solcore.TypeSystem.Properties

/-! The empty flexible substitution preserves the complete retained source
carrier, including staging flags and evidence metadata. This is a syntactic
identity law; it does not assert substitution correctness for execution. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution
open Frontend Frontend.SourceInference TypeSystem

@[simp] theorem without (variables : List TypeVarId) :
    Substitution.without [] variables = [] := by
  induction variables with
  | nil => rfl
  | cons head rest ih => simpa [Substitution.without, Substitution.erase] using ih

@[simp] theorem type (value : Ty) : Substitution.apply [] value = value :=
  Substitution.empty_apply value

@[simp] theorem type_function : Substitution.apply [] = (id : Ty → Ty) := funext type

@[simp] theorem predicate (value : ProgramPredicate) :
    TypedTraitResolution.applySubstitution [] value = value := by
  simp [TypedTraitResolution.applySubstitution]

@[simp] theorem predicate_function : TypedTraitResolution.applySubstitution [] = (id : ProgramPredicate → ProgramPredicate) := funext predicate

@[simp] theorem scheme (value : Scheme) : Scheme.apply [] value = value := by
  simp [Scheme.apply]

@[simp] theorem requirement (value : LocalSchemeRequirement) :
    value.applySubstitution [] = value := by simp [LocalSchemeRequirement.applySubstitution]

@[simp] theorem requirement_function : LocalSchemeRequirement.applySubstitution [] = (id : LocalSchemeRequirement → LocalSchemeRequirement) := funext requirement

@[simp] theorem binder (value : TypedBinder) : value.applySubstitution [] = value := by
  simp [TypedBinder.applySubstitution]

@[simp] theorem binder_function : TypedBinder.applySubstitution [] = (id : TypedBinder → TypedBinder) := funext binder

@[simp] theorem integerResolution (value : IntegerLiteralResolution) :
    value.applySubstitution [] = value := by simp [IntegerLiteralResolution.applySubstitution]

@[simp] theorem declaration (value : DeclarationInstantiation) :
    value.applySubstitution [] = value := by
  unfold DeclarationInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map (fun p => (p.1, Substitution.apply [] p.2))
    type := Substitution.apply [] value.type
    predicates := value.predicates.map (TypedTraitResolution.applySubstitution []) } = value
  simp

@[simp] theorem constructor (value : DataConstructorInstantiation) :
    value.applySubstitution [] = value := by
  unfold DataConstructorInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map (fun p => (p.1, Substitution.apply [] p.2))
    payloadTypes := value.payloadTypes.map (Substitution.apply [])
    resultType := Substitution.apply [] value.resultType } = value
  simp

@[simp] theorem coercion (value : CoercionStep) : value.applySubstitution [] = value := by
  simp [CoercionStep.applySubstitution]

@[simp] theorem coercion_function : CoercionStep.applySubstitution [] = (id : CoercionStep → CoercionStep) := funext coercion

@[simp] theorem indirect (value : IndirectCallResolution) : value.applySubstitution [] = value := by
  cases value
  simp [IndirectCallResolution.applySubstitution]

@[simp] theorem reference (value : ReferenceResolution) : value.applySubstitution [] = value := by
  cases value <;> simp [ReferenceResolution.applySubstitution]

@[simp] theorem call (value : CallResolution) : value.applySubstitution [] = value := by
  cases value <;> simp [CallResolution.applySubstitution]

@[simp] theorem expressionForm (value : ExpressionForm) : value.applySubstitution [] = value := by
  cases value <;> simp [ExpressionForm.applySubstitution]

@[simp] theorem expression (value : ExpressionNode) : value.applySubstitution [] = value := by
  simp [ExpressionNode.applySubstitution]

@[simp] theorem instruction (value : MatchPatternInstruction) : value.applySubstitution [] = value := by
  cases value <;> simp [MatchPatternInstruction.applySubstitution]

@[simp] theorem instruction_function : MatchPatternInstruction.applySubstitution [] = (id : MatchPatternInstruction → MatchPatternInstruction) := funext instruction

@[simp] theorem resolution (value : MatchPatternResolution) : value.applySubstitution [] = value := by
  cases value <;> simp [MatchPatternResolution.applySubstitution]

@[simp] theorem pattern (value : TypedMatchPattern) : value.applySubstitution [] = value := by
  simp [TypedMatchPattern.applySubstitution]

@[simp] theorem matchCase (value : TypedMatchCase) : value.applySubstitution [] = value := by
  simp [TypedMatchCase.applySubstitution]

@[simp] theorem matchCase_function : TypedMatchCase.applySubstitution [] = (id : TypedMatchCase → TypedMatchCase) := funext matchCase

@[simp] theorem matchResolution (value : MatchResolution) : value.applySubstitution [] = value := by
  simp [MatchResolution.applySubstitution]

@[simp] theorem place (value : PlaceResolution) : value.applySubstitution [] = value := by
  simp [PlaceResolution.applySubstitution]

@[simp] theorem assignment (value : AssignmentResolution) : value.applySubstitution [] = value := by
  simp [AssignmentResolution.applySubstitution]

@[simp] theorem forItem (value : ForItemForm) : value.applySubstitution [] = value := by
  cases value <;> simp [ForItemForm.applySubstitution]

@[simp] theorem forItem_function : ForItemForm.applySubstitution [] = (id : ForItemForm → ForItemForm) := funext forItem

@[simp] theorem statementForm (value : StatementForm) : value.applySubstitution [] = value := by
  cases value <;> simp [StatementForm.applySubstitution]

@[simp] theorem statement (value : StatementNode) : value.applySubstitution [] = value := by
  simp [StatementNode.applySubstitution]

@[simp] theorem node (value : Node) : value.applySubstitution [] = value := by
  cases value <;> simp [Node.applySubstitution]

@[simp] theorem node_function : Node.applySubstitution [] = (id : Node → Node) := funext node

@[simp] theorem source (value : TypedSource) : value.applySubstitution [] = value := by
  simp [TypedSource.applySubstitution]

end Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution
