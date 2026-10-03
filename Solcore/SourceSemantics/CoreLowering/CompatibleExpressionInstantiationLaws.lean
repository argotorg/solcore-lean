import Solcore.SourceSemantics.CoreLowering.CompatibleSourceInstantiationClosure

/-! Source instantiation laws are attached to stored, admitted occurrences.
Raw closedness covers every retained substitution row, including unused ones.
The laws preserve the full instantiation and the original source context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionInstantiationLaws
open Frontend SourceInference CompatibleSourceInstantiationClosure

def ConstructorLaw (source : TypedSource) (context : Context) (admitted : ExpressionId → Prop) : Prop :=
  ∀ id node instantiation arguments, admitted id → source.lookupExpression? id = some node →
    node.form = .constructor instantiation arguments →
    DataConstructorInstantiation.Admissible context instantiation →
    DataConstructorInstantiation.Valid context instantiation

def DeclarationLaw (source : TypedSource) (context : Context) (admitted : ExpressionId → Prop) : Prop :=
  ∀ id node callee arguments instantiation, admitted id → source.lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) →
    DeclarationInstantiation.Admissible context instantiation →
    DeclarationInstantiation.Valid context instantiation

def ConstructorRanges (source : TypedSource) (admitted : ExpressionId → Prop) : Prop :=
  ∀ id node instantiation arguments, admitted id → source.lookupExpression? id = some node →
    node.form = .constructor instantiation arguments →
    ClosedParameterRange instantiation.parameterSubstitution

def DeclarationRanges (source : TypedSource) (admitted : ExpressionId → Prop) : Prop :=
  ∀ id node callee arguments instantiation, admitted id → source.lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) →
    ClosedParameterRange instantiation.parameterSubstitution

variable {source : TypedSource} {context : Context} {admitted restricted : ExpressionId → Prop}

theorem ConstructorLaw.restrict (law : ConstructorLaw source context admitted)
    (subset : ∀ id, restricted id → admitted id) : ConstructorLaw source context restricted := by
  intro id node instantiation arguments allowed found form valid
  exact law id node instantiation arguments (subset id allowed) found form valid

theorem ConstructorRanges.restrict (ranges : ConstructorRanges source admitted)
    (subset : ∀ id, restricted id → admitted id) : ConstructorRanges source restricted := by
  intro id node instantiation arguments allowed found form
  exact ranges id node instantiation arguments (subset id allowed) found form

/-- Compatibility with the former globally closed flexible scopes. -/
theorem ConstructorLaw.of_closed (lexical : context.typeVariables = [])
    (residual : context.residualTypeVariables = false) : ConstructorLaw source context admitted := by
  intro _ _ _ _ _ _ _ admissible
  exact admissible.toValid lexical residual

theorem DeclarationLaw.of_closed (lexical : context.typeVariables = [])
    (residual : context.residualTypeVariables = false) : DeclarationLaw source context admitted := by
  intro _ _ _ _ _ _ _ _ admissible
  exact admissible.toValid lexical residual

/-- Only the used occurrence's raw substitution supplies closure. No compiler
acceptance or native representation is substituted for these source facts. -/
theorem ConstructorLaw.of_ranges (lexical : context.typeVariables = [])
    (ranges : ConstructorRanges source admitted) : ConstructorLaw source context admitted := by
  intro id node instantiation arguments allowed found form admissible
  exact constructor_valid admissible lexical (ranges id node instantiation arguments allowed found form)

theorem DeclarationLaw.of_ranges (lexical : context.typeVariables = [])
    (ranges : DeclarationRanges source admitted) : DeclarationLaw source context admitted := by
  intro id node callee arguments instantiation allowed found form admissible
  exact declaration_valid admissible lexical (ranges id node callee arguments instantiation allowed found form)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionInstantiationLaws
