import Solcore.SourceSemantics.CoreLowering.CallableNamedReversal

/-! Actual declaration inference and specialization keep opposite ordered
parameter ledgers. This module relates those exact records without identifying
source functions merely because their substitutions denote the same mapping. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableNamedCanonicalOrder
open Frontend SourceInference TypeSystem

/-- The canonical source record uses the reverse order retained by inference.
All other metadata fields are those authenticated by the real matcher. -/
def retainedInstantiation (specialized : SourceSpecialization.SpecializedFunction) : DeclarationInstantiation :=
  {CallableNamedMetadata.instantiation specialized with
    parameterSubstitution := specialized.parameterSubstitution.reverse}

@[simp] theorem reverse_retained (specialized : SourceSpecialization.SpecializedFunction) :
    CallableNamedReversal.instantiation (retainedInstantiation specialized) =
      CallableNamedMetadata.instantiation specialized := by
  simp [retainedInstantiation, CallableNamedReversal.instantiation, CallableNamedMetadata.instantiation]

/-- The record produced by declaration inference, followed by final flexible
solving and caller specialization. Both passes retain the ordered rigid keys. -/
def inferredInstantiation (signature : ProgramFunctionSignature) (next : Nat)
    (final : Substitution) (caller : ParameterSubstitution) : DeclarationInstantiation :=
  SourceSpecialization.applyInstantiation caller
    ((DeclarationInstantiation.ofInstantiated signature (signature.scheme.instantiate next)).applySubstitution final)

@[simp] theorem inferred_parameterDomain (signature : ProgramFunctionSignature) (next : Nat)
    (final : Substitution) (caller : ParameterSubstitution)
    (unique : signature.scheme.parameters.Nodup) :
    (inferredInstantiation signature next final caller).parameterSubstitution.map Prod.fst =
      signature.scheme.parameters.reverse := by
  simp only [inferredInstantiation, SourceSpecialization.applyInstantiation_parameterDomain,
    DeclarationInstantiation.applySubstitution_parameterDomain, DeclarationInstantiation.ofInstantiated]
  exact ConstrainedDeclarationScheme.instantiate_parameterSubstitution_domain_reverse signature.scheme next unique
end Solcore.SourceSemantics.CoreLowering.CallableNamedCanonicalOrder

namespace Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
open Frontend SourceInference TypeSystem
open CallableNamedCanonicalOrder

/-- The real matcher plus the checker's reverse domain order determines every
ordered field of the independently retained source instantiation. -/
theorem Matches.retained_canonical {specialized : SourceSpecialization.SpecializedFunction}
    {source : DeclarationInstantiation} (matched : Matches specialized source)
    (domain : source.parameterSubstitution.map Prod.fst =
      (specialized.parameterSubstitution.map Prod.fst).reverse) :
    source = retainedInstantiation specialized := by
  have reversed : Matches specialized (CallableNamedReversal.instantiation source) := by
    refine ⟨matched.ownership, matched.arguments, matched.declaration, ?_, matched.type,
      matched.predicates, matched.parameterComptime, matched.returnComptime⟩
    simpa only [CallableNamedReversal.instantiation, CallableNamedReversal.substitutions_reverse_right] using matched.substitution
  have ordered : specialized.parameterSubstitution.map Prod.fst =
      (CallableNamedReversal.instantiation source).parameterSubstitution.map Prod.fst := by
    simp only [CallableNamedReversal.instantiation, List.map_reverse, domain, List.reverse_reverse]
  have canonical := reversed.canonical ordered
  have inverted := congrArg CallableNamedReversal.instantiation canonical
  change CallableNamedReversal.instantiation (CallableNamedReversal.instantiation source) =
    retainedInstantiation specialized at inverted
  simpa only [CallableNamedReversal.instantiation_twice] using inverted

/-- Actual successful specialization and actual inferred-record formation close
the domain-order condition. The matcher continues to authenticate all fields. -/
theorem Matches.retained_of_specialization {signature : ProgramFunctionSignature}
    {function : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature function supplied = .ok specialized)
    (unique : signature.scheme.parameters.Nodup) (next : Nat) (final : Substitution) (caller : ParameterSubstitution)
    (matched : Matches specialized (inferredInstantiation signature next final caller)) :
    inferredInstantiation signature next final caller = retainedInstantiation specialized := by
  apply matched.retained_canonical
  rw [inferred_parameterDomain signature next final caller unique,
    SourceSpecialization.specializeFunction_parameterDomain accepted]
end Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
