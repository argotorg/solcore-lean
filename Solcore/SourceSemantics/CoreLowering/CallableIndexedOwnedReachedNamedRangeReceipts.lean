import Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
import Solcore.SourceSemantics.Instantiation

/-! Full raw replacement formation transfers through the actual compiler
matcher. Every retained replacement is located in the genuine source
substitution; order and native erasure play no role. Source validity remains
independent of executable seed acceptance. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedRangeReceipts
open Frontend SourceInference TypeSystem

private theorem binding_member {substitution : TypeSystem.ParameterSubstitution}
    {parameter : TypeParameterId} {type : Ty}
    (found : SourceCompilationPlan.exactParameterBinding? substitution parameter = some type) :
    (parameter, type) ∈ substitution := by
  unfold SourceCompilationPlan.exactParameterBinding? at found
  split at found
  · rename_i selected filtered
    have member : selected ∈ substitution.filter (fun item => item.1 == parameter) := by
      rw [filtered]
      exact List.mem_singleton_self _
    obtain ⟨member, key⟩ := List.mem_filter.mp member
    have keyEq : selected.1 = parameter := LawfulBEq.eq_of_beq key
    have typeEq : selected.2 = type := Option.some.inj found
    have same : selected = (parameter, type) := Prod.ext keyEq typeEq
    rwa [same] at member
  · cases found

theorem range_of_equivalent {context : SourceSemantics.Context}
    {left right : TypeSystem.ParameterSubstitution}
    (equivalent : SourceCompilationPlan.parameterSubstitutionsEquivalent left right = true)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed context right) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed context left := by
  have each : ∀ entry ∈ left,
      SourceCompilationPlan.exactParameterBinding? right entry.1 = some entry.2 := by
    simp only [SourceCompilationPlan.parameterSubstitutionsEquivalent, Bool.and_eq_true,
      List.all_eq_true, beq_iff_eq] at equivalent
    exact equivalent.1.2
  intro parameter type member
  exact range parameter type (binding_member (each (parameter, type) member))

theorem range_of_valid_match {context : SourceSemantics.Context}
    {specialized : SourceSpecialization.SpecializedFunction} {instantiation : DeclarationInstantiation}
    (matched : CallableNamedMetadata.Matches specialized instantiation)
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed context specialized.parameterSubstitution := by
  cases valid with
  | intro _ _ _ _ range => exact range_of_equivalent matched.substitution range

theorem range_of_selected {context : SourceSemantics.Context}
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    {specialized : SourceSpecialization.SpecializedFunction}
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (selected : SourceCoreFunctions.selectedSignature policy compilation source node instantiation isReference =
      .ok (index, signature))
    (record : SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed context specialized.parameterSubstitution :=
  range_of_valid_match
    (CallableNamedMetadata.matches_of_exact (NamedCalls.selected_signature_target selected).1 record) valid

private theorem scoped_at_catalog {context : SourceSemantics.Context} {type : Ty}
    (parameters : context.typeParameters = []) (scopedType : TypeWellScoped context [] type) :
    TypeWellScoped (SourceSemantics.Context.ofSignatures context.signatures) [] type := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => TypeWellScoped (.ofSignatures context.signatures) [] type)
    (motive_2 := fun types _ => TypesWellScoped (.ofSignatures context.signatures) [] types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ scopedType
  · intro metavariable member
    cases member
  · intro parameter member _
    rw [parameters] at member
    cases member
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments member arity _ argumentsTyping
    exact .nominal dataType arguments member arity argumentsTyping
  · intro contract arguments member arity _ argumentsTyping
    exact .contractNominal contract arguments member arity argumentsTyping
  · intro parameter result _ _ left right
    exact .function left right
  · intro left right _ _ leftTyping rightTyping
    exact .product leftTyping rightTyping
  · intro key value _ _ keyTyping valueTyping
    exact .mapping keyTyping valueTyping
  · intro inner _ innerTyping
    exact .proxy innerTyping
  · intro inner _ innerTyping
    exact .comptime innerTyping
  · exact .nil
  · intro head tail _ _ headTyping tailTyping
    exact .cons headTyping tailTyping

theorem range_at_catalog {context : SourceSemantics.Context}
    {substitution : TypeSystem.ParameterSubstitution}
    (parameters : context.typeParameters = [])
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed context substitution) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures context.signatures) substitution := by
  intro parameter type member
  exact ⟨TypeParameterBindersWellFormed.ofSignatures context.signatures,
    scoped_at_catalog parameters (range parameter type member).typeWellScoped⟩

theorem catalog_range_of_selected {context : SourceSemantics.Context}
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    {specialized : SourceSpecialization.SpecializedFunction}
    (parameters : context.typeParameters = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (selected : SourceCoreFunctions.selectedSignature policy compilation source node instantiation isReference =
      .ok (index, signature))
    (record : SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures context.signatures) specialized.parameterSubstitution :=
  range_at_catalog parameters (range_of_selected valid selected record)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedRangeReceipts
