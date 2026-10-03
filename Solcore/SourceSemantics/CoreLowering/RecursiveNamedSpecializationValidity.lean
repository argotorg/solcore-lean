import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationBodyFacts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedRetainedSubstitutionFacts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedSourceFrames

/-! Canonical declaration validity from actual specialization. The real guards
and ordered canonical domain provide the redundant metadata fields. Every raw
replacement, including unused nominal rows, still needs independent formation
in the source context. No body execution or native authority is inferred. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationValidity
open Frontend SourceInference TypeSystem

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

variable {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : TypeSystem.ParameterSubstitution}
  {specialized : SourceSpecialization.SpecializedFunction}

/-- These three equalities come from the actual leading guards, before any
specialized body is produced. The flags are not recovered from erased types. -/
theorem guards
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    signature.scheme.body = generic.type ∧
      signature.parameterComptime = generic.typedBody.inputs.map (·.comptime) ∧
      signature.returnComptime = generic.returnComptime := by
  unfold SourceSpecialization.specializeFunction at accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  by_cases typeSame : signature.scheme.body = generic.type
  · simp only [typeSame, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at accepted
    by_cases parametersSame : signature.parameterComptime = generic.typedBody.inputs.map (·.comptime)
    · simp only [parametersSame, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at accepted
      by_cases returnSame : signature.returnComptime = generic.returnComptime
      · exact ⟨typeSame, parametersSame, returnSame⟩
      · simp [returnSame, bne_iff_ne, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
    · simp [parametersSame, bne_iff_ne, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  · simp [typeSame, bne_iff_ne, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted

/-- The complete domain is the original declaration order, including unused
parameters. No used-type filtering is performed. -/
theorem exact
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (unique : signature.scheme.parameters.Nodup) :
    SourceSemantics.ParameterSubstitution.Exact specialized.parameterSubstitution signature.scheme.parameters := by
  refine ⟨unique, ?_⟩
  change (specialized.parameterSubstitution.map Prod.fst).Perm signature.scheme.parameters
  rw [SourceSpecialization.specializeFunction_parameterDomain accepted]

/-- Full raw range formation is the only context-dependent input beyond the
original signature's membership. The context's residual flag is unchanged. -/
theorem canonical_valid {context : Context}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (member : signature ∈ context.signatures.functions)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed context specialized.parameterSubstitution) :
    DeclarationInstantiation.Valid context (CallableNamedMetadata.instantiation specialized) := by
  obtain ⟨typeSame, parametersSame, returnSame⟩ := guards accepted
  have fields := CallableCoercionBodyProvenance.specialization_fields accepted
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  refine .intro signature member (identities.2.2.trans identities.1.symm)
    (exact accepted unique) range ?_ fields.2 ?_ ?_
  · change specialized.function.type = specialized.parameterSubstitution.apply signature.scheme.body
    rw [fields.1]
    change specialized.parameterSubstitution.apply generic.type = _
    rw [typeSame]
  · change specialized.function.typedBody.inputs.map (·.comptime) = signature.parameterComptime
    rw [fields.1]
    simpa only [SourceSpecialization.applyCheckedFunction, SourceSpecialization.applyTypedSource,
      List.map_map, SourceSpecialization.applyBinder, Function.comp_def] using parametersSame.symm
  · change specialized.function.returnComptime = signature.returnComptime
    rw [fields.1]
    exact returnSame.symm

/-- Program validity supplies parameter uniqueness at the same cataloged
signature; it does not replace the full replacement-range obligation. -/
theorem valid_of_program {program : CheckedProgram}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (member : signature ∈ program.signatures.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation specialized) :=
  canonical_valid accepted member (wellFormed.signatures.function_parameters signature member).1 range

theorem instantiated {program : CheckedProgram}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    Dynamic.FunctionInstantiates (Program.ofChecked program) (CallableNamedMetadata.instantiation specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program specialized) :=
  RecursiveNamedSpecializationBodyFacts.instantiated signatureMember genericMember accepted
    (canonical_valid accepted signatureMember unique range)

theorem retained_instantiated {program : CheckedProgram}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    Dynamic.FunctionInstantiates (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program specialized) :=
  RecursiveNamedRetainedSubstitutionFacts.retained_instantiates
    (instantiated signatureMember genericMember accepted unique range)

section Prepared
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}

/-- The computed validity discharges the full canonical-validity input to the
actual two-pass source-frame factory. Ordinary evidence and every raw range
row remain explicit static conditions. -/
theorem of_compilation
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) named.specialized.parameterSubstitution)
    (closed : named.specialized.assumptions = [])
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    CompatibleNamedBody.NamedAgreement named
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation named.specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program named.specialized)
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) :=
  RecursiveNamedPreparedSourceFrames.of_compilation signatureMember genericMember accepted
    (canonical_valid accepted signatureMember unique range) closed inputs compiled

/-- Reversed occurrence metadata retains exactly the same independent body
and prepared source view; substitution records themselves keep their order. -/
theorem retained_of_compilation
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) named.specialized.parameterSubstitution)
    (closed : named.specialized.assumptions = [])
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    CompatibleNamedBody.NamedAgreement named
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation named.specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program named.specialized)
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) :=
  RecursiveNamedPreparedSourceFrames.retained_of_compilation signatureMember genericMember accepted
    (canonical_valid accepted signatureMember unique range) closed inputs compiled
end Prepared

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationValidity
