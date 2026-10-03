import Solcore.SourceSemantics.CoreLowering.CallableCoercionBodyProvenance
import Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
import Solcore.SourceSemantics.CoreLowering.NamedCallSource
import Solcore.SourceSemantics.ProgramCheckingSoundness

/-! The actual accepted specialization constructs the independent canonical
body instantiation. Static validity, invocation evidence, statement roots and
captured environment remain separate conditions. Reversed occurrence metadata
requires its own substitution correspondence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationBodyFacts
open Frontend SourceInference TypeSystem

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

variable {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}

/-- The accepted guards identify the original cataloged declaration, its raw
body owner, and the complete specialized declaration record. -/
theorem identities
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    signature.id = generic.declaration ∧ generic.typedBody.owner = generic.declaration ∧
      specialized.declaration = generic.declaration := by
  unfold SourceSpecialization.specializeFunction at accepted
  by_cases declaration : signature.id = generic.declaration
  · simp only [declaration, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at accepted
    by_cases owner : generic.typedBody.owner = generic.declaration
    · simp only [owner, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at accepted
      have accepted := reject_ok accepted
      have accepted := reject_ok accepted
      have accepted := reject_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      cases analysis : SourceStageAnalysis.analyzeFunction
          (SourceSpecialization.applyCheckedFunction canonical generic) with
      | error error => simp only [analysis] at accepted; cases accepted
      | ok stages =>
        simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
        subst specialized
        exact ⟨declaration, owner, rfl⟩
    · simp [owner, bne_iff_ne, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  · simp [declaration, bne_iff_ne, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted

theorem body
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    specialized.function.typedBody = StructuralSubstitution.applyTypedSource
      specialized.parameterSubstitution generic.typedBody := by
  rw [(CallableCoercionBodyProvenance.specialization_fields accepted).1,
    StructuralSubstitution.applyTypedSource_frontend_eq]
  rfl

/-- Every solved row, its identity and full recursive evidence are retained in
the original order by the independent structural substitution. -/
theorem ledger
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    specialized.function.solvedRequirements = generic.solvedRequirements.map
      (StructuralSubstitution.applySolvedRequirement specialized.parameterSubstitution) := by
  rw [(CallableCoercionBodyProvenance.specialization_fields accepted).1]
  simp only [SourceSpecialization.applyCheckedFunction]
  congr 1
  funext requirement
  exact (StructuralSubstitution.applySolvedRequirement_frontend_eq _ _).symm

theorem result
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    specialized.function.inferredBodyType =
      specialized.parameterSubstitution.apply generic.inferredBodyType := by
  rw [(CallableCoercionBodyProvenance.specialization_fields accepted).1]
  rfl

/-- The body view uses canonical metadata and the real full solved ledger.
The declaration context keeps residual type variables enabled. -/
def bodyInstance (program : CheckedProgram) (specialized : SourceSpecialization.SpecializedFunction) :
    Dynamic.BodyInstance where
  context := declarationContext program.signatures specialized.declaration []
    specialized.assumptions specialized.function.solvedRequirements
  source := specialized.function.typedBody
  resultType := specialized.function.inferredBodyType

theorem context {program : CheckedProgram}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    (bodyInstance program specialized).context =
      declarationContext program.signatures generic.declaration []
        (signature.scheme.predicates.map
          (ProgramPredicate.applyParameters specialized.parameterSubstitution))
        (generic.solvedRequirements.map
          (StructuralSubstitution.applySolvedRequirement specialized.parameterSubstitution)) := by
  simp only [bodyInstance, (identities accepted).2.2,
    (CallableCoercionBodyProvenance.specialization_fields accepted).2, ledger accepted]

/-- This derives the dynamic instantiation judgment from the actual compiler
pass and catalog membership. It requires independent validity of the complete
canonical metadata, including unused substitution ranges. -/
theorem instantiated {program : CheckedProgram}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation specialized)) :
    Dynamic.FunctionInstantiates (Program.ofChecked program)
      (CallableNamedMetadata.instantiation specialized) (bodyInstance program specialized) := by
  obtain ⟨declaration, _, specializedDeclaration⟩ := identities accepted
  apply Dynamic.FunctionInstantiates.intro
    (signature := signature) (definition := FunctionDefinition.ofChecked generic)
  · exact signatureMember
  · exact List.mem_map.mpr ⟨generic, genericMember, rfl⟩
  · exact specializedDeclaration.trans declaration.symm
  · exact declaration.symm
  · exact valid
  · exact body accepted
  · exact result accepted
  · simpa only [Program.ofChecked, FunctionDefinition.ofChecked, BodyDefinition.ofChecked,
      CallableNamedMetadata.instantiation,
      (CallableCoercionBodyProvenance.specialization_fields accepted).2] using
      context (program := program) accepted

/-- The remaining closure facts come from the actual source invocation view;
they are never inferred from Core types, decoding, or successful execution. -/
theorem source_frame {program : CheckedProgram} {function : Dynamic.Closure}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation specialized))
    (source : function.source = specialized.function.typedBody)
    (context : function.context = (bodyInstance program specialized).context)
    (parameters : function.parameters = specialized.function.typedBody.inputs)
    (result : function.resultType = specialized.function.inferredBodyType)
    (captured : function.captured = [])
    (roots : Dynamic.StatementRoots specialized.function.typedBody.roots function.body)
    (covers : function.evidence.Covers (bodyInstance program specialized).context) :
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation specialized)
      (bodyInstance program specialized) function :=
  ⟨instantiated signatureMember genericMember accepted valid,
    source, context, parameters, result, captured, roots, covers⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationBodyFacts
