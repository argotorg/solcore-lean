import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodCertificates
import Solcore.SourceSemantics.CoreLowering.CallableCoercionPlanProvenance
import Solcore.SourceSemantics.SubstitutionCorrespondence

/-! A selected coercion method is rechecked with the same synthetic signature
and fuel as the loaded program. Its complete generic checker result therefore
comes from the retained method catalog. Specialization is then connected to
independent structural source substitution. Runtime calls and closure history
remain separate obligations. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionBodyProvenance
open Frontend SourceInference TypeSystem

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem require_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then action else .error error) = .ok value) :
    condition ∧ action = .ok value := by
  split at accepted
  · exact ⟨‹condition›, accepted⟩
  · cases accepted

private theorem filtered_find {α : Type} {entries : List α} {predicate : α → Bool} {value : α}
    (selected : entries.filter predicate = [value]) : entries.find? predicate = some value := by
  induction entries with
  | nil => cases selected
  | cons head tail ih =>
    cases test : predicate head <;> simp only [List.filter_cons, test, Bool.false_eq_true, if_false, if_true] at selected
    · simpa only [List.find?_cons, test] using ih selected
    · have same := (List.cons.inj selected).1
      subst value
      simp only [List.find?_cons, test]

/-- The two real checker call sites assemble the same complete signature.
Only append association differs in their ordered assumptions. -/
theorem synthetic_eq (implementation : ProgramImplementationSignature)
    (trait : ProgramTraitSignature) (method : ProgramImplMethodSignature) :
    (let base := implementation.functionSignatureOfMethod method
     let inherited := trait.wherePredicates.map (ProgramPredicate.applyParameters
       (trait.parameters.zip (implementation.head.subject :: implementation.head.arguments)))
     {base with scheme := {base.scheme with predicates := inherited ++ base.scheme.predicates}}) =
    implementation.functionSignatureOfMethodWithTrait trait method := by
  simp only [ProgramImplementationSignature.functionSignatureOfMethodWithTrait,
    ProgramImplementationSignature.functionSignatureOfMethod,
    ProgramImplementationSignature.methodAssumptions, List.append_assoc]

/-- Static selection and recheck receipts, before identifying the retained
checker result. No source execution or body-meaning premise is stored. -/
structure Selection (program : CheckedProgram) (method : ExecutableImplMethods.CheckedMethod) where
  implementation : ProgramImplementationSignature
  trait : ProgramTraitSignature
  declaration : ProgramImplMethodSignature
  generic : CheckedFunction
  supplied : ParameterSubstitution
  implementationMember : implementation ∈ program.signatures.implementations
  methodMember : declaration ∈ implementation.methods
  traitLookup : program.signatures.trait? declaration.traitMethod.trait = some trait
  traitMethodMember : method.traitMethod ∈ trait.methods
  methodId : method.id = declaration.id
  methodOwner : declaration.id.implementation = implementation.id
  association : declaration.traitMethod = method.traitMethod.id
  bodyChecked : checkFunctionBody program.environment program.signatures
    (implementation.functionSignatureOfMethodWithTrait trait declaration) 1024 = .ok generic
  specialized : SourceSpecialization.specializeFunction
    (implementation.functionSignatureOfMethodWithTrait trait declaration) generic supplied = .ok method.specialized
  checkedEq : method.checked = method.specialized.function

/-- Recover the actual singleton selectors, association guards and complete
same-fuel checker invocation from successful executable-method selection. -/
theorem selection {program : CheckedProgram} {primary : TypedTraitResolution.Evidence}
    {evidence : List TypedTraitResolution.Evidence} {arity : Nat} {name : String}
    {method : ExecutableImplMethods.CheckedMethod}
    (accepted : ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary evidence arity name = .ok method) :
    Nonempty (Selection program method) := by
  cases primary with
  | byImpl goal implementationId premises =>
    simp only [ExecutableImplMethods.checkMethodWithEvidenceAndArity] at accepted
    split at accepted <;> try contradiction
    try simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
    split at accepted <;> try contradiction
    try simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨implementation, implementationSelected, accepted⟩ := bind_ok accepted
    split at accepted <;> try contradiction
    split at accepted <;> try contradiction
    rename_i headMatch headMatched
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨trait, traitSelected, accepted⟩ := bind_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨declaration, methodSelected, accepted⟩ := bind_ok accepted
    obtain ⟨traitMethod, traitMethodSelected, accepted⟩ := bind_ok accepted
    obtain ⟨methodOwner, accepted⟩ := require_ok accepted
    obtain ⟨traitOwner, accepted⟩ := require_ok accepted
    obtain ⟨associated, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨generic, genericChecked, accepted⟩ := bind_ok accepted
    obtain ⟨specialized, specializedChecked, accepted⟩ := bind_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    cases accepted
    have implementationMember : implementation ∈ program.signatures.implementations := by
      change ((match program.signatures.implementations.filter _ with
        | [] => .error _ | [value] => .ok value | values => .error _) : Except ExecutableImplMethods.Error ProgramImplementationSignature) = .ok implementation at implementationSelected
      split at implementationSelected <;> try contradiction
      cases implementationSelected
      rename_i selected
      have member : implementation ∈ [implementation] := List.mem_cons_self
      rw [← selected] at member
      exact (List.mem_filter.mp member).1
    have methodMember : declaration ∈ implementation.methods := by
      change ((match implementation.methods.filter _ with
        | [] => .error _ | [value] => .ok value | values => .error _) : Except ExecutableImplMethods.Error ProgramImplMethodSignature) = .ok declaration at methodSelected
      split at methodSelected <;> try contradiction
      cases methodSelected
      rename_i selected
      have member : declaration ∈ [declaration] := List.mem_cons_self
      rw [← selected] at member
      exact (List.mem_filter.mp member).1
    have traitMember : traitMethod ∈ trait.methods := by
      change ((match trait.methods.filter _ with
        | [] => .error _ | [value] => .ok value | values => .error _) : Except ExecutableImplMethods.Error ProgramTraitMethodSignature) = .ok traitMethod at traitMethodSelected
      split at traitMethodSelected <;> try contradiction
      cases traitMethodSelected
      rename_i selected
      have member : traitMethod ∈ [traitMethod] := List.mem_cons_self
      rw [← selected] at member
      exact (List.mem_filter.mp member).1
    have traitLookup : program.signatures.trait? declaration.traitMethod.trait = some trait := by
      rw [associated, traitOwner]
      change ((match program.signatures.traits.filter _ with
        | [] => .error _ | [value] => .ok value | values => .error _) : Except ExecutableImplMethods.Error ProgramTraitSignature) = .ok trait at traitSelected
      split at traitSelected <;> try contradiction
      cases traitSelected
      rename_i selected
      have contained := List.mem_filter.mp (show trait ∈ program.signatures.traits.filter _ by rw [selected]; simp)
      have idEq : trait.id = _ := of_decide_eq_true contained.2
      unfold ProgramSignatures.trait?
      rw [idEq]
      exact filtered_find selected
    refine ⟨⟨implementation, trait, declaration, generic, headMatch.parameterSubstitution, implementationMember, methodMember,
      traitLookup, traitMember, rfl, methodOwner, associated, ?_, ?_, rfl⟩⟩
    · simpa only [synthetic_eq] using mapError_ok genericChecked
    · simpa only [synthetic_eq] using mapError_ok specializedChecked

private theorem retained_of_target {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {fuel : Nat} {targets : List ImplementationMethodCheckTarget} {methods : List CheckedImplementationMethod}
    (checked : ImplementationMethodBodiesChecked environment signatures fuel targets methods)
    {target : ImplementationMethodCheckTarget} (member : target ∈ targets) :
    ∃ retained, retained ∈ methods ∧ ImplementationMethodBodyChecked environment signatures fuel target retained := by
  induction checked with
  | nil => cases member
  | @cons head rest checkedMethod checkedMethods headChecked tailChecked ih =>
    rcases List.mem_cons.mp member with same | tail
    · subst target; exact ⟨checkedMethod, List.mem_cons_self, headChecked⟩
    · obtain ⟨retained, member, provenance⟩ := ih tail
      exact ⟨retained, List.mem_cons_of_mem _ member, provenance⟩

/-- Same signature and fuel identify the entire retained checker carrier,
including its typed graph, inference substitution and ordered evidence ledger. -/
theorem Selection.retained {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {method : ExecutableImplMethods.CheckedMethod} (selected : Selection program method) :
    ∃ retained, retained ∈ program.methods ∧ retained.id = method.id ∧ selected.generic = retained.checked := by
  have member : (⟨selected.implementation, selected.declaration⟩ : ImplementationMethodCheckTarget) ∈
      implementationMethodCheckTargets program.signatures := by
    apply List.mem_flatMap.mpr
    exact ⟨_, selected.implementationMember, List.mem_map.mpr ⟨_, selected.methodMember, rfl⟩⟩
  obtain ⟨retained, member, provenance⟩ := retained_of_target (checkLoadedProgram_success_body_checks loadedAccepted).2 member
  cases provenance with
  | intro idEq traitLookup checked =>
    have sameTrait := Option.some.inj (traitLookup.symm.trans selected.traitLookup)
    subst_vars
    have same := Except.ok.inj (selected.bodyChecked.symm.trans checked)
    exact ⟨retained, member, idEq.trans selected.methodId.symm, same⟩

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) : action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

/-- Successful specialization supplies its actual canonical substitution and
complete rewritten checker carrier; no equality of keys is used here. -/
theorem specialization_fields {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    specialized.function = SourceSpecialization.applyCheckedFunction specialized.parameterSubstitution generic ∧
    specialized.assumptions = signature.scheme.predicates.map
      (ProgramPredicate.applyParameters specialized.parameterSubstitution) := by
  unfold SourceSpecialization.specializeFunction at accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
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
  cases analysis : SourceStageAnalysis.analyzeFunction (SourceSpecialization.applyCheckedFunction canonical generic) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
    simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
    subst specialized
    exact ⟨rfl, rfl⟩

/-- The retained generic method is authenticated by the actual loaded checker.
This record carries static provenance only. -/
structure Certificate (program : CheckedProgram) (method : ExecutableImplMethods.CheckedMethod)
    extends Selection program method where
  retained : CheckedImplementationMethod
  retainedMember : retained ∈ program.methods
  retainedId : retained.id = method.id
  completeCheckedEq : generic = retained.checked

/-- The real coercion selector and loaded checker use the same budget 1024.
No conclusion about different checking budgets is needed or made. -/
theorem of_accepted {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {step : CoercionStep}
    {method : ExecutableImplMethods.CheckedMethod}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method) :
    Nonempty (Certificate program method) := by
  obtain ⟨outer⟩ := CallableCoercionMethodCertificates.of_accepted accepted
  obtain ⟨selected⟩ := selection outer.checked
  obtain ⟨retained, member, sameId, sameChecked⟩ := selected.retained loadedAccepted
  exact ⟨⟨selected, retained, member, sameId, sameChecked⟩⟩

theorem of_checked_program {raw : Workspace.RawWorkspace} {program : CheckedProgram}
    (checked : Frontend.checkProgram raw 1024 = .ok program)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {step : CoercionStep}
    {method : ExecutableImplMethods.CheckedMethod}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method) :
    Nonempty (Certificate program method) := by
  obtain ⟨loaded, _, loadedAccepted⟩ := checkProgram_success_load checked
  exact of_accepted loadedAccepted accepted

namespace Certificate
variable {program : CheckedProgram} {method : ExecutableImplMethods.CheckedMethod}

/-- Full application is anchored at the catalog's retained checker result. -/
theorem applied (receipt : Certificate program method) :
    method.specialized.function = SourceSpecialization.applyCheckedFunction
      method.specialized.parameterSubstitution receipt.retained.checked := by
  rw [← receipt.completeCheckedEq]
  exact (specialization_fields receipt.specialized).1

/-- This is the independent source operation, including every node's raw type,
requirements, coercion metadata and exact binder identities. -/
theorem body (receipt : Certificate program method) :
    method.specialized.function.typedBody = StructuralSubstitution.applyTypedSource
      method.specialized.parameterSubstitution receipt.retained.checked.typedBody := by
  rw [receipt.applied, StructuralSubstitution.applyTypedSource_frontend_eq]
  rfl

theorem owner (receipt : Certificate program method) :
    method.specialized.function.typedBody.owner = receipt.implementation.id := by
  rw [receipt.applied, SourceSpecialization.applyCheckedFunction_bodyOwner, ← receipt.completeCheckedEq]
  exact checkFunctionBody_success_typedBody_owner receipt.bodyChecked

theorem inputs (receipt : Certificate program method) :
    method.specialized.function.typedBody.inputs = receipt.retained.checked.typedBody.inputs.map
      (StructuralSubstitution.applyBinder method.specialized.parameterSubstitution) := by
  rw [receipt.body]
  rfl

theorem roots (receipt : Certificate program method) :
    method.specialized.function.typedBody.roots = receipt.retained.checked.typedBody.roots := by
  rw [receipt.body]
  rfl

/-- Ordered evidence is substituted field by field, including full recursive
implementation trees, without sorting or dropping repeated requirements. -/
theorem ledger (receipt : Certificate program method) :
    method.specialized.function.solvedRequirements = receipt.retained.checked.solvedRequirements.map
      (StructuralSubstitution.applySolvedRequirement method.specialized.parameterSubstitution) := by
  rw [receipt.applied]
  simp only [SourceSpecialization.applyCheckedFunction]
  congr 1
  funext requirement
  exact (StructuralSubstitution.applySolvedRequirement_frontend_eq _ _).symm

theorem result (receipt : Certificate program method) :
    method.specialized.function.inferredBodyType =
      method.specialized.parameterSubstitution.apply receipt.retained.checked.inferredBodyType ∧
    method.specialized.function.type = method.specialized.parameterSubstitution.apply receipt.retained.checked.type := by
  rw [receipt.applied]
  exact ⟨rfl, rfl⟩

/-- The synthetic checking context keeps trait, implementation and method
assumptions in their original order before canonical specialization. -/
theorem assumptions (receipt : Certificate program method) :
    method.specialized.assumptions =
      (receipt.implementation.methodAssumptions receipt.trait receipt.declaration).map
        (ProgramPredicate.applyParameters method.specialized.parameterSubstitution) :=
  (specialization_fields receipt.specialized).2

end Certificate

end Solcore.SourceSemantics.CoreLowering.CallableCoercionBodyProvenance
