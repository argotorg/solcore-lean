import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.Frontend.SourceInference.FunctionFuelAgreement
import Solcore.SourceSemantics.SubstitutionCorrespondence
import Solcore.SourceSemantics.ProgramCheckingSoundness

/-!
# Coercions: method certificates and source selection

Method certificates, body provenance, method instantiation, evidence origins and source selection of coercions.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodCertificates
/-! The actual coercion selector retains the primary tree and ordered method
evidence used to check its synthetic method. These receipts concern selection
and dictionaries; they do not identify the plan's emitted closure or prove its
body semantics. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodCertificates
open Frontend SourceInference
abbrev RawEvidence := TypedTraitResolution.Evidence
abbrev Dictionary := SourceTypedRuntime.RuntimeEvidenceEnvironment

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

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

private theorem method_fields {program : CheckedProgram} {primary : RawEvidence}
    {methodEvidence : Dictionary} {arity : Nat} {name : String}
    {method : ExecutableImplMethods.CheckedMethod}
    (accepted : ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary methodEvidence arity name = .ok method) :
    ∃ goal implementation, primary = .byImpl goal implementation method.implementationPremises ∧
      method.methodPremises = methodEvidence := by
  cases primary with
  | byImpl goal implementation premises =>
    simp only [ExecutableImplMethods.checkMethodWithEvidenceAndArity] at accepted
    split at accepted <;> try contradiction
    try simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
    split at accepted <;> try contradiction
    try simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨implementationSignature, _, accepted⟩ := bind_ok accepted
    split at accepted <;> try contradiction
    split at accepted <;> try contradiction
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨trait, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨implementationMethod, _, accepted⟩ := bind_ok accepted
    obtain ⟨traitMethod, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨genericChecked, _, accepted⟩ := bind_ok accepted
    obtain ⟨specialized, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    cases accepted
    exact ⟨goal, _, rfl, rfl⟩

open Solcore.SourceSemantics.Dynamic CallableEvidenceEnvironment
open CallableNamedMetadata (evidence environment evidence_represents)

private theorem validated_requirement {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : Dictionary} {id : RequirementId} {goal : ProgramPredicate} {raw : RawEvidence}
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available id goal = .ok raw) :
    EvidenceValid [] program.signatures.resolutionRules goal (evidence raw) := by
  have finish : ∀ selected,
      (match (TypedTraitResolution.resolve program.signatures.resolutionRules 32 goal).outcome with
        | .noSolution => Except.error (SourceTypedRuntime.RuntimeError.callEvidenceResolutionNoSolution caller.key node.id id goal)
        | .inconclusive reason => .error (.callEvidenceResolutionInconclusive caller.key node.id id reason)
        | .success chosen => if chosen == selected then .ok () else
            let .byImpl _ implementation _ := selected
            .error (.callEvidenceNotSelected caller.key node.id id goal implementation)) = .ok () →
      EvidenceValid [] program.signatures.resolutionRules goal (evidence selected) := by
    intro selected validated
    have checked : SourceCompilationPlan.validateRuntimeEvidenceSelection program.signatures caller.key 0 [goal] [selected] = .ok () := by
      split at validated <;> try contradiction
      split at validated
      · simp only [SourceCompilationPlan.validateRuntimeEvidenceSelection, *, if_true]; rfl
      · cases selected; cases validated
    have valid := CallableAuthenticatedCallEvidence.selection_valid checked
    cases valid with
    | cons head tail => exact head
  simp only [SourceCompilationPlan.exactRuntimeRequirementEvidence, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  obtain ⟨row, _, accepted⟩ := bind_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  cases retained : row.evidence with
  | implementation chosen =>
    simp only [retained] at accepted
    obtain ⟨_, validated, accepted⟩ := bind_ok accepted
    cases accepted
    exact finish _ validated
  | assumption predicate =>
    simp only [retained] at accepted
    split at accepted <;> try contradiction
    obtain ⟨_, validated, accepted⟩ := bind_ok accepted
    cases accepted
    exact finish _ validated

private theorem validated_requirements {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available returned : Dictionary} {ids : List RequirementId} {goals : List ProgramPredicate}
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidenceList program caller node available ids goals = .ok returned) :
    Forall₂ (fun goal raw => EvidenceValid [] program.signatures.resolutionRules goal (evidence raw)) goals returned := by
  induction ids generalizing goals returned with
  | nil => cases goals <;> cases accepted; exact .nil
  | cons id ids ih =>
    cases goals with
    | nil => cases accepted
    | cons goal goals =>
      unfold SourceCompilationPlan.exactRuntimeRequirementEvidenceList at accepted
      obtain ⟨head, headAccepted, accepted⟩ := bind_ok accepted
      obtain ⟨tail, tailAccepted, accepted⟩ := bind_ok accepted
      cases accepted
      exact .cons (validated_requirement headAccepted) (ih tailAccepted)

/-- The actual selector fixes each complete evidence tree and its ordered
requirement position. The trait arity and method name remain explicit. -/
structure Roots (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : Dictionary) (primaryId : RequirementId)
    (methodIds : List RequirementId) (arity : Nat) (name : String)
    (method : ExecutableImplMethods.CheckedMethod) where
  primary : RawEvidence
  methodEvidence : Dictionary
  primarySelected : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available
    primaryId (SourceCompilationPlan.runtimeEvidenceGoal primary) = .ok primary
  methodsSelected : SourceCompilationPlan.exactRuntimeRequirementEvidenceList program caller node available
    methodIds (methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal) = .ok methodEvidence
  checked : ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary methodEvidence arity name = .ok method
  shape : ∃ goal implementation, primary = .byImpl goal implementation method.implementationPremises
  methods : method.methodPremises = methodEvidence
  primaryValid : EvidenceValid [] program.signatures.resolutionRules (SourceCompilationPlan.runtimeEvidenceGoal primary) (evidence primary)
  methodsValid : Forall₂ (fun goal raw => EvidenceValid [] program.signatures.resolutionRules goal (evidence raw))
    (methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal) methodEvidence

/-- One common constructor consumes the actual primary and method selections;
neither validity nor the returned evidence is inferred from a specialization key. -/
def Roots.of_selected {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : Dictionary} {primaryId : RequirementId}
    {methodIds : List RequirementId} {arity : Nat} {name : String}
    {method : ExecutableImplMethods.CheckedMethod} {goal : ProgramPredicate}
    {goals : List ProgramPredicate} {primary : RawEvidence} {methodEvidence : Dictionary}
    (primarySelected : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available
      primaryId goal = .ok primary)
    (methodsSelected : SourceCompilationPlan.exactRuntimeRequirementEvidenceList program caller node available
      methodIds goals = .ok methodEvidence)
    (checked : ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary methodEvidence arity name = .ok method) :
    Roots program caller node available primaryId methodIds arity name method := {
  primary := primary
  methodEvidence := methodEvidence
  primarySelected := by
    have same := SourceCompilationPlan.exactRuntimeRequirementEvidence_success_goal _ _ _ _ _ _ _ primarySelected
    rwa [same]
  methodsSelected := by
    have same := SourceCompilationPlan.exactRuntimeRequirementEvidenceList_success_matches _ _ _ _ _ _ _ methodsSelected
    change methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal = _ at same
    rwa [same]
  checked := checked
  shape := by
    obtain ⟨goal, implementation, shape, _⟩ := method_fields checked
    exact ⟨goal, implementation, shape⟩
  methods := by
    obtain ⟨_, _, _, methods⟩ := method_fields checked
    exact methods
  primaryValid := by
    have same := SourceCompilationPlan.exactRuntimeRequirementEvidence_success_goal _ _ _ _ _ _ _ primarySelected
    rw [same]
    exact validated_requirement primarySelected
  methodsValid := by
    have same := SourceCompilationPlan.exactRuntimeRequirementEvidenceList_success_matches _ _ _ _ _ _ _ methodsSelected
    change methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal = _ at same
    rw [same]
    exact validated_requirements methodsSelected
}

/-- Exact roots of the returned method dictionary, taken from the real
selector. All validity facts concern complete evidence trees. -/
structure Certificate (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : Dictionary) (step : CoercionStep)
    (method : ExecutableImplMethods.CheckedMethod) where
  primary : RawEvidence
  methodEvidence : Dictionary
  primarySelected : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available
    step.requirement (SourceCompilationPlan.runtimeEvidenceGoal primary) = .ok primary
  methodsSelected : SourceCompilationPlan.exactRuntimeRequirementEvidenceList program caller node available
    step.methodRequirements (methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal) = .ok methodEvidence
  checked : ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary methodEvidence 2 "coerce" = .ok method
  shape : ∃ goal implementation, primary = .byImpl goal implementation method.implementationPremises
  methods : method.methodPremises = methodEvidence
  primaryValid : EvidenceValid [] program.signatures.resolutionRules (SourceCompilationPlan.runtimeEvidenceGoal primary) (evidence primary)
  methodsValid : Forall₂ (fun goal raw => EvidenceValid [] program.signatures.resolutionRules goal (evidence raw))
    (methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal) methodEvidence

def Certificate.roots {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : Dictionary} {step : CoercionStep}
    {method : ExecutableImplMethods.CheckedMethod}
    (receipt : Certificate program caller node available step method) :
    Roots program caller node available step.requirement step.methodRequirements 2 "coerce" method :=
  ⟨receipt.primary, receipt.methodEvidence, receipt.primarySelected, receipt.methodsSelected,
    receipt.checked, receipt.shape, receipt.methods, receipt.primaryValid, receipt.methodsValid⟩

/-- No separate premise is required for an intermediate method selection. -/
theorem of_accepted {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : Dictionary} {step : CoercionStep}
    {method : ExecutableImplMethods.CheckedMethod}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method) :
    Nonempty (Certificate program caller node available step method) := by
  simp only [SourceCompilationPlan.checkedCoercionMethod, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  obtain ⟨row, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, accepted⟩ := require_ok accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  obtain ⟨_, accepted⟩ := require_ok accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  obtain ⟨primary, primarySelected, accepted⟩ := bind_ok accepted
  obtain ⟨methodEvidence, methodsSelected, accepted⟩ := bind_ok accepted
  have checked := mapError_ok accepted
  let roots := Roots.of_selected primarySelected methodsSelected checked
  exact ⟨⟨roots.primary, roots.methodEvidence, roots.primarySelected, roots.methodsSelected,
    roots.checked, roots.shape, roots.methods, roots.primaryValid, roots.methodsValid⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionBodyProvenance
/-! A selected coercion method is rechecked with its actual synthetic signature.
The static method-checking receipt identifies its complete generic checker
result with the original retained method catalog. Specialization is then connected to
independent structural source substitution. Runtime calls and closure history
remain separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
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

/-- The same synthetic method check identifies the entire retained checker carrier,
including its typed graph, inference substitution and ordered evidence ledger. -/
theorem Selection.retained {program : CheckedProgram}
    (loadedAccepted : CallableMethodBodyCoherence.Checked program)
    {method : ExecutableImplMethods.CheckedMethod} (selected : Selection program method) :
    ∃ retained, retained ∈ program.methods ∧ retained.id = method.id ∧ selected.generic = retained.checked := by
  have member : (⟨selected.implementation, selected.declaration⟩ : ImplementationMethodCheckTarget) ∈
      implementationMethodCheckTargets program.signatures := by
    apply List.mem_flatMap.mpr
    exact ⟨_, selected.implementationMember, List.mem_map.mpr ⟨_, selected.methodMember, rfl⟩⟩
  obtain ⟨checkingFuel, checkedBodies⟩ := loadedAccepted
  obtain ⟨retained, member, provenance⟩ := retained_of_target checkedBodies member
  cases provenance with
  | intro idEq traitLookup checked =>
    have sameTrait := Option.some.inj (traitLookup.symm.trans selected.traitLookup)
    subst_vars
    have same := checkFunctionBody_success_unique_fuel selected.bodyChecked checked
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

/-- The real coercion selector and static method receipt use the same budget 1024.
The whole-program checker budget is independent of this receipt. -/
theorem of_accepted {program : CheckedProgram}
    (loadedAccepted : CallableMethodBodyCoherence.Checked program)
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
  exact of_accepted (CallableMethodBodyCoherence.of_loaded loadedAccepted) accepted

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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodInstantiation
/-! The method checker's actual head match and declaration-order specialization
are connected to independent source method instantiation. Type formation stays
an independent static obligation. No body execution or closure history is stored. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodInstantiation
open Frontend SourceInference TypeSystem

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) : action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

/-- The certificate collector changes order only: every key it visits uses the
first matching replacement from the actual caller substitution. -/
theorem collected_lookup (keys : List TypeParameterId) (supplied : ParameterSubstitution)
    {parameter : TypeParameterId} (member : parameter ∈ keys) :
    (ParameterSubstitution.lookup? (keys.map fun key => (key, (supplied.lookup? key).getD (.parameter key))) parameter).getD (.parameter parameter) =
      (supplied.lookup? parameter).getD (.parameter parameter) := by
  induction keys with
  | nil => cases member
  | cons key keys ih =>
    by_cases same : key = parameter
    · subst key; simp [ParameterSubstitution.lookup?]
    · have rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      simpa only [List.map_cons, ParameterSubstitution.lookup?, same, if_false] using ih rest

/-- Successful matching retains the checked head equation with the actual
supplied map, reordered by the rule collector. The metavariable map is not erased. -/
theorem matched_head {parameters : List TypeParameterId} {rule : TypedTraitResolution.ImplRule}
    {goal : ProgramPredicate} {result : TypedTraitResolution.HeadMatch}
    (matched : TypedTraitResolution.matchImplHeadWithParameters? parameters rule goal = some result) :
    ∃ variables : Substitution,
      (⟨(TypedTraitResolution.ruleParameters rule).map fun parameter =>
        (parameter, (result.parameterSubstitution.lookup? parameter).getD (.parameter parameter)), variables⟩ :
        TypedTraitResolution.RuleMatchSubstitution).applyPredicate rule.head = goal := by
  unfold TypedTraitResolution.matchImplHeadWithParameters? at matched
  cases certified : TypedTraitResolution.matchImplHeadWithParametersCertified? parameters rule goal with
  | none => simp [certified] at matched
  | some found =>
    simp only [certified, Option.map_some, Option.some.injEq] at matched
    subst result
    unfold TypedTraitResolution.matchImplHeadWithParametersCertified? at certified
    try dsimp only at certified
    split at certified <;> try contradiction
    try dsimp only at certified
    split at certified <;> try contradiction
    try dsimp only at certified
    split at certified <;> try contradiction
    try dsimp only at certified
    split at certified <;> try contradiction
    try dsimp only at certified
    split at certified <;> try contradiction
    rename_i headEq
    cases certified
    exact ⟨_, headEq⟩

/-- The canonical specialization looks up the same supplied replacement for
every declaration parameter, even when the supplied list has another order. -/
theorem specialization_lookup {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    ∀ parameter ∈ signature.scheme.parameters,
      specialized.parameterSubstitution.lookup? parameter = supplied.lookup? parameter := by
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
  obtain ⟨canonical, selected, accepted⟩ := bind_ok accepted
  have lookupEq : ∀ parameter ∈ signature.scheme.parameters,
      canonical.lookup? parameter = supplied.lookup? parameter := by
    clear accepted
    generalize signature.scheme.parameters = declared at selected ⊢
    induction declared generalizing canonical with
    | nil => simp
    | cons head rest ih =>
      change (match supplied.lookup? head with
        | none => Except.error (SourceSpecialization.Error.missingSuppliedParameter head)
        | some type => match SourceSpecialization.firstNonConcrete type with
          | some reason => Except.error (SourceSpecialization.Error.nonConcreteArgument head reason)
          | none => do pure ((head, type) :: (← (_ : Except SourceSpecialization.Error ParameterSubstitution)))) = .ok canonical at selected
      split at selected <;> try contradiction
      rename_i type found
      split at selected <;> try contradiction
      obtain ⟨tail, tailAccepted, selected⟩ := bind_ok selected
      cases selected
      intro parameter member
      by_cases same : head = parameter
      · subst parameter; simp only [ParameterSubstitution.lookup?, if_true, found]
      · have restMember := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        simpa only [ParameterSubstitution.lookup?, same, if_false] using ih tail tailAccepted parameter restMember


  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction (SourceSpecialization.applyCheckedFunction canonical generic) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
    simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
    subst specialized
    change ∀ parameter ∈ signature.scheme.parameters, canonical.lookup? parameter = supplied.lookup? parameter
    exact lookupEq


private theorem simultaneous_type {substitution : TypedTraitResolution.RuleMatchSubstitution}
    {supplied : ParameterSubstitution} (type : Ty)
    (rigid : ∀ metavariable, metavariable ∉ type.freeVariables)
    (agrees : ∀ parameter, TypeParameterOccurs parameter type →
      (substitution.parameters.lookup? parameter).getD (.parameter parameter) =
        (supplied.lookup? parameter).getD (.parameter parameter)) :
    substitution.applyType type = supplied.apply type := by
  induction type with
  | «variable» metavariable => exact False.elim (rigid metavariable (by simp [Ty.freeVariables]))
  | parameter parameter => exact agrees parameter rfl
  | constructor constructor => rfl
  | error => rfl
  | application left right ihLeft ihRight
  | function left right ihLeft ihRight
  | product left right ihLeft ihRight
  | mapping left right ihLeft ihRight =>
    simp only [TypedTraitResolution.RuleMatchSubstitution.applyType, ParameterSubstitution.apply]
    congr 1
    · apply ihLeft
      · intro metavariable member; apply rigid metavariable; simp_all
      · intro parameter member; exact agrees parameter (Or.inl member)
    · apply ihRight
      · intro metavariable member; apply rigid metavariable; simp_all
      · intro parameter member; exact agrees parameter (Or.inr member)
  | proxy inner ih | comptime inner ih =>
    simp only [TypedTraitResolution.RuleMatchSubstitution.applyType, ParameterSubstitution.apply]
    exact congrArg _ (ih rigid agrees)

/-- The collector order is extensionally irrelevant at the original rigid
head. Flexible-head freedom is an explicit source formation condition. -/
theorem matched_parameter_head {parameters : List TypeParameterId} {rule : TypedTraitResolution.ImplRule}
    {goal : ProgramPredicate} {result : TypedTraitResolution.HeadMatch}
    (matched : TypedTraitResolution.matchImplHeadWithParameters? parameters rule goal = some result)
    (rigid : ∀ metavariable, ¬ TypedTraitResolution.VariableOccursInPredicate metavariable rule.head) :
    ProgramPredicate.applyParameters result.parameterSubstitution rule.head = goal := by
  obtain ⟨variables, headEq⟩ := matched_head matched
  have typeEq : ∀ type, type = rule.head.subject ∨ type ∈ rule.head.arguments →
      (⟨(TypedTraitResolution.ruleParameters rule).map fun parameter =>
        (parameter, (result.parameterSubstitution.lookup? parameter).getD (.parameter parameter)), variables⟩ :
        TypedTraitResolution.RuleMatchSubstitution).applyType type = result.parameterSubstitution.apply type := by
    intro type position
    apply simultaneous_type
    · intro metavariable member; apply rigid metavariable
      rcases position with rfl | memberType
      · exact Or.inl member
      · exact Or.inr ⟨_, memberType, member⟩
    · intro parameter occurs
      apply collected_lookup
      apply TypedTraitResolution.mem_ruleParameters_iff.mpr
      apply Or.inl
      apply TypedTraitResolution.mem_predicateParameters_iff.mpr
      rcases position with rfl | memberType
      · exact Or.inl occurs
      · exact Or.inr ⟨_, memberType, occurs⟩
  have rewritten : (⟨(TypedTraitResolution.ruleParameters rule).map fun parameter =>
        (parameter, (result.parameterSubstitution.lookup? parameter).getD (.parameter parameter)), variables⟩ :
        TypedTraitResolution.RuleMatchSubstitution).applyPredicate rule.head =
      ProgramPredicate.applyParameters result.parameterSubstitution rule.head := by
    simp only [TypedTraitResolution.RuleMatchSubstitution.applyPredicate, ProgramPredicate.applyParameters]
    congr 1
    · exact typeEq _ (Or.inl rfl)
    · apply List.map_congr_left; intro type member; exact typeEq _ (Or.inr member)
  exact rewritten.symm.trans headEq

private theorem apply_type_congr {left right : ParameterSubstitution} (type : Ty)
    (agrees : ∀ parameter, TypeParameterOccurs parameter type → left.lookup? parameter = right.lookup? parameter) :
    left.apply type = right.apply type := by
  induction type with
  | «variable» metavariable => rfl
  | parameter parameter => simp only [ParameterSubstitution.apply, agrees parameter rfl]
  | constructor constructor => rfl
  | error => rfl
  | application left right ihLeft ihRight
  | function left right ihLeft ihRight
  | product left right ihLeft ihRight
  | mapping left right ihLeft ihRight =>
    simp only [ParameterSubstitution.apply]
    congr 1
    · exact ihLeft (fun parameter member => agrees parameter (Or.inl member))
    · exact ihRight (fun parameter member => agrees parameter (Or.inr member))
  | proxy inner ih | comptime inner ih => exact congrArg _ (ih agrees)

/-- Source scoping fixes which declaration parameters may occur. The actual
canonicalization preserves every replacement at those positions. -/
theorem specialization_predicate {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (predicate : ProgramPredicate)
    (covered : ∀ parameter, TypedTraitResolution.ParameterOccursInPredicate parameter predicate →
      parameter ∈ signature.scheme.parameters) :
    ProgramPredicate.applyParameters specialized.parameterSubstitution predicate =
      ProgramPredicate.applyParameters supplied predicate := by
  simp only [ProgramPredicate.applyParameters]
  congr 1
  · apply apply_type_congr; intro parameter occurs
    exact specialization_lookup accepted parameter (covered parameter (Or.inl occurs))
  · apply List.map_congr_left; intro type member
    apply apply_type_congr; intro parameter occurs
    exact specialization_lookup accepted parameter (covered parameter (Or.inr ⟨_, member, occurs⟩))


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

/-- These fields are outputs and guards of the real selector. In particular the
head match is the one that supplied the actual specialization request. -/
structure Selection (program : CheckedProgram) (primary : TypedTraitResolution.Evidence)
    (name : String) (method : ExecutableImplMethods.CheckedMethod)
    extends CallableCoercionBodyProvenance.Selection program method where
  goal : ProgramPredicate
  headMatch : TypedTraitResolution.HeadMatch
  primaryShape : primary = .byImpl goal (.declaration implementation.id) method.implementationPremises
  matched : TypedTraitResolution.matchImplHeadWithParameters? implementation.parameters implementation.implRule goal = some headMatch
  suppliedEq : supplied = headMatch.parameterSubstitution
  traitMember : trait ∈ program.signatures.traits
  goalTrait : goal.trait = .declaration trait.id
  declarationName : declaration.name = name
  methodsGoals : method.methodPremises.map SourceCompilationPlan.runtimeEvidenceGoal = method.methodPredicates
  predicates : method.methodPredicates = declaration.wherePredicates.map (ProgramPredicate.applyParameters supplied)

theorem selection {program : CheckedProgram} {primary : TypedTraitResolution.Evidence}
    {evidence : List TypedTraitResolution.Evidence} {arity : Nat} {name : String}
    {method : ExecutableImplMethods.CheckedMethod}
    (accepted : ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary evidence arity name = .ok method) :
    Nonempty (Selection program primary name method) := by
  cases primary with
  | byImpl goal implementationId premises =>
    simp only [ExecutableImplMethods.checkMethodWithEvidenceAndArity] at accepted
    split at accepted <;> try contradiction
    rename_i implementationId
    try simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
    split at accepted <;> try contradiction
    rename_i traitId goalTrait
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
    obtain ⟨closedPredicates, accepted⟩ := require_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨resultUnit, methodsValidated, accepted⟩ := bind_ok accepted
    cases resultUnit
    have methodsGoals : evidence.map SourceCompilationPlan.runtimeEvidenceGoal =
        traitMethod.wherePredicates.map (ProgramPredicate.applyParameters (trait.parameters.zip (goal.subject :: goal.arguments))) := by
      repeat clear accepted
      generalize traitMethod.wherePredicates.map (ProgramPredicate.applyParameters (trait.parameters.zip (goal.subject :: goal.arguments))) = predicates at methodsValidated ⊢
      change (if predicates.length = evidence.length then _ else Except.error
        (ExecutableImplMethods.Error.methodEvidenceCountMismatch declaration.id predicates.length evidence.length)) = .ok () at methodsValidated
      obtain ⟨lengths, checked⟩ := require_ok methodsValidated
      clear methodsValidated
      generalize (0 : Nat) = index at checked
      induction predicates generalizing evidence index with
      | nil => cases evidence <;> simp_all
      | cons predicate rest ih =>
        cases evidence with
        | nil => simp at lengths
        | cons raw remaining =>
          cases raw with
          | byImpl actual implementation premises =>
            change (if actual = predicate then _ else Except.error
              (ExecutableImplMethods.Error.methodEvidenceGoalMismatch declaration.id index predicate actual)) = .ok () at checked
            obtain ⟨same, checked⟩ := require_ok checked
            split at checked <;> try contradiction
            split at checked <;> try contradiction
            have tails : rest.length = remaining.length := by simpa using lengths
            simpa only [List.map_cons, SourceCompilationPlan.runtimeEvidenceGoal, same] using
              congrArg (List.cons predicate) (ih tails (index + 1) checked)
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
    have implementationIdentity : implementation.id = implementationId := by
      change ((match program.signatures.implementations.filter _ with
        | [] => .error _ | [value] => .ok value | values => .error _) : Except ExecutableImplMethods.Error ProgramImplementationSignature) = .ok implementation at implementationSelected
      split at implementationSelected <;> try contradiction
      cases implementationSelected
      rename_i selected
      have member : implementation ∈ [implementation] := List.mem_cons_self
      rw [← selected] at member
      exact of_decide_eq_true (List.mem_filter.mp member).2
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
    have declarationName : declaration.name = name := by
      change ((match implementation.methods.filter _ with
        | [] => .error _ | [value] => .ok value | values => .error _) : Except ExecutableImplMethods.Error ProgramImplMethodSignature) = .ok declaration at methodSelected
      split at methodSelected <;> try contradiction
      cases methodSelected
      rename_i selected
      have member : declaration ∈ [declaration] := List.mem_cons_self
      rw [← selected] at member
      exact of_decide_eq_true (List.mem_filter.mp member).2
    have traitEntry : trait ∈ program.signatures.traits ∧ trait.id = traitId := by
      change ((match program.signatures.traits.filter _ with
        | [] => .error _ | [value] => .ok value | values => .error _) : Except ExecutableImplMethods.Error ProgramTraitSignature) = .ok trait at traitSelected
      split at traitSelected <;> try contradiction
      cases traitSelected
      rename_i selected
      have member : trait ∈ [trait] := List.mem_cons_self
      rw [← selected] at member
      exact ⟨(List.mem_filter.mp member).1, of_decide_eq_true (List.mem_filter.mp member).2⟩
    refine ⟨{
      implementation, trait, declaration, generic, supplied := headMatch.parameterSubstitution
      implementationMember, methodMember, traitLookup, traitMethodMember := traitMember
      methodId := rfl, methodOwner, association := associated
      bodyChecked := by simpa only [CallableCoercionBodyProvenance.synthetic_eq] using mapError_ok genericChecked
      specialized := by simpa only [CallableCoercionBodyProvenance.synthetic_eq] using mapError_ok specializedChecked
      checkedEq := rfl
      goal, headMatch, suppliedEq := rfl, matched := headMatched
      primaryShape := by rw [implementationIdentity]
      traitMember := traitEntry.1
      goalTrait := by rw [traitEntry.2]; exact goalTrait
      declarationName
      methodsGoals
      predicates := closedPredicates
    }⟩


/-- Source formation facts are separate from runtime evidence validity. They
exclude flexible implementation heads and unrelated rigid parameters. -/
structure Formation (implementation : ProgramImplementationSignature)
    (declaration : ProgramImplMethodSignature) : Prop where
  parameters : implementation.parameters.Nodup
  headRigid : ∀ metavariable, ¬ TypedTraitResolution.VariableOccursInPredicate metavariable implementation.head
  headParameters : ∀ parameter, TypedTraitResolution.ParameterOccursInPredicate parameter implementation.head →
    parameter ∈ implementation.parameters
  methodParameters : ∀ predicate ∈ declaration.wherePredicates, ∀ parameter,
    TypedTraitResolution.ParameterOccursInPredicate parameter predicate → parameter ∈ implementation.parameters

/-- The same complete specialized carrier determines every source body field. -/
def bodyInstance (program : CheckedProgram) (method : ExecutableImplMethods.CheckedMethod) : Dynamic.BodyInstance := {
  source := method.specialized.function.typedBody
  resultType := method.specialized.function.inferredBodyType
  context := declarationContext program.signatures method.specialized.function.typedBody.owner []
    method.specialized.assumptions method.specialized.function.solvedRequirements
}

namespace Selection
variable {program : CheckedProgram} {primary : TypedTraitResolution.Evidence} {name : String}
  {method : ExecutableImplMethods.CheckedMethod}

theorem domain (selected : Selection program primary name method) :
    method.specialized.parameterSubstitution.map Prod.fst = selected.implementation.parameters :=
  SourceSpecialization.specializeFunction_parameterDomain selected.specialized

theorem exact_substitution (selected : Selection program primary name method)
    (formed : selected.implementation.parameters.Nodup) :
    SourceSemantics.ParameterSubstitution.Exact method.specialized.parameterSubstitution selected.implementation.parameters :=
  ⟨formed, by rw [SourceSemantics.ParameterSubstitution.domain, selected.domain]⟩

/-- Canonical implementation order and the collector head equation concern the
same map. No equality is inferred from a specialization key. -/
theorem determines (selected : Selection program primary name method)
    (formed : Formation selected.implementation selected.declaration) :
    Dynamic.ImplementationHeadDetermines selected.implementation selected.goal method.specialized.parameterSubstitution := by
  refine ⟨selected.domain, selected.exact_substitution formed.parameters, ?_⟩
  rw [specialization_predicate selected.specialized selected.implementation.head formed.headParameters,
    selected.suppliedEq]
  exact matched_parameter_head selected.matched formed.headRigid

theorem method_predicates (selected : Selection program primary name method)
    (formed : Formation selected.implementation selected.declaration) :
    method.methodPredicates = selected.declaration.wherePredicates.map
      (ProgramPredicate.applyParameters method.specialized.parameterSubstitution) := by
  rw [selected.predicates]
  apply List.map_congr_left
  intro predicate member
  exact (specialization_predicate selected.specialized predicate (formed.methodParameters predicate member)).symm

/-- Actual same-fuel retained checking and structural substitution yield the
source method instantiation. Range formation is not inferred from groundness. -/
theorem instantiates     (loadedAccepted : CallableMethodBodyCoherence.Checked program)
    (selected : Selection program primary name method)
    (formed : selected.implementation.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures program.signatures) method.specialized.parameterSubstitution) :
    ∃ definition, definition ∈ (Program.ofChecked program).methods ∧ definition.id = selected.declaration.id ∧
      Dynamic.TraitMethodInstantiates (Program.ofChecked program) selected.implementation selected.declaration selected.trait
        definition method.specialized.parameterSubstitution (bodyInstance program method) := by
  obtain ⟨retained, member, idEq, completeEq⟩ := selected.toSelection.retained loadedAccepted
  let receipt : CallableCoercionBodyProvenance.Certificate program method :=
    ⟨selected.toSelection, retained, member, idEq, completeEq⟩
  have owner : retained.checked.declaration = selected.implementation.id := by
    rw [← completeEq]
    exact checkFunctionBody_success_declaration selected.bodyChecked
  have traitOwner : selected.declaration.traitMethod.trait = selected.trait.id := by
    have found := selected.traitLookup
    unfold ProgramSignatures.trait? at found
    have same : decide (selected.trait.id = selected.declaration.traitMethod.trait) = true :=
      List.find?_some (p := fun trait : ProgramTraitSignature => decide (trait.id = selected.declaration.traitMethod.trait)) found
    exact (of_decide_eq_true same).symm
  refine ⟨MethodDefinition.ofChecked retained, List.mem_map.mpr ⟨retained, member, rfl⟩,
    idEq.trans selected.methodId, ?_⟩
  apply Dynamic.TraitMethodInstantiates.intro selected.implementationMember selected.methodMember selected.traitMember
    traitOwner
    (List.mem_map.mpr ⟨retained, member, rfl⟩) (idEq.trans selected.methodId) owner
    (selected.exact_substitution formed) range
  · exact receipt.body
  · exact receipt.result.1
  · change declarationContext program.signatures method.specialized.function.typedBody.owner [] method.specialized.assumptions
      method.specialized.function.solvedRequirements = _
    rw [receipt.owner, receipt.assumptions, receipt.ledger]
    change declarationContext program.signatures selected.implementation.id [] _ _ =
      declarationContext program.signatures retained.checked.declaration [] _ _
    rw [owner]
    rfl

end Selection

end Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodInstantiation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionEvidenceOrigins
/-! Fresh header evidence is justified by the actual caller dictionary when
each header goal is a caller assumption. The two compiler actions use the same
resolver and depth, so their complete trees agree without a cross-fuel
coherence premise. Source method bodies and emitted closure history remain
separate from these dictionary laws. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionEvidenceOrigins
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallableCoercionMethodCertificates (RawEvidence Dictionary)
open CallableNamedMetadata (evidence environment evidence_represents)
open CallableEvidenceEnvironment

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

/-- Every position records its own actual resolver result, including repeats. -/
def Resolved (program : CheckedProgram) (goals : List ProgramPredicate) (raw : Dictionary) : Prop :=
  Forall₂ (fun goal raw => (TypedTraitResolution.resolve program.signatures.resolutionRules 32 goal).outcome = .success raw) goals raw

private theorem validate_goals (key : SourceCompilationPlan.Key) (raw : Dictionary) :
    SourceCompilationPlan.validateRuntimeEvidence key (raw.map SourceCompilationPlan.runtimeEvidenceGoal) raw = .ok () := by
  unfold SourceCompilationPlan.validateRuntimeEvidence
  simp only [List.length_map, if_true]
  generalize indexEq : 0 = index
  clear indexEq
  induction raw generalizing index with
  | nil => rfl
  | cons head tail ih =>
    change (if SourceCompilationPlan.runtimeEvidenceGoal head = SourceCompilationPlan.runtimeEvidenceGoal head then _ else _) = Except.ok ()
    simpa only [if_true] using ih (index := index + 1)

/-- Invert the real materializer, retaining its fresh header resolver spine and
the exact three-way concatenation. The discarded validation still supplies the
full ordered assumption list. -/
theorem materialized_operator {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}
    {dictionary : Dictionary}
    (accepted : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller node selection = .ok dictionary) :
    ∃ headers, Resolved program selection.method.traitPredicates headers ∧
      dictionary = headers ++ selection.method.implementationPremises ++ selection.method.methodPremises ∧
      dictionary.map SourceCompilationPlan.runtimeEvidenceGoal = selection.method.specialized.assumptions := by
  rcases selection with ⟨requirement, method⟩
  cases method with
  | mk id traitMethod predicates implementationPredicates implementationPremises methodPredicates methodPremises synthetic checked specialized =>
    induction predicates generalizing specialized dictionary with
    | nil =>
      unfold SourceCompilationPlan.operatorMethodRuntimeEvidence at accepted
      obtain ⟨headers, headersAccepted, accepted⟩ := bind_ok accepted
      have empty : headers = [] := Except.ok.inj headersAccepted |>.symm
      subst headers
      obtain ⟨_, validated, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨[], .nil, rfl, SourceCompilationPlan.validateRuntimeEvidence_success_matches _ _ _ validated⟩
    | cons goal rest ih =>
      unfold SourceCompilationPlan.operatorMethodRuntimeEvidence at accepted
      obtain ⟨headers, headersAccepted, accepted⟩ := bind_ok accepted
      change (match (TypedTraitResolution.resolve program.signatures.resolutionRules 32 goal).outcome with
        | .noSolution => Except.error (SourceTypedRuntime.RuntimeError.callEvidenceResolutionNoSolution caller.key node.id requirement goal)
        | .inconclusive reason => Except.error (SourceTypedRuntime.RuntimeError.callEvidenceResolutionInconclusive caller.key node.id requirement reason)
        | .success raw => do
          let .byImpl actual _ _ := raw
          if actual != goal then throw (SourceTypedRuntime.RuntimeError.callRequirementEvidenceGoalMismatch caller.key node.id requirement goal actual)
          pure (raw :: (← _))) = .ok headers at headersAccepted
      split at headersAccepted <;> try contradiction
      split at headersAccepted <;> try contradiction
      rename_i actual implementation premises resolution
      split at headersAccepted <;> try contradiction
      obtain ⟨tail, tailAccepted, headersEq⟩ := bind_ok headersAccepted
      cases headersEq
      let tailDictionary := tail ++ implementationPremises ++ methodPremises
      let tailSpecialized := { specialized with assumptions := tailDictionary.map SourceCompilationPlan.runtimeEvidenceGoal }
      have tailRun : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller node
          ⟨requirement, ⟨id, traitMethod, rest, implementationPredicates, implementationPremises, methodPredicates, methodPremises,
            synthetic, checked, tailSpecialized⟩⟩ = .ok tailDictionary := by
        simp only [SourceCompilationPlan.operatorMethodRuntimeEvidence]
        rw [tailAccepted]
        change (do SourceCompilationPlan.validateRuntimeEvidence specialized.key (tailDictionary.map SourceCompilationPlan.runtimeEvidenceGoal) tailDictionary; pure tailDictionary) = .ok tailDictionary
        rw [validate_goals]; rfl
      obtain ⟨found, resolvedTail, tailEq, _⟩ := ih tailSpecialized tailRun
      have same : tail = found := List.append_cancel_right (List.append_cancel_right tailEq)
      obtain ⟨_, validated, accepted⟩ := bind_ok accepted
      cases accepted
      refine ⟨.byImpl actual implementation premises :: tail, .cons resolution ?_, rfl, ?_⟩
      · simpa only [same, Resolved] using resolvedTail
      · exact SourceCompilationPlan.validateRuntimeEvidence_success_matches _ _ _ validated

/-- Coercions use the same materializer and retain their actual primary requirement. -/
theorem materialized {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
    {dictionary : Dictionary}
    (accepted : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary) :
    ∃ headers, Resolved program method.traitPredicates headers ∧
      dictionary = headers ++ method.implementationPremises ++ method.methodPremises ∧
      dictionary.map SourceCompilationPlan.runtimeEvidenceGoal = method.specialized.assumptions :=
  materialized_operator (selection := ⟨step.requirement, method⟩) accepted

private theorem resolved_valid {program : CheckedProgram} {goal : ProgramPredicate} {raw : RawEvidence}
    (resolved : (TypedTraitResolution.resolve program.signatures.resolutionRules 32 goal).outcome = .success raw) :
    EvidenceValid [] program.signatures.resolutionRules goal (evidence raw) := by
  obtain ⟨semantic, represented, valid⟩ := TraitResolutionSoundness.resolve_success_evidenceValid resolved
  rwa [represented.functional (evidence_represents _)] at valid

private theorem resolved_goal {program : CheckedProgram} {goal : ProgramPredicate} {raw : RawEvidence}
    (resolved : (TypedTraitResolution.resolve program.signatures.resolutionRules 32 goal).outcome = .success raw) :
    SourceCompilationPlan.runtimeEvidenceGoal raw = goal := by
  simpa only [evidence_goal] using (resolved_valid resolved).evidence_goal_eq

theorem caller_resolved {program : CheckedProgram} {key : SourceCompilationPlan.Key}
    {goals : List ProgramPredicate} {raw : Dictionary}
    (accepted : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key goals = .ok raw) :
    Resolved program goals raw := by
  induction goals generalizing raw with
  | nil => cases accepted; exact .nil
  | cons goal goals ih =>
    simp only [SourceCompilationPlan.resolveRuntimeEvidenceEnvironment] at accepted
    split at accepted <;> try contradiction
    rename_i chosen resolution
    cases chosen with
    | byImpl actual implementation premises =>
      simp only at accepted
      split at accepted <;> try contradiction
      obtain ⟨tail, tailAccepted, accepted⟩ := bind_ok accepted
      cases accepted
      exact .cons resolution (ih tailAccepted)

/-- Identical goals are resolved by the same actual action. The first matching
caller entry therefore contains the complete fresh tree, not just its goal. -/
theorem Resolved.lookup {program : CheckedProgram} {goals : List ProgramPredicate} {raw : Dictionary}
    (caller : Resolved program goals raw) {goal : ProgramPredicate} {fresh : RawEvidence}
    (member : goal ∈ goals)
    (resolved : (TypedTraitResolution.resolve program.signatures.resolutionRules 32 goal).outcome = .success fresh) :
    (environment raw).LooksUp goal (evidence fresh) := by
  induction caller with
  | nil => cases member
  | @cons first head rest tail headResolved tailResolved ih =>
    have headGoal := resolved_goal headResolved
    by_cases same : first = goal
    · rw [same] at headResolved
      have sameTree := TraitResolution.Outcome.success.inj (headResolved.symm.trans resolved)
      change EvidenceEnvironment.LooksUp ((_, _) :: _) _ _
      rw [← sameTree, headGoal, same]
      exact .head
    · have restMember : goal ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      exact .tail (by simpa only [headGoal] using same) (ih restMember)

private theorem valid_each {rules : List ProgramImplRule} {goals : List ProgramPredicate} {trees : List TraitEvidence}
    (valid : Forall₂ (EvidenceValid [] rules) goals trees) :
    ∀ tree ∈ trees, EvidenceValid [] rules tree.goal tree := by
  induction valid with
  | nil => simp
  | cons head tail ih =>
    intro tree member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [head.evidence_goal_eq] using head
    · exact ih tree member

private theorem raw_valid_each {rules : List ProgramImplRule} {goals : List ProgramPredicate} {raw : Dictionary}
    (valid : Forall₂ (fun goal raw => EvidenceValid [] rules goal (evidence raw)) goals raw) :
    ∀ item ∈ raw, EvidenceValid [] rules (SourceCompilationPlan.runtimeEvidenceGoal item) (evidence item) := by
  induction valid with
  | nil => simp
  | cons head tail ih =>
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · rw [← evidence_goal, head.evidence_goal_eq]
      exact head
    · exact ih item member

private theorem dictionary_valid {rules : List ProgramImplRule} {raw : Dictionary}
    (each : ∀ item ∈ raw, EvidenceValid [] rules (SourceCompilationPlan.runtimeEvidenceGoal item) (evidence item)) :
    (environment raw).Valid rules := by
  induction raw with
  | nil => intro goal tree found; cases found
  | cons head tail ih =>
    intro goal tree found
    cases found with
    | head => exact each head (by simp)
    | tail _ found => exact ih (fun item member => each item (by simp [member])) _ _ found

private theorem assembled_each {caller : EvidenceEnvironment} {roots : List TraitEvidence} {raw : Dictionary}
    (each : ∀ item ∈ raw, EvidenceEntryOriginates caller roots (SourceCompilationPlan.runtimeEvidenceGoal item) (evidence item)) :
    EvidenceEnvironment.AssembledFrom caller roots (raw.map SourceCompilationPlan.runtimeEvidenceGoal) (environment raw) := by
  induction raw with
  | nil => exact .nil
  | cons head tail ih => exact .cons (each head (by simp)) (ih (fun item member => each item (by simp [member])))

private theorem resolved_each {program : CheckedProgram} {goals : List ProgramPredicate} {raw : Dictionary}
    (resolved : Resolved program goals raw) :
    ∀ item ∈ raw, ∃ goal, goal ∈ goals ∧
      (TypedTraitResolution.resolve program.signatures.resolutionRules 32 goal).outcome = .success item := by
  induction resolved with
  | nil => simp
  | @cons goal raw goals raws head tail ih =>
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨goal, by simp, head⟩
    · obtain ⟨selected, member, result⟩ := ih item member
      exact ⟨selected, by simp [member], result⟩

/-- The explicit static profile covers only headers found among actual caller
assumptions. Implementation and method premises keep their selected roots. -/
def CallerCovered (caller : SourceSpecialization.SpecializedFunction) (method : ExecutableImplMethods.CheckedMethod) : Prop :=
  ∀ goal ∈ method.traitPredicates, goal ∈ caller.assumptions

theorem roots_origins {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available dictionary : Dictionary} {primaryId : RequirementId}
    {methodIds : List RequirementId} {arity : Nat} {name : String}
    {method : ExecutableImplMethods.CheckedMethod}
    (selected : CallableCoercionMethodCertificates.Roots program caller node available primaryId methodIds arity name method)
    (covered : CallerCovered caller method)
    (callerAccepted : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (materialization : ∃ headers, Resolved program method.traitPredicates headers ∧
      dictionary = headers ++ method.implementationPremises ++ method.methodPremises ∧
      dictionary.map SourceCompilationPlan.runtimeEvidenceGoal = method.specialized.assumptions) :
    EvidenceEnvironment.AssembledFrom (environment available)
        (evidence selected.primary :: selected.methodEvidence.map evidence) method.specialized.assumptions (environment dictionary) ∧
      (environment dictionary).Valid program.signatures.resolutionRules ∧
      (environment dictionary).map Prod.fst = method.specialized.assumptions := by
  obtain ⟨headers, resolvedHeaders, shape, goals⟩ := materialization
  have callerResolved := caller_resolved callerAccepted
  have roots : ∀ item ∈ dictionary, EvidenceEntryOriginates (environment available)
      (evidence selected.primary :: selected.methodEvidence.map evidence)
      (SourceCompilationPlan.runtimeEvidenceGoal item) (evidence item) := by
    intro item member
    rw [shape] at member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · obtain ⟨goal, goalMember, resolved⟩ := resolved_each resolvedHeaders item member
        rw [resolved_goal resolved]
        exact .caller (callerResolved.lookup (covered _ goalMember) resolved)
      · obtain ⟨goal, implementation, primaryShape⟩ := selected.shape
        apply EvidenceEntryOriginates.root (root := evidence selected.primary) (by simp)
        · rw [primaryShape]
          simp only [evidence]
          exact .premise (List.mem_map.mpr ⟨item, member, rfl⟩) (.self _)
        · exact evidence_goal _
    · rw [selected.methods] at member
      exact .root (by simp [List.mem_map.mpr ⟨item, member, rfl⟩]) (.self _) (evidence_goal _)
  have eachValid : ∀ item ∈ dictionary,
      EvidenceValid [] program.signatures.resolutionRules (SourceCompilationPlan.runtimeEvidenceGoal item) (evidence item) := by
    intro item member
    rw [shape] at member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · obtain ⟨goal, _, resolved⟩ := resolved_each resolvedHeaders item member
        simpa only [resolved_goal resolved] using resolved_valid resolved
      · obtain ⟨goal, implementation, primaryShape⟩ := selected.shape
        have valid := selected.primaryValid
        rw [primaryShape] at valid
        simp only [evidence, SourceCompilationPlan.runtimeEvidenceGoal] at valid
        cases valid with
        | implementation _ _ _ children =>
          simpa only [evidence_goal] using valid_each children (evidence item) (List.mem_map.mpr ⟨item, member, rfl⟩)
    · rw [selected.methods] at member
      exact raw_valid_each selected.methodsValid item member
  exact ⟨goals ▸ assembled_each roots, dictionary_valid eachValid, by simpa only [environment, List.map_map, Function.comp_def] using goals⟩

theorem Certificate.origins {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available dictionary : Dictionary} {step : CoercionStep}
    {method : ExecutableImplMethods.CheckedMethod}
    (selected : CallableCoercionMethodCertificates.Certificate program caller node available step method)
    (covered : CallerCovered caller method)
    (callerAccepted : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary) :
    EvidenceEnvironment.AssembledFrom (environment available)
        (evidence selected.primary :: selected.methodEvidence.map evidence) method.specialized.assumptions (environment dictionary) ∧
      (environment dictionary).Valid program.signatures.resolutionRules ∧
      (environment dictionary).map Prod.fst = method.specialized.assumptions :=
  roots_origins selected.roots covered callerAccepted (materialized accepted)

theorem Certificate.covers {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available dictionary : Dictionary} {step : CoercionStep}
    {method : ExecutableImplMethods.CheckedMethod} {context : SourceSemantics.Context}
    (selected : CallableCoercionMethodCertificates.Certificate program caller node available step method)
    (covered : CallerCovered caller method)
    (callerAccepted : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary)
    (signatures : context.signatures = program.signatures) (assumptions : context.assumptions = method.specialized.assumptions) :
    (environment dictionary).Covers context := by
  obtain ⟨_, valid, goals⟩ := Certificate.origins selected covered callerAccepted accepted
  refine ⟨by simpa only [signatures] using valid, ?_⟩
  intro goal member
  exact EvidenceEnvironment.LooksUp.exists_of_key_mem (by simpa only [goals, assumptions] using member)

end Solcore.SourceSemantics.CoreLowering.CallableCoercionEvidenceOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceSelection
/-! Successful coercion preparation selects an independent source method and
the actual ordered dictionary. Caller-covered headers use the same resolver32;
uncovered origins, cross-fuel coherence and dictionary uniqueness are not
asserted. Runtime body execution and installed closure history remain separate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceSelection
open Frontend SourceInference TypeSystem Solcore.SourceSemantics.Dynamic
open CallableNamedMetadata (evidence environment)
open CallableEvidenceEnvironment
open CallableCoercionMethodInstantiation (Selection Formation bodyInstance)

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

/-- The exact runtime selector's returned tree is also the singleton result of
the real materializer. Both actions keep the same first-match raw row. -/
theorem requirement_materialized {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {id : RequirementId} {goal : ProgramPredicate} {raw : TypedTraitResolution.Evidence}
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available id goal = .ok raw) :
    SourceCompilationPlan.materializeCallEvidence caller node.id available [id] [goal] = .ok [raw] := by
  simp only [SourceCompilationPlan.exactRuntimeRequirementEvidence, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  obtain ⟨row, selected, accepted⟩ := bind_ok accepted
  rcases row with ⟨rowId, predicate, retained⟩
  split at accepted <;> try contradiction
  rename_i predicateEq
  have matchedPredicate : predicate = goal := by simpa using predicateEq
  split at accepted <;> try contradiction
  rename_i retainedEq
  have matchedRetained : retained.goal = goal := by simpa using retainedEq
  cases retained with
  | implementation stored =>
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    cases accepted
    simp [SourceCompilationPlan.materializeCallEvidence, selected, matchedPredicate, matchedRetained, bind, Except.bind, pure, Except.pure]
  | assumption assumed =>
    dsimp only at accepted
    split at accepted <;> try contradiction
    rename_i stored found
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    cases accepted
    simp [SourceCompilationPlan.materializeCallEvidence, selected, matchedPredicate, matchedRetained, bind, Except.bind, pure, Except.pure]
    change (match available.find? (fun item => decide (SourceCompilationPlan.runtimeEvidenceGoal item = assumed)) with
      | some item => Except.ok [item]
      | none => Except.error (SourceTypedRuntime.RuntimeError.missingRuntimeAssumptionEvidence caller.key node.id id assumed)) = .ok [raw]
    change available.find? (fun item => decide (SourceCompilationPlan.runtimeEvidenceGoal item = assumed)) = some raw at found
    rw [found]

/-- Reached-row validity comes from the authenticated returned tree; unrelated
ledger entries are not required to be valid here. -/
theorem requirement_produces {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {id : RequirementId} {goal : ProgramPredicate} {raw : TypedTraitResolution.Evidence} {context : Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available id goal = .ok raw)
    (valid : EvidenceValid [] program.signatures.resolutionRules goal (evidence raw)) :
    RequirementProducesEvidence context (environment available) id goal (evidence raw) := by
  have keys : ∀ goal, goal ∈ (environment available).map Prod.fst → goal ∈ context.assumptions := by
    intro goal member
    exact assumptions goal ((resolved_valid resolved).2 ▸ member)
  have produced := CallableAuthenticatedCallEvidence.produces_of_authenticated ledger keys
    (by simpa only [signatures] using (resolved_valid resolved).1)
    (requirement_materialized accepted) (Forall₂.cons (by simpa only [signatures] using valid) Forall₂.nil)
  cases produced with
  | cons head tail => exact head

theorem requirements_produce {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available returned : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {ids : List RequirementId} {goals : List ProgramPredicate} {context : Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidenceList program caller node available ids goals = .ok returned)
    (valid : Forall₂ (fun goal raw => EvidenceValid [] program.signatures.resolutionRules goal (evidence raw)) goals returned) :
    RequirementsProduceEnvironment context (environment available) ids goals (environment returned) := by
  induction ids generalizing goals returned with
  | nil => cases goals <;> cases accepted; exact .nil
  | cons id rest ih =>
    cases goals with
    | nil => cases accepted
    | cons goal goals =>
      unfold SourceCompilationPlan.exactRuntimeRequirementEvidenceList at accepted
      obtain ⟨raw, headAccepted, accepted⟩ := bind_ok accepted
      obtain ⟨tail, tailAccepted, accepted⟩ := bind_ok accepted
      cases accepted
      cases valid with
      | cons head tailValid =>
        have goalEq := SourceCompilationPlan.exactRuntimeRequirementEvidence_success_goal _ _ _ _ _ _ _ headAccepted
        simpa only [environment, List.map_cons, goalEq] using
          (RequirementsProduceEnvironment.cons (requirement_produces signatures ledger assumptions resolved headAccepted head)
            (ih tailAccepted tailValid))

private theorem trait_lookup {program : CheckedProgram} {primary : TypedTraitResolution.Evidence}
    {name : String} {method : ExecutableImplMethods.CheckedMethod}
    (selected : Selection program primary name method) :
    program.signatures.trait? method.traitMethod.id.trait = some selected.trait := by
  rw [← selected.association]
  exact selected.traitLookup

/-- The outer coercion guard fixes the selected trait's name, not just its
arity or numeric identity. The inner and outer singleton selectors agree. -/
theorem trait_name {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method)
    {primary : TypedTraitResolution.Evidence} (selected : Selection program primary "coerce" method) :
    selected.trait.name = "Coerce" := by
  simp only [SourceCompilationPlan.checkedCoercionMethod, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  obtain ⟨row, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, accepted⟩ := require_ok accepted
  split at accepted <;> try contradiction
  rename_i traitId goalTrait
  split at accepted <;> try contradiction
  rename_i trait found
  obtain ⟨traitGuard, accepted⟩ := require_ok accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  obtain ⟨raw, rawAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨methods, _, accepted⟩ := bind_ok accepted
  obtain ⟨actual⟩ := CallableCoercionMethodInstantiation.selection (mapError_ok accepted)
  have goalEq : actual.goal = row.predicate := by
    have matched := SourceCompilationPlan.exactRuntimeRequirementEvidence_success_goal _ _ _ _ _ _ _ rawAccepted
    rw [actual.primaryShape] at matched
    exact matched
  have traitIdEq : actual.trait.id = traitId := by
    have eq := actual.goalTrait
    rw [goalEq, goalTrait] at eq
    exact (ProgramTraitId.declaration.inj eq).symm
  have actualLookup := actual.traitLookup
  have owner : actual.declaration.traitMethod.trait = actual.trait.id := by
    unfold ProgramSignatures.trait? at actualLookup
    have eq := List.find?_some (p := fun trait : ProgramTraitSignature =>
      decide (trait.id = actual.declaration.traitMethod.trait)) actualLookup
    exact (of_decide_eq_true eq).symm
  rw [owner, traitIdEq] at actualLookup
  have same := Option.some.inj (actualLookup.symm.trans found)
  have selectedSame := Option.some.inj ((trait_lookup selected).symm.trans (trait_lookup actual))
  rw [selectedSame, same]
  have guards : trait.name = "Coerce" ∧ trait.parameters.length = 2 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using traitGuard
  exact guards.1


/-- The shared method source receipt retains the actual primary and every
ordered method requirement, independently of the expression that uses it. -/
structure MethodCertificate (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : SourceTypedRuntime.RuntimeEvidenceEnvironment)
    (primaryId : RequirementId) (methodIds : List RequirementId) (arity : Nat)
    (traitName methodName : String) (method : ExecutableImplMethods.CheckedMethod) where
  roots : CallableCoercionMethodCertificates.Roots program caller node available primaryId methodIds arity methodName method
  selected : Selection program roots.primary methodName method
  traitName : selected.trait.name = traitName

/-- Static source selection keeps the full implementation, declaration, trait,
head match and checked body. It contains no source execution or closure law. -/
structure Certificate (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : SourceTypedRuntime.RuntimeEvidenceEnvironment)
    (step : CoercionStep) (method : ExecutableImplMethods.CheckedMethod) where
  roots : CallableCoercionMethodCertificates.Certificate program caller node available step method
  selected : Selection program roots.primary "coerce" method
  traitName : selected.trait.name = "Coerce"

theorem of_accepted {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method) :
    Nonempty (Certificate program caller node available step method) := by
  obtain ⟨roots⟩ := CallableCoercionMethodCertificates.of_accepted accepted
  obtain ⟨selected⟩ := CallableCoercionMethodInstantiation.selection roots.checked
  exact ⟨⟨roots, selected, trait_name accepted selected⟩⟩

def Certificate.toMethodCertificate {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
    (receipt : Certificate program caller node available step method) :
    MethodCertificate program caller node available step.requirement step.methodRequirements 2 "Coerce" "coerce" method :=
  ⟨receipt.roots.roots, receipt.selected, receipt.traitName⟩

/-- Actual selector, same-fuel retained body and returned dictionary determine
an independent source selection. Range formation and caller coverage remain
explicit; neither is inferred from a ground specialization key. -/
theorem MethodCertificate.selects {program : CheckedProgram}
    (loadedAccepted : CallableMethodBodyCoherence.Checked program)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {primaryId : RequirementId} {methodIds : List RequirementId} {arity : Nat}
    {traitName methodName : String} {method : ExecutableImplMethods.CheckedMethod} {context : Context}
    (receipt : MethodCertificate program caller node available primaryId methodIds arity traitName methodName method)
    (formed : Formation receipt.selected.implementation receipt.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) method.specialized.parameterSubstitution)
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller method)
    (materialized : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller node ⟨primaryId, method⟩ = .ok dictionary) :
    OperatorMethodSelected (Program.ofChecked program) context (environment available) traitName methodName
      (primaryId :: methodIds) (bodyInstance program method) (environment dictionary) := by
  obtain ⟨definition, definitionMember, definitionId, instantiated⟩ :=
    receipt.selected.instantiates loadedAccepted formed.parameters range
  have determined := receipt.selected.determines formed
  have headTrait : receipt.selected.goal.trait = receipt.selected.implementation.head.trait := by
    exact (congrArg (fun goal : ProgramPredicate => goal.trait) determined.2.2).symm
  have produced := requirement_produces signatures ledger assumptions resolved
    receipt.roots.primarySelected receipt.roots.primaryValid
  have sourceSelected : EvidenceSelectsMethod (Program.ofChecked program)
      (evidence receipt.roots.primary) methodName definition := by
    simpa only [receipt.selected.primaryShape, evidence] using
      (EvidenceSelectsMethod.source (premises := method.implementationPremises.map evidence)
        receipt.selected.implementationMember headTrait receipt.selected.methodMember
        receipt.selected.declarationName definitionMember definitionId)
  have primaryGoal : SourceCompilationPlan.runtimeEvidenceGoal receipt.roots.primary = receipt.selected.goal := by
    exact congrArg SourceCompilationPlan.runtimeEvidenceGoal receipt.selected.primaryShape
  rw [primaryGoal] at produced
  have methodsProduced := requirements_produce signatures ledger assumptions resolved
    receipt.roots.methodsSelected receipt.roots.methodsValid
  have methodsGoals : receipt.roots.methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal =
      receipt.selected.declaration.wherePredicates.map
        (ProgramPredicate.applyParameters method.specialized.parameterSubstitution) := by
    rw [← receipt.roots.methods, receipt.selected.methodsGoals, receipt.selected.method_predicates formed]
  rw [methodsGoals] at methodsProduced
  have assembled := (CallableCoercionEvidenceOrigins.roots_origins receipt.roots covered resolved
    (CallableCoercionEvidenceOrigins.materialized_operator materialized)).1
  have methodAssumptions : method.specialized.assumptions =
      (SourceSemantics.methodAssumptions receipt.selected.trait receipt.selected.implementation receipt.selected.declaration).map
        (ProgramPredicate.applyParameters method.specialized.parameterSubstitution) :=
    (CallableCoercionBodyProvenance.specialization_fields receipt.selected.specialized).2
  rw [methodAssumptions] at assembled
  have traitOwner : receipt.selected.declaration.traitMethod.trait = receipt.selected.trait.id := by
    have found := receipt.selected.traitLookup
    unfold ProgramSignatures.trait? at found
    exact (of_decide_eq_true (List.find?_some
      (p := fun trait : ProgramTraitSignature => decide (trait.id = receipt.selected.declaration.traitMethod.trait)) found)).symm
  refine .intro (.intro produced sourceSelected) ?_ receipt.selected.implementationMember
    receipt.selected.traitMember receipt.traitName receipt.selected.goalTrait determined
    receipt.selected.methodMember receipt.selected.declarationName traitOwner methodsProduced instantiated ?_ ?_
  · exact ⟨method.implementationPremises.map evidence, by
      simpa only [evidence] using congrArg evidence receipt.selected.primaryShape⟩
  · simpa only [environment, List.map_map, Function.comp_def] using assembled
  · obtain ⟨_, valid, goals⟩ := CallableCoercionEvidenceOrigins.roots_origins receipt.roots covered resolved
      (CallableCoercionEvidenceOrigins.materialized_operator materialized)
    refine ⟨valid, ?_⟩
    intro goal member
    exact EvidenceEnvironment.LooksUp.exists_of_key_mem (goals.symm ▸ member)

theorem Certificate.selects {program : CheckedProgram}
    (loadedAccepted : CallableMethodBodyCoherence.Checked program)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod} {context : Context}
    (receipt : Certificate program caller node available step method)
    (formed : Formation receipt.selected.implementation receipt.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) method.specialized.parameterSubstitution)
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller method)
    (materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary) :
    OperatorMethodSelected (Program.ofChecked program) context (environment available) "Coerce" "coerce"
      (step.requirement :: step.methodRequirements) (bodyInstance program method) (environment dictionary) :=
  receipt.toMethodCertificate.selects loadedAccepted formed range signatures ledger assumptions resolved covered materialized

/-- Public preparation fixes the emitted complete carrier, and the actual
spine step fixes the same source selection and dictionary. This is a static
connection; it does not assert invocation of an installed method closure. -/
theorem prepared_step {program : CheckedProgram}
    (loadedAccepted : CallableMethodBodyCoherence.Checked program)
    {before : SourceSpecializationWorklist.Plan} {fuel budget : Nat}
    {project : CallableCoercionSpine.Projector} {compilation : CallableCoercionSpine.Context}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok compilation.plan)
    {caller : SourceSpecialization.SpecializedFunction} (member : caller ∈ compilation.plan.specializations)
    {node : ExpressionNode} (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    {coercion : CoercionStep} (site : coercion ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node)
    {available : CallableCoercionSpine.RuntimeEvidence}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    {scope : CallableCoercionSpine.Scope} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : CallableCoercionSpine.Lowered} {call : CallableCoercionSpine.Call}
    (step : CallableCoercionSpine.Step program project compilation caller available scope node policy input coercion output call)
    {context : Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (formed : ∀ receipt : Certificate program caller node available coercion step.method,
      Formation receipt.selected.implementation receipt.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) step.method.specialized.parameterSubstitution)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller step.method) :
    step.specialized = step.method.specialized ∧
      OperatorMethodSelected (Program.ofChecked program) context (environment available) "Coerce" "coerce"
        (coercion.requirement :: coercion.methodRequirements) (bodyInstance program step.method) (environment step.dictionary) := by
  obtain ⟨receipt⟩ := of_accepted step.selectedMethod
  exact ⟨CallableCoercionPreparation.step_specialized prepared member nodeMember site resolved step,
    receipt.selects loadedAccepted (formed receipt) range signatures ledger assumptions resolved covered step.materialized⟩

end Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceSelection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectionIdentity
/-! Source selection fixes its complete body when the actual reached requirement
and checked catalog fix identities. Ordered dictionaries need not be equal.
These are structural facts, not a runtime body or closure-history assumption. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectionIdentity
open Frontend SourceInference TypeSystem

theorem at_occurrence {a b : TypeSystem.ParameterSubstitution} {parameter : TypeParameterId}
    {type : TypeSystem.Ty} (occurs : TypeSystem.TypeParameterOccurs parameter type)
    (same : a.apply type = b.apply type) :
    (a.lookup? parameter).getD (.parameter parameter) = (b.lookup? parameter).getD (.parameter parameter) := by
  induction type with
  | «variable» _ | constructor _ | error => cases occurs
  | parameter found => cases occurs; exact same
  | application left right leftIH rightIH
  | function left right leftIH rightIH
  | product left right leftIH rightIH
  | mapping left right leftIH rightIH =>
    simp only [TypeSystem.ParameterSubstitution.apply, Ty.application.injEq, Ty.function.injEq,
      Ty.product.injEq, Ty.mapping.injEq] at same
    rcases occurs with occurs | occurs
    · exact leftIH occurs same.1
    · exact rightIH occurs same.2
  | proxy inner ih | comptime inner ih =>
    simp only [TypeSystem.ParameterSubstitution.apply, Ty.proxy.injEq, Ty.comptime.injEq] at same
    exact ih occurs same

theorem predicate_occurrence {a b : TypeSystem.ParameterSubstitution} {parameter : TypeParameterId}
    {predicate : ProgramPredicate} (occurs : TypeParameterOccursInPredicate parameter predicate)
    (same : ProgramPredicate.applyParameters a predicate = ProgramPredicate.applyParameters b predicate) :
    (a.lookup? parameter).getD (.parameter parameter) = (b.lookup? parameter).getD (.parameter parameter) := by
  rcases occurs with subject | ⟨argument, member, occurs⟩
  · exact at_occurrence subject (congrArg (fun p : ProgramPredicate => p.subject) same)
  · have arguments := congrArg (fun p : ProgramPredicate => p.arguments) same
    change predicate.arguments.map a.apply = predicate.arguments.map b.apply at arguments
    exact at_occurrence occurs ((List.map_inj_left.mp arguments) argument member)

theorem ordered_eq {a b : TypeSystem.ParameterSubstitution}
    (domain : a.map Prod.fst = b.map Prod.fst) (unique : (a.map Prod.fst).Nodup)
    (agrees : ∀ parameter ∈ a.map Prod.fst,
      (a.lookup? parameter).getD (.parameter parameter) = (b.lookup? parameter).getD (.parameter parameter)) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons head rest ih =>
    rcases head with ⟨parameter, value⟩
    cases b with
    | nil => simp at domain
    | cons other tail =>
      rcases other with ⟨other, replacement⟩
      simp only [List.map_cons, List.cons.injEq] at domain
      rcases domain with ⟨rfl, domain⟩
      have values := agrees parameter (by simp)
      simp only [TypeSystem.ParameterSubstitution.lookup?, if_true, Option.getD_some] at values
      subst replacement
      congr 1
      apply ih domain (List.nodup_cons.mp unique).2
      intro key member
      have ne : parameter ≠ key := by
        intro same
        subst key
        exact (List.nodup_cons.mp unique).1 member
      have same := agrees key (by simp [member])
      simpa only [TypeSystem.ParameterSubstitution.lookup?, ne, if_false] using same

theorem determines_functional {implementation : ProgramImplementationSignature} {goal : ProgramPredicate}
    {a b : TypeSystem.ParameterSubstitution}
    (occurs : ∀ parameter ∈ implementation.parameters, TypeParameterOccursInPredicate parameter implementation.head)
    (left : Dynamic.ImplementationHeadDetermines implementation goal a)
    (right : Dynamic.ImplementationHeadDetermines implementation goal b) : a = b := by
  apply ordered_eq (left.1.trans right.1.symm)
  · rw [left.1]; exact left.2.1.parameters_nodup
  · intro parameter member
    apply predicate_occurrence (occurs parameter (left.1 ▸ member))
    exact left.2.2.trans right.2.2.symm


/-- Only the catalog facts used by selection identity are retained. -/
structure Catalog (program : Program) : Prop where
  implementations : (program.signatures.implementations.map (·.id)).Nodup
  traits : (program.signatures.traits.map (·.id)).Nodup
  methods : (program.methods.map (·.id)).Nodup
  methodNames : ∀ implementation ∈ program.signatures.implementations,
    (implementation.methods.map (·.name)).Nodup
  parametersOccur : ∀ implementation ∈ program.signatures.implementations,
    ∀ parameter ∈ implementation.parameters, TypeParameterOccursInPredicate parameter implementation.head

/-- Public checker success supplies these facts without assuming body typing. -/
theorem Catalog.of_checked {raw : Workspace.RawWorkspace} {fuel : Nat} {checked : CheckedProgram}
    (accepted : checkProgram raw fuel = .ok checked) : Catalog (Program.ofChecked checked) := by
  obtain ⟨loaded, loadedAccepted, checkedAccepted⟩ := checkProgram_success_load accepted
  have ids := loadProgram_success_declarations_nodup loadedAccepted
  have signatures := checkLoadedProgram_success_signatures checkedAccepted
  refine ⟨buildProgramSignatures_success_implementation_ids_nodup ids signatures,
    buildProgramSignatures_success_trait_ids_nodup ids signatures, ?_, ?_, ?_⟩
  · simp only [Program.ofChecked, List.map_map, MethodDefinition.ofChecked, Function.comp_def]
    change (checked.methods.map (·.id)).Nodup
    rw [(checkLoadedProgram_success_ids checkedAccepted).2]
    exact buildProgramSignatures_success_implementation_method_ids_nodup ids signatures
  · intro implementation member
    exact (checkLoadedProgram_success_implementation_signature_structure checkedAccepted member).method_names_nodup
  · intro implementation member
    exact ImplementationSignatureHeadValidated.semantic_parameters_in_head
      (checkLoadedProgram_success_implementation_head_validated checkedAccepted member)

private theorem same_member {α β : Type} {rows : List α} {left right : α} {key : α → β}
    (unique : (rows.map key).Nodup) (leftMember : left ∈ rows) (rightMember : right ∈ rows)
    (same : key left = key right) : left = right := by
  induction rows generalizing left right with
  | nil => cases leftMember
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    simp only [List.mem_cons] at leftMember rightMember
    rcases leftMember with rfl | leftMember
    · rcases rightMember with rfl | rightMember
      · rfl
      · exact False.elim (unique.1 (List.mem_map.mpr ⟨_, rightMember, same.symm⟩))
    · rcases rightMember with rfl | rightMember
      · exact False.elim (unique.1 (List.mem_map.mpr ⟨_, leftMember, same⟩))
      · exact ih unique.2 leftMember rightMember same

/-- Local singleton selection suffices; unrelated ledger rows need not be unique. -/
theorem requirement_functional {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {id : RequirementId} {p q : ProgramPredicate} {a b : TraitEvidence}
    (unique : ∀ first second, ContainsRequirement context id first → ContainsRequirement context id second → first = second)
    (left : Dynamic.RequirementProducesEvidence context caller id p a)
    (right : Dynamic.RequirementProducesEvidence context caller id q b) : p = q ∧ a = b := by
  cases left with
  | intro first predFirst repFirst _ closeFirst _ =>
    cases right with
    | intro second predSecond repSecond _ closeSecond _ =>
      cases unique _ _ first second
      cases repFirst.functional repSecond
      exact ⟨predFirst.symm.trans predSecond, CallableEvidenceEnvironment.closes_functional closeFirst closeSecond⟩

/-- The actual materializer fixes exactly the reached primary ledger row. -/
theorem primary_unique {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceCompilationPlan.EvidenceEnvironment}
    {id : RequirementId} {goal : ProgramPredicate} {raw : TypedTraitResolution.Evidence} {context : SourceSemantics.Context}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available id goal = .ok raw) :
    ∀ first second, ContainsRequirement context id first → ContainsRequirement context id second → first = second := by
  obtain ⟨row, _, _, selected, _, _, _, _, _⟩ := CallableCallEvidence.cons_accepted
    (CallableCoercionSourceSelection.requirement_materialized accepted)
  intro first second firstMember secondMember
  exact (selected.unique ledger firstMember).trans (selected.unique ledger secondMember).symm

/-- Full source-body identity follows from the actual primary and catalog.
The resulting callee dictionaries are deliberately not compared. -/
theorem body_eq {program : Program} (catalog : Catalog program)
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {primary : RequirementId} {rest : List RequirementId}
    {leftBody rightBody : Dynamic.BodyInstance} {leftDictionary rightDictionary : Dynamic.EvidenceEnvironment}
    (unique : ∀ first second, ContainsRequirement context primary first → ContainsRequirement context primary second → first = second)
    (left : Dynamic.OperatorMethodSelected program context caller traitName methodName (primary :: rest) leftBody leftDictionary)
    (right : Dynamic.OperatorMethodSelected program context caller traitName methodName (primary :: rest) rightBody rightDictionary) :
    leftBody = rightBody := by
  cases left with
  | @intro _ _ goal closed implementation method trait definition substitution _ methodEvidence _
      selects shape implementationMember traitMember traitName goalTrait determined methodMember methodName methodOwner
      requirements instantiated assembled covers =>
    cases right with
    | @intro _ _ otherGoal otherClosed otherImplementation otherMethod otherTrait otherDefinition otherSubstitution _ otherMethodEvidence _
        otherSelects otherShape otherImplementationMember otherTraitMember otherTraitName otherGoalTrait otherDetermined
        otherMethodMember otherMethodName otherMethodOwner otherRequirements otherInstantiated otherAssembled otherCovers =>
      have sameRequirement : goal = otherGoal ∧ closed = otherClosed := by
        cases selects with
        | intro produced _ =>
          cases otherSelects with
          | intro otherProduced _ => exact requirement_functional unique produced otherProduced
      obtain ⟨premises, closedShape⟩ := shape
      obtain ⟨otherPremises, otherClosedShape⟩ := otherShape
      have sameClosed := closedShape.symm.trans (sameRequirement.2.trans otherClosedShape)
      have implementationId : implementation.id = otherImplementation.id := by
        injection sameClosed with _ implementationId _
        injection implementationId
      have sameImplementation := same_member catalog.implementations implementationMember otherImplementationMember implementationId
      subst otherImplementation
      have traitId : trait.id = otherTrait.id := by
        have same := goalTrait.symm.trans ((congrArg (fun goal : ProgramPredicate => goal.trait) sameRequirement.1).trans otherGoalTrait)
        injection same
      have sameTrait := same_member catalog.traits traitMember otherTraitMember traitId
      subst otherTrait
      have sameMethod := same_member (catalog.methodNames _ implementationMember) methodMember otherMethodMember (methodName.trans otherMethodName.symm)
      subst otherMethod
      have sameSubstitution := determines_functional (catalog.parametersOccur _ implementationMember) determined
        (sameRequirement.1.symm ▸ otherDetermined)
      subst otherSubstitution
      cases instantiated with
      | intro _ _ _ _ definitionMember definitionId _ _ _ source result context =>
        cases otherInstantiated with
        | intro _ _ _ _ otherDefinitionMember otherDefinitionId _ _ _ otherSource otherResult otherContext =>
          have sameDefinition := same_member catalog.methods definitionMember otherDefinitionMember (definitionId.trans otherDefinitionId.symm)
          subst otherDefinition
          cases leftBody; cases rightBody
          simp_all

end Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectionIdentity
end
