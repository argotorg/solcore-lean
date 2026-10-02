import Solcore.SourceSemantics.CoreLowering.CallableCoercionBodyProvenance
import Solcore.SourceSemantics.ProgramCheckingSoundness

/-! The method checker's actual head match and declaration-order specialization
are connected to independent source method instantiation. Type formation stays
an independent static obligation. No body execution or closure history is stored. -/
set_option autoImplicit false
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
theorem instantiates {loaded : LoadedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
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
