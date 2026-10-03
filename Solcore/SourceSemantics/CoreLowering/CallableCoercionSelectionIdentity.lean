import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceSelection
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
