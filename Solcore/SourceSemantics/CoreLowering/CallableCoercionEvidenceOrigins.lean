import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodCertificates

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
theorem materialized {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
    {dictionary : Dictionary}
    (accepted : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary) :
    ∃ headers, Resolved program method.traitPredicates headers ∧
      dictionary = headers ++ method.implementationPremises ++ method.methodPremises ∧
      dictionary.map SourceCompilationPlan.runtimeEvidenceGoal = method.specialized.assumptions := by
  cases method with
  | mk id traitMethod predicates implementationPredicates implementationPremises methodPredicates methodPremises synthetic checked specialized =>
    induction predicates generalizing specialized dictionary with
    | nil =>
      unfold SourceCompilationPlan.coercionMethodRuntimeEvidence at accepted
      obtain ⟨headers, headersAccepted, accepted⟩ := bind_ok accepted
      have empty : headers = [] := Except.ok.inj headersAccepted |>.symm
      subst headers
      obtain ⟨_, validated, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨[], .nil, rfl, SourceCompilationPlan.validateRuntimeEvidence_success_matches _ _ _ validated⟩
    | cons goal rest ih =>
      unfold SourceCompilationPlan.coercionMethodRuntimeEvidence at accepted
      obtain ⟨headers, headersAccepted, accepted⟩ := bind_ok accepted
      change (match (TypedTraitResolution.resolve program.signatures.resolutionRules 32 goal).outcome with
        | .noSolution => Except.error (SourceTypedRuntime.RuntimeError.callEvidenceResolutionNoSolution caller.key node.id step.requirement goal)
        | .inconclusive reason => Except.error (SourceTypedRuntime.RuntimeError.callEvidenceResolutionInconclusive caller.key node.id step.requirement reason)
        | .success raw => do
          let .byImpl actual _ _ := raw
          if actual != goal then throw (SourceTypedRuntime.RuntimeError.callRequirementEvidenceGoalMismatch caller.key node.id step.requirement goal actual)
          pure (raw :: (← _))) = .ok headers at headersAccepted
      split at headersAccepted <;> try contradiction
      split at headersAccepted <;> try contradiction
      rename_i actual implementation premises resolution
      split at headersAccepted <;> try contradiction
      obtain ⟨tail, tailAccepted, headersEq⟩ := bind_ok headersAccepted
      cases headersEq
      let tailDictionary := tail ++ implementationPremises ++ methodPremises
      let tailSpecialized := { specialized with assumptions := tailDictionary.map SourceCompilationPlan.runtimeEvidenceGoal }
      have tailRun : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step
          ⟨id, traitMethod, rest, implementationPredicates, implementationPremises, methodPredicates, methodPremises,
            synthetic, checked, tailSpecialized⟩ = .ok tailDictionary := by
        simp only [SourceCompilationPlan.coercionMethodRuntimeEvidence]
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
      (environment dictionary).map Prod.fst = method.specialized.assumptions := by
  obtain ⟨headers, resolvedHeaders, shape, goals⟩ := materialized accepted
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
