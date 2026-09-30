import Solcore.Frontend.SourceCompilationPlan.Types
import Solcore.Frontend.WordLiteral

/-!
Evaluator-independent preparation of closed specialization plans.

The worklist fixes source reachability. This module checks occurrence metadata,
authenticates evidence, and closes selected operator/coercion method frontiers
before execution. It does not import or construct runtime values or heaps, and
it does not evaluate source expressions or statements.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCompilationPlan

open SourceInference TypeSystem SourceTypedRuntime

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev EvidenceEnvironment := SourceTypedRuntime.RuntimeEvidenceEnvironment
abbrev Error := SourceTypedRuntime.RuntimeError

private def resultType? (function : CheckedFunction) : Option Ty :=
  match function.type with
  | .function _ result => some result
  | _ => none

def exactSpecialization (plan : Plan) (key : Key) :
    Except RuntimeError SourceSpecialization.SpecializedFunction :=
  match plan.specializations.filter fun specialized =>
      decide (specialized.key = key) with
  | [] => .error (.missingSpecialization key)
  | [specialized] => .ok specialized
  | candidates => .error (.duplicateSpecialization key candidates.length)

private def exactParameterBinding? (substitution : ParameterSubstitution)
    (parameter : TypeParameterId) : Option Ty :=
  match substitution.filter fun entry => entry.1 == parameter with
  | [entry] => some entry.2
  | _ => none

private def parameterSubstitutionsEquivalent
    (left right : ParameterSubstitution) : Bool :=
  left.length == right.length &&
    left.all (fun entry =>
      exactParameterBinding? right entry.1 == some entry.2) &&
    right.all fun entry =>
      exactParameterBinding? left entry.1 == some entry.2

private def specializationOwnershipCoherent
    (specialized : SourceSpecialization.SpecializedFunction) : Bool :=
  decide (specialized.key.declaration = specialized.declaration ∧
    specialized.function.declaration = specialized.declaration ∧
    specialized.function.typedBody.owner = specialized.declaration)

private def specializationMatchesInstantiation
    (specialized : SourceSpecialization.SpecializedFunction)
    (instantiation : DeclarationInstantiation) : Bool :=
  specializationOwnershipCoherent specialized &&
    specialized.key.arguments ==
      specialized.parameterSubstitution.map Prod.snd &&
    specialized.declaration == instantiation.declaration &&
    parameterSubstitutionsEquivalent specialized.parameterSubstitution
      instantiation.parameterSubstitution &&
    specialized.function.type == instantiation.type &&
    specialized.assumptions == instantiation.predicates &&
    specialized.function.typedBody.inputs.map (·.comptime) ==
      instantiation.parameterComptime &&
    specialized.function.returnComptime == instantiation.returnComptime

def exactInstantiationKey (plan : Plan)
    (instantiation : DeclarationInstantiation) : Except RuntimeError Key :=
  match plan.specializations.filter fun specialized =>
      specializationMatchesInstantiation specialized instantiation with
  | [] => .error (.missingInstantiationTarget instantiation.declaration
      instantiation.type)
  | [specialized] => .ok specialized.key
  | candidates => .error (.duplicateInstantiationTargets
      instantiation.declaration instantiation.type candidates.length)

private def predicateIsClosed (predicate : ProgramPredicate) : Bool :=
  predicate.subject.freeVariables.isEmpty &&
    predicate.arguments.all fun argument => argument.freeVariables.isEmpty

/-- Contextual local polymorphism deliberately retains open call metadata in
the caller and records one closed edge per reachable context.  Closed calls,
on the other hand, must still identify one exact canonical target. -/
private def instantiationIsClosed
    (instantiation : DeclarationInstantiation) : Bool :=
  instantiation.type.freeVariables.isEmpty &&
    (instantiation.parameterSubstitution.all fun entry =>
      entry.2.freeVariables.isEmpty) &&
    instantiation.predicates.all predicateIsClosed

def exactCallKey (plan : Plan) (caller : Key) (id : ExpressionId)
    (callee : Key) :
    Except RuntimeError Key :=
  match plan.callEdges.filter fun edge =>
      decide (edge.caller = caller) && decide (edge.occurrence = id) &&
        decide (edge.callee = callee) with
  | [] => .error (.missingCallEdge caller id)
  | [edge] => .ok edge.callee
  | edges => .error (.duplicateCallEdge caller id edges.length)

def exactReferenceKey (plan : Plan) (caller : Key)
    (id : ExpressionId) (callee : Key) : Except RuntimeError Key :=
  match plan.referenceEdges.filter fun edge =>
      decide (edge.caller = caller) && decide (edge.occurrence = id) &&
        decide (edge.callee = callee) with
  | [] => .error (.missingReferenceEdge caller id)
  | [edge] => .ok edge.callee
  | edges => .error (.duplicateReferenceEdge caller id edges.length)

def exactExpression (source : TypedSource) (id : ExpressionId) :
    Except RuntimeError ExpressionNode :=
  match source.lookupExpression? id with
  | some node => .ok node
  | none => .error (.missingExpression id)

def exactStatement (source : TypedSource) (id : StatementId) :
    Except RuntimeError StatementNode :=
  match source.lookupStatement? id with
  | some node => .ok node
  | none => .error (.missingStatement id)

def validateDirectDeclarationCallee (source : TypedSource)
    (call callee : ExpressionId)
    (instantiation : DeclarationInstantiation) : Except RuntimeError Unit :=
  match source.lookupExpression? callee with
  | some { type, form := .reference _ (.declaration reference), .. } =>
      if reference = instantiation && type = instantiation.type then
        pure ()
      else
        throw (.declarationMetadataMismatch call callee)
  | _ => throw (.declarationMetadataMismatch call callee)

private def exactSolvedRequirement? (function : CheckedFunction)
    (id : RequirementId) : Option SolvedRequirement :=
  match function.solvedRequirements.filter fun solved => solved.id == id with
  | [solved] => some solved
  | _ => none

private def firstDuplicateRequirement :
    List RequirementId → Option RequirementId
  | [] => none
  | requirement :: rest =>
      if rest.contains requirement then some requirement
      else firstDuplicateRequirement rest

private def coercionRequirementIds (steps : List CoercionStep) :
    List RequirementId :=
  steps.flatMap (fun step => step.requirements)

private def deduplicateRequirementLists
    (candidates : List (List RequirementId)) : List (List RequirementId) :=
  candidates.foldl (fun unique candidate =>
    if unique.contains candidate then unique else unique ++ [candidate]) []

/-- A direct call may carry a result path selected during overload resolution
before its signature predicates and a contextual result path after them.  The
IR deliberately concatenates both paths, so recover the unique middle ledger
by considering every path split and checking the stored order exactly. -/
private def directCallRequirementCandidates (node : ExpressionNode)
    (predicateCount : Nat) : List (List RequirementId) :=
  deduplicateRequirementLists <| (List.range (node.coercions.length + 1)).filterMap
    fun split =>
      let before := coercionRequirementIds (node.coercions.take split)
      let after := coercionRequirementIds (node.coercions.drop split)
      let middleAndAfter := node.requirements.drop before.length
      let middle := middleAndAfter.take predicateCount
      if node.requirements.take before.length = before &&
          middle.length = predicateCount &&
          middleAndAfter.drop predicateCount = after then
        some middle
      else
        none

private def requirementPredicatesMatch (function : CheckedFunction)
    (requirements : List RequirementId)
    (predicates : List ProgramPredicate) : Bool :=
  requirements.length == predicates.length &&
    (List.zip requirements predicates).all fun pair =>
      match exactSolvedRequirement? function pair.1 with
      | some solved => solved.predicate == pair.2 && solved.evidence.goal == pair.2
      | none => false

private def exactDirectCallRequirementIds
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) :
    Except RuntimeError (List RequirementId) := do
  if node.coercions.isEmpty &&
      node.requirements.length != instantiation.predicates.length then
    throw (.callRequirementCountMismatch caller.key node.id
      instantiation.predicates.length node.requirements.length)
  match firstDuplicateRequirement node.requirements with
  | some requirement =>
      throw (.duplicateCallRequirement caller.key node.id requirement)
  | none => pure ()
  let structuralCandidates := directCallRequirementCandidates node
    instantiation.predicates.length
  let candidates := structuralCandidates.filter fun requirements =>
    requirementPredicatesMatch caller.function requirements
      instantiation.predicates
  match structuralCandidates with
  | [requirements] => return requirements
  | _ => pure ()
  match candidates with
  | [requirements] => pure requirements
  | _ => throw (.invalidDirectCallRequirementLayout caller.key node.id
      node.requirements)

def ordinaryOwnedRequirements? (node : ExpressionNode) :
    Option (List RequirementId) :=
  let coercions := coercionRequirementIds node.coercions
  if node.requirements.length < coercions.length then
    none
  else
    let owned := node.requirements.take
      (node.requirements.length - coercions.length)
    if node.requirements = owned ++ coercions then some owned else none

/-- Recover the predicate-owned portion of a standalone declaration
reference.  Result-coercion requirements remain outside this ledger, exactly
as they do for other ordinary expressions. -/
private def exactDeclarationReferenceRequirementIds
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) :
    Except RuntimeError (List RequirementId) := do
  let requirements ← match ordinaryOwnedRequirements? node with
    | some requirements => pure requirements
    | none => throw (.invalidDeclarationReferenceRequirementLayout caller.key
        node.id node.requirements)
  if requirements.length != instantiation.predicates.length then
    throw (.callRequirementCountMismatch caller.key node.id
      instantiation.predicates.length requirements.length)
  match firstDuplicateRequirement requirements with
  | some requirement =>
      throw (.duplicateCallRequirement caller.key node.id requirement)
  | none => pure ()
  unless requirementPredicatesMatch caller.function requirements
      instantiation.predicates do
    throw (.invalidDeclarationReferenceRequirementLayout caller.key node.id
      requirements)
  pure requirements

def directLambdaLetBinder? (source : TypedSource)
    (id : Resolved.LocalId) : Option TypedBinder :=
  source.nodes.findSome? fun
    | .statement { form := .letDecl binder (some initializer), .. } =>
        if binder.id != id || binder.scheme.quantified.isEmpty then
          none
        else if SourceSpecialization.isDirectLambdaInitializer source
            initializer then
          some binder
        else
          none
    | _ => none

private def exactCallSolvedRequirement
    (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId) (requirement : RequirementId) :
    Except RuntimeError SolvedRequirement :=
  let candidates := caller.function.solvedRequirements.filter fun solved =>
    decide (solved.id = requirement)
  match candidates with
  | [] => .error (.missingSolvedRequirement caller.key occurrence requirement)
  | [solved] => .ok solved
  | solved => .error (.duplicateSolvedRequirements caller.key occurrence
      requirement solved.length)

def runtimeEvidenceGoal :
    TypedTraitResolution.Evidence → ProgramPredicate
  | .byImpl goal _ _ => goal

private def availableRuntimeEvidence?
    (environment : RuntimeEvidenceEnvironment)
    (predicate : ProgramPredicate) : Option TypedTraitResolution.Evidence :=
  environment.find? fun evidence =>
    decide (runtimeEvidenceGoal evidence = predicate)

private theorem availableRuntimeEvidence?_some_goal
    (environment : RuntimeEvidenceEnvironment)
    (predicate : ProgramPredicate) (evidence : TypedTraitResolution.Evidence)
    (found : availableRuntimeEvidence? environment predicate = some evidence) :
    runtimeEvidenceGoal evidence = predicate := by
  have accepted := List.find?_some found
  exact of_decide_eq_true accepted

private structure LocalRequirementBinding where
  template : LocalSchemeRequirement
  actualRequirement : RequirementId
  predicate : ProgramPredicate
  actualSolved : SolvedRequirement

private def localRequirementBindings
    (caller : SourceSpecialization.SpecializedFunction)
    (binder : TypedBinder) (node : ExpressionNode) :
    Except RuntimeError (Substitution × List LocalRequirementBinding) := do
  let substitution ←
    match SourceSpecialization.matchClosedSchemeInstance? binder.scheme
        node.rawType with
    | some substitution => pure substitution
    | none => throw (.localSchemeInstanceMismatch caller.key node.id binder.id
        binder.scheme.body node.rawType)
  if binder.schemeRequirements.length != node.requirements.length then
    throw (.localSchemeRequirementCountMismatch caller.key node.id binder.id
      binder.schemeRequirements.length node.requirements.length)
  let templateIds := binder.schemeRequirements.map (·.templateRequirement)
  match firstDuplicateRequirement templateIds with
  | some requirement =>
      throw (.duplicateLocalSchemeTemplateRequirement caller.key node.id
        binder.id requirement)
  | none => pure ()
  match firstDuplicateRequirement node.requirements with
  | some requirement =>
      throw (.duplicateLocalSchemeActualRequirement caller.key node.id
        binder.id requirement)
  | none => pure ()
  let pairs := List.zip binder.schemeRequirements node.requirements
  let mut bindings := []
  for (template, actualRequirement) in pairs do
    let templateSolved ← exactCallSolvedRequirement caller node.id
      template.templateRequirement
    if templateSolved.predicate != template.predicate then
      throw (.callRequirementPredicateMismatch caller.key node.id
        template.templateRequirement template.predicate
        templateSolved.predicate)
    if templateSolved.evidence.goal != template.predicate then
      throw (.callRequirementEvidenceGoalMismatch caller.key node.id
        template.templateRequirement template.predicate
        templateSolved.evidence.goal)
    match templateSolved.evidence with
    | .assumption _ => pure ()
    | .implementation _ =>
        throw (.localSchemeTemplateExpectedAssumption caller.key node.id
          binder.id template.templateRequirement)
    let predicate :=
      (template.applySubstitution substitution).predicate
    if !(TypedTraitResolution.predicateVariables predicate).isEmpty then
      throw (.nonGroundLocalSchemePredicate caller.key node.id binder.id
        actualRequirement predicate)
    let actualSolved ← exactCallSolvedRequirement caller node.id
      actualRequirement
    if actualSolved.predicate != predicate then
      throw (.callRequirementPredicateMismatch caller.key node.id
        actualRequirement predicate actualSolved.predicate)
    if actualSolved.evidence.goal != predicate then
      throw (.callRequirementEvidenceGoalMismatch caller.key node.id
        actualRequirement predicate actualSolved.evidence.goal)
    bindings := bindings ++ [{
      template
      actualRequirement
      predicate
      actualSolved
    }]
  pure (substitution, bindings)

def localRequirementWitnesses
    (caller : SourceSpecialization.SpecializedFunction)
    (available : RuntimeEvidenceEnvironment)
    (binder : TypedBinder) (node : ExpressionNode) :
    Except RuntimeError (Substitution × List LocalRequirementWitness) := do
  let (substitution, bindings) ← localRequirementBindings caller binder node
  let mut witnesses := []
  for binding in bindings do
    let evidence ← match binding.actualSolved.evidence with
      | .implementation evidence => pure evidence
      | .assumption assumption =>
          match availableRuntimeEvidence? available assumption with
          | some evidence => pure evidence
          | none => throw (.missingRuntimeAssumptionEvidence caller.key node.id
              binding.actualRequirement assumption)
    witnesses := witnesses ++ [{
      templateRequirement := binding.template.templateRequirement
      actualRequirement := binding.actualRequirement
      predicate := binding.predicate
      evidence
    }]
  pure (substitution, witnesses)

private def validateRuntimeEvidenceGoals (key : Key) :
    Nat → List ProgramPredicate → RuntimeEvidenceEnvironment →
      Except RuntimeError Unit
  | _, [], [] => pure ()
  | index, expected :: expectedRest, evidence :: evidenceRest => do
      let actual := runtimeEvidenceGoal evidence
      if actual = expected then
        validateRuntimeEvidenceGoals key (index + 1) expectedRest evidenceRest
      else
        throw (.runtimeEvidenceGoalMismatch key index expected actual)
  | _, expected, evidence =>
      throw (.runtimeEvidenceCountMismatch key expected.length evidence.length)

/-- Check the closed dictionary at a specialization boundary.  Its carrier
already rules out assumption leaves; this additionally fixes source order and
multiplicity to the callee's specialized `where` predicates. -/
def validateRuntimeEvidence (key : Key)
    (predicates : List ProgramPredicate)
    (environment : RuntimeEvidenceEnvironment) : Except RuntimeError Unit := do
  if predicates.length = environment.length then
    validateRuntimeEvidenceGoals key 0 predicates environment
  else
    throw (.runtimeEvidenceCountMismatch key predicates.length
      environment.length)

private def validateRuntimeEvidenceSelection (signatures : ProgramSignatures)
    (key : Key) : Nat → List ProgramPredicate → RuntimeEvidenceEnvironment →
      Except RuntimeError Unit
  | _, [], [] => pure ()
  | index, predicate :: predicates, evidence :: evidenceRest =>
      match (TypedTraitResolution.resolve signatures.resolutionRules 32
          predicate).outcome with
      | .noSolution =>
          throw (.runtimeEvidenceResolutionNoSolution key predicate)
      | .inconclusive reason =>
          throw (.runtimeEvidenceResolutionInconclusive key reason)
      | .success selected =>
          if selected == evidence then
            validateRuntimeEvidenceSelection signatures key (index + 1)
              predicates evidenceRest
          else
            let .byImpl _ implementation _ := evidence
            throw (.runtimeEvidenceNotSelected key index predicate
              implementation)
  | _, predicates, evidence =>
      throw (.runtimeEvidenceCountMismatch key predicates.length evidence.length)

def validateAuthenticatedRuntimeEvidence
    (signatures : ProgramSignatures) (key : Key)
    (predicates : List ProgramPredicate)
    (environment : RuntimeEvidenceEnvironment) : Except RuntimeError Unit := do
  validateRuntimeEvidence key predicates environment
  validateRuntimeEvidenceSelection signatures key 0 predicates environment

private theorem validateRuntimeEvidenceGoals_success
    (key : Key) (index : Nat) (predicates : List ProgramPredicate)
    (environment : RuntimeEvidenceEnvironment)
    (success : validateRuntimeEvidenceGoals key index predicates environment =
      .ok ()) :
    environment.Matches predicates := by
  induction predicates generalizing index environment with
  | nil =>
      cases environment with
      | nil => rfl
      | cons evidence rest =>
          simp [validateRuntimeEvidenceGoals] at success
  | cons predicate predicates induction =>
      cases environment with
      | nil => simp [validateRuntimeEvidenceGoals] at success
      | cons evidence rest =>
          cases evidence with
          | byImpl goal implementation premises =>
              by_cases same : goal = predicate
              · have tailSuccess :
                    validateRuntimeEvidenceGoals key (index + 1) predicates
                      rest = .ok () := by
                  simpa [validateRuntimeEvidenceGoals, runtimeEvidenceGoal,
                    same] using success
                have tail := induction (index := index + 1)
                  (environment := rest) tailSuccess
                unfold RuntimeEvidenceEnvironment.Matches
                  RuntimeEvidenceEnvironment.goals at tail ⊢
                simp [same, tail]
              · simp [validateRuntimeEvidenceGoals, runtimeEvidenceGoal,
                  same] at success

/-- Successful executable validation exposes the ordered closed-dictionary
invariant used by the evaluator boundary. -/
theorem validateRuntimeEvidence_success_matches
    (key : Key) (predicates : List ProgramPredicate)
    (environment : RuntimeEvidenceEnvironment)
    (success : validateRuntimeEvidence key predicates environment = .ok ()) :
    environment.Matches predicates := by
  unfold validateRuntimeEvidence at success
  split at success
  · exact validateRuntimeEvidenceGoals_success key 0 predicates environment
      success
  · simp at success

/-- Authentication refines ordered dictionary validation; a successfully
authenticated environment therefore has exactly the callee's predicate
ledger, including order and multiplicity. -/
theorem validateAuthenticatedRuntimeEvidence_success_matches
    (signatures : ProgramSignatures) (key : Key)
    (predicates : List ProgramPredicate)
    (environment : RuntimeEvidenceEnvironment)
    (success : validateAuthenticatedRuntimeEvidence signatures key predicates
      environment = .ok ()) :
    environment.Matches predicates := by
  change Except.bind (validateRuntimeEvidence key predicates environment)
      (fun _ => validateRuntimeEvidenceSelection signatures key 0 predicates
        environment) = .ok () at success
  unfold Except.bind at success
  split at success
  · contradiction
  · rename_i value validated
    have validatedUnit :
        validateRuntimeEvidence key predicates environment = .ok () := by
      simpa only [Subsingleton.elim value ()] using validated
    exact validateRuntimeEvidence_success_matches key predicates environment
      validatedUnit

/-- Materialize call evidence in the callee declaration's predicate order.
Concrete implementation evidence is retained verbatim.  A caller assumption
is closed by the dictionary supplied when the caller specialization was
entered; no trait search occurs during execution. -/
def materializeCallEvidence
    (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId)
    (available : RuntimeEvidenceEnvironment) :
    List RequirementId → List ProgramPredicate →
      Except RuntimeError RuntimeEvidenceEnvironment
  | [], [] => pure []
  | requirement :: requirements, predicate :: predicates => do
      let solved ← exactCallSolvedRequirement caller occurrence requirement
      if decide (solved.predicate ≠ predicate) then
        throw (.callRequirementPredicateMismatch caller.key occurrence
          requirement predicate solved.predicate)
      let goal := solved.evidence.goal
      if decide (goal ≠ solved.predicate) then
        throw (.callRequirementEvidenceGoalMismatch caller.key occurrence
          requirement solved.predicate goal)
      let evidence ← match solved.evidence with
        | .implementation evidence => pure evidence
        | .assumption assumption =>
            match availableRuntimeEvidence? available assumption with
            | some evidence => pure evidence
            | none => throw (.missingRuntimeAssumptionEvidence caller.key
                occurrence requirement assumption)
      pure (evidence :: (← materializeCallEvidence caller occurrence available
        requirements predicates))
  | requirements, predicates =>
      throw (.callRequirementCountMismatch caller.key occurrence
        predicates.length requirements.length)

private theorem exceptBind_eq_ok
    {errorType valueType resultType : Type}
    {first : Except errorType valueType}
    {next : valueType → Except errorType resultType}
    {result : resultType}
    (success : Except.bind first next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error error => contradiction
  | ok value => exact ⟨value, rfl, success⟩

private theorem exceptMap_eq_ok
    {errorType valueType resultType : Type}
    {source : Except errorType valueType}
    {function : valueType → resultType}
    {result : resultType}
    (success : function <$> source = .ok result) :
    ∃ value, source = .ok value ∧ function value = result := by
  cases source with
  | error error => contradiction
  | ok value => exact ⟨value, rfl, by injection success⟩

/-- Successful call-dictionary materialization preserves the callee's
predicate order exactly, regardless of whether each requirement was already
concrete or was discharged from the caller dictionary. -/
theorem materializeCallEvidence_success_matches
    (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId)
    (available result : RuntimeEvidenceEnvironment)
    (requirements : List RequirementId)
    (predicates : List ProgramPredicate)
    (success : materializeCallEvidence caller occurrence available requirements
      predicates = .ok result) :
    result.Matches predicates := by
  induction requirements generalizing predicates result with
  | nil =>
      cases predicates with
      | nil =>
          simp [materializeCallEvidence] at success
          subst result
          rfl
      | cons predicate predicates =>
          simp [materializeCallEvidence] at success
  | cons requirement requirements inductionHypothesis =>
      cases predicates with
      | nil => simp [materializeCallEvidence] at success
      | cons predicate predicates =>
          simp only [materializeCallEvidence] at success
          obtain ⟨solved, solvedResult, success⟩ := exceptBind_eq_ok success
          rcases solved with ⟨solvedId, solvedPredicate, solvedEvidence⟩
          split at success
          · contradiction
          · rename_i predicateAccepted
            have predicateRejected :
                decide (solvedPredicate ≠ predicate) = false := by
              simpa using predicateAccepted
            have predicateMatches : solvedPredicate = predicate := by
              exact Decidable.of_not_not
                (of_decide_eq_false predicateRejected)
            split at success
            · contradiction
            · rename_i goalAccepted
              have goalRejected :
                  decide (solvedEvidence.goal ≠ solvedPredicate) = false := by
                simpa using goalAccepted
              have goalMatches : solvedEvidence.goal = solvedPredicate := by
                exact Decidable.of_not_not (of_decide_eq_false goalRejected)
              cases solvedEvidence with
              | implementation evidence =>
                  change (List.cons evidence <$>
                    materializeCallEvidence caller occurrence available
                      requirements predicates) = .ok result at success
                  obtain ⟨tail, tailResult, resultEq⟩ :=
                    exceptMap_eq_ok success
                  subst result
                  have tailMatches := inductionHypothesis
                    (predicates := predicates) (result := tail) tailResult
                  unfold RuntimeEvidenceEnvironment.Matches at tailMatches ⊢
                  change runtimeEvidenceGoal evidence ::
                    RuntimeEvidenceEnvironment.goals tail =
                      predicate :: predicates
                  have evidenceMatches :
                      runtimeEvidenceGoal evidence = solvedPredicate := by
                    cases evidence
                    exact goalMatches
                  rw [evidenceMatches, predicateMatches, tailMatches]
              | assumption assumption =>
                  change
                    (match availableRuntimeEvidence? available assumption with
                    | some evidence => List.cons evidence <$>
                        materializeCallEvidence caller occurrence available
                          requirements predicates
                    | none => .error
                        (.missingRuntimeAssumptionEvidence caller.key occurrence
                          requirement assumption)) = .ok result at success
                  cases selected : availableRuntimeEvidence? available
                      assumption with
                  | some evidence =>
                    rw [selected] at success
                    change (List.cons evidence <$>
                      materializeCallEvidence caller occurrence available
                        requirements predicates) = .ok result at success
                    obtain ⟨tail, tailResult, resultEq⟩ :=
                      exceptMap_eq_ok success
                    subst result
                    have tailMatches := inductionHypothesis
                      (predicates := predicates) (result := tail) tailResult
                    have evidenceGoal := availableRuntimeEvidence?_some_goal
                      available assumption evidence selected
                    have assumptionMatches : assumption = solvedPredicate :=
                      goalMatches
                    unfold RuntimeEvidenceEnvironment.Matches at tailMatches ⊢
                    change runtimeEvidenceGoal evidence ::
                      RuntimeEvidenceEnvironment.goals tail =
                        predicate :: predicates
                    rw [evidenceGoal, assumptionMatches, predicateMatches,
                      tailMatches]
                  | none =>
                    rw [selected] at success
                    contradiction

def exactDirectCallRuntimeEvidence
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : RuntimeEvidenceEnvironment)
    (instantiation : DeclarationInstantiation) :
    Except RuntimeError RuntimeEvidenceEnvironment := do
  let requirements ← exactDirectCallRequirementIds caller node instantiation
  materializeCallEvidence caller node.id available requirements
    instantiation.predicates

def exactDeclarationReferenceRuntimeEvidence
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : RuntimeEvidenceEnvironment)
    (instantiation : DeclarationInstantiation) :
    Except RuntimeError RuntimeEvidenceEnvironment := do
  let requirements ← exactDeclarationReferenceRequirementIds caller node
    instantiation
  materializeCallEvidence caller node.id available requirements
    instantiation.predicates

/-- Successful direct-call evidence recovery produces the exact ordered
dictionary expected by the instantiated callee signature. -/
theorem exactDirectCallRuntimeEvidence_success_matches
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available result : RuntimeEvidenceEnvironment)
    (instantiation : DeclarationInstantiation)
    (success : exactDirectCallRuntimeEvidence caller node available
      instantiation = .ok result) :
    result.Matches instantiation.predicates := by
  simp only [exactDirectCallRuntimeEvidence] at success
  obtain ⟨requirements, _, materialized⟩ := exceptBind_eq_ok success
  exact materializeCallEvidence_success_matches caller node.id available result
    requirements instantiation.predicates materialized

/-- Declaration values use the same ordered dictionary contract as immediate
direct calls. -/
theorem exactDeclarationReferenceRuntimeEvidence_success_matches
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available result : RuntimeEvidenceEnvironment)
    (instantiation : DeclarationInstantiation)
    (success : exactDeclarationReferenceRuntimeEvidence caller node available
      instantiation = .ok result) :
    result.Matches instantiation.predicates := by
  simp only [exactDeclarationReferenceRuntimeEvidence] at success
  obtain ⟨requirements, _, materialized⟩ := exceptBind_eq_ok success
  exact materializeCallEvidence_success_matches caller node.id available result
    requirements instantiation.predicates materialized

private def validateSelectedCallImplementationEvidence
    (signatures : ProgramSignatures)
    (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId) (requirement : RequirementId)
    (goal : ProgramPredicate) (evidence : TypedTraitResolution.Evidence) :
    Except RuntimeError Unit :=
  match (TypedTraitResolution.resolve signatures.resolutionRules 32 goal).outcome with
  | .noSolution =>
      .error (.callEvidenceResolutionNoSolution caller.key occurrence
        requirement goal)
  | .inconclusive reason =>
      .error (.callEvidenceResolutionInconclusive caller.key occurrence
        requirement reason)
  | .success selected =>
      if selected == evidence then
        .ok ()
      else
        let .byImpl _ implementation _ := evidence
        .error (.callEvidenceNotSelected caller.key occurrence requirement
          goal implementation)

/-- Recover one concrete requirement witness at runtime.  Assumption markers
are discharged from the caller's closed dictionary; concrete witnesses are
authenticated again against the authoritative whole-program resolver. -/
def exactRuntimeRequirementEvidence (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : RuntimeEvidenceEnvironment)
    (requirement : RequirementId) (expected : ProgramPredicate) :
    Except RuntimeError TypedTraitResolution.Evidence := do
  let solved ← exactCallSolvedRequirement caller node.id requirement
  if decide (solved.predicate ≠ expected) then
    throw (.callRequirementPredicateMismatch caller.key node.id requirement
      expected solved.predicate)
  if decide (solved.evidence.goal ≠ expected) then
    throw (.callRequirementEvidenceGoalMismatch caller.key node.id requirement
      expected solved.evidence.goal)
  let evidence ← match solved.evidence with
    | .implementation evidence => pure evidence
    | .assumption predicate =>
        match availableRuntimeEvidence? available predicate with
        | some evidence => pure evidence
        | none => throw (.missingRuntimeAssumptionEvidence caller.key node.id
            requirement predicate)
  validateSelectedCallImplementationEvidence program.signatures caller node.id
    requirement expected evidence
  pure evidence

/-- A recovered and authenticated coercion/operator requirement has the goal
requested by the checked method signature. -/
theorem exactRuntimeRequirementEvidence_success_goal
    (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : RuntimeEvidenceEnvironment)
    (requirement : RequirementId) (expected : ProgramPredicate)
    (result : TypedTraitResolution.Evidence)
    (success : exactRuntimeRequirementEvidence program caller node available
      requirement expected = .ok result) :
    runtimeEvidenceGoal result = expected := by
  simp only [exactRuntimeRequirementEvidence] at success
  obtain ⟨solved, solvedResult, success⟩ := exceptBind_eq_ok success
  rcases solved with ⟨solvedId, solvedPredicate, solvedEvidence⟩
  split at success
  · contradiction
  · rename_i predicateAccepted
    have predicateRejected :
        decide (solvedPredicate ≠ expected) = false := by
      simpa using predicateAccepted
    have predicateMatches : solvedPredicate = expected := by
      exact Decidable.of_not_not (of_decide_eq_false predicateRejected)
    split at success
    · contradiction
    · rename_i goalAccepted
      have goalRejected :
          decide (solvedEvidence.goal ≠ expected) = false := by
        simpa using goalAccepted
      have goalMatches : solvedEvidence.goal = expected := by
        exact Decidable.of_not_not (of_decide_eq_false goalRejected)
      cases solvedEvidence with
      | implementation evidence =>
          change Except.bind
            (validateSelectedCallImplementationEvidence program.signatures
              caller node.id requirement expected evidence)
            (fun _ => .ok evidence) = .ok result at success
          obtain ⟨_, _, resultEq⟩ := exceptBind_eq_ok success
          injection resultEq with resultMatches
          subst result
          cases evidence
          exact goalMatches
      | assumption assumption =>
          change
            (match availableRuntimeEvidence? available assumption with
            | some evidence => Except.bind
                (validateSelectedCallImplementationEvidence program.signatures
                  caller node.id requirement expected evidence)
                (fun _ => .ok evidence)
            | none => .error
                (.missingRuntimeAssumptionEvidence caller.key node.id
                  requirement assumption)) = .ok result at success
          cases selected : availableRuntimeEvidence? available assumption with
          | none =>
              rw [selected] at success
              contradiction
          | some evidence =>
              rw [selected] at success
              obtain ⟨_, _, resultEq⟩ := exceptBind_eq_ok success
              injection resultEq with resultMatches
              subst result
              exact (availableRuntimeEvidence?_some_goal available assumption
                evidence selected).trans goalMatches

def exactRuntimeRequirementEvidenceList (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : RuntimeEvidenceEnvironment) :
    List RequirementId → List ProgramPredicate →
      Except RuntimeError (List TypedTraitResolution.Evidence)
  | [], [] => pure []
  | requirement :: requirements, predicate :: predicates => do
      let evidence ← exactRuntimeRequirementEvidence program caller node
        available requirement predicate
      pure (evidence :: (← exactRuntimeRequirementEvidenceList program caller
        node available requirements predicates))
  | requirements, predicates =>
      throw (.coercionMethodRequirementCountMismatch caller.key node.id
        { index := 0 } predicates.length requirements.length)

/-- Successful method-requirement recovery preserves the method predicate
ledger exactly.  This is the evidence contract consumed by every selected
coercion and overloaded-operator call helper. -/
theorem exactRuntimeRequirementEvidenceList_success_matches
    (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available result : RuntimeEvidenceEnvironment)
    (requirements : List RequirementId)
    (predicates : List ProgramPredicate)
    (success : exactRuntimeRequirementEvidenceList program caller node
      available requirements predicates = .ok result) :
    result.Matches predicates := by
  induction requirements generalizing predicates result with
  | nil =>
      cases predicates with
      | nil =>
          simp [exactRuntimeRequirementEvidenceList] at success
          subst result
          rfl
      | cons predicate predicates =>
          simp [exactRuntimeRequirementEvidenceList] at success
  | cons requirement requirements inductionHypothesis =>
      cases predicates with
      | nil => simp [exactRuntimeRequirementEvidenceList] at success
      | cons predicate predicates =>
          simp only [exactRuntimeRequirementEvidenceList] at success
          obtain ⟨evidence, evidenceSuccess, success⟩ :=
            exceptBind_eq_ok success
          obtain ⟨tail, tailSuccess, resultEq⟩ := exceptMap_eq_ok success
          subst result
          have evidenceGoal := exactRuntimeRequirementEvidence_success_goal
            program caller node available requirement predicate evidence
              evidenceSuccess
          have tailMatches := inductionHypothesis
            (predicates := predicates) (result := tail) tailSuccess
          unfold RuntimeEvidenceEnvironment.Matches at tailMatches ⊢
          change runtimeEvidenceGoal evidence ::
            RuntimeEvidenceEnvironment.goals tail = predicate :: predicates
          rw [evidenceGoal, tailMatches]

private structure RuntimeOperatorProfile where
  traitName : String
  methodName : String

private def runtimeUnaryProfile? :
    Syntax.UnaryOp → Option RuntimeOperatorProfile
  | operator =>
      match SourceInference.Detail.unaryOperatorDispatch operator with
      | .traitMethod traitName methodName => some { traitName, methodName }
      | .function _ => none

private def runtimeBinaryProfile? :
    Syntax.BinaryOp → Option RuntimeOperatorProfile
  | operator =>
      match SourceInference.Detail.binaryOperatorDispatch operator with
      | .traitMethod traitName methodName => some { traitName, methodName }
      | .function _ => none

private def runtimeUnaryResultType (operator : Syntax.UnaryOp)
    (operandType : Ty) : Ty :=
  if operator == .logicalNot then .bool else operandType

private def runtimeBinaryResultType (operator : Syntax.BinaryOp)
    (operandType : Ty) : Ty :=
  if SourceInference.Detail.binaryResultIsBool operator then .bool
  else operandType

private def runtimeOperatorMethodPredicates
    (trait : ProgramTraitSignature)
    (goal : ProgramPredicate) (expectedName : String)
    (wrap : ExecutableImplMethods.Error → RuntimeError) :
    Except RuntimeError (List ProgramPredicate) := do
  let goalArity := goal.arguments.length + 1
  unless goalArity = 1 do
    throw (wrap (.evidenceGoalArityMismatch goal.trait 1 goalArity))
  unless trait.parameters.length = 1 do
    throw (wrap (.traitArityMismatch trait.id 1 trait.parameters.length))
  let method ← match trait.methods.filter fun method =>
      method.name == expectedName with
    | [] => throw (wrap (.missingTraitMethod trait.id expectedName))
    | [method] => pure method
    | methods => throw (wrap (.multipleTraitMethods trait.id methods.length))
  let substitution : ParameterSubstitution :=
    trait.parameters.zip [goal.subject]
  pure (method.wherePredicates.map
    (ProgramPredicate.applyParameters substitution))

structure CheckedRuntimeOperatorMethod where
  primaryRequirement : RequirementId
  method : ExecutableImplMethods.CheckedMethod

def checkedUnaryOperatorMethod (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : RuntimeEvidenceEnvironment)
    (operator : Syntax.UnaryOp) :
    Except RuntimeError CheckedRuntimeOperatorMethod := do
  let profile ← match runtimeUnaryProfile? operator with
    | some profile => pure profile
    | none => throw (.unsupportedRuntimeUnary caller.key node.id operator)
  let requirements ← match ordinaryOwnedRequirements? node with
    | some requirements => pure requirements
    | none => throw (.unsupportedRequirements node.requirements)
  let primaryRequirement ← match requirements with
    | requirement :: _ => pure requirement
    | [] => throw (.unaryRequirementCountMismatch caller.key node.id 1 0)
  match firstDuplicateRequirement requirements with
  | some requirement =>
      throw (.duplicateUnaryRequirement caller.key node.id requirement)
  | none => pure ()
  let solved ← exactCallSolvedRequirement caller node.id primaryRequirement
  let predicate := solved.predicate
  let primary ← exactRuntimeRequirementEvidence program caller node available
    primaryRequirement predicate
  let traitId ← match predicate.trait with
    | .declaration id => pure id
    | .builtin id => throw (.executableUnaryMethod caller.key node.id
        (.builtinTraitNotExecutable id))
  let trait ← match program.signatures.trait? traitId with
    | some trait => pure trait
    | none => throw (.executableUnaryMethod caller.key node.id
        (.missingTrait traitId))
  unless trait.name = profile.traitName do
    throw (.runtimeUnaryTraitNameMismatch caller.key node.id
      profile.traitName trait.name)
  let methodPredicates ← runtimeOperatorMethodPredicates trait
    predicate profile.methodName
    (RuntimeError.executableUnaryMethod caller.key node.id)
  let expectedCount := methodPredicates.length + 1
  unless requirements.length = expectedCount do
    throw (.unaryRequirementCountMismatch caller.key node.id expectedCount
      requirements.length)
  let methodEvidence ← exactRuntimeRequirementEvidenceList program caller node
    available (requirements.drop 1) methodPredicates
  let method ←
    (ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary
      methodEvidence 1 profile.methodName).mapError fun error =>
        .executableUnaryMethod caller.key node.id error
  let expectedInputs := [predicate.subject]
  let actualInputs := method.specialized.function.typedBody.inputs.map
    fun binder => binder.scheme.body
  unless actualInputs = expectedInputs do
    throw (.runtimeUnaryInputTypesMismatch caller.key node.id expectedInputs
      actualInputs)
  let operandId ← match node.form with
    | .unary _ operand => pure operand
    | _ => throw (.unsupportedRuntimeUnary caller.key node.id operator)
  let operand ← exactExpression caller.function.typedBody operandId
  unless operand.type = predicate.subject do
    throw (.runtimeUnaryInputTypesMismatch caller.key node.id expectedInputs
      [operand.type])
  let expectedResult := runtimeUnaryResultType operator predicate.subject
  unless method.specialized.function.inferredBodyType = expectedResult do
    throw (.runtimeUnaryResultTypeMismatch caller.key node.id expectedResult
      method.specialized.function.inferredBodyType)
  unless node.rawType = expectedResult do
    throw (.runtimeUnaryResultTypeMismatch caller.key node.id expectedResult
      node.rawType)
  pure { primaryRequirement, method }

def checkedBinaryOperatorMethod (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : RuntimeEvidenceEnvironment)
    (operator : Syntax.BinaryOp) :
    Except RuntimeError CheckedRuntimeOperatorMethod := do
  let profile ← match runtimeBinaryProfile? operator with
    | some profile => pure profile
    | none => throw (.unsupportedRuntimeBinary caller.key node.id operator)
  let requirements ← match ordinaryOwnedRequirements? node with
    | some requirements => pure requirements
    | none => throw (.unsupportedRequirements node.requirements)
  let primaryRequirement ← match requirements with
    | requirement :: _ => pure requirement
    | [] => throw (.binaryRequirementCountMismatch caller.key node.id 1 0)
  match firstDuplicateRequirement requirements with
  | some requirement =>
      throw (.duplicateBinaryRequirement caller.key node.id requirement)
  | none => pure ()
  let solved ← exactCallSolvedRequirement caller node.id primaryRequirement
  let predicate := solved.predicate
  let primary ← exactRuntimeRequirementEvidence program caller node available
    primaryRequirement predicate
  let traitId ← match predicate.trait with
    | .declaration id => pure id
    | .builtin id => throw (.executableBinaryMethod caller.key node.id
        (.builtinTraitNotExecutable id))
  let trait ← match program.signatures.trait? traitId with
    | some trait => pure trait
    | none => throw (.executableBinaryMethod caller.key node.id
        (.missingTrait traitId))
  unless trait.name = profile.traitName do
    throw (.runtimeBinaryTraitNameMismatch caller.key node.id
      profile.traitName trait.name)
  let methodPredicates ← runtimeOperatorMethodPredicates trait
    predicate profile.methodName
    (RuntimeError.executableBinaryMethod caller.key node.id)
  let expectedCount := methodPredicates.length + 1
  unless requirements.length = expectedCount do
    throw (.binaryRequirementCountMismatch caller.key node.id expectedCount
      requirements.length)
  let methodEvidence ← exactRuntimeRequirementEvidenceList program caller node
    available (requirements.drop 1) methodPredicates
  let method ←
    (ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary
      methodEvidence 1 profile.methodName).mapError fun error =>
        .executableBinaryMethod caller.key node.id error
  let expectedInputs := [predicate.subject, predicate.subject]
  let actualInputs := method.specialized.function.typedBody.inputs.map
    fun binder => binder.scheme.body
  unless actualInputs = expectedInputs do
    throw (.runtimeBinaryInputTypesMismatch caller.key node.id expectedInputs
      actualInputs)
  let (leftId, rightId) ← match node.form with
    | .binary left _ right => pure (left, right)
    | _ => throw (.unsupportedRuntimeBinary caller.key node.id operator)
  let left ← exactExpression caller.function.typedBody leftId
  let right ← exactExpression caller.function.typedBody rightId
  let operandTypes := [left.type, right.type]
  unless operandTypes = expectedInputs do
    throw (.runtimeBinaryInputTypesMismatch caller.key node.id expectedInputs
      operandTypes)
  let expectedResult := runtimeBinaryResultType operator predicate.subject
  unless method.specialized.function.inferredBodyType = expectedResult do
    throw (.runtimeBinaryResultTypeMismatch caller.key node.id expectedResult
      method.specialized.function.inferredBodyType)
  unless node.rawType = expectedResult do
    throw (.runtimeBinaryResultTypeMismatch caller.key node.id expectedResult
      node.rawType)
  pure { primaryRequirement, method }

/-- Authenticate one retained `Coerce<From, To>` edge and recover the exact
checked implementation method selected by its evidence. -/
def checkedCoercionMethod (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : RuntimeEvidenceEnvironment)
    (step : CoercionStep) :
    Except RuntimeError ExecutableImplMethods.CheckedMethod := do
  match firstDuplicateRequirement step.requirements with
  | some requirement =>
      throw (.duplicateCoercionRequirement caller.key node.id requirement)
  | none => pure ()
  let solved ← exactCallSolvedRequirement caller node.id step.requirement
  let predicate := solved.predicate
  unless predicate.subject = step.source && predicate.arguments = [step.target] do
    throw (.coercionPredicateMismatch caller.key node.id step.requirement
      step.source step.target predicate)
  let traitId ← match predicate.trait with
    | .declaration id => pure id
    | trait => throw (.coercionTraitMismatch caller.key node.id
        step.requirement trait)
  let trait ← match program.signatures.trait? traitId with
    | some trait => pure trait
    | none => throw (.coercionTraitMismatch caller.key node.id
        step.requirement predicate.trait)
  unless trait.name = "Coerce" && trait.parameters.length = 2 do
    throw (.coercionTraitMismatch caller.key node.id step.requirement
      predicate.trait)
  let traitMethod ← match trait.methods.filter fun method =>
      method.name == "coerce" with
    | [method] => pure method
    | [] => throw (.executableCoercionMethod caller.key node.id
        step.requirement (.missingTraitMethod trait.id "coerce"))
    | methods => throw (.executableCoercionMethod caller.key node.id
        step.requirement (.multipleTraitMethods trait.id methods.length))
  let substitution : ParameterSubstitution :=
    trait.parameters.zip [predicate.subject, step.target]
  let methodPredicates := traitMethod.wherePredicates.map
    (ProgramPredicate.applyParameters substitution)
  if step.methodRequirements.length != methodPredicates.length then
    throw (.coercionMethodRequirementCountMismatch caller.key node.id
      step.requirement methodPredicates.length step.methodRequirements.length)
  let primary ← exactRuntimeRequirementEvidence program caller node available
    step.requirement predicate
  let methodEvidence ← exactRuntimeRequirementEvidenceList program caller node
    available step.methodRequirements methodPredicates
  (ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary
    methodEvidence 2 "coerce").mapError fun error =>
      .executableCoercionMethod caller.key node.id step.requirement error

private def resolveClosedMethodEvidence (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (requirement : RequirementId) :
    List ProgramPredicate →
      Except RuntimeError (List TypedTraitResolution.Evidence)
  | [] => pure []
  | predicate :: predicates =>
      match (TypedTraitResolution.resolve program.signatures.resolutionRules 32
          predicate).outcome with
      | .noSolution =>
          throw (.callEvidenceResolutionNoSolution caller.key node.id
            requirement predicate)
      | .inconclusive reason =>
          throw (.callEvidenceResolutionInconclusive caller.key node.id
            requirement reason)
      | .success evidence => do
          let .byImpl goal _ _ := evidence
          if goal != predicate then
            throw (.callRequirementEvidenceGoalMismatch caller.key node.id
              requirement predicate goal)
          pure (evidence :: (← resolveClosedMethodEvidence program caller
            node requirement predicates))

/-- The synthetic checked method lists trait-header, implementation-head, and
method predicates in that order.  Reconstruct the same closed runtime
dictionary rather than depending on incidental evidence-list order. -/
def coercionMethodRuntimeEvidence (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (step : CoercionStep)
    (method : ExecutableImplMethods.CheckedMethod) :
    Except RuntimeError RuntimeEvidenceEnvironment := do
  let traitEvidence ← resolveClosedMethodEvidence program caller node
    step.requirement method.traitPredicates
  let environment := traitEvidence ++ method.implementationPremises ++
    method.methodPremises
  validateRuntimeEvidence method.specialized.key method.specialized.assumptions
    environment
  pure environment

def operatorMethodRuntimeEvidence (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (selection : CheckedRuntimeOperatorMethod) :
    Except RuntimeError RuntimeEvidenceEnvironment := do
  let method := selection.method
  let traitEvidence ← resolveClosedMethodEvidence program caller node
    selection.primaryRequirement method.traitPredicates
  let environment := traitEvidence ++ method.implementationPremises ++
    method.methodPremises
  validateRuntimeEvidence method.specialized.key method.specialized.assumptions
    environment
  pure environment

def resolveRuntimeEvidenceEnvironment (program : CheckedProgram)
    (key : Key) : List ProgramPredicate →
      Except RuntimeError RuntimeEvidenceEnvironment
  | [] => pure []
  | predicate :: predicates =>
      match (TypedTraitResolution.resolve program.signatures.resolutionRules 32
          predicate).outcome with
      | .noSolution =>
          throw (.runtimeEvidenceResolutionNoSolution key predicate)
      | .inconclusive reason =>
          throw (.runtimeEvidenceResolutionInconclusive key reason)
      | .success evidence => do
          let .byImpl goal _ _ := evidence
          if goal != predicate then
            throw (.runtimeEvidenceGoalMismatch key 0 predicate goal)
          pure (evidence :: (← resolveRuntimeEvidenceEnvironment program key
            predicates))

private def directLambdaBodyRoots? (source : TypedSource)
    (binderId : Resolved.LocalId) : Option (List NodeId) :=
  source.nodes.findSome? fun
    | .statement { form := .letDecl binder (some initializer), .. } =>
        if binder.id != binderId then
          none
        else
          match source.lookupExpression? initializer with
          | some { form := .lambda _ _ body, .. } =>
              some (body.map NodeId.statement)
          | _ => none
    | _ => none

private def directLambdaInitializer? (source : TypedSource)
    (binderId : Resolved.LocalId) : Option ExpressionId :=
  source.nodes.findSome? fun
    | .statement { form := .letDecl binder (some initializer), .. } =>
        if binder.id == binderId &&
            SourceSpecialization.isDirectLambdaInitializer source initializer then
          some initializer
        else
          none
    | _ => none

private def directLexicalChildren (source : TypedSource)
    (id : NodeId) : List NodeId :=
  match source.lookupNode? id.occurrenceId with
  | some (.expression { form := .lambda _ _ _, .. }) => []
  | some (.expression node) =>
      SourceSpecialization.expressionChildNodeIds node
  | some (.statement node) =>
      SourceSpecialization.statementChildNodeIds source node
  | none => []

private def directLexicalFuel (source : TypedSource)
    (roots : List NodeId) : Nat :=
  roots.length + source.nodes.foldl (fun count node =>
    count + match node with
      | .expression expression =>
          (SourceSpecialization.expressionChildNodeIds expression).length
      | .statement statement =>
          (SourceSpecialization.statementChildNodeIds source statement).length) 0 + 1

private def collectDirectLexicalNodes (source : TypedSource) :
    Nat → List NodeId → List NodeId → List NodeId
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, pending :: rest, seen =>
      if seen.contains pending then
        collectDirectLexicalNodes source fuel rest seen
      else
        let nextSeen := seen ++ [pending]
        let children := (directLexicalChildren source pending).filter fun child =>
          !nextSeen.contains child && !rest.contains child
        collectDirectLexicalNodes source fuel (rest ++ children) nextSeen

private def directLambdaBodyContains (source : TypedSource)
    (binder : TypedBinder) (occurrence : ExpressionId) : Bool :=
  match directLambdaBodyRoots? source binder.id with
  | none => false
  | some roots =>
      (collectDirectLexicalNodes source (directLexicalFuel source roots)
        roots []).contains (.expression occurrence)

private def expressionRequirementCount (source : TypedSource)
    (requirement : RequirementId) : Nat :=
  source.nodes.foldl (fun count node =>
    match node with
    | .expression expression =>
        count + (expression.requirements.filter fun candidate =>
          candidate == requirement).length
    | .statement _ => count) 0

private def scopedLocalTemplateOwner? (source : TypedSource)
    (occurrence : ExpressionId) (requirement : RequirementId)
    (predicate : ProgramPredicate) : Option TypedBinder :=
  if expressionRequirementCount source requirement != 1 then
    none
  else
    match source.nodes.filterMap fun
      | .statement { form := .letDecl binder (some initializer), .. } =>
          if binder.scheme.quantified.isEmpty ||
              !SourceSpecialization.isDirectLambdaInitializer source initializer ||
              !directLambdaBodyContains source binder occurrence ||
              !(binder.schemeRequirements.any fun owned =>
                owned.templateRequirement == requirement &&
                  owned.predicate == predicate) then
            none
          else
            some binder
      | _ => none with
    | [binder] => some binder
    | _ => none

private def validateExecutableCallRequirementEvidence
    (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId) :
    List RequirementId → List ProgramPredicate → Except RuntimeError Unit
  | [], [] => pure ()
  | requirement :: requirements, predicate :: predicates => do
      let solved ← exactCallSolvedRequirement caller occurrence requirement
      if solved.predicate != predicate then
        throw (.callRequirementPredicateMismatch caller.key occurrence
          requirement predicate solved.predicate)
      if solved.evidence.goal != predicate then
        throw (.callRequirementEvidenceGoalMismatch caller.key occurrence
          requirement predicate solved.evidence.goal)
      match solved.evidence with
      | .implementation _ => pure ()
      | .assumption assumption =>
          let declarationAssumption := caller.assumptions.contains predicate
          let localTemplate :=
            (scopedLocalTemplateOwner? caller.function.typedBody occurrence
              requirement predicate).isSome
          unless declarationAssumption || localTemplate do
            throw (.unsupportedCallAssumptionEvidence caller.key occurrence
              requirement assumption)
      validateExecutableCallRequirementEvidence caller occurrence requirements
        predicates
  | requirements, predicates =>
      throw (.callRequirementCountMismatch caller.key occurrence
        predicates.length requirements.length)

private def validateExecutableDirectCallRequirements
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) :
    Except RuntimeError Unit := do
  let requirements ← exactDirectCallRequirementIds caller node instantiation
  validateExecutableCallRequirementEvidence caller node.id requirements
    instantiation.predicates

private def validateExecutableCallImplementationEvidence
    (signatures : ProgramSignatures)
    (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId) :
    List RequirementId → List ProgramPredicate → Except RuntimeError Unit
  | [], [] => pure ()
  | requirement :: requirements, predicate :: predicates => do
      let solved ← exactCallSolvedRequirement caller occurrence requirement
      match solved.evidence with
      | .assumption _ => pure ()
      | .implementation evidence =>
          validateSelectedCallImplementationEvidence signatures caller
            occurrence requirement predicate evidence
      validateExecutableCallImplementationEvidence signatures caller occurrence
        requirements predicates
  | requirements, predicates =>
      throw (.callRequirementCountMismatch caller.key occurrence
        predicates.length requirements.length)

private def validateExecutableDirectCallImplementationEvidence
    (signatures : ProgramSignatures)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) :
    Except RuntimeError Unit := do
  validateExecutableDirectCallRequirements caller node instantiation
  let requirements ← exactDirectCallRequirementIds caller node instantiation
  validateExecutableCallImplementationEvidence signatures caller node.id
    requirements instantiation.predicates

private def validateExecutableDeclarationReferenceRequirements
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) :
    Except RuntimeError Unit := do
  let requirements ← exactDeclarationReferenceRequirementIds caller node
    instantiation
  validateExecutableCallRequirementEvidence caller node.id requirements
    instantiation.predicates

private def validateExecutableDeclarationReferenceImplementationEvidence
    (signatures : ProgramSignatures)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) :
    Except RuntimeError Unit := do
  validateExecutableDeclarationReferenceRequirements caller node instantiation
  let requirements ← exactDeclarationReferenceRequirementIds caller node
    instantiation
  validateExecutableCallImplementationEvidence signatures caller node.id
    requirements instantiation.predicates

private def nodeUseCount (source : TypedSource) (target : NodeId) : Nat :=
  let rootCount := (source.roots.filter fun root => root == target).length
  source.nodes.foldl (fun count node =>
    count + match node with
      | .expression expression =>
          (SourceSpecialization.expressionChildNodeIds expression |>.filter
            fun child => child == target).length
      | .statement statement =>
          (SourceSpecialization.statementChildNodeIds source statement |>.filter
            fun child => child == target).length) rootCount

private def directDeclarationCalleeUseCount (source : TypedSource)
    (target : ExpressionId) : Nat :=
  source.nodes.foldl (fun count node =>
    match node with
    | .expression { form := .call callee _ (.declaration _), .. } =>
        if callee == target then count + 1 else count
    | _ => count) 0

private def declarationUse?
    (node : ExpressionNode) :
    Option (List RequirementId × DeclarationInstantiation) :=
  match node.form with
  | .call _ _ (.declaration instantiation) =>
      some (node.requirements, instantiation)
  | .reference _ (.declaration instantiation) => do
      let requirements ← ordinaryOwnedRequirements? node
      some (requirements, instantiation)
  | _ => none

private def validateQualifiedLocalTemplateCoverage
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (binder : TypedBinder) : Except RuntimeError Unit := do
  let templateIds := binder.schemeRequirements.map (·.templateRequirement)
  match firstDuplicateRequirement templateIds with
  | some requirement =>
      throw (.duplicateLocalSchemeTemplateRequirement caller.key node.id
        binder.id requirement)
  | none => pure ()
  let source := caller.function.typedBody
  let initializer ← match directLambdaInitializer? source binder.id with
    | some initializer => pure initializer
    | none => throw (.unsupportedQualifiedLocalReference caller.key node.id
        binder.id)
  unless nodeUseCount source (.expression initializer) == 1 do
    throw (.unsupportedQualifiedLocalInitializer caller.key binder.id initializer)
  let templateUses := source.nodes.filterMap fun
    | .expression expression =>
        match declarationUse? expression with
        | some (requirements, instantiation) =>
            if requirements.any templateIds.contains then
              some (expression, requirements, instantiation)
            else
              none
        | none => none
    | _ => none
  for (declarationUse, requirements, instantiation) in templateUses do
    let expected := binder.schemeRequirements.filter fun template =>
      requirements.contains template.templateRequirement
    let actual := (List.zip requirements instantiation.predicates).filter
      fun pair => templateIds.contains pair.1
    unless actual.map Prod.fst == expected.map (·.templateRequirement) &&
        actual.map Prod.snd == expected.map (·.predicate) do
      match expected.head? with
      | some first =>
          throw (.unsupportedLocalSchemeTemplateUse caller.key binder.id
            first.templateRequirement)
      | none => throw (.unsupportedRequirements declarationUse.requirements)
  for template in binder.schemeRequirements do
    let uses := source.nodes.filterMap fun
      | .expression expression =>
          if expression.requirements.contains template.templateRequirement then
            some expression
          else
            none
      | .statement _ => none
    let (declarationUse, requirements, instantiation) ← match uses with
      | [declarationUse] =>
          match declarationUse? declarationUse with
          | some (requirements, instantiation) =>
              pure (declarationUse, requirements, instantiation)
          | none => throw (.unsupportedLocalSchemeTemplateUse caller.key
              binder.id template.templateRequirement)
      | _ => throw (.unsupportedLocalSchemeTemplateUse caller.key binder.id
          template.templateRequirement)
    unless directLambdaBodyContains source binder declarationUse.id do
      throw (.unsupportedLocalSchemeTemplateUse caller.key binder.id
        template.templateRequirement)
    unless requirements.length == instantiation.predicates.length &&
        (List.zip requirements instantiation.predicates).any (fun pair =>
          pair.1 == template.templateRequirement &&
            pair.2 == template.predicate) do
      throw (.unsupportedLocalSchemeTemplateUse caller.key binder.id
        template.templateRequirement)
    match declarationUse.form with
    | .call callee _ (.declaration _) =>
        unless directDeclarationCalleeUseCount source callee == 1 &&
            nodeUseCount source (.expression callee) == 1 do
          throw (.unsupportedConstrainedDeclarationReference caller.key
            declarationUse.id callee)
    | .reference _ (.declaration _) =>
        unless directDeclarationCalleeUseCount source declarationUse.id == 0 do
          throw (.unsupportedConstrainedDeclarationReference caller.key
            declarationUse.id declarationUse.id)
    | _ =>
        throw (.unsupportedLocalSchemeTemplateUse caller.key binder.id
          template.templateRequirement)

private def validateQualifiedLocalReferenceLayout
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (binder : TypedBinder) : Except RuntimeError Unit := do
  validateQualifiedLocalTemplateCoverage caller node binder
  discard <| localRequirementBindings caller binder node

private def validateQualifiedLocalReference
    (caller : SourceSpecialization.SpecializedFunction)
    (available : RuntimeEvidenceEnvironment)
    (node : ExpressionNode) (binder : TypedBinder) :
    Except RuntimeError (List LocalRequirementWitness) := do
  validateQualifiedLocalTemplateCoverage caller node binder
  let (_, witnesses) ← localRequirementWitnesses caller available binder node
  pure witnesses

private def validateQualifiedLocalReferenceEvidence
    (signatures : ProgramSignatures)
    (caller : SourceSpecialization.SpecializedFunction)
    (available : RuntimeEvidenceEnvironment)
    (node : ExpressionNode) (binder : TypedBinder) : Except RuntimeError Unit := do
  let witnesses ← validateQualifiedLocalReference caller available node binder
  for witness in witnesses do
    validateSelectedCallImplementationEvidence signatures caller node.id
      witness.actualRequirement witness.predicate witness.evidence

private def literalEvidenceIsBuiltin (function : CheckedFunction)
    (resolution : IntegerLiteralResolution) : Bool :=
  match exactSolvedRequirement? function resolution.requirement with
  | none => false
  | some solved =>
      let expected := ProgramSignatures.builtinIntPredicate resolution.targetType
      solved.predicate == expected &&
        match solved.evidence with
        | .assumption _ => false
        | .implementation (.byImpl goal implementation premises) =>
            goal == expected && premises.isEmpty &&
              match resolution.targetType with
              | .constructor (.builtin .word) =>
                  implementation == ProgramImplId.builtin .intWord
              | .constructor (.builtin .integer) =>
                  implementation == ProgramImplId.builtin .intInteger
              | _ => false

private def validateLiteralResolution (function : CheckedFunction)
    (source : Syntax.CoreLiteralValue)
    (resolution : IntegerLiteralResolution) : Except RuntimeError Unit := do
  unless numericLiteralValue? source = some resolution.rawValue &&
      literalEvidenceIsBuiltin function resolution do
    throw (.invalidLiteralEvidence resolution.requirement)

private def patternLiteralResolutions :
    List MatchPatternInstruction →
      List (Syntax.CoreLiteralValue × IntegerLiteralResolution)
  | [] => []
  | .integerLiteral source resolution :: rest =>
      (source, resolution) :: patternLiteralResolutions rest
  | _ :: rest => patternLiteralResolutions rest

private def patternLiterals (pattern : TypedMatchPattern) :
    List (Syntax.CoreLiteralValue × IntegerLiteralResolution) :=
  match pattern.resolution with
  | .integerLiteral source resolution => [(source, resolution)]
  | .constructor _ instructions
  | .tuple instructions => patternLiteralResolutions instructions
  | .wildcard | .binder _ => []

private def validatePatternMetadata (function : CheckedFunction)
    (pattern : TypedMatchPattern) : Except RuntimeError Unit := do
  let literals := patternLiterals pattern
  unless pattern.requirements = literals.map fun entry => entry.2.requirement do
    throw .invalidPatternMetadata
  for literal in literals do
    validateLiteralResolution function literal.1 literal.2

private def validateAssignmentMetadata
    (assignment : AssignmentResolution) : Except RuntimeError Unit :=
  unless assignment.requirements.isEmpty do
    throw (.unsupportedRequirements assignment.requirements)

private def validateForItemMetadata : ForItemForm → Except RuntimeError Unit
  | .assignValue assignment _ _
  | .assignBitNot assignment => validateAssignmentMetadata assignment
  | .letDecl _ _ | .expression _ => pure ()

/-- Reconstruct every indirect-call endpoint from the callee and argument
nodes.  The retained resolution metadata is useful to execution only after it
has been checked against those authoritative children. -/
private def validateIndirectCallMetadata (source : TypedSource)
    (node : ExpressionNode) (callee : ExpressionId)
    (arguments : List ExpressionId) (metadata : IndirectCallResolution) :
    Except RuntimeError Unit := do
  unless metadata.hasValidArgumentCoercionPath do
    throw (.invalidIndirectArgumentCoercionPath node.id)
  let calleeNode ← exactExpression source callee
  let (parameterType, resultType) ← match calleeNode.type with
    | .function parameter result => pure (parameter, result)
    | type => throw (.indirectCalleeNotFunction node.id type)
  let argumentTypes ← arguments.mapM fun argument => do
    let argumentNode ← exactExpression source argument
    pure argumentNode.type
  unless arguments.length = metadata.argumentCount do
    throw (.argumentArityMismatch metadata.argumentCount arguments.length)
  let bundledType := Ty.productMany argumentTypes
  unless metadata.argumentTypeBeforeCoercion = bundledType do
    throw (.indirectArgumentBundleMismatch node.id bundledType
      metadata.argumentTypeBeforeCoercion)
  unless metadata.argumentTypeAfterCoercion = parameterType do
    throw (.indirectParameterTypeMismatch node.id parameterType
      metadata.argumentTypeAfterCoercion)
  unless node.rawType = resultType do
    throw (.indirectResultTypeMismatch node.id resultType node.rawType)
  unless node.requirements =
      coercionRequirementIds metadata.argumentCoercions ++
        coercionRequirementIds node.coercions do
    throw (.unsupportedRequirements node.requirements)

private def validateUnaryOperatorRequirementLayout
    (specialized : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (operator : Syntax.UnaryOp) :
    Except RuntimeError Unit := do
  let requirements ← match ordinaryOwnedRequirements? node with
    | some requirements => pure requirements
    | none => throw (.unsupportedRequirements node.requirements)
  if requirements.isEmpty then do
    let operandId ← match node.form with
      | .unary _ operand => pure operand
      | _ => throw (.unsupportedRuntimeUnary specialized.key node.id operator)
    let operand ← exactExpression specialized.function.typedBody operandId
    let expectedInput := match operator with
      | .logicalNot => Ty.bool
      | .bitNot =>
          if operand.type = Ty.integer then Ty.integer else Ty.word
    let expectedResult := runtimeUnaryResultType operator expectedInput
    unless operand.type = expectedInput do
      throw (.runtimeUnaryInputTypesMismatch specialized.key node.id
        [expectedInput] [operand.type])
    unless node.rawType = expectedResult do
      throw (.runtimeUnaryResultTypeMismatch specialized.key node.id
        expectedResult node.rawType)
  else
    if (runtimeUnaryProfile? operator).isNone then
      throw (.unsupportedRuntimeUnary specialized.key node.id operator)
    match firstDuplicateRequirement requirements with
    | some requirement =>
        throw (.duplicateUnaryRequirement specialized.key node.id requirement)
    | none => pure ()
    for requirement in requirements do
      let solved ← exactCallSolvedRequirement specialized node.id requirement
      unless solved.evidence.goal = solved.predicate do
        throw (.callRequirementEvidenceGoalMismatch specialized.key node.id
          requirement solved.predicate solved.evidence.goal)

private def validateBinaryOperatorRequirementLayout
    (specialized : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (operator : Syntax.BinaryOp) :
    Except RuntimeError Unit := do
  let requirements ← match ordinaryOwnedRequirements? node with
    | some requirements => pure requirements
    | none => throw (.unsupportedRequirements node.requirements)
  if requirements.isEmpty then do
    let (leftId, rightId) ← match node.form with
      | .binary left _ right => pure (left, right)
      | _ => throw (.unsupportedRuntimeBinary specialized.key node.id operator)
    let left ← exactExpression specialized.function.typedBody leftId
    let right ← exactExpression specialized.function.typedBody rightId
    let builtinInput := SourceInference.Detail.binaryBuiltinType operator
    let expectedInput :=
      if builtinInput = Ty.word && left.type = Ty.integer &&
          right.type = Ty.integer then
        Ty.integer
      else
        builtinInput
    let expectedInputs := [expectedInput, expectedInput]
    let actualInputs := [left.type, right.type]
    unless actualInputs = expectedInputs do
      throw (.runtimeBinaryInputTypesMismatch specialized.key node.id
        expectedInputs actualInputs)
    let expectedResult := runtimeBinaryResultType operator expectedInput
    unless node.rawType = expectedResult do
      throw (.runtimeBinaryResultTypeMismatch specialized.key node.id
        expectedResult node.rawType)
  else
    if (runtimeBinaryProfile? operator).isNone then
      throw (.unsupportedRuntimeBinary specialized.key node.id operator)
    match firstDuplicateRequirement requirements with
    | some requirement =>
        throw (.duplicateBinaryRequirement specialized.key node.id requirement)
    | none => pure ()
    for requirement in requirements do
      let solved ← exactCallSolvedRequirement specialized node.id requirement
      unless solved.evidence.goal = solved.predicate do
        throw (.callRequirementEvidenceGoalMismatch specialized.key node.id
          requirement solved.predicate solved.evidence.goal)

private def validateExpressionMetadata
    (specialized : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) : Except RuntimeError Unit := do
  let function := specialized.function
  unless node.hasValidCoercionPath do
    throw (.invalidExpressionCoercionPath node.id node.rawType node.type)
  match node.form with
  | .integerLiteral source resolution =>
      unless node.requirements =
          [resolution.requirement] ++ coercionRequirementIds node.coercions do
        throw (.unsupportedRequirements node.requirements)
      validateLiteralResolution function source resolution
  | .call callee arguments (.indirect metadata) =>
      validateIndirectCallMetadata function.typedBody node callee arguments
        metadata
  | .call _ _ (.declaration instantiation) =>
      validateExecutableDirectCallRequirements specialized node instantiation
  | .reference _ (.declaration instantiation) =>
      let directUses := directDeclarationCalleeUseCount function.typedBody node.id
      if directUses != 0 then
        unless node.requirements.isEmpty do
          throw (.unsupportedConstrainedDeclarationReference specialized.key
            node.id node.id)
      else
        validateExecutableDeclarationReferenceRequirements specialized node
          instantiation
  | .reference _ (.local binderId) =>
      let owned ← match ordinaryOwnedRequirements? node with
        | some requirements => pure requirements
        | none => throw (.unsupportedRequirements node.requirements)
      let ownedNode := {
        node with
        type := node.rawType
        requirements := owned
        coercions := []
      }
      match directLambdaLetBinder? function.typedBody binderId with
      | some binder =>
          if binder.schemeRequirements.isEmpty then
            unless owned.isEmpty do
              throw (.unsupportedRequirements owned)
          else
            validateQualifiedLocalReferenceLayout specialized ownedNode binder
      | none =>
          unless owned.isEmpty do
            throw (.unsupportedRequirements owned)
  | .unary operator _ =>
      validateUnaryOperatorRequirementLayout specialized node operator
  | .binary _ operator _ =>
      validateBinaryOperatorRequirementLayout specialized node operator
  | _ =>
      match ordinaryOwnedRequirements? node with
      | some [] => pure ()
      | _ => throw (.unsupportedRequirements node.requirements)

private def validateStatementMetadata (function : CheckedFunction) :
    StatementForm → Except RuntimeError Unit
  | .assignValue assignment _ _
  | .assignBitNot assignment => validateAssignmentMetadata assignment
  | .matchWith resolution => do
      let expected := resolution.cases.flatMap fun arm =>
        arm.pattern.requirements
      unless resolution.requirements = expected do
        throw .invalidPatternMetadata
      for arm in resolution.cases do
        validatePatternMetadata function arm.pattern
  | .forLoop initializer _ post _ =>
      for item in initializer ++ post do
        validateForItemMetadata item
  | _ => pure ()

/-- The effectful runtime implements builtin operations directly, but does not
silently reinterpret user-selected trait methods or coercions as builtins. -/
private def validateExecutableMetadata
    (specialized : SourceSpecialization.SpecializedFunction) :
    Except RuntimeError Unit :=
  let function := specialized.function
  for node in function.typedBody.nodes do
    match node with
    | .expression expression =>
        validateExpressionMetadata specialized expression
    | .statement statement => validateStatementMetadata function statement.form

/-- Source types whose outermost value is available only during staged
evaluation.  This intentionally inspects the source annotation rather than
its erased runtime representation. -/
def sourceTypeIsComptimeOnly : Ty → Bool
  | .constructor (.builtin .integer)
  | .comptime _ => true
  | _ => false

private def requireComptimeArgumentStage
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (index : Nat) (argument : ExpressionId) :
    Except RuntimeError Unit :=
  match caller.stageAnalysis.expressionStage? argument with
  | none => throw (.missingExpressionStage caller.key node.id argument)
  | some .comptime => pure ()
  | some actual =>
      throw (.comptimeArgumentStageMismatch caller.key node.id index argument
        actual)

private def validateStagedArguments
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (forceComptime : Bool) :
    Nat → List TypedBinder → List ExpressionId → Except RuntimeError Unit
  | _, [], [] => pure ()
  | index, parameter :: parameters, argument :: arguments => do
      if forceComptime || parameter.comptime ||
          sourceTypeIsComptimeOnly parameter.scheme.body then
        requireComptimeArgumentStage caller node index argument
      validateStagedArguments caller node forceComptime (index + 1)
        parameters arguments
  | _, parameters, arguments =>
      throw (.argumentArityMismatch parameters.length arguments.length)

def validateStagedCallableContract
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (arguments : List ExpressionId)
    (parameters : List TypedBinder) (stagedResult : Bool)
    (calleeOwner : Key) :
    Except RuntimeError Unit := do
  let effectfulStaging := caller.function.returnComptime ||
    sourceTypeIsComptimeOnly caller.function.inferredBodyType
  unless effectfulStaging do
    validateStagedArguments caller node stagedResult
      0 parameters arguments
    if stagedResult then
      match caller.stageAnalysis.expressionStage? node.id with
      | none => throw (.missingExpressionStage caller.key node.id node.id)
      | some .comptime => pure ()
      | some actual =>
          throw (.comptimeResultStageMismatch caller.key node.id calleeOwner
            actual)

def validateStagedCallBoundary
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (arguments : List ExpressionId)
    (callee : SourceSpecialization.SpecializedFunction) :
    Except RuntimeError Unit :=
  validateStagedCallableContract caller node arguments
    callee.function.typedBody.inputs
    (callee.function.returnComptime ||
      sourceTypeIsComptimeOnly callee.function.inferredBodyType)
    callee.key

private def validateSpecializationStaging
    (specialized : SourceSpecialization.SpecializedFunction) :
    Except RuntimeError Unit := do
  let function := specialized.function
  let effectfulStaging := function.returnComptime ||
    sourceTypeIsComptimeOnly function.inferredBodyType
  unless effectfulStaging do
    for sourceNode in function.typedBody.nodes do
      match sourceNode with
      | .expression expression =>
          if sourceTypeIsComptimeOnly expression.type then
            match specialized.stageAnalysis.expressionStage? expression.id with
            | some .comptime => pure ()
            | _ => throw (.stagedExpressionType expression.id expression.type)
      | .statement _ => pure ()

def validateSpecializationMetadataWith
    (allowAssumptions : Bool)
    (specialized : SourceSpecialization.SpecializedFunction) :
    Except RuntimeError Unit := do
  unless specializationOwnershipCoherent specialized do
    throw (.specializationOwnershipMismatch specialized.key
      specialized.declaration specialized.function.declaration
      specialized.function.typedBody.owner)
  unless allowAssumptions || specialized.assumptions.isEmpty do
    throw (.unresolvedAssumptions specialized.key specialized.assumptions)
  validateSpecializationStaging specialized
  validateExecutableMetadata specialized
  let declaredResult ← match resultType? specialized.function with
    | some result => pure result
    | none => throw (.invalidFunctionType specialized.key
        specialized.function.type)
  unless declaredResult = specialized.function.inferredBodyType do
    throw (.inferredResultTypeMismatch specialized.key declaredResult
      specialized.function.inferredBodyType)

def validateSpecializationMetadata
    (specialized : SourceSpecialization.SpecializedFunction) :
    Except RuntimeError Unit :=
  validateSpecializationMetadataWith false specialized

/-- An assumed specialization is executable only when every public entry has
already discharged its dictionary.  Both direct calls and first-class
declaration references carry that closed evidence across the boundary; a seed
still has no enclosing provider and therefore must remain closed. -/
private def allowsEvidenceInvocation (plan : Plan) (key : Key) : Bool :=
  (plan.callEdges.any (fun edge => edge.callee == key) ||
    plan.referenceEdges.any fun edge => edge.callee == key) &&
    !plan.seedKeys.contains key

/-- Preflight the metadata of every reachable specialization. The canonical
worklist has already fixed the ordinary call graph; selected-method closure is
validated separately against the program signatures. -/
def validateExecutablePlan (plan : Plan) : Except RuntimeError Unit := do
  for specialized in plan.specializations do
    validateSpecializationMetadataWith
      (allowsEvidenceInvocation plan specialized.key) specialized

private def extendCoercionMethodPlan (program : CheckedProgram)
    (helperBudget : Nat) (plan : Plan)
    (specialized : SourceSpecialization.SpecializedFunction)
    (available : RuntimeEvidenceEnvironment) (node : ExpressionNode)
    (step : CoercionStep) : Except RuntimeError Plan := do
  let method ← checkedCoercionMethod program specialized node available step
  validateStagedCallBoundary specialized node [node.id] method.specialized
  discard <| coercionMethodRuntimeEvidence program specialized node step method
  let outerEdge : SourceSpecializationWorklist.CallEdge := {
    caller := specialized.key
    occurrence := node.id
    callee := method.specialized.key
  }
  let outcome ← match SourceSpecializationWorklist.extendCompletePlan program
      plan method.specialized outerEdge helperBudget with
    | .ok outcome => pure outcome
    | .error error => throw (.coercionMethodWorklist specialized.key node.id
        step.requirement error)
  match outcome with
  | .complete extended => pure extended
  | .budgetExhausted _ next pending =>
      throw (.coercionMethodSpecializationBudgetExhausted specialized.key
        node.id step.requirement next pending.length)

private def extendOperatorMethodPlan (program : CheckedProgram)
    (helperBudget : Nat) (plan : Plan)
    (specialized : SourceSpecialization.SpecializedFunction)
    (available : RuntimeEvidenceEnvironment) (node : ExpressionNode) :
    Except RuntimeError Plan := do
  let requirements ← match ordinaryOwnedRequirements? node with
    | some requirements => pure requirements
    | none => throw (.unsupportedRequirements node.requirements)
  if requirements.isEmpty then
    pure plan
  else
    let ownedNode := {
      node with
      type := node.rawType
      requirements
      coercions := []
    }
    let selection ← match ownedNode.form with
      | .unary operator _ =>
          checkedUnaryOperatorMethod program specialized ownedNode available
            operator
      | .binary _ operator _ =>
          checkedBinaryOperatorMethod program specialized ownedNode available
            operator
      | _ => throw (.unsupportedRequirements requirements)
    let arguments ← match ownedNode.form with
      | .unary _ operand => pure [operand]
      | .binary left _ right => pure [left, right]
      | _ => throw (.unsupportedRequirements requirements)
    validateStagedCallBoundary specialized ownedNode arguments
      selection.method.specialized
    discard <| operatorMethodRuntimeEvidence program specialized ownedNode
      selection
    let outerEdge : SourceSpecializationWorklist.CallEdge := {
      caller := specialized.key
      occurrence := node.id
      callee := selection.method.specialized.key
    }
    let outcome ← match SourceSpecializationWorklist.extendCompletePlan program
        plan selection.method.specialized outerEdge helperBudget with
      | .ok outcome => pure outcome
      | .error error => throw (.operatorMethodWorklist specialized.key node.id
          error)
    match outcome with
    | .complete extended => pure extended
    | .budgetExhausted _ next pending =>
        throw (.operatorMethodSpecializationBudgetExhausted specialized.key
          node.id next pending.length)

private def validateSpecializationEvidenceAndExtend
    (program : CheckedProgram) (helperBudget : Nat) (plan : Plan)
    (specialized : SourceSpecialization.SpecializedFunction) :
    Except RuntimeError Plan := do
  let available ← resolveRuntimeEvidenceEnvironment program specialized.key
    specialized.assumptions
  let mut extended := plan
  for sourceNode in specialized.function.typedBody.nodes do
    match sourceNode with
    | .expression node =>
        match node.form with
        | .unary _ _ | .binary _ _ _ =>
            extended ← extendOperatorMethodPlan program helperBudget extended
              specialized available node
        | _ => pure ()
        for step in node.coercions do
          extended ← extendCoercionMethodPlan program helperBudget extended
            specialized available node step
        match node.form with
        | .call _ _ (.indirect metadata) =>
            for step in metadata.argumentCoercions do
              extended ← extendCoercionMethodPlan program helperBudget extended
                specialized available node step
        | _ => pure ()
        match node.form with
        | .call _ arguments (.declaration instantiation) => do
            if instantiationIsClosed instantiation then
              let target ← exactInstantiationKey extended instantiation
              let calleeKey ← exactCallKey extended specialized.key node.id
                target
              let callee ← exactSpecialization extended calleeKey
              validateStagedCallBoundary specialized node arguments callee
            else
              let callEdges := extended.callEdges.filter fun edge =>
                decide (edge.caller = specialized.key) &&
                  decide (edge.occurrence = node.id) &&
                  decide
                    (edge.callee.declaration = instantiation.declaration)
              if callEdges.isEmpty then
                throw (.missingCallEdge specialized.key node.id)
              for edge in callEdges do
                let callee ← exactSpecialization extended edge.callee
                validateStagedCallBoundary specialized node arguments callee
            validateExecutableDirectCallImplementationEvidence
              program.signatures specialized node instantiation
        | .reference _ (.declaration instantiation) =>
            if directDeclarationCalleeUseCount
                specialized.function.typedBody node.id == 0 then
              validateExecutableDeclarationReferenceImplementationEvidence
                program.signatures specialized node instantiation
            else
              pure ()
        | .reference _ (.local binderId) =>
            match directLambdaLetBinder?
                specialized.function.typedBody binderId with
            | some binder =>
                unless binder.schemeRequirements.isEmpty do
                  validateQualifiedLocalReferenceEvidence program.signatures
                    specialized available node binder
            | none => pure ()
        | _ => pure ()
    | .statement _ => pure ()
  pure extended

private def prepareExecutablePlanEvidenceAux (program : CheckedProgram)
    (helperBudget : Nat) : Nat → Nat → Plan → Except RuntimeError Plan
  | 0, next, plan =>
      match plan.specializations[next]? with
      | none => pure plan
      | some _ => throw (.executablePlanClosureFuelExhausted next)
  | remaining + 1, next, plan =>
      match plan.specializations[next]? with
      | none => pure plan
      | some specialized => do
          /- Every assumption is resolved below before the prepared plan can
          escape.  In particular this admits a ground constrained seed, whose
          authenticated evidence is supplied by the safe root boundary. -/
          validateSpecializationMetadataWith true specialized
          let extended ← validateSpecializationEvidenceAndExtend program
            helperBudget plan specialized
          prepareExecutablePlanEvidenceAux program helperBudget remaining
            (next + 1) extended

/-- A caller-supplied plan is executable only if replaying its roots against
the checked program reconstructs *all* of its specialized bodies and edges.
In particular, ground built-in operator layouts cannot be forged by erasing
the trait requirements of a generic source occurrence.  Detached method
specializations are appended only after this input-plan check. -/
def validateCanonicalInputPlan (program : CheckedProgram) (plan : Plan) :
    Except RuntimeError Unit := do
  let seeds ← plan.seedKeys.mapM fun key => do
    let specialized ← exactSpecialization plan key
    pure ({
      declaration := specialized.declaration
      parameterSubstitution := specialized.parameterSubstitution
    } : SourceSpecializationWorklist.Request)
  let outcome ← (SourceSpecializationWorklist.run program seeds
    plan.specializations.length).mapError RuntimeError.inputPlanWorklist
  match outcome with
  | .budgetExhausted _ next _ =>
      throw (.inputPlanBudgetExhausted next)
  | .complete expected =>
      unless expected == plan do
        throw .nonCanonicalInputPlan

/-- Close and authenticate every executable operator and coercion method before
execution.  The outer budget bounds the number of specializations inspected,
including detached methods appended during the pass.  The helper budget
independently bounds ordinary call/reference closure discovered from each
detached method. -/
def prepareExecutablePlanEvidenceWithBudget (program : CheckedProgram)
    (plan : Plan) (closureFuel helperBudget : Nat) :
    Except RuntimeError Plan := do
  let prepared ← prepareExecutablePlanEvidenceAux program helperBudget
    closureFuel 0 plan
  validateCanonicalInputPlan program plan
  pure prepared

/-- Default checked compilation-plan preparation. The bound mirrors the public
compiler's default specialization budget while remaining explicit through the
`WithBudget` entry for clients that need a different policy. -/
def prepareExecutablePlanEvidence (program : CheckedProgram)
    (plan : Plan) : Except RuntimeError Plan :=
  prepareExecutablePlanEvidenceWithBudget program plan 1024 1024

/-- Signature-aware safe-boundary validation.  In addition to authenticating
all retained evidence, this closes and validates the full source frontier of
every selected operator and coercion method before execution can mutate the
heap. -/
def validateExecutablePlanEvidence (program : CheckedProgram)
    (plan : Plan) : Except RuntimeError Unit := do
  discard <| prepareExecutablePlanEvidence program plan

end Solcore.Frontend.SourceCompilationPlan
