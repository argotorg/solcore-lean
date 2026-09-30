import Solcore.Frontend.SourceSpecializationWorklist

/-!
Backend-independent canonical specialization-plan validation.

This preserves the direct linker's diagnostic ordering and the proofs that
successful checking reconstructs the exact frontier and backs every edge by a
retained specialization. It does not import either lowering or an evaluator.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCompilationPlan.Canonical

open SourceInference TypeSystem

abbrev SpecializationKey := SourceSpecialization.SpecializationKey
abbrev SpecializedFunction := SourceSpecialization.SpecializedFunction
abbrev WorklistError := SourceSpecializationWorklist.Error
abbrev CallEdge := SourceSpecializationWorklist.CallEdge
abbrev ReferenceEdge := SourceSpecializationWorklist.ReferenceEdge
abbrev Plan := SourceSpecializationWorklist.Plan

/-- Diagnostics from canonical plan validation, before any backend lowering. -/
inductive Error where
  | worklist (error : WorklistError)
  | malformedCall (error : WorklistError)
  | indirectCall (occurrence : ExpressionId)
  | nonCanonicalSpecialization (key : SpecializationKey)
  | duplicateSpecialization (key : SpecializationKey)
  | missingSpecialization (key : SpecializationKey)
  | specializationOrderMismatch
      (expected actual : List SpecializationKey)
  | callEdgesMismatch (expected actual : List CallEdge)
  | referenceEdgesMismatch (expected actual : List ReferenceEdge)
  deriving Repr

private def liftWorklistValidation : WorklistError → Error
  | error@(.missingCalleeNode _ _) => .malformedCall error
  | error@(.calleeNotDeclarationReference _ _) => .malformedCall error
  | error@(.calleeInstantiationDeclarationMismatch _ _ _) =>
      .malformedCall error
  | error@(.calleeInstantiationMetadataMismatch _ _ _) =>
      .malformedCall error
  | error@(.calleeNodeTypeMismatch _ _ _) => .malformedCall error
  | error@(.specializedCalleeTypeMismatch _ _ _) => .malformedCall error
  | error@(.specializedCalleeAssumptionsMismatch _ _ _) =>
      .malformedCall error
  | error@(.specializedCalleeParameterComptimeMismatch _ _ _) =>
      .malformedCall error
  | error@(.specializedCalleeReturnComptimeMismatch _ _ _) =>
      .malformedCall error
  | .indirectCall occurrence => .indirectCall occurrence
  | error => .worklist error

private def firstDuplicateKey : List SpecializationKey → Option SpecializationKey
  | [] => none
  | key :: rest =>
      if rest.contains key then some key else firstDuplicateKey rest

private def specializationKeys
    (specializations : List SpecializedFunction) : List SpecializationKey :=
  specializations.map (·.key)

private def lookupSpecialization? (plan : Plan)
    (key : SpecializationKey) : Option SpecializedFunction :=
  plan.specializations.find? fun specialized => decide (specialized.key = key)

private def exactSpecialization (plan : Plan)
    (key : SpecializationKey) : Except Error SpecializedFunction :=
  match lookupSpecialization? plan key with
  | none => .error (.missingSpecialization key)
  | some specialized => .ok specialized

private def validateCanonicalSpecializations (program : CheckedProgram) :
    List SpecializedFunction → Except Error Unit
  | [] => pure ()
  | specialized :: rest => do
      let canonical ← (SourceSpecializationWorklist.resolveRequest program {
        declaration := specialized.declaration
        parameterSubstitution := specialized.parameterSubstitution
      }).mapError liftWorklistValidation
      if canonical == specialized then
        validateCanonicalSpecializations program rest
      else
        throw (.nonCanonicalSpecialization specialized.key)

private def validateKnownEdgeKeys (plan : Plan) :
    List CallEdge → Except Error Unit
  | [] => pure ()
  | edge :: rest => do
      if (lookupSpecialization? plan edge.caller).isNone then
        throw (.missingSpecialization edge.caller)
      else if (lookupSpecialization? plan edge.callee).isNone then
        throw (.missingSpecialization edge.callee)
      else
        validateKnownEdgeKeys plan rest

private def validateKnownReferenceEdgeKeys (plan : Plan) :
    List ReferenceEdge → Except Error Unit
  | [] => pure ()
  | edge :: rest => do
      if (lookupSpecialization? plan edge.caller).isNone then
        throw (.missingSpecialization edge.caller)
      else if (lookupSpecialization? plan edge.callee).isNone then
        throw (.missingSpecialization edge.callee)
      else
        validateKnownReferenceEdgeKeys plan rest

private def seedRequests (plan : Plan) :
    List SpecializationKey →
      Except Error (List SourceSpecializationWorklist.Request)
  | [] => pure []
  | key :: rest => do
      let specialized ← exactSpecialization plan key
      pure ({
        declaration := specialized.declaration
        parameterSubstitution := specialized.parameterSubstitution
      } :: (← seedRequests plan rest))

private theorem specializationKey_eq_of_beq
    (left right : SpecializationKey) (accepted : (left == right) = true) :
    left = right := by
  cases left
  cases right
  delta SourceSpecialization.instBEqSpecializationKey
    SourceSpecialization.instBEqSpecializationKey.beq at accepted
  simp only [Bool.and_eq_true, beq_iff_eq] at accepted
  simp_all

private theorem occurrenceId_eq_of_beq
    (left right : OccurrenceId) (accepted : (left == right) = true) :
    left = right := by
  cases left
  cases right
  delta SourceInference.instBEqOccurrenceId
    SourceInference.instBEqOccurrenceId.beq at accepted
  obtain ⟨ownerEqual, indexEqual⟩ := Bool.and_eq_true_iff.mp accepted
  cases beq_iff_eq.mp ownerEqual
  cases beq_iff_eq.mp indexEqual
  rfl

private theorem expressionId_eq_of_beq
    (left right : ExpressionId) (accepted : (left == right) = true) :
    left = right := by
  cases left with
  | mk leftOccurrence =>
      cases right with
      | mk rightOccurrence =>
          delta SourceInference.instBEqExpressionId
            SourceInference.instBEqExpressionId.beq at accepted
          cases occurrenceId_eq_of_beq _ _ accepted
          rfl

private theorem callEdge_eq_of_beq
    (left right : CallEdge) (accepted : (left == right) = true) :
    left = right := by
  cases left
  cases right
  delta SourceSpecializationWorklist.instBEqCallEdge
    SourceSpecializationWorklist.instBEqCallEdge.beq at accepted
  have outer := Bool.and_eq_true_iff.mp accepted
  have inner := Bool.and_eq_true_iff.mp outer.2
  cases specializationKey_eq_of_beq _ _ outer.1
  cases expressionId_eq_of_beq _ _ inner.1
  cases specializationKey_eq_of_beq _ _ inner.2
  rfl

private theorem referenceEdge_eq_of_beq
    (left right : ReferenceEdge) (accepted : (left == right) = true) :
    left = right := by
  cases left
  cases right
  delta SourceSpecializationWorklist.instBEqReferenceEdge
    SourceSpecializationWorklist.instBEqReferenceEdge.beq at accepted
  have outer := Bool.and_eq_true_iff.mp accepted
  have inner := Bool.and_eq_true_iff.mp outer.2
  cases specializationKey_eq_of_beq _ _ outer.1
  cases expressionId_eq_of_beq _ _ inner.1
  cases specializationKey_eq_of_beq _ _ inner.2
  rfl

private theorem beq_true_of_bne_not_true {Value : Type} [BEq Value]
    (left right : Value) (accepted : ¬(left != right) = true) :
    (left == right) = true := by
  cases equal : (left == right) with
  | false =>
      have different : (left != right) = true := by
        simp [bne, equal]
      exact False.elim (accepted different)
  | true => rfl

private theorem list_eq_of_beq {Value : Type} [BEq Value]
    (reflect : ∀ left right : Value, (left == right) = true → left = right) :
    ∀ left right : List Value, (left == right) = true → left = right
  | [], [], _ => rfl
  | [], _ :: _, accepted => by cases accepted
  | _ :: _, [], accepted => by cases accepted
  | left :: lefts, right :: rights, accepted => by
      have parts := Bool.and_eq_true_iff.mp accepted
      cases reflect left right parts.1
      cases list_eq_of_beq reflect lefts rights parts.2
      rfl

private theorem specializationKey_eq_of_specializedFunction_beq
    (left right : SpecializedFunction) (accepted : (left == right) = true) :
    left.key = right.key := by
  cases left
  cases right
  delta SourceSpecialization.instBEqSpecializedFunction
    SourceSpecialization.instBEqSpecializedFunction.beq at accepted
  exact specializationKey_eq_of_beq _ _
    (Bool.and_eq_true_iff.mp accepted).1

private theorem resolveRequest_key_eq_of_canonicalSpecializations
    (program : CheckedProgram) (specializations : List SpecializedFunction)
    (specialized : SpecializedFunction)
    (accepted : validateCanonicalSpecializations program specializations =
      .ok ())
    (member : specialized ∈ specializations) :
    ∃ canonical,
      SourceSpecializationWorklist.resolveRequest program {
        declaration := specialized.declaration
        parameterSubstitution := specialized.parameterSubstitution
      } = .ok canonical ∧ canonical.key = specialized.key := by
  induction specializations with
  | nil => simp at member
  | cons head rest ih =>
      simp only [validateCanonicalSpecializations] at accepted
      cases resolved : SourceSpecializationWorklist.resolveRequest program {
          declaration := head.declaration
          parameterSubstitution := head.parameterSubstitution
        } with
      | error error =>
          simp [resolved, Except.mapError, bind, Except.bind] at accepted
      | ok canonical =>
          simp only [resolved, Except.mapError, bind, Except.bind] at accepted
          split at accepted
          next equal =>
            simp only [List.mem_cons] at member
            cases member with
            | inl headEqual =>
                subst specialized
                exact ⟨canonical, resolved,
                  specializationKey_eq_of_specializedFunction_beq
                    canonical head equal⟩
            | inr restMember => exact ih accepted restMember
          next notEqual => cases accepted

private theorem canonicalSeedKeys_eq_of_seedRequests
    (program : CheckedProgram) (plan : Plan)
    (keys : List SpecializationKey)
    (seeds : List SourceSpecializationWorklist.Request)
    (canonical : validateCanonicalSpecializations program
      plan.specializations = .ok ())
    (seeded : seedRequests plan keys = .ok seeds) :
    SourceSpecializationWorklist.canonicalSeedKeys program seeds = .ok keys := by
  induction keys generalizing seeds with
  | nil =>
      simp only [seedRequests, pure, Pure.pure, Except.pure] at seeded
      cases seeded
      rfl
  | cons key rest ih =>
      simp only [seedRequests] at seeded
      cases found : exactSpecialization plan key with
      | error error =>
          simp [found, bind, Except.bind] at seeded
      | ok specialized =>
          simp only [found, bind, Except.bind] at seeded
          cases seededRest : seedRequests plan rest with
          | error error => simp [seededRest] at seeded
          | ok restSeeds =>
              simp only [seededRest, pure, Pure.pure, Except.pure] at seeded
              cases seeded
              have lookup : lookupSpecialization? plan key = some specialized := by
                unfold exactSpecialization at found
                split at found
                next equality => cases found
                next candidate equality =>
                  have candidateEqual : candidate = specialized := by
                    exact Except.ok.inj found
                  simpa [candidateEqual] using equality
              have member : specialized ∈ plan.specializations := by
                unfold lookupSpecialization? at lookup
                exact List.mem_of_find?_eq_some lookup
              obtain ⟨resolvedSpecialized, resolved, resolvedKey⟩ :=
                resolveRequest_key_eq_of_canonicalSpecializations
                program plan.specializations specialized canonical member
              have specializedKey : specialized.key = key := by
                unfold lookupSpecialization? at lookup
                have selected := List.find?_some lookup
                exact of_decide_eq_true selected
              simp only [SourceSpecializationWorklist.canonicalSeedKeys,
                resolved, bind, Except.bind, pure, Pure.pure, Except.pure]
              rw [resolvedKey, specializedKey]
              rw [ih restSeeds seededRest]

private theorem except_bind_ok {Failure Value Result : Type}
    (source : Except Failure Value)
    (continuation : Value → Except Failure Result) (result : Result)
    (accepted : source.bind continuation = .ok result) :
    ∃ value, source = .ok value ∧ continuation value = .ok result := by
  cases source with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_eq_ok {Failure OtherFailure Value : Type}
    (source : Except Failure Value) (transform : Failure → OtherFailure)
    (value : Value) (accepted : source.mapError transform = .ok value) :
    source = .ok value := by
  cases source with
  | error error => cases accepted
  | ok actual => cases accepted; rfl

private theorem key_mem_specializationKeys_of_lookup
    (plan : Plan) (key : SpecializationKey) (specialized : SpecializedFunction)
    (found : lookupSpecialization? plan key = some specialized) :
    key ∈ plan.specializationKeys := by
  have member : specialized ∈ plan.specializations := by
    unfold lookupSpecialization? at found
    exact List.mem_of_find?_eq_some found
  have selected : specialized.key = key := by
    unfold lookupSpecialization? at found
    have accepted := List.find?_some found
    exact of_decide_eq_true accepted
  exact List.mem_map.mpr ⟨specialized, member, selected⟩

private theorem validateKnownEdgeKeys_sound (plan : Plan)
    (edges : List CallEdge)
    (accepted : validateKnownEdgeKeys plan edges = .ok ()) :
    ∀ edge ∈ edges,
      edge.caller ∈ plan.specializationKeys ∧
        edge.callee ∈ plan.specializationKeys := by
  induction edges with
  | nil => simp
  | cons head rest ih =>
      simp only [validateKnownEdgeKeys] at accepted
      cases caller : lookupSpecialization? plan head.caller with
      | none => simp [caller] at accepted
      | some callerSpecialized =>
          cases callee : lookupSpecialization? plan head.callee with
          | none => simp [caller, callee] at accepted
          | some calleeSpecialized =>
              simp only [caller, callee, Option.isNone_some, Bool.false_eq_true,
                ↓reduceIte] at accepted
              intro edge member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact ⟨key_mem_specializationKeys_of_lookup plan _ _ caller,
                  key_mem_specializationKeys_of_lookup plan _ _ callee⟩
              · exact ih accepted edge member

private theorem validateKnownReferenceEdgeKeys_sound (plan : Plan)
    (edges : List ReferenceEdge)
    (accepted : validateKnownReferenceEdgeKeys plan edges = .ok ()) :
    ∀ edge ∈ edges,
      edge.caller ∈ plan.specializationKeys ∧
        edge.callee ∈ plan.specializationKeys := by
  induction edges with
  | nil => simp
  | cons head rest ih =>
      simp only [validateKnownReferenceEdgeKeys] at accepted
      cases caller : lookupSpecialization? plan head.caller with
      | none => simp [caller] at accepted
      | some callerSpecialized =>
          cases callee : lookupSpecialization? plan head.callee with
          | none => simp [caller, callee] at accepted
          | some calleeSpecialized =>
              simp only [caller, callee, Option.isNone_some, Bool.false_eq_true,
                ↓reduceIte] at accepted
              intro edge member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact ⟨key_mem_specializationKeys_of_lookup plan _ _ caller,
                  key_mem_specializationKeys_of_lookup plan _ _ callee⟩
              · exact ih accepted edge member

/-- Reconstruct the complete worklist result from canonical roots.  This
simultaneously checks reachability/order, missing specializations, and the exact
per-occurrence call-edge list instead of trusting a supplied `Plan`. -/
def validatePlan (program : CheckedProgram) (plan : Plan) : Except Error Unit := do
  let keys := specializationKeys plan.specializations
  match firstDuplicateKey keys with
  | some key => throw (.duplicateSpecialization key)
  | none => pure ()
  validateCanonicalSpecializations program plan.specializations
  for key in plan.seedKeys do
    if (lookupSpecialization? plan key).isNone then
      throw (.missingSpecialization key)
  validateKnownEdgeKeys plan plan.callEdges
  validateKnownReferenceEdgeKeys plan plan.referenceEdges
  let seeds ← seedRequests plan plan.seedKeys
  let rebuilt ← (SourceSpecializationWorklist.run program seeds
    plan.specializations.length).mapError liftWorklistValidation
  match rebuilt with
  | .budgetExhausted _ next _ =>
      throw (.missingSpecialization next)
  | .complete expected =>
      let expectedKeys := specializationKeys expected.specializations
      if expectedKeys != keys then
        throw (.specializationOrderMismatch expectedKeys keys)
      else if expected.callEdges != plan.callEdges then
        throw (.callEdgesMismatch expected.callEdges plan.callEdges)
      else if expected.referenceEdges != plan.referenceEdges then
        throw (.referenceEdgesMismatch expected.referenceEdges
          plan.referenceEdges)
      else
        pure ()

/-- Successful validation exposes the exact bounded worklist replay used by
the defensive canonical-plan check.  The replay preserves canonical root
order (including duplicate roots), specialization-key order, and both edge
ledgers. -/
theorem validatePlan_completeReplay (program : CheckedProgram) (plan : Plan)
    (accepted : validatePlan program plan = .ok ()) :
    ∃ seeds expected,
      SourceSpecializationWorklist.run program seeds
          plan.specializations.length = .ok (.complete expected) ∧
        expected.seedKeys = plan.seedKeys ∧
        expected.specializationKeys = plan.specializationKeys ∧
        expected.callEdges = plan.callEdges ∧
        expected.referenceEdges = plan.referenceEdges := by
  unfold validatePlan at accepted
  simp only at accepted
  split at accepted
  next duplicate => cases accepted
  next noDuplicate =>
    obtain ⟨_, canonical, accepted⟩ := except_bind_ok _ _ _ accepted
    obtain ⟨_, _, accepted⟩ := except_bind_ok _ _ _ accepted
    obtain ⟨_, _, accepted⟩ := except_bind_ok _ _ _ accepted
    obtain ⟨_, _, accepted⟩ := except_bind_ok _ _ _ accepted
    obtain ⟨seeds, seeded, accepted⟩ := except_bind_ok _ _ _ accepted
    obtain ⟨rebuilt, replayMapped, accepted⟩ :=
      except_bind_ok _ _ _ accepted
    have replayRaw := mapError_eq_ok
      (SourceSpecializationWorklist.run program seeds
        plan.specializations.length)
      liftWorklistValidation rebuilt replayMapped
    cases rebuilt with
    | budgetExhausted rebuilt next pending => cases accepted
    | complete expected =>
        split at accepted
        next mismatch => cases accepted
        next replayExpectedEqual =>
          split at accepted
          next mismatch => cases accepted
          next keyOrderNotDifferent =>
            split at accepted
            next mismatch => cases accepted
            next callEdgesNotDifferent =>
              cases replayExpectedEqual
              have keyOrderEqual :
                  specializationKeys expected.specializations =
                    specializationKeys plan.specializations :=
                list_eq_of_beq specializationKey_eq_of_beq _ _
                  (beq_true_of_bne_not_true _ _ keyOrderNotDifferent)
              have callEdgesEqual : expected.callEdges = plan.callEdges :=
                list_eq_of_beq callEdge_eq_of_beq _ _
                  (beq_true_of_bne_not_true _ _ callEdgesNotDifferent)
              split at accepted
              next mismatch => cases accepted
              next referenceEdgesNotDifferent =>
                have referenceEdgesEqual : expected.referenceEdges =
                    plan.referenceEdges :=
                  list_eq_of_beq referenceEdge_eq_of_beq _ _
                    (beq_true_of_bne_not_true _ _
                      referenceEdgesNotDifferent)
                have canonicalSeeds := canonicalSeedKeys_eq_of_seedRequests
                  program plan plan.seedKeys seeds canonical seeded
                have replaySeedKeys :=
                  SourceSpecializationWorklist.run_seedKeys_eq_canonical
                    program seeds plan.specializations.length
                    (.complete expected) replayRaw
                have seedKeysEqual : expected.seedKeys = plan.seedKeys := by
                  rw [canonicalSeeds] at replaySeedKeys
                  exact Except.ok.inj replaySeedKeys.symm
                exact ⟨seeds, expected, replayRaw, seedKeysEqual,
                  keyOrderEqual, callEdgesEqual, referenceEdgesEqual⟩

/-- Every endpoint named by an accepted plan's edge ledgers is backed by a
specialization in that plan. -/
theorem validatePlan_edgeKeys_mem (program : CheckedProgram) (plan : Plan)
    (accepted : validatePlan program plan = .ok ()) :
    (∀ edge ∈ plan.callEdges,
        edge.caller ∈ plan.specializationKeys ∧
          edge.callee ∈ plan.specializationKeys) ∧
      (∀ edge ∈ plan.referenceEdges,
        edge.caller ∈ plan.specializationKeys ∧
          edge.callee ∈ plan.specializationKeys) := by
  unfold validatePlan at accepted
  simp only at accepted
  split at accepted
  next duplicate => cases accepted
  next noDuplicate =>
    obtain ⟨_, _, accepted⟩ := except_bind_ok _ _ _ accepted
    obtain ⟨_, _, accepted⟩ := except_bind_ok _ _ _ accepted
    obtain ⟨_, callAccepted, accepted⟩ := except_bind_ok _ _ _ accepted
    obtain ⟨_, referenceAccepted, _⟩ := except_bind_ok _ _ _ accepted
    exact ⟨validateKnownEdgeKeys_sound plan plan.callEdges callAccepted,
      validateKnownReferenceEdgeKeys_sound plan plan.referenceEdges
        referenceAccepted⟩

end Solcore.Frontend.SourceCompilationPlan.Canonical
