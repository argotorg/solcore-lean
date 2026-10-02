import Solcore.SourceSemantics.CoreLowering.CallableCallEvidence

/-! Actual callee authentication validates every returned evidence tree. Together
with the real caller resolver and materializer receipts, it validates precisely
the retained rows consumed by a call; unrelated local templates are not required
to be valid declaration assumptions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedCallEvidence
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallableNamedMetadata (evidence environment evidence_represents)
open CallableEvidenceEnvironment

private instance : LawfulBEq ProgramTraitId where
  eq_of_beq := by
    intro a b same
    cases a <;> cases b <;> simp_all [BEq.beq, instBEqProgramTraitId.beq]
  rfl := by intro a; cases a with
    | builtin id => cases id <;> rfl
    | declaration id => simp [BEq.beq, instBEqProgramTraitId.beq]

private instance : LawfulBEq BuiltinImplId where
  eq_of_beq := by intro a b same; cases a <;> cases b <;> simp_all [BEq.beq, instBEqBuiltinImplId.beq, BuiltinImplId.ctorIdx]
  rfl := by intro a; cases a <;> rfl

private instance : LawfulBEq ProgramImplId where
  eq_of_beq := by
    intro a b same
    cases a with
    | builtin first =>
      cases b with
      | builtin second => exact congrArg ProgramImplId.builtin (eq_of_beq (show (first == second) = true from same))
      | declaration second => cases same
    | declaration first =>
      cases b with
      | builtin second => cases same
      | declaration second => exact congrArg ProgramImplId.declaration (eq_of_beq (show (first == second) = true from same))
  rfl := by intro a; cases a with
    | builtin id => cases id <;> rfl
    | declaration id => simp [BEq.beq, instBEqProgramImplId.beq]

/-- All positions are authenticated, including later entries shadowed by the
same goal. This is stronger than validity of observable first-match lookups. -/
theorem selection_valid {signatures : ProgramSignatures} {key : SourceCompilationPlan.Key} {index : Nat}
    {predicates : List ProgramPredicate} {actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (accepted : SourceCompilationPlan.validateRuntimeEvidenceSelection signatures key index predicates actual = .ok ()) :
    Forall₂ (fun goal raw => EvidenceValid [] signatures.resolutionRules goal (evidence raw)) predicates actual := by
  induction predicates generalizing actual index with
  | nil => cases actual <;> simp_all [SourceCompilationPlan.validateRuntimeEvidenceSelection]; exact .nil
  | cons goal rest ih =>
    cases actual with
    | nil => simp [SourceCompilationPlan.validateRuntimeEvidenceSelection] at accepted
    | cons raw remaining =>
      simp only [SourceCompilationPlan.validateRuntimeEvidenceSelection] at accepted
      split at accepted
      · cases accepted
      · cases accepted
      · rename_i selected resolved
        split at accepted
        · rename_i same
          have equal : selected = raw := eq_of_beq same
          obtain ⟨semantic, represents, valid⟩ := TraitResolutionSoundness.resolve_success_evidenceValid resolved
          have valid : EvidenceValid [] signatures.resolutionRules goal (evidence raw) := by
            rw [represents.functional (evidence_represents selected)] at valid
            simpa only [equal] using valid
          exact .cons valid (ih accepted)
        · cases raw; cases accepted

theorem authenticated_valid {signatures : ProgramSignatures} {key : SourceCompilationPlan.Key}
    {predicates : List ProgramPredicate} {actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (accepted : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence signatures key predicates actual = .ok ()) :
    Forall₂ (fun goal raw => EvidenceValid [] signatures.resolutionRules goal (evidence raw)) predicates actual := by
  unfold SourceCompilationPlan.validateAuthenticatedRuntimeEvidence at accepted
  cases goals : SourceCompilationPlan.validateRuntimeEvidence key predicates actual with
  | error error => simp [goals, bind, Except.bind] at accepted
  | ok value =>
    simp only [goals, bind, Except.bind] at accepted
    exact selection_valid accepted

/-- A retained implementation is the authenticated returned tree. A retained
assumption is justified by an actual caller dictionary key, not by its ID. -/
theorem retained_of_closed {context : Context} {caller : EvidenceEnvironment}
    {row : SolvedRequirement} {result : TraitEvidence}
    (keys : ∀ goal, goal ∈ caller.map Prod.fst → goal ∈ context.assumptions)
    (goal : row.evidence.goal = row.predicate)
    (closed : EvidenceCloses caller (predicateEvidence row.evidence) result)
    (valid : EvidenceValid [] context.signatures.resolutionRules row.predicate result) :
    SolvedRequirementValid context row := by
  cases row with
  | mk id predicate retained =>
    cases retained with
    | assumption assumed =>
      cases closed with
      | assumption found =>
        exact .intro (.intro (.assumption assumed) (by
          change EvidenceValid context.assumptions context.signatures.resolutionRules predicate (.assumption assumed)
          have same : assumed = predicate := goal
          cases same
          exact .assumption (keys _ found.key_mem)))
    | implementation raw =>
      have same := closes_functional closed (closes_self caller raw)
      rw [same] at valid
      exact .intro (.intro (.implementation (evidence_represents raw))
        (valid.weakenAssumptions (by simp)))

private theorem predicate_goal (retained : PredicateEvidence) :
    (predicateEvidence retained).goal = retained.goal := by
  cases retained with
  | assumption goal => rfl
  | implementation raw => cases raw; simp [predicateEvidence, evidence, TraitEvidence.goal, PredicateEvidence.goal]

/-- Only reached rows acquire validity. No validity premise is imposed on the
whole ledger, including unbound local-scheme templates. -/
theorem produces_of_authenticated {caller : SourceSpecialization.SpecializedFunction} {occurrence : ExpressionId}
    {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment} {ids : List RequirementId}
    {predicates : List ProgramPredicate} {context : Context}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (keys : ∀ goal, goal ∈ (environment available).map Prod.fst → goal ∈ context.assumptions)
    (callerValid : (environment available).Valid context.signatures.resolutionRules)
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok result)
    (authenticated : Forall₂ (fun goal raw => EvidenceValid [] context.signatures.resolutionRules goal (evidence raw)) predicates result) :
    RequirementsProduceEnvironment context (environment available) ids predicates (environment result) := by
  induction ids generalizing predicates result with
  | nil => cases predicates with
    | nil => cases accepted; exact .nil
    | cons => cases accepted
  | cons id ids ih =>
    cases predicates with
    | nil => cases accepted
    | cons predicate predicates =>
      obtain ⟨row, head, tail, selected, rowGoal, closed, headGoal, remaining, rfl⟩ := CallableCallEvidence.cons_accepted accepted
      cases authenticated with
      | cons valid validTail =>
        have openGoal : row.evidence.goal = row.predicate := by
          have same := EvidenceCloses.goal_eq callerValid closed
          rw [evidence_goal, predicate_goal, headGoal] at same
          exact same.symm.trans rowGoal.symm
        have retained := retained_of_closed keys openGoal closed (rowGoal ▸ valid)
        change RequirementsProduceEnvironment context (environment available) (id :: ids) (predicate :: predicates)
          ((SourceCompilationPlan.runtimeEvidenceGoal head, evidence head) :: environment tail)
        rw [headGoal]
        exact .cons (.intro (selected.contains ledger) rowGoal (predicate_represents _) retained closed valid)
          (ih remaining validTail)

/-- The three real compiler receipts close caller and reached-row validity.
Source context alignment is explicit and may include extra lexical assumptions. -/
theorem produces {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {occurrence : ExpressionId} {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate} {context : Context} {callee : SourceCompilationPlan.Key}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok result)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures callee predicates result = .ok ()) :
    RequirementsProduceEnvironment context (environment available) ids predicates (environment result) := by
  have keys : ∀ goal, goal ∈ (environment available).map Prod.fst → goal ∈ context.assumptions := by
    intro goal member
    exact assumptions _ ((resolved_valid resolved).2 ▸ member)
  exact produces_of_authenticated ledger keys
    (by simpa only [signatures] using (resolved_valid resolved).1) accepted
    (by simpa only [signatures] using authenticated_valid authenticated)

end Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedCallEvidence
