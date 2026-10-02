import Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedCallEvidence
import Solcore.SourceSemantics.Dynamic.Evaluation

/-! Exact source-ordered call requirement layouts recovered from successful
compiler selection. Coercion requirements stay on both sides of the selected
signature spine; no unordered set of requirement IDs is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCallRequirementLayouts
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallableNamedMetadata (evidence environment)

private instance : LawfulBEq RequirementId where
  eq_of_beq := by
    intro a b same
    cases a; cases b
    simp_all [BEq.beq, instBEqRequirementId.beq]
  rfl := by intro a; cases a; simp [BEq.beq, instBEqRequirementId.beq]

/-- The source split includes every coercion step and every retained ID. -/
def Split (node : ExpressionNode) (count : Nat) (ids : List RequirementId) : Prop :=
  ∃ before after, node.coercions = before ++ after ∧
    node.requirements = coercionRequirementIds before ++ (ids ++ coercionRequirementIds after) ∧ ids.length = count

private def candidateAt (node : ExpressionNode) (count split : Nat) : Option (List RequirementId) :=
  let before := coercionRequirementIds (node.coercions.take split)
  let after := coercionRequirementIds (node.coercions.drop split)
  let middleAndAfter := node.requirements.drop before.length
  let middle := middleAndAfter.take count
  if node.requirements.take before.length = before &&
      middle.length = count && middleAndAfter.drop count = after then some middle else none

private def uniqueLists (candidates : List (List RequirementId)) : List (List RequirementId) :=
  candidates.foldl (fun unique candidate => if unique.contains candidate then unique else unique ++ [candidate]) []

private def candidates (node : ExpressionNode) (count : Nat) : List (List RequirementId) :=
  uniqueLists ((List.range (node.coercions.length + 1)).filterMap (candidateAt node count))

private theorem uniqueLists_mem {id : List RequirementId} {items : List (List RequirementId)} :
    id ∈ uniqueLists items ↔ id ∈ items := by
  have general : ∀ initial, id ∈ items.foldl (fun unique candidate => if unique.contains candidate then unique else unique ++ [candidate]) initial ↔
      id ∈ initial ∨ id ∈ items := by
    induction items with
    | nil => intro initial; simp
    | cons head tail ih =>
      intro initial
      simp only [List.foldl_cons]
      split
      · rename_i present
        rw [ih]
        have member : head ∈ initial := List.contains_iff_mem.mp present
        simp only [List.mem_cons]
        constructor
        · intro accepted; exact accepted.elim Or.inl (fun h => .inr (.inr h))
        · rintro (h | h | h)
          · exact .inl h
          · exact .inl (h ▸ member)
          · exact .inr h
      · rw [ih]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · rintro ((h | h) | h)
          · exact .inl h
          · exact .inr (.inl h)
          · exact .inr (.inr h)
        · rintro (h | h | h)
          · exact .inl (.inl h)
          · exact .inl (.inr h)
          · exact .inr h
  simpa only [uniqueLists, List.not_mem_nil, false_or] using general []

private theorem candidateAt_sound {node : ExpressionNode} {count split : Nat} {ids : List RequirementId}
    (found : candidateAt node count split = some ids) : Split node count ids := by
  simp only [candidateAt] at found
  split at found
  · rename_i checks
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checks
    have same := Option.some.inj found
    subst ids
    refine ⟨node.coercions.take split, node.coercions.drop split, (List.take_append_drop ..).symm, ?_, checks.1.2⟩
    calc
      node.requirements = node.requirements.take (coercionRequirementIds (node.coercions.take split)).length ++
          node.requirements.drop (coercionRequirementIds (node.coercions.take split)).length := (List.take_append_drop ..).symm
      _ = coercionRequirementIds (node.coercions.take split) ++
          node.requirements.drop (coercionRequirementIds (node.coercions.take split)).length := by rw [checks.1.1]
      _ = _ := by
        congr 1
        have parts := List.take_append_drop count (node.requirements.drop (coercionRequirementIds (node.coercions.take split)).length)
        rw [checks.2] at parts
        exact parts.symm
  · cases found

private theorem candidateAt_complete {node : ExpressionNode} {count : Nat} {ids : List RequirementId}
    {before after : List CoercionStep}
    (steps : node.coercions = before ++ after)
    (requirements : node.requirements = coercionRequirementIds before ++ (ids ++ coercionRequirementIds after))
    (length : ids.length = count) : candidateAt node count before.length = some ids := by
  simp [candidateAt, steps, requirements, ← length]

private theorem candidates_iff {node : ExpressionNode} {count : Nat} {ids : List RequirementId} :
    ids ∈ candidates node count ↔ Split node count ids := by
  rw [candidates, uniqueLists_mem, List.mem_filterMap]
  constructor
  · rintro ⟨split, _, found⟩
    exact candidateAt_sound found
  · rintro ⟨before, after, steps, requirements, length⟩
    exact ⟨before.length, by simp only [List.mem_range, steps, List.length_append]; omega, candidateAt_complete steps requirements length⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩


private def predicateMatches (caller : SourceSpecialization.SpecializedFunction)
    (requirements : List RequirementId) (predicates : List ProgramPredicate) : Bool :=
  requirements.length == predicates.length &&
    (List.zip requirements predicates).all fun pair =>
      match (match caller.function.solvedRequirements.filter (fun solved => solved.id == pair.1) with
        | [solved] => some solved
        | _ => none) with
      | some solved => solved.predicate == pair.2 && solved.evidence.goal == pair.2
      | none => false

private theorem direct_selected {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (accepted : SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation = .ok actual) :
    ∃ ids, Split node instantiation.predicates.length ids ∧
      SourceCompilationPlan.materializeCallEvidence caller node.id available ids instantiation.predicates = .ok actual ∧
      (candidates node instantiation.predicates.length = [ids] ∨
        (candidates node instantiation.predicates.length).filter (fun ids => predicateMatches caller ids instantiation.predicates) = [ids]) := by
  unfold SourceCompilationPlan.exactDirectCallRuntimeEvidence at accepted
  obtain ⟨ids, chosen, materialized⟩ := bind_ok accepted
  change (do
    if node.coercions.isEmpty && node.requirements.length != instantiation.predicates.length then
      throw (.callRequirementCountMismatch caller.key node.id instantiation.predicates.length node.requirements.length)
    match (_ : Option RequirementId) with
    | some requirement => throw (.duplicateCallRequirement caller.key node.id requirement)
    | none => pure ()
    let structural := candidates node instantiation.predicates.length
    let matched := structural.filter fun ids => predicateMatches caller ids instantiation.predicates
    match structural with
    | [requirements] => return requirements
    | _ => pure ()
    match matched with
    | [requirements] => pure requirements
    | _ => throw (.invalidDirectCallRequirementLayout caller.key node.id node.requirements)
    : Except SourceTypedRuntime.RuntimeError (List RequirementId)) = .ok ids at chosen
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at chosen
  split at chosen
  · simp at chosen
  · split at chosen
    · cases chosen
    · split at chosen
      · rename_i selected same
        cases chosen
        exact ⟨ids, candidates_iff.mp (by rw [same]; simp), materialized, .inl same⟩
      · split at chosen
        · rename_i selected same
          cases chosen
          exact ⟨ids, candidates_iff.mp (List.mem_filter.mp (show ids ∈ (candidates node instantiation.predicates.length).filter (fun ids => predicateMatches caller ids instantiation.predicates) from by rw [same]; simp)).1, materialized, .inr same⟩
        · cases chosen

/-- The actual chosen signature dictionary has the independent interleaving
required for a source direct call. Full callee authentication validates only
its reached rows; no source ledger validity input is required. -/
theorem direct_produces {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment} {context : Context} {callee : SourceCompilationPlan.Key}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation = .ok actual)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures callee instantiation.predicates actual = .ok ()) :
    DirectCallProducesEvidence context (environment available) node.requirements node.coercions instantiation.predicates (environment actual) := by
  obtain ⟨ids, ⟨before, after, steps, requirements, _⟩, materialized, _⟩ := direct_selected accepted
  exact .intro steps requirements
    (CallableAuthenticatedCallEvidence.produces signatures ledger assumptions resolved materialized authenticated)


private instance : LawfulBEq ProgramTraitId where
  eq_of_beq := by intro a b same; cases a <;> cases b <;> simp_all [BEq.beq, instBEqProgramTraitId.beq]
  rfl := by
    intro a
    cases a with
    | builtin id => cases id <;> rfl
    | declaration id => simp [BEq.beq, instBEqProgramTraitId.beq]

private instance : LawfulBEq ProgramPredicate where
  eq_of_beq := by
    intro first second same
    cases first with
    | mk a b c =>
      cases second with
      | mk x y z =>
        change ((a == x) && ((b == y) && (c == z))) = true at same
        simp only [Bool.and_eq_true, beq_iff_eq] at same
        rcases same with ⟨rfl, rfl, rfl⟩
        rfl
  rfl := by
    intro value
    change ((value.trait == value.trait) && ((value.subject == value.subject) && (value.arguments == value.arguments))) = true
    simp

/-- Exact singleton rows are needed only for IDs reachable at this occurrence.
This is stronger than identifying two equal rows in a duplicated ledger. -/
def Singletons (caller : SourceSpecialization.SpecializedFunction) (context : Context) (node : ExpressionNode) : Prop :=
  ∀ id, id ∈ node.requirements → ∀ row, ContainsRequirement context id row → CallableCallEvidence.Selected caller id row

private theorem filter_singleton {rows : List SolvedRequirement} {row : SolvedRequirement}
    (unique : (rows.map (·.id)).Nodup) (member : row ∈ rows) :
    rows.filter (fun candidate => decide (candidate.id = row.id)) = [row] := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | member
    · have empty : rest.filter (fun candidate => decide (candidate.id = row.id)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro candidate present
        have different : candidate.id ≠ row.id := by
          intro same
          exact distinct.1 (List.mem_map.mpr ⟨candidate, present, same⟩)
        simp [different]
      simp [empty]
    · have different : first.id ≠ row.id := by
        intro same
        exact distinct.1 (List.mem_map.mpr ⟨row, member, same.symm⟩)
      simpa [different] using ih distinct.2 member

/-- The ordinary source identity invariant supplies the reached singleton
condition without imposing validity on unrelated retained rows. -/
theorem singletons_of_unique {caller : SourceSpecialization.SpecializedFunction}
    {context : Context} {node : ExpressionNode}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (unique : RequirementIdsUnique context) : Singletons caller context node := by
  intro id _ row contains
  obtain ⟨member, same⟩ := contains
  change caller.function.solvedRequirements.filter (fun candidate => decide (candidate.id = id)) = [row]
  rw [← ledger, ← same]
  exact filter_singleton unique member

private theorem predicateMatches_of_produces {caller : SourceSpecialization.SpecializedFunction} {context : Context}
    {available result : EvidenceEnvironment} {ids : List RequirementId} {predicates : List ProgramPredicate}
    (singleton : ∀ id, id ∈ ids → ∀ row, ContainsRequirement context id row → CallableCallEvidence.Selected caller id row)
    (produced : RequirementsProduceEnvironment context available ids predicates result) : predicateMatches caller ids predicates = true := by
  induction produced with
  | nil => rfl
  | @cons id ids predicate predicates selected result head tail ih =>
    have rest := ih (fun id member row contains => singleton id (List.mem_cons_of_mem _ member) row contains)
    cases head with
    | intro contains same represents valid closes closedValid =>
      rename_i row openEvidence
      have chosen := singleton _ (by simp) _ contains
      have chosen : caller.function.solvedRequirements.filter (fun solved => solved.id == id) = [row] := by
        have predicates : (fun solved : SolvedRequirement => solved.id == id) =
            (fun solved : SolvedRequirement => decide (solved.id = id)) := by
          funext solved
          apply Bool.eq_iff_iff.mpr
          simp only [beq_iff_eq, decide_eq_true_eq]
        rw [predicates]
        exact chosen
      have goal := valid.evidence_goal_eq
      simp only [predicateMatches, Bool.and_eq_true] at rest ⊢
      refine ⟨by simp [tail.length_eq.1], ?_⟩
      simp only [List.zip_cons_cons, List.all_cons, chosen, same, goal, BEq.rfl, Bool.true_and]
      exact rest.2

/-- Any independent source split whose reached ledger rows are singleton has
exactly the dictionary returned by the real compiler selection. -/
theorem direct_agrees {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {context : Context} {semantic : EvidenceEnvironment}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (singleton : Singletons caller context node)
    (accepted : SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation = .ok actual)
    (independent : DirectCallProducesEvidence context (environment available) node.requirements node.coercions instantiation.predicates semantic) :
    semantic = environment actual := by
  obtain ⟨ids, layout, materialized, chosen⟩ := direct_selected accepted
  cases independent with
  | @intro before after sourceIds sourceResult steps requirements produced =>
    have member : sourceIds ∈ candidates node instantiation.predicates.length :=
      candidates_iff.mpr ⟨before, after, steps, requirements, produced.length_eq.1⟩
    have same : sourceIds = ids := by
      rcases chosen with structural | filtered
      · rw [structural] at member
        exact List.mem_singleton.mp member
      · have matched := predicateMatches_of_produces (caller := caller) (fun id member row contains =>
          singleton id (by rw [requirements]; simp only [List.mem_append]; exact .inr (.inl member)) row contains) produced
        have inFilter : sourceIds ∈ (candidates node instantiation.predicates.length).filter
            (fun ids => predicateMatches caller ids instantiation.predicates) :=
          List.mem_filter.mpr ⟨member, matched⟩
        rw [filtered] at inFilter
        exact List.mem_singleton.mp inFilter
    subst sourceIds
    exact CallableCallEvidence.agrees ledger materialized produced

/-- Standalone references retain their signature requirements before the whole
output coercion path, including repeated requirement IDs in that path. -/
theorem ordinary_owned {node : ExpressionNode} {ids : List RequirementId}
    (selected : SourceCompilationPlan.ordinaryOwnedRequirements? node = some ids) :
    OrdinaryRequirementLayout node.requirements node.coercions ids := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements? at selected
  dsimp only at selected
  split at selected
  · cases selected
  · split at selected
    · rename_i same
      cases selected
      exact same
    · cases selected

private theorem reference_selected {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (accepted : SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence caller node available instantiation = .ok actual) :
    ∃ ids, OrdinaryRequirementLayout node.requirements node.coercions ids ∧
      SourceCompilationPlan.materializeCallEvidence caller node.id available ids instantiation.predicates = .ok actual := by
  unfold SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence at accepted
  obtain ⟨ids, chosen, materialized⟩ := bind_ok accepted
  change (do
    let requirements ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
      | some requirements => pure requirements
      | none => throw (.invalidDeclarationReferenceRequirementLayout caller.key node.id node.requirements)
    if requirements.length != instantiation.predicates.length then
      throw (.callRequirementCountMismatch caller.key node.id instantiation.predicates.length requirements.length)
    match (_ : List RequirementId → Option RequirementId) requirements with
    | some requirement => throw (.duplicateCallRequirement caller.key node.id requirement)
    | none => pure ()
    unless predicateMatches caller requirements instantiation.predicates do
      throw (.invalidDeclarationReferenceRequirementLayout caller.key node.id requirements)
    pure requirements : Except SourceTypedRuntime.RuntimeError (List RequirementId)) = .ok ids at chosen
  cases found : SourceCompilationPlan.ordinaryOwnedRequirements? node with
  | none => simp [found, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at chosen
  | some requirements =>
    simp only [found, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at chosen
    split at chosen
    · cases chosen
    · split at chosen
      · cases chosen
      · split at chosen
        · cases chosen
          exact ⟨ids, ordinary_owned found, materialized⟩
        · cases chosen

theorem reference_produces {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment} {context : Context} {callee : SourceCompilationPlan.Key}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence caller node available instantiation = .ok actual)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures callee instantiation.predicates actual = .ok ()) :
    ∃ ids, OrdinaryRequirementLayout node.requirements node.coercions ids ∧
      RequirementsProduceEnvironment context (environment available) ids instantiation.predicates (environment actual) := by
  obtain ⟨ids, layout, materialized⟩ := reference_selected accepted
  exact ⟨ids, layout, CallableAuthenticatedCallEvidence.produces signatures ledger assumptions resolved materialized authenticated⟩

theorem reference_agrees {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {context : Context} {ids : List RequirementId} {semantic : EvidenceEnvironment}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (accepted : SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence caller node available instantiation = .ok actual)
    (layout : OrdinaryRequirementLayout node.requirements node.coercions ids)
    (independent : RequirementsProduceEnvironment context (environment available) ids instantiation.predicates semantic) :
    semantic = environment actual := by
  obtain ⟨chosen, selected, materialized⟩ := reference_selected accepted
  have same : ids = chosen := List.append_cancel_right (layout.symm.trans selected)
  subst ids
  exact CallableCallEvidence.agrees ledger materialized independent

end Solcore.SourceSemantics.CoreLowering.CallableCallRequirementLayouts
