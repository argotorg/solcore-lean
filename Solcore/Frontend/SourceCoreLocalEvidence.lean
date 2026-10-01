import Solcore.Frontend.SourceCoreLocalPolymorphism
import Solcore.Frontend.SourceCompilationPlan

/-! Authenticated qualified-local evidence for finite lambda instances.
Original requirement identities remain on body occurrences. Closed witnesses
replace their template assumption rows in the compiler's contextual ledger;
unbound obligations are retained. This module prepares compiler metadata only;
the enclosing compiler authenticates the executable plan before calling it.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreLocalEvidence

open SourceInference TypeSystem
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Instance := SourceCoreLocalPolymorphism.Instance
abbrev Binding := SourceCoreLocalPolymorphism.Binding
abbrev Witness := SourceTypedRuntime.LocalRequirementWitness

mutual
  def applyEvidence (substitution : Substitution) :
      TypedTraitResolution.Evidence → TypedTraitResolution.Evidence
    | .byImpl goal implementation premises =>
        .byImpl (TypedTraitResolution.applySubstitution substitution goal) implementation
          (applyEvidences substitution premises)
  def applyEvidences (substitution : Substitution) :
      List TypedTraitResolution.Evidence → List TypedTraitResolution.Evidence
    | [] => []
    | evidence :: rest => applyEvidence substitution evidence :: applyEvidences substitution rest
end

def applyPredicateEvidence (substitution : Substitution) : PredicateEvidence → PredicateEvidence
  | .assumption predicate => .assumption (TypedTraitResolution.applySubstitution substitution predicate)
  | .implementation evidence => .implementation (applyEvidence substitution evidence)

def applySolvedRequirement (substitution : Substitution) (row : SolvedRequirement) : SolvedRequirement :=
  { row with
    predicate := TypedTraitResolution.applySubstitution substitution row.predicate
    evidence := applyPredicateEvidence substitution row.evidence
  }

theorem applyPredicateEvidence_goal (substitution : Substitution) (evidence : PredicateEvidence) :
    (applyPredicateEvidence substitution evidence).goal =
      TypedTraitResolution.applySubstitution substitution evidence.goal := by
  cases evidence with
  | assumption goal => rfl
  | implementation evidence => cases evidence; rfl

theorem applySolvedRequirement_alignment (substitution : Substitution) (row : SolvedRequirement)
    (aligned : row.evidence.goal = row.predicate) :
    (applySolvedRequirement substitution row).evidence.goal =
      (applySolvedRequirement substitution row).predicate := by
  simpa [applySolvedRequirement, applyPredicateEvidence_goal] using
    congrArg (TypedTraitResolution.applySubstitution substitution) aligned

def rewriteRow (witnesses : List Witness) (row : SolvedRequirement) : SolvedRequirement :=
  match witnesses.find? (fun witness => decide (witness.templateRequirement = row.id)) with
  | none => row
  | some witness => { row with evidence := .implementation witness.evidence }

def rewriteLedger (substitution : Substitution) (witnesses : List Witness)
    (rows : List SolvedRequirement) : List SolvedRequirement :=
  rows.map fun row => rewriteRow witnesses (applySolvedRequirement substitution row)

@[simp] theorem rewriteRow_id (witnesses : List Witness) (row : SolvedRequirement) :
    (rewriteRow witnesses row).id = row.id := by
  unfold rewriteRow
  split <;> rfl

theorem rewriteLedger_ids (substitution : Substitution) (witnesses : List Witness)
    (rows : List SolvedRequirement) :
    (rewriteLedger substitution witnesses rows).map (·.id) = rows.map (·.id) := by
  simp [rewriteLedger, List.map_map, Function.comp_def, applySolvedRequirement]

inductive Error where
  | plan (error : SourceCompilationPlan.Error)
  | discovery (error : SourceSpecializationWorklist.Error)
  | originMismatch (key : Key)
  | bindingMismatch (binder : Resolved.LocalId)
  | instanceMismatch (binder : Resolved.LocalId)
  | parentMismatch (key : Key)
  | missingReference (binder : Resolved.LocalId)
  | missingExpression (id : ExpressionId)
  | duplicateTemplate (requirement : RequirementId)
  | templateRowMismatch (requirement : RequirementId)
  | occurrenceMismatch (id : ExpressionId)
  deriving Repr

structure Prepared where private mk ::
  private origin : Instance
  caller : SourceSpecialization.SpecializedFunction
  witnesses : List Witness

def Prepared.substitution (prepared : Prepared) : Substitution := prepared.origin.origin.substitution
def Prepared.source (prepared : Prepared) : TypedSource := prepared.caller.function.typedBody

/-- Retain the exact authenticated lambda instance for later metadata exports. -/
def Prepared.instance (prepared : Prepared) : Instance := prepared.origin

structure Reference where private mk ::
  id : ExpressionId
  cumulative : Substitution
  witnesses : List Witness
  original : ExpressionNode
  owned : List RequirementId

/-- Only authenticated ordinary scheme-instance requirements are removed.
Coercion-owned requirements and the complete coercion path remain. -/
def Reference.normalized (reference : Reference) : ExpressionNode :=
  { reference.original with
    requirements := reference.original.requirements.filter
      (fun requirement => !reference.owned.contains requirement)
  }

@[simp] theorem Reference.normalized_coercions (reference : Reference) :
    reference.normalized.coercions = reference.original.coercions := rfl

@[simp] theorem Reference.normalized_type (reference : Reference) :
    reference.normalized.type = reference.original.type := rfl

@[simp] theorem Reference.normalized_form (reference : Reference) :
    reference.normalized.form = reference.original.form := rfl

def exactCaller (plan : SourceSpecializationWorklist.Plan) (binding : Binding) :
    Except Error SourceSpecialization.SpecializedFunction := do
  let caller ← (SourceCompilationPlan.exactSpecialization plan binding.caller).mapError Error.plan
  if caller.function.typedBody ≠ binding.source then throw (.originMismatch binding.caller)
  let retained := binding.source.nodes.any fun
    | .statement { form := .letDecl binder (some initializer), .. } =>
        decide (binder = binding.binder ∧ initializer = binding.initializer)
    | _ => false
  unless retained do throw (.bindingMismatch binding.binder.id)
  pure caller

private def activeContext (caller : SourceSpecialization.SpecializedFunction) (parent : Option Prepared) :
    Except Error (Substitution × List Witness) := do
  match parent with
  | none => pure ([], [])
  | some parent =>
      if parent.caller.key ≠ caller.key || parent.origin.origin.source ≠ caller.function.typedBody then
        throw (.parentMismatch caller.key)
      pure (parent.substitution, parent.witnesses)

private def validateWitnesses (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (substitution : Substitution) (witnesses : List Witness) : Except Error Unit := do
  let mut seen := []
  for witness in witnesses do
    if seen.contains witness.templateRequirement then throw (.duplicateTemplate witness.templateRequirement)
    seen := witness.templateRequirement :: seen
    let row ← match caller.function.solvedRequirements.filter (fun row => decide (row.id = witness.templateRequirement)) with
      | [row] => pure (applySolvedRequirement substitution row)
      | _ => throw (.templateRowMismatch witness.templateRequirement)
    if row.predicate ≠ witness.predicate || SourceCompilationPlan.runtimeEvidenceGoal witness.evidence ≠ witness.predicate then
      throw (.templateRowMismatch witness.templateRequirement)
    match row.evidence with
    | .assumption predicate =>
        if predicate ≠ witness.predicate then throw (.templateRowMismatch witness.templateRequirement)
    | .implementation _ => throw (.templateRowMismatch witness.templateRequirement)
    (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures caller.key
      [witness.predicate] [witness.evidence]).mapError Error.plan

def contextualCaller (caller : SourceSpecialization.SpecializedFunction)
    (substitution : Substitution) (witnesses : List Witness) : SourceSpecialization.SpecializedFunction :=
  { caller with function := { caller.function with
      typedBody := caller.function.typedBody.applySubstitution substitution
      solvedRequirements := rewriteLedger substitution witnesses caller.function.solvedRequirements } }

/-- Authenticate one original reference under the enclosing local instance.
The receipt removes exactly its qualified-scheme requirements; caller-selected
raw Core code or a fabricated obligation list cannot create this receipt. -/
def authenticateReference (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (binding : Binding) (parent : Option Prepared) (id : ExpressionId) : Except Error Reference := do
  let caller ← exactCaller plan binding
  let (active, inherited) ← activeContext caller parent
  validateWitnesses program caller active inherited
  let contextual := contextualCaller caller active inherited
  let node ← match contextual.function.typedBody.lookupExpression? id with
    | some node => pure node
    | none => throw (.missingExpression id)
  if id.occurrence.owner ≠ caller.key.declaration then throw (.bindingMismatch binding.binder.id)
  match node.form with
  | .reference _ (.local binder) =>
      if binder ≠ binding.binder.id then throw (.bindingMismatch binding.binder.id)
  | _ => throw (.bindingMismatch binding.binder.id)
  let owned ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
    | some owned => pure owned
    | none => throw (.plan (.unsupportedRequirements node.requirements))
  let raw := { node with type := node.rawType, requirements := owned, coercions := [] }
  let available ← (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
    |>.mapError Error.plan
  let (child, witnesses) ← (SourceCompilationPlan.localRequirementWitnesses contextual available
    (binding.binder.applySubstitution active) raw).mapError Error.plan
  let cumulative := child.compose active
  validateWitnesses program caller cumulative (inherited ++ witnesses)
  pure ⟨id, cumulative, witnesses, node, owned⟩

/-- Authenticate a policy's local occurrence before it reads callee metadata.
The current row must be the original contextual row or one of the two exact
normalized views used by the output-coercion traversal. Other rows are retained.
Repeated normalization and traversal of an already raw row preserve that view. -/
def normalizeOccurrence (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (binding : Binding) (parent : Option Prepared) (source : TypedSource) (id : ExpressionId) :
    Except Error TypedSource := do
  if source.owner ≠ binding.caller.declaration then throw (.originMismatch binding.caller)
  let reference ← authenticateReference program plan binding parent id
  let current ← match source.lookupExpression? id with
    | some node => pure node
    | none => throw (.missingExpression id)
  let normalized := reference.normalized
  let ordinary ← match SourceCompilationPlan.ordinaryOwnedRequirements? normalized with
    | some ordinary => pure ordinary
    | none => throw (.plan (.unsupportedRequirements normalized.requirements))
  let raw := { normalized with type := normalized.rawType, requirements := ordinary, coercions := [] }
  if current = reference.original then
    pure { source with nodes := source.nodes.map fun
      | .expression old => if old.id = id then .expression normalized else .expression old
      | .statement old => .statement old }
  else if current = normalized || current = raw then pure source
  else throw (.occurrenceMismatch id)

/-- Prepare a lambda child's exact caller ledger. A concrete original use site
authenticates its local dictionary; the full contextual key is checked before
any template row is replaced. Requirement IDs and unbound obligations survive. -/
def prepare (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (candidate : Instance) (parent : Option Prepared := none) : Except Error Prepared := do
  let origin := candidate.origin
  let binding : Binding := ⟨origin.caller, origin.source, origin.binder, origin.initializer, []⟩
  let caller ← exactCaller plan binding
  if origin.solvedRequirements != caller.function.solvedRequirements ||
      origin.parameterSubstitution ≠ caller.parameterSubstitution then throw (.originMismatch origin.caller)
  let discovered ← (SourceSpecializationWorklist.localLambdaInstances binding.source).mapError Error.discovery
  unless discovered.contains origin.localInstance do throw (.instanceMismatch binding.binder.id)
  let (active, inherited) ← activeContext caller parent
  let matching := binding.source.nodes.filterMap fun
    | .expression node@{ form := .reference _ (.local binder), .. } =>
        if binder = binding.binder.id then
          match SourceSpecialization.matchClosedSchemeInstance? (Scheme.apply active binding.binder.scheme)
            (active.apply node.rawType) with
          | some child => if child.compose active = origin.substitution then some node.id else none
          | none => none
        else none
    | _ => none
  let id ← match matching with
    | id :: _ => pure id
    | [] => throw (.missingReference binding.binder.id)
  let reference ← authenticateReference program plan binding parent id
  if reference.cumulative ≠ origin.substitution then throw (.instanceMismatch binding.binder.id)
  let witnesses := inherited ++ reference.witnesses
  validateWitnesses program caller origin.substitution witnesses
  pure ⟨candidate, contextualCaller caller origin.substitution witnesses, witnesses⟩

end Solcore.Frontend.SourceCoreLocalEvidence
