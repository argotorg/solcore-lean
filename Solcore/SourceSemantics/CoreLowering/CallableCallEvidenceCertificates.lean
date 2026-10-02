import Solcore.SourceSemantics.CoreLowering.CallableCallRequirementLayouts
import Solcore.Frontend.SourceCoreEvidence

/-! Successful declaration branches of the actual evidence lowering retain
caller resolution, exact target selection and the complete authenticated
callee dictionary. Returning none only delegates ordinary lowering; indirect
local calls do not select a declaration through this interface. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCallEvidenceCertificates
open Core Frontend SourceInference
open CallableNamedMetadata (environment)
abbrev Context := SourceCoreFunctions.Context
abbrev Key := SourceCompilationPlan.Key
abbrev Specialized := SourceSpecialization.SpecializedFunction
abbrev RuntimeEvidence := SourceTypedRuntime.RuntimeEvidenceEnvironment

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem edge_target {plan : SourceCompilationPlan.Plan} {caller target selected : Key}
    {id : ExpressionId} {reference : Bool}
    (accepted : (if reference then SourceCompilationPlan.exactReferenceKey plan caller id target
      else SourceCompilationPlan.exactCallKey plan caller id target) = .ok selected) : selected = target := by
  cases reference <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
  all_goals
    first | unfold SourceCompilationPlan.exactCallKey at accepted
          | unfold SourceCompilationPlan.exactReferenceKey at accepted
    split at accepted
    · cases accepted
    · rename_i edge filtered
      cases accepted
      have member : edge ∈ [edge] := .head _
      rw [← filtered] at member
      have facts := (List.mem_filter.mp member).2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at facts
      exact facts.2
    · cases accepted

/-- Receipts for the real selected plan record and the exact ordered raw
result. Full metadata matching is derived from the two actual selectors. -/
structure Selection (program : CheckedProgram) (caller : Specialized) (compilation : Context)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) (reference : Bool) where private mk ::
  available : RuntimeEvidence
  actual : RuntimeEvidence
  target : Key
  key : Key
  specialized : Specialized
  coercionsValid : node.hasValidCoercionPath = true
  owner : caller.key = compilation.owner
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available
  materialized : (if reference then SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence caller node available instantiation
    else SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation) = .ok actual
  targetSelected : SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok target
  edge : (if reference then SourceCompilationPlan.exactReferenceKey compilation.plan compilation.owner node.id target
    else SourceCompilationPlan.exactCallKey compilation.plan compilation.owner node.id target) = .ok key
  selected : SourceCompilationPlan.exactSpecialization compilation.plan key = .ok specialized
  authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key specialized.assumptions actual = .ok ()

namespace Selection
variable {program : CheckedProgram} {caller : Specialized} {compilation : Context}
  {node : ExpressionNode} {instantiation : DeclarationInstantiation} {reference : Bool}

theorem key_eq (receipt : Selection program caller compilation node instantiation reference) : receipt.key = receipt.target :=
  edge_target receipt.edge

theorem metadata (receipt : Selection program caller compilation node instantiation reference) :
    CallableNamedMetadata.Matches receipt.specialized instantiation :=
  CallableNamedMetadata.matches_of_exact receipt.targetSelected (receipt.key_eq ▸ receipt.selected)

theorem authenticated_predicates (receipt : Selection program caller compilation node instantiation reference) :
    SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures receipt.key instantiation.predicates receipt.actual = .ok () := by
  rw [← receipt.metadata.predicates]
  exact receipt.authenticated

end Selection

/-- The source callee carries the complete same declaration instantiation,
including ordered predicates and parameter metadata. -/
theorem callee_metadata {source : TypedSource} {id callee : ExpressionId}
    {instantiation : DeclarationInstantiation}
    (accepted : SourceCompilationPlan.validateDirectDeclarationCallee source id callee instantiation = .ok ()) :
    ∃ node name, source.lookupExpression? callee = some node ∧
      node.form = .reference name (.declaration instantiation) ∧ node.type = instantiation.type := by
  unfold SourceCompilationPlan.validateDirectDeclarationCallee at accepted
  split at accepted
  · rename_i found
    split at accepted
    · rename_i matched
      simp only [Bool.and_eq_true, decide_eq_true_eq] at matched
      obtain ⟨rfl, same⟩ := matched
      exact ⟨_, _, found, rfl, same⟩
    · cases accepted
  · cases accepted

/-- Actual outer lowering supplies the previously independent resolver,
materializer and authenticator receipts. The raw call/callee metadata and
argument arity are obtained before any child compilation or output coercion. -/
theorem direct_of_accepted {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {caller : Specialized} {compilation : Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreEvidence.Scope} {id callee : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    {lowered : SourceCoreEvidence.Lowered}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program projectType caller compilation child fuel source scope id reasonAt callables = .ok (some lowered)) :
    ∃ receipt : Selection program caller compilation node instantiation false,
      SourceCompilationPlan.validateDirectDeclarationCallee source id callee instantiation = .ok () ∧
      arguments.length = receipt.specialized.function.typedBody.inputs.length := by
  unfold SourceCoreEvidence.lowerWithProjector at accepted
  simp only [found, form, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted
  · cases accepted
  · by_cases path : node.hasValidCoercionPath = true
    · by_cases owned : caller.key = compilation.owner
      · simp only [path, ↓reduceIte, owned, ne_eq, not_true_eq_false] at accepted
        obtain ⟨available, resolved, accepted⟩ := bind_ok accepted
        obtain ⟨validated, calleeAccepted, branch⟩ := bind_ok accepted
        obtain ⟨actual, materialized, branch⟩ := bind_ok branch
        obtain ⟨target, targeted, branch⟩ := bind_ok branch
        obtain ⟨key, edge, branch⟩ := bind_ok branch
        obtain ⟨specialized, selected, branch⟩ := bind_ok branch
        obtain ⟨authenticatedUnit, authenticated, branch⟩ := bind_ok branch
        split at branch
        · cases branch
        · rename_i arity
          let receipt : Selection program caller compilation node instantiation false := {
            available, actual, target, key, specialized
            coercionsValid := path
            owner := owned
            resolved := by simpa only [owned] using mapError_ok resolved
            materialized := mapError_ok materialized
            targetSelected := mapError_ok targeted
            edge := by simpa only [(lookupExpression?_sound found).2, Bool.false_eq_true, ↓reduceIte] using mapError_ok edge
            selected := mapError_ok selected
            authenticated := by cases authenticatedUnit; exact mapError_ok authenticated }
          exact ⟨receipt, by cases validated; exact mapError_ok calleeAccepted, by simpa using arity⟩
      · simp [owned, path] at accepted
    · simp [path] at accepted

/-- Standalone declaration references use their actual owned requirement
prefix and selected plan edge, even with retained output coercions. -/
theorem reference_of_accepted {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {caller : Specialized} {compilation : Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreEvidence.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {name : String} {instantiation : DeclarationInstantiation}
    {lowered : SourceCoreEvidence.Lowered}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program projectType caller compilation child fuel source scope id reasonAt callables = .ok (some lowered)) :
    Nonempty (Selection program caller compilation node instantiation true) := by
  unfold SourceCoreEvidence.lowerWithProjector at accepted
  simp only [found, form, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted
  · cases accepted
  · by_cases path : node.hasValidCoercionPath = true
    · by_cases owned : caller.key = compilation.owner
      · simp only [path, ↓reduceIte, owned, ne_eq, not_true_eq_false] at accepted
        obtain ⟨available, resolved, branch⟩ := bind_ok accepted
        obtain ⟨actual, materialized, branch⟩ := bind_ok branch
        obtain ⟨target, targeted, branch⟩ := bind_ok branch
        obtain ⟨key, edge, branch⟩ := bind_ok branch
        obtain ⟨specialized, selected, branch⟩ := bind_ok branch
        obtain ⟨authenticatedUnit, authenticated, _⟩ := bind_ok branch
        exact ⟨{
          available, actual, target, key, specialized
          coercionsValid := path
          owner := owned
          resolved := by simpa only [owned] using mapError_ok resolved
          materialized := mapError_ok materialized
          targetSelected := mapError_ok targeted
          edge := by simpa only [(lookupExpression?_sound found).2, ↓reduceIte] using mapError_ok edge
          selected := mapError_ok selected
          authenticated := by cases authenticatedUnit; exact mapError_ok authenticated }⟩
      · simp [owned, path] at accepted
    · simp [path] at accepted

namespace Selection
variable {program : CheckedProgram} {caller : Specialized} {compilation : Context}
  {node : ExpressionNode} {instantiation : DeclarationInstantiation} {context : SourceSemantics.Context}

/-- Source context alignment remains independent of native projection and of
the actual compiler's administrative environment. -/
theorem direct_produces (receipt : Selection program caller compilation node instantiation false)
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions) :
    Dynamic.DirectCallProducesEvidence context (environment receipt.available) node.requirements node.coercions
      instantiation.predicates (environment receipt.actual) :=
  CallableCallRequirementLayouts.direct_produces signatures ledger assumptions receipt.resolved receipt.materialized receipt.authenticated_predicates

theorem direct_agrees (receipt : Selection program caller compilation node instantiation false)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (singleton : CallableCallRequirementLayouts.Singletons caller context node)
    {semantic : Dynamic.EvidenceEnvironment}
    (independent : Dynamic.DirectCallProducesEvidence context (environment receipt.available) node.requirements node.coercions instantiation.predicates semantic) :
    semantic = environment receipt.actual :=
  CallableCallRequirementLayouts.direct_agrees ledger singleton receipt.materialized independent

theorem reference_produces (receipt : Selection program caller compilation node instantiation true)
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions) :
    ∃ ids, Dynamic.OrdinaryRequirementLayout node.requirements node.coercions ids ∧
      Dynamic.RequirementsProduceEnvironment context (environment receipt.available) ids instantiation.predicates (environment receipt.actual) :=
  CallableCallRequirementLayouts.reference_produces signatures ledger assumptions receipt.resolved receipt.materialized receipt.authenticated_predicates

theorem reference_agrees (receipt : Selection program caller compilation node instantiation true)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    {ids : List RequirementId} {semantic : Dynamic.EvidenceEnvironment}
    (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions ids)
    (independent : Dynamic.RequirementsProduceEnvironment context (environment receipt.available) ids instantiation.predicates semantic) :
    semantic = environment receipt.actual :=
  CallableCallRequirementLayouts.reference_agrees ledger receipt.materialized layout independent

end Selection

/-- The ordinary fast path returns before checking either the caller or the
callee. Its none result must not be used as a declaration-selection receipt. -/
theorem direct_bypass {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {caller : Specialized} {compilation : Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreEvidence.Scope} {id callee : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (assumptions : caller.assumptions = []) :
    SourceCoreEvidence.lowerWithProjector program projectType caller compilation child fuel source scope id reasonAt callables = .ok none := by
  simp [SourceCoreEvidence.lowerWithProjector, found, form, requirements, coercions, assumptions, bind, Except.bind, pure, Except.pure]

end Solcore.SourceSemantics.CoreLowering.CallableCallEvidenceCertificates
