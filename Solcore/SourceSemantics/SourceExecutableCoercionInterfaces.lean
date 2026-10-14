import Solcore.Frontend.SourceInference.Resolution

/-! Source checker soundness needs an executable named Coerce interface only
at retained coercion sites. Actual compiler receipts supply this predicate;
its definition does not depend on compiler or source body typing theorems. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.ExecutableCoercionInterfaces
open Frontend SourceInference TypeSystem

def indirectArgumentCoercions (node : ExpressionNode) : List CoercionStep :=
  match node.form with
  | .call _ _ (.indirect metadata) => metadata.argumentCoercions
  | _ => []

/-- The exact catalog entry selected by a retained primary requirement has
one executable named method. Generic parameter equations come from the
successful source checker, before rigid specialization. -/
def HasInterface (signatures : ProgramSignatures) (trait : ProgramTraitId) : Prop :=
  ∃ id signature method,
    trait = .declaration id ∧ signatures.trait? id = some signature ∧
    signature.name = "Coerce" ∧ signature.parameters.length = 2 ∧
    signature.methods.filter (fun candidate => candidate.name == "coerce") = [method]

/-- Every site retains its actual unique primary ledger row. Both output and
indirect argument coercions are included, across the complete node table. -/
def CoercionInterfaces (signatures : ProgramSignatures) (requirements : List SolvedRequirement)
    (source : TypedSource) : Prop :=
  ∀ node, .expression node ∈ source.nodes →
    ∀ step ∈ node.coercions ++ indirectArgumentCoercions node,
      ∃ solved,
        requirements.filter (fun row => decide (row.id = step.requirement)) = [solved] ∧
        HasInterface signatures solved.predicate.trait

/-- The dispatch name is attached to the actual operator syntax. Imports may
use aliases, so an environment-wide name equation does not express this fact. -/
def operatorDispatch (node : ExpressionNode) (name : String) : Prop :=
  match node.form with
  | .unary operator _ =>
      ∃ method, Detail.unaryOperatorDispatch operator = .traitMethod name method
  | .binary _ operator _ =>
      ∃ method, Detail.binaryOperatorDispatch operator = .traitMethod name method
  | _ => False

/-- Ordinary operator requirements precede the output coercion ledger. The
selected compiler verifies the declaration name at this exact primary row. -/
def OperatorInterfaces (signatures : ProgramSignatures) (requirements : List SolvedRequirement)
    (source : TypedSource) : Prop :=
  ∀ node, .expression node ∈ source.nodes →
    ∀ primary companions name,
      node.requirements = (primary :: companions) ++ node.coercions.flatMap CoercionStep.requirements →
      operatorDispatch node name →
      ∃ solved trait,
        requirements.filter (fun row => decide (row.id = primary)) = [solved] ∧
        solved.predicate.trait = .declaration trait ∧
        (signatures.trait? trait).map (·.name) = some name

/-- Executable interfaces for the actual selected source table. -/
structure SourceInterfaces (signatures : ProgramSignatures)
    (requirements : List SolvedRequirement) (source : TypedSource) : Prop where
  coercions : CoercionInterfaces signatures requirements source
  operators : OperatorInterfaces signatures requirements source

abbrev BodyInterfaces (signatures : ProgramSignatures) (function : CheckedFunction) : Prop :=
  SourceInterfaces signatures function.solvedRequirements function.typedBody

theorem HasInterface.traitName {signatures : ProgramSignatures} {trait : Resolved.DeclarationId}
    (supported : HasInterface signatures (.declaration trait)) :
    (signatures.trait? trait).map (·.name) = some "Coerce" := by
  obtain ⟨id, signature, method, identity, found, name, _, _⟩ := supported
  cases identity
  simp only [found, Option.map_some, name]

theorem HasInterface.profile {signatures : ProgramSignatures} {trait : Resolved.DeclarationId}
    (supported : HasInterface signatures (.declaration trait))
    {context : Frontend.SourceInference.Context} (same : context.signatures = signatures) :
    ∃ profile : Detail.CoercionMethodProfile,
      Detail.coercionMethodProfile? context trait = .ok (some profile) := by
  obtain ⟨id, signature, method, identity, found, _, arity, unique⟩ := supported
  cases identity
  simp only [Detail.coercionMethodProfile?, same, found, arity,
    ↓reduceIte, unique, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

/-- A caller uses the primary ledger row already retained by inference.
Singleton executable lookup identifies that same complete source record. -/
theorem SourceInterfaces.interface_at {signatures : ProgramSignatures}
    {requirements : List SolvedRequirement} {source : TypedSource}
    (supported : SourceInterfaces signatures requirements source)
    {node : ExpressionNode} (member : .expression node ∈ source.nodes)
    {step : CoercionStep} (site : step ∈ node.coercions ++ indirectArgumentCoercions node)
    {solved : SolvedRequirement} (solvedMember : solved ∈ requirements)
    (sameRequirement : solved.id = step.requirement) :
    HasInterface signatures solved.predicate.trait := by
  obtain ⟨actual, selected, interface⟩ := supported.coercions node member step site
  have present : solved ∈ requirements.filter
      (fun row => decide (row.id = step.requirement)) :=
    List.mem_filter.mpr ⟨solvedMember, by simpa only [decide_eq_true_eq] using sameRequirement⟩
  rw [selected] at present
  have identity : solved = actual := List.mem_singleton.mp present
  exact identity ▸ interface

theorem SourceInterfaces.profile_at {signatures : ProgramSignatures}
    {requirements : List SolvedRequirement} {source : TypedSource}
    (supported : SourceInterfaces signatures requirements source)
    {node : ExpressionNode} (member : .expression node ∈ source.nodes)
    {step : CoercionStep} (site : step ∈ node.coercions ++ indirectArgumentCoercions node)
    {solved : SolvedRequirement} (solvedMember : solved ∈ requirements)
    (sameRequirement : solved.id = step.requirement)
    {trait : Resolved.DeclarationId} (traitEq : solved.predicate.trait = .declaration trait)
    {context : Frontend.SourceInference.Context} (same : context.signatures = signatures) :
    ∃ profile : Detail.CoercionMethodProfile,
      Detail.coercionMethodProfile? context trait = .ok (some profile) := by
  have interface := supported.interface_at member site solvedMember sameRequirement
  rw [traitEq] at interface
  exact interface.profile same

end Solcore.SourceSemantics.ExecutableCoercionInterfaces
