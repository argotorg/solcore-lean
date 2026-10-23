import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationOrigins
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationInputIdentities
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalOrigins

/-! Actual compiled rows supply the residual-scope validator receipt, including
method and late-added rows. Contextual sources retain the same original row and
the actual cumulative substitution; a header comparison is not used here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationResidualScopes
open Frontend SourceInference SourceSpecialization TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)

private theorem exact_member {plan : SourceSpecializationWorklist.Plan}
    {owner : SourceCompilationPlan.Key} {row : SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok row) :
    row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected
  · cases selected
  · next candidate only =>
    cases selected
    have member : row ∈ [row] := by simp
    rw [← only] at member
    exact (List.mem_filter.mp member).1
  · cases selected

/-- This consumes the actual full preparation result, rather than initial plan
membership, so implementation methods and later ordinary rows are included. -/
theorem row_supported (compiled : SourceCoreUnifiedCompilation.Compiled)
    {owner : SourceCompilationPlan.Key} {row : SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row) :
    ∀ node ∈ row.function.typedBody.nodes, ResidualNodeSupported row.function.typedBody node := by
  obtain ⟨signature, original, supplied, specialized⟩ :=
    CallablePreparedFinalSpecializationOrigins.of_default_preparation
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) row (exact_member selected)
  exact specializeFunction_residual_node_support specialized

structure ValidatedSource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : SourceCompilationPlan.Key) (active : Substitution) (source : TypedSource) where
  original : SpecializedFunction
  selected : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok original
  source_eq : source = original.function.typedBody.applySubstitution active
  supported : ∀ node ∈ original.function.typedBody.nodes,
    ResidualNodeSupported original.function.typedBody node

/-- The real original or contextual factory fixes the source row. -/
theorem of_receipt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {owner : SourceCompilationPlan.Key} {active : Substitution} {source : TypedSource}
    (receipt : LambdaSourceAlignment.SourceReceipt compiled.indexed.base.sourceProgram
      compiled.indexed.base.plan owner active source) :
    Nonempty (ValidatedSource compiled owner active source) := by
  cases receipt with
  | original selected =>
      exact ⟨⟨_, selected, (EmptySourceSubstitution.source _).symm, row_supported compiled selected⟩⟩
  | contextual accepted =>
      obtain ⟨row, selected, _, _, source⟩ := LambdaSourceAlignment.prepared_source accepted
      exact ⟨⟨row, selected, source, row_supported compiled selected⟩⟩

theorem invocation_source {compiled : SourceCoreUnifiedCompilation.Compiled}
    {relation : ActualBodyInvocation.BodyRelation}
    (index : ActualBodyInvocation.Index compiled relation) :
    Nonempty (ValidatedSource compiled index.owner index.active index.compilerSource) :=
  of_receipt index.compiler_source_receipt

/-- The accepted Packet and actual catalog binding identify the original
source whose node supports were checked. No candidate Source equality is an
independent premise. -/
theorem binding_supported {compiled : SourceCoreUnifiedCompilation.Compiled}
    {binding : SourceCoreLocalPolymorphism.Binding} {active : Substitution}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext active) :
    ∀ node ∈ binding.source.nodes, ResidualNodeSupported binding.source node := by
  obtain ⟨owner, source, _, _⟩ := SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨row, selected, original, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan, owner] at selected
  have supported := row_supported compiled selected
  rw [original, source] at supported
  exact supported

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationResidualScopes

/-! The runtime row uses the exact residual scope of each supplied path. -/
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationResidualScopes
open Frontend SourceInference SourceSpecialization TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)

theorem row_scope_unique (compiled : SourceCoreUnifiedCompilation.Compiled)
    {owner : SourceCompilationPlan.Key} {row : SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row)
    {node : NodeId} {left right : List TypeVarId}
    (first : ResidualScopePath row.function.typedBody node left)
    (second : ResidualScopePath row.function.typedBody node right) : left = right := by
  obtain ⟨signature, original, supplied, specialized⟩ :=
    CallablePreparedFinalSpecializationOrigins.of_default_preparation
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) row (exact_member selected)
  exact specializeFunction_residual_scope_unique specialized first second

theorem row_path_support (compiled : SourceCoreUnifiedCompilation.Compiled)
    {owner : SourceCompilationPlan.Key} {row : SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row)
    {node : Node} (member : node ∈ row.function.typedBody.nodes) {variables : List TypeVarId}
    (path : ResidualScopePath row.function.typedBody node.id variables) :
    (∀ type ∈ residualNodeTypes node, ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables) ∧
    (∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
      ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified) := by
  obtain ⟨signature, original, supplied, specialized⟩ :=
    CallablePreparedFinalSpecializationOrigins.of_default_preparation
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) row (exact_member selected)
  exact specializeFunction_residual_path_support specialized member path

theorem ValidatedSource.scope_unique {compiled : SourceCoreUnifiedCompilation.Compiled}
    {owner : SourceCompilationPlan.Key} {active : Substitution} {source : TypedSource}
    (validated : ValidatedSource compiled owner active source)
    {node : NodeId} {left right : List TypeVarId}
    (first : ResidualScopePath validated.original.function.typedBody node left)
    (second : ResidualScopePath validated.original.function.typedBody node right) : left = right :=
  row_scope_unique compiled validated.selected first second

theorem ValidatedSource.path_support {compiled : SourceCoreUnifiedCompilation.Compiled}
    {owner : SourceCompilationPlan.Key} {active : Substitution} {source : TypedSource}
    (validated : ValidatedSource compiled owner active source)
    {node : Node} (member : node ∈ validated.original.function.typedBody.nodes) {variables : List TypeVarId}
    (path : ResidualScopePath validated.original.function.typedBody node.id variables) :
    (∀ type ∈ residualNodeTypes node, ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables) ∧
    (∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
      ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified) :=
  row_path_support compiled validated.selected member path

/-- The stored bundle's actual catalog entry supplies the same original row;
no independent source equality or arbitrary scope agreement is needed. -/
theorem binding_scope_unique {compiled : SourceCoreUnifiedCompilation.Compiled}
    {binding : SourceCoreLocalPolymorphism.Binding} {active : Substitution}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext active)
    {node : NodeId} {left right : List TypeVarId}
    (first : ResidualScopePath binding.source node left)
    (second : ResidualScopePath binding.source node right) : left = right := by
  obtain ⟨owner, source, _, _⟩ := SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨row, selected, original, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan, owner] at selected
  have sameSource := original.trans source
  rw [← sameSource] at first second
  exact row_scope_unique compiled selected first second

theorem binding_path_support {compiled : SourceCoreUnifiedCompilation.Compiled}
    {binding : SourceCoreLocalPolymorphism.Binding} {active : Substitution}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext active)
    {node : Node} (present : node ∈ binding.source.nodes) {variables : List TypeVarId}
    (path : ResidualScopePath binding.source node.id variables) :
    (∀ type ∈ residualNodeTypes node, ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables) ∧
    (∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
      ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified) := by
  obtain ⟨owner, source, _, _⟩ := SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨row, selected, original, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan, owner] at selected
  have sameSource := original.trans source
  rw [← sameSource] at present path
  exact row_path_support compiled selected present path

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationResidualScopes
