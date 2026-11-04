import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalCatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads
import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativePreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativeFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerSlotForgetting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Builtins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.SelectedOperatorTypingCertificates
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodInstantiation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedConcreteRangeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Coercions
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceSelection
import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceShapeTable
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticProducers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicUnaryAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentProvenance
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection

/-!
# Selected compilations: method bodies

Scoped, terminal and whole-body bounds of method bodies, with method selection typing and ranges, closed coercion selection and the collectors of scoped method roots.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInterfaces
/-! Executable preparation authenticates the named Coerce interface at every
retained coercion site in each selected original source body. The source table
and complete rigid substitution remain explicit throughout the connection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInterfaces
open Frontend SourceInference TypeSystem
open ExecutableCoercionInterfaces
open CallableCoercionPreparation (argumentSteps Covered CoveredWith)
open CallableCoercionPreparationSteps (bind_ok)

private theorem require_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then action else .error error) = .ok value) :
    condition ∧ action = .ok value := by
  split at accepted
  · exact ⟨‹condition›, accepted⟩
  · cases accepted

theorem checkedCoercionMethod_interface
    {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method) :
    ∃ solved,
      caller.function.solvedRequirements.filter (fun row => decide (row.id = step.requirement)) = [solved] ∧
      HasInterface program.signatures solved.predicate.trait := by
  simp only [SourceCompilationPlan.checkedCoercionMethod, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  obtain ⟨solved, picked, accepted⟩ := bind_ok accepted
  have selected : caller.function.solvedRequirements.filter
      (fun row => decide (row.id = step.requirement)) = [solved] := by
    change (match caller.function.solvedRequirements.filter (fun row => decide (row.id = step.requirement)) with
      | [] => .error (.missingSolvedRequirement caller.key node.id step.requirement)
      | [row] => .ok row
      | rows => .error (.duplicateSolvedRequirements caller.key node.id step.requirement rows.length) :
      Except SourceTypedRuntime.RuntimeError SolvedRequirement) = .ok solved at picked
    cases filtered : caller.function.solvedRequirements.filter (fun row => decide (row.id = step.requirement)) with
    | nil => simp [filtered] at picked
    | cons row rest =>
      cases rest with
      | nil => simp only [filtered, Except.ok.injEq] at picked; subst solved; rfl
      | cons other rest => simp [filtered] at picked
  obtain ⟨_, accepted⟩ := require_ok accepted
  split at accepted <;> try contradiction
  rename_i traitId goalTrait
  split at accepted <;> try contradiction
  rename_i trait found
  obtain ⟨guard, accepted⟩ := require_ok accepted
  have guards : trait.name = "Coerce" ∧ trait.parameters.length = 2 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using guard
  split at accepted <;> try contradiction
  rename_i traitMethod single
  exact ⟨solved, selected, traitId, trait, traitMethod, goalTrait, found,
    guards.1, guards.2, single⟩

theorem coercions_of_covered {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction} {plan : SourceSpecializationWorklist.Plan}
    (covered : Covered program caller plan) :
    CoercionInterfaces program.signatures caller.function.solvedRequirements caller.function.typedBody := by
  obtain ⟨available, resolved, covered⟩ := covered
  intro node member step site
  obtain ⟨visit⟩ := covered node member step site
  exact checkedCoercionMethod_interface visit.selected

theorem of_covered {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction} {plan : SourceSpecializationWorklist.Plan}
    (covered : CoveredWith program caller plan) : BodyInterfaces program.signatures caller.function :=
  ⟨coercions_of_covered covered.coercions, SelectedCompilationOperatorInterfaces.of_covered covered⟩

theorem argumentSteps_apply (substitution : ParameterSubstitution) (node : ExpressionNode) :
    argumentSteps (SourceSpecialization.applyExpressionNode substitution node) =
      (argumentSteps node).map (SourceSpecialization.applyCoercionStep substitution) := by
  cases form : node.form <;>
    simp only [SourceSpecialization.applyExpressionNode, SourceSpecialization.applyExpressionForm,
      form, argumentSteps, List.map_nil]
  case call callee arguments resolution =>
    cases resolution <;> rfl

private theorem filter_applied (substitution : ParameterSubstitution)
    (requirements : List SolvedRequirement) (id : RequirementId) :
    (requirements.map (SourceSpecialization.applySolvedRequirement substitution)).filter
        (fun row => decide (row.id = id)) =
      (requirements.filter (fun row => decide (row.id = id))).map
        (SourceSpecialization.applySolvedRequirement substitution) := by
  induction requirements with
  | nil => rfl
  | cons first rest ih =>
    by_cases same : first.id = id <;>
      simp [same, SourceSpecialization.applySolvedRequirement, ih]

private theorem map_singleton {α β : Type} {f : α → β} {items : List α} {value : β}
    (same : items.map f = [value]) : ∃ item, items = [item] ∧ f item = value := by
  cases items with
  | nil => cases same
  | cons item rest =>
    cases rest with
    | nil => exact ⟨item, rfl, (List.cons.inj same).1⟩
    | cons next tail => cases same

/-- Interface presence transfers to the complete original body without
inverting any rigid type substitution. Every original requirement identity
and both ordered coercion lists are retained by specialization. -/
theorem of_applied {signatures : ProgramSignatures} {function : CheckedFunction}
    {substitution : ParameterSubstitution}
    (supported : BodyInterfaces signatures (SourceSpecialization.applyCheckedFunction substitution function)) :
    BodyInterfaces signatures function := by
  constructor
  · intro node member step site
    have nodeMember : .expression (SourceSpecialization.applyExpressionNode substitution node) ∈
        (SourceSpecialization.applyCheckedFunction substitution function).typedBody.nodes :=
      List.mem_map.mpr ⟨.expression node, member, rfl⟩
    have stepMember : SourceSpecialization.applyCoercionStep substitution step ∈
        (SourceSpecialization.applyExpressionNode substitution node).coercions ++
          argumentSteps (SourceSpecialization.applyExpressionNode substitution node) := by
      rw [argumentSteps_apply]
      change SourceSpecialization.applyCoercionStep substitution step ∈
        node.coercions.map (SourceSpecialization.applyCoercionStep substitution) ++ _
      rw [← List.map_append]
      exact List.mem_map.mpr ⟨step, site, rfl⟩
    obtain ⟨actual, selected, supported⟩ := supported.coercions _ nodeMember _ stepMember
    change (function.solvedRequirements.map (SourceSpecialization.applySolvedRequirement substitution)).filter
      (fun row => decide (row.id = step.requirement)) = [actual] at selected
    rw [filter_applied] at selected
    obtain ⟨original, singleton, applied⟩ := map_singleton selected
    refine ⟨original, singleton, ?_⟩
    rw [← applied] at supported
    exact supported
  · exact SelectedCompilationOperatorInterfaces.of_applied supported.operators

theorem of_specialization {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction} {plan : SourceSpecializationWorklist.Plan}
    {signature : ProgramFunctionSignature} {original : CheckedFunction} {supplied : ParameterSubstitution}
    (accepted : SourceSpecialization.specializeFunction signature original supplied = .ok caller)
    (covered : CoveredWith program caller plan) : BodyInterfaces program.signatures original := by
  apply of_applied (substitution := caller.parameterSubstitution)
  rw [← (CallableCoercionBodyProvenance.specialization_fields accepted).1]
  exact of_covered covered

/-- Original bodies are ordinary declarations or retained implementation
methods. Methods keep their own checker carrier and are never recategorized
as ordinary functions by a matching owner or specialization key. -/
def OriginalMember (program : CheckedProgram) (function : CheckedFunction) : Prop :=
  function ∈ program.functions ∨ ∃ method ∈ program.methods, function = method.checked

theorem original_of_catalogOrigin {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction} {plan : SourceSpecializationWorklist.Plan}
    (checked : CallableMethodBodyCoherence.Checked program)
    (origin : CallablePreparedFinalCatalogOrigins.CatalogOrigin program caller)
    (covered : CoveredWith program caller plan) :
    ∃ original, OriginalMember program original ∧
      caller.function = SourceSpecialization.applyCheckedFunction caller.parameterSubstitution original ∧
      BodyInterfaces program.signatures original := by
  cases origin with
  | ordinary origin =>
    obtain ⟨request, signature, original, _, member, _, specialized⟩ := origin
    exact ⟨original, Or.inl member,
      (CallableCoercionBodyProvenance.specialization_fields specialized).1,
      of_specialization specialized covered⟩
  | method selected =>
    obtain ⟨retained, member, _, identical⟩ := selected.retained checked
    exact ⟨selected.generic, Or.inr ⟨retained, member, identical⟩,
      (CallableCoercionBodyProvenance.specialization_fields selected.specialized).1,
      of_specialization selected.specialized covered⟩

/-- Every actual cached function belongs to the completed executable plan,
including ordinary helpers and methods discovered during its traversal. -/
theorem cached (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    BodyInterfaces compiled.sourceProgram.signatures named.specialized.function := by
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled
  have member := RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected rfl
  exact of_covered ((CallableCoercionPreparation.of_accepted_with prepared).2 named.specialized member)

/-- The actual cache position and preparation receipt supply the complete
original checker carrier and all executable coercion interfaces. Nested
lambda bodies are included because preparation visits the full node table. -/
theorem cached_original (compiled : SourceCoreUnifiedCompilation.Compiled)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    ∃ original, OriginalMember compiled.sourceProgram original ∧
      named.specialized.function =
        SourceSpecialization.applyCheckedFunction named.specialized.parameterSubstitution original ∧
      BodyInterfaces compiled.sourceProgram.signatures original := by
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled
  have member := RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected rfl
  exact original_of_catalogOrigin checked
    (CallablePreparedFinalCatalogOrigins.of_default_preparation prepared named.specialized member)
    ((CallableCoercionPreparation.of_accepted_with prepared).2 named.specialized member)

theorem checked_cached_original {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    (checked : Frontend.checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    ∃ original, OriginalMember compiled.sourceProgram original ∧
      named.specialized.function =
        SourceSpecialization.applyCheckedFunction named.specialized.parameterSubstitution original ∧
      BodyInterfaces compiled.sourceProgram.signatures original :=
  cached_original compiled (CallableMethodBodyCoherence.of_checked checked) selected

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInterfaces
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPostAdmission
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPostAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

theorem preserved {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt)
    {before after : Dynamic.Heap} {value : Dynamic.Value}
    (typed : Dynamic.ValueHasType sourceAt.context after value principal.sourceBody.resultType)
    (heap : Dynamic.HeapWellTyped sourceAt.context after)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    Dynamic.ExpressionEvaluationPreserved principal.sourceBody.context before after value principal.sourceBody.resultType := by
  obtain ⟨_, certificate⟩ := certified
  have runtime := certificate.sourceRuntimeValid
  have fields := RecursiveNamedInitialContextValidity.mono_fields sourceAt.extended
  have supports : Dynamic.TypeContextSupports sourceAt.context principal.sourceBody.context :=
    Dynamic.TypeContextSupports.ofClosed fields.signatures.symm
      (fields.targetClosed runtime.closed) runtime.closed sourceAt.closed runtime.residual_variables_open
  exact ⟨typed.transportContext supports, heap.transportContext supports, metadata⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPostAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedSupport
/-! Scoped method packets retain the actual selected implementation, complete
Source dictionary, parameter context and accepted flow. Reached children keep
their original lexical fields and mixed expression roots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallablePreparedMethodRuntimeProfileFactory (SourceAt policy scope)
open CompatibleEncoding (bind_ok)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : Principal compiled method)

abbrev parameterScope : SourceCoreLocalCell.Scope := scope (named := principal.named)

def nativePrefix : Core.Context :=
  principal.named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
    [.cell compiled.indexed.ancestry.layout.frame.type]

structure Packet where
  sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
    principal.sourceBody principal.dictionary
  flow : Expr
  accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy principal.cached.compilation)
    compiled.indexed.fuel principal.sourceBody.source (parameterScope principal)
    principal.cached.compilation.statements principal.named.signature.resultType
    (principal.cached.diagnostics.reasonAt principal.named.signature.key) true
    principal.cached.compilation.own.table.escapedReason = .ok flow
  emitted : principal.cached.compilation.body = CompatibleStatements.finish
    principal.named.signature.resultType flow principal.cached.compilation.own.fellThroughReason
    principal.cached.compilation.own.table.escapedReason
  shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape principal.sourceBody.source true
    principal.cached.compilation.statements

/-- The real accepted method body determines its flow without any execution premise. -/
theorem of_accepted
    (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
      principal.sourceBody principal.dictionary)
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape principal.sourceBody.source true
      principal.cached.compilation.statements) : Nonempty (Packet principal) := by
  have accepted := sourceAt.accepted principal.cached.compilation
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  exact ⟨⟨sourceAt, flow, generated, (Except.ok.inj returned).symm, shape⟩⟩

theorem statements (packet : Packet principal)
    (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt) :
    ∃ final facts, StatementsHaveType principal.sourceBody.source {returnType := principal.sourceBody.resultType}
      packet.sourceAt.context principal.cached.compilation.statements final facts ∧
      BodyCompletes principal.sourceBody.resultType facts := by
  obtain ⟨facts, typed⟩ := SelectedCompilationMethodBodySupport.source_typing
    principal packet.sourceAt certified
  obtain ⟨final, body, _roots, complete⟩ := typed.typing.body_typed
  refine ⟨final, facts, ?_, complete⟩
  have roots : (principal.sourceBody.source.roots.filterMap fun root => match root with
      | .statement statement => some statement | .expression _ => none) = principal.cached.compilation.statements :=
    principal.source_frame.roots.filterMap_eq
  exact roots ▸ body

theorem runtime (packet : Packet principal)
    (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      packet.sourceAt.context principal.sourceBody.source := by
  obtain ⟨_facts, typed⟩ := SelectedCompilationMethodBodySupport.source_typing
    principal packet.sourceAt certified
  exact typed.sourceRuntimeValid.transport (RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended)

abbrev Certificate
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ root : SelectedCompilationMixedRootSupport.RootAt compiled headers stages
      context invocation scope id lowered semanticFaults,
    root.compilation.administrativePrefix = 1

structure Support (packet : Packet principal)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep) : Prop where
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    principal.sourceBody.source (fun site root => principal.cached.diagnostics.placeReason principal.named.signature.key site root none) (fun site root raw => principal.cached.diagnostics.placeReason principal.named.signature.key site root (some raw)))
  tree : ∀ child, stages.Closure principal.sourceFunction child →
    ∃ expressionSyntax : ExpressionId → Prop,
      CallableIndexedOwnedPreparedBranchingCatalogSites.Collected (fun site root => principal.cached.diagnostics.placeReason principal.named.signature.key site root none)
        (fun site root raw => principal.cached.diagnostics.placeReason principal.named.signature.key site root (some raw)) (faults := semanticFaults) compiled.indexed.layouts
        principal.named.signature.key [] compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
        (fun error => .sourceAllocation (reprStr error)) (.initial compiled.compatible.checked)
        child.source expressionSyntax
        (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate child.source
          (fun context => Certificate headers stages semanticFaults context child))
        compiled.indexed.layouts.definitions (nativePrefix principal)
        packet.sourceAt.context (parameterScope principal) (.statements true principal.cached.compilation.statements)
        principal.sourceBody.resultType principal.named.signature.resultType packet.flow

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodies
/-! Both method body forms retain their actual compiler packet and SourceAt.
The alternatives contain static receipts only. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedMethodPrincipal (Principal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}

inductive Packet (principal : Principal compiled method) where
  | terminal : SelectedCompilationMethodBodySupport.Packet principal → Packet principal
  | scoped : SelectedCompilationMethodScopedSupport.Packet principal → Packet principal

def Packet.sourceAt {principal : Principal compiled method} (packet : Packet principal) :
    CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary :=
  match packet with
  | .terminal packet => packet.sourceAt
  | .scoped packet => packet.sourceAt

def Support (principal : Principal compiled method) (packet : Packet principal)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep) : Prop :=
  match packet with
  | .terminal packet => SelectedCompilationMethodBodySupport.Support
      principal packet headers stages semanticFaults
  | .scoped packet => SelectedCompilationMethodScopedSupport.Support
      principal packet headers stages semanticFaults

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedBounds
/-! The actual installed method and marked parameter entry supply admission,
physical cache slots and the frame used by the existing scoped flow engine.
Every reached expression is discharged by the strict mixed root family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationMethodScopedSupport (Packet Support parameterScope nativePrefix)
open SelectedCompilationMixedRootBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open SelectedCompilationMethodInvocationBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (support : Support principal packet headers stages semanticFaults)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (functionTypes : FunctionRuntimeViews functions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {registry : SourceCoreRawMetadata.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure principal.sourceFunction child)
  {administrative : Core.Context} {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : CallablePreparedMethodRuntimeMeaning.Installed principal.cached.compilation
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := principal.sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments packet.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)


variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled registry
    (fun reason token => faults (.semantic reason) token))

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "bodyBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)

include certified beforeTyped argumentsTyped in
private theorem heap_at_parameters {environment : Dynamic.Environment} {after : Dynamic.Heap}
    (allocation : Dynamic.BindersAllocate [] before principal.sourceFunction.parameters arguments environment after) :
    Dynamic.HeapWellTyped packet.sourceAt.context after := by
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq packet.sourceAt.extended
  have rawArguments : Dynamic.ValuesHaveTypes principal.sourceBody.context before arguments
      (principal.sourceBody.source.inputs.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes, principal.source_frame.context] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping
    (principal.source_frame.context ▸ beforeTyped) rawArguments (principal.source_frame.parameters ▸ allocation)
  obtain ⟨_, typed⟩ := SelectedCompilationMethodBodySupport.source_typing principal packet.sourceAt certified
  have runtime := typed.sourceRuntimeValid
  have fields := RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended
  exact allocated.transportClosed fields.signatures runtime.closed (fields.targetClosed runtime.closed)
    runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)

include packet in
private theorem prefix_agrees
    {localScope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {map : LocationMap} {typing : StoreTyping} {environment : Dynamic.Environment}
    {administrative : Core.Context} {location : Location}
    (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 localScope canonical)
    (reference : canonical[localScope.length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      map typing (SourceCoreCompatibleCatalog.packTypes (principal.named.inputs.map Prod.snd) :: administrative)
      localScope environment canonical compiled.indexed.layouts.definitions) :
    NativeExpressionContextSupport.Agrees (nativePrefix principal).length (nativePrefix principal)
      (SourceCoreCompatibleCatalog.packTypes (principal.named.inputs.map Prod.snd) :: administrative) := by
  have typed := related.runtime_hasTypes.type_tags
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (SourceCoreLocalCell.coreContext localScope ++
        SourceCoreCompatibleCatalog.packTypes (principal.named.inputs.map Prod.snd) :: administrative)[index]? = some value.type := by
    rw [← typed]
    simp [found]
  intro index smaller
  cases index with
  | zero => simp [nativePrefix, packet.sourceAt.parameterType]
  | succ slot =>
    have bound : slot < compiled.indexed.base.globals.length + 1 := by
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil] at smaller
      omega
    by_cases globalSlot : slot < compiled.indexed.base.globals.length
    · let signature := compiled.indexed.base.globals[slot]
      have selected : compiled.indexed.base.globals[slot]? = some signature :=
        List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
      have atType := tag (slots slot signature selected)
      have outside : ¬ localScope.length + 1 + slot < localScope.length := by omega
      have offset : localScope.length + 1 + slot - localScope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        globalSlot, selected, signature, SourceCoreCalls.Signature.referenceType,
        OptionalCell.referenceType, Value.type] using atType
    · have last : slot = compiled.indexed.base.globals.length := by omega
      have atType := tag reference
      have outside : ¬ localScope.length + 1 + compiled.indexed.base.globals.length < localScope.length := by omega
      have offset : localScope.length + 1 + compiled.indexed.base.globals.length - localScope.length =
          compiled.indexed.base.globals.length + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        last, Value.type] using atType

include support certified selected keyPhysical beforeTyped argumentsTyped stable semantic faithful observations assignmentInterpretation in
/-- Actual parameter allocation supplies the entire Source body entry. -/
theorem source_continuation
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    SourceContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata _owned history _emitted entry _added _length _spine reached _related physical slots
  intro size finalContext bodyOutcome outcome after trace matched within
  have prefixAgreement := prefix_agrees principal packet slots entry.reference entry.environments
  have environments := RecursiveNamedLambdaFormationHeads.environments_prefix entry.environments (nativePrefix principal) prefixAgreement
  have agrees : EnvironmentsAgree entry.embedding
      (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)) entry.actualBody :=
    RecursiveNamedLambdaFormationHeads.agrees_prefix entry.lookups
    ((parameterScope principal).length + (nativePrefix principal).length)
  have retainedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 (parameterScope principal)
      (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)) := by
    intro slot signature found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [List.getElem?_take, if_pos]
    · exact slots slot signature found
    · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
  have reference : (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length))[
      (parameterScope principal).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [List.getElem?_take, if_pos]
    · exact entry.reference
    · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨parameterScope principal, entry.mapping, entry.world, entry.heap, entry.store,
        entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)⟩ :=
    ⟨⟨reached, retainedSlots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet certified beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨staticFinal, facts, bodyTyped, _completes⟩ :=
    SelectedCompilationMethodScopedSupport.statements principal packet certified
  rw [← sourceEq] at bodyTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source packet.sourceAt.context
      principal.cached.compilation.statements := ⟨_, _, _, bodyTyped⟩
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ packet.sourceAt.unique
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true
      principal.cached.compilation.statements := sourceEq ▸ packet.shape
  obtain ⟨expressionSyntax, collected⟩ := support.tree child selected
  obtain ⟨assignmentAuthority⟩ := support.assignmentAuthority
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready
      (values := .initial compiled.compatible.checked) functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
      principal.sourceBody.source (fun site root => principal.cached.diagnostics.placeReason principal.named.signature.key site root none)
      (fun site root raw => principal.cached.diagnostics.placeReason principal.named.signature.key site root (some raw)) registry
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
  rw [← sourceEq] at assignmentDiagnostics
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history
  obtain ⟨flowValue, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativePreservation.preserves_at
      bodyBridge (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1)
      functions faithful observations extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model 1)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner (headers := headers) model 1 stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages child
            (Point scope id lowered) faults size := children size smaller root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      unique collected.tree (collected.sites registry) semantic assignmentDiagnostics rfl shape originalTyping packet.sourceAt.projection
      (Nat.le_of_lt within) environments entry.heaps entry.locals agrees entry.actualTyped reference entry.read entry.unmapped
      initial conditioned admitted trace
  have functionPost := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    unique bodyTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function packet.sourceAt.projection represented controlClosed
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated
      principal.cached.compilation.own.fellThroughReason principal.cached.compilation.own.table.escapedReason entry.embedding
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, bodyStore, finalMap, finalWorld, ?_, representedBody, heaps,
    maps, worlds, frame, metadata, ⟨returned.base.val, related⟩, ?_⟩
  · simpa only [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody
  · intro value same
    rw [same] at functionPost
    have postTyped := functionPost.at_value
    exact SelectedCompilationMethodPostAdmission.preserved principal packet.sourceAt certified
      postTyped.1 postTyped.2.heap metadata

include support certified selected keyPhysical beforeTyped argumentsTyped stable semantic functionTypes faithful observations assignmentInterpretation in
/-- Native completion is inverted through the same real flow and footer. -/
theorem native_continuation
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    NativeContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata prefixSize bodyStore _owned history _prefixWithin value finalStore _restored
    entry _added _length _spine reached _related physical slots within
  have prefixAgreement := prefix_agrees principal packet slots entry.reference entry.environments
  have environments := RecursiveNamedLambdaFormationHeads.environments_prefix entry.environments (nativePrefix principal) prefixAgreement
  have agrees : EnvironmentsAgree entry.embedding
      (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)) entry.actualBody :=
    RecursiveNamedLambdaFormationHeads.agrees_prefix entry.lookups
    ((parameterScope principal).length + (nativePrefix principal).length)
  have retainedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 (parameterScope principal)
      (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)) := by
    intro slot signature found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [List.getElem?_take, if_pos]
    · exact slots slot signature found
    · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
  have reference : (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length))[
      (parameterScope principal).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [List.getElem?_take, if_pos]
    · exact entry.reference
    · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨parameterScope principal, entry.mapping, entry.world, entry.heap, entry.store,
        entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)⟩ :=
    ⟨⟨reached, retainedSlots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet certified beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨staticFinal, facts, bodyTyped, _completes⟩ :=
    SelectedCompilationMethodScopedSupport.statements principal packet certified
  rw [← sourceEq] at bodyTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source packet.sourceAt.context
      principal.cached.compilation.statements := ⟨_, _, _, bodyTyped⟩
  have graph : OccurrenceGraphWellFormed child.source :=
    sourceEq ▸ (SelectedCompilationMethodScopedSupport.runtime principal packet certified).graph
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true
      principal.cached.compilation.statements := sourceEq ▸ packet.shape
  obtain ⟨expressionSyntax, collected⟩ := support.tree child selected
  obtain ⟨assignmentAuthority⟩ := support.assignmentAuthority
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready
      (values := .initial compiled.compatible.checked) functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
      principal.sourceBody.source (fun site root => principal.cached.diagnostics.placeReason principal.named.signature.key site root none)
      (fun site root raw => principal.cached.diagnostics.placeReason principal.named.signature.key site root (some raw)) registry
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
  rw [← sourceEq] at assignmentDiagnostics
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history
  have bodyTrace := entry.completed
  simp only [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace (Nat.le_of_lt within)
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativeFlow.reflects_at
      bodyBridge (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1)
      functions functionTypes faithful observations extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model 1)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner (headers := headers) model 1 stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages child
            (Point scope id lowered) faults size := children size smaller root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      graph collected.tree (collected.sites registry) semantic assignmentDiagnostics rfl shape originalTyping packet.sourceAt.projection
      (Nat.le_of_lt strict) environments entry.heaps entry.locals agrees entry.actualTyped reference entry.read entry.unmapped
      initial conditioned admitted flowTrace
  have functionPost := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    graph.nodeOccurrencesUnique bodyTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function packet.sourceAt.projection represented controlClosed
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound
      principal.cached.compilation.own.fellThroughReason principal.cached.compilation.own.table.escapedReason entry.embedding
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  refine ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld, trace,
    represented.body_result, representedBody, heaps, maps, worlds, frame, metadata, ⟨returned.base.val, related⟩, ?_⟩
  intro value same
  rw [same] at functionPost
  have postTyped := functionPost.at_value
  exact SelectedCompilationMethodPostAdmission.preserved principal packet.sourceAt certified
    postTyped.1 postTyped.2.heap metadata

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodTerminalBounds
/-! The genuine method parameter entry supplies admission and the complete
physical cache. Strict expression induction closes the actual terminal body;
the static support carries neither body execution nor a semantic callback. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodTerminalBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationMethodBodySupport (Packet Support)
open SelectedCompilationMethodRootBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open SelectedCompilationMethodInvocationBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (support : Support principal packet headers stages semanticFaults)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure principal.sourceFunction child)
  {administrative : Core.Context} {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : CallablePreparedMethodRuntimeMeaning.Installed principal.cached.compilation
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := principal.sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments packet.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "bodyBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)
local notation "point" => Point (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named)) packet.expression packet.receipt.child

include certified beforeTyped argumentsTyped in
private theorem heap_at_parameters {environment : Dynamic.Environment} {after : Dynamic.Heap}
    (allocation : Dynamic.BindersAllocate [] before principal.sourceFunction.parameters arguments environment after) :
    Dynamic.HeapWellTyped packet.sourceAt.context after := by
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq packet.sourceAt.extended
  have rawArguments : Dynamic.ValuesHaveTypes principal.sourceBody.context before arguments
      (principal.sourceBody.source.inputs.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes, principal.source_frame.context] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping
    (principal.source_frame.context ▸ beforeTyped) rawArguments (principal.source_frame.parameters ▸ allocation)
  obtain ⟨_, typed⟩ := SelectedCompilationMethodBodySupport.source_typing principal packet.sourceAt certified
  have runtime := typed.sourceRuntimeValid
  have fields := RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended
  exact allocated.transportClosed fields.signatures runtime.closed (fields.targetClosed runtime.closed)
    runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)

include support selected keyPhysical in
private theorem preserves_children (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow bodyBridge packet.sourceAt.context
      model stages child point faults budget := by
  obtain ⟨root⟩ := support.roots child selected
  intro size within
  have bound : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots packet.sourceAt.context model stages child point faults size :=
    children size within root.toRootAt owner keyPhysical
  rw [root.prefixLength] at bound
  intro current id code
  exact bound

include support selected keyPhysical in
private theorem reflects_children (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow bodyBridge packet.sourceAt.context
      model stages child point faults budget := by
  obtain ⟨root⟩ := support.roots child selected
  intro size within
  have bound : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots packet.sourceAt.context model stages child point faults size :=
    children size within root.toRootAt owner keyPhysical
  rw [root.prefixLength] at bound
  intro current id code
  exact bound

include support certified selected keyPhysical beforeTyped argumentsTyped stable in
/-- The genuine installed frame and marked allocation establish every body
admission field before the strict expression law is used. -/
theorem source_continuation (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    SourceContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata _owned history _emitted entry _added _length _spine reached _related physical slots
  intro size finalContext bodyOutcome outcome after trace matched within
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨_, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := ⟨⟨reached, slots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet certified beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  have view : LambdaMetadataViews.MetadataView child.source principal.sourceBody.source := sourceEq ▸ .refl _
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    SelectedCompilationMethodBodySupport.statements principal packet certified
  rw [← sourceEq] at bodyTyped
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ packet.sourceAt.unique
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
      frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.preserves_body
      (receipt := packet.receipt) (view := view) (bridge := bodyBridge)
      (bodyTyped := bodyTyped) (complete := completes) (certifies := fun lowered accepted =>
        show point _ _ lowered from ⟨rfl, rfl, Except.ok.inj (accepted.symm.trans packet.receipt.generated)⟩)
      (environments := entry.environments) (heaps := entry.heaps) (locals := entry.locals)
      (agrees := entry.lookups) (typed := entry.actualTyped) (initial := initial) (admitted := admitted)
      unique budget (preserves_children principal packet support functions selected owner keyPhysical budget children)
      trace matched (Nat.le_of_lt within)
  refine ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, ⟨returned.base.val, related⟩, ?_⟩
  intro value same
  cases same
  exact SelectedCompilationMethodPostAdmission.preserved principal packet.sourceAt certified
    post.at_value.1 post.at_value.2.heap metadata

include support certified selected keyPhysical beforeTyped argumentsTyped stable in
/-- Reflection uses the measured native body grade and constructs an
independently sized original Source body at the same reached entry. -/
theorem native_continuation (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    NativeContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata prefixSize bodyStore _owned history _prefixWithin value finalStore _restored
    entry _added _length _spine reached _related physical slots within
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨_, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := ⟨⟨reached, slots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet certified beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  have view : LambdaMetadataViews.MetadataView child.source principal.sourceBody.source := sourceEq ▸ .refl _
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    SelectedCompilationMethodBodySupport.statements principal packet certified
  rw [← sourceEq] at bodyTyped
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ packet.sourceAt.unique
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, result, heaps, maps, worlds,
      frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.reflects_body
      (receipt := packet.receipt) (view := view) (bridge := bodyBridge)
      (bodyTyped := bodyTyped) (complete := completes) (certifies := fun lowered accepted =>
        show point _ _ lowered from ⟨rfl, rfl, Except.ok.inj (accepted.symm.trans packet.receipt.generated)⟩)
      (environments := entry.environments) (heaps := entry.heaps) (locals := entry.locals)
      (agrees := entry.lookups) (typed := entry.actualTyped) (initial := initial) (admitted := admitted)
      unique budget (reflects_children principal packet support functions selected owner keyPhysical budget children)
      entry.completed (Nat.le_of_lt within)
  refine ⟨sourceSize, packet.sourceAt.context, CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome,
    outcome, after, finalMap, finalWorld, trace, matched, result, heaps, maps, worlds,
    frame, metadata, ⟨returned.base.val, related⟩, ?_⟩
  intro value same
  cases same
  exact SelectedCompilationMethodPostAdmission.preserved principal packet.sourceAt certified
    post.at_value.1 post.at_value.2.heap metadata

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodTerminalBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodyBounds
/-! Static method packet dispatch preserves the same genuine parameter entry
and current physical authority in either body form. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open SelectedCompilationMethodBodies (Packet Support)
open SelectedCompilationMixedRootBounds
open SelectedCompilationMethodInvocationBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (support : Support principal packet headers stages semanticFaults)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (functionTypes : FunctionRuntimeViews functions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {registry : SourceCoreRawMetadata.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure principal.sourceFunction child)
  {administrative : Core.Context} {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : CallablePreparedMethodRuntimeMeaning.Installed principal.cached.compilation
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := principal.sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments packet.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)


variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled registry
    (fun reason token => faults (.semantic reason) token))

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
include support certified selected keyPhysical beforeTyped argumentsTyped stable semantic faithful observations assignmentInterpretation in
theorem source_continuation
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    SourceContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  cases packet with
  | terminal packet =>
    exact SelectedCompilationMethodTerminalBounds.source_continuation
      principal packet support certified functions selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable budget
      (fun size smaller _context _invocation _scope _expression _lowered root owner physical =>
        children size smaller
          (SelectedCompilationMixedRootSupport.RootAt.ofMethod root) owner physical)
  | «scoped» packet =>
    exact SelectedCompilationMethodScopedBounds.source_continuation (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      principal packet support certified functions faithful observations selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable extension budget children

include support certified selected keyPhysical beforeTyped argumentsTyped stable semantic functionTypes faithful observations assignmentInterpretation in
theorem native_continuation
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    NativeContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  cases packet with
  | terminal packet =>
    exact SelectedCompilationMethodTerminalBounds.native_continuation
      principal packet support certified functions selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable budget
      (fun size smaller _context _invocation _scope _expression _lowered root owner physical =>
        children size smaller
          (SelectedCompilationMixedRootSupport.RootAt.ofMethod root) owner physical)
  | «scoped» packet =>
    exact SelectedCompilationMethodScopedBounds.native_continuation (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      principal packet support certified functions functionTypes faithful observations selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable extension budget children

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodHeadBounds
/-! Actual selected operator calls preserve and reflect the full caller state.
Ordered operand meaning supplies the reached argument heap; the real physical
method slot and marked parameter entry feed strict method body callbacks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id reasonAt lowered)
  {stages : Staging.Recursive.Registry}
  (port : Port (compiled := compiled) receipt context invocation.evidence stages)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (ownerFrame : owner.key.frameLocation = 0)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (slots : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix index.scope index.canonical)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
  (selection : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
    context invocation.evidence port.principal.traitName port.principal.methodName receipt.node.requirements
    port.principal.sourceBody port.principal.dictionary)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)

local notation "bridge" => callerBridge.forgetSlots
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A strict Source body callback at an authentic reached argument state. -/
def SourceBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    SelectedCompilationMethodInvocationBounds.SourceContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults)
      port.principal.cached.compilation port.sourceAt functions installed budget

/-- The native counterpart uses the same independently typed argument heap. -/
def NativeBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    SelectedCompilationMethodInvocationBounds.NativeContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults)
      port.principal.cached.compilation port.sourceAt functions installed budget

private theorem result_type : lowered.type = port.principal.named.signature.resultType :=
  receipt.result.symm.trans ((congrArg SourceCoreCalls.Signature.resultType port.signature).symm)

private theorem parameter_type : port.principal.named.signature.parameterType =
    (SourceCoreCalls.packArguments receipt.codes).type := by
  rw [port.signature]
  exact receipt.parameter

private theorem capture_read {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap}
    {store : Store} {canonical : Environment}
    (capture : CallableIndexedOwnedMethodPhysicalCaptures.Capture port.principal.cached port.principal.dictionary
      functions mapping world heap store canonical)
    (authority : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store) :
    store.read? (CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index) = some (.inRight .unit
      (.closure port.principal.named.signature.parameterType (LanguageResult.resultType port.principal.named.signature.resultType)
        (port.principal.cached.compilation.output.rename capture.installed.embedding.lift) capture.installed.captured)) := by
  have cachedCode : compiled.indexed.secondPass.closures[port.principal.cached.index]? = some
      (.lambda port.principal.named.signature.parameterType (LanguageResult.resultType port.principal.named.signature.resultType)
        port.principal.cached.compilation.output) := by
    simpa only [port.principal.cached.compilation.emitted] using port.principal.cached.cached
  simpa only [capture.embedding_eq, capture.captured_eq] using (authority.cached cachedCode).2

include owner receipt port callerBridge ownerFrame physical slots functions faults unique catalog selection runtime in
theorem preserves {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : PreservesBelow bridge context model stages invocation children faults size)
    (bodyMeaning : SourceBodies (headers := headers) (receiving := receiving) owner receipt port functions faults size) :
    PreservesAt bridge context model stages invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨orderedTyping, sourceResult⟩ :=
    SelectedCompilationMethodArgumentRows.raw_types receipt port catalog selection runtime unique typed
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  have originalTrace := trace
  rcases CallableIndexedOwnedPreparedStagedMethodSourceArguments.children receipt port unique trace with
    ⟨argumentsHeap, sources, sourceTrace, bodySize, bodyEnvironment, bound, finalContext, bodyOutcome, selectedChild,
      selected, allocated, bodyTrace, matched, strict⟩ | ⟨failure, outcomeEq, sourceTrace⟩
  · obtain ⟨values, middleStore, middleMap, middleWorld, argumentsEvaluated, represented, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
      SelectedCompilationMethodArgumentBounds.preserves_values bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace
    have argumentsTyped := post.values_typed
    have argumentsHeapTyped := post.at_values.heap
    obtain ⟨headerHeap, headerArguments, _result⟩ :=
      SelectedCompilationMethodArgumentRows.at_values receipt port catalog selection runtime unique typed
        argumentsHeapTyped argumentsTyped
    have parameters := SelectedCompilationMethodArgumentRows.represented_arguments receipt port represented
    obtain ⟨capture⟩ := SelectedCompilationMethodPhysicalCaptures.of_typed
      port.principal.cached port.principal.dictionary functions owner (callerBridge.pool reached) ownerFrame
      (physical reached) middleHeaps.runtime_hasTypes (slots reached) selection
    have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
      rw [capture.canonical_eq]
      exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, ⟨finalState, bodyRelated⟩, bodyPreserved⟩ :=
      SelectedCompilationMethodInvocationBounds.preserves
        port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner (callerBridge.pool reached)
        (capture.frame_eq.trans ownerFrame.symm) middleHeaps (physical reached) capturedSlots size
        (bodyMeaning (callerBridge.pool reached) capture.installed parameters headerHeap headerArguments post.at_values.rows selected)
        allocated bodyTrace matched strict
    have reference := agrees (slots initial _ _
      (CallableIndexedPreparedInventories.cached_global_at compiled port.principal.cached.selected))
    have read := capture_read receipt port functions capture (physical reached)
    have selectedValue := OptionalCell.read_success compilation.internalReason
      (show Evaluates (packValues values :: actual) middleStore
        (.var (ξ (current.length + compilation.administrativePrefix + port.principal.cached.index) + 1))
        (.cellRef (OptionalCell.cellType port.principal.named.signature.functionType)
          (CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index)) middleStore from .var reference) read
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot]
      exact SourceCoreCalls.call_success argumentsEvaluated selectedValue bodyEvaluated
    · simpa only [sourceResult, nativeResult] using result
    · refine after_expression_sized_of_preserved initial returned admitted originalTrace ?_
        (argumentFrame.trans bodyFrame)
      intro sourceValue same
      have preserved := bodyPreserved sourceValue same
      have actual := SelectedCompilationMethodArgumentRows.result_at_values receipt port catalog selection
        runtime unique typed preserved
      exact ⟨actual.1, actual.2, argumentMetadata.trans bodyMetadata⟩
  · subst outcome
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      SelectedCompilationMethodArgumentBounds.preserves_fault bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename]
      simpa only [receipt.result] using SourceCoreCalls.call_argument_failure
        (signature := receipt.signature) (index := ξ (current.length + compilation.administrativePrefix + receipt.index))
        (internalReason := compilation.internalReason) (receipt.parameter.symm ▸ argumentsEvaluated)
    · exact post.fault

include owner receipt port callerBridge ownerFrame physical slots functions faults unique catalog selection runtime in
theorem reflects {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : ReflectsBelow bridge context model stages invocation children faults size)
    (bodyMeaning : NativeBodies (headers := headers) (receiving := receiving) owner receipt port functions faults size) :
    ReflectsAt bridge context model stages invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨orderedTyping, sourceResult⟩ :=
    SelectedCompilationMethodArgumentRows.raw_types receipt port catalog selection runtime unique typed
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, middleMap, middleWorld, sourceTrace, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
    SelectedCompilationExpressionSequence.reflects bridge size sequence unique orderedTyping childMeaning
      environments heaps locals agrees actualTyped initial admitted argumentEvaluation smaller
  cases represented with
  | fault matched =>
    have evaluated := SourceCoreCalls.call_argument_failure
      (signature := port.principal.named.signature)
      (index := ξ (current.length + compilation.administrativePrefix + port.principal.cached.index))
      (internalReason := compilation.internalReason) (parameter.symm ▸ argumentEvaluation.sound)
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluated
    obtain ⟨_, trace⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.arguments_fault receipt port sourceTrace
    refine ⟨_, _, argumentsHeap, middleMap, middleWorld, trace, ?_, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, ?_⟩
    · rw [nativeResult]
      exact .fault matched
    · exact post.fault
  | @values sources values payloads =>
    have argumentsTyped := post.values_typed
    have argumentsHeapTyped := post.at_values.heap
    obtain ⟨headerHeap, headerArguments, _result⟩ :=
      SelectedCompilationMethodArgumentRows.at_values receipt port catalog selection runtime unique typed
        argumentsHeapTyped argumentsTyped
    have parameters := SelectedCompilationMethodArgumentRows.represented_arguments receipt port payloads
    obtain ⟨capture⟩ := SelectedCompilationMethodPhysicalCaptures.of_typed
      port.principal.cached port.principal.dictionary functions owner (callerBridge.pool reached) ownerFrame
      (physical reached) middleHeaps.runtime_hasTypes (slots reached) selection
    have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
      rw [capture.canonical_eq]
      exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
    have reference := agrees (slots initial _ _
      (CallableIndexedPreparedInventories.cached_global_at compiled port.principal.cached.selected))
    have read := capture_read receipt port functions capture (physical reached)
    obtain ⟨bodySize, bodySmaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
      argumentEvaluation.sound reference read completed
    obtain ⟨bodySourceSize, bodyEnvironment, bound, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld,
        allocated, bodyTrace, matched, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, ⟨finalState, bodyRelated⟩, bodyPreserved⟩ :=
      SelectedCompilationMethodInvocationBounds.reflects
        port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner (callerBridge.pool reached)
        (capture.frame_eq.trans ownerFrame.symm) middleHeaps (physical reached) capturedSlots size
        (bodyMeaning (callerBridge.pool reached) capture.installed parameters headerHeap headerArguments post.at_values.rows port.staged)
        bodyEvaluation (Nat.le_of_lt bodySmaller)
    obtain ⟨_, trace⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.applied receipt port sourceTrace
      port.staged allocated bodyTrace matched
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · simpa only [sourceResult, nativeResult] using result
    · refine after_expression_sized_of_preserved initial returned admitted trace ?_
        (argumentFrame.trans bodyFrame)
      intro sourceValue same
      have preserved := bodyPreserved sourceValue same
      have actual := SelectedCompilationMethodArgumentRows.result_at_values receipt port catalog selection
        runtime unique typed preserved
      exact ⟨actual.1, actual.2, argumentMetadata.trans bodyMetadata⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectBuiltinBounds
/-! The real contracted builtin call executes its ordered arguments once.
Its literal callee and both gates are pure; successful primitive application
keeps the reached heap, store and caller records. Child failures retain their
original Source scope and diagnostic. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectBuiltinBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open BuiltinCalls.Protocol
open GenericExpressionMeaning (agree_prefix rename_prefix)
universe u

open CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds (Point)

private theorem values_rep {checked : SourceCoreCompatibleCatalog.Checked} {receiving : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel checked receiving functions)
      mapping world types natives sources payloads) :
    ValuesRep checked receiving functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

private theorem prefixed_typed {definitions : DataEnvironment} {world : StoreTyping}
    {actual : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (function : BuiltinFunctionId) (identity contract : Word) :
    RuntimeEnvironmentHasTypes world (.unit :: contractedValue function identity contract actual :: actual)
      (.unit :: CallableContract.functionType (SourceCoreInteger.builtinParameter function)
        (SourceCoreInteger.builtinResult function) :: actualContext) definitions := by
  have closureTyped := SourceCoreInteger.builtinClosure_hasType (scope := actualContext) (definitions := definitions) function
  cases closureTyped with
  | lambda _ _ body => exact .cons .unit (.cons (.pair (.pair (.inRight .word) (.closure typed body)) .word) typed)

private theorem contracted_rename (function : BuiltinFunctionId) (identity contract : Word) (ξ : Renaming) :
    (contracted function identity contract).rename ξ = contracted function identity contract := by
  cases function <;> rfl

private theorem call_rename (function : BuiltinFunctionId) (identity contract unknown : Word)
    (arguments : Expr) (ξ : Renaming) :
    (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (contracted function identity contract) arguments).rename ξ =
    CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (contracted function identity contract) (arguments.rename ξ) := by
  simp [CallableContract.call, LanguageResult.bind, CallableContract.dispatch, CallableContract.guardResult,
    CallableContract.Gate.reason, LanguageResult.success, LanguageResult.failure,
    contracted_rename, Expr.rename, Renaming.lift]

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
  {ids : List ExpressionId} {function : BuiltinFunctionId} {codes : List SourceCoreBasic.LoweredExpr}
  {identity contract unknown : Word}
  (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
    (SourceCoreInteger.builtinResult function))
  (form : node.form = .call callee ids (.builtinFunction function))
  (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "headCode" => SourceCoreBasic.LoweredExpr.mk (SourceCoreInteger.builtinResult function)
  (CallableContract.call [CallableContract.Gate.mk contract none none] unknown (SourceCoreInteger.builtinResult function)
    (contracted function identity contract) (SourceCoreBasic.LoweredExpr.expression (SourceCoreCalls.packArguments codes)))

include bridge functions observations faults unique metadata form nativeTypes in
theorem preserves {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids function.parameterTypes codes)
    (childMeaning : PreservesBelow bridge context model registry invocation children faults size) :
    PreservesAt bridge context model registry invocation (Point scope id headCode) faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨typing, sourceResult⟩ := CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types
    unique metadata.found form metadata.coercions typed
  have prefixed := prefixed_typed actualTyped function identity contract
  have agreesPrefix : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: contractedValue function identity contract actual :: actual) :=
    agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
  rcases CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.children unique metadata.found form trace with
    ⟨sequenceSize, invocationSize, argumentsHeap, sources, sameSize, sourceTrace, applied⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, payloads, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_values bridge size sequence unique typing
        childMeaning environments heaps locals agreesPrefix prefixed initial admitted sourceTrace within
    have represented := values_rep payloads
    rw [nativeTypes] at represented
    have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
    obtain ⟨value, sameOutcome, sameHeap, _grade, primitive⟩ :=
      CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.source_value functions observations represented applied
    subst outcome
    subst after
    rw [rename_prefix, rename_prefix] at evaluated
    obtain ⟨actualResult, nativeResult, actualPrimitive, resultRep, completed⟩ := contracted_preserves
      (identity := identity) (contract := contract) (unknown := unknown) inputs evaluated
    have same := actualPrimitive.functional primitive
    subst actualResult
    refine ⟨.inRight .word nativeResult, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, ?_⟩
    · rw [call_rename]; exact completed
    · rw [sourceResult]
      exact .value (CompatibleBuiltinMeaning.result_represents inputs primitive resultRep)
    · refine ⟨post.rows, ?_⟩
      intro value same
      cases same
      exact ⟨sourceResult ▸ primitive.preserves.2, post.at_values.heap⟩
  · subst outcome
    have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_fault bridge size sequence unique typing
        childMeaning environments heaps locals agreesPrefix prefixed initial admitted sourceTrace within
    rw [rename_prefix, rename_prefix] at evaluated
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, ?_⟩
    · rw [call_rename]
      exact CallableContract.call_argument_failure [⟨contract, none, none⟩] unknown
        (contracted_evaluates function identity contract actual store)
        (gates_accept contract unknown .beforeArguments) evaluated
    · exact post.fault

include bridge functions observations faults unique metadata form nativeTypes in
theorem reflects {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids function.parameterTypes codes)
    (childMeaning : ReflectsBelow bridge context model registry invocation children faults size) :
    ReflectsAt bridge context model registry invocation (Point scope id headCode) faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨typing, sourceResult⟩ := CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types
    unique metadata.found form metadata.coercions typed
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.builtinFunction function)) :=
    ⟨node, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have prefixed := prefixed_typed actualTyped function identity contract
  have agreesPrefix : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: contractedValue function identity contract actual :: actual) :=
    agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
  rw [call_rename] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedBuiltinCallBounds.contracted_arguments_sized completed
  have shifted := argumentEvaluation
  rw [← rename_prefix, ← rename_prefix] at shifted
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
    SelectedCompilationExpressionSequence.reflects bridge size sequence unique typing childMeaning
      environments heaps locals agreesPrefix prefixed initial admitted shifted smaller
  cases represented with
  | @values sources values payloads =>
    have represented := values_rep payloads
    rw [nativeTypes] at represented
    have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
    obtain ⟨sourceValue, nativeValue, primitive, resultRep, same, sameStore⟩ :=
      contracted_reflects inputs argumentEvaluation.sound completed.sound
    subst value
    subst finalStore
    have trace := Staging.Recursive.Size.Expression.builtinApplied occurrence sourceTrace
      (Staging.Recursive.Size.Applies.builtin primitive)
    refine ⟨_, _, argumentsHeap, finalMap, finalWorld, trace, ?_, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, ?_⟩
    · rw [sourceResult]
      exact .value (CompatibleBuiltinMeaning.result_represents inputs primitive resultRep)
    · refine ⟨post.rows, ?_⟩
      intro value same
      cases same
      exact ⟨sourceResult ▸ primitive.preserves.2, post.at_values.heap⟩
  | fault matched =>
    have failed := CallableContract.call_argument_failure
      (result := SourceCoreInteger.builtinResult function) [⟨contract, none, none⟩] unknown
      (contracted_evaluates function identity contract actual store)
      (gates_accept contract unknown .beforeArguments) argumentEvaluation.sound
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
    have trace := Staging.Recursive.Size.Expression.builtinArgumentsFault occurrence sourceTrace
    refine ⟨_, _, argumentsHeap, finalMap, finalWorld, trace, .fault matched, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, ?_⟩
    exact post.fault

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectBuiltinBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionTyping
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionTyping
open Frontend SourceInference TypeSystem Solcore.SourceSemantics.Dynamic
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableCoercionSourceSelection
open CallableNamedMetadata (evidence environment)
open CallableCoercionMethodInstantiation (bodyInstance Formation)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}

theorem retained_valid (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (cached : Cached compiled method.specialized)
    (receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method) :
    MethodDefinition.Valid compiled.sourceProgram.signatures (MethodDefinition.ofChecked receipt.retained) :=
  bodies.methods receipt.retained ⟨cached.index, cached.named, method, cached.selected, cached.same,
    receipt.toSelection, receipt.retainedMember, receipt.retainedId, receipt.completeCheckedEq⟩

theorem certificate
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (cached : Cached compiled method.specialized)
    {primary : TypedTraitResolution.Evidence} {name : String}
    (selected : CallableCoercionMethodInstantiation.Selection compiled.sourceProgram primary name method)
    (parameters : selected.implementation.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) method.specialized.parameterSubstitution) :
    ∃ definition, definition ∈ (Program.ofChecked compiled.sourceProgram).methods ∧
      definition.id = selected.declaration.id ∧
      Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
        selected.implementation selected.declaration selected.trait definition
        method.specialized.parameterSubstitution (bodyInstance compiled.sourceProgram method) ∧
      ∃ types lexical facts, Dynamic.TraitMethodInstanceTypingCertificate
        (Program.ofChecked compiled.sourceProgram) selected.declaration method.specialized.parameterSubstitution
        definition (bodyInstance compiled.sourceProgram method) types lexical facts := by
  obtain ⟨definition, member, identity, instantiated⟩ := selected.instantiates checked parameters range
  obtain ⟨retained, retainedMember, retainedId, retainedBody⟩ := selected.toSelection.retained checked
  have retainedValid := bodies.methods retained
    ⟨cached.index, cached.named, method, cached.selected, cached.same, selected.toSelection,
      retainedMember, retainedId, retainedBody⟩
  have sameDefinition : definition = MethodDefinition.ofChecked retained :=
    StructuralSubstitution.eq_of_mem_of_mapped_nodup bodies.method_ids member
      (List.mem_map.mpr ⟨retained, retainedMember, rfl⟩)
      (identity.trans (retainedId.trans selected.methodId).symm)
  have valid : MethodDefinition.Valid compiled.sourceProgram.signatures definition :=
    sameDefinition ▸ retainedValid
  exact ⟨definition, member, identity, instantiated,
    instantiated.certificate_of_valid bodies.signatures valid⟩

theorem selects
    {method : ExecutableImplMethods.CheckedMethod}
    (loadedAccepted : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (cached : Cached compiled method.specialized)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {primaryId : RequirementId} {methodIds : List RequirementId} {arity : Nat}
    {traitName methodName : String} {context : Context}
    (receipt : MethodCertificate compiled.sourceProgram caller node available primaryId methodIds arity traitName methodName method)
    (formed : Formation receipt.selected.implementation receipt.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) method.specialized.parameterSubstitution)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller method)
    (materialized : SourceCompilationPlan.operatorMethodRuntimeEvidence compiled.sourceProgram caller node ⟨primaryId, method⟩ = .ok dictionary) :
    TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context (environment available) traitName methodName
      (primaryId :: methodIds) (bodyInstance compiled.sourceProgram method) (environment dictionary) := by
  obtain ⟨definition, definitionMember, definitionId, instantiated, certified⟩ :=
    certificate loadedAccepted bodies cached receipt.selected formed.parameters range
  have determined := receipt.selected.determines formed
  have headTrait : receipt.selected.goal.trait = receipt.selected.implementation.head.trait := by
    exact (congrArg (fun goal : ProgramPredicate => goal.trait) determined.2.2).symm
  have produced := requirement_produces signatures ledger assumptions resolved
    receipt.roots.primarySelected receipt.roots.primaryValid
  have sourceSelected : EvidenceSelectsMethod (Program.ofChecked compiled.sourceProgram)
      (evidence receipt.roots.primary) methodName definition := by
    simpa only [receipt.selected.primaryShape, evidence] using
      (EvidenceSelectsMethod.source (premises := method.implementationPremises.map evidence)
        receipt.selected.implementationMember headTrait receipt.selected.methodMember
        receipt.selected.declarationName definitionMember definitionId)
  have primaryGoal : SourceCompilationPlan.runtimeEvidenceGoal receipt.roots.primary = receipt.selected.goal := by
    exact congrArg SourceCompilationPlan.runtimeEvidenceGoal receipt.selected.primaryShape
  rw [primaryGoal] at produced
  have methodsProduced := requirements_produce signatures ledger assumptions resolved
    receipt.roots.methodsSelected receipt.roots.methodsValid
  have methodsGoals : receipt.roots.methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal =
      receipt.selected.declaration.wherePredicates.map
        (ProgramPredicate.applyParameters method.specialized.parameterSubstitution) := by
    rw [← receipt.roots.methods, receipt.selected.methodsGoals, receipt.selected.method_predicates formed]
  rw [methodsGoals] at methodsProduced
  have assembled := (CallableCoercionEvidenceOrigins.roots_origins receipt.roots covered resolved
    (CallableCoercionEvidenceOrigins.materialized_operator materialized)).1
  have methodAssumptions : method.specialized.assumptions =
      (SourceSemantics.methodAssumptions receipt.selected.trait receipt.selected.implementation receipt.selected.declaration).map
        (ProgramPredicate.applyParameters method.specialized.parameterSubstitution) :=
    (CallableCoercionBodyProvenance.specialization_fields receipt.selected.specialized).2
  rw [methodAssumptions] at assembled
  have traitOwner : receipt.selected.declaration.traitMethod.trait = receipt.selected.trait.id := by
    have found := receipt.selected.traitLookup
    unfold ProgramSignatures.trait? at found
    exact (of_decide_eq_true (List.find?_some
      (p := fun trait : ProgramTraitSignature => decide (trait.id = receipt.selected.declaration.traitMethod.trait)) found)).symm
  refine .intro (.intro produced sourceSelected) ?_ receipt.selected.implementationMember
    receipt.selected.traitMember receipt.traitName receipt.selected.goalTrait determined
    receipt.selected.methodMember receipt.selected.declarationName traitOwner methodsProduced instantiated ?_ ?_ certified
  · exact ⟨method.implementationPremises.map evidence, by
      simpa only [evidence] using congrArg evidence receipt.selected.primaryShape⟩
  · simpa only [environment, List.map_map, Function.comp_def] using assembled
  · obtain ⟨_, valid, goals⟩ := CallableCoercionEvidenceOrigins.roots_origins receipt.roots covered resolved
      (CallableCoercionEvidenceOrigins.materialized_operator materialized)
    refine ⟨valid, ?_⟩
    intro goal member
    exact EvidenceEnvironment.LooksUp.exists_of_key_mem (goals.symm ▸ member)


theorem source_selects
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
    {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Core.Word} {policy : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
    {receipt : Operator compiled.sourceProgram project caller compilation child fuel source scope id reasonAt policy node output}
    (cached : Cached compiled receipt.selection.method.specialized)
    (selected : SourceReceipt receipt)
    (formed : Formation selected.certificate.selected.implementation selected.certificate.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) receipt.selection.method.specialized.parameterSubstitution)
    {context : Context} (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller receipt.selection.method) :
    TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context (environment receipt.available)
      selected.traitName selected.methodName receipt.requirements
      (bodyInstance compiled.sourceProgram receipt.selection.method) (environment receipt.dictionary) := by
  rw [selected.requirements]
  exact selects checked bodies cached selected.certificate formed range signatures ledger assumptions
    receipt.resolved covered receipt.materialized

theorem selected_typed {sourceProgram : Program} {context : Context}
    {callerEvidence dictionary : Dynamic.EvidenceEnvironment} {traitName methodName : String}
    {requirements : List RequirementId} {body : Dynamic.BodyInstance}
    (selected : Dynamic.TypedOperatorMethodSelected sourceProgram context callerEvidence traitName methodName
      requirements body dictionary) :
    ∃ types lexicalContext facts,
      Dynamic.BodyInstanceTypingCertificate sourceProgram body types lexicalContext facts ∧
      CompatibleRuntimeContextValidity.Valid body.context.solvedRequirements lexicalContext dictionary := by
  cases selected with
  | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covers certified =>
    obtain ⟨types, lexicalContext, facts, typed⟩ := certified
    refine ⟨types, lexicalContext, facts, typed.toBodyInstanceTypingCertificate, ?_⟩
    exact (show CompatibleRuntimeContextValidity.Valid body.context.solvedRequirements body.context dictionary from
      ⟨rfl, typed.requirement_ledger.toRuntime, covers⟩).mono typed.typing.inputs_extend

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRuntimeProfile
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRuntimeProfile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallablePreparedMethodSelection CallableCoercionMethodInstantiation
open CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogHookMeaning
open CallablePreparedMethodRuntimeProfileFactory (SourceAt)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

/-- The real retained method's declared callable type agrees with its raw input
binders before and after structural substitution. No packed arity is inverted. -/
theorem callable_shape {program : CheckedProgram} {method : ExecutableImplMethods.CheckedMethod}
    (receipt : CallableCoercionBodyProvenance.Certificate program method)
    (valid : MethodDefinition.Valid program.signatures (MethodDefinition.ofChecked receipt.retained)) :
    method.specialized.function.type = .function
      (TypeSystem.Ty.productMany (method.specialized.function.typedBody.inputs.map (fun b => b.scheme.body)))
      method.specialized.function.inferredBodyType := by
  cases valid with
  | intro _ _ _ _ _ _ _ _ _ body =>
    cases body with
    | intro _ _ _ _ shape result _ _ _ extended _ _ _ _ _ _ =>
      have inputs := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      change receipt.retained.checked.typedBody.inputs.map (fun b => b.scheme.body) = _ at inputs
      have genericShape : receipt.retained.checked.type = .function
          (TypeSystem.Ty.productMany (receipt.retained.checked.typedBody.inputs.map (fun b => b.scheme.body)))
          receipt.retained.checked.inferredBodyType := by
        rw [inputs]
        exact shape.trans (congrArg (TypeSystem.Ty.function _) result.symm)
      rw [receipt.result.2, genericShape]
      simp only [TypeSystem.ParameterSubstitution.apply]
      rw [← receipt.result.1, StructuralSubstitution.apply_productMany, receipt.inputs]
      simp only [List.map_map, Function.comp_def, StructuralSubstitution.applyBinder, StructuralSubstitution.applyScheme]

private theorem project_productMany {catalog : SourceCoreCompatibleCatalog.Catalog}
    {types : List TypeSystem.Ty} {native : List Core.Ty}
    (projected : types.mapM catalog.project = .ok native) :
    catalog.project (TypeSystem.Ty.productMany types) = .ok (SourceCoreCompatibleCatalog.packTypes native) := by
  induction types generalizing native with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projected
    subst native
    rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at projected
    obtain ⟨first, firstProjected, projected⟩ := bind_ok projected
    obtain ⟨rest, restProjected, projected⟩ := bind_ok projected
    cases projected
    cases tail with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at restProjected
      subst rest
      exact firstProjected
    | cons next suffix =>
      have remaining := ih restProjected
      rw [List.mapM_cons] at restProjected
      obtain ⟨nextNative, _, restProjected⟩ := bind_ok restProjected
      obtain ⟨suffixNative, _, restProjected⟩ := bind_ok restProjected
      cases restProjected
      change (do pure (Ty.product (← catalog.project head)
        (← catalog.project (TypeSystem.Ty.productMany (next :: suffix))))) = _
      rw [firstProjected, remaining]
      rfl

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (cached : Cached compiled method.specialized)

theorem parameters : (bodyInstance compiled.sourceProgram method).source.inputs = cached.named.inputs.map Prod.fst := by
  obtain ⟨row, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled cached.selected
  have fields := SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted
  rw [← fields.1, cached.same] at fields
  exact fields.2.1.symm

theorem parameter_pack
    (receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method)
    (valid : MethodDefinition.Valid compiled.sourceProgram.signatures (MethodDefinition.ofChecked receipt.retained)) :
    cached.named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) := by
  obtain ⟨row, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled cached.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  have shape := callable_shape receipt valid
  have inputs := parameters cached
  change method.specialized.function.typedBody.inputs = _ at inputs
  rw [inputs] at shape
  have actualShape : row.function.type = .function
      (TypeSystem.Ty.productMany (cached.named.inputs.map (fun b => b.1.scheme.body)))
      row.function.inferredBodyType := by
    rw [← same, cached.same]
    simpa only [List.map_map, Function.comp_def] using shape
  have projected := CompatibleExpressionReads.projectType_of_accepted
    (RecursiveNamedHeaderParameterProjections.prepared_parameter accepted actualShape)
  have vector := project_productMany
    (RecursiveNamedPreparedParameterProjections.cached_projected compiled cached.selected)
  exact Except.ok.inj (projected.symm.trans vector)

theorem source_at {values : SourceCoreCompatibleValues.Context}
    (sameChecked : values.checked = compiled.compatible.checked)
    (receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {context : SourceSemantics.Context} {callerEvidence dictionary : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      traitName methodName requirements (bodyInstance compiled.sourceProgram method) dictionary)
    (unique : NodeOccurrencesUnique (bodyInstance compiled.sourceProgram method).source)
    (signatures : compiled.sourceProgram.signatures = values.checked.signatures) :
    Nonempty (SourceAt cached.compilation values (bodyInstance compiled.sourceProgram method) dictionary) := by
  obtain ⟨types, lexical, facts, typed, valid⟩ := SelectedCompilationMethodSelectionTyping.selected_typed selected
  have fields := RecursiveNamedInitialContextValidity.mono_fields typed.typing.inputs_extend
  refine ⟨⟨?_, parameters cached, cached.frame selected.selected, lexical, types, typed.typing.inputs_extend,
    ?_, fields.typeVariables.trans typed.type_variables_empty,
    fields.residualTypeVariables.trans typed.residual_type_variables_open,
    fields.signatures.trans (typed.signatures_eq.trans signatures), ?_, parameter_pack cached receipt (SelectedCompilationMethodSelectionTyping.retained_valid bodies cached receipt), unique⟩⟩
  · simp only [CallableIndexedNamedGeneration.source, cached.same, bodyInstance]
  · change CompatibleRuntimeContextValidity.Valid method.specialized.function.solvedRequirements lexical dictionary at valid
    simpa only [cached.same] using valid
  · rw [sameChecked]
    exact CallablePreparedMethodRuntimeProfileFactory.result_projection cached


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRuntimeProfile
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionRanges
/-! Actual implementation-head matching recovers every ordered replacement
from an admitted goal. Concrete specialization then closes its raw catalog type. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionRanges
open Frontend TypeSystem

private def applicationArguments : Ty → List Ty
  | .application head argument => applicationArguments head ++ [argument]
  | _ => []

private theorem arguments_applyMany (head : Ty) (arguments : List Ty) :
    applicationArguments (Ty.applyMany head arguments) = applicationArguments head ++ arguments := by
  induction arguments generalizing head with
  | nil => simp [Ty.applyMany]
  | cons argument rest ih =>
    change applicationArguments (Ty.applyMany (.application head argument) rest) = _
    rw [ih]
    simp [applicationArguments, List.append_assoc]

private theorem arguments_nominal (declaration : Resolved.DeclarationId) (arguments : List Ty) :
    applicationArguments (Ty.nominal declaration arguments) = arguments := by
  simp [Ty.nominal, arguments_applyMany, applicationArguments]

private theorem scoped_arguments {context : Context} {variables : List TypeVarId} {type : Ty}
    (typed : TypeWellScoped context variables type) :
    ∀ argument ∈ applicationArguments type, TypeWellScoped context variables argument := by
  cases typed with
  | nominal declaration arguments member arity typed
  | contractNominal declaration arguments member arity typed =>
    rw [arguments_nominal]
    intro argument member
    exact typed.member member
  | _ => simp [applicationArguments]

private def applicationHead : Ty → Ty
  | .application head _ => applicationHead head
  | other => other

private theorem head_applyMany (head : Ty) (arguments : List Ty) :
    applicationHead (Ty.applyMany head arguments) = applicationHead head := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument rest ih => exact ih (.application head argument)

private theorem nominal_ne_proxy (declaration : Resolved.DeclarationId) (arguments : List Ty) (inner : Ty) :
    Ty.nominal declaration arguments ≠ .proxy inner := by
  intro same
  have heads := congrArg applicationHead same
  simp [Ty.nominal, head_applyMany, applicationHead] at heads

private theorem nominal_ne_comptime (declaration : Resolved.DeclarationId) (arguments : List Ty) (inner : Ty) :
    Ty.nominal declaration arguments ≠ .comptime inner := by
  intro same
  have heads := congrArg applicationHead same
  simp [Ty.nominal, head_applyMany, applicationHead] at heads

private theorem scoped_proxy {context : Context} {variables : List TypeVarId} {type : Ty}
    (typed : TypeWellScoped context variables type) :
    ∀ inner, type = .proxy inner → TypeWellScoped context variables inner := by
  cases typed with
  | nominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_proxy declaration.id arguments inner same)
  | contractNominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_proxy declaration.id arguments inner same)
  | proxy inner => intro _ same; cases same; exact inner
  | _ => intro _ same; cases same

private theorem scoped_comptime {context : Context} {variables : List TypeVarId} {type : Ty}
    (typed : TypeWellScoped context variables type) :
    ∀ inner, type = .comptime inner → TypeWellScoped context variables inner := by
  cases typed with
  | nominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_comptime declaration.id arguments inner same)
  | contractNominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_comptime declaration.id arguments inner same)
  | comptime inner => intro _ same; cases same; exact inner
  | _ => intro _ same; cases same

private theorem occurs_applyMany (parameter : TypeParameterId) (head : Ty) (arguments : List Ty) :
    TypeParameterOccurs parameter (Ty.applyMany head arguments) ↔
      TypeParameterOccurs parameter head ∨ ∃ argument ∈ arguments, TypeParameterOccurs parameter argument := by
  induction arguments generalizing head with
  | nil => simp [Ty.applyMany]
  | cons argument rest ih =>
    change TypeParameterOccurs parameter (Ty.applyMany (.application head argument) rest) ↔ _
    rw [ih]
    simp only [TypeSystem.TypeParameterOccurs, List.mem_cons, exists_eq_or_imp, or_assoc]

private theorem occurs_nominal {parameter : TypeParameterId} {declaration : Resolved.DeclarationId} {arguments : List Ty}
    (occurs : TypeParameterOccurs parameter (Ty.nominal declaration arguments)) :
    ∃ argument ∈ arguments, TypeParameterOccurs parameter argument := by
  rcases (occurs_applyMany parameter (.constructor (.declaration declaration)) arguments).mp occurs with impossible | found
  · cases impossible
  · exact found

/-- The original well-scoped head prevents parameters from appearing in an
ill-formed nominal head with missing arguments. Each genuine occurrence recovers its replacement. -/
private theorem scoped_at_occurrence {original target : Context} {originalVariables variables : List TypeVarId}
    (substitution : TypeSystem.ParameterSubstitution) {type : Ty}
    (originalTyped : TypeWellScoped original originalVariables type) :
    ∀ parameter, TypeParameterOccurs parameter type →
      TypeWellScoped target variables (substitution.apply type) →
      TypeWellScoped target variables ((substitution.lookup? parameter).getD (.parameter parameter)) := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => ∀ parameter, TypeParameterOccurs parameter type →
      TypeWellScoped target variables (substitution.apply type) →
      TypeWellScoped target variables ((substitution.lookup? parameter).getD (.parameter parameter)))
    (motive_2 := fun types _ => ∀ type ∈ types, ∀ parameter, TypeParameterOccurs parameter type →
      TypeWellScoped target variables (substitution.apply type) →
      TypeWellScoped target variables ((substitution.lookup? parameter).getD (.parameter parameter)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ originalTyped
  · intro metavariable bound parameter occurs; cases occurs
  · intro actual bound owned parameter occurs typed
    cases occurs
    exact typed
  · intro builtin parameter occurs; cases occurs
  · intro declaration arguments cataloged arity originalTyped ih parameter occurs typed
    obtain ⟨argument, member, occurs⟩ := occurs_nominal occurs
    apply ih argument member parameter occurs
    rw [StructuralSubstitution.apply_nominal] at typed
    exact scoped_arguments typed _ (by rw [arguments_nominal]; exact List.mem_map.mpr ⟨argument, member, rfl⟩)
  · intro declaration arguments cataloged arity originalTyped ih parameter occurs typed
    obtain ⟨argument, member, occurs⟩ := occurs_nominal occurs
    apply ih argument member parameter occurs
    rw [StructuralSubstitution.apply_nominal] at typed
    exact scoped_arguments typed _ (by rw [arguments_nominal]; exact List.mem_map.mpr ⟨argument, member, rfl⟩)
  · intro left right first second leftIH rightIH parameter occurs typed
    rcases occurs with occurs | occurs
    · exact leftIH parameter occurs (typed.function_components _ _ rfl).1
    · exact rightIH parameter occurs (typed.function_components _ _ rfl).2
  · intro left right first second leftIH rightIH parameter occurs typed
    rcases occurs with occurs | occurs
    · exact leftIH parameter occurs (typed.product_components _ _ rfl).1
    · exact rightIH parameter occurs (typed.product_components _ _ rfl).2
  · intro left right first second leftIH rightIH parameter occurs typed
    rcases occurs with occurs | occurs
    · exact leftIH parameter occurs (typed.mapping_components _ _ rfl).1
    · exact rightIH parameter occurs (typed.mapping_components _ _ rfl).2
  · intro inner originalTyped ih parameter occurs typed
    exact ih parameter occurs (scoped_proxy typed _ rfl)
  · intro inner originalTyped ih parameter occurs typed
    exact ih parameter occurs (scoped_comptime typed _ rfl)
  · intro type member; cases member
  · intro head tail headTyped tailTyped headIH tailIH type member
    rcases List.mem_cons.mp member with rfl | member
    · exact headIH
    · exact tailIH type member

private theorem admissible_at_occurrence
    {original context : Context} {originalVariables : List TypeVarId}
    (substitution : TypeSystem.ParameterSubstitution) {type : Ty} {parameter : TypeParameterId}
    (originalTyped : TypeWellScoped original originalVariables type)
    (occurs : TypeParameterOccurs parameter type)
    (admitted : TypeAdmissible context (substitution.apply type)) :
    TypeAdmissible context ((substitution.lookup? parameter).getD (.parameter parameter)) := by
  have replacementScoped := scoped_at_occurrence substitution originalTyped parameter occurs admitted.typeWellScoped
  cases residual : context.residualTypeVariables with
  | false =>
    exact ⟨admitted.binders, by simpa [admissibleTypeVariables, residual] using replacementScoped⟩
  | true =>
    exact StructuralSubstitution.TypeWellScoped.toAdmissibleOfResidual admitted.binders residual replacementScoped

/-- Every original implementation parameter occurs in its well-formed head.
The genuine selected head equation identifies the admitted replacement, and
actual specialization acceptance supplies its full concrete check. -/
theorem of_selected
    {program : CheckedProgram} {primary : TypedTraitResolution.Evidence}
    {name : String} {method : ExecutableImplMethods.CheckedMethod}
    (selected : CallableCoercionMethodInstantiation.Selection program primary name method)
    (catalog : SignatureCatalogWellFormed program.signatures)
    (formed : CallableCoercionMethodInstantiation.Formation selected.implementation selected.declaration)
    {context : Context} (signatures : context.signatures = program.signatures)
    (admitted : PredicateAdmissible context selected.goal) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) method.specialized.parameterSubstitution := by
  let substitution := method.specialized.parameterSubstitution
  have original := catalog.implementations_semantic selected.implementation selected.implementationMember
  have determined := selected.determines formed
  have headEq := determined.2.2
  rw [← headEq] at admitted
  intro parameter replacement member
  have parameterMember : parameter ∈ selected.implementation.parameters := by
    rw [← selected.domain]
    exact List.mem_map.mpr ⟨(parameter, replacement), member, rfl⟩
  have lookup := StructuralSubstitution.ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup
    (selected.exact_substitution formed.parameters).domain_nodup member
  have replacementAdmitted : TypeAdmissible context replacement := by
    rcases original.parameters_in_head parameter parameterMember with occurs | ⟨argument, argumentMember, occurs⟩
    · have recovered := admissible_at_occurrence substitution original.head.subject.typeWellScoped occurs admitted.subject
      simpa only [substitution, lookup, Option.getD_some] using recovered
    · have argumentAdmitted : TypeAdmissible context (substitution.apply argument) :=
        admitted.arguments _ (List.mem_map.mpr ⟨argument, argumentMember, rfl⟩)
      have recovered := admissible_at_occurrence substitution
        (original.head.arguments argument argumentMember).typeWellScoped occurs argumentAdmitted
      simpa only [substitution, lookup, Option.getD_some] using recovered
  have concrete := SourceSpecializationAcceptance.specializeFunction_parameterReplacement_concrete
    selected.specialized parameter replacement lookup
  have closed := CallableIndexedOwnedReachedNamedConcreteRangeReceipts.admissible_concrete_at_catalog
    replacementAdmitted concrete
  simpa only [signatures] using closed

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionRanges
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionIssuance
/-! The original coercion selector and final preparation supply the complete
method port. Only syntactic source shape and formation are static inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionIssuance
open Core Frontend SourceInference
open CallablePreparedMethodSelection
open CallableIndexedOwnedPreparedStagedCoercionAuthority
open CallableNamedMetadata (environment)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available
    scope node policy input coercion output call)

structure Support (selected : CallableCoercionSourceSelection.Certificate
    compiled.sourceProgram caller node available coercion step.method) : Prop where
  formed : CallableCoercionMethodInstantiation.Formation selected.selected.implementation selected.selected.declaration
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) step.method.specialized.parameterSubstitution
  covered : CallableCoercionEvidenceOrigins.CallerCovered caller step.method
  unique : NodeOccurrencesUnique (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram step.method).source
  empty : step.method.specialized.assumptions = []
  parameters : step.method.specialized.function.typedBody.inputs.map (fun binder => binder.scheme.body) = [coercion.source]
  result : step.method.specialized.function.inferredBodyType = coercion.target

private theorem exact_member {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) : row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected <;> try contradiction
  rename_i actual found
  cases selected
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [found]
    simp
  exact (List.mem_filter.mp member).1

private theorem exact_key {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) : row.key = key := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected <;> try contradiction
  rename_i actual found
  cases selected
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [found]
    simp
  exact of_decide_eq_true (List.mem_filter.mp member).2

private theorem cached_key {method : ExecutableImplMethods.CheckedMethod}
    (cached : Cached compiled method.specialized) : cached.named.signature.key = method.specialized.key := by
  have record := CallableIndexedActualNamedSourceReceipts.cached_record compiled cached.selected cached.compilation.hook
  exact (exact_key record).symm.trans (congrArg (fun row : SourceSpecialization.SpecializedFunction => row.key) cached.same)

private theorem descriptor {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method) :
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named principal.named.signature.key)) := by
  obtain ⟨origin, selected, _, _⟩ := principal.hook_history
  cases made : SourceCoreCallableContracts.descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named principal.named.signature.key) with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at made
    split at made
    · next absent => rw [selected] at absent; cases absent
    · cases made
  | ok descriptor => exact ⟨descriptor⟩

include step in
theorem of_actual
    (selected : CallableCoercionSourceSelection.Certificate compiled.sourceProgram caller node available coercion step.method)
    (support : Support step selected)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (site : coercion ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty {port : Port (compiled := compiled) step context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages) //
      SelectedCompilationMethodBodySupport.Certified port.principal port.sourceAt} := by
  have same := CallableCoercionPreparation.step_specialized prepared callerMember nodeMember site resolved step
  have target := step.selected
  rw [same, samePlan] at target
  obtain ⟨initial⟩ := cached_row compiled (exact_member target)
  obtain ⟨diagnostics, code, diagnosticPresent, codeFound, codeAccepted⟩ := NamedCalls.compiled_at compiled.indexed initial.selected
  obtain ⟨generation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed codeAccepted
  let cached : Cached compiled step.method.specialized :=
    ⟨initial.index, initial.named, _, code, initial.selected, initial.same, codeFound, generation⟩
  have chosenTyped := SelectedCompilationMethodSelectionTyping.selects checked bodies cached
    selected.toMethodCertificate support.formed support.range signatures ledger assumptions resolved support.covered step.materialized
  have chosenTyped : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      "Coerce" "coerce" coercion.requirements
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram step.method)
      (environment step.dictionary) := by simpa only [dictionary, CoercionStep.requirements] using chosenTyped
  have chosen := chosenTyped.selected
  let principal := CallableIndexedOwnedMethodPrincipal.of_selected cached chosen
  have key : cached.named.signature.key = step.key :=
    (cached_key cached).trans (CallableCoercionPreparation.exact_call_key step.edge).symm
  have member : (cached.named.signature, cached.index) ∈ compilation.globals.zipIdx.filter
      (fun row => decide (row.1.key = step.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr ?_, ?_⟩
    · rw [globals]
      exact CallableIndexedPreparedInventories.cached_global_at compiled cached.selected
    · simp only [key, decide_true]
  rw [step.global] at member
  have aligned := Prod.mk.inj (List.mem_singleton.mp member)
  obtain ⟨descriptor⟩ := descriptor principal
  obtain ⟨sidecar, _, _, staged⟩ := RecursiveMethodPreparedStageScopes.selected_of_descriptor actualStages principal descriptor
  obtain ⟨retained⟩ := CallableCoercionBodyProvenance.of_accepted checked step.selectedMethod
  obtain ⟨sourceAt⟩ := SelectedCompilationMethodRuntimeProfile.source_at (values := .initial compiled.compatible.checked) cached rfl retained bodies
    chosenTyped support.unique (CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm
  have empty : principal.sourceBody.context.assumptions = [] := support.empty
  have emptyDictionary := RecursiveMethodSelectionIdentity.dictionary_empty chosen empty
  let port : Port (compiled := compiled) step context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages) := by
    refine ⟨principal, aligned.1, aligned.2, ?_, support.result, chosen, ?_, _, staged,
      ⟨diagnostics, diagnosticPresent, rfl⟩, ?_, sourceAt⟩
    · change cached.named.inputs.map (fun binding => binding.1.scheme.body) = [coercion.source]
      have inputs := CallablePreparedMethodRuntimeProfileFactory.parameters cached
      have types := congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) inputs
      change step.method.specialized.function.typedBody.inputs.map (fun binder => binder.scheme.body) = _ at types
      simpa only [List.map_map, Function.comp_def] using types.symm.trans support.parameters
    · intro body dictionary selectedActual
      exact RecursiveMethodSelectionIdentity.same_empty catalog
        (fun _ _ first second => unique.contains_unique first second) chosen selectedActual empty
    · change CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
        cached.named.specialized (environment step.dictionary)
      rw [cached.same]
      exact ⟨[], by rw [support.empty]; rfl, emptyDictionary⟩
  exact ⟨⟨port, SelectedCompilationMethodBodySupport.Certified.of_typed principal sourceAt chosenTyped⟩⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionIssuance
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosedCoercionSelection
/-! A finite catalog of closed coercion methods supplies selection support from
original method formation and actual final-plan source shape checks. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosedCoercionSelection
open Core Frontend SourceInference
open CallableCoercionMethodInstantiation (Formation bodyInstance)

open CallableIndexedOwnedPreparedStagedClosedCoercionSelection (Catalog)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available
    scope node policy input coercion output call)

include step in
theorem selection_support     (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (cached : CallablePreparedMethodSelection.Cached compiled step.method.specialized)
    (catalog : Catalog compiled)
    (selected : CallableCoercionSourceSelection.Certificate compiled.sourceProgram caller node available coercion step.method)
    (callerMember : caller ∈ compiled.indexed.base.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (site : coercion ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available) :
    SelectedCompilationCoercionIssuance.Support step selected := by
  let chosen := selected.selected
  have formed : Formation chosen.implementation chosen.declaration :=
    catalog.formed chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  have domain := chosen.domain
  have parameters := catalog.parameters chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  have substitution : step.method.specialized.parameterSubstitution = [] :=
    List.map_eq_nil_iff.mp (domain.trans parameters)
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
      step.method.specialized.parameterSubstitution := by
    intro parameter replacement member
    rw [substitution] at member
    cases member
  have assumptions : step.method.specialized.assumptions = [] := by
    have fields := CallableCoercionBodyProvenance.specialization_fields chosen.specialized
    rw [fields.2]
    change List.map _ (chosen.implementation.methodAssumptions chosen.trait chosen.declaration) = []
    rw [catalog.assumptions chosen.implementation chosen.implementationMember
      chosen.declaration chosen.methodMember chosen.trait chosen.traitMember]
    rfl
  have covered : CallableCoercionEvidenceOrigins.CallerCovered caller step.method := by
    obtain ⟨headers, resolved, assembled, goals⟩ := CallableCoercionEvidenceOrigins.materialized step.materialized
    have dictionary : step.dictionary = [] := List.map_eq_nil_iff.mp (goals.trans assumptions)
    have allEmpty := assembled.symm.trans dictionary
    have headersEmpty : headers = [] := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp allEmpty).1).1
    rw [headersEmpty] at resolved
    have goalsEmpty : step.method.traitPredicates = [] := by
      have lengths := resolved.length_eq
      simpa using lengths
    intro goal member
    rw [goalsEmpty] at member
    cases member
  obtain ⟨definition, _member, _id, instantiated, types, lexical, facts, typing⟩ :=
    SelectedCompilationMethodSelectionTyping.certificate checked bodies cached chosen formed.parameters range
  have shape := catalog.shapes.shape callerMember nodeMember site resolved step.selectedMethod
  exact ⟨formed, range, covered, typing.graph_closed.wellFormed.nodeOccurrencesUnique,
    assumptions, shape.parameters, shape.result⟩

include step in
theorem of_actual
    (methods : Catalog compiled)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (site : coercion ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = CallableNamedMetadata.environment available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty {port : CallableIndexedOwnedPreparedStagedCoercionAuthority.Port (compiled := compiled) step context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages) //
      SelectedCompilationMethodBodySupport.Certified port.principal port.sourceAt} := by
  obtain ⟨selected⟩ := CallableCoercionSourceSelection.of_accepted step.selectedMethod
  have same := CallableCoercionPreparation.step_specialized prepared callerMember nodeMember site resolved step
  have target := step.selected
  rw [same, samePlan] at target
  obtain ⟨cached⟩ := CallablePreparedMethodSelection.cached_row compiled
    (CallableNamedMetadata.specialization_of_exact target).1
  have support := selection_support step checked bodies cached methods selected (samePlan ▸ callerMember) nodeMember site resolved
  exact SelectedCompilationCoercionIssuance.of_actual step selected support checked bodies catalog
    prepared callerMember nodeMember site samePlan globals signatures ledger assumptions resolved unique dictionary actualStages

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosedCoercionSelection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedCollectors
/-! The actual cached implementation and its accepted flow provide native child
typing. The one compiler traversal preserves every reached lexical context and
the selected method's original Source ledger and full dictionary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SelectedCompilationMethodScopedSupport
open CallablePreparedMethodRuntimeProfileFactory (policy)
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {recipe : SourceCoreIndexedSession.Recipe}
  (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (member : entry ∈ compiled.indexed.entries)

include ready member in
/-- The complete physical cache bounds the actual method closure's native slots. -/
theorem body_typed :
    HasType (SourceCoreLocalCell.coreContext (parameterScope principal) ++ nativePrefix principal)
      principal.cached.compilation.body (LanguageResult.resultType principal.named.signature.resultType)
      compiled.indexed.layouts.definitions := by
  have cached := CallableIndexedCachedNativeTyping.prepared_native_closure compiled.indexedPrepared member
    principal.cached.cached (CallableIndexedPreparedInventories.cached_global_at compiled principal.cached.selected)
  have supported := RecursiveNamedCatalogPreparedInitialization.supported_cached ready principal.cached.cached
  rw [principal.cached.compilation.emitted] at cached supported
  have original : HasType ((compiled.indexed.base.globals.map (·.referenceType) ++
      [.cell compiled.indexed.ancestry.layout.frame.type]) ++
        SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      (.lambda principal.named.signature.parameterType (LanguageResult.resultType principal.named.signature.resultType)
        principal.cached.compilation.output)
      principal.named.signature.functionType compiled.indexed.layouts.definitions := by
    simpa only [List.append_assoc, List.singleton_append] using cached
  have minimal := NativeExpressionContextSupport.prefix_typing (targetSuffix := []) original
    (by simpa only [List.length_append, List.length_map, List.length_singleton] using supported)
  cases minimal with
  | lambda _ _ body =>
    simpa only [parameterScope, CallablePreparedMethodRuntimeProfileFactory.scope,
      nativePrefix, List.append_nil, List.append_assoc, List.cons_append] using
      CallableIndexedParameterNativeInversion.body_native principal.cached.compilation body

private def matchContext : SourceCoreCompatibleDataMatches.Context :=
  CompatibleMatchAmbientLowering.withDefinitions
    ⟨.initial compiled.compatible.checked, principal.named.specialized.function.solvedRequirements,
      some (CallableIndexedNamedGeneration.allocator compiled.indexed principal.named), none⟩
    compiled.indexed.layouts.definitions

private theorem match_policy : CompatibleMatchAmbientLowering.PolicySuccess
    (policy principal.cached.compilation) (matchContext principal) := by
  apply CompatibleMatchAmbientLowering.PolicySuccess.extend (by rfl)
  exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

private def invalidProjection (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  principal.cached.diagnostics.placeReason principal.named.signature.key site root none

private def invalidOperand (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (operator : Solcore.Syntax.ValueAssignOp) : Word :=
  if operator = .equal then Word.zero else principal.cached.compilation.own.assignments.reasonAt site root (.value operator)

private def invalidUnary (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  principal.cached.compilation.own.assignments.reasonAt site root .bitNot

private def missingDefault (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) (type : TypeSystem.Ty) : Word :=
  principal.cached.diagnostics.placeReason principal.named.signature.key site root (some type)

private theorem assignments : CompatibleAssignmentStatements.AssignmentPolicy
    (policy principal.cached.compilation) (.initial compiled.compatible.checked)
    (invalidProjection principal) (invalidOperand principal) (missingDefault principal) := by
  refine ⟨rfl, rfl, ?_⟩
  change some _ = some _
  apply congrArg some
  funext expression fuel source scope site assignment operator rhs output next reasonAt
  cases operator <;> rfl

private theorem unaryPolicy : CompatibleBitNotStatements.Policy
    (policy principal.cached.compilation) (.initial compiled.compatible.checked)
    (invalidProjection principal) (invalidUnary principal) (missingDefault principal) := rfl

variable (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)

include ready member signatures certified in
/-- Children retain the complete runtime context fields along actual binders. -/
theorem collected
    {faults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs principal.sourceBody.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator
        (invalidOperand principal site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs principal.sourceBody.source site assignment →
      assignment.target.type = .word → faults (.invalidUnaryOperand .bitNot)
        (invalidUnary principal site assignment.target.root))
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax principal.sourceBody.source expressionSyntax
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType)
    (children : ∀ context, Dynamic.RuntimeContextFields packet.sourceAt.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context →
      expressionSyntax id → principal.sourceBody.source.lookupExpression? id = some node →
      ExpressionHasType principal.sourceBody.source context id node.type →
      (policy principal.cached.compilation).lowerExpression fuel principal.sourceBody.source scope id
        (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ nativePrefix principal)
        lowered.expression nativeType compiled.indexed.layouts.definitions →
      certificates context scope id lowered) :
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected (invalidProjection principal) (missingDefault principal) (faults := faults) compiled.indexed.layouts
      principal.named.signature.key [] compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      (fun error => .sourceAllocation (reprStr error)) (.initial compiled.compatible.checked)
      principal.sourceBody.source expressionSyntax
      (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate principal.sourceBody.source certificates)
      compiled.indexed.layouts.definitions (nativePrefix principal)
      packet.sourceAt.context (parameterScope principal) (.statements true principal.cached.compilation.statements)
      principal.sourceBody.resultType principal.named.signature.resultType packet.flow := by
  have body := body_typed principal ready member
  rw [packet.emitted] at body
  obtain ⟨nativeType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow body
  obtain ⟨_, typed⟩ := SelectedCompilationMethodBodySupport.source_typing
    principal packet.sourceAt certified
  have ownership := typed.local_identity_ownership
  have current := runtime principal packet certified
  exact CallableIndexedOwnedPreparedNativeBranchingCollectors.collected
    (expressionSyntax := expressionSyntax) (certificates := certificates) (LocalView.refl _)
    (by intro id member; cases member) packet.sourceAt.unique rfl
    (by
      intro scope binder monomorphic
      change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
      simp only [SourceCoreGeneralFunctions.contextualBinder, monomorphic, List.isEmpty_nil, ↓reduceIte]
      rfl)
    rfl (assignments principal) (unaryPolicy principal) operands unary (match_policy principal) rfl rfl rfl
    (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    ((CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm ▸ signatures)
    packet.sourceAt.valid.ledger
    (fun context fields scope fuel id node lowered declarations approved _reached found typed accepted nativeType native =>
      children context fields (scope := scope) (fuel := fuel) (id := id) (node := node)
        (lowered := lowered) declarations approved found typed accepted (nativeType := nativeType) native)
    syntaxTree rfl packet.shape (.refl _) current.variables_closed current.residual_variables_open
    packet.sourceAt.signatures (packet.sourceAt.declarations principal.cached.compilation)
    (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
    packet.sourceAt.projection packet.accepted flowTyped

include ready member signatures certified in
/-- The static family is issued from the original compiler callback at each
actual method stage. It contains no execution or body correspondence premise. -/
theorem of_compiler
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs principal.sourceBody.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw semanticFaults operator
        (invalidOperand principal site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs principal.sourceBody.source site assignment →
      assignment.target.type = .word → semanticFaults (.invalidUnaryOperand .bitNot)
        (invalidUnary principal site assignment.target.root))
    {expressionSyntax : ExpressionId → Prop}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax principal.sourceBody.source expressionSyntax
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType)
    (children : ∀ child, stages.Closure principal.sourceFunction child →
      ∀ context, Dynamic.RuntimeContextFields packet.sourceAt.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context →
      expressionSyntax id → principal.sourceBody.source.lookupExpression? id = some node →
      ExpressionHasType principal.sourceBody.source context id node.type →
      (policy principal.cached.compilation).lowerExpression fuel principal.sourceBody.source scope id
        (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ nativePrefix principal)
        lowered.expression nativeType compiled.indexed.layouts.definitions →
      Certificate headers stages semanticFaults context child scope id lowered) :
    Support principal packet headers stages semanticFaults := by
  refine ⟨PreparedAssignmentDiagnosticProducers.cached principal.cached diagnostic
    principal.source_eq.symm packet.sourceAt.unique, ?_⟩
  intro child selected
  rw [stages.source selected]
  exact ⟨expressionSyntax, collected principal packet ready member signatures certified operands unary syntaxTree (children child selected)⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodEvidenceScopedRoots
/-! Authentic direct evidence calls inside selected implementation methods
retain the real caller dictionary and reached lexical ledger. The accepted
method compiler and shared scoped collector supply every child root. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodEvidenceScopedRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SelectedCompilationMethodScopedSupport
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open SelectedCompilationMixedRootSupport (RootAt)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

/-- The initial method profile contains actual references and declaration calls.
The full original node table excludes indirect, indexed and operator-method sites. -/
abbrev DirectSource := CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots.DirectSource

section Resolved
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)
  (sourceForms : DirectSource principal.sourceBody.source)
  {directSites : DeclarationInstantiation → Prop}
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
    compiled.sourceProgram principal.named.specialized principal.dictionary)

local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

private theorem policy_receipt {scope : SourceCoreLocalCell.Scope} {fuel : Nat}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    ∃ predecessor, Nonempty (CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      principal.named principal.cached.diagnostics principal.cached.code principal.cached.compilation
      predecessor principal.sourceBody.source scope id
      (principal.cached.diagnostics.reasonAt principal.named.signature.key) lowered) := by
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext principal.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    principal.cached.compilation.parents principal.cached.compilation.own.assignments principal.cached.diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
    compiled.indexed.base.callableContext none none fuel principal.sourceBody.source scope id
    (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered at accepted
  cases fuel with
  | zero => rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted; cases accepted
  | succ predecessor =>
    exact ⟨predecessor, CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
      principal.cached.compilation principal.record accepted⟩

include diagnostic receiver bodies certified sourceForms supported metadata rows covered resolved in
/-- The actual compiler action and selected scope supply a mixed root with all
readiness obligations derived from original Source forms and full context fields. -/
theorem of_child_with_evidence
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields packet.sourceAt.context context)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    (declarations : CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context)
    (tree : GeneralSyntax principal.sourceBody.source id directSites)
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (typed : ExpressionHasType principal.sourceBody.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    Certificate headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      context child scope id lowered := by
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨predecessor, ⟨root⟩⟩ := policy_receipt principal accepted
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables supported
    metadata scope (principal.cached.diagnostics.reasonAt principal.named.signature.key)
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    packet.sourceAt.unique declarations profile (fun id node tree found => metadata.coercions id tree node found) tree found typed root.selected.accepted
  let result : RootAt compiled headers stages context child scope id lowered
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := RootAt.ofRoot {
    compilerFuel := predecessor + 1
    accepted := by simpa only [sourceEq] using root.selected.accepted
    certificate := by simpa only [sourceEq] using certificate
    node := node
    found := by simpa only [sourceEq] using found
    rawResult := rfl
    typed := by simpa only [sourceEq] using typed
    sameLedger := fields.solvedRequirements.trans packet.sourceAt.valid.ledger
    runtimeLedger := fields.runtimeRequirementLedger packet.sourceAt.valid.runtime
    unique := sourceEq ▸ packet.sourceAt.unique
    catalog := bodies.signatures
    runtime := by simpa only [sourceEq] using (runtime principal packet certified).transport fields
    covers := by rw [stages.evidence selected]; exact fields.covers packet.sourceAt.valid.covers
    actualFunctionType := by rw [root.callables]; rfl
    uninitialized := by
      intro current id code read _reached location
      exact CallableIndexedOwnedPreparedStagedMethodTerminalSupport.uninitialized principal diagnostic receiver
        packet.sourceAt.unique (by simpa only [sourceEq] using read) location
    callsReady := by
      intro callFuel callScope callId callee ids callMetadata code compiler _path
      rcases sourceForms callId compiler.original (by simpa only [sourceEq] using compiler.found) with
        ⟨name, resolution, form⟩ | ⟨actualCallee, arguments, instantiation, form⟩ <;>
        have impossible := compiler.originalForm <;> simp [form] at impossible
    directReady := by
      intro callFuel callScope callId callee ids instantiation code compiler path
      have originalTree : GeneralSyntax child.source id directSites := by simpa only [sourceEq] using tree
      have childMetadata : MetadataFor compiled.indexed principal.named child.source directSites := by
        simpa only [sourceEq] using metadata
      have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path originalTree
      have site := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax.direct_site
        actualTree compiler.metadata.found compiler.form
      obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory_at compiler rows
        (covered instantiation site compiler.index compiler.signature compiler.target compiler.global) rfl
      rcases CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.accepted_direct_action
        root.compilerPolicy childMetadata actualTree compiler.metadata.found compiler.form compiler.accepted with bypass | authentic
      · obtain ⟨requirements, assumptions⟩ :=
          CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct
            compiler.metadata.found compiler.form bypass
        have special := fun callback budget =>
          (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.direct_hook root.compilerPolicy
            childMetadata actualTree compiler.metadata.found compiler.form callback budget callScope
            (principal.cached.diagnostics.reasonAt principal.named.signature.key)).trans
            (CallableCallEvidenceCertificates.direct_bypass compiler.metadata.found compiler.form requirements
              compiler.metadata.coercions assumptions)
        have ordinary := compiler.ordinary special
          (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy root.compilerPolicy childMetadata actualTree)
        exact ⟨⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
          compiler port ordinary requirements context child.evidence⟩,
          SelectedCompilationCatalog.certificates bodies rows port.header port.member,
          SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member⟩⟩
      · obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
          compiler.metadata.found compiler.form authentic
        rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at actual
        let caller := CallableIndexedOwnedPreparedStagedMethodCallerResolvedEvidence.of_selected
          principal packet.sourceAt resolved selected fields
        exact ⟨⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence_of_resolved
          compiler port actual caller.resolved caller.signatures caller.ledger caller.assumptions caller.unique⟩,
          SelectedCompilationCatalog.certificates bodies rows port.header port.member,
          SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member⟩⟩
    indexReady := by
      intro indexScope indexId base key actual baseNode keyNode layout comparison first second indexed _keyFound form _sourceType _path
      rcases sourceForms indexId actual (by simpa only [sourceEq] using indexed.metadata.found) with
        ⟨name, resolution, nodeForm⟩ | ⟨callee, arguments, instantiation, nodeForm⟩ <;> simp [nodeForm] at form
    methodReady := by
      intro callFuel callScope callId code compiler _path
      rcases sourceForms callId compiler.node (by simpa only [sourceEq] using compiler.metadata.found) with
        ⟨name, resolution, nodeForm⟩ | ⟨callee, arguments, instantiation, nodeForm⟩
      all_goals
        rcases compiler.operator.form with ⟨op, operand, form, _arguments⟩ | ⟨op, left, right, form, _arguments⟩ <;>
          simp [nodeForm] at form }
  exact ⟨result, rfl⟩

include diagnostic receiver bodies certified sourceForms supported metadata rows covered resolved in
/-- The original scoped grammar and actual method compiler provide every child. -/
theorem of_actual_with_evidence
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {stages : Staging.Recursive.Registry}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax principal.sourceBody.source
      (fun id => GeneralSyntax principal.sourceBody.source id directSites)
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType) :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  have operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs principal.sourceBody.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) operator
        (GenericAssignmentDiagnostics.token principal.cached.compilation.own.assignments site assignment.target.root operator) := by
    intro site assignment operator rhs origin profile
    obtain ⟨first, prepared⟩ := CallableIndexedOwnedAssignmentProvenance.method_assignments principal diagnostic
    exact PreparedBranchingAssignmentDiagnostics.operands prepared
      (fun _ _ represented => CallableIndexedOwnedAssignmentProvenance.cached_operands
        principal.cached diagnostic receiver represented) origin profile
  have unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs principal.sourceBody.source site assignment →
      assignment.target.type = .word → CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
        (.invalidUnaryOperand .bitNot)
        (GenericAssignmentUnaryDiagnostics.unaryToken principal.cached.compilation.own.assignments site assignment.target.root) := by
    intro site assignment origin rawWord
    obtain ⟨first, prepared⟩ := CallableIndexedOwnedAssignmentProvenance.method_assignments principal diagnostic
    exact GenericAssignmentUnaryDiagnostics.prepared_unary_included prepared
      (fun _ _ represented => CallableIndexedOwnedPublicUnaryAssignmentDiagnostics.cached_unary
        principal.cached diagnostic receiver represented) origin rawWord
  apply SelectedCompilationMethodScopedCollectors.of_compiler principal packet ready member bodies.signatures certified diagnostic operands unary syntaxTree
  intro child selected context fields scope fuel id node lowered declarations tree found typed accepted _nativeType _native
  exact of_child_with_evidence principal packet diagnostic receiver bodies certified sourceForms supported metadata rows covered resolved selected fields
    declarations tree found typed accepted

end Resolved

section Generic
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)
  (sourceForms : DirectSource principal.sourceBody.source)
  {directSites : DeclarationInstantiation → Prop}
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (catalog : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)

local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

private def resolved_generic :
    CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
      compiled.sourceProgram principal.named.specialized principal.dictionary := by
  have empty := CallableIndexedOwnedPreparedStagedMethodCallerEvidence.assumptions_empty_generic principal catalog
  have dictionary := RecursiveMethodSelectionIdentity.dictionary_empty principal.selected empty
  have callerEmpty : principal.named.specialized.assumptions = [] := by
    rw [principal.cached.same]
    exact empty
  refine ⟨[], ?_, dictionary⟩
  rw [callerEmpty]
  rfl

include diagnostic receiver bodies certified sourceForms supported metadata rows covered catalog in
theorem of_child_generic
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields packet.sourceAt.context context)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    (declarations : CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context)
    (tree : GeneralSyntax principal.sourceBody.source id directSites)
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (typed : ExpressionHasType principal.sourceBody.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    Certificate headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      context child scope id lowered := by
  exact of_child_with_evidence principal packet diagnostic receiver bodies certified sourceForms supported metadata rows covered
    (resolved_generic principal catalog) selected fields declarations tree found typed accepted

include diagnostic receiver bodies certified sourceForms supported metadata rows covered catalog in
theorem of_actual_generic
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {stages : Staging.Recursive.Registry}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax principal.sourceBody.source
      (fun id => GeneralSyntax principal.sourceBody.source id directSites)
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType) :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  exact of_actual_with_evidence principal packet diagnostic receiver bodies certified sourceForms supported metadata rows covered
    (resolved_generic principal catalog) ready member syntaxTree

end Generic


section Legacy
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)
  (sourceForms : DirectSource principal.sourceBody.source)
  {directSites : DeclarationInstantiation → Prop}
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (catalog : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)

local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

include diagnostic receiver bodies certified sourceForms supported metadata rows covered catalog in
theorem of_child
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields packet.sourceAt.context context)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    (declarations : CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context)
    (tree : GeneralSyntax principal.sourceBody.source id directSites)
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (typed : ExpressionHasType principal.sourceBody.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    Certificate headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      context child scope id lowered := by
  exact of_child_generic principal packet diagnostic receiver bodies certified sourceForms supported metadata rows covered
    (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed catalog) selected fields
    declarations tree found typed accepted

include diagnostic receiver bodies certified sourceForms supported metadata rows covered catalog in
theorem of_actual
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {stages : Staging.Recursive.Registry}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax principal.sourceBody.source
      (fun id => GeneralSyntax principal.sourceBody.source id directSites)
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType) :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  exact of_actual_generic principal packet diagnostic receiver bodies certified sourceForms supported metadata rows covered
    (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed catalog) ready member syntaxTree

end Legacy

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodEvidenceScopedRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosedCoercionSourceSelection
/-! Actual method selection and dictionary materialization determine the
original Source coercion rule before either body executes. Closed catalog
facts discharge formation, full substitution range and caller coverage. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosedCoercionSourceSelection
open Core Frontend SourceInference
open CallableCoercionMethodInstantiation (Formation bodyInstance)
open CallableNamedMetadata (environment)

theorem selects {compiled : SourceCoreUnifiedCompilation.Compiled}
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
    {context : SourceSemantics.Context}
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (catalog : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
    (accepted : SourceCompilationPlan.checkedCoercionMethod compiled.sourceProgram caller node available step = .ok method)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment
      compiled.sourceProgram caller.key caller.assumptions = .ok available)
    (materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence
      compiled.sourceProgram caller node step method = .ok dictionary)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions) :
    Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context
      (environment available) "Coerce" "coerce" (step.requirement :: step.methodRequirements)
      (bodyInstance compiled.sourceProgram method) (environment dictionary) := by
  obtain ⟨receipt⟩ := CallableCoercionSourceSelection.of_accepted accepted
  let chosen := receipt.selected
  have formed : Formation chosen.implementation chosen.declaration :=
    catalog.formed chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  have parameters := catalog.parameters chosen.implementation chosen.implementationMember
    chosen.declaration chosen.methodMember
  have substitution : method.specialized.parameterSubstitution = [] :=
    List.map_eq_nil_iff.mp (chosen.domain.trans parameters)
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
      method.specialized.parameterSubstitution := by
    intro parameter replacement member
    rw [substitution] at member
    cases member
  have methodAssumptions : method.specialized.assumptions = [] := by
    rw [(CallableCoercionBodyProvenance.specialization_fields chosen.specialized).2]
    change List.map _ (chosen.implementation.methodAssumptions chosen.trait chosen.declaration) = []
    rw [catalog.assumptions chosen.implementation chosen.implementationMember
      chosen.declaration chosen.methodMember chosen.trait chosen.traitMember]
    rfl
  have covered : CallableCoercionEvidenceOrigins.CallerCovered caller method := by
    obtain ⟨headers, origins, assembled, goals⟩ := CallableCoercionEvidenceOrigins.materialized materialized
    have dictionaryEmpty : dictionary = [] := List.map_eq_nil_iff.mp (goals.trans methodAssumptions)
    have allEmpty := assembled.symm.trans dictionaryEmpty
    have headersEmpty : headers = [] :=
      (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp allEmpty).1).1
    rw [headersEmpty] at origins
    have traitPredicatesEmpty : method.traitPredicates = [] := by
      have lengths := origins.length_eq
      simpa using lengths
    intro goal member
    rw [traitPredicatesEmpty] at member
    cases member
  exact receipt.selects checked formed range signatures ledger assumptions resolved covered materialized

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosedCoercionSourceSelection
end
