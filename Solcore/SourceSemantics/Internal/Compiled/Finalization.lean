import Solcore.SourceSemantics.Internal.Compiled.Origins
import Solcore.SourceSemantics.Internal.Inference.Soundness
import Solcore.Frontend.SourceInference.Internal.DirectCallInference
import Solcore.Frontend.SourceInference.Internal.DirectCallPredicates
import Solcore.SourceSemantics.Internal.Inference.GeneralizationBarriers
import Solcore.SourceSemantics.Internal.Selected.StatementReferences
import Solcore.Frontend.Internal.CheckingProperties
import Solcore.SourceSemantics.Internal.Formation.NormalizedCalls
import Lean
import Solcore.SourceSemantics.Internal.Substitution.StructuralLaws

/-!
# Finalization of selected bodies

One successful body check keeps its inference, return unification and finalization. Cataloged calls,
direct-call predicates, generalization boundaries and normalized formation follow from that receipt,
and so does the non-template ledger of specialization.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalFinalization
/-! One successful body check retains its actual inference, return unification
and finalization. The reusable solver resources come from that finalizer;
neither declarative body typing nor monomorphic locals are assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness

def context (environment : ProgramEnvironment) (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature) (declaration : ProgramDeclaration) : SourceInference.Context :=
  { environment, signatures, scope := .ofDeclaration declaration,
    typeParameters := signature.scheme.parameters, assumptions := signature.scheme.predicates }

def initial (signature : ProgramFunctionSignature) (declaration : ProgramDeclaration) : State :=
  State.initial declaration.id
    ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
      (parameter.1, Scheme.mono parameter.2)) signature.parameterComptime

structure BodyReceipt (environment : ProgramEnvironment) (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature) (fuel : Nat) (checked : CheckedFunction) where
  accepted : checkFunctionBody environment signatures signature fuel = .ok checked
  declaration : ProgramDeclaration
  body : Detail.BlockResult
  returned : State
  finalized : SourceInference.Result
  declared : environment.declaration? signature.id = some declaration
  inferred : Detail.inferStatementsFuel fuel (context environment signatures signature declaration)
    signature.source.value.body.value (Ty.productMany signature.returnTypes)
    (initial signature declaration) = .ok body
  unified : Detail.unify body.state body.type (Ty.productMany signature.returnTypes) = .ok returned
  finalization : Detail.finalize (context environment signatures signature declaration)
    (Ty.productMany signature.returnTypes) returned (body.statements.map NodeId.statement) = .ok finalized
  checkedResult : checked = {
    declaration := signature.id
    type := signature.scheme.body
    inferredBodyType := finalized.type
    returnComptime := signature.returnComptime
    substitution := finalized.substitution
    solvedRequirements := finalized.solvedRequirements
    typedBody := finalized.typedSource }

namespace BodyReceipt
variable {environment : ProgramEnvironment} {signatures : ProgramSignatures}
  {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}

theorem of_check (accepted : checkFunctionBody environment signatures signature fuel = .ok checked) :
    Nonempty (BodyReceipt environment signatures signature fuel checked) := by
  obtain ⟨declaration, body, returned, finalized, declared, inferred, unified, finalization, result⟩ :=
    checkFunctionBody_success_witness accepted
  exact ⟨⟨accepted, declaration, body, returned, finalized, declared, inferred, unified, finalization, result⟩⟩

def resources (receipt : BodyReceipt environment signatures signature fuel checked) :
    FinalInferenceResources (context environment signatures signature receipt.declaration)
      (Ty.productMany signature.returnTypes) receipt.returned
      (receipt.body.statements.map NodeId.statement) receipt.finalized :=
  FinalInferenceResources.ofFinalize receipt.finalization

theorem returned_nodes (receipt : BodyReceipt environment signatures signature fuel checked) :
    receipt.returned.nodes = receipt.body.state.nodes :=
  (Detail.unify_occurrenceState_eq receipt.unified).1

theorem returned_requirements (receipt : BodyReceipt environment signatures signature fuel checked) :
    receipt.returned.requirements = receipt.body.state.requirements :=
  Detail.unify_requirements_eq receipt.unified

theorem solver_requirements (receipt : BodyReceipt environment signatures signature fuel checked) :
    receipt.resources.finalState.requirements = receipt.body.state.requirements :=
  receipt.resources.requirements_eq.trans receipt.returned_requirements

theorem substitution (receipt : BodyReceipt environment signatures signature fuel checked) :
    checked.substitution = receipt.finalized.substitution :=
  congrArg CheckedFunction.substitution receipt.checkedResult

theorem solved (receipt : BodyReceipt environment signatures signature fuel checked) :
    checked.solvedRequirements = receipt.finalized.solvedRequirements :=
  congrArg CheckedFunction.solvedRequirements receipt.checkedResult

theorem source (receipt : BodyReceipt environment signatures signature fuel checked) :
    checked.typedBody = receipt.finalized.typedSource :=
  congrArg CheckedFunction.typedBody receipt.checkedResult

theorem source_nodes (receipt : BodyReceipt environment signatures signature fuel checked) :
    checked.typedBody.nodes = receipt.body.state.nodes.map (Node.applySubstitution receipt.finalized.substitution) := by
  rw [receipt.source, receipt.resources.source_eq]
  change receipt.returned.nodes.map (Node.applySubstitution receipt.finalized.substitution) = _
  rw [receipt.returned_nodes]

end BodyReceipt
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledSelectedFinalization
/-! Selected compilation exposes the original checked body and its actual
finalizer together, before parameter specialization. All states, substitutions
and solved rows belong to that one successful checking computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem

structure Selected (compiled : SourceCoreCompiler.Compiled)
    (row : SourceSpecialization.SpecializedFunction) (fuel : Nat) where
  original : CheckedFunction
  originalMember : original ∈ compiled.program.functions
  signature : ProgramFunctionSignature
  signatureMember : signature ∈ compiled.program.signatures.functions
  body : BodyReceipt compiled.program.environment compiled.program.signatures signature fuel original
  specialized : row.function = SourceSpecialization.applyCheckedFunction row.parameterSubstitution original

theorem of_compile {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    Nonempty (Selected compiled row options.checkingFuel) := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  have lowered : SourceCoreCompiler.compileChecked compiled.program seeds options = .ok compiled := by
    simpa only [SourceCoreCompiler.compile, checked, Except.mapError, bind, Except.bind] using accepted
  obtain ⟨requests, ran⟩ := SourceCompiledLocalReadOrigins.compileChecked_worklist lowered
  obtain ⟨original, originalMember, selectedSignature, supplied, specialized⟩ :=
    SourceSpecializationWorklist.run_original ran member
  obtain ⟨signature, signatureMember, bodyChecked⟩ := checkProgram_success_function_body checked originalMember
  obtain ⟨body⟩ := BodyReceipt.of_check bodyChecked
  exact ⟨⟨original, originalMember, signature, signatureMember, body,
    SourceCompiledLocalReadOrigins.specializeFunction_applied specialized⟩⟩

namespace Selected
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem source (receipt : Selected compiled row fuel) :
    row.function.typedBody = SourceSpecialization.applyTypedSource row.parameterSubstitution
      receipt.body.finalized.typedSource := by
  rw [receipt.specialized, ← receipt.body.source]
  rfl

theorem solved (receipt : Selected compiled row fuel) :
    row.function.solvedRequirements = receipt.body.finalized.solvedRequirements.map
      (SourceSpecialization.applySolvedRequirement row.parameterSubstitution) := by
  rw [receipt.specialized, ← receipt.body.solved]
  rfl

end Selected
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledTemplateCallOrigins
/-! Every finalized classified template in an actually checked selected body
retains its original declaration-call emitter. This removes the direct-ID
membership premise from the selected-row endpoint. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledTemplateCallOrigins
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization DirectCallEvents

namespace BodyReceipt
variable {environment : ProgramEnvironment} {signatures : ProgramSignatures}
  {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}

theorem classified (receipt : BodyReceipt environment signatures signature fuel checked) :
    ClassifiedCallEvents.Classified receipt.returned :=
  ClassifiedCallEvents.Progress.unify receipt.unified
    (ClassifiedCallEvents.initializedStatements_classified receipt.inferred)

theorem direct_origins (receipt : BodyReceipt environment signatures signature fuel checked) :
    Origins receipt.returned :=
  Progress.unify receipt.unified (initializedStatements_origins receipt.inferred)

theorem finalized_template_direct
    (receipt : BodyReceipt environment signatures signature fuel checked)
    {id : RequirementId} (member : id ∈ sourceLocalSchemeTemplateIds receipt.finalized.typedSource) :
    id ∈ receipt.returned.directCallRequirements :=
  classified receipt ((finalize_templateIdsAligned_validated receipt.finalization id).mp member)

theorem finalized_template_emitter
    (receipt : BodyReceipt environment signatures signature fuel checked)
    {id : RequirementId} (member : id ∈ sourceLocalSchemeTemplateIds receipt.finalized.typedSource) :
    HasCall receipt.finalized.typedSource.nodes id := by
  have emitter := direct_origins receipt id (finalized_template_direct receipt member)
  rw [receipt.resources.source_eq]
  exact SourceCompiledDirectCallOrigins.solved_call emitter receipt.finalized.substitution

end BodyReceipt

/-- The same actual selected receipt supplies all source-template emitters,
including templates owned by nested local binders. -/
theorem selected_template_emitter
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) {id : RequirementId}
    (member : id ∈ sourceLocalSchemeTemplateIds row.function.typedBody) :
    HasCall row.function.typedBody.nodes id := by
  rw [selected.source] at member ⊢
  have original : id ∈ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource := by
    change id ∈ sourceLocalSchemeTemplateIds (StructuralSubstitution.applyTypedSource row.parameterSubstitution selected.body.finalized.typedSource) at member
    simpa only [StructuralSubstitution.sourceLocalSchemeTemplateIds_applyTypedSource] using member
  exact SourceCompiledDirectCallOrigins.specialized_call
    (BodyReceipt.finalized_template_emitter selected.body original) row.parameterSubstitution

/-- Raw public compilation itself supplies the checked body and provenance;
there is no direct-ID, body-typing, or ownership premise. -/
theorem compile_template_emitters
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∀ id ∈ sourceLocalSchemeTemplateIds row.function.typedBody,
      HasCall row.function.typedBody.nodes id := by
  obtain ⟨selected⟩ := SourceCompiledLocalFinalization.of_compile accepted member
  exact fun _ present => selected_template_emitter selected present

end Solcore.SourceSemantics.SourceCompiledTemplateCallOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledCatalogedCallOrigins
/-! The actual selected declaration catalog follows every finalized template
emitter through solving and specialization. No source body typing is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledCatalogedCallOrigins
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open SourceCompiledLocalFinalization CatalogedDirectCallEvents

variable {catalog : List Resolved.DeclarationId}

theorem solved_call {nodes : List Node} {requirement : RequirementId}
    (emitter : HasCall catalog nodes requirement) (substitution : Substitution) :
    HasCall catalog (nodes.map (Node.applySubstitution substitution)) requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued, cataloged⟩ := emitter
  refine ⟨node.applySubstitution substitution,
    List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, instantiation.applySubstitution substitution, ?_, issued, cataloged⟩
  change node.form.applySubstitution substitution = _
  rw [form]
  rfl

theorem specialized_call {source : TypedSource} {requirement : RequirementId}
    (emitter : HasCall catalog source.nodes requirement) (substitution : ParameterSubstitution) :
    HasCall catalog (SourceSpecialization.applyTypedSource substitution source).nodes requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued, cataloged⟩ := emitter
  refine ⟨SourceSpecialization.applyExpressionNode substitution node,
    List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, SourceSpecialization.applyInstantiation substitution instantiation, ?_, issued, cataloged⟩
  change SourceSpecialization.applyExpressionForm substitution node.form = _
  rw [form]
  rfl

namespace BodyReceipt
variable {environment : ProgramEnvironment} {signatures : ProgramSignatures}
  {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}

theorem direct_origins (receipt : BodyReceipt environment signatures signature fuel checked) :
    Origins (signatures.functions.map (·.id)) receipt.returned :=
  Progress.unify receipt.unified (initializedStatements_origins receipt.inferred)

theorem finalized_template_emitter
    (receipt : BodyReceipt environment signatures signature fuel checked)
    {id : RequirementId} (member : id ∈ sourceLocalSchemeTemplateIds receipt.finalized.typedSource) :
    HasCall (signatures.functions.map (·.id)) receipt.finalized.typedSource.nodes id := by
  have emitter := direct_origins receipt id (SourceCompiledTemplateCallOrigins.BodyReceipt.finalized_template_direct receipt member)
  rw [receipt.resources.source_eq]
  exact solved_call emitter receipt.finalized.substitution

end BodyReceipt

/-- The same actual selected receipt supplies all source-template emitters,
including templates owned by nested local binders. -/
theorem selected_template_emitter
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) {id : RequirementId}
    (member : id ∈ sourceLocalSchemeTemplateIds row.function.typedBody) :
    HasCall (compiled.program.signatures.functions.map (·.id)) row.function.typedBody.nodes id := by
  rw [selected.source] at member ⊢
  have original : id ∈ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource := by
    change id ∈ sourceLocalSchemeTemplateIds (StructuralSubstitution.applyTypedSource row.parameterSubstitution selected.body.finalized.typedSource) at member
    simpa only [StructuralSubstitution.sourceLocalSchemeTemplateIds_applyTypedSource] using member
  exact specialized_call
    (BodyReceipt.finalized_template_emitter selected.body original) row.parameterSubstitution

theorem receipt_ready_origins
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (origins : Origins (context.signatures.functions.map (·.id)) initial) :
    Origins (context.signatures.functions.map (·.id)) receipt.ready :=
  inferExprFuel_origins_progress receipt.child origins

/-- Raw public compilation itself supplies the checked body and provenance;
there is no direct-ID, body-typing, or ownership premise. -/
theorem compile_template_emitters
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∀ id ∈ sourceLocalSchemeTemplateIds row.function.typedBody,
      HasCall (compiled.program.signatures.functions.map (·.id)) row.function.typedBody.nodes id := by
  obtain ⟨selected⟩ := SourceCompiledLocalFinalization.of_compile accepted member
  exact fun _ present => selected_template_emitter selected present

end Solcore.SourceSemantics.SourceCompiledCatalogedCallOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledDirectCallPredicateOrigins
/-! Actual direct-call issuance is paired with the same raw ledger predicate,
then transported through the selected finalizer and rigid specialization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledDirectCallPredicateOrigins
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open SourceCompiledLocalFinalization DirectCallPredicateEvents

variable {catalog : List Resolved.DeclarationId}

theorem solved_call {nodes : List Node} {requirement : Requirement}
    (emitter : HasCall catalog nodes requirement) (substitution : Substitution) :
    HasCall catalog (nodes.map (Node.applySubstitution substitution))
      { requirement with predicate := TypedTraitResolution.applySubstitution substitution requirement.predicate } := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued, cataloged, predicate⟩ := emitter
  refine ⟨node.applySubstitution substitution,
    List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, instantiation.applySubstitution substitution, ?_, issued, cataloged,
    List.mem_map.mpr ⟨requirement.predicate, predicate, rfl⟩⟩
  change node.form.applySubstitution substitution = _
  rw [form]
  rfl

theorem specialized_call {source : TypedSource} {requirement : Requirement}
    (emitter : HasCall catalog source.nodes requirement) (substitution : ParameterSubstitution) :
    HasCall catalog (SourceSpecialization.applyTypedSource substitution source).nodes
      { requirement with predicate := ProgramPredicate.applyParameters substitution requirement.predicate } := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued, cataloged, predicate⟩ := emitter
  refine ⟨SourceSpecialization.applyExpressionNode substitution node,
    List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, SourceSpecialization.applyInstantiation substitution instantiation, ?_, issued, cataloged,
    List.mem_map.mpr ⟨requirement.predicate, predicate, rfl⟩⟩
  change SourceSpecialization.applyExpressionForm substitution node.form = _
  rw [form]
  rfl

private theorem solved_row_of_requirement_mem
    {inferenceContext : SourceInference.Context} {state : State}
    {requirements : List Requirement} {solved : List SolvedRequirement}
    (corresponds : Forall₂ (fun requirement row =>
      row.id = requirement.id ∧
        row.predicate = Detail.applyPredicate state requirement.predicate ∧
        Detail.solveRequirementEvidence inferenceContext state requirement = .ok row.evidence)
      requirements solved)
    {requirement : Requirement} (member : requirement ∈ requirements) :
    ∃ row, row ∈ solved ∧ row.id = requirement.id ∧
      row.predicate = Detail.applyPredicate state requirement.predicate := by
  induction corresponds with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, head.1, head.2.1⟩
    · obtain ⟨row, present, same, predicate⟩ := ih member
      exact ⟨row, List.mem_cons_of_mem _ present, same, predicate⟩

namespace BodyReceipt
variable {environment : ProgramEnvironment} {signatures : ProgramSignatures}
  {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}

theorem direct_origins (receipt : BodyReceipt environment signatures signature fuel checked) :
    Origins (signatures.functions.map (·.id)) receipt.returned :=
  Progress.unify receipt.unified (initializedStatements_origins receipt.inferred)

/-- Both the ledger row and the call instantiation come from the same actual
inference. The node's extra coercion IDs are never used to infer its predicate. -/
theorem raw_template_emitter
    (receipt : BodyReceipt environment signatures signature fuel checked)
    {id : RequirementId} (member : id ∈ sourceLocalSchemeTemplateIds receipt.finalized.typedSource) :
    ∃ requirement ∈ receipt.returned.requirements, requirement.id = id ∧
      HasCall (signatures.functions.map (·.id)) receipt.returned.nodes requirement :=
  direct_origins receipt id
    (SourceCompiledTemplateCallOrigins.BodyReceipt.finalized_template_direct receipt member)

theorem finalized_direct_emitter
    (receipt : BodyReceipt environment signatures signature fuel checked)
    {id : RequirementId} (member : id ∈ receipt.returned.directCallRequirements) :
    ∃ solved ∈ receipt.finalized.solvedRequirements, solved.id = id ∧
      HasCall (signatures.functions.map (·.id)) receipt.finalized.typedSource.nodes
        { id, predicate := solved.predicate } := by
  obtain ⟨requirement, present, same, call⟩ := direct_origins receipt id member
  have solverMember : requirement ∈ receipt.resources.finalState.requirements := by
    rw [receipt.resources.requirements_eq]
    exact present
  obtain ⟨solved, solvedMember, solvedId, predicate⟩ :=
    solved_row_of_requirement_mem (solveRequirements_corresponds receipt.resources.solve_success) solverMember
  refine ⟨solved, solvedMember, solvedId.trans same, ?_⟩
  have predicateEq : solved.predicate =
      TypedTraitResolution.applySubstitution receipt.finalized.substitution requirement.predicate := by
    rw [predicate, receipt.resources.substitution_eq]
    rfl
  rw [receipt.resources.source_eq, predicateEq, ← same]
  exact solved_call call receipt.finalized.substitution

theorem finalized_template_emitter
    (receipt : BodyReceipt environment signatures signature fuel checked)
    {id : RequirementId} (member : id ∈ sourceLocalSchemeTemplateIds receipt.finalized.typedSource) :
    ∃ solved ∈ receipt.finalized.solvedRequirements, solved.id = id ∧
      HasCall (signatures.functions.map (·.id)) receipt.finalized.typedSource.nodes
        { id, predicate := solved.predicate } :=
  finalized_direct_emitter receipt
    (SourceCompiledTemplateCallOrigins.BodyReceipt.finalized_template_direct receipt member)

end BodyReceipt

theorem selected_template_emitter
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) {id : RequirementId}
    (member : id ∈ sourceLocalSchemeTemplateIds row.function.typedBody) :
    ∃ solved ∈ row.function.solvedRequirements, solved.id = id ∧
      HasCall (compiled.program.signatures.functions.map (·.id)) row.function.typedBody.nodes
        { id, predicate := solved.predicate } := by
  rw [selected.source] at member
  have original : id ∈ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource := by
    change id ∈ sourceLocalSchemeTemplateIds
      (StructuralSubstitution.applyTypedSource row.parameterSubstitution selected.body.finalized.typedSource) at member
    simpa only [StructuralSubstitution.sourceLocalSchemeTemplateIds_applyTypedSource] using member
  obtain ⟨solved, present, same, call⟩ := BodyReceipt.finalized_template_emitter selected.body original
  refine ⟨SourceSpecialization.applySolvedRequirement row.parameterSubstitution solved, ?_, same, ?_⟩
  · rw [selected.solved]
    exact List.mem_map.mpr ⟨solved, present, rfl⟩
  · rw [selected.source]
    exact specialized_call call row.parameterSubstitution

theorem receipt_ready_origins
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (origins : Origins (context.signatures.functions.map (·.id)) initial) :
    Origins (context.signatures.functions.map (·.id)) receipt.ready :=
  inferExprFuel_origins_progress receipt.child origins

/-- Raw compilation supplies the actual selected body and all issuance facts. -/
theorem compile_template_emitters
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∀ id ∈ sourceLocalSchemeTemplateIds row.function.typedBody,
      ∃ solved ∈ row.function.solvedRequirements, solved.id = id ∧
        HasCall (compiled.program.signatures.functions.map (·.id)) row.function.typedBody.nodes
          { id, predicate := solved.predicate } := by
  obtain ⟨selected⟩ := SourceCompiledLocalFinalization.of_compile accepted member
  exact fun _ present => selected_template_emitter selected present

end Solcore.SourceSemantics.SourceCompiledDirectCallPredicateOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledFinalizedGeneralizationBoundaries
/-! Original inference, generalization, finalization and parameter
specialization share one actual checking witness. The finalizer's capture
validation applies to the same original binder identified by the worklist. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceCompiledLocalGeneralizationEvents LocalGeneralizationBoundaries

namespace Selected
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

/-- Build the inference receipt from this finalizer's own body and substitution. -/
def inferenceReceipt (selected : Selected compiled row fuel) : InferredSelectedBody compiled row fuel := by
  have ready : LocalGeneralizationEvents.Ready (initial selected.signature selected.body.declaration) := by
    refine ⟨State.initial_requirementsWellFormed _ _ _, ?_, ?_⟩
    · intro id impossible
      exact False.elim (List.not_mem_nil impossible)
    · intro node impossible
      exact False.elim (List.not_mem_nil impossible)
  refine {
    original := selected.original
    originalMember := selected.originalMember
    signature := selected.signature
    signatureMember := selected.signatureMember
    declaration := selected.body.declaration
    declared := selected.body.declared
    body := selected.body.body
    substitution := selected.body.finalized.substitution
    inferred := selected.body.inferred
    solved := selected.body.source_nodes
    specialized := ?_
    events := LocalGeneralizationEvents.inferStatementsFuel_origins selected.body.inferred ready
      LocalGeneralizationEvents.Origins.empty
  }
  rw [selected.specialized]
  rfl

theorem inference_body (selected : Selected compiled row fuel) :
    selected.inferenceReceipt.body = selected.body.body := rfl

theorem inference_substitution (selected : Selected compiled row fuel) :
    selected.inferenceReceipt.substitution = selected.body.finalized.substitution := rfl

/-- Return-type unification is an actual continuation of the body and keeps
its retired-local boundary. -/
theorem returned_boundary (selected : Selected compiled row fuel) {binding : LocalLambdaBinding}
    (event : BoundedBindingEvent selected.inferenceReceipt binding) :
    OriginSince selected.inferenceReceipt.initialState.nextLocal selected.body.returned
      event.originalBinder binding.initializer :=
  event.boundary.progress (LocalReadScopeProgress.Progress.unify selected.body.unified)

/-- The finalizer validates capture avoidance for this exact original binder.
Its membership follows from the retained initialized statement occurrence. -/
theorem binding_no_capture (selected : Selected compiled row fuel) {binding : LocalLambdaBinding}
    (event : BoundedBindingEvent selected.inferenceReceipt binding) :
    Detail.LocalBinderInstantiationNoCapture selected.body.finalized.substitution event.originalBinder := by
  apply selected.body.resources.local_no_capture
  unfold TypedSource.initializedLetBinders
  apply List.mem_flatMap.mpr
  refine ⟨.statement event.original, ?_, ?_⟩
  · change .statement event.original ∈ selected.body.returned.nodes
    rw [selected.body.returned_nodes]
    exact event.originalPresent
  · simp only [Node.initializedLetBinders, event.originalForm, StatementForm.initializedLetBinders]
    exact List.mem_singleton_self _

end Selected

structure FinalizedBindingEvent {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : Selected compiled row fuel) (binding : LocalLambdaBinding)
    extends BoundedBindingEvent receipt.inferenceReceipt binding where
  noCapture : Detail.LocalBinderInstantiationNoCapture receipt.body.finalized.substitution originalBinder

/-- Accepted compilation supplies actual local discovery and one shared
checker/finalizer witness for all returned generalization boundaries. -/
theorem compile_finalized_binding_boundaries {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∃ instances, localLambdaInstances row.function.typedBody = .ok instances ∧
        ∀ value ∈ instances,
          value.binding ∈ localLambdaBindings row.function.typedBody ∧
          LocalLambdaInstance.ReadOrigin row.function.typedBody value ∧
          Nonempty (FinalizedBindingEvent selected value.binding) := by
  obtain ⟨selected⟩ := of_compile accepted member
  obtain ⟨instances, discovered, bindings⟩ := SourceCompiledLocalBindings.compile_binding_origins accepted member
  refine ⟨selected, instances, discovered, ?_⟩
  intro value present
  have binding := bindings value present
  obtain ⟨event⟩ := selected.inferenceReceipt.binding_boundary binding.1
  exact ⟨binding.1, binding.2.1, ⟨{
    toBoundedBindingEvent := event
    noCapture := selected.binding_no_capture event
  }⟩⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedInitializerContexts
/-! The selected worklist's original binder enters the initializer context of
the same successful finalizer. Retained source membership and the parent-child
edge are derived from its actual inference receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness SourceSpecializationWorklist

namespace FinalizedBindingEvent
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
  {fuel : Nat} {selected : Selected compiled row fuel} {binding : LocalLambdaBinding}

def initializerBinding (event : FinalizedBindingEvent selected binding) : InitializedLetBinding :=
  ⟨event.originalBinder.applySubstitution selected.body.finalized.substitution,
    .expression binding.initializer⟩

theorem finalized_statement (event : FinalizedBindingEvent selected binding) :
    ContainsStatement selected.body.finalized.typedSource event.original.id
      (event.original.applySubstitution selected.body.finalized.substitution) := by
  rw [selected.body.resources.source_eq]
  apply FlexibleSubstitution.ContainsStatement.applySubstitution
  refine ⟨?_, rfl⟩
  change .statement event.original ∈ selected.body.returned.nodes
  rw [selected.body.returned_nodes]
  exact event.originalPresent

theorem initializer_retained (event : FinalizedBindingEvent selected binding) :
    event.initializerBinding ∈ initializedLetBindings selected.body.finalized.typedSource := by
  unfold initializedLetBindings
  apply List.mem_flatMap.mpr
  refine ⟨.statement (event.original.applySubstitution selected.body.finalized.substitution),
    event.finalized_statement.1, ?_⟩
  simp [StatementNode.applySubstitution, event.originalForm, StatementForm.applySubstitution,
    statementInitializedLetBindings, initializerBinding]

theorem initializer_edge (event : FinalizedBindingEvent selected binding) :
    DirectChild selected.body.finalized.typedSource (.statement event.original.id)
      event.initializerBinding.initializer := by
  apply directChild_statement_reference event.finalized_statement
  simp [StatementNode.applySubstitution, event.originalForm, StatementForm.applySubstitution,
    StatementForm.references, initializerBinding]

/-- Entering the actual retained child preserves the recursive type invariant
and extends the same lexical initializer stack. No initializer typing is an
input to this boundary step. -/
theorem enter (event : FinalizedBindingEvent selected binding)
    {state : State} {context : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (invariant : RecursiveExpressionInvariant
      (SourceCompiledLocalFinalization.context compiled.program.environment
        compiled.program.signatures selected.signature selected.body.declaration)
      selected.body.finalized state context)
    (actual : ActualContext
      (SourceCompiledLocalFinalization.context compiled.program.environment
        compiled.program.signatures selected.signature selected.body.declaration)
      selected.body.finalized frames context)
    (covered : ActualContext.Covers selected.body.finalized frames (.statement event.original.id)) :
    RecursiveExpressionInvariant
      (SourceCompiledLocalFinalization.context compiled.program.environment
        compiled.program.signatures selected.signature selected.body.declaration)
      selected.body.finalized state (localSchemeInitializerContext context event.initializerBinding.binder) ∧
    ActualContext
      (SourceCompiledLocalFinalization.context compiled.program.environment
        compiled.program.signatures selected.signature selected.body.declaration)
      selected.body.finalized (frames ++ [event.initializerBinding])
      (localSchemeInitializerContext context event.initializerBinding.binder) ∧
    ActualContext.Covers selected.body.finalized (frames ++ [event.initializerBinding])
      (.expression binding.initializer) := by
  have child := actual.enter covered event.initializerBinding event.initializer_retained event.initializer_edge
  exact ⟨invariant.generalizedInitializer event.initializerBinding.binder, child⟩

end FinalizedBindingEvent
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledSelectedInferenceProgress
/-! The selected original checker receipt derives its actual inference-ready
states and substitution continuation from successful program checking. These
facts precede declarative body typing and apply to generalized local bodies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem

structure BodyInferenceProgress {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}
    (receipt : BodyReceipt environment signatures signature fuel checked) : Prop where
  initialReady : (initial signature receipt.declaration).InferenceReady
  returnBelow : (Ty.productMany signature.returnTypes).VariablesBelow
    (initial signature receipt.declaration).inference.next
  body : (initial signature receipt.declaration).InferenceProgress receipt.body.state
  bodyReady : receipt.body.state.InferenceReady
  bodyTypeBelow : receipt.body.type.VariablesBelow receipt.body.state.inference.next
  returnUnification : receipt.body.state.InferenceProgress receipt.returned
  returnedReady : receipt.returned.InferenceReady
  finalization : receipt.returned.InferenceProgress receipt.resources.finalState

namespace BodyInferenceProgress
variable {environment : ProgramEnvironment} {signatures : ProgramSignatures}
  {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}
  {receipt : BodyReceipt environment signatures signature fuel checked}

theorem final_substitution (progress : BodyInferenceProgress receipt) :
    receipt.finalized.substitution.SemanticallyExtends receipt.body.state.inference.substitution := by
  rw [receipt.resources.substitution_eq]
  exact (progress.returnUnification.trans progress.finalization).substitution_extends

theorem initial_substitution (progress : BodyInferenceProgress receipt) :
    receipt.finalized.substitution.SemanticallyExtends
      (initial signature receipt.declaration).inference.substitution := by
  rw [receipt.resources.substitution_eq]
  exact (progress.body.trans (progress.returnUnification.trans progress.finalization)).substitution_extends

end BodyInferenceProgress

theorem Selected.inferenceProgress {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    BodyInferenceProgress selected.body := by
  have formation := Frontend.checkProgram_success_signature_formation checked
  have functions : ∀ candidate ∈ compiled.program.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes) := by
    intro candidate member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  have ready : (initial selected.signature selected.body.declaration).InferenceReady :=
    State.InferenceReady.initial _ _ _
  have returns : (Ty.productMany selected.signature.returnTypes).VariablesBelow
      (initial selected.signature selected.body.declaration).inference.next :=
    Ty.variablesBelow_productMany
      ((formation.functions selected.signature selected.signatureMember).2.1.variablesBelow _)
  have body := Detail.inferStatementsFuel_inferenceProperties ready formation functions returns selected.body.inferred
  have returnBound := returns.weaken body.1.next_le
  have unified := Detail.unify_inferenceProgress body.2.1.solved body.2.2 returnBound selected.body.unified
  have returned := Detail.unify_preserves_inferenceReady body.2.1 body.2.2 returnBound selected.body.unified
  exact ⟨ready, returns, body.1, body.2.1, body.2.2, unified, returned,
    selected.body.resources.progress_of_ready returned⟩

/-- Actual selected compilation supplies the whole inference continuation,
including the final solver, without a body-typing or monomorphism premise. -/
theorem compile_inference_progress {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel, BodyInferenceProgress selected.body := by
  obtain ⟨selected⟩ := of_compile accepted member
  exact ⟨selected, selected.inferenceProgress (SourceCoreCompiler.compile_checked_source accepted)⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledNormalizedFormation
/-! The same selected original check supplies every terminal input to the
normalized inference traversal. Its complete raw ledger therefore has formed
predicates after the actual final substitution, before semantic body typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceInferenceRequirementFormation SourceInferenceNormalizedCoercionFormation

namespace Selected
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

def normalizedContext (selected : Selected compiled row fuel) : SourceSemantics.Context :=
  declarationContext compiled.program.signatures selected.signature.id
    selected.signature.scheme.parameters selected.signature.scheme.predicates
    selected.body.finalized.solvedRequirements

theorem normalizedFormationContext (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    InferenceFormationContext semantic
      (context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration)
      selected.body.finalized.substitution := by
  have catalog : SignatureCatalogWellFormed semantic.signatures :=
    signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked
  have canonical := (Frontend.checkProgram_success_signature_parameters_wellFormed checked).functions
    selected.signature selected.signatureMember
  have declarationEq := (ProgramEnvironment.declaration?_sound selected.body.declared).2
  have binders : TypeParameterBindersWellFormed semantic :=
    StructuralSubstitution.TypeParameterBindersWellFormed.transportContext parameters owner
      (SourceSemantics.SignatureParametersWellFormed.declarationContextBinders
        (signatures := compiled.program.signatures) canonical selected.signature.scheme.predicates [])
  have scope : ProducerScope
      (context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration)
      semantic := {
    binders, signatures, parameters, residual, catalog
    owner := by simpa only [context, ProgramTypeScope.ofDeclaration, declarationEq] using owner }
  have formation := CoercionFormationContext.of_function signatures catalog
    (signatures.symm ▸ selected.signatureMember) parameters owner residual
    (context := context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration) rfl
  refine { formation with
    range := selected.body.resources.producerRange scope
    scope
    canonical := ?_
    validated := Frontend.checkProgram_success_signature_formation checked
    functionShapes := ?_ }
  · simpa only [context, ProgramTypeScope.ofDeclaration, declarationEq] using canonical
  · intro candidate member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2

/-- The finalizer itself discharges continuation and capture inventories.
Only static context fields are supplied to permit lexical initializer scopes. -/
theorem normalizedBodyFormation (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    TypeAdmissible semantic (selected.body.finalized.substitution.apply selected.body.body.type) ∧
      NormalizedStateFormation semantic selected.body.finalized.substitution selected.body.body.state := by
  have formation := selected.normalizedFormationContext checked signatures parameters owner residual
  have progress := selected.inferenceProgress checked
  have entry := function_entry_normalized_formation formation.toFormationContext
    (signatures.symm ▸ selected.signatureMember) parameters owner selected.body.declaration.id
  have returns : ∀ type ∈ selected.signature.returnTypes,
      TypeAdmissible semantic (selected.body.finalized.substitution.apply type) := by
    intro type member
    have formed := (formation.catalog.functions_semantic selected.signature
      (signatures.symm ▸ selected.signatureMember)).return_types type member
    apply type_applySubstitution_residual residual formation.range
    exact TypeAdmissible.ofWellFormed (StructuralSubstitution.TypeWellFormed.transportContext
      (source := signatureContext semantic.signatures selected.signature.id
        selected.signature.scheme.parameters selected.signature.scheme.predicates)
      rfl parameters owner formed)
  have capture : NoCaptureNodes selected.body.finalized.substitution selected.body.body.state.nodes := by
    rw [← selected.body.returned_nodes]
    exact NoCaptureNodes.of_finalizer selected.body.resources
  exact inferStatementsFuel_normalized_formation semantic selected.body.finalized.substitution
    fuel _ _ _ _ progress.initialReady (State.initial_nodesBelowNextOccurrence _ _ _)
    entry formation progress.returnBelow (normalized_productMany formation.scope.binders returns)
    _ selected.body.inferred progress.final_substitution capture

theorem normalizedLedger (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ∀ requirement ∈ selected.body.body.state.requirements,
      PredicateAdmissible selected.normalizedContext
        (TypedTraitResolution.applySubstitution selected.body.finalized.substitution requirement.predicate) :=
  (selected.normalizedBodyFormation checked rfl rfl rfl rfl).2.requirements

end Selected

/-- Successful selected compilation now supplies whole-body ledger formation
without any issuance, initializer typing or monomorphism premise. -/
theorem compile_normalized_ledger {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ requirement ∈ selected.body.body.state.requirements,
        PredicateAdmissible selected.normalizedContext
          (TypedTraitResolution.applySubstitution selected.body.finalized.substitution requirement.predicate) := by
  obtain ⟨selected⟩ := of_compile accepted member
  exact ⟨selected, selected.normalizedLedger (SourceCoreCompiler.compile_checked_source accepted)⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceSpecializedNonTemplateLedger
/-! The actual specialization guard closes every solved predicate outside
the source's owned template inventory, before any semantic body premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceSpecializedNonTemplateLedger
open Frontend SourceInference TypeSystem SourceSpecializationWorklist

private instance : LawfulBEq RequirementId where
  eq_of_beq := by
    intro left right same
    cases left
    cases right
    simp_all [BEq.beq, instBEqRequirementId.beq]
  rfl := by intro value; cases value; simp [BEq.beq, instBEqRequirementId.beq]

private def unfoldCheck (hypothesis : Lean.Name) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let some checkedDecl := (← Lean.getLCtx).findFromUserName? hypothesis
      | throwError "missing checked call"
    let type ← Lean.instantiateMVars (← Lean.Meta.inferType checkedDecl.toExpr)
    let some (_, left, _) := type.eq? | throwError "expected equality: {type}"
    let .const targetName _ := left.getAppFn | throwError "expected checked constant: {left}"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let updated ← Lean.Meta.unfoldLocalDecl goal checkedDecl.fvarId targetName
    Lean.Elab.Tactic.replaceMainGoal [updated]

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

private def qualified (source : TypedSource) : List TypedBinder :=
  source.nodes.filterMap fun
    | .statement {form := .letDecl binder initializer, ..} =>
        if !binder.scheme.quantified.isEmpty &&
            initializer.any (SourceSpecialization.isDirectLambdaInitializer source)
        then some binder else none
    | _ => none

private def qualifiedIds (source : TypedSource) : List RequirementId :=
  ((qualified source).flatMap fun binder =>
    binder.schemeRequirements.map fun requirement => (binder, requirement)).map
      fun entry => entry.2.templateRequirement

private theorem qualified_eq (source : TypedSource) :
    qualified source = (localLambdaBindings source).map (·.binder) := by
  change source.nodes.filterMap _ = (source.nodes.filterMap _).map _
  rw [List.map_filterMap]
  congr 1
  funext node
  cases node with
  | expression expression => rfl
  | statement statement =>
      cases statement with
      | mk id span type form =>
          cases form <;> try rfl
          rename_i binder initializer
          cases initializer with
          | none => simp
          | some initializer =>
              cases empty : binder.scheme.quantified.isEmpty <;>
                cases direct : SourceSpecialization.isDirectLambdaInitializer source initializer <;>
                  simp [empty, direct]

private theorem qualifiedIds_subset (source : TypedSource) :
    qualifiedIds source ⊆ sourceLocalSchemeTemplateIds source := by
  intro id member
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
  obtain ⟨binder, binderMember, pairMember⟩ := List.mem_flatMap.mp entryMember
  obtain ⟨requirement, schemeMember, pairEq⟩ := List.mem_map.mp pairMember
  subst entry
  rw [qualified_eq] at binderMember
  obtain ⟨binding, bindingMember, binderEq⟩ := List.mem_map.mp binderMember
  subst binder
  obtain ⟨statement, statementMember, form⟩ := localLambdaBindings_statement_origin bindingMember
  let owner : LocalSchemeTemplateOwner := {
    binder := binding.binder
    initializer := .expression binding.initializer
    requirement }
  apply sourceLocalSchemeTemplateIds_mem_iff.mpr
  refine ⟨owner, ?_, same⟩
  apply List.mem_flatMap.mpr
  refine ⟨{binder := binding.binder, initializer := .expression binding.initializer}, ?_, ?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨.statement statement, statementMember, ?_⟩
    change _ ∈ statementInitializedLetBindings statement.form
    rw [form]
    exact List.mem_singleton_self _
  · exact List.mem_map.mpr ⟨requirement, schemeMember, rfl⟩

private theorem concrete_closed {type : Ty}
    (concrete : SourceSpecialization.firstNonConcrete type = none) :
    type.freeVariables = [] := by
  induction type with
  | «variable» => cases concrete
  | parameter | constructor | error => rfl
  | application left right leftIH rightIH
  | function left right leftIH rightIH
  | product left right leftIH rightIH
  | mapping left right leftIH rightIH =>
      simp only [SourceSpecialization.firstNonConcrete] at concrete
      cases found : SourceSpecialization.firstNonConcrete left with
      | some reason => simp [found] at concrete
      | none =>
          have rightConcrete : SourceSpecialization.firstNonConcrete right = none := by
            simpa [found] using concrete
          have leftClosed := leftIH found
          have rightClosed := rightIH rightConcrete
          simp only [List.eq_nil_iff_forall_not_mem] at leftClosed rightClosed ⊢
          intro metavariable
          simp [leftClosed metavariable, rightClosed metavariable]
  | proxy inner ih | comptime inner ih => exact ih concrete

/-- The private executable guard supplies concrete types for this exact
solved row. Its exemption list consists only of genuine source templates. -/
theorem specialized_closed {signature : ProgramFunctionSignature}
    {original : CheckedFunction} {supplied : ParameterSubstitution}
    {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature original supplied = .ok row)
    {requirement : SolvedRequirement} (member : requirement ∈ row.function.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds row.function.typedBody) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] := by
  unfold SourceSpecialization.specializeFunction at accepted
  iterate 5 have accepted := reject_ok accepted
  iterate 4 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨ids, owned, accepted⟩ := bind_ok accepted
  obtain ⟨_, concrete, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction
      (SourceSpecialization.applyCheckedFunction canonical original) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
      simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
      subst row
      run_tac unfoldCheck `owned
      obtain ⟨_, _, owned⟩ := bind_ok owned
      dsimp only at owned
      split at owned <;> try cases owned
      iterate 2 obtain ⟨_, _, owned⟩ := bind_ok owned
      have idsEq : qualifiedIds (SourceSpecialization.applyCheckedFunction canonical original).typedBody = ids := by
        change Except.ok _ = Except.ok ids at owned
        exact Except.ok.inj owned
      have absent : requirement.id ∉ ids := by
        rw [← idsEq]
        exact fun contains => ordinary (qualifiedIds_subset _ contains)
      have filtered : requirement ∈
          ((SourceSpecialization.applyCheckedFunction canonical original).solvedRequirements.filter
            fun solved => !ids.contains solved.id) := by
        apply List.mem_filter.mpr
        exact ⟨member, by simp [absent]⟩
      run_tac unfoldCheck `concrete
      split at concrete
      · cases concrete
      · rename_i allConcrete
        have typeClosed (type : Ty)
            (present : type ∈ requirement.predicate.subject :: requirement.predicate.arguments) :
            type.freeVariables = [] := by
          apply concrete_closed
          apply (List.findSome?_eq_none_iff.mp allConcrete) type
          apply List.mem_append_right
          apply List.mem_flatMap.mpr
          refine ⟨requirement, filtered, ?_⟩
          exact List.mem_append_left _ present
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro metavariable occurs
        rcases TypedTraitResolution.mem_predicateVariables_iff.mp occurs with
          subject | ⟨argument, argumentMember, argumentOccurs⟩
        · rw [typeClosed _ (List.mem_cons_self)] at subject
          cases subject
        · rw [typeClosed _ (List.mem_cons_of_mem _ argumentMember)] at argumentOccurs
          cases argumentOccurs

private theorem parameters_keep (parameters : ParameterSubstitution) (type : Ty) :
    type.freeVariables ⊆ (parameters.apply type).freeVariables := by
  intro metavariable occurs
  induction type with
  | «variable» value => exact occurs
  | parameter value | constructor value | error => cases occurs
  | proxy inner ih | comptime inner ih => exact ih occurs
  | application left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_application_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))
  | function left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_function_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))
  | product left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_product_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))
  | mapping left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_mapping_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))

private theorem predicate_parameters_keep (parameters : ParameterSubstitution) (predicate : ProgramPredicate) :
    TypedTraitResolution.predicateVariables predicate ⊆
      TypedTraitResolution.predicateVariables (ProgramPredicate.applyParameters parameters predicate) := by
  intro metavariable occurs
  apply TypedTraitResolution.mem_predicateVariables_iff.mpr
  rcases TypedTraitResolution.mem_predicateVariables_iff.mp occurs with subject | ⟨argument, present, occurs⟩
  · exact .inl (parameters_keep parameters _ subject)
  · exact .inr ⟨parameters.apply argument, List.mem_map.mpr ⟨argument, present, rfl⟩,
      parameters_keep parameters argument occurs⟩

/-- Rigid specialization cannot hide a flexible variable from an original
predicate. The exact source inventory retains every template identifier. -/
theorem original_closed_of_application
    {row : SourceSpecialization.SpecializedFunction} {original : CheckedFunction}
    (closed : ∀ requirement ∈ row.function.solvedRequirements,
      requirement.id ∉ sourceLocalSchemeTemplateIds row.function.typedBody →
      TypedTraitResolution.predicateVariables requirement.predicate = [])
    (same : row.function = SourceSpecialization.applyCheckedFunction row.parameterSubstitution original)
    {requirement : SolvedRequirement} (member : requirement ∈ original.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds original.typedBody) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] := by
  let applied := SourceSpecialization.applySolvedRequirement row.parameterSubstitution requirement
  have appliedMember : applied ∈ row.function.solvedRequirements := by
    rw [same]
    exact List.mem_map.mpr ⟨requirement, member, rfl⟩
  have appliedOrdinary : applied.id ∉ sourceLocalSchemeTemplateIds row.function.typedBody := by
    rw [same]
    change requirement.id ∉ sourceLocalSchemeTemplateIds
      (StructuralSubstitution.applyTypedSource row.parameterSubstitution original.typedBody)
    simpa only [StructuralSubstitution.sourceLocalSchemeTemplateIds_applyTypedSource] using ordinary
  have specializedClosed := closed applied appliedMember appliedOrdinary
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro metavariable occurs
  have kept := predicate_parameters_keep row.parameterSubstitution requirement.predicate occurs
  change metavariable ∈ TypedTraitResolution.predicateVariables applied.predicate at kept
  rw [specializedClosed] at kept
  cases kept

/-- The accepted specializer closes the original predicate too, before any
body typing or final generalization barrier is supplied. -/
theorem original_closed {signature : ProgramFunctionSignature}
    {original : CheckedFunction} {supplied : ParameterSubstitution}
    {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature original supplied = .ok row)
    {requirement : SolvedRequirement} (member : requirement ∈ original.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds original.typedBody) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] :=
  original_closed_of_application (fun _ member ordinary => specialized_closed accepted member ordinary)
    (SourceCompiledLocalReadOrigins.specializeFunction_applied accepted) member ordinary

end Solcore.SourceSemantics.SourceSpecializedNonTemplateLedger
end
