import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationValidity
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationStageFacts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedParameterProjections
import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
import Solcore.SourceSemantics.CoreLowering.CallableEvidenceEnvironment
import Solcore.SourceSemantics.CoreLowering.BuiltinNamedCallMeaning

/-! The real public worklist supplies complete specialization carriers and their
original generic definitions. Executable-plan growth and the actual preparation
pass supply ordered inputs, statement roots and the full resolved dictionary.
Independent program typing, every raw substitution range and invocation arity
remain explicit. The source call correspondence does not construct runtime
Entry/Authority/profiles, extend the ordinary closed Header, or prove recursive
staging and contextual local-evidence transformation semantics. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
open Frontend SourceInference TypeSystem SourceSpecializationWorklist

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) :
    ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α}
    {map : ε → δ} {value : α} (accepted : action.mapError map = .ok value) :
    action = .ok value := by
  cases action <;> cases accepted
  rfl

/-- Static provenance contains the actual request, complete source definition
and success equation. It has no execution or body-law field. -/
def Origin (program : CheckedProgram) (specialized : SourceSpecialization.SpecializedFunction) : Prop :=
  ∃ request signature generic,
    signature ∈ program.signatures.functions ∧ generic ∈ program.functions ∧
    resolveRequest program request = .ok specialized ∧
    SourceSpecialization.specializeFunction signature generic request.parameterSubstitution = .ok specialized

theorem resolve_origin {program : CheckedProgram} {request : Request}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : resolveRequest program request = .ok specialized) : Origin program specialized := by
  have resolved := accepted
  unfold resolveRequest at accepted
  obtain ⟨declaration, _, accepted⟩ := bind_ok accepted
  split at accepted
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  · obtain ⟨signature, selectedSignature, accepted⟩ := bind_ok accepted
    obtain ⟨generic, selectedGeneric, accepted⟩ := bind_ok accepted
    have signatureMember : signature ∈ program.signatures.functions := by
      change (match program.signatures.functions.filter (fun signature =>
        decide (signature.id = request.declaration)) with
        | [] => .error (.missingSignature request.declaration)
        | [signature] => .ok signature
        | signatures => .error (.duplicateSignatures request.declaration signatures.length) : Except SourceSpecializationWorklist.Error ProgramFunctionSignature) =
          .ok signature at selectedSignature
      split at selectedSignature
      · cases selectedSignature
      · rename_i entry same
        cases selectedSignature
        exact (List.mem_filter.mp (same ▸ List.mem_cons_self)).1
      · cases selectedSignature
    have genericMember : generic ∈ program.functions := by
      change (match program.functions.filter (fun generic =>
        decide (generic.declaration = request.declaration)) with
        | [] => .error (.missingFunction request.declaration)
        | [generic] => .ok generic
        | functions => .error (.duplicateFunctions request.declaration functions.length) : Except SourceSpecializationWorklist.Error CheckedFunction) =
          .ok generic at selectedGeneric
      split at selectedGeneric
      · cases selectedGeneric
      · rename_i entry same
        cases selectedGeneric
        exact (List.mem_filter.mp (same ▸ List.mem_cons_self)).1
      · cases selectedGeneric
    cases specializedEq : SourceSpecialization.specializeFunction signature generic
        request.parameterSubstitution with
    | error error => simp [specializedEq, throw, throwThe, MonadExceptOf.throw] at accepted
    | ok output =>
      simp only [specializedEq, pure, Except.pure, Except.ok.injEq] at accepted
      subst output
      exact ⟨request, signature, generic, signatureMember, genericMember, resolved, specializedEq⟩

private theorem next_resolved {program : CheckedProgram} {seen : List SourceSpecialization.SpecializationKey}
    {queue rest : List Request} {request : Request} {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : nextUnseen program seen queue = .ok (some (request, specialized, rest))) :
    resolveRequest program request = .ok specialized := by
  induction queue with
  | nil => cases accepted
  | cons head tail ih =>
    unfold nextUnseen at accepted
    obtain ⟨value, resolved, accepted⟩ := bind_ok accepted
    split at accepted
    · exact ih accepted
    · cases accepted
      exact resolved

private theorem runAux_origins {program : CheckedProgram}
    {seedKeys seen : List SourceSpecialization.SpecializationKey} {queue : List Request}
    {entries : List SourceSpecialization.SpecializedFunction} {calls : List CallEdge}
    {references : List ReferenceEdge} {budget : Nat} {outcome : Outcome}
    (initial : ∀ row ∈ entries, Origin program row)
    (accepted : runAux program seedKeys queue seen entries calls references budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations, Origin program row := by
  induction budget generalizing queue seen entries calls references outcome with
  | zero =>
    unfold runAux at accepted
    obtain ⟨next, _, accepted⟩ := bind_ok accepted
    cases next with
    | none => cases accepted; exact initial
    | some item => rcases item with ⟨request, selected, rest⟩; cases accepted; exact initial
  | succ budget ih =>
    unfold runAux at accepted
    obtain ⟨next, found, accepted⟩ := bind_ok accepted
    cases next with
    | none => cases accepted; exact initial
    | some item =>
      rcases item with ⟨request, selected, rest⟩
      obtain ⟨⟨requests, newCalls, newReferences⟩, _, accepted⟩ := bind_ok accepted
      apply ih (accepted := accepted)
      intro row member
      rcases List.mem_append.mp member with old | added
      · exact initial row old
      · have same : row = selected := by simpa using added
        subst row
        exact resolve_origin (next_resolved found)

/-- Only carriers actually appended by the successful queue are covered. The
unprocessed candidate at budget exhaustion is not made a retained row. -/
theorem worklist_origins {program : CheckedProgram} {requests : List Request}
    {budget : Nat} {outcome : Outcome} (accepted : run program requests budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations, Origin program row := by
  unfold run at accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  exact runAux_origins (by simp) accepted

/-- Success of the current pure compiler retains the original complete plan
from the actual worklist, before detached method preparation extends it. -/
theorem compiler_plan {program : CheckedProgram} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compileChecked program seeds options = .ok compiled) :
    ∃ requests, run program requests options.specializationBudget = .ok (.complete compiled.plan) := by
  unfold SourceCoreCompiler.compileChecked at accepted
  obtain ⟨requests, _, accepted⟩ := bind_ok accepted
  obtain ⟨outcome, worklist, accepted⟩ := bind_ok accepted
  have worklist := mapError_ok worklist
  cases outcome with
  | budgetExhausted plan next pending =>
    change Except.error (SourceCoreCompiler.Error.specializationBudgetExhausted next pending.length) = .ok compiled at accepted
    cases accepted
  | complete plan =>
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    split at accepted
    · simp [throw, throwThe, MonadExceptOf.throw] at accepted
    · split at accepted
      · split at accepted
        · cases accepted; exact ⟨requests, worklist⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at accepted
      · split at accepted
        · simp [throw, throwThe, MonadExceptOf.throw] at accepted
        · split at accepted
          · obtain ⟨roots, _, accepted⟩ := bind_ok accepted
            split at accepted
            · cases accepted; exact ⟨requests, worklist⟩
            · simp [throw, throwThe, MonadExceptOf.throw] at accepted
          · simp [throw, throwThe, MonadExceptOf.throw] at accepted

theorem public_origins {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
    (issued : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe) :
    recipe.compiled.sourceProgram = program ∧
      ∀ row ∈ recipe.compiled.validationPlan.specializations, Origin program row := by
  obtain ⟨source, generated, cached, _⟩ := RecursiveNamedPreparedStageContracts.public_compilation accepted issued
  obtain ⟨programEq, planEq, _⟩ := SourceCoreCompiler.Compiled.artifact_fields source cached
  obtain ⟨requests, worklist⟩ := compiler_plan generated
  refine ⟨programEq.trans (SourceCoreCompiler.compileChecked_program generated), ?_⟩
  rw [planEq]
  exact worklist_origins worklist

private theorem mapM_member {α β ε : Type} {action : α → Except ε β}
    {inputs : List α} {outputs : List β} {input : α}
    (accepted : inputs.mapM action = .ok outputs) (member : input ∈ inputs) :
    ∃ output ∈ outputs, action input = .ok output := by
  induction inputs generalizing outputs with
  | nil => cases member
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, generated, accepted⟩ := bind_ok accepted
    obtain ⟨rest, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨first, by simp, generated⟩
    · obtain ⟨output, outputMember, generated⟩ := ih remaining member
      exact ⟨output, by simp [outputMember], generated⟩

/-- A retained original row survives method-plan growth as the same complete
carrier. Reversed mapM preparation supplies its real physical named slot. -/
theorem cached_row (compiled : SourceCoreUnifiedCompilation.Compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.validationPlan.specializations) :
    ∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function), compiled.indexed.base.functions[index]? = some named ∧ named.specialized = row := by
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled
  obtain ⟨growth, _⟩ := CallableCoercionPreparation.of_accepted prepared
  have retained := growth.entries.subset member
  have generated := RecursiveNamedPreparedParameterProjections.automatic_functions compiled.compatiblePrepared
  rw [CallableIndexedPreparedInventories.indexed_base compiled.indexedPrepared] at retained
  obtain ⟨named, namedMember, accepted⟩ := mapM_member generated (List.mem_reverse.mpr retained)
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp namedMember
  refine ⟨index, named, ?_, (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1⟩
  rwa [CallableIndexedPreparedInventories.indexed_base compiled.indexedPrepared]

/-- Every field is an actual static factory receipt. The dictionary keeps
all recursive evidence and the compiler's original list order. -/
structure Prepared (compiled : SourceCoreUnifiedCompilation.Compiled)
    (row : SourceSpecialization.SpecializedFunction) where
  index : Nat
  named : SourceCoreGeneralFunctions.Function
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  code : Core.Expr
  compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code
  available : SourceTypedRuntime.RuntimeEvidenceEnvironment
  selected : compiled.indexed.base.functions[index]? = some named
  same : named.specialized = row
  cached : compiled.indexed.secondPass.closures[index]? = some code
  origin : Origin compiled.sourceProgram row
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram row.key row.assumptions =
    .ok available

theorem of_public_compile {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
    (issued : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe)
    (member : row ∈ recipe.compiled.validationPlan.specializations) :
    Nonempty (Prepared recipe.compiled row) := by
  obtain ⟨programEq, origins⟩ := public_origins accepted issued
  obtain ⟨index, named, selected, same⟩ := cached_row recipe.compiled member
  obtain ⟨diagnostics, code, cached, ⟨compilation⟩⟩ := CallableIndexedNamedGeneration.compiled_at recipe.compiled.indexed selected
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled
  obtain ⟨growth, covered⟩ := CallableCoercionPreparation.of_accepted prepared
  obtain ⟨available, resolved, _⟩ := covered row (growth.entries.subset member)
  exact ⟨⟨index, named, diagnostics, code, compilation, available, selected, same, cached,
    by simpa only [programEq] using origins row member, resolved⟩⟩

/-- This global source view has empty lexical capture and the actual resolved
dictionary, including nonempty constraints. No native closure is inferred. -/
def Prepared.view {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row) : Dynamic.Closure :=
  { RecursiveNamedPreparedSourceFrames.view compiled.sourceProgram prepared.named prepared.compilation.statements with
    evidence := CallableNamedMetadata.environment prepared.available }

namespace Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)

include prepared

theorem instantiated (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    Dynamic.FunctionInstantiates (Program.ofChecked compiled.sourceProgram)
      (CallableNamedMetadata.instantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _, accepted⟩ := prepared.origin
  exact RecursiveNamedSpecializationBodyFacts.instantiated signatureMember genericMember accepted
    (RecursiveNamedSpecializationValidity.valid_of_program wellFormed signatureMember accepted range)

theorem source_frame (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) (CallableNamedMetadata.instantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view := by
  refine ⟨prepared.instantiated wellFormed range, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · exact congrArg (fun row => row.function.typedBody) prepared.same
  · exact congrArg (fun row => (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row).context) prepared.same
  · exact congrArg (fun row => row.function.typedBody.inputs) prepared.same
  · exact congrArg (fun row => row.function.inferredBodyType) prepared.same
  · change Dynamic.StatementRoots row.function.typedBody.roots prepared.compilation.statements
    simpa only [prepared.same] using RecursiveNamedPreparedSourceFrames.compiled_roots prepared.compilation
  · exact CallableEvidenceEnvironment.resolved_covers rfl prepared.resolved

theorem agreement : CompatibleNamedBody.NamedAgreement prepared.named prepared.view := by
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled prepared.selected
  have original := RecursiveNamedPreparedSourceFrames.agreement accepted prepared.compilation
  exact ⟨original.source, original.roots, original.parameters, original.result⟩

theorem has_stages (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Staging.FunctionHasStages row.function := by
  obtain ⟨request, signature, generic, _, genericMember, _, accepted⟩ := prepared.origin
  exact RecursiveNamedSpecializationStageFacts.has_stages_of_program wellFormed genericMember accepted

/-- Actual ordered evidence is valid and covers the full specialized source
context. Equality of predicate keys alone is not used as a dictionary proof. -/
theorem dictionary :
    (CallableNamedMetadata.environment prepared.available).Valid compiled.sourceProgram.signatures.resolutionRules ∧
    (CallableNamedMetadata.environment prepared.available).map Prod.fst = row.assumptions :=
  CallableEvidenceEnvironment.resolved_valid prepared.resolved

/-- Authentication fixes the complete recursive dictionary, including unused
rows. It does not compare only goals or infer an arbitrary source dictionary. -/
theorem authenticated_dictionary {actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence
      compiled.sourceProgram.signatures row.key row.assumptions actual = .ok ()) :
    actual = prepared.available :=
  CallableNamedMetadata.authenticated_evidence_eq authenticated prepared.resolved

theorem retained_frame (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) (CallableNamedCanonicalOrder.retainedInstantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view := by
  have frame := prepared.source_frame wellFormed range
  exact ⟨RecursiveNamedRetainedSubstitutionFacts.retained_instantiates frame.instantiated,
    frame.source, frame.context, frame.parameters, frame.result, frame.captured, frame.roots, frame.covers⟩

/-- The generic program's independent global call and its actual specialized
body use the same dictionary, outcome and whole heap in both directions. -/
theorem call_outcome_iff (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : row.function.typedBody.inputs.length = arguments.length) :
    FunctionCallBody.Outcome (Program.ofChecked compiled.sourceProgram) context caller prepared.view.evidence before
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩) arguments outcome after ↔
    NamedCalls.BodyOutcome (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      prepared.view.evidence before arguments outcome after := by
  have frame := prepared.source_frame wellFormed range
  exact ⟨BuiltinNamedCalls.source_dispatch wellFormed.function_ids frame (by rwa [frame.parameters]), frame.call⟩

end Prepared
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
