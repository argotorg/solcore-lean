import Solcore.Frontend.SourceCoreCompiler
import Solcore.Frontend.SourceInference.Internal.ProgramProperties
import Solcore.Frontend.SourceInference.Internal.DirectCallInference
import Solcore.Frontend.SourceInference.Internal.LocalGeneralization
import Solcore.Frontend.SourceInference.Internal.LocalGeneralizationBounds
import Solcore.Frontend.SourceInference.Internal.LocalReadOrigins
import Solcore.SourceSemantics.SourceInferenceActualCallGraph
import Solcore.Frontend.SourceInference.Internal.LocalReadScopes

/-!
# Origins in selected compilation

What selected compilation keeps from original inference: local reads and their events, direct calls,
lambda bindings, generalization events, template uses and ordered argument calls. The direct-call
initializer origins and receipt uniqueness are here too.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalReadOrigins
/-! Accepted selected compilation retains the actual finite worklist run.
Local-read provenance is obtained from processed rows of that run. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalReadOrigins
open Frontend SourceInference

private theorem bind_ok {Error Value Result : Type}
    (source : Except Error Value) (continuation : Value → Except Error Result)
    (result : Result)
    (accepted : (do let value ← source; continuation value) = .ok result) :
    ∃ value, source = .ok value ∧ continuation value = .ok result := by
  cases source with
  | error error => simp [bind, Except.bind] at accepted
  | ok value => exact ⟨value, rfl, by simpa only [bind, Except.bind] using accepted⟩

theorem specializeFunction_applied {signature : ProgramFunctionSignature}
    {function : CheckedFunction} {supplied : TypeSystem.ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature function supplied = .ok specialized) :
    specialized.function = SourceSpecialization.applyCheckedFunction specialized.parameterSubstitution function := by
  unfold SourceSpecialization.specializeFunction at accepted
  by_cases guard0 : (signature.id != function.declaration) = true
  · simp only [guard0] at accepted; cases accepted
  · simp only [guard0] at accepted
    by_cases guard1 : (function.typedBody.owner != function.declaration) = true
    · simp only [guard1] at accepted; cases accepted
    · simp only [guard1] at accepted
      by_cases guard2 : (signature.scheme.body != function.type) = true
      · simp only [guard2] at accepted; cases accepted
      · simp only [guard2] at accepted
        by_cases guard3 : (signature.parameterComptime != function.typedBody.inputs.map (·.comptime)) = true
        · simp only [guard3] at accepted; cases accepted
        · simp only [guard3] at accepted
          by_cases guard4 : (signature.returnComptime != function.returnComptime) = true
          · simp only [guard4] at accepted; cases accepted
          · simp only [guard4] at accepted
            obtain ⟨check0, _, accepted⟩ := bind_ok _ _ _ accepted
            cases check0
            obtain ⟨check1, _, accepted⟩ := bind_ok _ _ _ accepted
            cases check1
            obtain ⟨check2, _, accepted⟩ := bind_ok _ _ _ accepted
            cases check2
            obtain ⟨check3, _, accepted⟩ := bind_ok _ _ _ accepted
            cases check3
            obtain ⟨canonical, _, accepted⟩ := bind_ok _ _ _ accepted
            obtain ⟨after0, _, accepted⟩ := bind_ok _ _ _ accepted
            obtain ⟨after1, _, accepted⟩ := bind_ok _ _ _ accepted
            obtain ⟨after2, _, accepted⟩ := bind_ok _ _ _ accepted
            obtain ⟨after3, _, accepted⟩ := bind_ok _ _ _ accepted
            cases analysis : SourceStageAnalysis.analyzeFunction (SourceSpecialization.applyCheckedFunction canonical function) with
            | error error => simp only [analysis] at accepted; cases accepted
            | ok stages =>
              simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
              subst specialized
              rfl

/-- Parameter specialization retains the exact original local occurrence,
local binder ID and requirement identities. -/
theorem specialized_local_read_original {substitution : TypeSystem.ParameterSubstitution}
    {source : TypedSource} {expression : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (present : Node.expression expression ∈ (SourceSpecialization.applyTypedSource substitution source).nodes)
    (form : expression.form = .reference name (.local binder)) :
    ∃ original : ExpressionNode, Node.expression original ∈ source.nodes ∧
      original.id = expression.id ∧ original.form = .reference name (.local binder) ∧
      original.requirements = expression.requirements ∧
      original.localSchemeInstantiationStart = expression.localSchemeInstantiationStart := by
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | statement statement => cases same
  | expression original =>
    have expressionEq : SourceSpecialization.applyExpressionNode substitution original = expression := Node.expression.inj same
    subst expression
    refine ⟨original,member,rfl,?_,rfl,rfl⟩
    change SourceSpecialization.applyExpressionForm substitution original.form = .reference name (.local binder) at form
    cases shape : original.form <;> simp_all [SourceSpecialization.applyExpressionForm, SourceSpecialization.applyReferenceResolution]
    rename_i actual resolution
    cases resolution <;> simp_all

theorem compileChecked_worklist {program : CheckedProgram} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compileChecked program seeds options = .ok compiled) :
    ∃ requests, SourceSpecializationWorklist.run program requests options.specializationBudget =
      .ok (.complete compiled.plan) := by
  unfold SourceCoreCompiler.compileChecked at accepted
  obtain ⟨requests, _, afterRequests⟩ := bind_ok _ _ _ accepted
  obtain ⟨outcome, runMapped, afterRun⟩ := bind_ok _ _ _ afterRequests
  have ran : SourceSpecializationWorklist.run program requests options.specializationBudget = .ok outcome := by
    cases result : SourceSpecializationWorklist.run program requests options.specializationBudget with
    | error error => simp [result, Except.mapError] at runMapped
    | ok actual =>
        simp only [result, Except.mapError, Except.ok.injEq] at runMapped
        exact congrArg Except.ok runMapped
  cases outcome with
  | budgetExhausted plan next pending =>
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at afterRun
  | complete plan =>
      simp only [pure, Except.pure, bind, Except.bind] at afterRun
      obtain ⟨checkedUnit, _, afterLinking⟩ := bind_ok _ _ _ afterRun
      split at afterLinking
      · simp [throw, throwThe, MonadExceptOf.throw] at afterLinking
      · split at afterLinking
        · split at afterLinking
          · cases afterLinking
            exact ⟨requests, ran⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at afterLinking
        · split at afterLinking
          · simp [throw, throwThe, MonadExceptOf.throw] at afterLinking
          · split at afterLinking
            · obtain ⟨roots, _, afterRoots⟩ := bind_ok _ _ _ afterLinking
              split at afterRoots
              · cases afterRoots
                exact ⟨requests, ran⟩
              · simp [throw, throwThe, MonadExceptOf.throw] at afterRoots
            · simp [throw, throwThe, MonadExceptOf.throw] at afterLinking

theorem compileChecked_local_instances {program : CheckedProgram} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compileChecked program seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ instances, SourceSpecializationWorklist.localLambdaInstances row.function.typedBody = .ok instances ∧
      ∀ value ∈ instances, SourceSpecializationWorklist.LocalLambdaInstance.ReadOrigin row.function.typedBody value := by
  obtain ⟨requests, ran⟩ := compileChecked_worklist accepted
  exact SourceSpecializationWorklist.run_local_instances ran member

theorem compile_local_instances {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ instances, SourceSpecializationWorklist.localLambdaInstances row.function.typedBody = .ok instances ∧
      ∀ value ∈ instances, SourceSpecializationWorklist.LocalLambdaInstance.ReadOrigin row.function.typedBody value := by
  unfold SourceCoreCompiler.compile at accepted
  obtain ⟨program, _, lowered⟩ := bind_ok _ _ _ accepted
  exact compileChecked_local_instances lowered member

/-- The immediate occurrence of an actual local instance is retained even
when its closed matcher was reached through a contextual parent. -/
theorem readOrigin_expression {source : TypedSource}
    {localInstance : SourceSpecializationWorklist.LocalLambdaInstance}
    (origin : SourceSpecializationWorklist.LocalLambdaInstance.ReadOrigin source localInstance) :
    ∃ expression : ExpressionNode, ∃ name,
      Node.expression expression ∈ source.nodes ∧
      expression.form = .reference name (.local localInstance.binding.binder.id) := by
  cases origin with
  | root expression present name form _ => exact ⟨expression,name,present,form⟩
  | contextual _ expression present name form _ _ _ => exact ⟨expression,name,present,form⟩

/-- Raw accepted compilation identifies the original body-check equation for
its selected row and maps each discovered local read back to that exact body. -/
theorem compile_original_local_reads {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ original ∈ compiled.program.functions, ∃ signature,
      signature ∈ compiled.program.signatures.functions ∧
      checkFunctionBody compiled.program.environment compiled.program.signatures signature options.checkingFuel = .ok original ∧
      ∃ instances, SourceSpecializationWorklist.localLambdaInstances row.function.typedBody = .ok instances ∧
      ∀ localInstance ∈ instances, ∃ selected originalRead : ExpressionNode, ∃ name,
        Node.expression selected ∈ row.function.typedBody.nodes ∧
        selected.form = .reference name (.local localInstance.binding.binder.id) ∧
        Node.expression originalRead ∈ original.typedBody.nodes ∧
        originalRead.id = selected.id ∧
        originalRead.form = .reference name (.local localInstance.binding.binder.id) ∧
        originalRead.requirements = selected.requirements ∧
        originalRead.localSchemeInstantiationStart = selected.localSchemeInstantiationStart := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  unfold SourceCoreCompiler.compile at accepted
  obtain ⟨program, _, lowered⟩ := bind_ok _ _ _ accepted
  have programEq := SourceCoreCompiler.compileChecked_program lowered
  obtain ⟨requests, ran⟩ := compileChecked_worklist lowered
  obtain ⟨original, originalMember, signature, supplied, specialized⟩ :=
    SourceSpecializationWorklist.run_original ran member
  have originalMember : original ∈ compiled.program.functions := by rw [programEq]; exact originalMember
  obtain ⟨originalSignature, signatureMember, bodyChecked⟩ :=
    Frontend.checkProgram_success_function_body checked originalMember
  obtain ⟨instances, discovered, origins⟩ := compileChecked_local_instances lowered member
  refine ⟨original,originalMember,originalSignature,signatureMember,bodyChecked,instances,discovered,?_⟩
  intro localInstance instanceMember
  obtain ⟨selected,name,present,form⟩ := readOrigin_expression (origins localInstance instanceMember)
  have sourceEq : row.function.typedBody =
      SourceSpecialization.applyTypedSource row.parameterSubstitution original.typedBody := by
    rw [specializeFunction_applied specialized]
    rfl
  obtain ⟨originalRead, originalPresent, idEq, originalForm, requirementsEq, startEq⟩ :=
    specialized_local_read_original (sourceEq ▸ present) form
  exact ⟨selected,originalRead,name,present,form,originalPresent,idEq,originalForm,requirementsEq,startEq⟩

/-- Final inference substitution preserves the original local occurrence and
its issued requirement identities, including expected-type coercion rows. -/
theorem solved_local_read_original {substitution : TypeSystem.Substitution}
    {nodes : List Node} {expression : ExpressionNode} {name : String}
    {binder : Resolved.LocalId}
    (present : Node.expression expression ∈ nodes.map (Node.applySubstitution substitution))
    (form : expression.form = .reference name (.local binder)) :
    ∃ original : ExpressionNode, Node.expression original ∈ nodes ∧
      original.id = expression.id ∧ original.form = .reference name (.local binder) ∧
      original.requirements = expression.requirements ∧
      original.localSchemeInstantiationStart = expression.localSchemeInstantiationStart := by
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | statement statement => cases same
  | expression original =>
    have expressionEq : original.applySubstitution substitution = expression := Node.expression.inj same
    subst expression
    refine ⟨original, member, rfl, ?_, rfl, rfl⟩
    change original.form.applySubstitution substitution = .reference name (.local binder) at form
    cases shape : original.form <;>
      simp_all [ExpressionForm.applySubstitution, ReferenceResolution.applySubstitution]
    rename_i actual resolution
    cases resolution <;> simp_all

/-- The final checked table is the node table from the actual statement
inference, followed only by the solver's final type substitution. -/
theorem checkFunctionBody_inference_nodes
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}
    (accepted : checkFunctionBody environment signatures signature fuel = .ok checked) :
    ∃ declaration body substitution,
      environment.declaration? signature.id = some declaration ∧
      Detail.inferStatementsFuel fuel
        { environment, signatures, scope := .ofDeclaration declaration,
          typeParameters := signature.scheme.parameters,
          assumptions := signature.scheme.predicates }
        signature.source.value.body.value (TypeSystem.Ty.productMany signature.returnTypes)
        (State.initial declaration.id
          ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
            (parameter.1, TypeSystem.Scheme.mono parameter.2))
          signature.parameterComptime) = .ok body ∧
      checked.typedBody.nodes = body.state.nodes.map (Node.applySubstitution substitution) := by
  obtain ⟨declaration, body, finalState, result, declared, inferred, unified, finalized, same⟩ :=
    checkFunctionBody_success_witness accepted
  refine ⟨declaration, body, result.substitution, declared, inferred, ?_⟩
  rw [same, Detail.finalize_typedSource finalized]
  change finalState.nodes.map (Node.applySubstitution result.substitution) = _
  rw [(Detail.unify_occurrenceState_eq unified).1]

/-- Every selected local-lambda instance has a local reference in the node
table produced by the original successful statement-inference call. -/
theorem compile_inferred_local_reads
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ original ∈ compiled.program.functions, ∃ signature declaration body,
      signature ∈ compiled.program.signatures.functions ∧
      compiled.program.environment.declaration? signature.id = some declaration ∧
      Detail.inferStatementsFuel options.checkingFuel
        { environment := compiled.program.environment,
          signatures := compiled.program.signatures,
          scope := .ofDeclaration declaration,
          typeParameters := signature.scheme.parameters,
          assumptions := signature.scheme.predicates }
        signature.source.value.body.value (TypeSystem.Ty.productMany signature.returnTypes)
        (State.initial declaration.id
          ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
            (parameter.1, TypeSystem.Scheme.mono parameter.2))
          signature.parameterComptime) = .ok body ∧
      ∃ instances, SourceSpecializationWorklist.localLambdaInstances row.function.typedBody = .ok instances ∧
      ∀ localInstance ∈ instances, ∃ selected inferredRead : ExpressionNode, ∃ name,
        Node.expression selected ∈ row.function.typedBody.nodes ∧
        selected.form = .reference name (.local localInstance.binding.binder.id) ∧
        Node.expression inferredRead ∈ body.state.nodes ∧
        inferredRead.id = selected.id ∧
        inferredRead.form = .reference name (.local localInstance.binding.binder.id) ∧
        inferredRead.requirements = selected.requirements ∧
        inferredRead.localSchemeInstantiationStart = selected.localSchemeInstantiationStart := by
  obtain ⟨original, originalMember, signature, signatureMember, bodyChecked,
    instances, discovered, origins⟩ := compile_original_local_reads accepted member
  obtain ⟨declaration, body, substitution, declared, inferred, nodesEq⟩ :=
    checkFunctionBody_inference_nodes bodyChecked
  refine ⟨original, originalMember, signature, declaration, body, signatureMember,
    declared, inferred, instances, discovered, ?_⟩
  intro localInstance present
  obtain ⟨selected, originalRead, name, selectedPresent, selectedForm, originalPresent,
    idEq, originalForm, requirementsEq, startEq⟩ := origins localInstance present
  obtain ⟨inferredRead, inferredPresent, inferredId, inferredForm, inferredRequirements, inferredStart⟩ :=
    solved_local_read_original (nodesEq ▸ originalPresent) originalForm
  exact ⟨selected, inferredRead, name, selectedPresent, selectedForm, inferredPresent,
    inferredId.trans idEq, inferredForm, inferredRequirements.trans requirementsEq,
    inferredStart.trans startEq⟩

end Solcore.SourceSemantics.SourceCompiledLocalReadOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledDirectCallOrigins
/-! Actual direct-call emitters survive final solving and parameter
specialization into the selected compilation row. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledDirectCallOrigins
open Frontend SourceInference TypeSystem DirectCallEvents

private theorem requirement_contains {ids : List RequirementId} {id : RequirementId}
    (member : ids.contains id = true) : id ∈ ids := by
  induction ids with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.contains_cons, Bool.or_eq_true] at member
    rcases member with same | later
    · apply List.mem_cons.mpr
      apply Or.inl
      have indices : id.index = head.index := by
        change (id.index == head.index) = true at same
        exact beq_iff_eq.mp same
      cases id; cases head; cases indices; rfl
    · exact List.mem_cons_of_mem _ (ih later)

/-- The generalizer selects templates only from genuine direct-call IDs. -/
theorem generalized_template_direct (state : State) (locals : TypeSystem.Environment)
    (cutoff : Nat) (type : Ty) (template : LocalSchemeRequirement)
    (member : template ∈ (Detail.generalizeValue state locals cutoff type).requirements) :
    template.templateRequirement ∈ state.directCallRequirements := by
  unfold Detail.generalizeValue at member
  dsimp only at member
  obtain ⟨raw, eligible, selected⟩ := List.mem_filterMap.mp member
  have classified := (List.mem_filter.mp eligible).2
  simp only [Bool.and_eq_true] at classified
  have direct := classified.1
  split at selected
  · cases selected
    exact requirement_contains direct
  · contradiction

theorem generalized_template_emitter {state : State} (origins : Origins state)
    (locals : TypeSystem.Environment) (cutoff : Nat) (type : Ty)
    {template : LocalSchemeRequirement}
    (member : template ∈ (Detail.generalizeValue state locals cutoff type).requirements) :
    HasCall state.nodes template.templateRequirement :=
  origins _ (generalized_template_direct state locals cutoff type template member)

theorem solved_call {nodes : List Node} {requirement : RequirementId}
    (emitter : HasCall nodes requirement) (substitution : Substitution) :
    HasCall (nodes.map (Node.applySubstitution substitution)) requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued⟩ := emitter
  refine ⟨node.applySubstitution substitution,
    List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, instantiation.applySubstitution substitution, ?_, issued⟩
  change node.form.applySubstitution substitution = _
  rw [form]
  rfl

theorem specialized_call {source : TypedSource} {requirement : RequirementId}
    (emitter : HasCall source.nodes requirement) (substitution : ParameterSubstitution) :
    HasCall (SourceSpecialization.applyTypedSource substitution source).nodes requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued⟩ := emitter
  refine ⟨SourceSpecialization.applyExpressionNode substitution node,
    List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, SourceSpecialization.applyInstantiation substitution instantiation, ?_, issued⟩
  change SourceSpecialization.applyExpressionForm substitution node.form = _
  rw [form]
  rfl

/-- The exact initialized inference and final node substitution from checking
one selected original function. -/
structure BodyRun (environment : ProgramEnvironment) (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature) (fuel : Nat) (checked : CheckedFunction) where
  declaration : ProgramDeclaration
  body : Detail.BlockResult
  substitution : Substitution
  declared : environment.declaration? signature.id = some declaration
  inferred : Detail.inferStatementsFuel fuel
    {environment, signatures, scope := .ofDeclaration declaration,
      typeParameters := signature.scheme.parameters, assumptions := signature.scheme.predicates}
    signature.source.value.body.value (Ty.productMany signature.returnTypes)
    (State.initial declaration.id
      ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
        (parameter.1, Scheme.mono parameter.2)) signature.parameterComptime) = .ok body
  nodes : checked.typedBody.nodes = body.state.nodes.map (Node.applySubstitution substitution)

theorem checkFunctionBody_run {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}
    (accepted : checkFunctionBody environment signatures signature fuel = .ok checked) :
    Nonempty (BodyRun environment signatures signature fuel checked) := by
  obtain ⟨declaration, body, substitution, declared, inferred, nodes⟩ :=
    SourceCompiledLocalReadOrigins.checkFunctionBody_inference_nodes accepted
  exact ⟨⟨declaration, body, substitution, declared, inferred, nodes⟩⟩

theorem BodyRun.direct_call {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}
    (run : BodyRun environment signatures signature fuel checked)
    {requirement : RequirementId} (direct : requirement ∈ run.body.state.directCallRequirements) :
    HasCall checked.typedBody.nodes requirement := by
  rw [run.nodes]
  exact solved_call (initializedStatements_origins run.inferred requirement direct) run.substitution

private theorem bind_ok {Error Value Result : Type}
    (source : Except Error Value) (continuation : Value → Except Error Result)
    (result : Result)
    (accepted : (do let value ← source; continuation value) = .ok result) :
    ∃ value, source = .ok value ∧ continuation value = .ok result := by
  cases source with
  | error error => simp [bind, Except.bind] at accepted
  | ok value => exact ⟨value, rfl, by simpa only [bind, Except.bind] using accepted⟩

/-- Successful selected compilation supplies the actual initialized source
run and preserves all its direct emitters in the same specialized row. -/
theorem compile_direct_emitters
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ original ∈ compiled.program.functions, ∃ signature,
      signature ∈ compiled.program.signatures.functions ∧
      ∃ run : BodyRun compiled.program.environment compiled.program.signatures
        signature options.checkingFuel original,
      ∀ requirement ∈ run.body.state.directCallRequirements,
        HasCall row.function.typedBody.nodes requirement := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  unfold SourceCoreCompiler.compile at accepted
  obtain ⟨program, _, lowered⟩ := bind_ok _ _ _ accepted
  have programEq := SourceCoreCompiler.compileChecked_program lowered
  obtain ⟨requests, ran⟩ := SourceCompiledLocalReadOrigins.compileChecked_worklist lowered
  obtain ⟨original, originalMember, signature, supplied, specialized⟩ :=
    SourceSpecializationWorklist.run_original ran member
  have originalMember : original ∈ compiled.program.functions := by
    rw [programEq]; exact originalMember
  obtain ⟨originalSignature, signatureMember, bodyChecked⟩ :=
    Frontend.checkProgram_success_function_body checked originalMember
  obtain ⟨run⟩ := checkFunctionBody_run bodyChecked
  refine ⟨original, originalMember, originalSignature, signatureMember, run, ?_⟩
  have sourceEq : row.function.typedBody =
      SourceSpecialization.applyTypedSource row.parameterSubstitution original.typedBody := by
    rw [SourceCompiledLocalReadOrigins.specializeFunction_applied specialized]
    rfl
  intro requirement direct
  rw [sourceEq]
  exact specialized_call (run.direct_call direct) row.parameterSubstitution

end Solcore.SourceSemantics.SourceCompiledDirectCallOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalBindings
/-! Selected compilation retains membership in the actual local-lambda
collector and the complete original declaration that supplied each binding. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceCompiledLocalBindings
open Frontend SourceInference SourceSpecializationWorklist

theorem compileChecked_binding_origins
    {program : CheckedProgram} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compileChecked program seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.plan.specializations) :
    ∃ instances, localLambdaInstances row.function.typedBody = .ok instances ∧
      ∀ value ∈ instances,
        value.binding ∈ localLambdaBindings row.function.typedBody ∧
        LocalLambdaInstance.ReadOrigin row.function.typedBody value ∧
        ∃ statement : StatementNode, Node.statement statement ∈ row.function.typedBody.nodes ∧
          statement.form = .letDecl value.binding.binder (some value.binding.initializer) := by
  obtain ⟨instances, discovered, origins⟩ :=
    SourceCompiledLocalReadOrigins.compileChecked_local_instances accepted member
  refine ⟨instances, discovered, ?_⟩
  intro value present
  have binding := localLambdaInstances_bindings discovered value present
  exact ⟨binding, origins value present, localLambdaBindings_statement_origin binding⟩

theorem compile_binding_origins
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.plan.specializations) :
    ∃ instances, localLambdaInstances row.function.typedBody = .ok instances ∧
      ∀ value ∈ instances,
        value.binding ∈ localLambdaBindings row.function.typedBody ∧
        LocalLambdaInstance.ReadOrigin row.function.typedBody value ∧
        ∃ statement : StatementNode, Node.statement statement ∈ row.function.typedBody.nodes ∧
          statement.form = .letDecl value.binding.binder (some value.binding.initializer) := by
  obtain ⟨instances, discovered, origins⟩ :=
    SourceCompiledLocalReadOrigins.compile_local_instances accepted member
  refine ⟨instances, discovered, ?_⟩
  intro value present
  have binding := localLambdaInstances_bindings discovered value present
  exact ⟨binding, origins value present, localLambdaBindings_statement_origin binding⟩

end Solcore.SourceSemantics.SourceCompiledLocalBindings
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
/-! Selected rows retain the exact initialized statement binder produced by
original inference, followed by the actual solver and parameter substitutions.
Generalization events refer to that original initializer return state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
open Frontend SourceInference TypeSystem

/-- Parameter specialization retains the initialized statement identity and
its exact binder transformation. -/
theorem specialized_initialized_statement_original {substitution : ParameterSubstitution}
    {source : TypedSource} {statement : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    (present : Node.statement statement ∈ (SourceSpecialization.applyTypedSource substitution source).nodes)
    (form : statement.form = .letDecl binder (some initializer)) :
    ∃ original : StatementNode, ∃ originalBinder : TypedBinder,
      Node.statement original ∈ source.nodes ∧ original.id = statement.id ∧
      original.form = .letDecl originalBinder (some initializer) ∧
      SourceSpecialization.applyBinder substitution originalBinder = binder := by
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression expression => cases same
  | statement original =>
      have selected : SourceSpecialization.applyStatementNode substitution original = statement := Node.statement.inj same
      subst statement
      change SourceSpecialization.applyStatementForm substitution original.form = .letDecl binder (some initializer) at form
      cases shape : original.form <;> simp only [shape, SourceSpecialization.applyStatementForm] at form
      case letDecl actual value =>
        obtain ⟨sameBinder, sameInitializer⟩ := StatementForm.letDecl.inj form
        exact ⟨original, actual, member, rfl, by rw [shape, sameInitializer], sameBinder⟩
      all_goals cases form

/-- The solver's final substitution retains the initialized occurrence and
acts on its binder through the real capture-avoiding binder operation. -/
theorem solved_initialized_statement_original {substitution : Substitution}
    {nodes : List Node} {statement : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    (present : Node.statement statement ∈ nodes.map (Node.applySubstitution substitution))
    (form : statement.form = .letDecl binder (some initializer)) :
    ∃ original : StatementNode, ∃ originalBinder : TypedBinder,
      Node.statement original ∈ nodes ∧ original.id = statement.id ∧
      original.form = .letDecl originalBinder (some initializer) ∧
      originalBinder.applySubstitution substitution = binder := by
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression expression => cases same
  | statement original =>
      have selected : original.applySubstitution substitution = statement := Node.statement.inj same
      subst statement
      change original.form.applySubstitution substitution = .letDecl binder (some initializer) at form
      cases shape : original.form <;> simp only [shape, StatementForm.applySubstitution] at form
      case letDecl actual value =>
        obtain ⟨sameBinder, sameInitializer⟩ := StatementForm.letDecl.inj form
        exact ⟨original, actual, member, rfl, by rw [shape, sameInitializer], sameBinder⟩
      all_goals cases form

/-- The full selected source row, original declaration body and both actual
substitutions belong to one accepted compilation. -/
structure InferredSelectedBody (compiled : SourceCoreCompiler.Compiled)
    (row : SourceSpecialization.SpecializedFunction) (fuel : Nat) where
  original : CheckedFunction
  originalMember : original ∈ compiled.program.functions
  signature : ProgramFunctionSignature
  signatureMember : signature ∈ compiled.program.signatures.functions
  declaration : ProgramDeclaration
  declared : compiled.program.environment.declaration? signature.id = some declaration
  body : Detail.BlockResult
  substitution : Substitution
  inferred : Detail.inferStatementsFuel fuel
    { environment := compiled.program.environment, signatures := compiled.program.signatures,
      scope := .ofDeclaration declaration, typeParameters := signature.scheme.parameters,
      assumptions := signature.scheme.predicates }
    signature.source.value.body.value (Ty.productMany signature.returnTypes)
    (State.initial declaration.id
      ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
        (parameter.1, Scheme.mono parameter.2)) signature.parameterComptime) = .ok body
  solved : original.typedBody.nodes = body.state.nodes.map (Node.applySubstitution substitution)
  specialized : row.function.typedBody = SourceSpecialization.applyTypedSource row.parameterSubstitution original.typedBody
  events : LocalGeneralizationEvents.Origins body.state.nodes

/-- No body or generalization law is a premise. The original checker call,
solver substitution and selected worklist row are recovered from compilation. -/
theorem compile_selected_body {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    Nonempty (InferredSelectedBody compiled row options.checkingFuel) := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  have lowered : SourceCoreCompiler.compileChecked compiled.program seeds options = .ok compiled := by
    simpa only [SourceCoreCompiler.compile, checked, Except.mapError, bind, Except.bind] using accepted
  obtain ⟨requests, ran⟩ := SourceCompiledLocalReadOrigins.compileChecked_worklist lowered
  obtain ⟨original, originalMember, selectedSignature, supplied, specialized⟩ :=
    SourceSpecializationWorklist.run_original ran member
  obtain ⟨signature, signatureMember, bodyChecked⟩ := checkProgram_success_function_body checked originalMember
  obtain ⟨declaration, body, substitution, declared, inferred, nodes⟩ :=
    SourceCompiledLocalReadOrigins.checkFunctionBody_inference_nodes bodyChecked
  have sourceEq : row.function.typedBody = SourceSpecialization.applyTypedSource row.parameterSubstitution original.typedBody := by
    rw [SourceCompiledLocalReadOrigins.specializeFunction_applied specialized]
    rfl
  have ready : LocalGeneralizationEvents.Ready (State.initial declaration.id
      ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
        (parameter.1, Scheme.mono parameter.2)) signature.parameterComptime) := by
    refine ⟨State.initial_requirementsWellFormed _ _ _, ?_, ?_⟩
    · intro id impossible
      exact False.elim (List.not_mem_nil impossible)
    · intro node impossible
      exact False.elim (List.not_mem_nil impossible)
  exact ⟨⟨original, originalMember, signature, signatureMember, declaration, declared, body, substitution,
    inferred, nodes, sourceEq,
    LocalGeneralizationEvents.inferStatementsFuel_origins inferred ready LocalGeneralizationEvents.Origins.empty⟩⟩

/-- The selected initialized binder is related to its real original event by
both executable substitutions, with the exact initializer and statement IDs. -/
theorem InferredSelectedBody.initialized_event {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel)
    {statement : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    (present : Node.statement statement ∈ row.function.typedBody.nodes)
    (form : statement.form = .letDecl binder (some initializer)) :
    ∃ original : StatementNode, ∃ originalBinder : TypedBinder,
      Node.statement original ∈ receipt.body.state.nodes ∧ original.id = statement.id ∧
      original.form = .letDecl originalBinder (some initializer) ∧
      SourceSpecialization.applyBinder row.parameterSubstitution
        (originalBinder.applySubstitution receipt.substitution) = binder ∧
      LocalGeneralizationEvents.Origin originalBinder initializer := by
  obtain ⟨checkedStatement, checkedBinder, checkedPresent, checkedId, checkedForm, specializedBinder⟩ :=
    specialized_initialized_statement_original (receipt.specialized ▸ present) form
  obtain ⟨inferredStatement, inferredBinder, inferredPresent, inferredId, inferredForm, solvedBinder⟩ :=
    solved_initialized_statement_original (receipt.solved ▸ checkedPresent) checkedForm
  refine ⟨inferredStatement, inferredBinder, inferredPresent, inferredId.trans checkedId, inferredForm, ?_, ?_⟩
  · rw [solvedBinder]
    exact specializedBinder
  · have event := receipt.events inferredStatement inferredPresent
    simpa only [LocalGeneralizationEvents.Statement, inferredForm] using event

end Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalGeneralizationBindings
/-! Actual worklist binding membership selects the original checker event.
The selected binder keeps its stable identity and quantified variables through
both real substitutions, while its full scheme transformation remains explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
open Frontend SourceInference SourceSpecializationWorklist TypeSystem

structure BindingEvent {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel) (binding : LocalLambdaBinding) where
  selected : StatementNode
  selectedPresent : .statement selected ∈ row.function.typedBody.nodes
  selectedForm : selected.form = .letDecl binding.binder (some binding.initializer)
  original : StatementNode
  originalBinder : TypedBinder
  originalPresent : .statement original ∈ receipt.body.state.nodes
  sameStatement : original.id = selected.id
  originalForm : original.form = .letDecl originalBinder (some binding.initializer)
  transformed : SourceSpecialization.applyBinder row.parameterSubstitution
    (originalBinder.applySubstitution receipt.substitution) = binding.binder
  sameLocal : originalBinder.id = binding.binder.id
  sameQuantified : originalBinder.scheme.quantified = binding.binder.scheme.quantified
  event : LocalGeneralizationEvents.Origin originalBinder binding.initializer

/-- A collector member is the exact binder of a real selected statement, so
its original event is selected without assuming uniqueness merely from an ID. -/
theorem InferredSelectedBody.binding_event {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel) {binding : LocalLambdaBinding}
    (member : binding ∈ localLambdaBindings row.function.typedBody) :
    Nonempty (BindingEvent receipt binding) := by
  obtain ⟨selected, selectedPresent, selectedForm⟩ := localLambdaBindings_statement_origin member
  obtain ⟨original, binder, originalPresent, sameId, originalForm, transformed, event⟩ :=
    receipt.initialized_event selectedPresent selectedForm
  have sameLocal := congrArg TypedBinder.id transformed
  change binder.id = binding.binder.id at sameLocal
  have sameQuantified := congrArg (fun value : TypedBinder => value.scheme.quantified) transformed
  change binder.scheme.quantified = binding.binder.scheme.quantified at sameQuantified
  exact ⟨⟨selected, selectedPresent, selectedForm, original, binder, originalPresent,
    sameId, originalForm, transformed, sameLocal, sameQuantified, event⟩⟩

/-- Selected compilation supplies both actual instance membership and the
original event; no assumed checker generalization or specialization law is used. -/
theorem compile_binding_events {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ receipt : InferredSelectedBody compiled row options.checkingFuel,
      ∃ instances, localLambdaInstances row.function.typedBody = .ok instances ∧
        ∀ value ∈ instances,
          value.binding ∈ localLambdaBindings row.function.typedBody ∧
          LocalLambdaInstance.ReadOrigin row.function.typedBody value ∧
          Nonempty (BindingEvent receipt value.binding) := by
  obtain ⟨receipt⟩ := compile_selected_body accepted member
  obtain ⟨instances, discovered, bindings⟩ := SourceCompiledLocalBindings.compile_binding_origins accepted member
  refine ⟨receipt, instances, discovered, ?_⟩
  intro value present
  have binding := bindings value present
  exact ⟨binding.1, binding.2.1, receipt.binding_event binding.1⟩

end Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalGeneralizationBoundaries
/-! The actual empty function entry closes the bounded event traversal.
Selected local instances retain their original generalization boundary and its
read containment at the final inferred body state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
open Frontend SourceInference SourceSpecializationWorklist TypeSystem
open LocalGeneralizationBoundaries

/-- This is the parameter state used by the original checker equation. -/
def InferredSelectedBody.initialState {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel) : State :=
  State.initial receipt.declaration.id
    ((receipt.signature.parameterNames.zip receipt.signature.parameterTypes).map fun parameter =>
      (parameter.1, Scheme.mono parameter.2)) receipt.signature.parameterComptime

/-- Every event is created by actual body inference. The initial node table is
empty and parameter binders lie below its real allocator cutoff. -/
theorem InferredSelectedBody.bounded_origins {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel) :
    OriginsSince receipt.initialState.nextLocal receipt.body.state := by
  have ready : LocalGeneralizationEvents.Ready receipt.initialState := by
    refine ⟨State.initial_requirementsWellFormed _ _ _, ?_, ?_⟩
    · intro id impossible
      exact False.elim (List.not_mem_nil impossible)
    · intro node impossible
      exact False.elim (List.not_mem_nil impossible)
  have below : receipt.initialState.LocalBindersBelowNextLocal :=
    State.initial_localBindersBelowNextLocal _ _ _
  exact (inferStatementsFuel_boundaries_progress receipt.inferred).empty_entry ready below rfl

structure BoundedBindingEvent {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel) (binding : LocalLambdaBinding)
    extends BindingEvent receipt binding where
  boundary : OriginSince receipt.initialState.nextLocal receipt.body.state originalBinder binding.initializer

/-- The selected statement and both substitutions identify the very same
original event whose retired reads remain contained after all continuations. -/
theorem InferredSelectedBody.binding_boundary {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel) {binding : LocalLambdaBinding}
    (member : binding ∈ localLambdaBindings row.function.typedBody) :
    Nonempty (BoundedBindingEvent receipt binding) := by
  obtain ⟨event⟩ := receipt.binding_event member
  refine ⟨{ toBindingEvent := event, boundary := ?_ }⟩
  have boundary := receipt.bounded_origins event.original event.originalPresent
  simpa only [StatementSince, event.originalForm] using boundary

/-- The final compiler connection needs only actual accepted selected
compilation. Discovery supplies membership and read ancestry; original
inference supplies generalization and final-state containment. -/
theorem compile_binding_boundaries {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ receipt : InferredSelectedBody compiled row options.checkingFuel,
      ∃ instances, localLambdaInstances row.function.typedBody = .ok instances ∧
        ∀ value ∈ instances,
          value.binding ∈ localLambdaBindings row.function.typedBody ∧
          LocalLambdaInstance.ReadOrigin row.function.typedBody value ∧
          Nonempty (BoundedBindingEvent receipt value.binding) := by
  obtain ⟨receipt⟩ := compile_selected_body accepted member
  obtain ⟨instances, discovered, bindings⟩ := SourceCompiledLocalBindings.compile_binding_origins accepted member
  refine ⟨receipt, instances, discovered, ?_⟩
  intro value present
  have binding := bindings value present
  exact ⟨binding.1, binding.2.1, receipt.binding_boundary binding.1⟩

end Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalTemplateUses
/-! Selected compilation keeps the compiler's actual template-ownership
checks and the exact direct lexical body on which those checks succeeded. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalTemplateUses
open Frontend SourceInference SourceSpecializationWorklist

/-- No independent source coverage or whole-original typing assumption is
needed: both discovery and template checks are part of accepted compilation. -/
theorem compile_template_receipts
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.plan.specializations) :
    ∃ instances, localLambdaInstances row.function.typedBody = .ok instances ∧
      ∀ localInstance ∈ instances,
        LocalLambdaInstance.ReadOrigin row.function.typedBody localInstance ∧
        ∃ nodes, localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes ∧
          nodes ⊆ row.function.typedBody.nodes ∧
          LocalTemplateUses (localLambdaBindings row.function.typedBody) localInstance nodes := by
  obtain ⟨instances, discovered, origins⟩ :=
    SourceCompiledLocalReadOrigins.compile_local_instances accepted member
  exact ⟨instances, discovered, fun localInstance present =>
    ⟨origins localInstance present,
      localLambdaInstances_template_receipts discovered localInstance present⟩⟩

end Solcore.SourceSemantics.SourceCompiledLocalTemplateUses
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalReadEvents
/-! Actual selected compilation exposes the original successful local lookup
and the requirement batch it issued in the final inference ledger. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceCompiledLocalReadEvents
open Frontend SourceInference

/-- Function inference starts with no local read events or issued obligations.
The traversal obtains both from actual successful inference operations. -/
theorem inferStatements_initial_origins
    {fuel : Nat} {context : SourceInference.Context} {statements : List Syntax.Statement}
    {expected : TypeSystem.Ty} {owner : Resolved.DeclarationId}
    {locals : TypeSystem.Environment} {comptime : List Bool} {body : Detail.BlockResult}
    (accepted : Detail.inferStatementsFuel fuel context statements expected
      (State.initial owner locals comptime) = .ok body) :
    LocalReadEvents.Origins body.state := by
  apply LocalReadEvents.inferStatementsFuel_origins accepted
    (State.initial_requirementsWellFormed owner locals comptime)
  · intro id member
    exact False.elim (List.not_mem_nil member)
  · intro node member
    exact False.elim (List.not_mem_nil member)

/-- Each local-lambda row discovered by the actual selected worklist retains
an actual original lookup, its exact occurrence and its operational batch.
No assumption about typing every original function is used. -/
theorem compile_local_lookup_events
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ original ∈ compiled.program.functions, ∃ signature declaration body,
      signature ∈ compiled.program.signatures.functions ∧
      compiled.program.environment.declaration? signature.id = some declaration ∧
      Detail.inferStatementsFuel options.checkingFuel
        { environment := compiled.program.environment,
          signatures := compiled.program.signatures,
          scope := .ofDeclaration declaration,
          typeParameters := signature.scheme.parameters,
          assumptions := signature.scheme.predicates }
        signature.source.value.body.value (TypeSystem.Ty.productMany signature.returnTypes)
        (State.initial declaration.id
          ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
            (parameter.1, TypeSystem.Scheme.mono parameter.2))
          signature.parameterComptime) = .ok body ∧
      ∃ instances, SourceSpecializationWorklist.localLambdaInstances row.function.typedBody = .ok instances ∧
      ∀ localInstance ∈ instances, ∃ selected inferredRead : ExpressionNode, ∃ name,
        Node.expression selected ∈ row.function.typedBody.nodes ∧
        selected.form = .reference name (.local localInstance.binding.binder.id) ∧
        Node.expression inferredRead ∈ body.state.nodes ∧
        inferredRead.id = selected.id ∧
        inferredRead.form = .reference name (.local localInstance.binding.binder.id) ∧
        inferredRead.requirements = selected.requirements ∧
        inferredRead.localSchemeInstantiationStart = selected.localSchemeInstantiationStart ∧
        ∃ lookup : LocalReadEvents.Lookup,
          inferredRead.id = lookup.id ∧
          inferredRead.form = .reference lookup.name.value (.local lookup.binder.id) ∧
          inferredRead.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
          lookup.batch.1 <+: inferredRead.requirements ∧
          RequirementPredicatesCorrespond body.state.requirements lookup.predicates lookup.batch.1 ∧
          (∀ requirement ∈ body.state.requirements, requirement.id ∈ lookup.batch.1 →
            ∀ cutoff, requirement ∈ Detail.generalizeValueBlockingRequirements body.state cutoff) := by
  obtain ⟨original, originalMember, signature, declaration, body, signatureMember,
    declared, inferred, instances, discovered, reads⟩ :=
    SourceCompiledLocalReadOrigins.compile_inferred_local_reads accepted member
  have origins := inferStatements_initial_origins inferred
  refine ⟨original, originalMember, signature, declaration, body, signatureMember,
    declared, inferred, instances, discovered, ?_⟩
  intro localInstance present
  obtain ⟨selected, inferredRead, name, selectedPresent, selectedForm,
    inferredPresent, sameId, originalForm, sameRequirements, sameStart⟩ :=
    reads localInstance present
  have origin := origins inferredRead inferredPresent name localInstance.binding.binder.id originalForm
  exact ⟨selected, inferredRead, name, selectedPresent, selectedForm, inferredPresent,
    sameId, originalForm, sameRequirements, sameStart, LocalReadEvents.Origin.operational origin⟩

/-- Ownership validation and original inference events concern the same
actual discovered local instance and the same selected source body. -/
theorem compile_local_obligations
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ original ∈ compiled.program.functions, ∃ signature declaration body,
      signature ∈ compiled.program.signatures.functions ∧
      compiled.program.environment.declaration? signature.id = some declaration ∧
      Detail.inferStatementsFuel options.checkingFuel
        { environment := compiled.program.environment,
          signatures := compiled.program.signatures,
          scope := .ofDeclaration declaration,
          typeParameters := signature.scheme.parameters,
          assumptions := signature.scheme.predicates }
        signature.source.value.body.value (TypeSystem.Ty.productMany signature.returnTypes)
        (State.initial declaration.id
          ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
            (parameter.1, TypeSystem.Scheme.mono parameter.2))
          signature.parameterComptime) = .ok body ∧
      ∃ instances, SourceSpecializationWorklist.localLambdaInstances row.function.typedBody = .ok instances ∧
      ∀ localInstance ∈ instances, ∃ nodes,
        SourceSpecializationWorklist.localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes ∧
        nodes ⊆ row.function.typedBody.nodes ∧
        SourceSpecializationWorklist.LocalTemplateUses
          (SourceSpecializationWorklist.localLambdaBindings row.function.typedBody) localInstance nodes ∧
        ∃ selected inferredRead : ExpressionNode, ∃ name,
        Node.expression selected ∈ row.function.typedBody.nodes ∧
        selected.form = .reference name (.local localInstance.binding.binder.id) ∧
        Node.expression inferredRead ∈ body.state.nodes ∧
        inferredRead.id = selected.id ∧
        inferredRead.form = .reference name (.local localInstance.binding.binder.id) ∧
        inferredRead.requirements = selected.requirements ∧
        inferredRead.localSchemeInstantiationStart = selected.localSchemeInstantiationStart ∧
        ∃ lookup : LocalReadEvents.Lookup,
          inferredRead.id = lookup.id ∧
          inferredRead.form = .reference lookup.name.value (.local lookup.binder.id) ∧
          inferredRead.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
          lookup.batch.1 <+: inferredRead.requirements ∧
          RequirementPredicatesCorrespond body.state.requirements lookup.predicates lookup.batch.1 ∧
          (∀ requirement ∈ body.state.requirements, requirement.id ∈ lookup.batch.1 →
            ∀ cutoff, requirement ∈ Detail.generalizeValueBlockingRequirements body.state cutoff) := by
  obtain ⟨original, originalMember, signature, declaration, body, signatureMember,
    declared, inferred, instances, discovered, events⟩ := compile_local_lookup_events accepted member
  refine ⟨original, originalMember, signature, declaration, body, signatureMember,
    declared, inferred, instances, discovered, ?_⟩
  intro localInstance present
  obtain ⟨nodes, bodyNodes, subset, templates⟩ :=
    SourceSpecializationWorklist.localLambdaInstances_template_receipts discovered localInstance present
  exact ⟨nodes, bodyNodes, subset, templates, events localInstance present⟩

end Solcore.SourceSemantics.SourceCompiledLocalReadEvents
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledOrderedArgumentCalls
/-! Ordered argument provenance records the actual expression calls and their
threaded states. It also represents a synthetic singleton list around a real
unary operand, without asserting that the list itself occurred in the run. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem Detail SourceInferenceExecution

inductive OrderedExpressionCalls (provenance : CallIndex → Prop)
    (context : SourceInference.Context) :
    Nat → List Syntax.Expr → State → List InferredExpression → State → Prop where
  | nil {fuel : Nat} {state : State} :
      OrderedExpressionCalls provenance context (fuel + 1) [] state [] state
  | cons {fuel : Nat} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final : State} {value : InferredExpression} {values : List InferredExpression}
      (accepted : inferExprFuel fuel context source none initial = .ok (value, middle))
      (here : provenance (.expression fuel context source none initial value middle))
      (tail : OrderedExpressionCalls provenance context fuel sources middle values final) :
      OrderedExpressionCalls provenance context (fuel + 1) (source :: sources)
        initial (value :: values) final

namespace OrderedExpressionCalls
variable {provenance : CallIndex → Prop} {context : SourceInference.Context}
    {fuel : Nat} {sources : List Syntax.Expr} {initial final : State}
    {values : List InferredExpression}

theorem accepted (calls : OrderedExpressionCalls provenance context fuel sources initial values final) :
    inferExprsFuel fuel context sources initial = .ok (values, final) := by
  induction calls with
  | nil => simp only [inferExprsFuel]
  | cons accepted _ _ induction =>
      simp only [inferExprsFuel, accepted, bind, Except.bind, induction, pure, Pure.pure, Except.pure]

/-- Exact successful head and tail results recover their recorded provenance. -/
theorem split {source : Syntax.Expr} {middle : State} {value : InferredExpression}
    (calls : OrderedExpressionCalls provenance context (fuel + 1) (source :: sources)
      initial (value :: values) final)
    (headAccepted : inferExprFuel fuel context source none initial = .ok (value, middle)) :
    provenance (.expression fuel context source none initial value middle) ∧
      OrderedExpressionCalls provenance context fuel sources middle values final := by
  cases calls with
  | cons actual here tail =>
      have same := Except.ok.inj (actual.symm.trans headAccepted)
      cases Prod.mk.inj same with
      | intro sameValue sameState =>
          cases sameValue
          cases sameState
          exact ⟨here, tail⟩

theorem of_call (descend : ChildClosed provenance) :
    ∀ {fuel : Nat} {sources : List Syntax.Expr} {initial final : State}
      {values : List InferredExpression},
    provenance (.expressions fuel context sources initial values final) →
    inferExprsFuel fuel context sources initial = .ok (values, final) →
    OrderedExpressionCalls provenance context fuel sources initial values final := by
  intro fuel
  induction fuel with
  | zero =>
      intro sources initial final values _ accepted
      simp only [inferExprsFuel] at accepted
      cases accepted
  | succ fuel induction =>
      intro sources initial final values here accepted
      cases sources with
      | nil =>
          simp only [inferExprsFuel, Except.ok.injEq, Prod.mk.injEq] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          exact .nil
      | cons source sources =>
          have parentAccepted := accepted
          unfold inferExprsFuel at accepted
          cases headAccepted : inferExprFuel fuel context source none initial with
          | error error => simp [headAccepted, bind, Except.bind] at accepted
          | ok pair =>
              rcases pair with ⟨head, middle⟩
              simp only [headAccepted, bind, Except.bind] at accepted
              cases tailAccepted : inferExprsFuel fuel context sources middle with
              | error error => simp [tailAccepted] at accepted
              | ok pair =>
                  rcases pair with ⟨tail, tailFinal⟩
                  simp only [tailAccepted, pure, Pure.pure, Except.pure, Except.ok.injEq,
                    Prod.mk.injEq] at accepted
                  rcases accepted with ⟨rfl, rfl⟩
                  exact .cons headAccepted
                    (descend here (.expressions_head parentAccepted headAccepted))
                    (induction (descend here (.expressions_tail parentAccepted headAccepted tailAccepted))
                      tailAccepted)

theorem of_accepted
    (accepted : inferExprsFuel fuel context sources initial = .ok (values, final)) :
    OrderedExpressionCalls (fun _ => True) context fuel sources initial values final :=
  of_call true_childClosed trivial accepted

/-- A real operand call can be used as a singleton argument sequence. -/
theorem singleton {source : Syntax.Expr} {value : InferredExpression}
    (accepted : inferExprFuel fuel context source none initial = .ok (value, final))
    (here : provenance (.expression fuel context source none initial value final)) :
    OrderedExpressionCalls provenance context (fuel + 1) [source] initial [value] final := by
  cases fuel with
  | zero =>
      simp only [inferExprFuel] at accepted
      cases accepted
  | succ fuel => exact .cons accepted here .nil

end OrderedExpressionCalls
end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceDirectCallInitializerOrigins
/-! A real statement position retains its actual call and the direct-emitter
progress through its prefix and suffix. Initializer receipts then expose the
same ready state and the exact raw row selected by generalization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceDirectCallInitializerOrigins
open Frontend SourceInference TypeSystem Detail DirectCallEvents

structure StatementCall (context : SourceInference.Context) (source : Syntax.Statement)
    (expected : Ty) (initial final : State) where
  fuel : Nat
  entry : State
  result : StatementResult
  accepted : inferStatementFuel fuel context source expected entry = .ok result
  prefixProgress : Progress initial entry
  suffixProgress : Progress result.state final

/-- This follows the actual list computation, so repeated equal source syntax
cannot select an unrelated call or a different entering state. -/
theorem statementCall_of_position
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (StatementCall context source expected initial result.state) := by
  induction fuel generalizing sources initial result index with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil => simp at position
    | cons head rest =>
      cases headRun : inferStatementFuel fuel context head expected initial with
      | error error => simp [inferStatementsFuel, headRun, bind, Except.bind] at accepted
      | ok headResult =>
        have headProgress := inferStatementFuel_origins_progress headRun
        cases rest with
        | nil =>
          have same : result.state = headResult.state := by
            simp only [inferStatementsFuel, headRun, bind, Except.bind, pure, Pure.pure,
              Except.pure, Except.ok.injEq] at accepted
            exact (congrArg BlockResult.state accepted).symm
          cases index with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at position
            subst source
            exact ⟨⟨fuel, initial, headResult, headRun, .refl _, same.symm ▸ Progress.refl _⟩⟩
          | succ index => simp at position
        | cons next remaining =>
          cases tailRun : inferStatementsFuel fuel context (next :: remaining) expected headResult.state with
          | error error => simp [inferStatementsFuel, headRun, tailRun, bind, Except.bind] at accepted
          | ok tailResult =>
            have same : result.state = tailResult.state := by
              simp only [inferStatementsFuel, headRun, tailRun, bind, Except.bind, pure,
                Pure.pure, Except.pure, Except.ok.injEq] at accepted
              exact (congrArg BlockResult.state accepted).symm
            cases index with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at position
              subst source
              exact ⟨⟨fuel, initial, headResult, headRun, .refl _,
                same.symm ▸ inferStatementsFuel_origins_progress tailRun⟩⟩
            | succ index =>
              obtain ⟨found⟩ := ih tailRun position
              exact ⟨⟨found.fuel, found.entry, found.result, found.accepted,
                headProgress.trans found.prefixProgress, same.symm ▸ found.suffixProgress⟩⟩

theorem receipt_ready_origins
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (origins : Origins initial) : Origins receipt.ready :=
  inferExprFuel_origins_progress receipt.child origins

theorem header_ready_origins
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (origins : Origins initial) : Origins receipt.ready :=
  inferExprFuel_origins_progress receipt.child origins

/-- The actual initialized statement, including its annotation choice,
receives ready-state emitter provenance from this very prefix. -/
theorem StatementCall.initialized
    {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial final : State}
    (call : StatementCall context source expected initial final)
    (origins : Origins initial)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ childFuel, ∃ receipt : LocalLetRequirementTiming.Receipt childFuel context source call.entry call.result,
      Origins receipt.ready := by
  have accepted := call.accepted
  cases fuelEq : call.fuel with
  | zero => simp [fuelEq, inferStatementFuel] at accepted
  | succ fuel =>
    rw [fuelEq] at accepted
    obtain ⟨receipt⟩ := LocalLetRequirementTiming.of_initialized_accepted form accepted
    exact ⟨fuel, receipt, receipt_ready_origins receipt (call.prefixProgress origins)⟩

/-- No externally supplied emitter invariant is needed for an actual
position in the initialized original function run. -/
theorem initialized_statement_position
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {owner : Resolved.DeclarationId} {parameters : Environment}
    {comptime : List Bool} {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (accepted : inferStatementsFuel fuel context sources expected
      (State.initial owner parameters comptime) = .ok result)
    (position : sources[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ call : StatementCall context source expected (State.initial owner parameters comptime) result.state,
    ∃ childFuel, ∃ receipt : LocalLetRequirementTiming.Receipt childFuel context source call.entry call.result,
      Origins receipt.ready := by
  obtain ⟨call⟩ := statementCall_of_position accepted position
  obtain ⟨childFuel, receipt, ready⟩ := call.initialized (initial_origins _ _ _) form
  exact ⟨call, childFuel, receipt, ready⟩

/-- A template in this exact new binder has its actual raw row and call
emitter at the initializer return, before subsequent inference can run. -/
theorem receipt_template_emitter
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (origins : Origins initial) {template : LocalSchemeRequirement}
    (member : template ∈ receipt.binding.1.schemeRequirements) :
    ∃ raw ∈ receipt.ready.requirements,
      raw.id = template.templateRequirement ∧
      template.predicate = applyPredicate receipt.ready raw.predicate ∧
      HasCall receipt.ready.nodes template.templateRequirement := by
  obtain ⟨raw, present, same, predicate⟩ := generalizeValue_requirement_source
    receipt.ready receipt.locals initial.nextRequirement (receipt.ready.resolve receipt.value.type)
    template member
  exact ⟨raw, present, same, predicate,
    SourceCompiledDirectCallOrigins.generalized_template_emitter (receipt_ready_origins receipt origins)
      receipt.locals initial.nextRequirement (receipt.ready.resolve receipt.value.type) member⟩

end Solcore.SourceSemantics.SourceInferenceDirectCallInitializerOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationReceiptUniqueness
/-! An initializer receipt is determined by its exact checker call. Source
syntax determines the annotation, and the executable child determines its
returned value and pre-generalization state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference
open TypeSystem Detail

theorem LocalLetRequirementTiming.Annotation.unique
    {context : Context} {syntaxType : Option Syntax.TypeExpr} {left right : Option Ty}
    (first : LocalLetRequirementTiming.Annotation context syntaxType left)
    (second : LocalLetRequirementTiming.Annotation context syntaxType right) : left = right := by
  cases first with
  | none => cases second; rfl
  | some accepted =>
      cases second with
      | some other =>
          have same := Except.ok.inj (accepted.symm.trans other)
          exact congrArg Option.some same

theorem LocalLetRequirementTiming.Receipt.unique
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (first second : LocalLetRequirementTiming.Receipt fuel context statement initial result) :
    first = second := by
  rcases first with ⟨name, initializer, annotation, expected, annotationAccepted,
    form, value, ready, child, completed⟩
  rcases second with ⟨otherName, otherInitializer, otherAnnotation, otherExpected,
    otherAnnotationAccepted, otherForm, otherValue, otherReady, otherChild, otherCompleted⟩
  have forms := form.symm.trans otherForm
  cases Syntax.StatementValue.letDecl.inj forms with
  | intro sameName rest =>
      rcases rest with ⟨sameAnnotation, sameInitializer⟩
      cases sameName
      cases sameAnnotation
      cases Option.some.inj sameInitializer
      have sameExpected := annotationAccepted.unique otherAnnotationAccepted
      cases sameExpected
      have sameChild := Except.ok.inj (child.symm.trans otherChild)
      cases Prod.mk.inj sameChild with
      | intro sameValue sameReady =>
          cases sameValue
          cases sameReady
          rfl

theorem LocalHeaderRequirementTiming.Receipt.unique
    {fuel : Nat} {context : Context} {statement : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (first second : LocalHeaderRequirementTiming.Receipt fuel context statement initial result) :
    first = second := by
  rcases first with ⟨name, initializer, annotation, expected, annotationAccepted,
    form, value, ready, child, completed⟩
  rcases second with ⟨otherName, otherInitializer, otherAnnotation, otherExpected,
    otherAnnotationAccepted, otherForm, otherValue, otherReady, otherChild, otherCompleted⟩
  have forms := form.symm.trans otherForm
  cases Syntax.ForItemValue.letDecl.inj forms with
  | intro sameName rest =>
      rcases rest with ⟨sameAnnotation, sameInitializer⟩
      cases sameName
      cases sameAnnotation
      cases Option.some.inj sameInitializer
      have sameExpected := annotationAccepted.unique otherAnnotationAccepted
      cases sameExpected
      have sameChild := Except.ok.inj (child.symm.trans otherChild)
      cases Prod.mk.inj sameChild with
      | intro sameValue sameReady =>
          cases sameValue
          cases sameReady
          rfl

end Solcore.Frontend.SourceInference
end
