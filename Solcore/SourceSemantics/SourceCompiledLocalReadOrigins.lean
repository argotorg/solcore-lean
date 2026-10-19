import Solcore.Frontend.SourceCoreCompiler
import Solcore.Frontend.SourceInference.ProgramProperties

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
