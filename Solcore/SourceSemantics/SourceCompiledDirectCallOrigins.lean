import Solcore.Frontend.SourceInference.DirectCallOriginsInference
import Solcore.SourceSemantics.SourceCompiledLocalReadOrigins

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
