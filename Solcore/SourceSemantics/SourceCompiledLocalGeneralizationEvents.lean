import Solcore.SourceSemantics.SourceCompiledLocalReadOrigins
import Solcore.Frontend.SourceInference.LocalGeneralizationInference

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
