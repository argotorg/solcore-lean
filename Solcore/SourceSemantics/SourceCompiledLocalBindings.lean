import Solcore.SourceSemantics.SourceCompiledLocalReadOrigins

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
