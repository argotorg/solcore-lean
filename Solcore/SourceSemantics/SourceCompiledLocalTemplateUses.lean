import Solcore.SourceSemantics.SourceCompiledLocalReadOrigins

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
