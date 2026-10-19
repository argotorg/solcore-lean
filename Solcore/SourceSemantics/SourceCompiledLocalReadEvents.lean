import Solcore.SourceSemantics.SourceCompiledLocalTemplateUses
import Solcore.Frontend.SourceInference.LocalReadOriginsInference

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
