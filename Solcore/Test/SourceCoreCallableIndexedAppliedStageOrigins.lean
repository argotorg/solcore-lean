import Solcore.SourceSemantics.CoreLowering.CallableIndexedAppliedStageOrigins
import Solcore.Test.SourceCoreCallableAncestryReadRecipes

/-! Actual metadata factories supply the applied header and descriptor origin.
The indexed consumer requires the same full rewritten source. These tests do
not turn a substitution-only source receipt into an applied one, nor construct
body typing from history. The existing recipe fixture checks distinct caller
and lexical contexts, original witnesses and the observable source export. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedAppliedStageOrigins
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAppliedViewProvenance CallableIndexedAppliedStageOrigins
open SourceCoreCallableAncestryReadRecipes

abbrev actual_view := @Recipe.of_view
abbrev actual_header := @header_of_prepared
abbrev actual_code := @code_origin
abbrev actual_scope := @selected
abbrev original_source_receipt := @LambdaSourceAlignment.SourceReceipt.original

section Recipe
variable {checked : Checked} {base : Base checked} {inputs : Inputs base}
  {callerFrame lexicalFrame : Frame} {caller lexical : MetadataState} {view target : Core.Word}
  (recipe : Recipe inputs callerFrame lexicalFrame caller lexical view target)
  {contract : SourceCoreStageContracts.Contract}
  (canonical : CanonicalHeader inputs recipe.read.template contract)

include canonical in
theorem actual_bound {function : Dynamic.Closure}
    (retained : recipe.read.descriptor.contract = some contract)
    (aligned : Alignment recipe function) :
    CallableLedger.Binds base.plan (.closure function) (CallContractCertificates.semanticContract contract) :=
  (origin recipe canonical retained aligned).binds

include canonical in
theorem ordered_parameters : contract.parameters =
    recipe.applied.parameters.map (TypedBinder.applySubstitution recipe.read.substitution) :=
  recipe.contract_parameters canonical

include canonical in
theorem source_result : contract.stagedResult =
    SourceCompilationPlan.sourceTypeIsComptimeOnly (recipe.read.substitution.apply recipe.applied.resultType) :=
  recipe.contract_result canonical

theorem separate_contexts :
    (recipe.read.after lexical).metadata.active = recipe.read.substitution.compose lexical.metadata.active ∧
    (recipe.read.after lexical).nativeActive = recipe.read.entry.view.cumulative :=
  ⟨recipe.semantic_active, recipe.native_active⟩

theorem full_lexical_source : (recipe.read.after lexical).metadata.source =
    SourceTypedRuntime.rewriteLocalRequirements recipe.read.witnesses
      (lexical.metadata.source.applySubstitution recipe.read.substitution) := recipe.full_source

theorem actual_rewritten_node :
    (recipe.read.after lexical).metadata.source.lookupExpression? recipe.read.entry.view.principal.initializer =
      some (SourceTypedRuntime.rewriteExpressionLocalRequirements recipe.read.witnesses
        (recipe.applied.node.applySubstitution recipe.read.substitution)) := recipe.source_node

theorem original_witness_order (captured : SourceTypedRuntime.Environment)
    (evidence : SourceCompilationPlan.EvidenceEnvironment) :
    recipe.applied.sourceValue captured evidence =
      .instantiated recipe.read.substitution recipe.read.witnesses
        (.closure recipe.applied.parameters recipe.applied.resultType recipe.applied.body
          lexical.metadata.source lexical.metadata.owner captured evidence) := recipe.source_value _ _

theorem authenticated_after : CallableAncestryPairedLookup.Authenticates inputs
    (.appliedView view target callerFrame lexicalFrame) (some (recipe.read.after lexical)) := recipe.authenticated
end Recipe

section Original
variable {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
  {table : SourceCoreStageCodebook.Table} {function : Dynamic.Closure} {scope : Staging.Recursive.Scope}

theorem selected_original (selected : RecursiveStageRegistry.Selected program plan table function scope) :
    ∃ sidecar active, SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar ∧
      scope = RecursiveStageRegistry.scope sidecar active function ∧
      scope.origin.declaration = sidecar.caller.key.declaration := selected.original
end Original

/-- Fresh recipe execution; the whole native callable fixture remains in its
existing test module and is not duplicated here. -/
def run : IO Unit := Tests.SourceCoreCallableAncestryReadRecipes.run

end Tests.SourceCoreCallableIndexedAppliedStageOrigins
