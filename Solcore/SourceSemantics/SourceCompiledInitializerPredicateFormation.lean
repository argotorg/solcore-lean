import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledNormalizedTemplates
import Solcore.SourceSemantics.SourceCompiledGeneralizedInitializerContexts
import Solcore.SourceSemantics.SourceCompiledTopLevelInitializerContinuation

/-! Selected initialized-let receipts and retained worklist bindings consume
whole-body predicate formation at their exact finalized initializer scopes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness SourceSpecializationWorklist

namespace FinalizedBindingEvent
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : Selected compiled row fuel} {binding : LocalLambdaBinding}

theorem finalPredicates (event : FinalizedBindingEvent selected binding)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.signature.id)
    (residual : target.residualTypeVariables = true) :
    ∀ requirement ∈ (event.originalBinder.applySubstitution selected.body.finalized.substitution).schemeRequirements,
      PredicateAdmissible (localSchemeInitializerContext target
        (event.originalBinder.applySubstitution selected.body.finalized.substitution)) requirement.predicate :=
  selected.normalizedBindingPredicates checked signatures parameters owner residual event.initializer_retained

end FinalizedBindingEvent

namespace InitializerContinuation
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

/-- This uses the continuation's exact recorded binder and initializer. All
predicate formation is discharged by the selected body traversal and solver. -/
theorem finalPredicates (continuation : InitializerContinuation selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.signature.id)
    (residual : target.residualTypeVariables = true) :
    ∀ requirement ∈ (continuation.receipt.binding.1.applySubstitution
        selected.body.finalized.substitution).schemeRequirements,
      PredicateAdmissible (localSchemeInitializerContext target
        (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)) requirement.predicate := by
  apply selected.originalBindingPredicates checked signatures parameters owner residual
    (initializer := .expression continuation.receipt.value.id)
  intro requirement member
  apply List.mem_flatMap.mpr
  refine ⟨({ binder := continuation.receipt.binding.1
             initializer := .expression continuation.receipt.value.id } : InitializedLetBinding),
    ?_, List.mem_map.mpr ⟨requirement, member, rfl⟩⟩
  apply List.mem_flatMap.mpr
  refine ⟨.statement { id := continuation.entry.allocateStatementId.1
                       span := source.span
                       type := .unit
                       form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id) },
    continuation.original_retained, ?_⟩
  exact List.mem_singleton_self _

end InitializerContinuation
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
