import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerEvidence

/-! An authentic complete method resolver receipt survives parameter entry
and lexical context changes. The method's own assumptions remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerResolvedEvidence
open Frontend SourceInference
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (ResolvedCaller)
open CallableIndexedOwnedPreparedStagedMethodCallerEvidence (CallerAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}

def of_selected (principal : Principal compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (resolved : ResolvedCaller compiled.sourceProgram principal.named.specialized principal.dictionary)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context}
    (fields : Dynamic.RuntimeContextFields sourceAt.context context) :
    CallerAt principal context child.evidence := by
  have parameters := RecursiveNamedInitialContextValidity.mono_fields sourceAt.extended
  refine ⟨?_, fields.signatures.trans (parameters.signatures.trans rfl),
    fields.solvedRequirements.trans sourceAt.valid.ledger, ?_,
    (fields.runtimeRequirementLedger sourceAt.valid.runtime).idsUnique⟩
  · rw [stages.evidence selected]
    exact resolved
  · intro goal member
    rw [fields.assumptions, parameters.assumptions]
    change goal ∈ method.specialized.assumptions
    simpa only [principal.cached.same] using member

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerResolvedEvidence
