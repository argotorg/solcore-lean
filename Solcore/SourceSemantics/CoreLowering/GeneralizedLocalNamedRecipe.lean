import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipeCompilation

/-! Actual named caller and allocation histories instantiate the checked static
read recipe. The selected target keeps its entire specialization key. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipeCompilation
open Core Frontend SourceInference TypeSystem
open CallableIndexedNamedGeneration (Prepared state)
open CallableIndexedHistory

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id : ExpressionId}

/-- Runtime histories authenticate the two real parents of the static recipe. -/
def Observations.recipe (observed : Observations prepared named source id)
    {callerGhost lexicalGhost : GhostFrame} {caller lexical : MetadataState}
    (callerEq : caller = state named) (lexicalEq : lexical = state named)
    (callerHistory : CallableAncestryPairedLookup.Authenticates prepared.ancestry.graph.inputs callerGhost (some caller))
    (lexicalHistory : CallableAncestryPairedLookup.Authenticates prepared.ancestry.graph.inputs lexicalGhost (some lexical)) :
    CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost lexicalGhost caller lexical
      observed.entry.id observed.target := by
  subst caller
  subst lexical
  exact ⟨callerHistory, lexicalHistory, observed.read, observed.readAccepted, observed.applied, observed.appliedAccepted⟩

theorem Observations.recipe_fields (observed : Observations prepared named source id)
    {callerGhost lexicalGhost : GhostFrame} {caller lexical : MetadataState}
    (callerEq : caller = state named) (lexicalEq : lexical = state named)
    (callerHistory : CallableAncestryPairedLookup.Authenticates prepared.ancestry.graph.inputs callerGhost (some caller))
    (lexicalHistory : CallableAncestryPairedLookup.Authenticates prepared.ancestry.graph.inputs lexicalGhost (some lexical)) :
    let recipe := observed.recipe callerEq lexicalEq callerHistory lexicalHistory
    recipe.read.entry = observed.read.entry ∧ recipe.read.binder = observed.read.binder ∧
      recipe.read.node = observed.read.node := by
  subst caller
  subst lexical
  exact ⟨rfl, rfl, rfl⟩

variable {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {certificate : GeneralizedLocalNamedReadCompilation.Certificate prepared named source scope id reasonAt lowered}

theorem Receipt.target (receipt : Receipt certificate) :
    prepared.ancestry.graph.inputs.callable.table.idAt?
      (.lambda certificate.read.candidate.origin.caller certificate.read.candidate.origin.initializer
        certificate.read.candidate.origin.substitution) = some receipt.observations.target := by
  rw [← receipt.candidate, receipt.observations.origin]
  exact receipt.observations.targetSelected

theorem Receipt.initializer (receipt : Receipt certificate) :
    receipt.observations.read.entry.view.principal.initializer = certificate.read.binding.initializer :=
  receipt.observations.initializer.trans (congrArg (·.initializer) receipt.binding)

theorem Receipt.scheme (receipt : Receipt certificate) :
    receipt.observations.read.binder.scheme = certificate.read.binding.binder.scheme :=
  receipt.observations.scheme.trans (congrArg (fun binding => binding.binder.scheme) receipt.binding)

theorem Receipt.candidate_initializer (receipt : Receipt certificate) :
    certificate.read.candidate.origin.initializer = certificate.read.binding.initializer := by
  rw [← receipt.candidate, ← receipt.binding]
  exact receipt.observations.candidateInitializer

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipeCompilation
