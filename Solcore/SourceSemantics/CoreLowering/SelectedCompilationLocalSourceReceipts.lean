import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedCatalogFormation

/-! The actual caller and read packets select the same original final-plan row.
This equality comes from their common exact key, independently of runtime
Source history or equality of lambda headers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalSourceReceipts
open Core Frontend SourceInference TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {relation : TypedSource → TypedSource → Prop}

/-- The native caller's actual view has exactly its accepted flexible action. -/
theorem compiler_source
    (material : GeneralizedLocalAcceptedMaterialization.Materialization
      compiled mapping world function relation) :
    material.code.view = material.candidate.origin.source.applySubstitution material.code.active := by
  rw [material.view, material.active, GeneralizedLocalLambdaEmissionFacts.Emission.source,
    GeneralizedLocalLambdaEmissionFacts.Emission.substitution]

/-- Both accepted factories resolve the exact caller key in the same final
plan. The target binding source is identified by the real read catalog entry. -/
theorem read_source
    (material : GeneralizedLocalAcceptedMaterialization.Materialization
      compiled mapping world function relation)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals
      material.code.compilation.owner material.code.active material.code.view scope id reason lowered)
    {inputs : Inputs} {raw : Core.Expr} (packet : Packet inputs receipt.candidate raw)
    (indexed : Indexed compiled.indexed packet) :
    material.candidate.origin.source = receipt.binding.source := by
  obtain ⟨callerRow, callerSelected, callerSource, _, _⟩ :=
    LambdaSourceAlignment.prepared_source material.packet.original.emission.authentic
  obtain ⟨targetRow, targetSelected, targetSource, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [material.indexed.plan] at callerSelected
  rw [indexed.plan] at targetSelected
  have owner : material.code.compilation.owner = material.candidate.origin.caller := by
    rw [material.compilation]
    exact material.indexed.owner
  have origins := GeneralizedLocalAcceptedCatalogFormation.read_origins receipt
  rw [origins.1, owner] at targetSelected
  have same : callerRow = targetRow := Except.ok.inj (callerSelected.symm.trans targetSelected)
  rw [same] at callerSource
  exact callerSource.symm.trans (targetSource.trans origins.2.1)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalSourceReceipts
