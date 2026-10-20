import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfileReceipts
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyCollector
import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyExpressions
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaScopeDeclarations

/-! Original closure typing and actual contextual compilation produce the
whole lexical body tree at the real parameter scope. Every leaf is extracted
from its own accepted callback, including issued reads and numeric literals. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyAdmission
open Core Frontend SourceInference GeneralHeap
open GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code)
  {program : Program} (frame : Dynamic.ClosureFrame program function)

def scope : SourceCoreLocalCell.Scope :=
  material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id,binding.2)) ++ material.inputs.scope

theorem binder_policy : ∀ current binder, binder.scheme.quantified = [] →
    (GeneralizedLocalBodyCompiler.policy material).lowerBinder material.code.view current binder =
      SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked material.code.view current binder := by
  intro current binder mono
  change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
  simp only [SourceCoreGeneralFunctions.contextualBinder,mono,List.isEmpty_nil,↓reduceIte]
  unfold GeneralizedLocalLambdaCompilation.representation
  rw [material.indexed.represented]
  rfl

theorem allocation_policy : (GeneralizedLocalBodyCompiler.policy material).sourceCells =
    some (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
      compiled.indexed.base.globals.length (compiled.indexed.layouts.allocatorAt material.code.compilation.owner
        material.code.active material.code.allocationError)) := by
  have accepted := material.code.allocationProfile
  rw [material.policy] at accepted
  exact accepted

theorem result_projected : compiled.compatible.checked.catalog.project function.resultType = .ok material.code.receipt.resultCore := by
  have accepted := material.code.receipt.resultProjected
  simp only [material.policy,material.indexed.projector] at accepted
  exact CompatibleExpressionReads.projectType_of_accepted accepted

include frame in
theorem tree : ∃ flow,
    material.code.receipt.body = CompatibleStatements.finish material.code.receipt.resultCore flow
      material.code.compilation.internalReason material.code.compilation.internalReason ∧
    CellAwareOrdinaryBodyTree.Tree compiled.indexed.layouts material.code.compilation.owner material.code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length material.code.allocationError
      (.initial compiled.compatible.checked) function.source
      (CellAwareLexicalBodyExpressions.StaticCertificate compiled.compatible.checked function.source material.code.reasonAt)
      inputs.context (scope material) true function.body function.resultType material.code.receipt.resultCore flow := by
  have compilerSource := GeneralizedLocalBodyProfileReceipts.view_source material
  have unique : NodeOccurrencesUnique material.code.view := by simpa only [compilerSource] using material.unique
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_parameters
    (values := .initial compiled.compatible.checked) material.code inputs frame material.capturedDeclarations
  obtain ⟨finalContext,facts,bodyTyped,_completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame inputs.extended
  rw [← compilerSource] at declarations bodyTyped
  have syntaxTree := CellAwareOrdinaryBodySyntax.of_scan (GeneralizedLocalBodyProfileReceipts.scan material)
    unique (GeneralizedLocalBodyProfileReceipts.lexical material) rfl bodyTyped
  have expressions : ∀ sourceContext, ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations material.code.view scope sourceContext →
      GeneralizedLocalOrdinaryExpressionProfile.Tree material.inputs.locals material.inputs.current.owner material.code.view id →
      material.code.view.lookupExpression? id = some node → ExpressionHasType material.code.view sourceContext id node.type →
      (GeneralizedLocalBodyCompiler.policy material).lowerExpression fuel material.code.view scope id material.code.reasonAt = .ok lowered →
      CellAwareLexicalBodyExpressions.StaticCertificate compiled.compatible.checked material.code.view material.code.reasonAt sourceContext scope id lowered := by
    intro sourceContext current fuel id node lowered declarations profile found typed accepted
    rw [GeneralizedLocalBodyCompiler.expression_reader] at accepted
    refine ⟨compiled.indexed.fuel,material.code.compilation.solvedRequirements,node,found,typed,?_⟩
    exact GeneralizedLocalBodyExpressionCertificate.of_accepted material profile unique declarations found typed accepted
  have result := CellAwareOrdinaryBodyCollector.tree_of_body (values := .initial compiled.compatible.checked) (GeneralizedLocalBodyCompiler.statement_reader material)
    (binder_policy material) (allocation_policy material) expressions syntaxTree declarations (result_projected material)
    (CallableIndexedLambdaSemanticInvocation.loops_accepted (values := .initial compiled.compatible.checked)
      material.code (GeneralizedLocalBodyCompiler.policy material) (GeneralizedLocalBodyCompiler.callback material))
  simpa only [compilerSource,scope] using result

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyAdmission
