import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds

/-! Every indirect head obtains its callsite from the actual named compiler
policy and its sidecar from the actual named invocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallPorts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : Compilation compiled.indexed named diagnostics code)
  {rootFuel fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt (namedPolicy generation rootFuel)
    (namedLowerBody generation) fuel (context compiled.indexed named)
    source scope id callee ids metadata reasonAt lowered)

include compiler in
theorem read_policy :
    (namedPolicy generation rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id := by
  have viewed : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed named).plan compiled.indexed.base.locals named.signature.key none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, compiler.found, compiler.originalForm]
  simp only [namedPolicy, viewed, bind, Except.bind]
  rfl

theorem callable_policy :
    (namedPolicy generation rootFuel).callables = SourceCoreGeneralFunctions.callablePolicy
      (some compiled.indexed.ancestry.graph.inputs.callable) [] := by
  change SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [] = _
  rw [compiled.indexed.ancestry.graph.inputs.callableSelected]

theorem function_type : (namedPolicy generation rootFuel).callables.functionType = CallableContract.functionType := by
  rw [callable_policy generation]
  rfl

structure Authority (named : SourceCoreGeneralFunctions.Function) (invocation : Staging.Recursive.Scope) where
  sidecar : SourceCoreStageContracts.Sidecar
  caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan named.signature.key = .ok sidecar
  view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source invocation.source
  guardFrame : invocation.guards = CallableLedger.frame sidecar
  unique : NodeOccurrencesUnique sidecar.source

theorem port {invocation : Staging.Recursive.Scope}
    (authority : Authority (compiled := compiled) named invocation)
    (sourceEq : invocation.source = source)
    (parent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
    (calleeReceipt : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      source scope callee reasonAt compiler.calleeCode) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
      (compiled := compiled) (invocation := invocation) compiler) := by
  obtain ⟨prepared⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.prepared
    compiler (read_policy generation compiler) [] (callable_policy generation)
  refine ⟨{ prepared := prepared
            sidecar := authority.sidecar
            caller := ?_
            view := ?_
            guardFrame := authority.guardFrame
            originalUnique := authority.unique
            sourceParent := parent
            calleeNode := calleeReceipt.observations.original
            calleeFound := calleeReceipt.observations.originalFound }⟩
  · rw [prepared.caller]
    exact authority.caller
  · simpa only [sourceEq] using authority.view

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallPorts
