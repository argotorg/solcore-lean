import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureStaticTransport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds

/-! The finite terminal packet comes from the same accepted compiler-view tree
at the literal parameter inputs. Its read policy, authenticated selected Source
scope and reached read-diagnostic interpretation remain genuine static fields.
The raw registry is independently selected; no execution law is stored. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureTerminalPackets
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedLambdaValues

/-- The same finite compiler-view tree constructs the retained parent packet
without a pre-supplied BodyWith or certificate-transport callback. -/
theorem of_tree {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (readFuel : Nat) (policy : SourceCoreLoops.Policy)
    (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy policy)
    {changed : List ExpressionId}
    (edited : LocalView function.source code.view changed)
    (avoids : Avoids function.source (function.body.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique function.source)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow)
    {tree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) code.view
      (CompatibleExpressionProducts.Syntax code.view)
      (CallableIndexedOwnedPreparedStagedFiniteClosureBodyBounds.Family (compiled := compiled) code readFuel code.view)
      compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow}
    (registry : SourceCoreRawMetadata.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (sites : tree.CatalogSites .reachable registry semanticFaults)
    (stages : Staging.Recursive.Registry)
    (expression : ExpressionId)
    (shape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      code.view expression function.body)
    (reader : policy.readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (uninitialized : ∀ current id lowered,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        function.source inputs.context code.reasonAt current id lowered →
      ∀ location, semanticFaults (.uninitializedLocation location) (code.reasonAt id)) :
    ∃ packet : CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds.FiniteTerminal
        (compiled := compiled) code inputs registry semanticFaults stages,
      packet.expression = expression ∧ packet.child = child ∧
      packet.body.readFuel = readFuel ∧ packet.body.policy = policy ∧
      packet.body.flow = flow ∧ HEq packet.body.actualTree tree := by
  obtain ⟨finite, sameContext, sameReadFuel, samePolicy, sameFlow, sameTree⟩ :=
    CallableIndexedOwnedPreparedStagedFiniteClosureStaticTransport.of_tree
      code inputs frame readFuel policy callback edited avoids unique sameLedger
      projection generated registry semanticFaults sites
  exact ⟨{
    body := finite
    sameContext := sameContext
    expression := expression
    shape := shape
    reader := by rw [samePolicy]; exact reader
    child := child
    selected := selected
    uninitialized := by simpa only [sameReadFuel, sameContext] using uninitialized },
    rfl, rfl, sameReadFuel, samePolicy, sameFlow, sameTree⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureTerminalPackets
