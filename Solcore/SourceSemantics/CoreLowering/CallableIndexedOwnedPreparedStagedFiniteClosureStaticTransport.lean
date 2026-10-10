import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewScalarTrees

/-! Finite syntax and selected literal/read receipts cross an actual local
compiler view only at reached, unedited body occurrences. The same accepted
body tree then constructs fixed finite closure support without caller-supplied
certificate transports. Original raw typing remains the parameter-frame proof;
no execution law or typing equality is inferred from a metadata view. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureStaticTransport
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedLambdaValues CallableIndexedLambdaStaticBodySupport

section Transport
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
include edited avoids

/-- The finite syntax follows actual reference edges and full node lookup. -/
theorem finite_syntax {id : ExpressionId} (finite : CompatibleExpressionProducts.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionProducts.Syntax view id := by
  revert reached
  induction finite with
  | literal found atomic =>
      intro reached
      exact .literal ((expression_lookup edited avoids reached).symm.trans found) atomic
  | read found form =>
      intro reached
      exact .read ((expression_lookup edited avoids reached).symm.trans found) form
  | @group id node inner found form child ih =>
      intro reached
      have childReached : Reaches source roots (.expression inner) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      exact .group ((expression_lookup edited avoids reached).symm.trans found) form (ih childReached)
  | @pair id node left right found form first second firstIH secondIH =>
      intro reached
      have firstReached : Reaches source roots (.expression left) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      have secondReached : Reaches source roots (.expression right) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      exact .pair ((expression_lookup edited avoids reached).symm.trans found) form
        (firstIH firstReached) (secondIH secondReached)

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}

/-- LiteralSites stay paired with the exact transported compiler tree. -/
theorem literal_sites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered}
    (sites : tree.LiteralSites
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code))
    (reached : Reaches source roots (.expression id)) :
    (CallableLambdaViewScalarTrees.products edited avoids tree reached).LiteralSites
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved view id code) := by
  revert reached
  induction sites with
  | literal receipt selected =>
      intro reached
      exact .literal
        (CallableLambdaViewExpressionLeaves.literal edited avoids reached receipt)
        (CallableLambdaViewMatchRuntimeCertificates.literal edited avoids selected reached)
  | read receipt =>
      intro reached
      exact .read (CallableLambdaViewExpressionLeaves.loweredRead edited avoids reached receipt)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree childSites ih =>
      intro reached
      have child : Reaches source roots (.expression inner) :=
        .expression reached receipt.found (by simp [form, ExpressionForm.references])
      exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
        ((expression_lookup edited avoids child).symm.trans innerFound) sourceType
        (CallableLambdaViewScalarTrees.products edited avoids tree child) (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType
      firstTree secondTree firstSites secondSites firstIH secondIH =>
      intro reached
      have leftReached : Reaches source roots (.expression left) :=
        .expression reached receipt.found (by simp [form, ExpressionForm.references])
      have rightReached : Reaches source roots (.expression right) :=
        .expression reached receipt.found (by simp [form, ExpressionForm.references])
      exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
        ((expression_lookup edited avoids leftReached).symm.trans leftFound)
        ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
        (CallableLambdaViewScalarTrees.products edited avoids firstTree leftReached)
        (CallableLambdaViewScalarTrees.products edited avoids secondTree rightReached)
        (firstIH leftReached) (secondIH rightReached)

/-- The fixed finite certificate retains its actual tree and selected sites. -/
theorem certificate {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate fuel values
      source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate fuel values
      view context solved reasonAt scope id lowered := by
  obtain ⟨tree, sites⟩ := receipt
  exact ⟨CallableLambdaViewScalarTrees.products edited avoids tree reached,
    literal_sites edited avoids sites reached⟩

/-- The original reachability path supplies the reverse syntax transport. -/
theorem syntax_original {id : ExpressionId}
    (finite : CompatibleExpressionProducts.Syntax view id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionProducts.Syntax source id := by
  have reverse : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact finite_syntax reverse (avoids.view edited.metadata) finite (reached.metadata edited.metadata)

/-- The reverse certificate transports only authentic reached occurrences. -/
theorem certificate_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate fuel values
      view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate fuel values
      source context solved reasonAt scope id lowered := by
  have reverse : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact certificate reverse (avoids.view edited.metadata) receipt (reached.metadata edited.metadata)
end Transport

/-- The accepted finite compiler-view tree supplies both reachable callbacks
internally. Its context and target registry remain actual static inputs. -/
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
    (sites : tree.CatalogSites .reachable registry semanticFaults) :
    ∃ body : CallableIndexedOwnedPreparedStagedFiniteClosureBodyBounds.FiniteBody (compiled := compiled) code registry semanticFaults,
      body.toContext = inputs ∧ body.readFuel = readFuel ∧ body.policy = policy ∧
      body.flow = flow ∧ HEq body.actualTree tree := by
  exact BodyWith.of_tree (values := .initial compiled.compatible.checked) (prepared := compiled.indexed)
    (expressionSyntax := CompatibleExpressionProducts.Syntax)
    (certificates := CallableIndexedOwnedPreparedStagedFiniteClosureBodyBounds.Family (compiled := compiled) code)
    code inputs frame readFuel policy callback edited avoids unique sameLedger
    (fun id reached finite => syntax_original edited avoids finite reached)
    (fun context current id lowered reached receipt =>
      certificate_original (fuel := readFuel) (values := .initial compiled.compatible.checked)
        (context := context) (scope := current) (id := id) (lowered := lowered)
        edited avoids receipt reached)
    projection generated sites

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureStaticTransport
