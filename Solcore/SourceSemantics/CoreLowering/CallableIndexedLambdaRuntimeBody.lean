import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewMatchRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation

/-! Static runtime body receipts retain the actual lambda callback and accepted
view. Full imperative/match trees return to the canonical source through local
edit reachability. Numeric leaf support comes from the concrete builtin family.
The complete runtime ledger and dictionary come from the actual source closure
frame. Named, indirect and method children, and a combined callable recursion
argument, remain separate boundaries. No body execution law is stored here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

abbrev body_scope := @CallableIndexedLambdaSemanticInvocation.body_scope
abbrev loops_accepted := @CallableIndexedLambdaSemanticInvocation.loops_accepted

/-- The source frame carries runtime implementation rows and coverage of the
same complete context. Ordered parameter extension changes only lexical fields. -/
theorem context_valid {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements) :
    CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements inputs.context function.evidence := by
  exact (CompatibleRuntimeContextValidity.Valid.mk sameLedger frame.code.requirement_ledger frame.evidence_covers).mono inputs.extended

structure Body {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    extends CallableIndexedLambdaEntryPrefix.Context code where private mk ::
  frame : Dynamic.ClosureFrame program function
  readFuel : Nat
  policy : SourceCoreLoops.Policy
  callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy policy
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow
  projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
    code.compilation.internalReason code.compilation.internalReason
  actualTree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values code.view
    (CompatibleExpressionBuiltins.Syntax code.view)
    (fun context => CompatibleExpressionBuiltinRuntime.Certificate readFuel values code.view context
      code.compilation.solvedRequirements code.reasonAt)
    prepared.layouts.definitions administrative context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow
  actualSites : actualTree.CatalogSites .reachable registry faults
  tree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values function.source
    (CompatibleExpressionBuiltins.Syntax function.source)
    (fun context => CompatibleExpressionBuiltinRuntime.Certificate readFuel values function.source context
      code.compilation.solvedRequirements code.reasonAt)
    prepared.layouts.definitions administrative context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow
  sites : tree.CatalogSites .reachable registry faults
  valid : CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source

/-- The actual compiler-view Tree, its indexed diagnostics and the real flow
acceptance construct the canonical receipt; canonical recompilation is absent. -/
theorem Body.of_tree {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function) (readFuel : Nat) (policy : SourceCoreLoops.Policy)
    (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy policy)
    {changed : List ExpressionId}
    (edited : CallableLambdaViewEdits.LocalView function.source code.view changed)
    (avoids : CallableLambdaBodyReachability.Avoids function.source (function.body.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique function.source)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow)
    {tree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
      prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values code.view
      (CompatibleExpressionBuiltins.Syntax code.view)
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate readFuel values code.view context
        code.compilation.solvedRequirements code.reasonAt)
      prepared.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (sites : tree.CatalogSites .reachable registry faults) :
    ∃ body : Body code program registry faults,
      body.toContext = inputs ∧ body.readFuel = readFuel ∧ body.policy = policy ∧
      body.flow = flow ∧ HEq body.actualTree tree := by
  obtain ⟨canonical, canonicalSites⟩ := CallableLambdaViewMatchRuntimeCertificates.original edited avoids unique sites
  have accepted := loops_accepted code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  rw [generated] at accepted
  exact ⟨{
    toContext := inputs
    frame := frame
    readFuel := readFuel
    policy := policy
    callback := callback
    flow := flow
    generated := generated
    projection := projection
    emitted := Except.ok.inj accepted.symm
    actualTree := tree
    actualSites := sites
    tree := canonical
    sites := canonicalSites
    valid := context_valid code inputs frame sameLedger
    unique := unique }, rfl, rfl, rfl, rfl, HEq.rfl⟩


theorem Body.accepted {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {code : Code prepared function scope administrative} {program : Program}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : Body code program registry faults) :
    SourceCoreLoops.lowerStatementsWithPolicy body.policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body := loops_accepted code body.policy body.callback

abbrev Entry {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : Body code program registry faults) (profile : values.checked.catalog.callableContracts = true)
    (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location) (current : NativeFrame) (currentGhost : GhostFrame) :=
  CallableIndexedLambdaEntryPrefix.Entry captured code history body.toContext profile registry arguments nativeArguments
    before store location current currentGhost

/-- Nonempty captures and ordered parameters use the existing real entry
construction. The body receipt contributes its source context, never a body law. -/
theorem entry_exists {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : Body code program registry faults) (profile : values.checked.catalog.callableContracts = true)
    {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
      mapping world code.receipt.loweredParameters arguments nativeArguments)
    {before : Dynamic.Heap} {store : Store} {location : Location}
    {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
    (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
    (unmapped : location ∉ mapping)
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true) :
    Nonempty (Entry captured code history body profile arguments nativeArguments before store location current currentGhost) :=
  CallableIndexedLambdaEntryPrefix.entry_exists captured code history body.toContext profile
    represented heaps locals reference read currentCarried unmapped allowed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeBody
