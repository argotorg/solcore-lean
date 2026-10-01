import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSemanticReceipt

/-! Lambda body semantics at the canonical source retain the actual compiler
view separately. The real lambda callback and parameter fold provide the view
acceptance equation; no canonical body compiler equation is needed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

structure Body {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program)
    extends CallableIndexedLambdaEntryPrefix.Context code where
  frame : Dynamic.ClosureFrame program function
  readFuel : Nat
  certificate : BuiltinNamedBody.SemanticReceipt prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError readFuel values
    function.source context code.compilation.solvedRequirements code.reasonAt
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body function.resultType code.receipt.resultCore code.compilation.internalReason
    code.compilation.internalReason code.receipt.body
  valid : CompatibleExpressionLiterals.ContextValid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source

abbrev parameters := @CallableIndexedLambdaEntryPrefix.parameters
abbrev prefix_accepted := @CallableIndexedLambdaEntryPrefix.prefix_accepted

abbrev Entry {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
    (registry : SourceCoreRawMetadata.Registry) (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location) (current : NativeFrame) (currentGhost : GhostFrame) :=
  CallableIndexedLambdaEntryPrefix.Entry captured code history body.toContext profile registry arguments nativeArguments
    before store location current currentGhost

/-- The parameter scope is extracted from the real lambda binder action. -/
theorem body_scope {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) :
    code.receipt.bodyScope = code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
  simpa only [List.map_reverse] using (FunctionCode.Parameters.of_accepted code.receipt.parametersCompiled).scope

/-- Only the actual callback equation changes the compiler action into its
loop-body API; the accepted source argument remains the real view. -/
theorem loops_accepted {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (policy : SourceCoreLoops.Policy)
    (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy policy) :
    SourceCoreLoops.lowerStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body := by
  have accepted := code.receipt.bodyCompiled
  rw [callback, body_scope code] at accepted
  exact accepted

structure ViewBody {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program) where private mk ::
  body : Body code program
  policy : SourceCoreLoops.Policy
  callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy policy
  actual : CallableLambdaViewSemanticReceipt.Receipt prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError body.readFuel values
    function.source code.view body.context code.compilation.solvedRequirements code.reasonAt
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body function.resultType code.receipt.resultCore policy code.fuel code.compilation.internalReason
    code.compilation.internalReason code.receipt.body
  semantic : body.certificate = actual.canonical

/-- Build canonical semantics from static syntax/Tree at the actually compiled
view, retaining that view's accepted equation and the exact callback identity. -/
theorem ViewBody.of_tree {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
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
    (valid : CompatibleExpressionLiterals.ContextValid code.compilation.solvedRequirements inputs.context function.evidence)
    (projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    (syntaxTree : BuiltinLexicalStatements.Syntax code.view inputs.context true function.body function.resultType)
    {flow : Expr}
    (emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
      code.compilation.internalReason code.compilation.internalReason)
    (tree : BuiltinLexicalStatements.Tree prepared.layouts code.compilation.owner code.active prepared.ancestry.layout.frame
      prepared.base.globals.length code.allocationError readFuel values code.view code.compilation.solvedRequirements code.reasonAt
      inputs.context (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      true function.body function.resultType code.receipt.resultCore flow) :
    Nonempty (ViewBody code program) := by
  obtain ⟨actual⟩ := BuiltinNamedBody.of_tree (loops_accepted code policy callback) projection syntaxTree emitted tree
  let receipt := CallableLambdaViewSemanticReceipt.of_certificate (statements := function.body) edited avoids unique actual
  exact ⟨⟨{ toContext := inputs, frame, readFuel, certificate := receipt.canonical, valid, unique },
    policy, callback, receipt, rfl⟩⟩

/-- Every native prefix step is derived from its actual compiler receipt.
The caller token and lexical token have independent carried histories. -/
theorem entry_exists {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
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
    Nonempty (Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost) := by
  exact CallableIndexedLambdaEntryPrefix.entry_exists captured code history body.toContext profile
    represented heaps locals reference read currentCarried unmapped allowed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation
