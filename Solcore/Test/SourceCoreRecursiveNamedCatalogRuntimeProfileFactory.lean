import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
import Solcore.Test.SourceCoreRecursiveNamedCatalogRuntimeMutualMeaning
import Solcore.Test.SourceCoreRecursiveNamedCatalogNativeContexts

/-! Actual cached typing and entry data supply the body native context. The
same compiler inputs produce a runtime profile, without ordinary ledger
validity, arbitrary Profile providers or body execution assumptions. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreRecursiveNamedCatalogRuntimeProfileFactory
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds RecursiveNamedCatalogNativeContexts
open RecursiveNamedCatalogRuntimeProfileFactory NativeExpressionContextSupport

section Actual
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {administrative : Core.Context} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {tracked : Bool} {suffix : Core.Context}
  (inputs : Inputs tracked diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
    (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
    header.named.signature.functionType ambient.definitions)
  (support : supported (.lambda header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
  (complete : Complete headers) (globals : header.globals = base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include inputs cachedTyped support complete globals entry in
theorem actual_extraction : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :=
  extract_source inputs cachedTyped support complete globals entry

include inputs cachedTyped support complete globals entry in
theorem actual_provider (catalog : SignatureCatalogWellFormed values.checked.signatures) :
    ∃ result : Receipt diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ faults : FunctionCalls.FaultRep, result.extracted.diagnostics registry faults →
        ∃ profile : RuntimeMatchProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
            (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults,
          profile.flow = result.flow ∧ HEq profile.tree result.extracted.tree :=
  provider inputs cachedTyped support complete globals entry catalog

variable (result : Receipt diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (catalog : SignatureCatalogWellFormed values.checked.signatures) {faults : FunctionCalls.FaultRep}
  (interpreted : result.extracted.diagnostics registry faults)

theorem same_flow : (result.profile catalog interpreted).flow = result.flow := rfl

theorem same_tree : (result.profile catalog interpreted).tree = result.extracted.tree := rfl

include catalog interpreted in
theorem same_emitted_body : header.body = CompatibleStatements.finish header.output
    (result.profile catalog interpreted).flow header.fellThrough header.escaped :=
  (result.profile catalog interpreted).emitted

/-- Runtime validity does not drop the templates/unused rows in the source ledger. -/
theorem same_full_ledger :
    header.context.solvedRequirements = header.solved ∧ inputs.matchCompilation.solvedRequirements = header.solved :=
  ⟨header.valid.ledger, inputs.matchLedger⟩

include inputs in
theorem actual_expression_child {context : SourceSemantics.Context}
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = true)
    (signatures : context.signatures = values.checked.signatures)
    {scope : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source scope context)
    (syntaxTree : expressionSyntax id) (found : header.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType header.function.source context id node.type)
    (accepted : header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered) :
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation header.readFuel header.function.source
      context header.solved header.reasonAt scope id lowered :=
  inputs.expressions context closed residual signatures declarations syntaxTree found typed accepted

theorem actual_residual : header.context.typeVariables = [] ∧ header.context.residualTypeVariables = true :=
  RecursiveNamedSourceContextFacts.header_fields header
end Actual

abbrev unused_ledger := SourceCoreRecursiveNamedCatalogRuntimeMatchProfiles.fields_not_ordinary

def run : IO Unit := do
  SourceCoreRecursiveNamedCatalogRuntimeMutualMeaning.run
  SourceCoreRecursiveNamedCatalogNativeContexts.run
  IO.println "runtime profile factory: same cached code / actual body entry / full ledger / static compiler extraction and diagnostics GREEN"

end Tests.SourceCoreRecursiveNamedCatalogRuntimeProfileFactory
