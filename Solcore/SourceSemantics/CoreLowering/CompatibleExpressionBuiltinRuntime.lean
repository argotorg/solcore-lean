import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntimeExtraction
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime

/-! Builtin expression meaning consumes numeric receipts only at the exact
literal leaves of the existing tree. Every unused ledger row remains present.
The support is static and follows actual accepted compiler children.
Constructor validity, mapping comparison, source metadata and runtime entry
conditions remain independent. No dictionary coverage is inferred. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

abbrev Certificate (fuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionBuiltins.Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
    (context := context) (solved := solved) (reasonAt := reasonAt)
    (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)

/-- The support preserves the exact pre-existing grammar and emitted code. -/
theorem Certificate.forget {fuel values source context solved reasonAt scope id code}
    (receipt : Certificate fuel values source context solved reasonAt scope id code) :
    CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id code :=
  receipt.choose

/-- Actual atomic acceptance supplies the exact validator-selected literal row. -/
theorem literalFactory {policy body context values source scope reasonAt} :
    CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate context.solvedRequirements source id code) := by
  intro id node fuel code found atomic unitType special readPolicy leafPolicy accepted
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted
  exact ⟨receipt.forget, receipt⟩

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (sameLedger : context.solvedRequirements = solved) (runtime : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful functionLeaves functionTypes sameLedger runtime unique uninitialized missing in
/-- Every independent source outcome is preserved using the complete runtime
ledger and actual selected rows at this tree's numeric leaves. -/
theorem preserves :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate fuel values source context solved reasonAt) faults :=
  CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful functionLeaves functionTypes
    program evidence unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtime unique faults)

include extension faithful functionLeaves functionTypes sameLedger runtime uninitialized missing in
/-- Original native completion reconstructs an independent source outcome.
No source execution or preservation law is an input. -/
theorem reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate fuel values source context solved reasonAt) faults :=
  CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful functionLeaves functionTypes
    program evidence uninitialized missing
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtime source faults)

/-- One supported compiler traversal closes all builtin and general-expression literal leaves. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (CompatibleExpressionBuiltins.Syntax source))
    (policyFor : CompatibleExpressionBuiltins.PolicyFor policy context readFuel values source scope reasonAt)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (coercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : CompatibleExpressionBuiltins.Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Certificate readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  exact CompatibleExpressionBuiltins.tree_of_functions_with_literals _ literalFactory unique declarations signatures
    constructorValid policyFor native active profile coercions syntaxTree found typed accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime
