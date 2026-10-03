import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime

/-! General expression meaning consumes numeric receipts only at the exact
literal leaves of the existing tree. Every unused ledger row remains present.
The support is static: actual whole-root compiler extraction is a separate step.
Constructor validity, mapping comparison, source metadata and runtime entry
conditions remain independent. No dictionary coverage is inferred. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntime
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

abbrev Certificate (fuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionGeneral.Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
    (context := context) (solved := solved) (reasonAt := reasonAt)
    (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)

/-- The support preserves the exact pre-existing grammar and emitted code. -/
theorem Certificate.forget {fuel values source context solved reasonAt scope id code}
    (receipt : Certificate fuel values source context solved reasonAt scope id code) :
    CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope id code :=
  receipt.choose

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
  CompatibleExpressionGeneral.preserves_with_literals functions extension faithful functionLeaves functionTypes
    program evidence unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtime unique faults)

include extension faithful functionLeaves functionTypes sameLedger runtime uninitialized missing in
/-- Original native completion reconstructs an independent source outcome.
No source execution or preservation law is an input. -/
theorem reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate fuel values source context solved reasonAt) faults :=
  CompatibleExpressionGeneral.reflects_with_literals functions extension faithful functionLeaves functionTypes
    program evidence uninitialized missing
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtime source faults)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntime
