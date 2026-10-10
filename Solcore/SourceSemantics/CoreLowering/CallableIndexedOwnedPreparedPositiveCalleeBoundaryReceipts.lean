import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveFunctionOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeStageReceipts

/-! The receiving positive function model retains enough actual provenance to
construct the original selected call boundary. Compatible raw views preserve
that same callee. User dispatch and builtin rows remain independent of guard
acceptance, physical arity and body execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveCalleeBoundaryReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
open CallableIndexedOwnedIndirectSourceAdapters

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty}
  {sourceValue : Dynamic.Value} {carrier : Value} {type : Ty}

/-- Only original retained Source, Code and descriptor constructors are used.
No legacy closure support or semantic diagnostic law is manufactured. -/
theorem function_origin
    (positive : FunctionOrigins qualification headers keys bodyRegistry faults profile
      mapping world raw sourceValue carrier type) :
    CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier := by
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  cases positive with
  | closure member =>
    obtain ⟨packet⟩ := member
    cases packet.association with
    | ordinary owner captured code history support origin prepared qualified prefixContext globals referenceIndex typed =>
      exact CompatibleAmbientStageOrigins.actual_lambda_origin stages.accepted code.descriptor
        support.source_receipt code.viewOfSource support.unique code.found
        (code.form.trans code.sourceForm) _
    | principal owner captured code history support origin prepared qualified globals leading referenceIndex typed =>
      exact CompatibleAmbientStageOrigins.actual_lambda_origin stages.accepted code.descriptor
        support.source_receipt code.viewOfSource support.body.unique code.found
        (code.form.trans code.sourceForm) _
  | global member =>
    obtain ⟨packet⟩ := member
    cases packet with
    | named origin member sourceAt capture installed number projection descriptor typed =>
      apply RecursiveStageProjection.named_origin stages.accepted descriptor
      rw [sourceAt.retained]
      simpa only [CallableNamedReversal.global, CallableNamedReversal.target_reverse,
        CallableNamedMetadata.global] using sourceAt.row.target
  | builtin related =>
    cases related with
    | prior prior =>
      cases prior with
      | prior original =>
        cases original with
        | builtin builtin =>
          cases builtin with
          | builtin selected number descriptor typed =>
            exact RecursiveStageProjection.builtin_origin stages.accepted descriptor _

/-- Compatible type views are projected forward from the genuine positive
payload. The Source callable shape remains a separate raw typing fact. -/
theorem payload_origin
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world raw sourceValue carrier type) :
    IsFunction sourceValue → CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function positive => intro _; exact function_origin positive
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro callable; cases callable
  | nil | cons | empty | entry | absent | present => trivial

section Caller
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {sidecar : SourceCoreStageContracts.Sidecar}

include compiler prepared in
/-- The original same-caller row factory runs once at the actual positive
callee. Its user or builtin alternative retains the authentic selected row. -/
theorem boundary_at_payload
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
    (sidecarSource : sidecar.source = source)
    (unique : NodeOccurrencesUnique source)
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world raw sourceValue carrier type)
    (shape : IsFunction sourceValue) :
    CallableIndexedOwnedContextualCalleeStageReceipts.BoundaryAt
      sidecar prepared.site callee ids metadata compiler.original sourceValue carrier :=
  CallableIndexedOwnedContextualCalleeStageReceipts.boundary_at_origin compiler prepared caller sidecarSource unique
    (payload_origin represented shape)

end Caller
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveCalleeBoundaryReceipts
