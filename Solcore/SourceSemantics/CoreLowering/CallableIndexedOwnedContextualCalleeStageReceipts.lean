import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeOriginReadReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedStageOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectNativePrefix

/-! Actual positive callee leaves supply their original artifact origin. Real
caller preparation then yields a user-callable Dispatch or the authentic builtin
row, whose absent user contract passes the first gate. Both paths retain the
original codebook request and physical counts. No selected hidden Code, guard
verdict, body execution law or receiving-model inverse is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeStageReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualCellOrigins
open CallableIndexedOwnedContextualCalleeOriginReadReceipts (CalleeAt)
open CallableIndexedOwnedIndirectSourceAdapters
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Only retained positive constructors are projected. Closures keep their
actual static member code/support; named and builtin branches use their real original
source-shaped leaf receipts and the actual projection-parameterized factory. -/
theorem function_origin {mapping : LocationMap} {world : StoreTyping}
    {raw : TypeSystem.Ty} {sourceValue : Dynamic.Value} {carrier : Value} {type : Ty}
    (positive : FunctionOrigins headers keys bodyRegistry faults mapping world raw sourceValue carrier type) :
    CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier := by
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  cases positive with
  | closure member =>
      exact member.stage_origin
  | global related =>
      cases related with
      | prior prior =>
          cases prior with
          | prior original =>
              cases original with
              | builtin builtin => cases builtin
              | named owner member sourceAt capture installed number projection descriptor typed =>
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

/-- Compatible raw views retain exactly the same positive function leaf. The
occurrence's raw type does not select its hidden code or native descriptor. -/
theorem callee_origin {mapping : LocationMap} {world : StoreTyping}
    {raw : TypeSystem.Ty} {sourceValue : Dynamic.Value} {carrier : Value} {type : Ty}
    (callee : CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := mapping) (world := world) raw sourceValue carrier type) :
    CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier := by
  obtain ⟨parameter, result, _view, positive⟩ := callee
  exact function_origin positive

/-- Builtins have no user staging contract. Their exact original row retains
its full request, entry origin, native tag and absent guard independently of
physical application arity, which is checked by the second gate. -/
structure BuiltinAt (sidecar : SourceCoreStageContracts.Sidecar)
    (site : SourceCoreCallableContracts.Callsite) (callee : ExpressionId)
    (ids : List ExpressionId) (metadata : IndirectCallResolution) (node : ExpressionNode)
    (function : Dynamic.BuiltinFunction) (carrier : Value) (row : SourceCoreStageCodebook.Decision) : Prop where
  selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata node row
  entryOrigin : row.entry.origin = .builtin function.id
  uncontracted : row.entry.contract = none
  shape : ∃ raw, carrier = .pair raw (.word row.entry.id)
  unguarded : row.guard = none

/-- Authentication retains the builtin's actual physical parameter list. -/
theorem BuiltinAt.parameter_count
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
    {function : Dynamic.BuiltinFunction} {carrier : Value} {row : SourceCoreStageCodebook.Decision}
    (receipt : BuiltinAt sidecar site callee ids metadata node function carrier row) :
    row.entry.parameterCount = function.id.parameterTypes.length := by
  have authenticated := receipt.selected.authenticated
  unfold CallEntryCertificates.Authenticated at authenticated
  rw [receipt.entryOrigin] at authenticated
  generalize count : row.entry.parameterCount = actualCount at authenticated
  generalize attached : row.entry.contract = actualContract at authenticated
  cases authenticated
  rfl

/-- A user contract retains real Dispatch; the builtin alternative retains its
real unguarded row. No impossible builtin user-contract binding is asserted. -/
inductive BoundaryAt (sidecar : SourceCoreStageContracts.Sidecar)
    (site : SourceCoreCallableContracts.Callsite) (callee : ExpressionId)
    (ids : List ExpressionId) (metadata : IndirectCallResolution) (node : ExpressionNode) :
    Dynamic.Value → Value → Prop where
  | user {sourceValue : Dynamic.Value} {carrier : Value}
      (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call ids sourceValue carrier)
      (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata node dispatch.row) :
      BoundaryAt sidecar site callee ids metadata node sourceValue carrier
  | builtin {function : Dynamic.BuiltinFunction} {carrier : Value} {row : SourceCoreStageCodebook.Decision}
      (receipt : BuiltinAt sidecar site callee ids metadata node function carrier row) :
      BoundaryAt sidecar site callee ids metadata node (.builtin function) carrier

section Caller
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (unique : NodeOccurrencesUnique source)

include caller sidecarSource unique in
/-- Real caller preparation and the exact positive callee construct the actual
row at this source call. User and builtin alternatives both retain the original
Generated request from this actual same-carrier origin; no uniform
post-to-Dispatch or guard law is an input. -/
theorem boundary_at_origin {sourceValue : Dynamic.Value} {carrier : Value}
    (actualOrigin : CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier) :
    BoundaryAt sidecar prepared.site callee ids metadata compiler.original sourceValue carrier := by
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  have atSite := stages.accepted
  rw [← prepared.table] at atSite
  have contains : ContainsExpression sidecar.source prepared.site.call compiler.original := by
    rw [sidecarSource, prepared.call]
    exact lookupExpression?_sound compiler.found
  have uniqueAt : NodeOccurrencesUnique sidecar.source := sidecarSource.symm ▸ unique
  have rows := CallCodebookCertificates.rows_of_prepareWithProjection atSite caller contains compiler.originalForm
  have origin : CallableLedger.OriginRep sidecar.plan prepared.site.table sourceValue carrier := by
    have plan := (CallContractCertificates.sidecar_of_accepted caller).1
    rw [plan, prepared.table]
    exact actualOrigin
  cases origin with
  | @closure function raw entry owner occurrence active contract member entryOrigin retained provenance =>
      obtain ⟨dispatch⟩ := CallableLedger.dispatch rows
        (CallableLedger.OriginRep.closure member entryOrigin retained provenance) provenance.binds
      have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages
        prepared.table caller contains compiler.originalForm uniqueAt dispatch.found
      exact .user dispatch selected
  | @named function raw entry key contract member entryOrigin retained target contractPrepared =>
      obtain ⟨dispatch⟩ := CallableLedger.dispatch rows
        (CallableLedger.OriginRep.named member entryOrigin retained target contractPrepared)
        (CallableLedger.Binds.named target contractPrepared)
      have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages
        prepared.table caller contains compiler.originalForm uniqueAt dispatch.found
      exact .user dispatch selected
  | @builtin function raw entry member entryOrigin retained =>
      obtain ⟨ledger⟩ := rows entry member
      have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages
        prepared.table caller contains compiler.originalForm uniqueAt ledger.found
      refine .builtin ⟨selected, ?_, ?_, ?_, ledger.builtin retained⟩
      · rw [ledger.entry_eq]; exact entryOrigin
      · rw [ledger.entry_eq]; exact retained
      · refine ⟨raw, ?_⟩
        rw [ledger.entry_eq]

include caller sidecarSource unique in
/-- The positive callee projection feeds the model-independent actual origin
factory. Diagnostic-free typed formation may use boundary_at_origin directly
with its own genuine same-code origin, without rebuilding a function model. -/
theorem boundary_at_callee {mapping : LocationMap} {world : StoreTyping}
    {raw : TypeSystem.Ty} {sourceValue : Dynamic.Value} {carrier : Value} {type : Ty}
    (calleeAt : CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := mapping) (world := world) raw sourceValue carrier type) :
    BoundaryAt sidecar prepared.site callee ids metadata compiler.original sourceValue carrier :=
  boundary_at_origin compiler prepared caller sidecarSource unique (callee_origin calleeAt)

include caller sidecarSource unique in
/-- A genuine successful child post classifies its retained positive payload
and constructs the actual first-gate boundary at that same value and state.
Raw callable shape remains a genuine Source fact; no native tag supplies it. -/
theorem boundary_at_post
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    {context : SourceSemantics.Context} {index : ProtectedStateTransition.Index}
    (reached : callerProtocol.State index)
    {calleeNode : ExpressionNode} {sourceValue : Dynamic.Value} {carrier : Value}
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (shape : IsFunction sourceValue)
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile calleeNode.type compiler.calleeCode.type
      (.value sourceValue) (.inRight .word carrier) reached) :
    BoundaryAt sidecar prepared.site callee ids metadata compiler.original sourceValue carrier ∧
    CallableIndexedOwnedSourceAdmission.Admission bridge context reached ∧
    CellOrigins headers keys bodyRegistry registry faults profile
      index.mapping index.world index.heap index.store ∧
    CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (faults := faults)
      (mapping := index.mapping) (world := index.world) calleeNode.type sourceValue carrier compiler.calleeCode.type := by
  have successful := post.at_value
  have calleeAt := CallableIndexedOwnedContextualCalleeOriginReadReceipts.callable_at profile successful.2.2 shape
  exact ⟨boundary_at_callee compiler prepared caller sidecarSource unique calleeAt,
    successful.1, post.cells, calleeAt⟩
end Caller

section BuiltinGate
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {function : Dynamic.BuiltinFunction} {carrier : Value} {row : SourceCoreStageCodebook.Decision}
  (receipt : BuiltinAt sidecar site callee ids metadata node function carrier row)

include receipt

/-- The authentic absent guard fixes the original first-gate native result.
Source builtin bypass and native row acceptance remain separate retained facts. -/
theorem BuiltinAt.first_gate (unknown : Word) (actual : Environment) (store : Store) :
    Evaluates (carrier :: actual) store
      (CallableContract.dispatch site.gates .beforeArguments unknown (.second (.var 0)))
      (.inRight .word .unit) store := by
  obtain ⟨raw, shape⟩ := receipt.shape
  have read : Evaluates (carrier :: actual) store (.second (.var 0)) (.word row.entry.id) store :=
    .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some shape))
  have accepted : row.beforeArguments = .ok () := by
    simp only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer, receipt.unguarded]
  have original := site.dispatch_known .beforeArguments unknown row.entry.id row receipt.selected.found read
  rw [SourceCoreCallableContracts.reason_accepted row site.reasonAt .beforeArguments accepted] at original
  simpa only [CallableContract.resultValue] using original

/-- An actual original first-gate prefix keeps its full remaining argument/
application trace and strict budget. The failed prefix is impossible only for
this authentic builtin row; no argument or body computation is performed. -/
theorem BuiltinAt.resolve_prefix {budget : Nat} {unknown : Word} {result : Ty}
    {arguments : Expr} {actual : Environment} {calleeStore finalStore : Store} {value : Value}
    (prefixTrace : CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget site unknown result arguments
      actual calleeStore carrier value finalStore) :
    Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) site.call ids (.builtin function) ∧
    ∃ size, EvaluationSize size (.unit :: carrier :: actual) calleeStore
      (CallableIndexedOwnedStoredIndirectNativePrefix.suffix site unknown result arguments) value finalStore ∧ size < budget := by
  have accepted := receipt.first_gate unknown actual calleeStore
  cases prefixTrace with
  | failed gate strict =>
      have same := (evaluation_deterministic gate.sound accepted).1
      cases same
  | passed gate remaining gateStrict suffixStrict =>
      obtain ⟨same, stores⟩ := evaluation_deterministic gate.sound accepted
      cases same
      subst stores
      exact ⟨.builtin function, _, remaining, suffixStrict⟩
end BuiltinGate

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeStageReceipts
