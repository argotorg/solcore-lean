import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins

/-! One original principal formation produces the genuine Source/native trace.
The formation copies the captured cells, so the retained prepared principal
support constructs its prospective positive receipt for the formed closure over
the copies. The same trace adds Source admission and the existing positive post
at the reached packet transported to the formed state. No old StaticMember
is inverted and no body callback is supplied. The current payload model still
stores the forward plain leaf; migration to prepared leaves remains separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedPrincipalLambdaSupport (Support PreparedAt Receipt)
open CallableIndexedOwnedContextualCellOrigins (CellOrigins PostWithOrigins)
open CallableIndexedOwnedSourceAdmission

section Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The prepared principal seed of a code is the seed of the same code over
other captures. -/
theorem prepared_recapture {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code} (prepared : PreparedAt code support) (environment : Dynamic.Environment) :
    PreparedAt (code.recapture environment) (support.recapture environment) := by
  cases prepared with
  | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView _ =>
    exact .recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView environment

/-- A prepared principal code is the lambda of a selected method Site, which
copies its captures. -/
theorem prepared_snapshots {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code} (prepared : PreparedAt code support) :
    code.policy.snapshotLambda code.id = true := by
  cases prepared with
  | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView environment =>
    exact site.snapshots

end Prepared

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : PreparedAt code support)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "plain" => support.plain actualSites sites
local notation "history" => CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
  captured code plain owner initial packet
local notation "carrier " formed:max => value code (Formed.embedding formed)
  (CallableIndexedLambdaValues.History.native history) (Formed.closureActual formed)

include actualSites sites packet prepared profile in
/-- The authentic method factory runs once and copies the captured cells.
Preparation is retained from its own support, recaptured at the copies, and
runtime typing comes from that actual formed value. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (carrier formed)) formed.finalStore ∧
      Nonempty (Receipt headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (carrier formed)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (carrier formed) ∧
          finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation
      captured code plain owner initial packet profile heaps (prepared_snapshots prepared) ordinary coercions
  have typed : RuntimeValueHasType formed.finalWorld (carrier formed)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions :=
    (CallableIndexedOwnedMethodLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
      (registry := bodyRegistry) represented
  have leading : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code plain owner initial packet
  exact ⟨formed, sourceTrace, nativeTrace,
    ⟨.principal (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) actualSites sites ⟨rfl⟩ (prepared_recapture prepared formed.captured)
      (packet.observed.of_slots formed.slots) leading
      (CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code plain) typed⟩,
    determined⟩

variable
  (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include actualSites sites cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile in
/-- The prepared receipt and current positive post accompany the same actual
Source/native formation over the copies, at the reached packet transported to
the formed state. The factory is invoked once; only the new value erases
forward into the current plain positive model. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
        captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (carrier formed)) formed.finalStore ∧
      Nonempty (Receipt headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (carrier formed)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore) ∧
      (∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner
          support.principal.named).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩,
        (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates
          ⟨initial, packet⟩ reached ∧
        PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
          function.context profile code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure))
          (.inRight .word (carrier formed)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (carrier formed) ∧
          finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code support actualSites sites prepared owner initial packet profile cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure))
      (.inRight .word (carrier formed)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    obtain ⟨receipt⟩ := member
    exact CallableIndexedOwnedContextualCellOrigins.payload_static_member (registry := registry) profile ⟨receipt.forget⟩
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
    (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member,
    ⟨reached, related,
      CallableIndexedOwnedContextualCellOrigins.post_at_same_state
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        profile reached post formed.heaps represented⟩,
    determined⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalFormationReceipts
