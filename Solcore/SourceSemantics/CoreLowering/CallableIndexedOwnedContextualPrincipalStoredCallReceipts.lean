import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredMemberCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation

/-! Actual contextual principal formation supplies the positive member used by
the shared stored-call adapters. Method authority, Source origin, leading
bundle and same-body PrincipalAt remain genuine retained fields. The original
Selection supplies its exact escaped-control row; live reads stay explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualPrincipalStoredCallReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualStoredClosureAssociationReceipts (Member)
open CallableIndexedOwnedContextualLambdaProvenance (PrincipalAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
  (owner : OwnedKey keys)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {parentScope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {certificate : GenericExpressionMeaning.Certificate}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source parentScope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (selected : CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
    (certificate := certificate) compiler prepared code)

section ExistingMember
variable (history : History code)
  (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
  (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
  (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
  (nativeTyped : RuntimeValueHasType world (value code captured.embedding history.native actual)
    (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (provenance : PrincipalAt code support)

include selected origin globals leading referenceIndex nativeTyped provenance in
/-- The real principal branch retains its complete same-Code provenance and
uses the original selected compiler row, without rank or authority recovery. -/
theorem member_from_selection :
    Member headers keys registry faults mapping world function
      (value code captured.embedding history.native actual) code.receipt.loweredParameters
      code.receipt.parameterCore code.receipt.resultCore :=
  Member.principal owner captured code history support origin globals leading referenceIndex
    nativeTyped provenance selected.escaped

variable {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Nat}
  (reference : ReferenceRepresents mapping world location target
    (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore))
  (sourceRead : Dynamic.Heap.Reads heap location ⟨FunctionValues.sourceType function, some (.closure function), none⟩)
  (nativeRead : store.read? target = some (.inRight .unit (value code captured.embedding history.native actual)))

include selected origin globals leading referenceIndex nativeTyped provenance reference sourceRead nativeRead in
/-- Only actual initialized Source/native cell reads are attached. This
positive receipt feeds both shared whole-call directions at their real state. -/
theorem stored_from_selection :
    CallableIndexedOwnedContextualInitializedClosureReceipts.StoredAt headers keys registry faults
      mapping world heap store location function (value code captured.embedding history.native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore :=
  ⟨member_from_selection (captured := captured) (code := code) (support := support) (owner := owner)
    (selected := selected) (history := history) (origin := origin) (globals := globals) (leading := leading)
    (referenceIndex := referenceIndex) (nativeTyped := nativeTyped) (provenance := provenance),
    target, reference, sourceRead, nativeRead⟩

include selected origin globals leading referenceIndex nativeTyped provenance in
/-- The shared positive projection preserves the principal's actual callable
origin at exactly its retained native carrier and original table. -/
theorem stage_origin_from_selection :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) (value code captured.embedding history.native actual) := by
  exact CallableIndexedOwnedContextualStoredMemberCallBounds.member_stage_origin
    (member_from_selection (captured := captured) (code := code) (support := support) (owner := owner)
      (selected := selected) (history := history) (origin := origin) (globals := globals) (leading := leading)
      (referenceIndex := referenceIndex) (nativeTyped := nativeTyped) (provenance := provenance))
end ExistingMember

section Formation
variable {heap : Dynamic.Heap} {store : Store}
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (provenance : PrincipalAt code support)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)

include selected packet profile provenance inclusion in
/-- One original contextual principal formation returns its exact pure Source
trace, native trace, receiving-model value and positive member. The history,
leading bundle and Source origin come from the same actual initial packet. -/
theorem formation_member_from_selection
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)) store ∧
    functions.Represents registry mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual) ∧
      finalStore = store) ∧
    Member headers keys registry faults mapping world function
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  exact CallableIndexedOwnedContextualStoredClosureAssociationReceipts.principal_formation_member
    (captured := captured) (code := code) (support := support) (owner := owner)
    (initial := initial) (packet := packet) (profile := profile) (provenance := provenance)
    (functions := functions) (inclusion := inclusion) (escaped := selected.escaped)
    stored ordinary coercions
end Formation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualPrincipalStoredCallReceipts
