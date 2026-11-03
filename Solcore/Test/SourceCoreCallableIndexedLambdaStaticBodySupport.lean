import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads
import Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody

/-! These consumers retain the actual compiler view, canonical static body,
complete runtime ledger, captures and history under one support family.
Named calls have no static rank decrease. Only literal nested-lambda tokens
use rank, independently of all source and native execution grades. This unit
does not close named lambda-body execution, indirect apply or method bodies.
The runtime runner reuses the registered seven actual lambda cases once. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaStaticBodySupport
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaStaticBodySupport

abbrev actual_body := @BodyWith.of_tree
abbrev actual_entry := @CallableIndexedLambdaEntryPrefix.entry_exists_for_with_spine
abbrev actual_lambda_site := @RecursiveNamedLambdaFormationHeads.LambdaWith.of_site

section Body
variable {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code prepared function scope administrative} {program : SourceSemantics.Program}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : BodyWith expressionSyntax certificates code program registry faults)

include body in
theorem original_view_and_static_body :
    SourceCoreLoops.lowerStatementsWithPolicy body.policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body ∧
    code.receipt.body = CompatibleStatements.finish code.receipt.resultCore body.flow
      code.compilation.internalReason code.compilation.internalReason ∧
    body.tree.CatalogSites .reachable registry faults ∧ body.actualTree.CatalogSites .reachable registry faults :=
  ⟨body.accepted, body.emitted, body.sites, body.actualSites⟩

include body in
theorem full_context_and_origin_shape :
    body.context.solvedRequirements = code.compilation.solvedRequirements ∧
    RuntimeRequirementLedgerValid body.context ∧ function.evidence.Covers body.context ∧
    NodeOccurrencesUnique function.source :=
  ⟨body.valid.ledger, body.valid.runtime, body.valid.covers, body.unique⟩

theorem legacy_body_roundtrip
    (legacy : CallableIndexedLambdaRuntimeBody.Body code program registry faults) :
    CallableIndexedLambdaRuntimeBody.Body.fromWith legacy.toWith = legacy := by
  cases legacy
  rfl
end Body

section Values
open CallableIndexedLambdaRuntimeValues
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {support : SupportFamily prepared} {P : SupportCondition prepared support}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  {environment : Dynamic.Environment} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog values.checked.catalog) projects
    prepared.layouts.definitions}
  {current : Captures prepared mapping world scope environment actual}
  {code : Code prepared function scope current.administrative} {history : History code}
  {heap : Dynamic.Heap} {store : Store} {location : Location}
  (formed : Formed model current code history heap store location)
  (body : support formed.closureCode)
  (supported : P (function := formed.closure) formed.captures formed.closureCode formed.closureHistory body)
  (profile : values.checked.catalog.callableContracts = true)
  (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)

include formed body supported profile stored in
/-- The formed closure over the copies of the creation environment keeps the
support receipt and condition of its code. -/
theorem actual_formation {program : SourceSemantics.Program}
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment heap
      code.id (.closure formed.closure) formed.finalHeap ∧
    Evaluates actual store (code.lowered.expression.rename current.embedding)
      (.inRight .word (value code formed.embedding history.native formed.closureActual)) formed.finalStore ∧
    RepresentsWith prepared support P formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
  formation_with prepared program formed body supported profile stored ordinary coercions

include formed body supported profile stored in
theorem actual_reflection {program : SourceSemantics.Program}
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) {result : Value} {after : Store}
    (completed : Evaluates actual store (code.lowered.expression.rename current.embedding) result after) :
    result = .inRight .word (value code formed.embedding history.native formed.closureActual) ∧
    after = formed.finalStore ∧
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment heap
      code.id (.closure formed.closure) formed.finalHeap ∧
    RepresentsWith prepared support P formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
  reflects_with prepared program formed body supported profile stored ordinary coercions completed

theorem retained_code_history_and_condition
    {sourceType : TypeSystem.Ty} {native : Value} {type : Ty}
    (related : RepresentsWith prepared support P mapping world sourceType (.closure function) native type) :
    ∃ scope actual, ∃ (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code) (body : support code),
      P captured code history body ∧ sourceType = FunctionValues.sourceType function ∧
      native = value code captured.embedding history.native actual ∧
      type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore :=
  RepresentsWith.closure_inv prepared related
end Values

section Capture
open CallableIndexedLambdaRuntimeValues
variable {values : SourceCoreCompatibleValues.Context} (prepared : Prepared values.checked) (program : SourceSemantics.Program)
  (support : SupportFamily prepared)
  (origin : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
    (code : Code prepared function scope administrative) → History code → Prop)
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  (callerPrefix : Nat)

theorem actual_same_capture_condition {mapping futureMapping world futureWorld function scope actual}
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code) (body : support code)
    (supported : captureCondition prepared program support origin (headers := headers) (locations := locations)
      callerPrefix captured code history body)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    captureCondition prepared program support origin (headers := headers) (locations := locations)
      callerPrefix (captured.extend maps worlds) code history body :=
  captureCondition_stable prepared program support origin callerPrefix captured code history body supported maps worlds

abbrev actual_capture := @RecursiveNamedLambdaFormationHeads.capture_globals
abbrev actual_capture_condition := @RecursiveNamedLambdaFormationHeads.LambdaWith.capture_condition
abbrev actual_cached_slots := @RecursiveNamedLambdaFormationHeads.cached_capture_slots
end Capture

section Boundaries
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {support : Nat → {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → Code prepared function scope administrative → Type}
  {calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate}
  {source : TypedSource} {context : SourceSemantics.Context} {children : GenericExpressionMeaning.Certificate}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

theorem named_rank_unrestricted (rank : Nat) (head : calls children scope id lowered) :
    CallsWith prepared support rank calls source context children scope id lowered := .existing head

theorem no_nested_lambda_at_zero
    (head : NestedLambda prepared support 0 source context scope id lowered) : False :=
  Nat.not_lt_zero head.childRank head.smaller

/-- Two real globals, their independent frame and an arbitrary unused native
suffix survive the finite used-prefix retention; the full actual env stays. -/
theorem nonempty_globals_unused_suffix (unused : Environment) :
    let canonical : Environment := [.word (Word.ofNatModulo 7), .cellRef .word 3, .cellRef .bool 4, .cellRef .unit 5] ++ unused
    let finite := canonical.take 4
    finite[0]? = some (.word (Word.ofNatModulo 7)) ∧
      finite[1]? = some (.cellRef .word 3) ∧ finite[2]? = some (.cellRef .bool 4) ∧
      finite[3]? = some (.cellRef .unit 5) ∧ canonical.drop 4 = unused := by simp

end Boundaries

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedLambdaStaticBodySupport
