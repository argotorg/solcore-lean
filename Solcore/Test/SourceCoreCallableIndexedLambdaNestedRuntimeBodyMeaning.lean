import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimePreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeEntry
import Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody

/-! Actual public compilation and native observations audit nested formation.
The runtime harness retains full captures and stores. Static Code/History and
catalog authority remain formal receipts, rather than inferred observations. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaNestedRuntimeBodyMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableIndexedHistory CallableIndexedLambdaValues

open SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedLambdaFormationHeads
open CallableIndexedLambdaNestedRuntimeCertificates CallableIndexedLambdaNestedRuntimeBodyMeaning

abbrev actual_body := @CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.of_tree
abbrev original_source_child := @CallableIndexedLambdaRuntimePreservation.preserves_nested_sized_for
abbrev original_native_child := @CallableIndexedLambdaRuntimeEntry.reflects_original_nested_for

variable {values : SourceCoreCompatibleValues.Context} {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
  {locations : Locations (prepared := indexed.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)}
  {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {rank : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

section Execution
variable {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code indexed function outerScope administrative)
  (body : Body headers caller registry faults rank code)
  (profile : values.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (globals : caller.globals = indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (family : CallableIndexedLambdaNamedRuntimeBodyMeaning.CatalogFamily headers locations 0
    (model headers locations registry faults profile) registry faults)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
local notation "F" => model headers locations registry faults profile
local notation "P" => CallableIndexedLambdaNestedFormationEntries.protectedEntry caller headers locations 0 1
include body complete globals slots extension family uninitialized missing escaped owners in
theorem closed_body_preserves (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      environment canonical indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry F mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before body.body.context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)
    (reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope).length +
      1 + indexed.base.globals.length]? = some (.cellRef indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (encode indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : P
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      mapping world before store canonical)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.body.context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.receipt.body.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry F)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry F finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      P
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
        finalMap finalWorld after finalStore canonical :=
  CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.preserves_sized code body profile complete globals slots extension family owners uninitialized missing escaped budget size within environments heaps locals agrees typed reference read unmapped installed trace

include body complete globals slots extension family uninitialized missing escaped in
theorem closed_body_reflects (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      environment canonical indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry F mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before body.body.context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)
    (reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope).length +
      1 + indexed.base.globals.length]? = some (.cellRef indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (encode indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : P
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.receipt.body.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.body.context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry F)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry F finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      P
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
        finalMap finalWorld after finalStore canonical :=
  CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.reflects_sized code body profile complete globals slots extension family uninitialized missing escaped budget size within environments heaps locals agrees typed reference read unmapped installed evaluated

end Execution

section Receipts
variable {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code indexed function outerScope administrative}
  (body : Body headers caller registry faults rank code)

include body in
theorem same_actual_finish :
    SourceCoreLoops.lowerStatementsWithPolicy body.body.policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body ∧ body.toKernel.emitted = body.body.emitted := ⟨body.body.accepted, rfl⟩

include body in
theorem complete_dictionary :
    body.body.context.solvedRequirements = code.compilation.solvedRequirements ∧
    RuntimeRequirementLedgerValid body.body.context ∧ function.evidence.Covers body.body.context ∧
    body.body.tree.CatalogSites .reachable registry faults ∧ body.body.actualTree.CatalogSites .reachable registry faults :=
  ⟨body.body.valid.ledger, body.body.valid.runtime, body.body.valid.covers, body.body.sites, body.body.actualSites⟩

include body in
theorem actual_source_compilation :
    function.source = CallableIndexedNamedGeneration.source caller.named ∧
    code.compilation = CallableIndexedNamedGeneration.context indexed caller.named ∧ code.active = [] :=
  ⟨body.source, body.compilation, body.active⟩
end Receipts

section Captures
variable {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures indexed mapping world outerScope function.captured actual)
  (code : Code indexed function outerScope captured.administrative) (history : History code)
  (supportedBody : Support headers registry faults code)
  (supported : Condition (registry := registry) (faults := faults) headers locations captured code history supportedBody)

include supported in
theorem actual_capture_globals :
    history.metadata = CallableIndexedNamedGeneration.state supportedBody.1.named ∧
    ∃ location, CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 outerScope captured.canonical location :=
  supported
end Captures

section Boundaries
variable {support : RankedSupport (indexed := indexed)} {children : GenericExpressionMeaning.Certificate}
  {compilation : SourceCoreFunctions.Context}

theorem literal_rank_zero
    (head : Lambda support 0 caller source context evidence scope id lowered) : False :=
  Nat.not_lt_zero _ head.smaller

/-- Named recursion has no static rank decrease requirement. -/
theorem named_at_rank_zero
    (head : CallableLambdaViewNamedRuntimeCertificates.Head (ambient := CallableIndexedAmbient.ambientDefinitions indexed)
      headers compilation source context evidence children scope id lowered) :
    Head support 0 caller headers compilation source context evidence children scope id lowered := .existing head

/-- A native cell tag does not identify its physical location. -/
theorem same_type_different_reference (type : Core.Ty) :
    (Value.cellRef type 0).type = (Value.cellRef type 1).type ∧ Value.cellRef type 0 ≠ Value.cellRef type 1 := by
  constructor
  · rfl
  · intro equal
    cases equal

/-- Full source metadata does not replace the actual lambda ghost by a named one. -/
theorem lambda_history_is_not_named
    {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code indexed function outerScope administrative} {history : History code}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    (entry : CallableIndexedLambdaCatalogEntries.SourceEntry code history headers locations 0 1 scope mapping world heap store canonical)
    (metadata : history.metadata = CallableIndexedNamedGeneration.state caller.named) (origin : Word) :
    history.metadata = CallableIndexedNamedGeneration.state caller.named ∧ entry.catalog.authority.ghost ≠ .named origin := by
  refine ⟨metadata, ?_⟩
  rw [entry.ghost]
  intro same
  cases same

/-- The actual source entry and its physical frame are supplied independently. -/
abbrev reached_entry := @CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.entry_of_source
end Boundaries

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "type Maker = function(Word) returns(F);",
    "trait Mark<T> {}", "trait Stamp<T> {}", "impl Mark<Word> {}", "impl Stamp<Word> {}",
    "function keep(value: Word) returns(Word) { return value + 1; }",
    "function recurse(value: Word) returns(Word) { if(value == 0) { return 0; } return recurse(value - 1) + 1; }",
    "function marked<T>(value: T) returns(T) where T: Mark, T: Stamp, T: Mark { return value; }",
    "function nested(seed: Word) returns(Maker) { return lam(item: Word) -> F { let prior = keep(seed + item); return lam(last: Word) -> Word { return keep(prior + last); }; }; }",
    "function direct(seed: Word) returns(Maker) { return lam(item: Word) -> F { let prior = marked(seed + item); return lam(last: Word) -> Word { return marked(prior + last); }; }; }",
    "function recursive(seed: Word) returns(Maker) { return lam(item: Word) -> F { let prior = recurse(item) + seed; return lam(last: Word) -> Word { return keep(prior + last); }; }; }",
    "function emptyouter(seed: Word) returns(function() returns(F)) { return lam() -> F { return lam(last: Word) -> Word { return keep(seed + last); }; }; }",
    "function emptyinner(seed: Word) returns(function(Word) returns(function() returns(Word))) { return lam(item: Word) -> function() returns(Word) { return lam() -> Word { return keep(seed + item); }; }; }",
    "function firstfault(seed: Word) returns(Maker) { return lam(item: Word) -> F { let gap: Word; let prior = keep(gap); return lam(last: Word) -> Word { return keep(prior + last); }; }; }",
    "function laterfault(seed: Word) returns(Maker) { return lam(item: Word) -> F { let written = keep(seed); let gap: Word; let prior = keep(gap); return lam(last: Word) -> Word { return keep(prior + last); }; }; }",
    "function parallel(seed: Word) returns(Maker) { return lam(item: Word) -> F { let first = lam(last: Word) -> Word { return keep(seed + last); }; return lam(last: Word) -> Word { return keep(item + last); }; }; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey :=
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, []⟩
  | none => throw (IO.userError s!"nested lambda missing fixture {name}")

private def containsLambda : Nat → Core.Expr → Core.Expr → Bool
  | 0, _, _ => false
  | fuel + 1, expected, code =>
    let recurse := containsLambda fuel expected
    match code with
    | .lambda _ _ body => body == expected || recurse body
    | .pair a b | .apply a b | .storeCell a b | .letE a b | .binary _ a b => recurse a || recurse b
    | .first a | .second a | .inLeft _ a | .inRight _ a | .newCell _ a | .loadCell a | .construct _ a | .unary _ a => recurse a
    | .caseE a b c | .ifE a b c | .ternary _ a b c => recurse a || recurse b || recurse c
    | .matchData _ _ a branches => recurse a || branches.any recurse
    | _ => false

private def closureSuffix (native : Core.Value) (inert : Core.Value) : IO (Core.Value × Core.Expr) := do
  match native with
  | .pair (.pair manifest (.closure parameter result body captures)) origin =>
    pure (.pair (.pair manifest (.closure parameter result body (captures ++ [.bool true, .unit, inert]))) origin, body)
  | _ => throw (IO.userError "nested lambda actual closure carrier")

/-- The only admitted difference is this exact appended unused capture tail.
Every code, annotation, origin, used capture, cell and store position is compared. -/
private def suffixValue : Nat → Core.Value → Core.Value → Core.Value → Bool
  | 0, expected, actual, _ => expected == actual
  | fuel + 1, expected, actual, inert =>
    let recur := fun expected actual => suffixValue fuel expected actual inert
    match expected, actual with
    | .pair a b, .pair c d => recur a c && recur b d
    | .inLeft t a, .inLeft u b | .inRight t a, .inRight u b => t == u && recur a b
    | .closure p r body captures, .closure ap ar abody acaptures =>
      p == ap && r == ar && body == abody && acaptures.length ≥ captures.length &&
      (captures.zip (acaptures.take captures.length)).all (fun (a,b) => recur a b) &&
      (acaptures.drop captures.length == [] || acaptures.drop captures.length == [.bool true, .unit, inert])
    | _, _ => expected == actual

private def complete (state : Core.State) : IO Core.StatefulRunResult := do
  let expected := Core.runStateful 500000 state
  for fuel in [0, 1, 31, 500000] do
    let actual := match Core.runStateful fuel state with
      | .outOfFuel checkpoint => Core.runStateful 500000 checkpoint
      | done => done
    SourceCompilerFeatureSupport.require (actual == expected) s!"nested lambda full resume {fuel}"
  pure expected

private def expectedNames (name : String) : List String :=
  match name with
  | "nested" | "direct" => ["item", "value", "prior", "last", "value"]
  | "recursive" => ["item", "value", "value", "value", "value", "value", "prior", "last", "value"]
  | "emptyouter" => ["last", "value"]
  | "emptyinner" => ["item", "value"]
  | "firstfault" => ["item", "gap"]
  | "laterfault" => ["item", "value", "written", "gap"]
  | "parallel" => ["item", "first", "last", "value"]
  | _ => []

private def native_bodies : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "nested lambda checker" (checkProgram workspace)
  let names := ["nested", "direct", "recursive", "emptyouter", "emptyinner", "firstfault", "laterfault", "parallel"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"nested lambda worklist {reprStr other}")
  let automatic ← SourceCompilerFeatureSupport.get "nested lambda base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "nested lambda indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let word := Word.ofNatModulo
  for (name, selectedKey) in names.zip keys do
    let created ← SourceCompilerFeatureSupport.get "nested lambda maker" (prepared.runSource selectedKey [.word (word 3)] 500000)
    match created.result.native.observation with
    | .succeeded native original =>
      let inert := Core.Value.closure .unit .unit (.var 0) [.word (word 991), .bool true]
      let before := original ++ [inert]
      let arguments := if name == "emptyouter" then .unit else .word (word 4)
      let state := Core.State.initial CallableIndexedLambdaCalls.applyPayload [native, arguments] before
      let expected ← complete state
      let (richer, outerBody) ← closureSuffix native inert
      let withSuffix := Core.runStateful 500000 (Core.State.initial CallableIndexedLambdaCalls.applyPayload [richer, arguments] before)
      match expected, withSuffix with
      | .done (.inRight resultType (.pair (.pair manifest (.closure parameter result body captures)) origin)) after,
        .done (.inRight actualType (.pair (.pair actualManifest (.closure actualParameter actualResult actualBody actualCaptures)) actualOrigin)) actualAfter =>
        SourceCompilerFeatureSupport.require
          (actualType == resultType && actualManifest == manifest && actualParameter == parameter && actualResult == result &&
           actualBody == body && actualOrigin == origin && actualAfter.length == after.length &&
           (after.zip actualAfter).all (fun (a,b) => suffixValue 3000 a b inert) &&
           (captures.zip (actualCaptures.take captures.length)).all (fun (a,b) => suffixValue 3000 a b inert) && actualCaptures.drop captures.length == [.bool true, .unit, inert])
          s!"nested lambda full actual returned captures with unused outer suffix {name}: types={actualType == resultType}, manifest={actualManifest == manifest}, code={actualBody == body}, origin={actualOrigin == origin}, storelen={actualAfter.length == after.length}, store={(after.zip actualAfter).all (fun (a,b) => suffixValue 3000 a b inert)}, prefix={actualCaptures.take captures.length == captures}, lengths={captures.length}/{actualCaptures.length}, tail={actualCaptures.drop captures.length == [.bool true, .unit, inert]}"
      | _, _ => SourceCompilerFeatureSupport.require (withSuffix == expected) s!"nested lambda original fault suffix {name}"
      let (result, finalStore) ← match expected with
        | .done (.inRight _ inner) after =>
          let (richerInner, innerBody) ← closureSuffix inner inert
          SourceCompilerFeatureSupport.require (containsLambda 3000 innerBody outerBody) "nested lambda actual emitted child body"
          let last := if name == "emptyinner" then .unit else .word (word 5)
          let second := Core.State.initial CallableIndexedLambdaCalls.applyPayload [inner, last] after
          let finished ← complete second
          SourceCompilerFeatureSupport.require (Core.runStateful 500000 (Core.State.initial CallableIndexedLambdaCalls.applyPayload [richerInner, last] after) == finished)
            s!"nested lambda arbitrary unused inner suffix {name}"
          match finished with
          | .done value store => pure (value, store)
          | other => throw (IO.userError s!"nested lambda inner completion {name}: {reprStr other}")
        | .done value after => pure (value, after)
        | other => throw (IO.userError s!"nested lambda original completion {name}: {reprStr other}")
      SourceCompilerFeatureSupport.require (finalStore.take before.length == before) "nested lambda full original store prefix"
      let ledger ← SourceCompilerFeatureSupport.get "nested lambda full allocations" (SourceCoreAllocationLedger.scan prepared.layouts [] finalStore)
      let rows := ledger.rows.filter (fun row => row.markerIndex ≥ before.length)
      SourceCompilerFeatureSupport.require (rows.map (fun row => row.entry.key.binder.name) == expectedNames name)
        s!"nested lambda exact ordered allocation names {name}: {reprStr (rows.map (fun row => row.entry.key.binder.name))}"
      SourceCompilerFeatureSupport.require (ledger.pending.isNone && finalStore.length == before.length + 3 * rows.length)
        "nested lambda all administrative/source cells accounted"
      for (row, index) in rows.zipIdx do
        SourceCompilerFeatureSupport.require (row.markerIndex == before.length + 3 * index + 1)
          "nested lambda exact snapshot/marker/payload order"
        SourceCompilerFeatureSupport.require (row.payload.isSome || row.entry.key.binder.name == "gap")
          "nested lambda every reached nonfault cell initialized"
      if name == "firstfault" || name == "laterfault" then
        match result, rows.getLast? with
        | .inLeft _ (.word token), some missing =>
          match created.result.diagnostics.diagnostic? token with
          | some diagnostic =>
            SourceCompilerFeatureSupport.require
              (diagnostic.error == .uninitializedLocal missing.entry.key.binder.id && missing.payload.isNone)
              "nested lambda exact first missing ID"
          | none => throw (IO.userError "nested lambda fault token")
        | _, _ => throw (IO.userError "nested lambda expected original fault")
      else
        let n := if name == "nested" then 14 else if name == "direct" then 12 else if name == "recursive" then 13
          else if name == "emptyouter" then 9 else if name == "emptyinner" then 8 else 10
        SourceCompilerFeatureSupport.require (result == .inRight .word (.word (word n))) s!"nested lambda final result {name}"
    | other => throw (IO.userError s!"nested lambda creation {name}: {reprStr other}")

def run : IO Unit := do
  native_bodies
  IO.println "nested lambda bodies: actual nested formation, ordinary/direct/recursive children, empty arities, ordered cells, first/later faults, full captures/store and resume GREEN"
end Tests.SourceCoreCallableIndexedLambdaNestedRuntimeBodyMeaning
