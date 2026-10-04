import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimePreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeEntry
import Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody

/-! The actual compiler view supplies named/direct receipts at the closure's
same complete dictionary. Source and native bodies consume their original grades.
Catalog authority, captures and history are separate static inputs. This cut
closes named recursion inside lambda bodies; nested lambda formation, indirect
apply, general methods and comptime remain separate grammar boundaries. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaNamedRuntimeBodyMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaNamedRuntimeBodyMeaning

abbrev actual_body := @of_tree
abbrev original_source_child := @CallableIndexedLambdaRuntimePreservation.preserves_named_sized_for
abbrev original_native_child := @CallableIndexedLambdaRuntimeEntry.reflects_original_named_for
abbrev closed_body_preserves := @Body.preserves_sized
abbrev closed_body_reflects := @Body.reflects_sized

section Receipt
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code prepared function scope administrative} {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : Body headers code program registry faults)

include body in
theorem same_actual_finish :
    SourceCoreLoops.lowerStatementsWithPolicy body.policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body ∧
    body.toKernel.emitted = body.emitted := ⟨body.accepted, rfl⟩

include body in
theorem complete_dictionary :
    body.context.solvedRequirements = code.compilation.solvedRequirements ∧
    RuntimeRequirementLedgerValid body.context ∧ function.evidence.Covers body.context ∧
    body.tree.CatalogSites .reachable registry faults ∧ body.actualTree.CatalogSites .reachable registry faults :=
  ⟨body.valid.ledger, body.valid.runtime, body.valid.covers, body.sites, body.actualSites⟩

include body in
theorem ordered_parameter_context :
    MonoBindersExtend function.source.owner function.context function.parameters body.types body.context ∧
    code.receipt.bodyScope = code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope :=
  ⟨body.extended, CallableIndexedLambdaSemanticInvocation.body_scope code⟩
end Receipt

section Ordinary
open CallableAncestryPairedLookup RecursiveNamedCatalog CallableLambdaViewNamedRuntimeCertificates
variable {checked : Checked} {base : Base checked} {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program} {headers : Inventory prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
  (receipt : Ordinary headers compilation source context children scope id output)

include receipt in
theorem actual_emission_kept :
    output.expression = SourceCoreCalls.call receipt.header.named.signature
      (scope.length + compilation.administrativePrefix + receipt.emission.index)
      (SourceCoreCalls.packArguments receipt.codes).expression compilation.internalReason ∧
    compilation.globals[receipt.emission.index]? = some receipt.header.named.signature := by
  obtain ⟨code, _, _, selected⟩ := receipt.emission.equation
  exact ⟨code, selected⟩

end Ordinary

section Boundaries
/-- Runtime ledger validity retains an unused assumption row; it does not
turn the body into the old ordinary literal context. -/
abbrev unused_ledger := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.runtime_not_ordinary

/-- The source child grade has no equality premise with a native body grade. -/
theorem independent_grades (source native budget : Nat) (sourceWithin : source ≤ budget)
    (nativeWithin : native < budget) : source ≤ budget ∧ native < budget := ⟨sourceWithin, nativeWithin⟩

/-- Actual emitted code may be typed with an arbitrary unused suffix. The
canonical dictionary/global prefix and history are not inferred from it. -/
theorem nonempty_globals_unused_suffix (unused : Environment) :
    let captured : Environment := [.cellRef .word 11, .cellRef .bool 12, .cellRef .unit 13] ++ unused
    captured[0]? = some (.cellRef .word 11) ∧ captured[1]? = some (.cellRef .bool 12) ∧
      captured[2]? = some (.cellRef .unit 13) ∧ captured.drop 3 = unused := by simp
end Boundaries

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "trait Mark<T> {}", "trait Stamp<T> {}", "impl Mark<Word> {}", "impl Stamp<Word> {}",
    "function keep(value: Word) returns(Word) { return value + 1; }",
    "function recurse(value: Word) returns(Word) { if(value == 0) { return 0; } return recurse(value - 1) + 1; }",
    "function marked<T>(value: T) returns(T) where T: Mark, T: Stamp, T: Mark { return value; }",
    "function missing(value: Word) returns(Word) { let gap: Word; return gap; }",
    "function named(seed: Word) returns(F) { let unused: Word = 99; return lam(item: Word) -> Word { let prior = seed + item; return keep(prior); }; }",
    "function nested(seed: Word) returns(F) { return lam(item: Word) -> Word { return keep(keep(item + seed)); }; }",
    "function recursive(seed: Word) returns(F) { return lam(item: Word) -> Word { return recurse(item) + seed; }; }",
    "function direct(seed: Word) returns(F) { return lam(item: Word) -> Word { return marked(seed + item); }; }",
    "function firstfault(seed: Word) returns(F) { return lam(item: Word) -> Word { let gap: Word; return keep(gap) + keep(seed); }; }",
    "function laterfault(seed: Word) returns(F) { return lam(item: Word) -> Word { let written = keep(seed); let gap: Word; return keep(gap); }; }",
    "function bodyfault(seed: Word) returns(F) { return lam(item: Word) -> Word { return missing(item); }; }",
    "function zero(seed: Word) returns(function() returns(Word)) { return lam() -> Word { return keep(seed); }; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey :=
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, []⟩
  | none => throw (IO.userError s!"runtime lambda missing fixture {name}")

private def containsLambda : Nat → Core.Expr → Core.Expr → Bool
  | 0, _, _ => false
  | fuel + 1, expected, code =>
    let recurse := containsLambda fuel expected
    match code with
    | .lambda _ _ body => body == expected || recurse body
    | .pair a b | .apply a b | .storeCell a b | .letE a b | .binary _ a b => recurse a || recurse b
    | .first a | .second a | .inLeft _ a | .inRight _ a | .newCell _ a | .loadCell a
    | .construct _ a | .unary _ a => recurse a
    | .caseE a b c | .ifE a b c | .ternary _ a b c => recurse a || recurse b || recurse c
    | .matchData _ _ a branches => recurse a || branches.any recurse
    | _ => false

private def expectedRows (name : String) : List (String × TypeSystem.Ty × Option Core.Value) :=
  let w := fun n => some (Core.Value.word (Word.ofNatModulo n))
  match name with
  | "named" => [("item", .word, w 4), ("prior", .word, w 7), ("value", .word, w 7)]
  | "nested" => [("item", .word, w 4), ("value", .word, w 7), ("value", .word, w 8)]
  | "recursive" => [("item", .word, w 4), ("value", .word, w 4), ("value", .word, w 3), ("value", .word, w 2), ("value", .word, w 1), ("value", .word, w 0)]
  | "direct" => [("item", .word, w 4), ("value", .word, w 7)]
  | "firstfault" => [("item", .word, w 4), ("gap", .word, none)]
  | "laterfault" => [("item", .word, w 4), ("value", .word, w 3), ("written", .word, w 4), ("gap", .word, none)]
  | "bodyfault" => [("item", .word, w 4), ("value", .word, w 4), ("gap", .word, none)]
  | "zero" => [("value", .word, w 3)]
  | _ => []

private def native_bodies : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "runtime lambda checker" (checkProgram workspace)
  let names := ["named", "nested", "recursive", "direct", "firstfault", "laterfault", "bodyfault", "zero"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"runtime lambda worklist {reprStr other}")
  let automatic ← SourceCompilerFeatureSupport.get "runtime lambda base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "runtime lambda indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let word := Word.ofNatModulo
  for (name, selectedKey) in names.zip keys do
    let created ← SourceCompilerFeatureSupport.get "runtime lambda maker" (prepared.runSource selectedKey [.word (word 3)] 500000)
    match created.result.native.observation with
    | .succeeded native original =>
      let inert := Core.Value.closure .unit .unit (.var 0) [.word (word 991), .bool true]
      let before := original ++ [inert]
      let arguments := if name == "zero" then .unit else .word (word (4))
      let state := Core.State.initial CallableIndexedLambdaCalls.applyPayload [native, arguments] before
      let expected := Core.runStateful 500000 state
      let (richer, actualCaptured) ← match native with
        | .pair (.pair manifest (.closure parameter result body captures)) origin =>
          let extended := captures ++ [.bool true, .unit, inert]
          pure (.pair (.pair manifest (.closure parameter result body extended)) origin, extended)
        | _ => throw (IO.userError "named lambda actual captured closure missing")
      let richerState := Core.State.initial CallableIndexedLambdaCalls.applyPayload [richer, arguments] before
      SourceCompilerFeatureSupport.require (Core.runStateful 500000 richerState == expected)
        s!"named lambda nonempty globals and unused native capture suffix {name}"
      SourceCompilerFeatureSupport.require (actualCaptured.drop (actualCaptured.length - 3) == [.bool true, .unit, inert])
        "named lambda full arbitrary capture suffix retained"
      for fuel in [0, 1, 31, 500000] do
        let actual := match Core.runStateful fuel state with
          | .outOfFuel checkpoint => Core.runStateful 500000 checkpoint
          | finished => finished
        SourceCompilerFeatureSupport.require (actual == expected) s!"runtime lambda full resume {name}/{fuel}"
      match expected with
      | .done value after =>
        SourceCompilerFeatureSupport.require (after.take before.length == before) s!"runtime lambda prefix/captures {name}"
        let ledger ← SourceCompilerFeatureSupport.get "runtime lambda ordered allocations" (SourceCoreAllocationLedger.scan prepared.layouts [] after)
        let rows := ledger.rows.filter (fun row => row.markerIndex ≥ before.length)
        let expected := expectedRows name
        SourceCompilerFeatureSupport.require
          (decide (rows.map (fun row => (row.entry.key.binder.name, row.entry.key.binder.scheme.body, row.payload)) = expected))
          s!"runtime lambda full ordered raw bindings {name}"
        let (executable, snapshot) ← match native with
          | .pair (.pair _ (.closure _ _ executable (lexical :: _))) (.word origin) =>
            match SourceCoreCallableIndexedFrames.decode prepared.ancestry.layout.frame lexical with
            | some frame => pure (executable, SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
                (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table origin frame .empty))
            | none => throw (IO.userError "runtime lambda lexical frame decode")
          | _ => throw (IO.userError "runtime lambda actual closure shape")
        let administrativeCount := 0
        SourceCompilerFeatureSupport.require
          (ledger.pending.isNone && after.length == before.length + 3 * rows.length + administrativeCount)
          s!"runtime lambda unaccounted native cells {name}"
        for (row, index) in rows.zipIdx do
          let expectedSnapshot ← if row.entry.key.owner == selectedKey then pure snapshot else do
            let origin ← match prepared.ancestry.graph.inputs.callable.table.idAt? (.named row.entry.key.owner) with
              | some origin => pure origin
              | none => throw (IO.userError "named lambda actual callee descriptor missing")
            pure (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
              (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))
          SourceCompilerFeatureSupport.require
            (row.markerIndex == before.length + 3 * index + 1 && after[row.markerIndex - 1]? == some expectedSnapshot)
            "runtime lambda exact snapshot/marker/payload order"
        for index in List.range administrativeCount do
          let location := before.length + 3 * rows.length + index
          match after[location]? with
          | some (.inRight .unit (.closure .unit resultType body captures)) =>
            SourceCompilerFeatureSupport.require
              (resultType == LocalLoop.resultType .word && containsLambda 2000 body executable &&
               captures.head? == some (.cellRef (OptionalCell.cellType (LocalLoop.functionType .word)) location) &&
               Core.infer? (.unit :: captures.map Core.Value.type) body prepared.layouts.definitions == some resultType)
              "runtime lambda full loop closure code/self/capture types"
          | _ => throw (IO.userError "runtime lambda loop administrative cell")
        if name == "firstfault" || name == "laterfault" || name == "bodyfault" then
          match value with
          | .inLeft .word (.word token) =>
            match created.result.diagnostics.diagnostic? token, rows.getLast? with
            | some diagnostic, some missing =>
              SourceCompilerFeatureSupport.require
                (diagnostic.error == .uninitializedLocal missing.entry.key.binder.id && missing.payload.isNone)
                "runtime lambda exact first missing binder"
            | _, _ => throw (IO.userError "runtime lambda missing fault receipt")
          | _ => throw (IO.userError "runtime lambda expected failure")
        else
          let result := if name == "named" then 8 else if name == "nested" then 9 else if name == "zero" then 4 else 7
          SourceCompilerFeatureSupport.require (value == .inRight .word (.word (word result)))
            s!"runtime lambda result {name}"

      | other => throw (IO.userError s!"runtime lambda incomplete {name}: {reprStr other}")
    | other => throw (IO.userError s!"runtime lambda creation {name}: {reprStr other}")

def run : IO Unit := do
  native_bodies
  IO.println "named lambda bodies: actual ordinary/direct receipts, recursion, ordered argument cells, first/later/body faults, full captures/store and resume GREEN"
end Tests.SourceCoreCallableIndexedLambdaNamedRuntimeBodyMeaning
