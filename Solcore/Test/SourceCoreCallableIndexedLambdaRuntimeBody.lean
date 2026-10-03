import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeBody
import Solcore.Test.SourceCoreCallableIndexedLambdaViewCalls
import Solcore.Test.SourceCoreCallableIndexedLambdaValues

/-! Formal consumers retain actual view acceptance, ordered parameters,
canonical full match trees, runtime ledger and entry context independently.
The runtime fixture audits real captured lambdas; this stage does not provide
a combined named/anonymous recursive meaning theorem. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaRuntimeBody
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaRuntimeBody
open GeneralHeap ReadOnly CompatiblePayload

/-- The factory's existential retains the exact supplied context, fuel,
policy, emitted flow and actual view tree. No whole-body runtime law is input. -/
abbrev actual_body := @CallableIndexedLambdaRuntimeBody.Body.of_tree
abbrev actual_prefix := @CallableIndexedLambdaRuntimeBody.entry_exists
abbrev actual_full_match_transport := @CallableLambdaViewMatchRuntimeCertificates.original

section Body
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code prepared function scope administrative} {program : SourceSemantics.Program}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : Body code program registry faults)

include body in
theorem actual_view_accepted :
    SourceCoreLoops.lowerStatementsWithPolicy body.policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body := body.accepted

include body in
theorem original_code_and_tree :
    code.receipt.body = CompatibleStatements.finish code.receipt.resultCore body.flow
      code.compilation.internalReason code.compilation.internalReason ∧
    body.tree.CatalogSites .reachable registry faults ∧ body.actualTree.CatalogSites .reachable registry faults :=
  ⟨body.emitted, body.sites, body.actualSites⟩

include body in
theorem complete_context :
    body.context.solvedRequirements = code.compilation.solvedRequirements ∧
    RuntimeRequirementLedgerValid body.context ∧ function.evidence.Covers body.context :=
  ⟨body.valid.ledger, body.valid.runtime, body.valid.covers⟩

include body in
theorem ordered_parameters :
    MonoBindersExtend function.source.owner function.context function.parameters body.types body.context ∧
    code.receipt.bodyScope = code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope :=
  ⟨body.extended, body_scope code⟩
end Body

section Boundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def context : SourceSemantics.Context := (Context.ofSignatures signatures).withSolvedRequirements [row]

/-- Runtime validity cannot supply the old ordinary premise for an unused row. -/
theorem runtime_not_ordinary :
    CompatibleRuntimeContextValidity.Valid [row] context [] ∧
      ¬ CompatibleExpressionLiterals.ContextValid [row] context [] := by
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · change ([⟨0⟩] : List RequirementId).Nodup; decide
    · intro item evidence member implementation
      have same : item = row := by simpa [context, Context.withSolvedRequirements] using member
      subst item
      cases implementation
  · constructor
    · intro predicate evidence found; cases found
    · intro predicate member; cases member
  · intro ordinary
    have valid := ordinary.valid.entriesValid row (by simp [context, Context.withSolvedRequirements])
    cases valid with
    | intro retained =>
      cases retained with
      | intro represents valid =>
        cases represents
        cases valid with
        | assumption member => cases member
end Boundary

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "function loops(seed: Word) returns(F) { let unused: Word = 99; return lam(item: Word) -> Word { let sum = seed; for(let i: Word = 0; i < item; i += 1) { if(i == 1) { continue; } sum += i; } while(sum < seed + 10) { sum += 1; if(sum > seed + 5) { break; } } return sum; }; }",
    "function selected(seed: Word) returns(F) { return lam(item: Word) -> Word { match((item, seed)) { case (0, chosen) { return chosen; } case (left, right) { return left + right; } default { return 77; } } }; }",
    "function first(seed: Word) returns(F) { return lam(item: Word) -> Word { match((item, seed)) { case (0, chosen) { return chosen; } case (left, right) { return left + right; } default { return 77; } } }; }",
    "function defaulted(seed: Word) returns(F) { return lam(item: Word) -> Word { match(item) { case 0 { return seed; } default { let extra = seed + item; return extra; } } }; }",
    "function failed(seed: Word) returns(F) { return lam(item: Word) -> Word { match(item) { case 0 { return seed; } default { let prior = seed + item; let missing: Word; return missing; } } }; }",
    "function scrutinee(seed: Word) returns(F) { return lam(item: Word) -> Word { let missing: Word; match(missing) { case 0 { return seed; } default { return item; } } }; }",
    "function zero(seed: Word) returns(function() returns(Word)) { return lam() -> Word { { return seed; } }; }"
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
  | "loops" => [("item", .word, w 4), ("sum", .word, w 9), ("i", .word, w 4)]
  | "first" => [("item", .word, w 0), ("", .product .word .word, some (.pair (.word (Word.ofNatModulo 0)) (.word (Word.ofNatModulo 3)))), ("chosen", .word, w 3)]
  | "selected" => [("item", .word, w 4), ("", .product .word .word, some (.pair (.word (Word.ofNatModulo 4)) (.word (Word.ofNatModulo 3)))), ("left", .word, w 4), ("right", .word, w 3)]
  | "defaulted" => [("item", .word, w 4), ("", .word, w 4), ("extra", .word, w 7)]
  | "failed" => [("item", .word, w 4), ("", .word, w 4), ("prior", .word, w 7), ("missing", .word, none)]
  | "scrutinee" => [("item", .word, w 4), ("missing", .word, none)]
  | _ => []

private def native_bodies : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "runtime lambda checker" (checkProgram workspace)
  let names := ["loops", "first", "selected", "defaulted", "failed", "scrutinee", "zero"]
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
      let arguments := if name == "zero" then .unit else .word (word (if name == "first" then 0 else 4))
      let state := Core.State.initial CallableIndexedLambdaCalls.applyPayload [native, arguments] before
      let expected := Core.runStateful 500000 state
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
        let administrativeCount := if name == "loops" then 2 else 0
        SourceCompilerFeatureSupport.require
          (ledger.pending.isNone && after.length == before.length + 3 * rows.length + administrativeCount)
          s!"runtime lambda unaccounted native cells {name}"
        for (row, index) in rows.zipIdx do
          SourceCompilerFeatureSupport.require
            (row.markerIndex == before.length + 3 * index + 1 && after[row.markerIndex - 1]? == some snapshot)
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
        if name == "failed" || name == "scrutinee" then
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
          let result := if name == "loops" then 9 else if name == "first" || name == "zero" then 3 else 7
          SourceCompilerFeatureSupport.require (value == .inRight .word (.word (word result)))
            s!"runtime lambda result {name}"

      | other => throw (IO.userError s!"runtime lambda incomplete {name}: {reprStr other}")
    | other => throw (IO.userError s!"runtime lambda creation {name}: {reprStr other}")

def run : IO Unit := do
  native_bodies
  IO.println "runtime lambda static bodies: actual view / full imperative tree / captured frame / ordered parameters and match binders / complete ledger / caller restore and full resume GREEN"
end Tests.SourceCoreCallableIndexedLambdaRuntimeBody
