import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedSupport
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Real bootstrap/cached-row consumers discharge the former syntax support
premise. Source syntax, child certificates and diagnostic interpretation remain
explicit; support does not certify source authority or execution. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCachedSupport
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory
open NativeExpressionContextSupport RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

variable (cached : SourceCoreUnifiedCompilation.Compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare cached = .ok recipe)
  (rows : List LambdaRow)
  (cachedRows : cached.indexed.secondPass.closures = rows.map LambdaRow.expression)
  (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
    cached.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
  (member : nativeEntry ∈ cached.indexed.entries)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (definitions : ambient.definitions = cached.indexed.layouts.definitions)
  {headers : Inventory cached.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {header : Header cached.indexed.ancestry values ambient.definitions program}
  (sameCache : header.compiled.closures = cached.indexed.secondPass.closures)
  (complete : Complete headers) (globals : header.globals = cached.indexed.base.globals.length)
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include recipeAccepted cachedRows ordered sameCache in
/-- This is the same selected full cached lambda used by native extraction. -/
theorem actual_support :
    supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code)
      (cached.indexed.base.globals.length + 1) = true :=
  RecursiveNamedCachedSupport.header_supported cached recipeAccepted rows cachedRows ordered sameCache

include member definitions sameCache complete globals recipeAccepted cachedRows ordered entry in
theorem actual_canonical :
    HasType (SourceCoreLocalCell.coreContext (bodyScope header) ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      header.body (LanguageResult.resultType header.output) ambient.definitions :=
  RecursiveNamedCachedSupport.canonical_body cached recipeAccepted rows cachedRows ordered member definitions sameCache complete globals entry

variable {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

include member definitions sameCache complete globals recipeAccepted cachedRows ordered entry in
/-- This consumer feeds the real prepared root's native proof into the single
compiler traversal, without requesting body/loop HasType at actual Γ. -/
theorem actual_extraction (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (closed : header.context.typeVariables = []) (residual : header.context.residualTypeVariables = false)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :=
  RecursiveNamedCachedSupport.extract cached recipeAccepted rows cachedRows ordered member definitions sameCache complete globals entry
    diagnosticPolicy registered prefixEq factory readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy
    syntaxTree closed residual sourceSignatures declarations projection accepted

/-- The selected receipt still owns the diagnostic obligations. -/
theorem actual_profile {diagnosticPolicy : AssignmentDiagnosticPolicy} {faults : FunctionCalls.FaultRep}
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (interpreted : receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults) :=
  ⟨receipt.profile interpreted⟩

/-- Every binding construct lifts the mapping while leaving its own slot fixed. -/
theorem lambda_bound :
    supported ((Expr.lambda .unit .unit (.pair (.var 0) (.var 1))).rename (shift 7)) 8 = true ∧
    supported (.lambda .unit .unit (.pair (.var 0) (.var 1))) 1 = true := by decide

theorem case_bound :
    supported ((Expr.caseE (.var 0) (.pair (.var 0) (.var 1)) (.var 1)).rename (shift 7)) 8 = true ∧
    supported (.caseE (.var 0) (.pair (.var 0) (.var 1)) (.var 1)) 1 = true := by decide

theorem let_bound :
    supported ((Expr.letE (.var 0) (.lambda .unit .unit (.pair (.var 0) (.var 2)))).rename (shift 7)) 8 = true ∧
    supported (.letE (.var 0) (.lambda .unit .unit (.pair (.var 0) (.var 2)))) 1 = true := by decide

theorem match_bound :
    supported ((Expr.matchData ⟨0⟩ .unit (.var 0) [(.var 0), (.pair (.var 0) (.var 1))]).rename (shift 7)) 8 = true ∧
    supported (.matchData ⟨0⟩ .unit (.var 0) [(.var 0), (.pair (.var 0) (.var 1))]) 1 = true := by decide

/-- A collapsing renaming needs the explicit bound-reflection condition. -/
theorem collapsing_renaming :
    supported ((Expr.var 8).rename (fun _ => 0)) 1 = true ∧
    supported (.var 8) 1 = false ∧
    ¬ NativeExpressionRenamingSupport.ReflectsBound (fun _ => 0) 1 1 := by
  refine ⟨rfl, rfl, ?_⟩
  intro bound
  have := bound 8 (by decide)
  omega

/-- Syntactic support does not assert well-formed type annotations. -/
theorem support_is_not_annotation_typing :
    supported (.lambda (.namedData ⟨0⟩) (.namedData ⟨0⟩) (.var 0)) 0 = true ∧
    ¬ (Ty.namedData ⟨0⟩).WellFormed [] := by
  refine ⟨rfl, ?_⟩
  intro typed
  cases typed with
  | namedData found => simp at found

private def content : String := String.intercalate "\n" [
  "function step(n: Word) returns (Word) { return n + 1; }",
  "function self(n: Word) returns (Word) { if (n == 0) { return 0; } return self(n - 1); }",
  "function loop(n: Word) returns (Word) { let total = 0; for (let i = 0; i < n; i += 1) { total += step(i); } return total; }",
  "function down(n: Word) returns (Word) { while (n != 0) { n -= 1; } return n; }",
  "function assign(m: mapping(Bool => Word)) returns (Word) { m[true] = step(6); return m[true]; }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(value: Word) -> Word { seed += value; return seed; }; }",
  "function fail() returns (Word) { let saved = 17; let gap: Word; return gap; }",
  "function zero() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def bootstrap (state : Core.State) : IO (Value × Store) :=
  match runStateful 300000 state with
  | .done value store => pure (value, store)
  | other => throw (IO.userError s!"cached support bootstrap incomplete: {reprStr other}")

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let indexed := compiled.indexed
  let recipe ← get "actual support recipe" (SourceCoreIndexedSession.Recipe.prepare compiled)
  let rows ← indexed.secondPass.closures.mapM fun expression =>
    match expression with
    | .lambda parameter result body => pure (⟨parameter, result, body⟩ : LambdaRow)
    | _ => throw (IO.userError "actual support row not lambda")
  let canonical := initialEnvironment indexed.base.globals indexed.ancestry.layout.frame
  require (canonical.length == indexed.base.globals.length + 1) "support canonical length changed"
  require (rows.length > 1 && rows.length == indexed.base.globals.length) "support full ordered row count changed"
  let expected := RecursiveGlobalInitializationTyping.initialStore indexed.base.globals rows indexed.ancestry.layout.frame
  let (value, store) ← bootstrap (.initial recipe.bootstrap [] [])
  require (reprStr store == reprStr expected) "support complete initialized store changed"
  require (reprStr value == reprStr (Value.inRight .word .unit)) "support bootstrap result changed"
  for (row, slot) in rows.zipIdx do
    let signature ← match indexed.base.globals[slot]? with
      | some signature => pure signature
      | none => throw (IO.userError "support ordered signature missing")
    require (signature.functionType == .function row.parameter row.result) "support complete signature order changed"
    require (supported row.expression canonical.length) "cached lambda exceeds globals/frame support"
    for shiftCount in [0, 1, 7, 19] do
      require (supported (row.expression.rename (shift shiftCount)) (canonical.length + shiftCount))
        "actual cached renamed support lost binder boundary"
    match store.read? (RecursiveNamedCatalogInitialization.location indexed.base.globals slot) with
    | some (.inRight .unit (.closure parameter result body captured)) =>
      require (captured.length == slot + canonical.length) "support actual capture length changed"
      require (reprStr captured == reprStr (List.replicate slot Value.unit ++ canonical))
        "support full actual capture changed"
      require (reprStr body == reprStr (row.body.rename (shift slot).lift)) "support actual stored body changed"
      require (infer? (parameter :: captured.map Value.type) body indexed.layouts.definitions == some result)
        "support actual stored body native typing failed"
      require (supported body (captured.length + 1)) "stored native body support failed"
    | _ => throw (IO.userError "support initialized full closure missing")
  for fuel in [0, 1, 43, 300000] do
    let result ← match runStateful fuel (.initial recipe.bootstrap [] []) with
      | .done value store => pure (value, store)
      | .outOfFuel checkpoint => bootstrap checkpoint
      | other => throw (IO.userError s!"support bootstrap fault: {reprStr other}")
    require (reprStr result == reprStr (value, store)) "support full initialization resume changed"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "cached support public resume" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"support old cells changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"support full ordered cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "actual cached support" content
    ["self", "loop", "down", "assign", "make", "fail", "zero"]
  inspect compiled
  let mapping : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 31), (.bool true, w 91), (.bool false, w 4)]
  let updated : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 7), (.bool true, w 91), (.bool false, w 4)]
  let tests : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("self", [w 2], w 0, [(.word, some (w 2)), (.word, some (w 1)), (.word, some (w 0))]),
    ("loop", [w 2], w 3, [(.word, some (w 2)), (.word, some (w 3)), (.word, some (w 2)), (.word, some (w 0)), (.word, some (w 1))]),
    ("down", [w 2], w 0, [(.word, some (w 0))]),
    ("assign", [mapping], w 7, [(.mapping .bool .word, some updated), (.word, some (w 6))]),
    ("zero", [], .unit, [])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩, ⟨.bool, some (.bool false)⟩]}
  let baselines ← tests.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failed ← finish compiled "fail" [] 300000 initial
  for fuel in [0, 7, 43, 300000] do
    for (test, baseline) in tests.zip baselines do
      let (name, arguments, expected, expectedCells) := test
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"support full public resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"support result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"support expected success {name}")
    let observed ← finish compiled "fail" [] fuel initial
    require (reprStr observed == reprStr failed) "support first fault/resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final => cells initial final [(.word, some (w 17)), (.word, none)] "fail"
    | _ => throw (IO.userError "support first fault lost")
  IO.println "cached support: actual recipe, full ordered caches/captures, binder shifts, recursive/loop/assignment cells, first fault/resume GREEN"

end Tests.SourceCoreRecursiveNamedCachedSupport
