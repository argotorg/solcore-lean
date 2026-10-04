import Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingReadMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Frontend.SourceCoreCallableIndexedLedger

/-! Actual accepted mapping-read consumers. Static declaration and source
annotation facts remain independent of the native projection and execution. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
namespace Tests.SourceCoreRecursiveStageMappingReadMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload
open CompatibleMapping.VirtualRoot

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
  {declared : TypedBinder} {key value : TypeSystem.Ty}
  (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id) = .ok lowered.expression)
  (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
  (unique : NodeOccurrencesUnique source)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (typed : ExpressionHasType source context id node.type)
  (form : node.form = .reference name (.local binder))
  (declaration : SourceCoreDataPlaces.rootBinder source binder = .ok declared)
  (declaredType : declared.scheme.body = .mapping key value)
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {faults : FunctionCalls.FaultRep}

include accepted read unique declarations typed form declaration declaredType sameSource extension in
/-- The actual successful compiler and independently typed source declaration
close the reflection certificate. Only the original completed native run is
left as an execution premise. -/
theorem actual_reflects :
    RecursiveStagePrimitiveMeaning.Reflects functions (registry := registry) program stages invocation context
      (fun current occurrence code => current = scope ∧ occurrence = id ∧ code = lowered) faults := by
  intro current occurrence code receipt
  obtain ⟨rfl, rfl, rfl⟩ := receipt
  exact RecursiveStageMappingReadMeaning.reflects functions program stages invocation sameSource extension
    (RecursiveStageMappingReadMeaning.of_accepted accepted read unique declarations typed form declaration declaredType)

include accepted read unique declarations typed form declaration declaredType sameSource extension in
/-- Successful source evaluation and semantic failure use the same actual read
receipt. The complete source and native stores are related after initialization. -/
theorem actual_preserves
    (uninitialized : ∀ expression location, faults (.uninitializedLocation location) (reasonAt expression))
    {root : ExpressionNode} (found : invocation.source.lookupExpression? id = some root)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.Outcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Staging.Recursive.Expression program stages invocation context environment before id outcome after) :
    ∃ native finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) native finalStore ∧
      RecursiveStagePrimitiveMeaning.Result functions (registry := registry) finalMap finalWorld root.type lowered.type faults outcome native ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact RecursiveStageMappingReadMeaning.preserves functions program stages invocation sameSource extension unique uninitialized
    (RecursiveStageMappingReadMeaning.of_accepted accepted read unique declarations typed form declaration declaredType)
    found environments heaps locals agrees trace

/-- Inversion records the original initialization write, including its target,
result and complete final store. No constructed native execution is used. -/
theorem original_empty_write {environment : Core.Environment} {before after : Core.Store}
    {index target : Nat} {type : Core.Ty} {empty result : Core.Value} {literal : Core.Expr}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : before.read? target = some (.inLeft type .unit)) (quoted : Quoted empty literal)
    (evaluated : Evaluates environment before
      (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal) result after) :
    result = .inRight .word empty ∧ before.write? target (.inRight .unit empty) = some after := by
  rcases RecursiveStageMappingReadMeaning.read_completed lookup read quoted evaluated with
    ⟨_, _, impossible, _⟩ | ⟨_, _, sameOptional, resultEq, written⟩
  · cases impossible
  · cases sameOptional
    exact ⟨resultEq, written⟩

/-- A later read of an initialized mapping keeps the entire native store. -/
theorem original_present {environment : Core.Environment} {before after : Core.Store}
    {index target : Nat} {type : Core.Ty} {empty present result : Core.Value} {literal : Core.Expr}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : before.read? target = some (.inRight .unit present)) (quoted : Quoted empty literal)
    (evaluated : Evaluates environment before
      (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal) result after) :
    result = .inRight .word present ∧ after = before := by
  rcases RecursiveStageMappingReadMeaning.read_completed lookup read quoted evaluated with
    ⟨_, _, sameOptional, resultEq, storeEq⟩ | ⟨_, _, impossible, _⟩
  · cases sameOptional
    exact ⟨resultEq, storeEq⟩
  · cases impossible

/-- Initialization preserves every other native cell, including unused
administrative cells outside the source location map. -/
theorem original_empty_preserves_other {environment : Core.Environment} {before after : Core.Store}
    {index target other : Nat} {type : Core.Ty} {empty result : Core.Value} {literal : Core.Expr}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : before.read? target = some (.inLeft type .unit)) (quoted : Quoted empty literal)
    (evaluated : Evaluates environment before
      (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal) result after)
    (different : other ≠ target) : after.read? other = before.read? other :=
  Store.write?_preserves_other (original_empty_write lookup read quoted evaluated).2 different

end Tests.SourceCoreRecursiveStageMappingReadMeaning

namespace Tests.SourceCoreRecursiveStageMappingReadMeaning.NativeReads
open Solcore Solcore.Frontend SourceInference Core

private abbrev get := @SourceCoreUnifiedCorpusSupport.get
private abbrev require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def w (n : Nat) : Core.Value := .word (Word.ofNatModulo n)
private def mapType : TypeSystem.Ty := .mapping .word .word
private def nestedType : TypeSystem.Ty := .mapping .word (.mapping (.proxy .word) .word)
private def empty : SourceTypedRuntime.Value := .mapping .word .word []
private def nestedEmpty : SourceTypedRuntime.Value := .mapping .word (.mapping (.proxy .word) .word) []
private def populated : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) .word [(word 1, word 7), (word 1, word 9)]

private def content := String.intercalate "\n" [
  "function fresh() returns (mapping(Word => Word)) { let table: mapping(Word => Word); return table; }",
  "function repeat() returns ((mapping(Word => Word), mapping(Word => Word))) { let table: mapping(Word => Word); let alias = table; let second = table; return (alias, second); }",
  "function input(table: mapping(Word => Word)) returns (mapping(Word => Word)) { let alias = table; return alias; }",
  "function nested() returns (mapping(Word => mapping(@Word => Word))) { let table: mapping(Word => mapping(@Word => Word)); return table; }",
  "function afterFault() returns (mapping(Word => Word)) { let marker: Word = 7; let table: mapping(Word => Word); let alias = table; let gap: Word; let late: mapping(Word => Word); let stop = gap; return late; }"
]

private def nativeFinish (code : Core.Expr) (environment : Core.Environment)
    (store : Core.Store) (fuel : Nat) : IO (Core.Value × Core.Store) := do
  let first := Core.runStateful fuel (.initial code environment store)
  let final := match first with
    | .outOfFuel checkpoint => Core.runStateful 300000 checkpoint
    | other => other
  match final with
  | .done value after => pure (value, after)
  | other => throw (IO.userError s!"mapping native leaf did not finish: {reprStr other}")

private def wholeFinish (compiled : SourceCoreUnifiedCompilation.Compiled)
    (name : String) (arguments : List SourceTypedRuntime.Value) (fuel : Nat)
    (initial : SourceTypedRuntime.RuntimeState) :
    IO (SourceTypedRuntime.RunResult × String) := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  let final ← get "mapping actual native resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution
    | none => throw (IO.userError "mapping native execution receipt missing")
  let store := SourceCoreCallableIndexedLedger.store execution.completion
  require (!store.isEmpty) "mapping native store missing"
  if name == "afterFault" then
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
    let selected ← get "mapping native fault source" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
    let missing ← match selected.function.typedBody.nodes.filterMap (fun item => match item with
        | .expression node => match node.form with
          | .reference "gap" (.local binder) => some (node, binder)
          | _ => none
        | _ => none) with
      | [missing] => pure missing
      | _ => throw (IO.userError "mapping original fault occurrence changed")
    match execution.completion.result.native.observation with
    | .failed reason _ =>
      let diagnostic ← match execution.completion.result.diagnostics.diagnostic? reason with
        | some diagnostic => pure diagnostic
        | none => throw (IO.userError "mapping native fault has no diagnostic")
      require (diagnostic.error == .uninitializedLocal missing.2 &&
        diagnostic.site == .occurrence missing.1.id.occurrence && diagnostic.span == some missing.1.span)
        "mapping native reason/original occurrence/span changed"
    | _ => throw (IO.userError "mapping native first fault was not returned")
  pure (final.observation, reprStr (execution.completion.result.native.observation, store))

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    "mapping source prefix changed"
  require (reprStr ((final.heap.drop initial.heap.length).map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"mapping full ordered source heap changed: {reprStr final.heap}"

private def whole (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let initial : SourceTypedRuntime.RuntimeState := {
    heap := [⟨.comptime .word, none⟩, ⟨.word, some (word 983)⟩] }
  let tests : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value ×
      List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("fresh", [], empty, [(mapType, some empty)]),
    ("repeat", [], .product empty empty, List.replicate 3 (mapType, some empty)),
    ("input", [populated], populated, List.replicate 2 (mapType, some populated)),
    ("nested", [], nestedEmpty, [(nestedType, some nestedEmpty)])]
  let success ← tests.mapM fun (name, args, _, _) => wholeFinish compiled name args 300000 initial
  let failure ← wholeFinish compiled "afterFault" [] 300000 initial
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "afterFault"
  let selected ← get "mapping fault specialization" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  let gap ← match (SourceCoreDataPlaces.declaredBinders selected.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "mapping actual missing binder changed")
  for fuel in [0, 1, 17, 300000] do
    for ((name, args, expected, expectedCells), baseline) in tests.zip success do
      let actual ← wholeFinish compiled name args fuel initial
      require (reprStr actual == reprStr baseline) "mapping whole native store/source heap/resume changed"
      match actual.1 with
      | .done value final =>
        require (reprStr value == reprStr expected) s!"mapping whole result changed: {name}: {reprStr value}"
        cells initial final expectedCells
        require (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          "mapping whole heap is not deeply safe"
      | other => throw (IO.userError s!"mapping unexpected success result {name}: {reprStr other}")
    let actual ← wholeFinish compiled "afterFault" [] fuel initial
    require (reprStr actual == reprStr failure) "mapping first fault/full native store/resume changed"
    match actual.1 with
    | .fault (.uninitializedLocal binder) final =>
      require (binder == gap) "mapping actual first-fault binder changed"
      cells initial final [(.word, some (word 7)), (mapType, some empty), (mapType, some empty),
        (.word, none), (mapType, none)]
    | other => throw (IO.userError s!"mapping first fault changed: {reprStr other}")

private def leaves (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
  let mut count := 0
  for name in ["fresh", "repeat", "input", "nested", "afterFault"] do
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
    let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
      | [named] => pure named
      | _ => throw (IO.userError "mapping root cache row changed")
    let selected ← get "mapping exact full specialization" (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan key)
    require (selected == named.specialized) "mapping full specialization/ledger changed"
    let source := selected.function.typedBody
    let ledger := selected.function.solvedRequirements
    for item in source.nodes do
      match item with
      | .expression node =>
        match node.form with
        | .reference _ (.local binder) =>
          let declared ← get "mapping actual binder" (SourceCoreDataPlaces.rootBinder source binder)
          match declared.scheme.body with
          | .mapping keyType valueType =>
            require (declared.scheme.quantified.isEmpty && declared.schemeRequirements.isEmpty &&
              node.requirements.isEmpty && node.coercions.isEmpty) "mapping read is not ordinary"
            let type ← get "mapping native projection" (values.checked.catalog.project declared.scheme.body)
            let scope := [(binder, type)]
            let reason := Word.ofNatModulo (4000 + node.id.occurrence.index)
            let code ← get "mapping actual lowerRead" (SourceCoreCompatibleDataExpressions.lowerRead 100 values source scope node.id reason)
            let rawEmpty : SourceCoreCompatibleValues.Value := .mapping keyType valueType []
            let encoded ← get "mapping empty/default carrier" (SourceCoreCompatibleValues.encode 100 values declared.scheme.body rawEmpty)
            require (encoded.context.registry.entries == values.registry.entries) "mapping default changed runtime registry"
            let populatedValue : SourceCoreCompatibleValues.Value := if declared.scheme.body == mapType then
              .mapping (.comptime .word) .word [(.word (Word.ofNatModulo 1), .word (Word.ofNatModulo 7)),
                (.word (Word.ofNatModulo 1), .word (Word.ofNatModulo 9))] else rawEmpty
            let full ← get "mapping initialized payload" (SourceCoreCompatibleValues.encode 100 values declared.scheme.body populatedValue)
            require (full.context.registry.entries.take values.registry.entries.length == values.registry.entries) "mapping initialized value changed registry"
            let captured := Core.Value.closure .unit .word (.var 1) [w 97, w 101]
            let initialCells : Core.Store := [captured, w 103]
            let suffix : Core.Store := [.pair (w 107) captured]
            let environment : Core.Environment := [.cellRef (OptionalCell.cellType type) initialCells.length, captured]
            let absent := initialCells ++ [.inLeft type .unit] ++ suffix
            let initialized := initialCells ++ [.inRight .unit encoded.value] ++ suffix
            let present := initialCells ++ [.inRight .unit full.value] ++ suffix
            let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ =>
              .error (.unsupportedExpression node.id node.form)
            let compilation : SourceCoreFunctions.Context := {
              plan := compiled.indexed.base.plan, owner := key, globals := compiled.indexed.base.globals,
              administrativePrefix := 1, solvedRequirements := ledger, internalReason := Word.zero }
            let lower := fun current => SourceCoreFunctions.lowerExpressionWithPolicy
              (SourceCoreCompatibleDataExpressions.functionPolicy 100 values) noBody 100
              {compilation with solvedRequirements := current} source scope node.id (fun _ => reason)
            let actual ← get "mapping actual whole expression callback" (lower ledger)
            require (actual.expression == code && actual.type == type) "mapping callback/leaf code changed"
            let rows := match ledger with
              | [] => [ledger]
              | first :: _ =>
                let extra := {first with id := ⟨(ledger.map (fun (row : SolvedRequirement) => row.id.index)).foldl max 0 + 1⟩, evidence := .assumption first.predicate}
                [ledger, extra :: ledger, ledger ++ [extra]]
            for complete in rows do
              let same ← get "mapping full unused ledger" (lower complete)
              require (same == actual) "mapping unused ordered rows changed native code"
            for fuel in [0, 1, 17, 300000] do
              let first ← nativeFinish code environment absent fuel
              require (first == (.inRight .word encoded.value, initialized)) "mapping empty first read/full write changed"
              let again ← nativeFinish code environment first.2 fuel
              require (again == first) "mapping second read wrote/allocated a different cell"
              let existing ← nativeFinish code environment present fuel
              require (existing == (.inRight .word full.value, present)) "mapping present read/default metadata/full store changed"
            count := count + 1
          | _ => pure ()
        | .integerLiteral literal resolution =>
          let _ ← get "mapping retained marker Selected" (SourceCoreElaboration.validateWordIntegerLiteral ledger node literal resolution)
          require (node.requirements == [resolution.requirement]) "mapping marker full row changed"
        | _ => pure ()
      | _ => pure ()
  require (count == 10) s!"mapping actual ordinary read count changed: {count}"

/-- New leaf and whole-source IO only; this does not call an older runner. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "staged local mapping reads" content
    ["fresh", "repeat", "input", "nested", "afterFault"]
  require (compiled.keys.length == 5 && compiled.indexed.base.functions.length == 5 &&
    compiled.indexed.secondPass.closures.length == 5) "mapping full actual root inventory changed"
  leaves compiled
  whole compiled
  IO.println "staged mapping reads: actual first write/repeat/alias/input/nested defaults/raw keys/first fault/full ledger/full stores/four resume budgets GREEN"

end Tests.SourceCoreRecursiveStageMappingReadMeaning.NativeReads

namespace Tests.SourceCoreRecursiveStageMappingReadMeaning

/-- Independent new mapping-read cases, registered once by the test runner. -/
def run : IO Unit := NativeReads.run

end Tests.SourceCoreRecursiveStageMappingReadMeaning
