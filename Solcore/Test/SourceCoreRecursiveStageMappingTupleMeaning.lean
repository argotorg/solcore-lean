import Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingTupleMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Frontend.SourceCoreCallableIndexedLedger

/-! Actual ordered tuple lowering composes concrete mapping and primitive
receipts. Full final heap and first-fault observations are checked at real
compiled roots; the new runner does not invoke an older runner. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveStageMappingTupleMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly RecursiveStageMappingTupleMeaning
abbrev FaultRep := RecursiveStageTupleMeaning.FaultRep

section Accepted
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {budget fuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {node : ExpressionNode} {ids : List ExpressionId} {reasonAt : ExpressionId → Word}
  {code : SourceCoreBasic.LoweredExpr}
  (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
  (form : node.form = .tuple ids) (typed : ExpressionHasType source context id node.type)
  (special : ∀ child remaining, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child remaining source scope id reasonAt) = .ok none)
  (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
  (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (budget + 1) compilation source scope id reasonAt = .ok code)
  (extract : ∀ child, child ∈ ids → ∀ childNode lowered, source.lookupExpression? child = some childNode →
    ExpressionHasType source context child childNode.type →
    SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope child reasonAt = .ok lowered →
    Certificate fuel values source context compilation.solvedRequirements reasonAt scope child lowered)

include unique found form typed special readPolicy leafPolicy accepted extract in
theorem accepted_root : Certificate fuel values source context compilation.solvedRequirements reasonAt scope id code :=
  of_functions unique found form typed special readPolicy leafPolicy accepted extract

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ child location, faults (.uninitializedLocation location) (reasonAt child))

include unique found form typed special readPolicy leafPolicy accepted extract sameSource sameLedger extension runtime uninitialized in
theorem accepted_reflects
    {mapping : LocationMap} {world : StoreTyping} {admin : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      admin scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expression program stages invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type code.type (FaultRep faults) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects functions program stages invocation sameSource sameLedger extension runtime uninitialized
    (accepted_root unique found form typed special readPolicy leafPolicy accepted extract)
    (sameSource ▸ found) environments heaps locals agrees evaluated

include unique found form typed special readPolicy leafPolicy accepted extract sameSource sameLedger extension runtime uninitialized in
theorem accepted_preserves
    {mapping : LocationMap} {world : StoreTyping} {admin : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.Outcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      admin scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Staging.Recursive.Expression program stages invocation context environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type code.type (FaultRep faults) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves functions program stages invocation sameSource sameLedger extension runtime uninitialized unique
    (accepted_root unique found form typed special readPolicy leafPolicy accepted extract)
    (sameSource ▸ found) environments heaps locals agrees trace
end Accepted

/-- Repeated mapping occurrences retain the same actual read receipt three
 times. The second and third reads observe the first read's initialized cell. -/
theorem repeated_mapping {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id child : ExpressionId} {node childNode : ExpressionNode}
    {code : SourceCoreBasic.LoweredExpr}
    (header : CompatibleExpressionTuples.Header values source id node [child, child, child]
      [childNode.type, childNode.type, childNode.type] [code, code, code])
    (found : source.lookupExpression? child = some childNode)
    (selected : RecursiveStageMappingReadMeaning.Supported (fuel := fuel) (values := values) (source := source)
      (context := context) (reasonAt := reasonAt) scope child code) :
    Certificate fuel values source context solved reasonAt scope id (SourceCoreCalls.packArguments [code, code, code]) := by
  let entries := [(child, code)]
  have sequence : DataExpressionSequence.Tree source (RecursiveStageTupleMeaning.Entries scope entries) scope
      [child, child, child] [childNode.type, childNode.type, childNode.type] [code, code, code] :=
    .cons found ⟨rfl, by simp [entries]⟩ (.cons found ⟨rfl, by simp [entries]⟩ (.single found ⟨rfl, by simp [entries]⟩))
  have children : ∀ current lowered, (current, lowered) ∈ entries →
      Certificate fuel values source context solved reasonAt scope current lowered := by
    intro current lowered member
    have same : current = child ∧ lowered = code := by simpa [entries, Prod.mk.injEq] using member
    rcases same with ⟨rfl, rfl⟩
    exact RecursiveStageMappingTupleMeaning.mapping selected
  exact .tuple header sequence children

/-- Concrete tuple composition never represents a rejected nested stage as
successful native completion. -/
theorem no_stage_result {faults : FunctionCalls.FaultRep} {scope : Staging.Recursive.Scope}
    {id : ExpressionId} {reason : Staging.CallGuard.Fault} {token : Word} :
    ¬ FaultRep faults (.stage scope id reason) token := by intro impossible; exact impossible

private abbrev get := @SourceCoreUnifiedCorpusSupport.get
private abbrev require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def mapType : TypeSystem.Ty := .mapping .word .word
private def empty : SourceTypedRuntime.Value := .mapping .word .word []
private def populated : SourceTypedRuntime.Value := .mapping (.comptime .word) .word [(word 1, word 7), (word 1, word 9)]
private def content := String.intercalate "\n" [
  "function triple() returns ((mapping(Word => Word), Word, mapping(Word => Word))) { let table: mapping(Word => Word); return (table, 7, table); }",
  "function nested() returns (((mapping(Word => Word), mapping(Word => Word)), mapping(Word => Word))) { let a: mapping(Word => Word); let b: mapping(Word => Word); return ((a, b), a); }",
  "function input(table: mapping(Word => Word)) returns ((mapping(Word => Word), mapping(Word => Word), mapping(Word => Word))) { return (table, table, table); }",
  "function firstFault() returns ((Word, mapping(Word => Word))) { let gap: Word; let late: mapping(Word => Word); return (gap, late); }",
  "function laterFault() returns ((mapping(Word => Word), Word, mapping(Word => Word))) { let table: mapping(Word => Word); let gap: Word; let late: mapping(Word => Word); return (table, gap, late); }"
]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO (SourceTypedRuntime.RunResult × String) := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  let final ← get "mapping tuple actual resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution
    | none => throw (IO.userError "mapping tuple native receipt absent")
  let store := SourceCoreCallableIndexedLedger.store execution.completion
  require (!store.isEmpty) "mapping tuple native store absent"
  if name == "firstFault" || name == "laterFault" then
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
    let selected ← get "mapping tuple exact specialization" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
    let missing ← match selected.function.typedBody.nodes.filterMap (fun item => match item with
      | .expression node => match node.form with | .reference "gap" (.local binder) => some (node, binder) | _ => none
      | _ => none) with
      | [missing] => pure missing
      | _ => throw (IO.userError "mapping tuple original gap occurrence absent")
    match execution.completion.result.native.observation with
    | .failed reason _ =>
      let diagnostic ← match execution.completion.result.diagnostics.diagnostic? reason with
        | some diagnostic => pure diagnostic
        | none => throw (IO.userError "mapping tuple native diagnostic absent")
      require (diagnostic.error == .uninitializedLocal missing.2 &&
        diagnostic.site == .occurrence missing.1.id.occurrence && diagnostic.span == some missing.1.span)
        "mapping tuple original first fault occurrence/span changed"
    | _ => throw (IO.userError "mapping tuple native fault missing")
    match final.observation with
    | .fault (.uninitializedLocal binder) _ =>
      require (binder == missing.2) "mapping tuple decoded original fault binder changed"
    | _ => throw (IO.userError "mapping tuple decoded first fault missing")
  pure (final.observation, reprStr (execution.completion.result.native.observation, store))

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "mapping tuple source prefix changed"
  require (reprStr ((final.heap.drop initial.heap.length).map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"mapping tuple full ordered heap changed: {reprStr final.heap}"

/-- Five actual roots audit nary/nested/repeated reads, raw initialized keys,
first and later faults, full source/native heaps and original checkpoint resume. -/
def run : IO Unit := do
  let names := ["triple", "nested", "input", "firstFault", "laterFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "staged tuples with mapping leaves" content names
  require (compiled.keys.length == 5 && compiled.indexed.base.functions.length == 5 &&
    compiled.indexed.secondPass.closures.length == 5) "mapping tuple full root inventory changed"
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (word 983)⟩]}
  let tests : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value ×
      List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("triple", [], .product empty (.product (word 7) empty), [(mapType, some empty)]),
    ("nested", [], .product (.product empty empty) empty, List.replicate 2 (mapType, some empty)),
    ("input", [populated], .product populated (.product populated populated), [(mapType, some populated)])]
  let successes ← tests.mapM fun (name, args, _, _) => finish compiled name args 300000 initial
  let failures ← ["firstFault", "laterFault"].mapM fun name => finish compiled name [] 300000 initial
  for fuel in [0, 1, 17, 300000] do
    for ((name, args, expected, expectedCells), baseline) in tests.zip successes do
      let actual ← finish compiled name args fuel initial
      require (reprStr actual == reprStr baseline) "mapping tuple full native/source heap or checkpoint changed"
      match actual.1 with
      | .done value final =>
        require (reprStr value == reprStr expected) s!"mapping tuple result changed: {name} {reprStr value}"
        cells initial final expectedCells
        require (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          "mapping tuple source heap not deeply safe"
      | other => throw (IO.userError s!"mapping tuple unexpected success {reprStr other}")
    for (name, baseline) in ["firstFault", "laterFault"].zip failures do
      let actual ← finish compiled name [] fuel initial
      require (reprStr actual == reprStr baseline) "mapping tuple fault full native store/checkpoint changed"
      match actual.1 with
      | .fault (.uninitializedLocal _) final =>
        cells initial final (if name == "firstFault" then [(.word, none), (mapType, none)]
          else [(mapType, some empty), (.word, none), (mapType, none)])
      | other => throw (IO.userError s!"mapping tuple first fault changed {reprStr other}")
  IO.println "staged mapping tuples: actual nary/nested/repeated/raw keys/first-later faults/full heaps/four resume budgets GREEN"

end Tests.SourceCoreRecursiveStageMappingTupleMeaning
