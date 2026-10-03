import Solcore.SourceSemantics.CoreLowering.RecursiveStagePrimitiveMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Test.SourceCoreCompatibleGeneralRuntimeExtraction

/-! Actual literal acceptance builds two ordered occurrences of the same static
leaf, then the closed staged primitive theorem supplies reflection. Real native
subtree audits retain all ledger rows and every native cell. Unsupported unit,
mapping initialization and generalized reads remain explicit boundaries. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 32768
namespace Tests.SourceCoreRecursiveStagePrimitiveMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly CompatibleExpressionPrimitives
open RecursiveStagePrimitiveMeaning

abbrev actual_preserves := @RecursiveStagePrimitiveMeaning.preserves
abbrev actual_ordinary_read := @RecursiveStagePrimitiveMeaning.read_reflects

section Accepted
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel readFuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id pairId : ExpressionId} {node pairNode : ExpressionNode} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  (found : source.lookupExpression? id = some node) (atomic : CompatibleExpressionLiterals.Atomic node.form)
  (stageAtomic : Staging.Recursive.AtomicForm node.form)
  (unitType : node.form = .tuple [] → node.type = .unit)
  (special : ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
  (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
  (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
  (metadata : Metadata values.checked source pairId pairNode (.product lowered.type lowered.type))
  (form : pairNode.form = .tuple [id, id]) (pairType : pairNode.type = .product node.type node.type)

include found atomic stageAtomic unitType special readPolicy leafPolicy accepted metadata form pairType in
theorem accepted_pair :
    ∃ tree : Tree readFuel values source context compilation.solvedRequirements reasonAt scope pairId
      ⟨.product lowered.type lowered.type, LocalSequence.pair lowered.type lowered.type lowered.expression lowered.expression⟩,
      Supported tree := by
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted
  have leaf : LiteralSupported (source := source) (solved := compilation.solvedRequirements) id lowered := by
    obtain ⟨other, otherFound, literal, selected⟩ := receipt
    have same := Option.some.inj (otherFound.symm.trans found)
    subst other
    exact ⟨node, found, literal, selected, stageAtomic⟩
  exact ⟨.pair metadata form found found pairType (.product (.literal receipt.forget)) (.product (.literal receipt.forget)),
    .pair metadata form found found pairType _ _ (.product _ (.literal receipt.forget leaf)) (.product _ (.literal receipt.forget leaf))⟩

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ child location, faults (.uninitializedLocation location) (reasonAt child))

include readFuel sameSource uninitialized sameLedger runtime found atomic stageAtomic unitType special readPolicy leafPolicy accepted metadata form pairType in
theorem actual_pair_reflects :
    ReflectsCode functions program stages invocation (context := context) (registry := registry) (faults := faults) scope pairId
      ⟨.product lowered.type lowered.type, LocalSequence.pair lowered.type lowered.type lowered.expression lowered.expression⟩ := by
  obtain ⟨tree, supported⟩ := accepted_pair (readFuel := readFuel) (context := context) (reasonAt := reasonAt)
    found atomic stageAtomic unitType special readPolicy leafPolicy accepted metadata form pairType
  exact RecursiveStagePrimitiveMeaning.reflects functions program stages invocation sameSource uninitialized sameLedger runtime supported
end Accepted

section Boundaries

theorem unit_not_supported {source : TypedSource} {solved : List SolvedRequirement}
    {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (unit : node.form = .tuple []) :
    ¬ LiteralSupported (source := source) (solved := solved) id code := by
  intro supported
  exact literal_no_unit supported found unit

theorem mapping_read_not_supported {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Word}
    {context : SourceSemantics.Context} {code : SourceCoreBasic.LoweredExpr} {declared : TypedBinder}
    {key value : TypeSystem.Ty}
    (declaration : SourceCoreDataPlaces.rootBinder source declared.id = .ok declared)
    (mapping : declared.scheme.body = .mapping key value)
    (actual : ∀ receipt : CompatibleExpressionReads.Certificate fuel values source scope id reason code.expression,
      receipt.binder = declared.id) :
    ¬ ReadSupported (fuel := fuel) (values := values) (source := source) (context := context)
      (reasonAt := fun _ => reason) (scope := scope) id code := by
  rintro ⟨receipt, _, _, ordinary⟩
  have same : receipt.declared = declared := Except.ok.inj ((actual receipt ▸ receipt.declaration).symm.trans declaration)
  exact ordinary ⟨key, value, same ▸ mapping⟩

theorem generalized_cell_excluded {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : Core.DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {value : Core.Value} {type : Core.Ty}
    (represented : GenericHeap.CellRepresents model mapping world cell value type) : cell.generalized = none :=
  represented.ordinary

theorem staged_result_has_no_rejection {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {faults : FunctionCalls.FaultRep}
    {invocation : Staging.Recursive.Scope} {id : ExpressionId} {reason : Staging.CallGuard.Fault} {value : Value} :
    ¬ Result functions (registry := registry) mapping world sourceType type faults (.fault (.stage invocation id reason)) value := by
  intro impossible
  cases impossible

abbrev full_unused_ledger := @Tests.SourceCoreCompatibleGeneralRuntimeExtraction.accepted_reflects
end Boundaries

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def w (n : Nat) : Core.Value := .word (Word.ofNatModulo n)
private def content := String.intercalate "\n" [
  "function pairRead(a: Word, b: Word) returns ((Word, Word)) { return (a + 3, ~b); }",
  "function shortRead(gate: Bool) returns (Bool) { let absent: Bool; return gate && absent; }",
  "function firstFault() returns (Word) { let first: Word; let second: Word; return first + second; }",
  "function secondFault() returns (Word) { let first: Word = 9; let second: Word; return first + second; }"
]

private def finish (code : Core.Expr) (environment : Core.Environment) (store : Core.Store) (fuel : Nat) : IO (Core.Value × Core.Store) := do
  let first := Core.runStateful fuel (.initial code environment store)
  let result := match first with
    | .outOfFuel checkpoint => Core.runStateful 300000 checkpoint
    | other => other
  match result with
  | .done value after => pure (value, after)
  | other => throw (IO.userError s!"native primitive incomplete: {reprStr other}")

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut roots := 0
  let mut reads := 0
  let mut literals := 0
  for name in ["pairRead", "shortRead", "firstFault", "secondFault"] do
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
    let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
      | [named] => pure named
      | _ => throw (IO.userError "actual primitive root not unique")
    let selected ← get "same full primitive specialization" (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (selected == named.specialized) "primitive full metadata changed"
    let source := selected.function.typedBody
    let binders := (SourceCoreDataPlaces.declaredBinders source).reverse
    let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
    let mut scope : SourceCoreLocalCell.Scope := []
    let mut native : List Core.Value := []
    let mut fields : Core.Store := []
    let captured := Core.Value.closure .unit .word (.var 1) [w 97, w 101]
    let initialCells : Core.Store := [captured, w 103]
    for binder in binders do
      let type ← get "ordinary read actual type" (values.checked.catalog.project binder.scheme.body)
      require (match binder.scheme.body with | .mapping .. => false | _ => true) "mapping branch entered supported audit"
      scope := scope ++ [(binder.id, type)]
      native := native ++ [.cellRef (OptionalCell.cellType type) (initialCells.length + fields.length)]
      let payload : Option Core.Value := if binder.name == "a" then some (w 11) else if binder.name == "b" then some (w 5)
        else if binder.name == "gate" then some (.bool false)
        else if binder.name == "first" && name == "secondFault" then some (w 9) else none
      fields := fields ++ [match payload with | some value => .inRight .unit value | none => .inLeft type .unit]
    native := native ++ [captured]
    let store := initialCells ++ fields
    let reasonAt := fun id : ExpressionId => Word.ofNatModulo (1000 + id.occurrence.index)
    let policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
    let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .error (.unsupportedExpression ⟨⟨source.owner,0⟩⟩ (.tuple []))
    let mut results : List ExpressionId := []
    for item in source.nodes do
      match item with
      | .statement statement => if let .returnStmt (some id) := statement.form then results := results ++ [id]
      | .expression node =>
        match node.form with
        | .reference _ (.local binder) =>
          let _ ← get "actual lowerRead" (SourceCoreCompatibleDataExpressions.lowerRead 100 values source scope node.id (reasonAt node.id))
          let declared ← get "actual rootBinder" (SourceCoreDataPlaces.rootBinder source binder)
          require (declared.scheme.quantified.isEmpty && declared.schemeRequirements.isEmpty) "read generalized metadata changed"
          reads := reads + 1
        | .integerLiteral literal resolution =>
          let _ ← get "selected numeric Word row" (SourceCoreElaboration.validateWordIntegerLiteral selected.function.solvedRequirements node literal resolution)
          require (node.requirements == [resolution.requirement]) "numeric leaf ownership changed"
          literals := literals + 1
        | .unary .. | .binary .. | .tuple .. => require (node.requirements.isEmpty && node.coercions.isEmpty) "primitive parent metadata changed"
        | _ => pure ()
    require (results.length == 1) "primitive return occurrence changed"
    for id in results do
      let ledger := selected.function.solvedRequirements
      let rows := match ledger with
        | [] => [ledger]
        | first :: _ =>
          let extra := {first with id := ⟨(ledger.map (fun (row : SolvedRequirement) => row.id.index)).foldl max 0 + 1⟩, evidence := .assumption first.predicate}
          [ledger, extra :: ledger, ledger ++ [extra]]
      let compilation : SourceCoreFunctions.Context := {
        plan := compiled.indexed.base.plan
        owner := named.signature.key
        globals := compiled.indexed.base.globals
        administrativePrefix := 1
        solvedRequirements := ledger
        internalReason := Word.zero }
      let base ← get "actual primitive root lowering" (SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 100 compilation source scope id reasonAt)
      for complete in rows do
        let lowered ← get "same full ledger primitive root" (SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 100
          {compilation with solvedRequirements := complete} source scope id reasonAt)
        require (lowered == base) "unused ledger changed actual native code"
        let baseline ← finish lowered.expression native store 300000
        for fuel in [0, 1, 17, 300000] do
          let result ← finish lowered.expression native store fuel
          require (result == baseline && result.2 == store) "original whole native store/resume changed"
        match name, baseline.1 with
        | "pairRead", .inRight .word (.pair (.word first) (.word second)) =>
          require (first == Word.ofNatModulo 14 && second == (Word.ofNatModulo 5).bitNot) "ordered pair primitive result changed"
        | "shortRead", .inRight .word (.bool false) =>
          let gateIndex ← match binders.zipIdx.filterMap (fun (binder, index) => if binder.name == "gate" then some index else none) with
            | [index] => pure index
            | _ => throw (IO.userError "actual short circuit binder changed")
          let activeStore := store.set (initialCells.length + gateIndex) (.inRight .unit (.bool true))
          let missing ← match source.nodes.filterMap (fun item =>
            match item with
            | .expression node =>
              match node.form with
              | .reference "absent" (.local _) => some node.id
              | _ => none
            | _ => none) with
            | [child] => pure child
            | _ => throw (IO.userError "actual short circuit missing occurrence changed")
          for fuel in [0, 1, 17, 300000] do
            let active ← finish lowered.expression native activeStore fuel
            require (active == (.inLeft .bool (.word (reasonAt missing)), activeStore))
              "actual right branch fault/store changed"
        | "firstFault", .inLeft .word (.word reason) | "secondFault", .inLeft .word (.word reason) =>
          let expectedName := if name == "firstFault" then "first" else "second"
          let candidates := source.nodes.filterMap fun item =>
            match item with
            | .expression node =>
              match node.form with
              | .reference name (.local _) => if name == expectedName then some node.id else none
              | _ => none
            | _ => none
          let missing ← match candidates with
            | [child] => pure child
            | _ => throw (IO.userError "exact missing read identity changed")
          require (reason == reasonAt missing) "original first/later fault token changed"
        | _, other => throw (IO.userError s!"primitive subtree result changed {reprStr other}")
      roots := roots + 1
  require (roots == 4 && reads == 8 && literals == 2) s!"actual primitive coverage {roots}/{reads}/{literals}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "native staged primitives" content ["pairRead", "shortRead", "firstFault", "secondFault"]
  inspect compiled
  IO.println "staged native primitives: actual supported reads/operators/Selected rows/full unused ledger/ordered pair/short circuit/exact fault/whole native store/resume GREEN"
end Tests.SourceCoreRecursiveStagePrimitiveMeaning
