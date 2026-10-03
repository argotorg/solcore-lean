import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntime
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! The semantic family uses the old General Tree plus static receipts for
its literal leaves. The formal consumer obtains a repeated numeric child from
the actual compiler and builds its exact pair tree. Whole-root support
extraction is intentionally not claimed. Runtime fixtures separately exercise
actual control/data compilation, full stores and first-fault resume. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleGeneralRuntime
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly

section Accepted
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel readFuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id pairId : ExpressionId} {node pairNode : ExpressionNode} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  (found : source.lookupExpression? id = some node) (atomic : CompatibleExpressionLiterals.Atomic node.form)
  (unitType : node.form = .tuple [] → node.type = .unit)
  (special : ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
  (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
  (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
  (metadata : CompatibleExpressionPrimitives.Metadata values.checked source pairId pairNode (.product lowered.type lowered.type))
  (form : pairNode.form = .tuple [id, id]) (pairType : pairNode.type = .product node.type node.type)

include found atomic unitType special readPolicy leafPolicy accepted metadata form pairType

/-- Repeated leaves keep both occurrences and the same full selected row.
The parent metadata is explicit static data, not a compiler-root receipt. -/
theorem accepted_pair :
    CompatibleExpressionGeneralRuntime.Certificate readFuel values source context compilation.solvedRequirements reasonAt
      scope pairId ⟨.product lowered.type lowered.type,
        LocalSequence.pair lowered.type lowered.type lowered.expression lowered.expression⟩ := by
  have leaf := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted
  let tree : CompatibleExpressionProducts.Tree readFuel values source context compilation.solvedRequirements reasonAt scope pairId
      ⟨.product lowered.type lowered.type, LocalSequence.pair lowered.type lowered.type lowered.expression lowered.expression⟩ :=
    .pair metadata form found found pairType (.literal leaf.forget) (.literal leaf.forget)
  have sites : tree.LiteralSites (fun _ i code => CompatibleExpressionLiteralRuntime.Certificate compilation.solvedRequirements source i code) :=
    .pair metadata form found found pairType _ _ (.literal leaf.forget leaf) (.literal leaf.forget leaf)
  exact ⟨.fragment (.fragment (.fragment (.fragment (.primitive (.product tree))))),
    .fragment _ (.fragment _ (.fragment _ (.fragment _ (.primitive _ (.product _ sites)))))⟩

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ child location, faults (.uninitializedLocation location) (reasonAt child))
  (missing : ∀ child key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt child).add tag))

include extension faithful functionLeaves functionTypes sameLedger runtime uninitialized missing

theorem accepted_pair_preserves (unique : NodeOccurrencesUnique source) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (fun s i code => s = scope ∧ i = pairId ∧ code =
        ⟨.product lowered.type lowered.type, LocalSequence.pair lowered.type lowered.type lowered.expression lowered.expression⟩) faults := by
  have receipt := accepted_pair (readFuel := 0) (context := context) found atomic unitType special readPolicy leafPolicy accepted metadata form pairType
  intro s i code selected
  obtain ⟨rfl, rfl, rfl⟩ := selected
  exact CompatibleExpressionGeneralRuntime.preserves functions extension faithful functionLeaves functionTypes
    program evidence sameLedger runtime unique uninitialized missing receipt

theorem accepted_pair_reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (fun s i code => s = scope ∧ i = pairId ∧ code =
        ⟨.product lowered.type lowered.type, LocalSequence.pair lowered.type lowered.type lowered.expression lowered.expression⟩) faults := by
  have receipt := accepted_pair (readFuel := 0) (context := context) found atomic unitType special readPolicy leafPolicy accepted metadata form pairType
  intro s i code selected
  obtain ⟨rfl, rfl, rfl⟩ := selected
  exact CompatibleExpressionGeneralRuntime.reflects functions extension faithful functionLeaves functionTypes
    program evidence sameLedger runtime uninitialized missing receipt
end Accepted

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (value : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "function nested() returns (Word) { return (true ? (5 + 7) : (11 / 0)) * 3; }",
  "function shortCircuit() returns (Bool) { let absent: Word; return false && (absent == 17); }",
  "function paired() returns ((Word, Word)) { let prior = 19; return (prior, 23); }",
  "function mappingRoot() returns (Word) { let table: mapping(Word => Word); table[29] = 31; return table[29] + table[37]; }",
  "function leftFault() returns (Word) { let prior = 41; let absent: Word; return absent + (43 / 0); }",
  "function rightFault() returns (Word) { let prior = 47; let absent: Word; return (prior + 53) + absent; }"
]

/-- Inspect real numeric compiler leaves with the complete retained ledger.
Unrelated assumptions are explicit test mutations; no checker-production
claim is made for those altered ledgers. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut numeric := 0
  for named in compiled.indexed.base.functions do
    let actual ← get "general exact specialization" (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (actual == named.specialized) "general selected full record changed"
    let source := actual.function.typedBody
    let ledger := actual.function.solvedRequirements
    for retained in source.nodes do
      match retained with
      | .expression node =>
        match form : node.form with
        | .integerLiteral literal resolution =>
          numeric := numeric + 1
          let fresh : RequirementId := ⟨(ledger.map (·.id.index)).foldl max 0 + 1⟩
          let unrelated : SolvedRequirement := ⟨fresh, resolution.predicate, .assumption resolution.predicate⟩
          for rows in [ledger, unrelated :: ledger, ledger ++ [unrelated]] do
            let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
            let policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
            let compilation : SourceCoreFunctions.Context := {
              plan := compiled.indexed.base.plan, owner := named.signature.key,
              globals := compiled.indexed.base.globals, administrativePrefix := 1,
              solvedRequirements := rows, internalReason := Word.zero }
            let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .error (.unsupportedExpression node.id node.form)
            if found : source.lookupExpression? node.id = some node then
              match accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 100 compilation source [] node.id (fun _ => Word.zero) with
              | .error error => throw (IO.userError s!"general numeric compiler rejected: {reprStr error}")
              | .ok lowered =>
                have atomic : CompatibleExpressionLiterals.Atomic node.form := form ▸ .integer literal resolution
                have unitType : node.form = .tuple [] → node.type = .unit := by intro impossible; rw [form] at impossible; cases impossible
                have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType (by intros; rfl) rfl rfl accepted
                let _receipt := receipt
                let selected ← match rows.filter (·.id == resolution.requirement) with
                  | [selected] => pure selected
                  | _ => throw (IO.userError "general numeric row not singleton")
                let implementation : ProgramImplId := .builtin (if node.type == .integer then .intInteger else .intWord)
                require (selected.predicate == resolution.predicate && selected.evidence == .implementation (.byImpl resolution.predicate implementation []))
                  "general exact implementation receipt changed"
                let payload := if node.type == .integer then Core.Value.integer (Int.ofNat resolution.rawValue)
                  else Core.Value.word (Word.ofNatModulo resolution.rawValue)
                let captured := Core.Value.closure .unit .word (.var 0) [.word (Word.ofNatModulo 101)]
                let store : Store := [captured, .word (Word.ofNatModulo 103)]
                for fuel in [0, 1, 7, 1000] do
                  let state := Core.runStateful fuel (.initial lowered.expression [captured] store)
                  let finished := match state with
                    | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
                    | result => result
                  match finished with
                  | .done actual after => require (actual == .inRight .word payload && after == store) "general leaf payload/store changed"
                  | other => throw (IO.userError s!"general leaf did not complete: {reprStr other}")
            else throw (IO.userError "general source lookup changed")
        | _ => pure ()
      | _ => pure ()
  require (numeric ≥ 14) "general numeric audit unexpectedly small"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"general full source cells changed: {reprStr state.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "general runtime literals" content
    ["nested", "shortCircuit", "paired", "mappingRoot", "leftFault", "rightFault"]
  inspect compiled
  for fuel in [0, 37, 151, 300000] do
    for name in ["nested", "shortCircuit", "paired", "mappingRoot", "leftFault", "rightFault"] do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel
      let finished ← get "general public resume" (started.resume 300000)
      match name, finished.observation with
      | "nested", .done value state => require (reprStr value == reprStr (word 36)) "nested result"; cells state []
      | "shortCircuit", .done (.bool false) state => cells state [(.word, none)]
      | "paired", .done value state =>
        require (reprStr value == reprStr (SourceTypedRuntime.Value.product (word 19) (word 23))) "pair result"
        cells state [(.word, some (word 19))]
      | "mappingRoot", .done value state =>
        require (reprStr value == reprStr (word 31)) "mapping result"
        cells state [(.mapping .word .word, some (.mapping .word .word [(word 29, word 31)]))]
      | "leftFault", .fault (.uninitializedLocal binder) state
      | "rightFault", .fault (.uninitializedLocal binder) state =>
        let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
        let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
          | [named] => pure named
          | _ => throw (IO.userError "general fault function missing")
        let expected ← match (SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "absent") with
          | [binder] => pure binder.id
          | _ => throw (IO.userError "general absent binder missing")
        require (binder == expected) "general first fault identity changed"
        cells state [(.word, some (word (if name == "leftFault" then 41 else 47))), (.word, none)]
      | _, other => throw (IO.userError s!"general unexpected {name}: {reprStr other}")
  IO.println "general runtime leaves / full ledger / ordered control-data / first fault / full heap / resume GREEN"
end Tests.SourceCoreCompatibleGeneralRuntime
