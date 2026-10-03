import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Actual atomic compiler receipts supply the selected numeric evidence.
Full runtime ledgers, including unrelated assumptions, stay unchanged. This
unit covers the ordinary function-policy leaf branch; contextual expressions
and larger expression trees are not certified here. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleLiteralRuntime
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly

section Accepted
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (found : source.lookupExpression? id = some node)
  (atomic : CompatibleExpressionLiterals.Atomic node.form)
  (unitType : node.form = .tuple [] → node.type = .unit)
  (special : ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
  (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
  (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
  (program : SourceSemantics.Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context) (faults : FunctionCalls.FaultRep)

include found atomic unitType special readPolicy leafPolicy accepted sameLedger runtime

/-- No whole-context ordinary validity or source execution callback is needed
for a receipt taken from the actual accepted atomic compilation. -/
theorem accepted_preserves (unique : NodeOccurrencesUnique source) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun s i code => s = scope ∧ i = id ∧ code = lowered) faults := by
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted
  intro s i code selected
  obtain ⟨rfl, rfl, rfl⟩ := selected
  exact CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtime unique faults receipt

/-- The same static receipt closes reflection from native completion alone. -/
theorem accepted_reflects :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun s i code => s = scope ∧ i = id ∧ code = lowered) faults := by
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted
  intro s i code selected
  obtain ⟨rfl, rfl, rfl⟩ := selected
  exact CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtime source faults receipt
end Accepted

section ActualFrame
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
  {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
  {types : List TypeSystem.Ty} {solved : List SolvedRequirement}
  (frame : NamedCalls.SourceFrame program instantiation body function)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved)
  (faults : FunctionCalls.FaultRep)

include frame extended programTyped sameLedger

/-- Initial frame validity supplies the complete runtime ledger without an
empty-template condition, Header.valid, or an ordinary-ledger callback. -/
theorem frame_preserves (unique : NodeOccurrencesUnique function.source) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context function.evidence function.source
      (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved function.source id lowered) faults :=
  CompatibleExpressionLiteralRuntime.preserves functions program context function.evidence
    ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped) unique faults

theorem frame_reflects :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context function.evidence function.source
      (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved function.source id lowered) faults :=
  CompatibleExpressionLiteralRuntime.reflects functions program context function.evidence
    ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped) function.source faults
end ActualFrame


section Boundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def resolution : IntegerLiteralResolution := ⟨37, .word, ⟨0⟩⟩
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"literal_runtime", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def node : ExpressionNode := {
  id := ⟨⟨owner, 0⟩⟩, span := ⟨⟨.main, "literal_runtime.solc"⟩, 0, 2⟩,
  type := .word, form := .integerLiteral (.decimal "37") resolution, requirements := [⟨0⟩] }

/-- The old literal metadata deliberately does not certify implementation
provenance. A runtime-valid assumption-only ledger cannot replace acceptance. -/
theorem metadata_not_acceptance :
    CompatibleExpressionLiterals.Literal [row] node .word
      (LanguageResult.success (.word (Word.ofNatModulo 37))) ∧
    RuntimeRequirementLedgerValid ((Context.ofSignatures signatures).withSolvedRequirements [row]) ∧
    ¬ CompatibleExpressionLiteralRuntime.NumericSelected [row] node := by
  refine ⟨?_, ?_, ?_⟩
  · apply CompatibleExpressionLiterals.Literal.resolvedWord (validated := ⟨Word.ofNatModulo 37, [⟨0⟩]⟩) rfl
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩
    · exact numericLiteralValue?_sound rfl
    · exact ⟨row, by simp, rfl, rfl⟩
  · refine ⟨?_, ?_⟩
    · change ([⟨0⟩] : List RequirementId).Nodup
      decide
    · intro item evidence member implementation
      have eq : item = row := by simpa [Context.withSolvedRequirements] using member
      subst item
      cases implementation
  · intro selected
    obtain ⟨item, singleton, _, implementation⟩ := selected (.decimal "37") resolution rfl
    have eq : item = row := by simpa [row, resolution] using singleton.symm
    subst item
    cases implementation
end Boundary

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def huge : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639937
private def content : String := String.intercalate "\n" [
  "function unitRoot() { return (); }",
  "function boolRoot() returns (Bool) { return true; }",
  "function wordRoot() returns (Word) { let first = 0x25; return first; }",
  s!"function wrapRoot() returns (Word) \{ return {huge}; }",
  s!"function integerRoot() returns (integer) \{ let full = {huge}; return full; }",
  "function faultRoot() returns (Word) { let prior = 41; let missing: Word; return missing + 43; }"
]

private def scalar? : Expr → Option Core.Value
  | .unit => some .unit | .bool b => some (.bool b) | .word w => some (.word w)
  | .integer n => some (.integer n) | _ => none

private def inspectNode (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (rows : List SolvedRequirement) (node : ExpressionNode)
    (atomic : CompatibleExpressionLiterals.Atomic node.form) : IO Ty := do
  let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
  let policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
  let context : SourceCoreFunctions.Context := {
    plan := compiled.indexed.base.plan, owner := named.signature.key,
    globals := compiled.indexed.base.globals, administrativePrefix := 1,
    solvedRequirements := rows, internalReason := Word.zero }
  let lowerBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ =>
    .error (.unsupportedExpression node.id node.form)
  if found : source.lookupExpression? node.id = some node then
    if unitType : node.form = .tuple [] → node.type = .unit then
      match accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody 100 context source [] node.id (fun _ => Word.zero) with
      | .error error => throw (IO.userError s!"actual atomic compiler rejected: {reprStr error}")
      | .ok lowered =>
        have receipt : CompatibleExpressionLiteralRuntime.Certificate rows source node.id lowered := CompatibleExpressionLiteralRuntime.of_functions
          found atomic unitType (by intros; rfl) rfl rfl accepted
        let _receipt := receipt
        let expected ← match lowered.expression with
          | .inRight .word payload => match scalar? payload with
            | some value => pure (.inRight .word value)
            | none => throw (IO.userError "atomic payload is not scalar")
          | _ => throw (IO.userError "atomic language result carrier changed")
        match node.form with
        | .integerLiteral _ resolution =>
          let selected ← match rows.filter (·.id == resolution.requirement) with
            | [selected] => pure selected
            | _ => throw (IO.userError "atomic selected row is not singleton")
          let implementation : ProgramImplId := .builtin (if node.type == .integer then .intInteger else .intWord)
          require (selected.predicate == resolution.predicate &&
            selected.evidence == .implementation (.byImpl resolution.predicate implementation []))
            "atomic full implementation receipt changed"
          let numeric := if node.type == .integer then Core.Value.integer (Int.ofNat resolution.rawValue)
            else .word (Word.ofNatModulo resolution.rawValue)
          require (expected == .inRight .word numeric) "atomic numeric target/payload changed"
        | _ => pure ()
        let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
          .letE (.newCell (.function .unit .unit) (.lambda .unit .unit .unit)) (lowered.expression.weakenAt 0),
          compiled.compatible.checked.catalog.definitions⟩
        require native.check "actual atomic emission failed Core typing"
        for fuel in [0, 1, 5, 1000] do
          let completed := match native.runStateful fuel with
            | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
            | other => other
          match completed with
          | .done value store =>
            require (value == expected && store == [.closure .unit .unit .unit []])
              "atomic leaf changed result/administrative store on resume"
          | other => throw (IO.userError s!"atomic native completion missing: {reprStr other}")
        pure lowered.type
    else throw (IO.userError "atomic unit has wrong raw type")
  else throw (IO.userError "atomic occurrence lookup changed")

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut types := []
  let mut numeric := 0
  let mut legacy := 0
  for named in compiled.indexed.base.functions do
    let actual ← get "atomic actual specialization"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (actual == named.specialized) "atomic full selected record changed"
    let source : TypedSource := actual.function.typedBody
    let ledger : List SolvedRequirement := actual.function.solvedRequirements
    for retained in source.nodes do
      match retained with
      | .expression node =>
        let atomic : Option (PLift (CompatibleExpressionLiterals.Atomic node.form)) := match form : node.form with
          | .tuple [] => some ⟨form ▸ CompatibleExpressionLiterals.Atomic.unit⟩
          | .reference name (.builtinBoolean value) => some ⟨form ▸ CompatibleExpressionLiterals.Atomic.bool name value⟩
          | .literal value => some ⟨form ▸ CompatibleExpressionLiterals.Atomic.word value⟩
          | .integerLiteral value resolution => some ⟨form ▸ CompatibleExpressionLiterals.Atomic.integer value resolution⟩
          | _ => none
        if let some boxed := atomic then
          let atomic := boxed.down
          types := types ++ [← inspectNode compiled named source ledger node atomic]
          match node.form with
          | .integerLiteral _ resolution =>
            numeric := numeric + 1
            let fresh : RequirementId := ⟨(ledger.map (·.id.index)).foldl max 0 + 1⟩
            let assumption : SolvedRequirement := ⟨fresh, resolution.predicate, .assumption resolution.predicate⟩
            -- Explicit test mutations retain every original row; they are not
            -- asserted to be produced by the independent checker.
            for rows in [assumption :: ledger, ledger ++ [assumption]] do
              let type ← inspectNode compiled named source rows node atomic
              require (types.contains type) "unrelated assumption changed native type"
            let malformed := ledger.map fun row => if row.id == resolution.requirement then
              {row with evidence := .assumption row.predicate} else row
            let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
            let context : SourceCoreFunctions.Context := {
              plan := compiled.indexed.base.plan, owner := named.signature.key,
              globals := compiled.indexed.base.globals, administrativePrefix := 1,
              solvedRequirements := malformed, internalReason := Word.zero }
            let rejected := SourceCoreFunctions.lowerExpressionWithPolicy
              (SourceCoreCompatibleDataExpressions.functionPolicy 100 values)
              (fun _ _ _ _ _ _ _ _ _ => .error (.unsupportedExpression node.id node.form))
              100 context source [] node.id (fun _ => Word.zero)
            require rejected.toOption.isNone "actual compiler accepted missing implementation provenance"
            if node.type == .word then
              let old := {node with form := .literal (.decimal "37"), requirements := [], coercions := []}
              let oldSource := {source with nodes := source.nodes.map fun
                | .expression entry => if entry.id == old.id then .expression old else .expression entry
                | .statement entry => .statement entry}
              let oldType ← inspectNode compiled named oldSource ledger old (.word _)
              require (oldType == .word) "retained legacy literal branch missing"
              legacy := legacy + 1
          | _ => pure ()
      | _ => pure ()
  for expected in [Ty.unit, .bool, .word, .integer] do
    require (types.contains expected) s!"actual atomic family missed {reprStr expected}"
  require (numeric ≥ 5 && legacy ≥ 4) "atomic numeric/legacy audit too small"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"atomic full source heap changed: {reprStr state.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "atomic runtime receipts" content
    ["unitRoot", "boolRoot", "wordRoot", "wrapRoot", "integerRoot", "faultRoot"]
  inspect compiled
  let missing ← match (compiled.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "atomic missing binder identity lost")
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("unitRoot", .unit, []), ("boolRoot", .bool true, []),
    ("wordRoot", .word (Word.ofNatModulo 37), [(.word, some (.word (Word.ofNatModulo 37)))]),
    ("wrapRoot", .word (Word.ofNatModulo 1), []),
    ("integerRoot", .integer (Int.ofNat huge), [(.integer, some (.integer (Int.ofNat huge)))])]
  for fuel in [0, 37, 151, 300000] do
    for (name, expected, heap) in successes do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel
      let finished ← get "atomic public resume" (started.resume 300000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr expected) "atomic public completed value changed"
        cells state heap
      | other => throw (IO.userError s!"atomic public success expected: {reprStr other}")
    let started ← SourceCoreUnifiedCorpusSupport.execute compiled "faultRoot" [] fuel
    let finished ← get "atomic public fault resume" (started.resume 300000)
    match finished.observation with
    | .fault (.uninitializedLocal actual) state =>
      require (actual == missing) "atomic first fault identity changed"
      cells state [(.word, some (.word (Word.ofNatModulo 41))), (.word, none)]
    | other => throw (IO.userError s!"atomic first fault expected: {reprStr other}")
  IO.println "atomic actual receipts / full runtime ledger / Unit Bool Word Integer / full heap / resume GREEN"

end Tests.SourceCoreCompatibleLiteralRuntime
