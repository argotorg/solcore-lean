import Solcore.SourceSemantics.CoreLowering.CompatiblePatternLiteralRuntime
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Actual matcher acceptance supplies numeric implementation provenance. The
formal consumers keep the complete runtime ledger and need neither Covers nor
ordinary validity. Runtime checks also preserve unrelated assumption rows;
those ledger mutations are retained-IR tests, not checker-produced programs. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatiblePatternLiteralRuntime
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatiblePatternLeaves
open SourceCoreCompatibleDataMatches

section Accepted
variable {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
  {fuel : Nat} {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
  {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : CertifiedPattern compilation.definitions}
  (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
  (signatures : context.signatures = compilation.signatures)
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context) (leaf : LeafResolution pattern.resolution)
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
  {sourceValue : Dynamic.Value} {value : Core.Value} {world : StoreTyping}
  (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
include accepted signatures sameLedger runtime leaf represented

theorem accepted_preserves (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store :=
  CompatiblePatternLiteralRuntime.preserves
    (CompatiblePatternLiteralRuntime.of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)
    signatures sameLedger runtime leaf represented environment store

theorem accepted_reflects {environment : Environment} {store after : Store} {outcome : Core.Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome after) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧ after = store :=
  CompatiblePatternLiteralRuntime.reflects
    (CompatiblePatternLiteralRuntime.of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)
    signatures sameLedger runtime leaf represented completed
end Accepted

section ActualFrame
variable {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
  {types : List TypeSystem.Ty} (frame : NamedCalls.SourceFrame program instantiation body function)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (programTyped : ProgramWellFormed program)
  {compilation : SourceCoreCompatibleDataMatches.Context} {fuel : Nat} {scope : Scope}
  {site : StatementId} {span : Syntax.SourceSpan} {expected : TypeSystem.Ty}
  {pattern : TypedMatchPattern} {compiled : CertifiedPattern compilation.definitions}
  (accepted : compilePattern compilation fuel function.source scope site span expected pattern = .ok compiled)
  (signatures : context.signatures = compilation.signatures)
  (sameLedger : function.context.solvedRequirements = compilation.solvedRequirements)
  (leaf : LeafResolution pattern.resolution)
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
  {sourceValue : Dynamic.Value} {value : Core.Value} {world : StoreTyping}
  (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
include frame extended programTyped accepted signatures sameLedger leaf represented

theorem frame_preserves (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store :=
  accepted_preserves accepted signatures
    ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped) leaf represented environment store

theorem frame_reflects {environment : Environment} {store after : Store} {outcome : Core.Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome after) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧ after = store :=
  accepted_reflects accepted signatures
    ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped) leaf represented completed
end ActualFrame

section Boundaries
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def resolution : IntegerLiteralResolution := ⟨37, .word, ⟨0⟩⟩

/-- Runtime validity leaves assumption rows present. It does not authenticate
such a row as the validator-selected numeric implementation. -/
theorem runtime_not_selection :
    RuntimeRequirementLedgerValid ((Context.ofSignatures signatures).withSolvedRequirements [row]) ∧
    ¬ ∃ implementation, NumericLiteralEvidenceReceipts.Selected [row] resolution implementation := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · change ([⟨0⟩] : List RequirementId).Nodup
      decide
    · intro item evidence member implementation
      have eq : item = row := by simpa [Context.withSolvedRequirements] using member
      subst item
      cases implementation
  · rintro ⟨implementation, item, singleton, _, selected⟩
    have eq : item = row := by simpa [row, resolution] using singleton.symm
    subst item
    cases selected

theorem wildcard_needs_no_numeric (compilation : SourceCoreCompatibleDataMatches.Context) :
    CompatiblePatternLiteralRuntime.NumericSelected compilation .wildcard := by
  intro literal numeric impossible
  cases impossible

theorem binder_needs_no_numeric (compilation : SourceCoreCompatibleDataMatches.Context) (binder : TypedBinder) :
    CompatiblePatternLiteralRuntime.NumericSelected compilation (.binder binder) := by
  intro literal numeric impossible
  cases impossible
end Boundaries

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def huge : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639937
private def content : String := String.intercalate "\n" [
  "function wordMatch(x: Word) returns (Word) { match (x) { case 37 { return 11; } case bound { return bound; } } }",
  s!"function wordWrap(x: Word) returns (Word) \{ match (x) \{ case {huge} \{ return 13; } default \{ return 17; } } }",
  s!"function integerMatch(x: integer) returns (Word) \{ match (x) \{ case {huge} \{ return 19; } default \{ return 23; } } }",
  "function faultMatch(x: Word) returns (Word) { match (x) { case 37 { x = 41; let missing: Word; return missing; } default { return 29; } } }"
]

private def inspectPattern (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (site : StatementId) (span : Syntax.SourceSpan) (pattern : TypedMatchPattern)
    (rows : List SolvedRequirement) : IO Unit := do
  let compilation : SourceCoreCompatibleDataMatches.Context :=
    ⟨.initial checked, rows, none, none⟩
  match accepted : compilePattern compilation 100 source [] site span pattern.type pattern with
  | .error error => throw (IO.userError s!"actual numeric matcher rejected: {reprStr error}")
  | .ok compiled =>
    have receipt := CompatiblePatternLiteralRuntime.of_compilePattern compilation 100 source [] site span pattern.type pattern compiled accepted
    let _receipt := receipt
    match pattern.resolution with
    | .integerLiteral _ numeric =>
      let selected ← match rows.filter (·.id == numeric.requirement) with
        | [row] => pure row
        | _ => throw (IO.userError "numeric matcher row lost singleton identity")
      let implementation : ProgramImplId := .builtin (if pattern.type == .integer then .intInteger else .intWord)
      require (selected.predicate == numeric.predicate &&
        selected.evidence == .implementation (.byImpl numeric.predicate implementation []))
        "numeric matcher full implementation/premises changed"
      let expected := if pattern.type == .integer then Core.Value.integer (Int.ofNat numeric.rawValue)
        else .word (Word.ofNatModulo numeric.rawValue)
      let different := if pattern.type == .integer then Core.Value.integer (Int.ofNat numeric.rawValue + 1)
        else .word (Word.ofNatModulo (numeric.rawValue + 1))
      for (input, wanted) in [(expected, Core.Value.inRight .unit .unit), (different, .inLeft .unit .unit)] do
        let quoted ← match SourceCoreCompatibleDataExpressions.quote input with
          | some code => pure code | none => throw (IO.userError "numeric input quote missing")
        let code := Core.Expr.apply compiled.pattern.matcher quoted
        require (Core.Program.mk compiled.pattern.resultType code compilation.definitions).check
          "numeric matcher actual native typing failed"
        let sentinel : Core.Store := [.integer 901, .closure .unit .integer (.var 1) [.integer 777], .cellRef .integer 0]
        for fuel in [0, 2, 11, 1000] do
          let outcome := match Core.runStateful fuel (.initial code [] sentinel) with
            | .outOfFuel pending => Core.runStateful 1000 pending
            | other => other
          match outcome with
          | .done actual store =>
            require (actual == wanted && store == sentinel)
              "numeric match/miss or full saved store/captures changed on resume"
          | other => throw (IO.userError s!"numeric matcher did not finish: {reprStr other}")
    | _ => throw (IO.userError "numeric matcher audit reached a nonnumeric pattern")

private def inspect (artifact : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut count := 0
  for named in artifact.indexed.base.functions do
    let selected ← get "actual selected numeric matcher owner"
      (SourceCompilationPlan.exactSpecialization artifact.indexed.base.plan named.signature.key)
    require (selected == named.specialized) "numeric matcher full selected function changed"
    let source := selected.function.typedBody
    let rows := selected.function.solvedRequirements
    for retained in source.nodes do
      match retained with
      | .statement statement => match statement.form with
        | .matchWith metadata =>
          for arm in metadata.cases do
            match arm.pattern.resolution with
            | .integerLiteral _ numeric =>
              count := count + 1
              inspectPattern artifact.compatible.checked source statement.id arm.span arm.pattern rows
              let fresh : RequirementId := ⟨(rows.map (·.id.index)).foldl max 0 + 1⟩
              let unused : SolvedRequirement := ⟨fresh, numeric.predicate, .assumption numeric.predicate⟩
              for fullRows in [unused :: rows, rows ++ [unused]] do
                inspectPattern artifact.compatible.checked source statement.id arm.span arm.pattern fullRows
              let malformed := rows.map fun row => if row.id == numeric.requirement then
                {row with evidence := .assumption row.predicate} else row
              let compilation : SourceCoreCompatibleDataMatches.Context :=
                ⟨.initial artifact.compatible.checked, malformed, none, none⟩
              require (compilePattern compilation 100 source [] statement.id arm.span arm.pattern.type arm.pattern).toOption.isNone
                "numeric matcher accepted metadata without actual implementation"
              let duplicated := rows ++ rows.filter (·.id == numeric.requirement)
              require (compilePattern {compilation with solvedRequirements := duplicated} 100 source [] statement.id arm.span arm.pattern.type arm.pattern).toOption.isNone
                "numeric matcher accepted a duplicate selected requirement ID"
            | _ => pure ()
        | _ => pure ()
      | _ => pure ()
  require (count == 4) "actual matcher audit count changed"

/-- The matcher is compiled from a real specialized body that still contains
qualified-local template rows. This certifies only the reached pattern, not
the lambda or the complete callable body. -/
private def template_root : IO Unit := do
  let program ← get "pattern checked template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " let f = lam(item) { return keep(item); }; let number: Word = 61;",
      " match (number) { case 61 { return (f(1), f(flag)); } default { return (f(2), f(flag)); } } }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "template pattern signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "template pattern function missing")
  let actual ← get "pattern actual template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger.map (·.id) == generic.solvedRequirements.map (·.id))
    "pattern template IDs or complete ordered ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !actual.assumptions.contains predicate)
          "pattern template assumption was promoted"
      | _ => throw (IO.userError "pattern template implementation fabricated")
    | _ => throw (IO.userError "pattern template row missing or duplicated")
  let checked ← get "pattern template catalog" (SourceCoreCompatibleCatalog.prepare program.signatures 100 [.word, .bool])
  let mut count := 0
  for node in source.nodes do
    match node with
    | .statement statement => match statement.form with
      | .matchWith metadata =>
        for arm in metadata.cases do
          match arm.pattern.resolution with
          | .integerLiteral _ _ =>
            inspectPattern checked source statement.id arm.span arm.pattern ledger
            count := count + 1
          | _ => pure ()
      | _ => pure ()
    | _ => pure ()
  require (count == 1) "template pattern occurrence count changed"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"numeric pattern full source heap changed: {reprStr state.heap}"

def run : IO Unit := do
  let artifact ← SourceCoreUnifiedCorpusSupport.prepare "runtime numeric pattern receipts" content
    ["wordMatch", "wordWrap", "integerMatch", "faultMatch"]
  inspect artifact
  template_root
  let w := Word.ofNatModulo
  let successes : List (String × SourceTypedRuntime.Value × Nat × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("wordMatch", .word (w 37), 11, [(.word, some (.word (w 37))), (.word, some (.word (w 37)))]),
    ("wordMatch", .word (w 7), 7, [(.word, some (.word (w 7))), (.word, some (.word (w 7))), (.word, some (.word (w 7)))]),
    ("wordWrap", .word (w 1), 13, [(.word, some (.word (w 1))), (.word, some (.word (w 1)))]),
    ("wordWrap", .word (w 2), 17, [(.word, some (.word (w 2))), (.word, some (.word (w 2)))]),
    ("integerMatch", .integer (Int.ofNat huge), 19, [(.integer, some (.integer (Int.ofNat huge))), (.integer, some (.integer (Int.ofNat huge)))]),
    ("integerMatch", .integer 1, 23, [(.integer, some (.integer 1)), (.integer, some (.integer 1))]),
    ("faultMatch", .word (w 3), 29, [(.word, some (.word (w 3))), (.word, some (.word (w 3)))])]
  let missing ← match (artifact.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
    | [binder] => pure binder.id | _ => throw (IO.userError "numeric pattern missing binder identity lost")
  for fuel in [0, 37, 151, 300000] do
    for (name, input, result, heap) in successes do
      let first ← SourceCoreUnifiedCorpusSupport.execute artifact name [input] fuel
      let finished ← get "numeric match public resume" (first.resume 300000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr (SourceTypedRuntime.Value.word (w result))) "numeric match public result changed"
        cells state heap
      | other => throw (IO.userError s!"numeric match success expected: {reprStr other}")
    let first ← SourceCoreUnifiedCorpusSupport.execute artifact "faultMatch" [.word (w 37)] fuel
    let finished ← get "numeric match fault resume" (first.resume 300000)
    match finished.observation with
    | .fault (.uninitializedLocal actual) state =>
      require (actual == missing) "numeric pattern first fault identity changed"
      cells state [(.word, some (.word (w 41))), (.word, some (.word (w 37))), (.word, none)]
    | other => throw (IO.userError s!"numeric selected arm fault expected: {reprStr other}")
  IO.println "pattern actual numeric rows / complete runtime ledger / Word Integer match and miss / full store and heap / resume GREEN"
end Tests.SourceCoreCompatiblePatternLiteralRuntime
