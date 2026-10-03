import Solcore.SourceSemantics.CoreLowering.CompatibleMatchContextFactory
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Actual composite matcher acceptance supplies every numeric leaf receipt.
The formal consumers preserve the full ledger and do not require ordinary
validity, Covers, source execution or preservation as a reflection input.
Retained-IR tests for repeated leaves and unused rows are labelled separately.
Whole ordered Match and Header/Profile integration are not claimed here. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatiblePatternRuntime
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
  (runtime : RuntimeRequirementLedgerValid context)
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  (extension : SourceCoreRawMetadata.Extends compilation.values.registry registry)
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
  {sourceValue : Dynamic.Value} {value : Core.Value} {world : StoreTyping}
  (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
include accepted signatures sameLedger runtime catalogValid extension represented

theorem accepted_preserves (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store :=
  CompatiblePatternRuntime.preserves
    (CompatiblePatternRuntime.of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)
    ⟨signatures, sameLedger, runtime⟩ catalogValid extension represented environment store

theorem accepted_reflects {environment : Environment} {store after : Store} {outcome : Core.Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome after) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧ after = store :=
  CompatiblePatternRuntime.reflects
    (CompatiblePatternRuntime.of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)
    ⟨signatures, sameLedger, runtime⟩ catalogValid extension represented completed
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

  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  (extension : SourceCoreRawMetadata.Extends compilation.values.registry registry)
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
  {sourceValue : Dynamic.Value} {value : Core.Value} {world : StoreTyping}
  (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
include frame extended programTyped accepted signatures sameLedger catalogValid extension represented

theorem frame_preserves (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store :=
  accepted_preserves accepted signatures
    ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped) catalogValid extension represented environment store

theorem frame_reflects {environment : Environment} {store after : Store} {outcome : Core.Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome after) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧ after = store :=
  accepted_reflects accepted signatures
    ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped) catalogValid extension represented completed
end ActualFrame


section Boundaries
open CompatiblePatternCertificates CompatiblePatternDecision

/-- Both occurrences retain the same child proof when an instruction stream
repeats a numeric resolution; no set-like normalization is performed. -/
theorem repeated_sites {compilation : Compilation} {source : TypedSource} {site : StatementId}
    {span : Syntax.SourceSpan} {scope : Scope} {type : TypeSystem.Ty} {native : Core.Ty}
    {literal : Syntax.CoreLiteralValue} {numeric : IntegerLiteralResolution} {matcher : Core.Expr}
    (projection : projected compilation source type = .ok native)
    (validated : literalMatcher compilation site span type literal numeric = .ok matcher)
    :
    Forest.LiteralSites (fun numeric => ∃ implementation, NumericLiteralEvidenceReceipts.Selected compilation.solvedRequirements numeric implementation) (Forest.cons
      (Tree.literal (scope := scope) (rest := [.integerLiteral literal numeric]) projection validated)
      (Forest.cons (Tree.literal (scope := scope) (rest := []) projection validated) .nil)) := by
  intro resolution occurrence
  cases occurrence with
  | head first =>
    exact Tree.literalSites _ _
      (fun expected literal resolution matcher accepted =>
        CompatiblePatternLiteralRuntime.literalMatcher_selected compilation site span expected literal resolution matcher accepted) _ first
  | tail remaining =>
    cases remaining with
    | head first =>
      exact Tree.literalSites _ _
        (fun expected literal resolution matcher accepted =>
          CompatiblePatternLiteralRuntime.literalMatcher_selected compilation site span expected literal resolution matcher accepted) _ first
    | tail impossible => cases impossible

theorem empty_forest_sites {compilation : Compilation} {source : TypedSource} {site : StatementId}
    {span : Syntax.SourceSpan} {scope : Scope} (literals : IntegerLiteralResolution → Prop)
    (instructions : List MatchPatternInstruction) :
    Forest.LiteralSites literals (Forest.nil (compilation := compilation) (source := source)
      (site := site) (span := span) (scope := scope) (instructions := instructions)) := by
  intro resolution impossible
  cases impossible

/-- The factory retains the whole ledger and actual covering dictionary across
an independently typed match arm's binder context. -/
theorem scoped_runtime_fields {source : TypedSource} {parent child : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)}
    {request : GenericMatchChildren.Request} {solved : List SolvedRequirement}
    {evidence : Dynamic.EvidenceEnvironment}
    (related : GenericMatchChildren.ScopedContextFor source parent hiddenIds scrutineeType cases fallback request child)
    (valid : CompatibleRuntimeContextValidity.Valid solved parent evidence) :
    child.solvedRequirements = solved ∧ RuntimeRequirementLedgerValid child ∧ evidence.Covers child := by
  have result := CompatibleMatchContextFactory.scoped_runtime related valid
  exact ⟨result.ledger, result.runtime, result.covers⟩

end Boundaries

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def content : String := String.intercalate "\n" [
  "enum Tree { Leaf(Word), Pair(Tree, Tree) }",
  "enum Box<T> { Box(T) }",
  "function nested(tree: Tree) returns (Word) { match (tree) { case .Pair(.Leaf(37), .Leaf(bound)) { return bound; } case .Pair(.Leaf(left), .Leaf(right)) { return left + right; } default { return 99; } } }",
  "function tuple(a: Word, b: Word) returns (Word) { match ((a, b)) { case (37, 37) { return 11; } case (left, right) { return left + right; } } }",
  "function integerTuple(a: integer, b: Word) returns (Word) { match ((a, b)) { case (73, bound) { return bound; } default { return 17; } } }",
  "function faultTuple(a: Word, b: Word) returns (Word) { match ((a, b)) { case (37, bound) { a = bound; let missing: Word; return missing; } default { return 29; } } }"
]

private def auditPattern (compilation : SourceCoreCompatibleDataMatches.Context) (source : TypedSource)
    (site : StatementId) (span : Syntax.SourceSpan) (pattern : TypedMatchPattern)
    (inputs : List (Core.Value × Core.Value)) (names : List String) : IO Unit := do
  match accepted : compilePattern compilation 100 source [] site span pattern.type pattern with
  | .error error => throw (IO.userError s!"composite matcher rejected: {reprStr error}")
  | .ok compiled =>
    have receipt := CompatiblePatternRuntime.of_compilePattern compilation 100 source [] site span pattern.type pattern compiled accepted
    let _receipt := receipt
    require (compiled.pattern.requirements == pattern.requirements && compiled.pattern.bindings.map (·.1.name) == names)
      "composite matcher changed ordered requirements or binders"
    let code := Core.Expr.apply compiled.pattern.matcher (.var 0)
    require (Core.infer? [compiled.pattern.type] code compilation.definitions == some compiled.pattern.resultType)
      "composite matcher native typing failed"
    let sentinel : Core.Store := [.integer 901, .closure .unit .integer (.var 1) [.integer 777], .cellRef .integer 0]
    for (input, wanted) in inputs do
      for fuel in [0, 3, 19, 10000] do
        let result := match Core.runStateful fuel (.initial code [input] sentinel) with
          | .outOfFuel pending => Core.runStateful 10000 pending
          | other => other
        match result with
        | .done actual after =>
          require (actual == wanted && after == sentinel)
            "composite match/miss, ordered bindings, captured sentinel or full store changed"
        | other => throw (IO.userError s!"composite matcher did not finish: {reprStr other}")

/-- Retained metadata fixtures isolate raw constructor identity and the empty
ordered forest. They are accepted by the actual pattern compiler. -/
private def raw_and_empty (program : CheckedProgram) (source : TypedSource)
    (site : StatementId) (span : Syntax.SourceSpan) : IO Unit := do
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "Box signature missing")
  let boxType := TypeSystem.Ty.nominal box.id [.word]
  let stagedType := TypeSystem.Ty.nominal box.id [.comptime .word]
  let ordinary : DataConstructorInstantiation := ⟨⟨box.id, 0⟩, box.parameters.zip [.word], [.word], boxType⟩
  let staged : DataConstructorInstantiation := ⟨⟨box.id, 0⟩, box.parameters.zip [.comptime .word], [.comptime .word], stagedType⟩
  let checked ← get "composite raw guard catalog" (SourceCoreCompatibleCatalog.prepare program.signatures 100 [boxType, stagedType, .unit])
  let first ← get "composite ordinary raw constructor"
    (SourceCoreCompatibleValues.encode 100 (.initial checked) boxType (.constructed ordinary [.word (Word.ofNatModulo 7)]))
  let second ← get "composite staged raw constructor"
    (SourceCoreCompatibleValues.encode 100 first.context boxType (.constructed staged [.word (Word.ofNatModulo 7)]))
  let compilation : SourceCoreCompatibleDataMatches.Context := ⟨second.context, [], none, some (checked.catalog.definitions ++ [⟨[.unit]⟩])⟩
  let pattern : TypedMatchPattern := {
    source := .group span (.constructor span (some span) [] "Box" 1), type := boxType
    resolution := .constructor ordinary [.wildcard] }
  auditPattern compilation source site span pattern
    [(first.value, .inRight .unit .unit), (second.value, .inLeft .unit .unit)] []
  let empty : TypedMatchPattern := {source := .tuple span 0, type := .unit, resolution := .tuple []}
  auditPattern compilation source site span empty [(.unit, .inRight .unit .unit)] []

/-- A real checked specialization retains qualified local template rows. Only
the reached composite pattern is compiled; the complete lambda body is outside
this consumer's scope. -/
private def template_root : IO Unit := do
  let program ← get "composite template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " let f = lam(item) { return keep(item); }; let number: Word = 61;",
      " match ((number, number)) { case (61, 61) { return (f(1), f(flag)); } default { return (f(2), f(flag)); } } }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "composite template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "composite template function missing")
  let actual ← get "composite actual template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger.map (·.id) == generic.solvedRequirements.map (·.id))
    "composite template IDs or complete ordered ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !actual.assumptions.contains predicate)
          "composite template assumption was promoted"
      | _ => throw (IO.userError "composite template implementation fabricated")
    | _ => throw (IO.userError "composite template row missing or duplicated")
  let checked ← get "composite template catalog"
    (SourceCoreCompatibleCatalog.prepare program.signatures 100 [.word, .bool, .product .word .word])
  let compilation : SourceCoreCompatibleDataMatches.Context := ⟨.initial checked, ledger, none, none⟩
  let w := Word.ofNatModulo
  let mut count := 0
  for node in source.nodes do
    match node with
    | .statement statement => match statement.form with
      | .matchWith metadata =>
        for arm in metadata.cases do
          auditPattern compilation source statement.id arm.span arm.pattern
            [(.pair (.word (w 61)) (.word (w 61)), .inRight .unit .unit),
             (.pair (.word (w 62)) (.word (w 61)), .inLeft .unit .unit),
             (.pair (.word (w 61)) (.word (w 62)), .inLeft .unit .unit)] []
          count := count + 1
      | _ => pure ()
    | _ => pure ()
  require (count == 1) "composite template occurrence count changed"

private def inspect (artifact : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let w := Word.ofNatModulo
  let tree ← match artifact.sourceProgram.signatures.dataTypes.find? (·.name == "Tree") with
    | some tree => pure tree | none => throw (IO.userError "Tree signature missing")
  let treeType := TypeSystem.Ty.nominal tree.id []
  let leaf : DataConstructorInstantiation := ⟨⟨tree.id, 0⟩, [], [.word], treeType⟩
  let pair : DataConstructorInstantiation := ⟨⟨tree.id, 1⟩, [], [treeType, treeType], treeType⟩
  let leafValue (n : Nat) : SourceCoreCompatibleValues.Value := .constructed leaf [.word (w n)]
  let mut values := SourceCoreCompatibleValues.Context.initial artifact.compatible.checked
  let mut nativeTrees : List Core.Value := []
  for input in [(SourceCoreDataValues.Value.constructed pair [leafValue 37, leafValue 8]),
      .constructed pair [leafValue 2, leafValue 8], leafValue 7] do
    let encoded ← get "composite constructor input" (SourceCoreCompatibleValues.encode 100 values treeType input)
    values := encoded.context
    nativeTrees := nativeTrees ++ [encoded.value]
  let mut count := 0
  for named in artifact.indexed.base.functions do
    let actual ← get "composite full selected record"
      (SourceCompilationPlan.exactSpecialization artifact.indexed.base.plan named.signature.key)
    require (actual == named.specialized) "composite owner specialization changed"
    let signature ← match artifact.sourceProgram.signatures.functions.find? (·.id == actual.function.declaration) with
      | some signature => pure signature | none => throw (IO.userError "actual signature missing")
    let source := actual.function.typedBody
    let rows := actual.function.solvedRequirements
    for node in source.nodes do
      match node with
      | .statement statement => match statement.form with
        | .matchWith metadata =>
          for (arm, index) in metadata.cases.zipIdx do
            let compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, rows, none, none⟩
            let failure := Core.Value.inLeft (bundleType (← get "binding native types"
              ((match compilePattern compilation 100 source [] statement.id arm.span arm.pattern.type arm.pattern with
                | .ok compiled => .ok compiled.pattern.bindingTypes | .error error => .error error)))) .unit
            let (inputs, names) : List (Core.Value × Core.Value) × List String :=
              if signature.name == "nested" then
                if index == 0 then (nativeTrees.zip [.inRight .unit (.word (w 8)), failure, failure], ["bound"])
                else (nativeTrees.zip [.inRight .unit (.pair (.word (w 37)) (.word (w 8))),
                  .inRight .unit (.pair (.word (w 2)) (.word (w 8))), failure], ["left", "right"])
              else if signature.name == "tuple" then
                if index == 0 then ([(.pair (.word (w 37)) (.word (w 37)), .inRight .unit .unit),
                  (.pair (.word (w 1)) (.word (w 37)), failure), (.pair (.word (w 37)) (.word (w 2)), failure)], [])
                else ([(.pair (.word (w 4)) (.word (w 9)), .inRight .unit (.pair (.word (w 4)) (.word (w 9))))], ["left", "right"])
              else if signature.name == "integerTuple" then
                ([(.pair (.integer 73) (.word (w 8)), .inRight .unit (.word (w 8))),
                  (.pair (.integer 74) (.word (w 8)), failure)], ["bound"])
              else ([(.pair (.word (w 37)) (.word (w 8)), .inRight .unit (.word (w 8))),
                (.pair (.word (w 1)) (.word (w 8)), failure)], ["bound"])
            auditPattern compilation source statement.id arm.span arm.pattern inputs names
            let unusedId : RequirementId := ⟨(rows.map (·.id.index)).foldl max 0 + 1⟩
            let unusedGoal := ProgramSignatures.builtinIntPredicate .word
            let unused : SolvedRequirement := ⟨unusedId, unusedGoal, .assumption unusedGoal⟩
            for fullRows in [unused :: rows, rows ++ [unused]] do
              auditPattern {compilation with solvedRequirements := fullRows} source statement.id arm.span arm.pattern inputs names
            if signature.name == "tuple" && index == 0 then
              match arm.pattern.resolution with
              | .tuple [first@(.integerLiteral _ numeric), .integerLiteral _ _] =>
                let repeated := {arm.pattern with resolution := .tuple [first, first], requirements := [numeric.requirement, numeric.requirement]}
                auditPattern compilation source statement.id arm.span repeated inputs names
                let malformed := rows.map fun row => if row.id == numeric.requirement then
                  {row with evidence := .assumption row.predicate} else row
                require (compilePattern {compilation with solvedRequirements := malformed} 100 source [] statement.id arm.span repeated.type repeated).toOption.isNone
                  "composite matcher accepted a numeric assumption row"
              | _ => throw (IO.userError "tuple numeric instruction order changed")
            if count == 0 then raw_and_empty artifact.sourceProgram source statement.id arm.span
            count := count + 1
        | _ => pure ()
      | _ => pure ()
  require (count == 6) "composite matcher occurrence count changed"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"composite full ordered source heap changed: {reprStr state.heap}"

def run : IO Unit := do
  let artifact ← SourceCoreUnifiedCorpusSupport.prepare "composite runtime pattern receipts" content
    ["nested", "tuple", "integerTuple", "faultTuple"]
  inspect artifact
  template_root
  let w := Word.ofNatModulo
  let successes : List (String × List SourceTypedRuntime.Value × Nat × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("tuple", [.word (w 37), .word (w 37)], 11, [(.word, some (.word (w 37))), (.word, some (.word (w 37))),
      (.product .word .word, some (.product (.word (w 37)) (.word (w 37))))]),
    ("tuple", [.word (w 4), .word (w 9)], 13, [(.word, some (.word (w 4))), (.word, some (.word (w 9))),
      (.product .word .word, some (.product (.word (w 4)) (.word (w 9)))), (.word, some (.word (w 4))), (.word, some (.word (w 9)))]),
    ("integerTuple", [.integer 73, .word (w 8)], 8, [(.integer, some (.integer 73)), (.word, some (.word (w 8))),
      (.product .integer .word, some (.product (.integer 73) (.word (w 8)))), (.word, some (.word (w 8)))]),
    ("integerTuple", [.integer 74, .word (w 8)], 17, [(.integer, some (.integer 74)), (.word, some (.word (w 8))),
      (.product .integer .word, some (.product (.integer 74) (.word (w 8))))]),
    ("faultTuple", [.word (w 1), .word (w 8)], 29, [(.word, some (.word (w 1))), (.word, some (.word (w 8))),
      (.product .word .word, some (.product (.word (w 1)) (.word (w 8))))])]
  let missing ← match (artifact.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
    | [binder] => pure binder.id | _ => throw (IO.userError "composite missing binder identity lost")
  for fuel in [0, 37, 151, 300000] do
    for (name, inputs, result, heap) in successes do
      let first ← SourceCoreUnifiedCorpusSupport.execute artifact name inputs fuel
      let finished ← get "composite public resume" (first.resume 300000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr (SourceTypedRuntime.Value.word (w result))) "composite result changed"
        cells state heap
      | other => throw (IO.userError s!"composite success expected: {reprStr other}")
    let first ← SourceCoreUnifiedCorpusSupport.execute artifact "faultTuple" [.word (w 37), .word (w 8)] fuel
    let finished ← get "composite fault resume" (first.resume 300000)
    match finished.observation with
    | .fault (.uninitializedLocal actual) state =>
      require (actual == missing) "composite first fault identity changed"
      cells state [(.word, some (.word (w 8))), (.word, some (.word (w 8))),
        (.product .word .word, some (.product (.word (w 37)) (.word (w 8)))), (.word, some (.word (w 8))), (.word, none)]
    | other => throw (IO.userError s!"composite arm fault expected: {reprStr other}")
  IO.println "composite pattern actual numeric sites / nested and repeated order / early and late miss / full ledger and store / heap fault resume GREEN"

end Tests.SourceCoreCompatiblePatternRuntime
