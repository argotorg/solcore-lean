import Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuationMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Default-backed stopping and typed no-default stopping are tested separately.
The formal consumers retain actual statement identity, emitted suffixes and
original native child sizes. Runtime checks use the public compiler and resume
API, comparing every source cell. This foundation does not extend the existing
universal statement Tree with a no-default match case. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false

namespace Tests.SourceCoreReachableMatchContinuations
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering CoreProof
open ReachableMatchContinuations

section Formal
variable {source : TypedSource} {id : StatementId} {node : StatementNode}
  {resolution : MatchResolution} {rest fallback : List StatementId}
  {program : SourceSemantics.Program} {context finalContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}

theorem default_stopped_source (mode : Bool) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback) (branches : BranchStops source resolution)
    (trace : ScalarStatementViews.ListExecutes mode program context evidence source environment before
      (id :: rest) finalContext outcome after) :
    Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧
      Dynamic.TerminalControl outcome :=
  source_stopped_head mode unique (.of_source found form present branches) trace

theorem default_stopped_fault {reason : Dynamic.SemanticFault}
    (mode : Bool) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback) (branches : BranchStops source resolution)
    (trace : ScalarStatementViews.ListFaults mode program context evidence source environment before
      (id :: rest) finalContext reason after) :
    finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after :=
  source_stopped_fault mode unique (.of_source found form present branches) trace

theorem original_source_receipts {origin : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {type : Core.Ty} {suffix : Expr}
    (identity : GenericLexicalStatements.StatementSourceIdentity origin source)
    (stops : DefaultStopped origin id resolution)
    (issued : GenericLexicalStatements.IssuedSuffix origin scope mode rest type suffix) :
    DefaultStopped source id resolution ∧ GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix :=
  ⟨stops.transport identity, issued.transport identity⟩

theorem actual_match_issued {policy : SourceCoreLoops.Policy} {fuel : Nat} {scope : SourceCoreLoops.Scope}
    {type readType : Core.Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word} {code : Expr}
    (read : policy.readStatement source id = .ok (node, readType)) (form : node.form = .matchWith resolution)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope (id :: rest)
      type reasonAt mode escaped = .ok code) :
    ∃ callback matched suffix,
      policy.lowerMatch = some callback ∧
      callback policy.lowerExpression
        (fun _ childSource childScope statements resultType childReasonAt childSelfReason =>
          SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel childSource childScope statements
            resultType childReasonAt false childSelfReason)
        fuel source scope id resolution type reasonAt escaped = .ok matched ∧
      ReachableStatementContinuations.Issued policy fuel source scope rest type reasonAt mode escaped suffix ∧
      code = LocalLoop.sequence type matched suffix :=
  match_issued read form accepted

theorem nonunit_typed_match_stops {control : ControlContext} {facts : StatementFacts} {expected : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution) (typed : StatementHasType source control context id context facts)
    (complete : BodyCompletes expected (BodyFacts.singleton facts)) (nonunit : expected ≠ .unit) :
    MatchControlStopped source control context id node resolution facts :=
  .of_singleton_completes unique found form typed complete nonunit

theorem typed_match_terminal {control : ControlContext} {facts : StatementFacts}
    (stops : MatchControlStopped source control context id node resolution facts)
    (programWF : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (agrees : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (trace : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    Dynamic.TerminalControl outcome :=
  stops.terminal_at programWF runtime covers agrees heapTyped trace

theorem typed_sequence_head {control : ControlContext} {facts : StatementFacts}
    (mode : Bool) (unique : NodeOccurrencesUnique source)
    (stops : MatchControlStopped source control context id node resolution facts)
    (programWF : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (agrees : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (trace : ScalarStatementViews.ListExecutes mode program context evidence source environment before
      (id :: rest) finalContext outcome after) :
    Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧
      Dynamic.TerminalControl outcome :=
  source_typed_stopped_head mode unique stops programWF runtime covers agrees heapTyped trace

theorem typed_sequence_fault {control : ControlContext} {facts : StatementFacts} {reason : Dynamic.SemanticFault}
    (mode : Bool) (unique : NodeOccurrencesUnique source)
    (stops : MatchControlStopped source control context id node resolution facts)
    (programWF : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (agrees : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (trace : ScalarStatementViews.ListFaults mode program context evidence source environment before
      (id :: rest) finalContext reason after) :
    finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after :=
  source_typed_stopped_fault mode unique stops programWF runtime covers agrees heapTyped trace

theorem typed_no_default_excludes_no_branch {control : ControlContext} {scrutineeType : TypeSystem.Ty}
    {caseFacts : List BodyFacts} {value : Dynamic.Value}
    (typed : TypedNoDefault source control context resolution scrutineeType caseFacts)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (valueTyped : Dynamic.ValueHasType context before value scrutineeType)
    (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody .noBranch) : False :=
  typed.no_branch catalog valueTyped selected

theorem typed_selected_arm_stops {control : ControlContext} {scrutineeType : TypeSystem.Ty}
    {caseFacts : List BodyFacts} {value : Dynamic.Value} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)} {summary : ControlSummary}
    (typed : TypedNoDefault source control context resolution scrutineeType caseFacts)
    (merged : mergeBodyControls caseFacts none = some summary) (stops : summary.fallthrough = none)
    (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm body bindings)) :
    ∃ facts armContext bodyFinal,
      StatementsHaveType source control armContext body bodyFinal facts ∧ facts.control.fallthrough = none :=
  typed.arm_control merged stops selected

theorem no_default_not_universal (absent : resolution.defaultBody = none) :
    ¬ DefaultStopped source id resolution := by
  intro stops
  obtain ⟨fallback, present⟩ := stops.default_present
  rw [absent] at present
  cases present

theorem empty_default_not_stopped (present : resolution.defaultBody = some []) :
    ¬ BranchStops source resolution := by
  intro branches
  obtain ⟨_, _, _, stopped⟩ := branches.fallback [] present
  exact stopped.nonempty rfl

/-- Ordinary expression completion witnesses why BodyCompletes alone cannot
be used as a universal stopping cast. -/
theorem completion_can_fallthrough :
    let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := false, control := .ordinary .word}
    BodyCompletes .word (BodyFacts.singleton facts) ∧ facts.control.fallthrough ≠ none := by
  simp [BodyCompletes, BodyFacts.singleton, ControlSummary.ordinary]
end Formal

theorem concrete_native_return {size : Nat} {native : Core.Environment} {initial final : Store}
    {suffix : Expr} {result : Value} (value : Word)
    (original : EvaluationSize size native initial
      (LocalLoop.sequence .word (LocalLoop.returned (.word value)) suffix) result final) :
    result = LocalLoop.returnedValue (.word value) ∧ final = initial ∧
      ∃ child, child < size ∧ EvaluationSize child native initial
        (LocalLoop.returned (.word value)) result final := by
  have head : Evaluates native initial (LocalLoop.returned (.word value)) (LocalLoop.returnedValue (.word value)) initial :=
    LocalLoop.returned_evaluates .word
  obtain ⟨child, smaller, actual, _⟩ := native_issued_stopped rfl original (by
    intro child middle result _ actual
    obtain ⟨same, _⟩ := evaluation_deterministic actual.sound head
    exact same ▸ ReachableStatementContinuations.NativeTerminal.returned (.word value))
  obtain ⟨same, storeEq⟩ := evaluation_deterministic actual.sound head
  exact ⟨same, storeEq, child, smaller, actual⟩

theorem concrete_native_fault {size : Nat} {native : Core.Environment} {initial final : Store}
    {type : Core.Ty} {suffix : Expr} {result : Value} (reason : Word)
    (original : EvaluationSize size native initial
      (LocalLoop.sequence type (LanguageResult.failure (LocalLoop.controlType type) (.word reason)) suffix) result final) :
    result = .inLeft (LocalLoop.controlType type) (.word reason) ∧ final = initial ∧
      ∃ child, child < size ∧ EvaluationSize child native initial
        (LanguageResult.failure (LocalLoop.controlType type) (.word reason)) result final := by
  have head : Evaluates native initial (LanguageResult.failure (LocalLoop.controlType type) (.word reason))
      (.inLeft (LocalLoop.controlType type) (.word reason)) initial := .inLeft .word
  obtain ⟨child, smaller, actual, _⟩ := native_issued_stopped rfl original (by
    intro child middle result _ actual
    obtain ⟨same, _⟩ := evaluation_deterministic actual.sound head
    exact same ▸ ReachableStatementContinuations.NativeTerminal.failure reason)
  obtain ⟨same, storeEq⟩ := evaluation_deterministic actual.sound head
  exact ⟨same, storeEq, child, smaller, actual⟩

private def content : String := String.intercalate "\n" [
  "enum Choice { Left(Word), Right(Word) }",
  "function direct(seed: Word) returns (Word) { match (seed) { case 0 { return 43; } default { return 47; } } }",
  "function dead(seed: Word) returns (Word) { match (seed) { case 0 { if (true) { return 13; } else { return 17; } } default { { return 19; } } } let gap: Word; gap; }",
  "function pattern(seed: Word) returns (Word) { match ((seed, 11)) { case (0, x) { { return x; } let skipped = 99; } default { if (true) { return seed; } else { return 61; } let skipped = 99; } } return 99; }",
  "function same(seed: Word) returns (Word) { match (seed) { case 0 { return 23; } case 1 { return 23; } default { return 23; } } return 99; }",
  "function reachable(seed: Word) returns (Word) { match (seed) { case 0 {} default { return 31; } } return 29; }",
  "function failed(seed: Word) returns (Word) { match (seed) { case 0 { let prior = 37; let gap: Word; return gap; } default { return 41; } } let skipped = 99; return skipped; }",
  "function scrutineeFault() returns (Word) { let gap: Word; match (gap) { case 0 { return 1; } default { return 2; } } let skipped = 99; return skipped; }",
  "function nominalLeft(value: Choice) returns (Word) { match (value) { case .Left(x) { return x; } case .Right(y) { return y; } } }",
  "function nominalRight(value: Choice) returns (Word) { match (value) { case .Left(x) { return x; } case .Right(y) { return y; } } }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "reachable match continuations missing diagnostics")
    | some diagnostic => pure diagnostic.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "reachable match parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut defaultNodes := 0
  let mut noDefaultNodes := 0
  let mut nilSuffixes := 0
  let mut nonemptySuffixes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostics.base.find? named.signature.key with
      | none => throw (IO.userError "reachable match own diagnostics missing")
      | some own => pure own
    let source := CallableIndexedNamedGeneration.source named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
      (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none
    let policy : SourceCoreLoops.Policy := {
      actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
        own.assignments diagnostics named.signature.key lower with
      sourceCells := actual.expressions.sourceCells
      lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }
    let statements ← get "reachable match actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "reachable match actual body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let same ← get "reachable match actual compiler body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    require (body == same) "reachable match changed actual body code"
    for item in source.nodes do
      match item with
      | .statement node =>
        match node.form with
        | .matchWith resolution =>
          if resolution.defaultBody.isSome then defaultNodes := defaultNodes + 1
          else noDefaultNodes := noDefaultNodes + 1
          require (!(SourceCoreDataPlaces.declaredBinders source).any (fun binder => binder.id == resolution.hiddenScrutinee))
            "reachable match hidden scrutinee overlaps a source binder"
        | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
      let node ← match source.lookupStatement? id with
        | none => throw (IO.userError "reachable match root lookup missing")
        | some node => pure node
      match node.form with
      | .matchWith resolution =>
        let callback ← match policy.lowerMatch with
          | none => throw (IO.userError "reachable match callback missing")
          | some callback => pure callback
        let matched ← get "reachable match actual callback"
          (callback policy.lowerExpression
            (fun _ childSource childScope childStatements resultType childReasonAt escaped =>
              SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) childSource childScope childStatements
                resultType childReasonAt false escaped)
            (prepared.fuel - 1) source scope id resolution named.signature.resultType reasonAt own.table.escapedReason)
        let suffix ← get "reachable match complete emitted suffix"
          (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
            named.signature.resultType reasonAt true own.table.escapedReason)
        let whole ← get "reachable match whole flow"
          (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
            named.signature.resultType reasonAt true own.table.escapedReason)
        require (whole == LocalLoop.sequence named.signature.resultType matched suffix)
          "reachable match did not retain actual callback and full suffix"
        if rest.isEmpty then nilSuffixes := nilSuffixes + 1 else nonemptySuffixes := nonemptySuffixes + 1
      | _ => pure ()
    | [] => pure ()
  require (defaultNodes == 7 && noDefaultNodes == 2 && nilSuffixes == 3 && nonemptySuffixes == 5)
    s!"reachable match fixture coverage changed: {defaultNodes}/{noDefaultNodes}/{nilSuffixes}/{nonemptySuffixes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "reachable match public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "reachable match continuations" content
    ["direct", "dead", "pattern", "same", "reachable", "failed", "scrutineeFault", "nominalLeft", "nominalRight"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("direct", [w 0], w 43, [(.word, some (w 0)), (.word, some (w 0))]),
    ("direct", [w 1], w 47, [(.word, some (w 1)), (.word, some (w 1))]),
    ("dead", [w 0], w 13, [(.word, some (w 0)), (.word, some (w 0))]),
    ("dead", [w 1], w 19, [(.word, some (w 1)), (.word, some (w 1))]),
    ("pattern", [w 0], w 11, [(.word, some (w 0)), (.product .word .word, some (.product (w 0) (w 11))), (.word, some (w 11))]),
    ("pattern", [w 2], w 2, [(.word, some (w 2)), (.product .word .word, some (.product (w 2) (w 11)))]),
    ("same", [w 0], w 23, [(.word, some (w 0)), (.word, some (w 0))]),
    ("same", [w 1], w 23, [(.word, some (w 1)), (.word, some (w 1))]),
    ("same", [w 2], w 23, [(.word, some (w 2)), (.word, some (w 2))]),
    ("reachable", [w 0], w 29, [(.word, some (w 0)), (.word, some (w 0))]),
    ("reachable", [w 1], w 31, [(.word, some (w 1)), (.word, some (w 1))]),
    ("failed", [w 1], w 41, [(.word, some (w 1)), (.word, some (w 1))])]
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  for fuel in [0, 31, 300000] do
    for ((name, arguments, expected, expectedCells), baseline) in successes.zip baselines do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable match full resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected) s!"reachable match result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
          s!"reachable match full heap/dead suffix changed {name}"
      | other => throw (IO.userError s!"reachable match expected done {name}: {reprStr other}")
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("failed", [w 0], [(.word, some (w 0)), (.word, some (w 0)), (.word, some (w 37)), (.word, none)]),
    ("scrutineeFault", [], [(.word, none)])]
  for (name, arguments, expectedCells) in failures do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 31, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable match fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
          s!"reachable match first fault/dead suffix changed {name}"
      | other => throw (IO.userError s!"reachable match expected fault {name}: {reprStr other}")
  let choice ← match compiled.indexed.base.sourceProgram.signatures.dataTypes.find? (·.name == "Choice") with
    | none => throw (IO.userError "reachable match Choice missing")
    | some choice => pure choice
  let sourceType := TypeSystem.Ty.nominal choice.id []
  for (name, constructor, value) in [("nominalLeft", 0, 5), ("nominalRight", 1, 7)] do
    let metadata : DataConstructorInstantiation := ⟨⟨choice.id, constructor⟩, [], [.word], sourceType⟩
    let expected : SourceTypedRuntime.Value := .constructed metadata [w value]
    let baseline ← finish compiled name [expected] 300000 initial
    for fuel in [0, 31, 300000] do
      let observed ← finish compiled name [expected] fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable typed nominal resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr (w value)) s!"reachable typed nominal result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨sourceType, some expected⟩, ⟨sourceType, some expected⟩, ⟨.word, some (w value)⟩]))
          s!"reachable typed nominal full heap changed {name}"
      | other => throw (IO.userError s!"reachable typed nominal expected done {name}: {reprStr other}")
  IO.println "reachable match continuations: separate default/typed exhaustive boundaries, actual issued suffix, full source cells/fault/public resume GREEN"

end Tests.SourceCoreReachableMatchContinuations
