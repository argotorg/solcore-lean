import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementMeaning
import Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuationMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Test.SourceCoreReachableStatementContinuations
import Solcore.Test.SourceCoreReachableImperativeMatchStatements

/-! Default-backed match stopping composes with the existing block/if receipts.
The source table, typed case order and merged control summary remain explicit.
No-default stopping stays typed and pointwise. Native child grades and suffix
provenance are consumed by the existing helpers, never fields of a receipt. -/
set_option autoImplicit false
namespace Tests.SourceCoreTypedDefaultMatchContinuations
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open ReachableStatementContinuations CoreProof

section Formal
variable {source : TypedSource} {id : StatementId} {node : StatementNode}
  {resolution : MatchResolution} {fallback : List StatementId}
  {control : ControlContext} {context defaultFinal : SourceSemantics.Context}
  {scrutineeType : TypeSystem.Ty} {caseFacts : List BodyFacts} {defaultFacts : BodyFacts} {summary : ControlSummary}

theorem typed_default_stop
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback)
    (casesTyped : MatchCasesHaveType source control context scrutineeType resolution.cases caseFacts)
    (defaultTyped : StatementsHaveType source control context fallback defaultFinal defaultFacts)
    (merged : mergeBodyControls caseFacts (some defaultFacts) = some summary)
    (arms : ∀ arm fact, (arm, fact) ∈ resolution.cases.zip caseFacts → StoppingStatements source arm.body fact.control)
    (defaultStops : StoppingStatements source fallback defaultFacts.control) :
    StoppingStatement source id summary.eraseValue :=
  .matchDefault found form present casesTyped defaultTyped merged arms defaultStops

theorem concrete_returning_default
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback)
    (casesTyped : MatchCasesHaveType source control context scrutineeType resolution.cases caseFacts)
    (defaultTyped : StatementsHaveType source control context fallback defaultFinal defaultFacts)
    (merged : mergeBodyControls caseFacts (some defaultFacts) = some summary)
    (armReturns : ∀ arm fact, (arm, fact) ∈ resolution.cases.zip caseFacts →
      ∃ returned returnNode expression, arm.body = [returned] ∧ source.lookupStatement? returned = some returnNode ∧
        returnNode.form = .returnStmt (some expression) ∧ fact.control = .returned)
    {returned : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (defaultBody : fallback = [returned]) (defaultFound : source.lookupStatement? returned = some returnNode)
    (defaultForm : returnNode.form = .returnStmt (some expression)) (defaultControl : defaultFacts.control = .returned) :
    StoppingStatement source id summary.eraseValue := by
  apply typed_default_stop found form present casesTyped defaultTyped merged
  · intro arm fact member
    obtain ⟨returned, returnNode, expression, body, found, form, same⟩ := armReturns arm fact member
    rw [body, same]
    exact .stop (.returnValue found form)
  · rw [defaultBody, defaultControl]
    exact .stop (.returnValue defaultFound defaultForm)

theorem default_in_block {block : StatementId} {blockNode : StatementNode} {dead : List StatementId}
    (found : source.lookupStatement? block = some blockNode) (form : blockNode.form = .block (id :: dead))
    (matchStops : StoppingStatement source id summary) :
    StoppingStatement source block summary.eraseValue :=
  .block found form (.stop matchStops)

theorem default_in_if {conditional : StatementId} {conditionalNode : StatementNode} {condition : ExpressionId}
    {left right : List StatementId} {leftSummary rightSummary : ControlSummary}
    (found : source.lookupStatement? conditional = some conditionalNode)
    (form : conditionalNode.form = .ifThen condition left (some right))
    (leftStops : StoppingStatements source left leftSummary) (rightStops : StoppingStatements source right rightSummary) :
    StoppingStatement source conditional (.branches leftSummary rightSummary) :=
  .conditional found form leftStops rightStops

theorem origin_default_transport {origin : TypedSource} {statements : List StatementId}
    (identity : GenericLexicalStatements.StatementSourceIdentity origin source)
    (stops : StoppingStatements origin statements summary) (unique : NodeOccurrencesUnique source) :
    ListTerminates source statements :=
  GenericLexicalStatements.Stopped.list_terminates unique identity stops

theorem default_source_head {rest : List StatementId} {program : SourceSemantics.Program} {evidence : Dynamic.EvidenceEnvironment}
    {finalContext : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (mode : Bool) (unique : NodeOccurrencesUnique source) (stops : StoppingStatement source id summary)
    (trace : ScalarStatementViews.ListExecutes mode program context evidence source environment before
      (id :: rest) finalContext outcome after) :
    Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧ Dynamic.TerminalControl outcome :=
  source_stopped_head mode unique stops trace

theorem default_source_fault {rest : List StatementId} {program : SourceSemantics.Program} {evidence : Dynamic.EvidenceEnvironment}
    {finalContext : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (mode : Bool) (unique : NodeOccurrencesUnique source) (stops : StoppingStatement source id summary)
    (trace : ScalarStatementViews.ListFaults mode program context evidence source environment before
      (id :: rest) finalContext reason after) :
    finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after :=
  source_stopped_fault mode unique stops trace

theorem no_stopping_nil : ¬ StoppingStatements source [] summary := by
  intro stopped
  exact stopped.nonempty rfl
end Formal

abbrev no_default_universal := @Tests.SourceCoreReachableImperativeMatchStatements.no_default_match_has_no_stopping_head

abbrev original_native_return := @Tests.SourceCoreReachableStatementContinuations.concrete_return_stops
abbrev original_native_fault := @Tests.SourceCoreReachableStatementContinuations.concrete_fault_stops

private def content : String := String.intercalate "\n" [
  "enum Choice { Left(Word), Right(Word) }",
  "function nestedDefault(seed: Word) returns (Word) { { match (seed) { case 0 { return 19; } default { return 23; } } } let gap: Word; gap; }",
  "function nestedIf(seed: Word) returns (Word) { if (seed == 0) { match (seed) { case 0 { return 29; } default { return 31; } } } else { return 37; } let gap: Word; gap; }",
  "function deep(seed: Word) returns (Word) { { match (seed) { case 0 { return 47; } default { { match (seed + 1) { case 2 { return 41; } default { return 43; } } } } } } return 99; }",
  "function prefix(seed: Word) returns (Word) { let stamp = 53; { match (seed) { case 0 { let gap: Word; return gap; } default { return 59; } } } let dead = 99; return dead; }",
  "function unit(seed: Word) returns (Unit) { { match (seed) { case 0 { return; } default { return; } } } let gap: Word; gap; }",
  "function ordinary(seed: Word) returns (Word) { match (seed) { case 0 {} default { return 71; } } return 67; }",
  "function noDefault(value: Choice) returns (Word) { match (value) { case .Left(x) { return x; } case .Right(y) { return y; } } }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostic ← match prepared.base.diagnostics with
    | none => throw (IO.userError "typed default match diagnostics missing")
    | some diagnostic => pure diagnostic.program
  let diagnostic := match prepared.base.callableContext with
    | none => diagnostic | some native => {diagnostic with rootTable := native.diagnostics.rootTable}
  let parents ← get "typed default match contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut defaults := 0
  let mut noDefaults := 0
  let mut suffixes := 0
  let mut emptySuffixes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostic.base.find? named.signature.key with
      | none => throw (IO.userError "typed default match own diagnostics missing")
      | some own => pure own
    let source := CallableIndexedNamedGeneration.source named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostic.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostic
      (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none
    let policy : SourceCoreLoops.Policy := {
      actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
        own.assignments diagnostic named.signature.key lower with
      sourceCells := actual.expressions.sourceCells
      lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }
    let statements ← get "typed default match actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "typed default match actual body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let cached ← get "typed default match cached body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostic parents own statements)
    require (body == cached) "typed default match changed actual body"
    for item in source.nodes do
      match item with
      | .statement node =>
        match node.form with
        | .matchWith resolution =>
          if resolution.defaultBody.isSome then defaults := defaults + 1 else noDefaults := noDefaults + 1
        | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
      let node ← match source.lookupStatement? id with
        | none => throw (IO.userError "typed default match root lookup missing") | some node => pure node
      let rootSequence := match node.form with
        | .block _ | .ifThen _ _ (some _) | .matchWith _ => true
        | _ => false
      if rootSequence then
        let whole ← get "typed default match whole flow"
          (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
            named.signature.resultType reasonAt true own.table.escapedReason)
        let childFuel := prepared.fuel - 1
        let suffix ← get "typed default match issued suffix"
          (SourceCoreLoops.lowerFlowStatementsWithPolicy policy childFuel source scope rest
            named.signature.resultType reasonAt true own.table.escapedReason)
        let head ← match node.form with
          | .block inner =>
            get "typed default match inner block"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy childFuel source scope inner
                named.signature.resultType reasonAt false own.table.escapedReason)
          | .ifThen condition left (some right) => do
            let test ← get "typed default match condition" (lower childFuel source scope condition reasonAt)
            let leftCode ← get "typed default match left"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy childFuel source scope left
                named.signature.resultType reasonAt false own.table.escapedReason)
            let rightCode ← get "typed default match right"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy childFuel source scope right
                named.signature.resultType reasonAt false own.table.escapedReason)
            pure (LocalLoop.conditional named.signature.resultType test.expression leftCode rightCode)
          | .matchWith resolution => do
            let callback ← match policy.lowerMatch with
              | none => throw (IO.userError "typed default match callback missing") | some callback => pure callback
            get "typed default match callback"
              (callback policy.lowerExpression
                (fun _ childSource childScope childStatements resultType childReasonAt escaped =>
                  SourceCoreLoops.lowerFlowStatementsWithPolicy policy childFuel childSource childScope childStatements
                    resultType childReasonAt false escaped)
                childFuel source scope id resolution named.signature.resultType reasonAt own.table.escapedReason)
          | _ => pure whole
        match node.form with
        | .block _ | .ifThen _ _ (some _) | .matchWith _ =>
          require (whole == LocalLoop.sequence named.signature.resultType head suffix)
            "typed default match lost full original suffix code"
          if rest.isEmpty then emptySuffixes := emptySuffixes + 1 else suffixes := suffixes + 1
        | _ => pure ()
    | [] => pure ()
  require (defaults == 7 && noDefaults == 1 && suffixes == 5 && emptySuffixes == 1)
    s!"typed default match fixture coverage changed {defaults}/{noDefaults}/{suffixes}/{emptySuffixes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "typed default match public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "typed default match continuations" content
    ["nestedDefault", "nestedIf", "deep", "prefix", "unit", "ordinary", "noDefault"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 811)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("nestedDefault", [w 0], w 19, [(.word, some (w 0)), (.word, some (w 0))]),
    ("nestedDefault", [w 1], w 23, [(.word, some (w 1)), (.word, some (w 1))]),
    ("nestedIf", [w 0], w 29, [(.word, some (w 0)), (.word, some (w 0))]),
    ("nestedIf", [w 1], w 37, [(.word, some (w 1))]),
    ("deep", [w 0], w 47, [(.word, some (w 0)), (.word, some (w 0))]),
    ("deep", [w 1], w 41, [(.word, some (w 1)), (.word, some (w 1)), (.word, some (w 2))]),
    ("deep", [w 2], w 43, [(.word, some (w 2)), (.word, some (w 2)), (.word, some (w 3))]),
    ("prefix", [w 1], w 59, [(.word, some (w 1)), (.word, some (w 53)), (.word, some (w 1))]),
    ("unit", [w 0], .unit, [(.word, some (w 0)), (.word, some (w 0))]),
    ("unit", [w 1], .unit, [(.word, some (w 1)), (.word, some (w 1))]),
    ("ordinary", [w 0], w 67, [(.word, some (w 0)), (.word, some (w 0))]),
    ("ordinary", [w 1], w 71, [(.word, some (w 1)), (.word, some (w 1))])]
  for (name, arguments, expected, cells) in successes do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 31, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"typed default match resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected) s!"typed default match result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"typed default match full cells/dead suffix changed {name}"
      | other => throw (IO.userError s!"typed default match expected done {name}: {reprStr other}")
  let baseline ← finish compiled "prefix" [w 0] 300000 initial
  for fuel in [0, 31, 300000] do
    let observed ← finish compiled "prefix" [w 0] fuel initial
    require (reprStr observed == reprStr baseline) "typed default match first fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
      require (reprStr final.heap == reprStr (initial.heap ++ [⟨.word, some (w 0)⟩, ⟨.word, some (w 53)⟩, ⟨.word, some (w 0)⟩, ⟨.word, none⟩]))
        "typed default match first fault full cells changed"
    | other => throw (IO.userError s!"typed default match expected fault: {reprStr other}")
  let choice ← match compiled.indexed.base.sourceProgram.signatures.dataTypes.find? (·.name == "Choice") with
    | none => throw (IO.userError "typed default match nominal missing") | some choice => pure choice
  let sourceType := TypeSystem.Ty.nominal choice.id []
  for (index, payload) in [(0, 73), (1, 79)] do
    let metadata : DataConstructorInstantiation := ⟨⟨choice.id, index⟩, [], [.word], sourceType⟩
    let argument : SourceTypedRuntime.Value := .constructed metadata [w payload]
    let baseline ← finish compiled "noDefault" [argument] 300000 initial
    for fuel in [0, 31, 300000] do
      let observed ← finish compiled "noDefault" [argument] fuel initial
      require (reprStr observed == reprStr baseline) "typed no-default public resume changed"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr (w payload)) "typed no-default nominal result changed"
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨sourceType, some argument⟩, ⟨sourceType, some argument⟩, ⟨.word, some (w payload)⟩]))
          "typed no-default nominal full cells changed"
      | other => throw (IO.userError s!"typed no-default expected done: {reprStr other}")
  IO.println "typed default match continuations: nested block/if, actual issued suffix, typed no-default separate, full cells/fault/resume GREEN"

end Tests.SourceCoreTypedDefaultMatchContinuations
