import Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Actual validator receipts close numeric leaves in a complete runtime ledger.
An unrelated uncovered assumption is retained. The executable audits below use
actual checked numeric nodes and explicitly marked mutations of their ledgers;
mutated ledgers are not claimed to come from a well-formed checked program. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreNumericLiteralEvidenceReceipts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreElaboration NumericLiteralEvidenceReceipts

section Accepted
variable {solved : List SolvedRequirement} {node : ExpressionNode}
  {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
  {context : SourceSemantics.Context}
  (sameLedger : context.solvedRequirements = solved) (runtime : RuntimeRequirementLedgerValid context)
  (form : node.form = .integerLiteral literal resolution)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
  (environment : Dynamic.Environment) (heap : Dynamic.Heap)

include sameLedger runtime form

/-- Concrete primitive source and native semantics use no ordinary ledger or
covering-dictionary callback. Arbitrary native environments and stores persist. -/
theorem word_leaf {validated : WordIntegerLiteral}
    (accepted : validateWordIntegerLiteral solved node literal resolution = .ok validated)
    (actual : Core.Environment) (store : Core.Store) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions (.word validated.value) heap ∧
    Evaluates actual store (.inRight .word (.word validated.value))
      (.inRight .word (.word validated.value)) store :=
  ⟨word_raw accepted form sameLedger runtime program evidence source environment heap, .inRight .word⟩

/-- Reflection inverts the completed native leaf and constructs the independent
source result. It does not consume preservation or prior source execution. -/
theorem word_reflects {validated : WordIntegerLiteral}
    (accepted : validateWordIntegerLiteral solved node literal resolution = .ok validated)
    {actual : Core.Environment} {store after : Core.Store} {result : Core.Value}
    (completed : Evaluates actual store (.inRight .word (.word validated.value)) result after) :
    result = .inRight .word (.word validated.value) ∧ after = store ∧
    Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions (.word validated.value) heap := by
  cases completed with
  | inRight evaluated =>
    cases evaluated
    exact ⟨rfl, rfl, word_raw accepted form sameLedger runtime program evidence source environment heap⟩

theorem integer_leaf {validated : NativeIntegerLiteral}
    (accepted : validateNativeIntegerLiteral solved node literal resolution = .ok validated)
    (actual : Core.Environment) (store : Core.Store) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions (.integer validated.value) heap ∧
    Evaluates actual store (.inRight .word (.integer validated.value))
      (.inRight .word (.integer validated.value)) store :=
  ⟨integer_raw accepted form sameLedger runtime program evidence source environment heap, .inRight .integer⟩

theorem integer_reflects {validated : NativeIntegerLiteral}
    (accepted : validateNativeIntegerLiteral solved node literal resolution = .ok validated)
    {actual : Core.Environment} {store after : Core.Store} {result : Core.Value}
    (completed : Evaluates actual store (.inRight .word (.integer validated.value)) result after) :
    result = .inRight .word (.integer validated.value) ∧ after = store ∧
    Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions (.integer validated.value) heap := by
  cases completed with
  | inRight evaluated =>
    cases evaluated
    exact ⟨rfl, rfl, integer_raw accepted form sameLedger runtime program evidence source environment heap⟩

omit form in
/-- Empty-premise evidence does not inspect the ambient dictionary, even when
it contains no entry for another assumption in the complete ledger. -/
theorem arbitrary_dictionary {validated : WordIntegerLiteral}
    (accepted : validateWordIntegerLiteral solved node literal resolution = .ok validated) :
    Dynamic.RequirementProducesEvidence context evidence resolution.requirement resolution.predicate
      (.implementation resolution.predicate (.builtin .intWord) []) ∧
    ¬ Dynamic.RequirementUnavailable context evidence resolution.requirement :=
  ⟨(word accepted).produces sameLedger runtime evidence, (word accepted).safe sameLedger runtime evidence⟩
end Accepted

/-- The complete runtime ledger is computed from the actual initial source
frame, even when local template IDs are nonempty. The validator chooses the
one primitive implementation row; no prior Header.valid is supplied. -/
theorem frame_word_leaf {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {solved : List SolvedRequirement}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program)
    (sameLedger : function.context.solvedRequirements = solved)
    {node : ExpressionNode} {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : WordIntegerLiteral}
    (accepted : validateWordIntegerLiteral solved node literal resolution = .ok validated)
    (form : node.form = .integerLiteral literal resolution)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionFormEvaluates program context function.evidence function.source environment heap
      node.form node.requirements node.coercions (.word validated.value) heap :=
  word_raw accepted form ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped)
    program function.evidence function.source environment heap

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def selected : SolvedRequirement := ⟨⟨0⟩, goal, .implementation (.byImpl goal (.builtin .intWord) [])⟩
private def assumed : SolvedRequirement := ⟨⟨1⟩, goal, .assumption goal⟩
private def rows : List SolvedRequirement := [assumed, selected]
private def context : SourceSemantics.Context := (Context.ofSignatures signatures).withSolvedRequirements rows
private def resolution : IntegerLiteralResolution := ⟨37, .word, ⟨0⟩⟩
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"numeric_receipts", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def node : ExpressionNode := {
  id := ⟨⟨owner, 0⟩⟩, span := ⟨⟨.main, "numeric_receipts.solc"⟩, 0, 2⟩,
  type := .word, form := .integerLiteral (.decimal "37") resolution, requirements := [⟨0⟩] }

private theorem runtime : RuntimeRequirementLedgerValid context := by
  refine ⟨?_, ?_⟩
  · change ([⟨1⟩, ⟨0⟩] : List RequirementId).Nodup
    decide
  all_goals skip
  intro row evidence member isImpl
  simp only [context, Context.withSolvedRequirements, rows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · cases isImpl
  · refine .intro (.intro (.implementation (.byImpl .nil)) ?_)
    apply EvidenceValid.implementation (rule := ProgramSignatures.builtinIntWordRule)
    · simp [context, Context.withSolvedRequirements, Context.ofSignatures, signatures,
        ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]
    · rfl
    · exact .intro ⟨[], []⟩ ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩ rfl rfl
    · exact .nil

/-- A concrete successful validator leaf coexists with an uncovered assumption
row. The complete ledger is runtime-valid but is not ordinary-valid. -/
theorem uncovered_unused_row :
    validateWordIntegerLiteral rows node (.decimal "37") resolution = .ok ⟨Word.ofNatModulo 37, [⟨0⟩]⟩ ∧
    RuntimeRequirementLedgerValid context ∧ ¬ RequirementLedgerWellFormed context ∧
    Dynamic.RequirementProducesEvidence context [] resolution.requirement resolution.predicate
      (.implementation resolution.predicate (.builtin .intWord) []) := by
  have accepted : validateWordIntegerLiteral rows node (.decimal "37") resolution = .ok ⟨Word.ofNatModulo 37, [⟨0⟩]⟩ := by rfl
  refine ⟨accepted, runtime, ?_, (word accepted).produces rfl runtime []⟩
  intro ordinary
  have valid := ordinary.entriesValid assumed (by simp [context, Context.withSolvedRequirements, rows])
  cases valid with
  | intro retained =>
    cases retained with
    | intro represents valid =>
      cases represents
      cases valid with
      | assumption member => cases member

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def huge : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639937
private def content : String := String.intercalate "\n" [
  "function wordRoot() returns (Word) { let first = 0x25; return first; }",
  s!"function wrapRoot() returns (Word) \{ return {huge}; }",
  s!"function integerRoot() returns (integer) \{ let full = {huge}; return full; }",
  "function faultRoot() returns (Word) { let prior = 41; let missing: Word; return missing + 43; }"
]

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut wordCount := 0
  let mut integerCount := 0
  for named in compiled.indexed.base.functions do
    let actual ← get "numeric actual specialization"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (actual == named.specialized) "numeric full selected record changed"
    let source := actual.function.typedBody
    let ledger := actual.function.solvedRequirements
    for retained in source.nodes do
      match retained with
      | .expression node => match node.form with
        | .integerLiteral literal resolution =>
          let selected ← match ledger.filter (·.id == resolution.requirement) with
            | [selected] => pure selected
            | _ => throw (IO.userError "numeric real row is not singleton")
          let implementation : ProgramImplId := if resolution.targetType == .integer then .builtin .intInteger else .builtin .intWord
          let raw : TypedTraitResolution.Evidence := .byImpl resolution.predicate implementation []
          require (selected.predicate == resolution.predicate && selected.evidence == .implementation raw)
            "numeric selected full evidence changed"
          let validate (rows : List SolvedRequirement) : Except SourceCoreElaboration.Error (Core.Value × List RequirementId) :=
            if node.type == .integer then
              (validateNativeIntegerLiteral rows node literal resolution).map fun value => (.integer value.value, value.consumedRequirements)
            else
              (validateWordIntegerLiteral rows node literal resolution).map fun value => (.word value.value, value.consumedRequirements)
          let checked ← get "numeric actual validator" (validate ledger)
          let expected := if node.type == .integer then Core.Value.integer (Int.ofNat resolution.rawValue)
            else .word (Word.ofNatModulo resolution.rawValue)
          require (checked.1 == expected && checked.2 == [resolution.requirement]) "numeric value/consumed order changed"
          let fresh : RequirementId := ⟨(ledger.map (·.id.index)).foldl max 0 + 1⟩
          let assumption : SolvedRequirement := ⟨fresh, resolution.predicate, .assumption resolution.predicate⟩
          -- These are explicit ledger mutations, not checker-produced ledgers.
          let variants := [ledger, assumption :: ledger, ledger ++ [assumption],
            (ledger.filter (·.id != resolution.requirement)) ++ [selected, assumption]]
          for rows in variants do
            let observed ← get "numeric unrelated assumption" (validate rows)
            require (observed == checked) "unrelated retained row changed selected numeric result"
            let context : SourceCoreFunctions.Context := {
              plan := compiled.indexed.base.plan, owner := named.signature.key,
              globals := compiled.indexed.base.globals, administrativePrefix := 1,
              solvedRequirements := rows, internalReason := Word.zero }
            let lowered ← get "numeric actual primitive compiler"
              (SourceCoreFunctions.lowerExpressionWithReasons
                (fun _ _ _ _ _ _ _ _ _ => .error (.unsupportedExpression node.id node.form))
                20 context source [] node.id (fun _ => Word.zero))
            let expectedCode : Expr := match checked.1 with
              | .word value => .inRight .word (.word value)
              | .integer value => .inRight .word (.integer value)
              | _ => .unit
            require (lowered.expression == expectedCode) "actual numeric emission differs from validator payload"
            let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
              .letE (.newCell (.function .unit .unit) (.lambda .unit .unit .unit)) (lowered.expression.weakenAt 0),
              compiled.compatible.checked.catalog.definitions⟩
            require native.check "numeric emitted code failed Core typing"
            for fuel in [0, 1, 5, 1000] do
              let completed := match native.runStateful fuel with
                | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
                | other => other
              match completed with
              | .done value store =>
                require (value == .inRight .word checked.1 && store == [.closure .unit .unit .unit []])
                  "numeric primitive changed result/administrative store on resume"
              | other => throw (IO.userError s!"numeric primitive did not finish: {reprStr other}")
          let wrongImpl : ProgramImplId := if implementation == .builtin .intWord then .builtin .intInteger else .builtin .intWord
          let malformed := [
            ledger.filter (·.id != resolution.requirement), ledger ++ [selected],
            ledger.map fun row => if row.id == resolution.requirement then {row with evidence := .assumption row.predicate} else row,
            ledger.map fun row => if row.id == resolution.requirement then {row with evidence := .implementation (.byImpl resolution.predicate wrongImpl [])} else row,
            ledger.map fun row => if row.id == resolution.requirement then {row with evidence := .implementation (.byImpl resolution.predicate implementation [raw])} else row,
            ledger.map fun row => if row.id == resolution.requirement then {row with predicate := ProgramSignatures.builtinIntPredicate .bool} else row,
            ledger.map fun row => if row.id == resolution.requirement then {row with evidence := .implementation (.byImpl (ProgramSignatures.builtinIntPredicate .bool) implementation [])} else row]
          for rows in malformed do
            require (validate rows |>.toOption.isNone) "numeric malformed selected receipt was accepted"
          if node.type == .integer then integerCount := integerCount + 1 else wordCount := wordCount + 1
        | _ => pure ()
      | _ => pure ()
  require (wordCount ≥ 4 && integerCount ≥ 1) "numeric audit missed Word/Integer or fault suffix literal"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"numeric full source heap changed: {reprStr state.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "numeric evidence receipts" content
    ["wordRoot", "wrapRoot", "integerRoot", "faultRoot"]
  inspect compiled
  let missing ← match (compiled.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "numeric missing binder identity lost")
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("wordRoot", .word (Word.ofNatModulo 37), [(.word, some (.word (Word.ofNatModulo 37)))]),
    ("wrapRoot", .word (Word.ofNatModulo 1), []),
    ("integerRoot", .integer (Int.ofNat huge), [(.integer, some (.integer (Int.ofNat huge)))])]
  for fuel in [0, 37, 151, 300000] do
    for (name, expected, heap) in successes do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel
      let finished ← get "numeric public resume" (started.resume 300000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr expected) "numeric public completed value changed"
        cells state heap
      | other => throw (IO.userError s!"numeric public success expected: {reprStr other}")
    let started ← SourceCoreUnifiedCorpusSupport.execute compiled "faultRoot" [] fuel
    let finished ← get "numeric public fault resume" (started.resume 300000)
    match finished.observation with
    | .fault (.uninitializedLocal actual) state =>
      require (actual == missing) "numeric first fault identity changed"
      cells state [(.word, some (.word (Word.ofNatModulo 41))), (.word, none)]
    | other => throw (IO.userError s!"numeric first fault expected: {reprStr other}")
  IO.println "numeric selected implementation / retained unrelated rows / exact emission / full heaps / resume GREEN"

end Tests.SourceCoreNumericLiteralEvidenceReceipts
