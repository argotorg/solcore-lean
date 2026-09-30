import Solcore.Frontend.SourceCoreDataExpressions
import Solcore.Frontend.SourceCoreGeneralEntry

#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCoreDataExpressions

open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceCoreGeneralEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def w (value : Nat) : Word := Word.ofNatModulo value
private def present (value : Value) : Value := .inRight .unit value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
    "enum Row { First(Word, Bool), Other(Word, Bool) }",
    "function leaf(value: integer) returns (Tree<integer>) { return .Leaf(value); }",
    "function branch(left: Tree<integer>, right: Tree<integer>, marker: Word) returns (Tree<integer>) { return .Pair(left, right); }",
    "function proxyValue() returns (@Word) { return @Word; }",
    "function find(marker: Word, table: mapping(Word => Word), key: Word) returns (Word) { return table[key]; }",
    "function missing(table: mapping(Word => Tree<integer>), key: Word) returns (Tree<integer>) { return table[key]; }"
  ] }]
}

private def rootExpression (source : TypedSource) : Except SourceCoreBasic.Error ExpressionId := do
  let [.statement root] := source.roots | throw (.missingReturn .unit)
  let statement ← match source.lookupStatement? root with
    | some statement => pure statement
    | none => throw (.missingStatement root)
  match statement.form with
  | .returnStmt (some value) => pure value
  | _ => throw (.unsupportedStatement root statement.form)

/-- Test child policy: operands in these fixtures are ordinary local reads.
Injected effects below test the leaf's sequencing independently of any claim
about the supplied child policy's source semantics. -/
private def localChild (checked : Checked) : SourceCoreDataExpressions.ExpressionLowerer :=
  fun _ source scope id reasonAt => do
    let (node, type) ← SourceCoreDataExpressions.readExpression checked source id
    match node.form with
    | .reference _ (.local binder) =>
      let (index, slot) ← match SourceCoreLocalCell.lookup? scope binder with
        | some found => pure found
        | none => throw (.missingBinding binder)
      SourceCoreBasic.ensureType (.occurrence id.occurrence) type slot
      pure ⟨type, OptionalCell.read type (.var index) (reasonAt id)⟩
    | _ => throw (.unsupportedExpression id node.form)

private def lowerer (checked : Checked) (signatures : ProgramSignatures)
    (child : SourceCoreDataExpressions.ExpressionLowerer) : BodyLowerer checked SourceCoreBasic.Error :=
  fun fuel request => do
    let source := request.specialized.function.typedBody
    let root ← rootExpression source
    let table ← (SourceCoreFaultSites.prepare source request.sourceResultType).mapError
      (fun _ => SourceCoreBasic.Error.missingReturn request.result.type)
    let node ← match source.lookupExpression? root with
      | some node => pure node
      | none => throw (.missingExpression root)
    let missingReason := w 17
    let table := {table with additional := table.additional ++ [(missingReason, {
      error := .typeMismatch request.sourceResultType none,
      site := .occurrence root.occurrence, span := some node.span
    })]}
    let reasonAt := fun id => if id = root then missingReason else table.reasonAt id
    let lowered ← SourceCoreDataExpressions.lowerWithReasons fuel checked signatures child
      source (inputScope request.inputs) root reasonAt
    pure ⟨lowered.expression, table⟩

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"data expression function missing: {name}")

private def prepareEntry (program : CheckedProgram) (checked : Checked) (name : String)
    (child : SourceCoreDataExpressions.ExpressionLowerer) : IO (Entry checked) := do
  let selected ← request program name
  let plan ← match SourceSpecializationWorklist.run program [selected] 100 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"data expression worklist failed: {reprStr result}")
  match prepare program plan checked 100 (lowerer checked program.signatures child) with
  | .ok prepared => match prepared.entries with
      | [entry] => pure entry
      | _ => throw (IO.userError "data expression seed mismatch")
  | .error error => throw (IO.userError s!"data expression compile failed: {reprStr error}")

private def sourceFor (program : CheckedProgram) (name : String) : IO TypedSource := do
  let selected ← request program name
  match SourceSpecializationWorklist.run program [selected] 100 with
  | .ok (.complete plan) => match plan.specializations with
      | specialized :: _ => pure specialized.function.typedBody
      | _ => throw (IO.userError "source specialization missing")
  | _ => throw (IO.userError "source specialization failed")

private def modifyExpression (source : TypedSource) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode) : TypedSource :=
  { source with nodes := source.nodes.map fun
    | .expression node => .expression (if node.id = id then modify node else node)
    | node => node }

private def rejected {α : Type} : Except SourceCoreBasic.Error α → Bool
  | .error _ => true
  | .ok _ => false

private def execute {checked : Checked} (entry : Entry checked) (arguments : List Value) :
    IO LanguageResult.Observation :=
  match entry.run arguments 100000 with
  | .ok result => pure result.observation
  | .error error => throw (IO.userError s!"data expression input rejected: {reprStr error}")

private def effectChild (checked : Checked) : SourceCoreDataExpressions.ExpressionLowerer :=
  fun fuel source scope id reasonAt => do
    let lowered ← localChild checked fuel source scope id reasonAt
    let node ← match source.lookupExpression? id with
      | some node => pure node
      | none => throw (.missingExpression id)
    let digit := match node.form with
      | .reference "table" _ => 1
      | .reference "key" _ => 2
      | _ => 0
    -- `find` has marker/table/key, so marker is the third lexical reference.
    pure ⟨lowered.type, .letE
      (.storeCell (.var 2) (.inRight .unit (.binary .wordAdd
        (.binary .wordMul
          (.caseE (.loadCell (.var 2)) (.word Word.zero) (.var 0)) (.word (w 10))) (.word (w digit)))))
      (lowered.expression.weakenAt 0)⟩

private def keyFailureChild (checked : Checked) : SourceCoreDataExpressions.ExpressionLowerer :=
  fun fuel source scope id reasonAt => do
    let node ← match source.lookupExpression? id with
      | some node => pure node
      | none => throw (.missingExpression id)
    match node.form with
    | .reference "key" _ => pure ⟨.word, LanguageResult.failure .word (.word (w 21))⟩
    | _ => effectChild checked fuel source scope id reasonAt

private def firstFailureChild (checked : Checked) : SourceCoreDataExpressions.ExpressionLowerer :=
  fun fuel source scope id reasonAt => do
    let lowered ← localChild checked fuel source scope id reasonAt
    let node ← match source.lookupExpression? id with
      | some node => pure node
      | none => throw (.missingExpression id)
    match node.form with
    | .reference "left" _ => pure ⟨lowered.type, LanguageResult.failure lowered.type (.word (w 23))⟩
    | .reference "right" _ => pure ⟨lowered.type,
      .letE (.storeCell (.var 0) (.inRight .unit (.word (w 99)))) (lowered.expression.weakenAt 0)⟩
    | _ => pure lowered

example {checked : Checked} {context : Core.Context}
    (compiled : SourceCoreDataExpressions.Certified checked context) :
    HasType context compiled.lowered.expression (LanguageResult.resultType compiled.lowered.type)
      checked.catalog.definitions := compiled.typed

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"data expression source rejected: {reprStr errors}")
  let treeSignature ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some signature => pure signature
    | none => throw (IO.userError "Tree missing")
  let rowSignature ← match program.signatures.dataTypes.find? (·.name == "Row") with
    | some signature => pure signature
    | none => throw (IO.userError "Row missing")
  let treeType := TypeSystem.Ty.nominal treeSignature.id [.integer]
  let rowType := TypeSystem.Ty.nominal rowSignature.id []
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 100
      [treeType, rowType, .proxy .word, .mapping .word .word, .mapping .word treeType] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"data expression catalog rejected: {reprStr error}")
  let treeId := (checked.catalog.identity? treeType).getD ⟨999⟩
  let proxyId := (checked.catalog.identity? (.proxy .word)).getD ⟨999⟩
  let mapId := (checked.catalog.identity? (.mapping .word .word)).getD ⟨999⟩
  let treeMapId := (checked.catalog.identity? (.mapping .word treeType)).getD ⟨999⟩
  let leaf := fun value => Value.constructed ⟨treeId, 0⟩ (.integer value)
  let leafEntry ← prepareEntry program checked "leaf" (localChild checked)
  assertTrue ((← execute leafEntry [.integer (-7)]) == .succeeded (leaf (-7)) [present (.integer (-7))])
    "actual nominal constructor lowering failed"
  let branch ← prepareEntry program checked "branch" (localChild checked)
  let args := [leaf 1, leaf 2, .word Word.zero]
  assertTrue ((← execute branch args) == .succeeded (.constructed ⟨treeId, 1⟩ (.pair (leaf 1) (leaf 2))) (args.map present))
    "constructor payload packing changed"
  let failedBranch ← prepareEntry program checked "branch" (firstFailureChild checked)
  assertTrue ((← execute failedBranch args) == .failed (w 23) (args.map present))
    "failed first constructor argument did not skip later effects"
  let proxy ← prepareEntry program checked "proxyValue" (localChild checked)
  assertTrue ((← execute proxy []) == .succeeded (.constructed ⟨proxyId, 0⟩ .unit) []) "proxy lowering failed"

  let mapping := Value.constructed ⟨mapId, 1⟩
    (.pair (.pair (.word (w 5)) (.word (w 44))) (.constructed ⟨mapId, 0⟩ .unit))
  let find ← prepareEntry program checked "find" (effectChild checked)
  match ← execute find [.word Word.zero, mapping, .word (w 5)] with
  | .succeeded (.word value) store =>
    assertTrue (value == w 44 && store[0]? == some (present (.word (w 12)))) "mapping base/key evaluation order changed"
    assertTrue (store.length == 3 + checked.catalog.entries.length + 1) "mapping helper preparation count changed"
  | other => throw (IO.userError s!"mapping lookup failed: {reprStr other}")
  let failedFind ← prepareEntry program checked "find" (keyFailureChild checked)
  assertTrue ((← execute failedFind [.word Word.zero, mapping, .word (w 5)]) ==
      .failed (w 21) [present (.word (w 1)), present mapping, present (.word (w 5))])
    "key failure must preserve base effects and skip comparator/helper allocation"
  let layout : OrderedMapping.Layout := ⟨.word, .word, mapId⟩
  let lazyBody := Expr.letE (OptionalCell.allocate layout.type)
    (LocalSequence.pair layout.type layout.type
      (SourceCoreDataExpressions.readMapping layout (.var 0))
      (SourceCoreDataExpressions.readMapping layout (.var 0)))
  let lazyProgram : Program := ⟨LanguageResult.resultType (.product layout.type layout.type), lazyBody, checked.catalog.definitions⟩
  assertTrue lazyProgram.check "lazy mapping read failed typing"
  let empty := OrderedMapping.encode layout []
  assertTrue (lazyProgram.runStateful 1000 == .done (.inRight .word (.pair empty empty)) [present empty])
    "lazy mapping read must initialize once at the original location"
  let simpleFind ← prepareEntry program checked "find" (localChild checked)
  match ← execute simpleFind [.word Word.zero, mapping, .word (w 9)] with
  | .succeeded (.word value) _ => assertTrue (value == Word.zero) "absent Word mapping default changed"
  | _ => throw (IO.userError "absent Word mapping did not default")
  let missing ← prepareEntry program checked "missing" (localChild checked)
  match ← execute missing [.constructed ⟨treeMapId, 0⟩ .unit, .word (w 1)] with
  | .failed reason store =>
    assertTrue (reason == w 17 && store.length == 2 + checked.catalog.entries.length + 1)
      "absent nominal mapping did not preserve failure/helper state"
    assertTrue (missing.failureDiagnostic? reason |>.isSome) "caller missing-default diagnostic token was lost"
  | _ => throw (IO.userError "absent nominal mapping unexpectedly invented a value")
  let source ← sourceFor program "branch"
  let root ← match rootExpression source with
    | .ok root => pure root
    | .error error => throw (IO.userError s!"constructor root missing: {reprStr error}")
  let rootNode ← match source.lookupExpression? root with
    | some node => pure node
    | none => throw (IO.userError "constructor node missing")
  let .constructor instantiation arguments := rootNode.form | throw (IO.userError "constructor fixture form changed")
  let scope := inputScope branch.inputs
  let reasonAt := fun _ => Word.zero
  for malformed in [
      {instantiation with parameterSubstitution := []},
      {instantiation with payloadTypes := [.bool, .bool]},
      {instantiation with constructor := {instantiation.constructor with constructorIndex := 99}}] do
    let forged := modifyExpression source root fun node => {node with form := .constructor malformed arguments}
    assertTrue (rejected (SourceCoreDataExpressions.lowerWithReasons 100 checked program.signatures
      (localChild checked) forged scope root reasonAt)) "forged constructor metadata accepted"
  let short := modifyExpression source root fun node => {node with form := .constructor instantiation []}
  assertTrue (rejected (SourceCoreDataExpressions.lowerWithReasons 100 checked program.signatures
    (localChild checked) short scope root reasonAt)) "constructor arity mismatch accepted"
  assertTrue (rejected (SourceCoreDataExpressions.lowerWithReasons 0 checked program.signatures
    (localChild checked) source scope root reasonAt)) "data leaf compile budget ignored"

  -- Member is exercised as retained typed IR: the static source relation uses
  -- uniform positional fields across every registered constructor.
  let base ← match arguments with
    | base :: _ => pure base
    | _ => throw (IO.userError "member base occurrence missing")
  let baseNode ← match source.lookupExpression? base with
    | some node => pure node
    | none => throw (IO.userError "member base node missing")
  let .reference _ (.local binder) := baseNode.form | throw (IO.userError "member base local missing")
  let rowId := (checked.catalog.identity? rowType).getD ⟨999⟩
  let memberSource := modifyExpression (modifyExpression source base fun node => {node with type := rowType})
    root fun node => {node with type := .word, form := .member base "0" 0}
  let memberScope := [(binder, Core.Ty.namedData rowId)]
  let context := [OptionalCell.referenceType (.namedData rowId)]
  let certified ← match SourceCoreDataExpressions.lowerChecked 100 checked program.signatures
      (localChild checked) memberSource memberScope context root reasonAt with
    | .ok certified => pure certified
    | .error error => throw (IO.userError s!"uniform member rejected: {reprStr error}")
  for tag in [0, 1] do
    let value := Value.constructed ⟨rowId, tag⟩ (.pair (.word (w 76)) (.bool true))
    let store := [present value]
    let initial := State.initial certified.lowered.expression
      [.cellRef (OptionalCell.cellType (.namedData rowId)) 0] store
    assertTrue (runStateful 1000 initial == .done (.inRight .word (.word (w 76))) store)
      "member selection used the wrong constructor payload layout"
  for malformed in [
      modifyExpression memberSource root fun node => {node with form := .member base "2" 2},
      modifyExpression memberSource root fun node => {node with type := .bool},
      modifyExpression memberSource root fun node => {node with requirements := [⟨0⟩]}] do
    assertTrue (rejected (SourceCoreDataExpressions.lowerWithReasons 100 checked program.signatures
      (localChild checked) malformed memberScope root reasonAt)) "invalid member metadata accepted"
  IO.println "source Core data expression leaves GREEN"

end Tests.SourceCoreDataExpressions
