import Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentHeads
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! The same static assignment Head supports bare and projected paths under a
fixed budget. Concrete named Trees close child meaning; the reflected actual
continuation and installed caller entry stay together without source replay. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedAssignmentHeadBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CallableAncestryPairedLookup
abbrev ValuesContext := SourceCoreCompatibleValues.Context

/-! Concrete named argument/body trees close the only guarded RHS meaning
interface. Both empty and nonempty projection paths retain real installed
observations; no execution is added to a static assignment Head. -/
variable {checked : CallableAncestryPairedLookup.Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {source : TypedSource} {program : SourceSemantics.Program}
  {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context
    (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt) scope administrative ambient.definitions assignment operator rhs)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (runtimeViews : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))


include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem named_preserves (budget : Nat) {updated : Dynamic.Value} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ))  := by
  exact ProtectedAssignmentHeads.Head.preserves_prefix_bounded functions extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    faithful observations head environments heaps locals agrees actualTyped installed budget
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget) trace bounded

include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem named_fault (budget : Nat) (errors : head.ReachableErrors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before assignment.target operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical  := by
  exact ProtectedAssignmentHeads.Head.preserves_fault_reachable_bounded functions extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    faithful observations head environments heaps locals agrees actualTyped installed budget
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget) errors trace bounded next output

include extension faithful observations environments heaps locals agrees actualTyped installed valid runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem named_reflects (budget : Nat) (errors : head.ReachableErrors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    RecursiveNamedAssignmentHeadContracts.ResultAt size values.checked registry functions program context evidence source faults
      (NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix) scope (head.writtenContext actualContext)
      assignment.target operator rhs environment canonical actual before store mapping world (next.rename ξ) output value finalStore  := by
  exact ProtectedAssignmentHeads.Head.reflects_reachable_bounded functions extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    faithful observations head environments heaps locals agrees actualTyped installed budget
    (RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing) budget) runtimeViews errors completed bounded


/-- The bounded continuation keeps the actual caller entry and the seven
runtime-typed slots. The source witness receives no native-cost bound. -/
theorem continuation_below {size budget : Nat} {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (receipt : RecursiveNamedAssignmentHeadContracts.ResultAt size values.checked registry functions program context evidence source faults
      (NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix) scope (head.writtenContext actualContext)
      assignment.target operator rhs environment canonical actual before store mapping world (next.rename ξ) output value finalStore)
    (within : size ≤ budget) :
    (∃ sourceSize reason after, SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source
      environment before assignment.target operator rhs reason after) ∨
    (∃ sourceSize updated after slots written finalMap finalWorld remainingSize,
      SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after written canonical ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      remainingSize < budget ∧ EvaluationSize remainingSize (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  cases receipt with
  | fault trace _ _ _ _ _ _ _ _ => exact .inl ⟨_, _, _, trace⟩
  | success trace heaps _ _ _ _ count typed retained strict remaining =>
    exact .inr ⟨_, _, _, _, _, _, _, _, trace, heaps, retained, count, typed, Nat.lt_of_lt_of_le strict within, remaining⟩

private def content : String := String.intercalate "\n" [
  "function mark(value: Word) returns (Word) { let copied = value; return copied; }",
  "function fail(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function mixed(raw: mapping(Word => Word), seed: Word) returns (Word) { let root: Word; root = mark(seed); raw[mark(root)] += mark(5); root += mark(raw[root]); raw[mark(root)] = mark(11); return root; }",
  "function bareFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let root: Word; root += mark(seed); raw[mark(seed)] = mark(5); return root; }",
  "function keyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let root: Word; root = mark(seed); root += mark(2); raw[fail(root)] = mark(5); return root; }",
  "function rhsFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let root: Word; root = mark(seed); root += mark(2); raw[mark(root)] = fail(5); return root; }",
  "function unitResult(raw: mapping(Word => Word), seed: Word) { let root: Word; root = mark(seed); raw[mark(root)] = mark(5); root += mark(2); }"
]
private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (wordValue n))
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"bounded common assignment resume {name}" (first.resume 400000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"bounded common assignment prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue
    (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"bounded common assignment ordered cells {name}: {reprStr final.heap}"
private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "bounded common assignment gap binder" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "bounded common assignment exact fault binder missing")

/-- Cached execution interleaves both Head shapes and checks every ordered
source cell, raw header, duplicate entry and first-fault boundary after resume. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "bounded common assignment heads" content
    ["mixed", "bareFault", "keyFault", "rhsFault", "unitResult"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled
  let mapValue (entries : List (Nat × Nat)) : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    (entries.map fun (key, value) => (wordValue key, wordValue value))
  let raw := mapValue [(7,37),(7,91)]
  let changed := mapValue [(7,42),(7,91),(49,11)]
  let replaced := mapValue [(7,5),(7,91)]
  let rootCell (value : SourceTypedRuntime.Value) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.mapping .word .word, some value)
  let args := [raw, wordValue 7]
  for fuel in [0,43,211,400000] do
    match ← finish compiled "mixed" args fuel initial with
    | .done (.word value) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (value == Word.ofNatModulo 49) "bounded common assignment mixed result changed"
      cells initial final (rootCell changed :: ([7,49,7,7,7,7,5,5,42,42,49,49,11,11].map present)) "mixed"
    | other => throw (IO.userError s!"bounded common assignment mixed: {reprStr other}")
    match ← finish compiled "bareFault" args fuel initial with
    | .fault (.invalidAssignmentOperands operator left right) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (operator == .add && left == none && right == some .word) "bounded common assignment operand fault changed"
      cells initial final ([rootCell raw, present 7, (.word, none)] ++ [7,7].map present) "bareFault"
    | other => throw (IO.userError s!"bounded common assignment bare fault: {reprStr other}")
    for (name, numbers) in [("keyFault", [7,9,7,7,2,2,9]), ("rhsFault", [7,9,7,7,2,2,9,9,5])] do
      match ← finish compiled name args fuel initial with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) s!"bounded common assignment fault binder {name}"
        cells initial final (rootCell raw :: numbers.map present ++ [(.word, none)]) name
      | other => throw (IO.userError s!"bounded common assignment fault {name}: {reprStr other}")
    match ← finish compiled "unitResult" args fuel initial with
    | .done .unit final => cells initial final (rootCell replaced :: ([7,9,7,7,7,7,5,5,2,2].map present)) "unitResult"
    | other => throw (IO.userError s!"bounded common assignment Unit: {reprStr other}")
  IO.println "bounded common assignment heads: same bare/projected Head, original seven-slot continuation and Entry, independent source costs, interleaved updates/first faults, raw duplicates, Unit and resume GREEN"

end Tests.SourceCoreRecursiveNamedAssignmentHeadBounds
