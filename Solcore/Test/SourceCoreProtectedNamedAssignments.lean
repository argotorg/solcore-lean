import Solcore.SourceSemantics.CoreLowering.NamedAssignmentStatementTail
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Concrete named expression trees supply all key/RHS/tail meanings. Real
installed/global/history guards remain entry facts. Cached checked-source
runs cover write-before-tail-fault, earlier key/RHS/default faults and resume. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedAssignments
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup TypedScopedStatements
open NamedAssignmentStatementTail
section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))


include extension faithful observations runtimeViews valid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Static named argument/body trees and the real installed entry close the
entire projected assignment and fixed-scope tail. All fault prefixes are
included; no runtime child/body meaning is an external premise. -/
theorem concrete_named_preserves {mode : Bool} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies compilation fuel source context solved reasonAt scope administrative mode statements expected type code)
    (errors : ProtectedAssignmentTails.Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (trace : Executes mode program context evidence source environment before statements finalContext outcome after) :
    finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical :=
  NamedAssignmentStatementTail.Tree.preserves functions extension faithful observations runtimeViews evidence valid unique owners
    uninitialized missing bodyUninitialized bodyMissing tree errors environments heaps locals agrees actualTyped installed trace

include extension faithful observations runtimeViews valid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Actual completed Core code supplies key, getter, RHS and tail outcomes in
source order. Installed closure payloads and frame history are retained from
the real administrative preservation receipts. -/
theorem concrete_named_reflects {mode : Bool} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies compilation fuel source context solved reasonAt scope administrative mode statements expected type code)
    (errors : ProtectedAssignmentTails.Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements context outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical :=
  NamedAssignmentStatementTail.Tree.reflects functions extension faithful observations runtimeViews evidence valid unique owners
    uninitialized missing bodyUninitialized bodyMissing tree errors environments heaps locals agrees actualTyped installed evaluated

end Static

private def content : String := String.intercalate "\n" [
  "function key(value: Word) returns (Word) { return value; }",
  "function first(value: Word) returns (Word) { let copied = value; return copied; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function compound(raw: mapping(Word => Word), seed: Word) returns (Word) { raw[key(seed)] += first(seed); first(seed); return raw[key(seed)]; }",
  "function keyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { raw[bad(seed)] += first(seed); return seed; }",
  "function rhsFault(raw: mapping(Word => Word), seed: Word) returns (Word) { raw[key(seed)] += bad(seed); return seed; }",
  "function tailFault(raw: mapping(Word => Word), seed: Word) returns (Word) { raw[key(seed)] += first(seed); return bad(seed); }",
  "function unitTail(raw: mapping(Word => Word), seed: Word) { raw[key(seed)] = first(seed); first(seed); }",
  "function getterFault(table: mapping(Word => mapping(Word => function(Word) returns (Word))), seed: Word, replacement: function(Word) returns (Word)) returns (Word) { table[key(seed)][first(seed)] = replacement; return seed; }"
]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected assignment resume {name}" (first.resume 300000)).observation

private def checkPrefix (initial final : SourceTypedRuntime.RuntimeState) : IO Unit :=
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    "protected assignment source prefix changed"

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  checkPrefix initial final
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"protected assignment ordered cells {name}: {reprStr final.heap}"

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "bad"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected assignment fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected assignment exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named assignments" content
    ["compound", "keyFault", "rhsFault", "tailFault", "unitTail", "getterFault"]
  let seven : SourceTypedRuntime.Value := .word (Word.ofNatModulo 7)
  let raw : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(seven, .word (Word.ofNatModulo 37)), (seven, .word (Word.ofNatModulo 91))]
  let updated : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(seven, .word (Word.ofNatModulo 44)), (seven, .word (Word.ofNatModulo 91))]
  let replaced : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(seven, seven), (seven, .word (Word.ofNatModulo 91))]
  let mapType : TypeSystem.Ty := .mapping .word .word
  let functionTy : TypeSystem.Ty := .function .word .word
  let innerTy : TypeSystem.Ty := .mapping (.comptime .word) (.comptime functionTy)
  let outer : SourceTypedRuntime.Value := .mapping (.comptime .word) innerTy []
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "key"
  let replacement : SourceTypedRuntime.Value := .global key []
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (Word.ofNatModulo 819))⟩]}
  let gap ← gapBinder compiled
  for fuel in [0, 43, 300000] do
    match ← finish compiled "compound" [raw, seven] fuel initial with
    | .done (.word actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == Word.ofNatModulo 44) "compound named result changed"
      cells initial final [(mapType, some updated), (.word, some seven), (.word, some seven),
        (.word, some seven), (.word, some seven), (.word, some seven), (.word, some seven), (.word, some seven)] "compound"
    | other => throw (IO.userError s!"protected assignment compound: {reprStr other}")
    match ← finish compiled "keyFault" [raw, seven] fuel initial with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "key fault lost source binder"
      cells initial final [(mapType, some raw), (.word, some seven), (.word, some seven), (.word, none)] "keyFault"
    | other => throw (IO.userError s!"protected assignment key fault: {reprStr other}")
    match ← finish compiled "rhsFault" [raw, seven] fuel initial with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "RHS fault lost source binder"
      cells initial final [(mapType, some raw), (.word, some seven), (.word, some seven), (.word, some seven), (.word, none)] "rhsFault"
    | other => throw (IO.userError s!"protected assignment RHS fault: {reprStr other}")
    match ← finish compiled "tailFault" [raw, seven] fuel initial with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "tail fault lost source binder"
      cells initial final [(mapType, some updated), (.word, some seven), (.word, some seven),
        (.word, some seven), (.word, some seven), (.word, some seven), (.word, none)] "tailFault"
    | other => throw (IO.userError s!"protected assignment written tail fault: {reprStr other}")
    match ← finish compiled "unitTail" [raw, seven] fuel initial with
    | .done .unit final =>
      cells initial final [(mapType, some replaced), (.word, some seven), (.word, some seven),
        (.word, some seven), (.word, some seven), (.word, some seven), (.word, some seven)] "unitTail"
    | other => throw (IO.userError s!"protected assignment Unit tail: {reprStr other}")
    match ← finish compiled "getterFault" [outer, seven, replacement] fuel initial with
    | .fault (.typeMismatch actual none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == .comptime functionTy) "getter fault raw default type changed"
      cells initial final [( .mapping .word (.mapping .word functionTy), some outer), (.word, some seven),
        (functionTy, some replacement), (.word, some seven), (.word, some seven), (.word, some seven)] "getterFault"
    | other => throw (IO.userError s!"protected assignment missing default: {reprStr other}")
  IO.println "protected named assignments: concrete guarded tail, all fault phases, ordered cells/raw metadata/duplicates, write-before-fault, default and resume GREEN"
end Tests.SourceCoreProtectedNamedAssignments
