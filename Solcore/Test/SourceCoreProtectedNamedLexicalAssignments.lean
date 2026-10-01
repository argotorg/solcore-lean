import Solcore.SourceSemantics.CoreLowering.NamedLexicalAssignments
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Concrete consumers close named child/body meanings at the actual static
administrative context. Core-only fixtures combine source bindings, scoped
control and bare/projected writes; ordered source cells, raw headers/duplicate keys,
first faults, retained writes and real resume are observed separately. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedLexicalAssignments
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open NamedLexicalAssignments
section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
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

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The finite statement tree and concrete expression/body certificates close
all runtime child obligations, including after source bindings, condition slots and seven-slot writes. The actual protected entry is retained as a runtime boundary. -/
theorem concrete_named_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode statements expected type code) :
    ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedLexicalAssignments.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem concrete_named_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode statements expected type code) :
    ProtectedLexicalAssignments.ControlAt.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedLexicalAssignments.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- A real head, including an empty projection path, composes with the same
concrete recursive tail. No projected-path or runtime child premise is needed. -/
theorem concrete_named_assignment_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (head : ProtectedAssignmentHeads.Head values source context
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope administrative ambient.definitions assignment operator rhs)
    (errors : head.Errors registry faults)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode rest expected type body) :
    ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) :=
  concrete_named_preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.assignment found form head errors tail)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Whole completed code is reflected through a bare or projected head before
the recursive tail; its seven real slots and protected entry come from the head. -/
theorem concrete_named_assignment_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (head : ProtectedAssignmentHeads.Head values source context
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope administrative ambient.definitions assignment operator rhs)
    (errors : head.Errors registry faults)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode rest expected type body) :
    ProtectedLexicalAssignments.ControlAt.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) :=
  concrete_named_reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.assignment found form head errors tail)

end Static

private def content : String := String.intercalate "\n" [
  "function key(value: Word) returns (Word) { let copied = value; return copied; }",
  "function first(value: Word) returns (Word) { let copied = value; return copied; }",
  "function predicate(value: Word) returns (Bool) { let copied = value; return copied > 0; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function nested(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { let delta = first(saved + 1); raw[key(1)] += first(delta); } if (predicate(saved)) { let delta = first(saved + 2); raw[key(1)] += first(delta); } else { raw[key(bad(saved))] += first(99); } return first(raw[key(1)]); }",
  "function shadow(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { let saved = first(4); raw[key(1)] += first(saved); } if (predicate(saved)) { raw[key(1)] += first(2); } else { raw[key(1)] += first(5); } return first(saved); }",
  "function rhsFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { let delta = first(4); raw[key(1)] += first(delta); } if (predicate(saved)) { let delta = first(2); raw[key(1)] += bad(delta); } return first(99); }",
  "function keyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { let delta = first(4); raw[key(1)] += first(delta); } if (predicate(saved)) { raw[bad(saved)] += first(99); } return first(100); }",
  "function earlyReturn(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); if (predicate(saved)) { let delta = first(2); raw[key(1)] += first(delta); return first(raw[key(1)]); } else { return first(6); } return bad(99); }",
  "function tailFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { let delta = first(4); raw[key(1)] += first(delta); } if (predicate(saved)) { raw[key(1)] += first(2); } return bad(saved); }",
  "function unitTail(raw: mapping(Word => Word), seed: Word) { let saved = first(seed); let gap: Word; { let delta = first(4); raw[key(1)] = first(delta); } if (predicate(saved)) { raw[key(1)] += first(2); } }",
  "function getterFault(table: mapping(Word => mapping(Word => function(Word) returns (Word))), seed: Word, replacement: function(Word) returns (Word)) returns (Word) { { let chosen = first(seed); table[key(chosen)][first(chosen)] = replacement; } return seed; }",
  "function bareMixed(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: Word; saved = first(seed); { let delta = first(saved + 1); saved += first(delta); raw[key(1)] += first(saved); } if (predicate(saved)) { saved = first(saved + 2); raw[key(1)] += first(saved); } else { saved = first(99); } return first(saved + raw[key(1)]); }",
  "function bareBranch(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { let saved: Word; saved = first(4); raw[key(1)] += first(saved); } if (predicate(saved)) { saved += first(2); } else { saved = first(5); } return first(saved); }",
  "function bareOperandFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: Word; { raw[key(1)] += first(4); saved += first(seed); } return first(99); }",
  "function bareRhsFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { saved += first(4); raw[key(1)] += first(saved); } if (predicate(saved)) { saved = bad(saved); } return first(99); }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (wordValue n))
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected lexical assignment resume {name}" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected lexical assignment prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"protected lexical assignment ordered cells {name}: {reprStr final.heap}"

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "bad"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected lexical assignment fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected lexical assignment exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named lexical assignments" content
    ["nested", "shadow", "rhsFault", "keyFault", "earlyReturn", "tailFault", "unitTail", "getterFault",
      "bareMixed", "bareBranch", "bareOperandFault", "bareRhsFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled
  let mapType : TypeSystem.Ty := .mapping .word .word
  for fuel in [0, 43, 300000] do
    match ← finish compiled "nested" [table 10, wordValue 3] fuel initial with
    | .done actual final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue 19)) "nested assignment result changed"
      cells initial final ((mapType, some (table 19)) :: ([3,3,3,3,4,4,4,1,1,4,4,3,3,5,5,5,1,1,5,5,1,1,19,19]).map present) "nested"
    | other => throw (IO.userError s!"protected nested assignment: {reprStr other}")
    for (seed, updated) in [(3,16), (0,19)] do
      match ← finish compiled "shadow" [table 10, wordValue seed] fuel initial with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue seed)) "assignment inner binding escaped"
        let chosen := if seed = 0 then 5 else 2
        cells initial final ((mapType, some (table updated)) ::
          ([seed,seed,seed,seed,4,4,4,1,1,4,4,seed,seed,1,1,chosen,chosen,seed,seed]).map present) "shadow"
      | other => throw (IO.userError s!"protected assignment restored branch: {reprStr other}")
    for (name, numbers, written) in [
        ("rhsFault", [3,3,3,3,4,4,4,1,1,4,4,3,3,2,2,2,1,1,2],14),
        ("keyFault", [3,3,3,3,4,4,4,1,1,4,4,3,3,3],14),
        ("tailFault", [3,3,3,3,4,4,4,1,1,4,4,3,3,1,1,2,2,3],16)] do
      match ← finish compiled name [table 10, wordValue 3] fuel initial with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) s!"assignment fault binder changed {name}"
        cells initial final ((mapType, some (table written)) :: (numbers.map present ++ [(.word,none)])) name
      | other => throw (IO.userError s!"protected lexical assignment fault {name}: {reprStr other}")
    for (seed, result, updated, numbers) in [
        (3,12,12,[3,3,3,3,3,3,2,2,2,1,1,2,2,1,1,12,12]),
        (0,6,10,[0,0,0,0,0,0,6,6])] do
      match ← finish compiled "earlyReturn" [table 10,wordValue seed] fuel initial with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) "assignment early return changed"
        cells initial final ((mapType,some (table updated)) :: numbers.map present) "earlyReturn"
      | other => throw (IO.userError s!"protected assignment early return: {reprStr other}")
    match ← finish compiled "unitTail" [table 10,wordValue 3] fuel initial with
    | .done .unit final =>
      cells initial final ((mapType,some (table 6)) ::
        (([3,3,3,3]).map present ++ [(.word,none)] ++ ([4,4,4,1,1,4,4,3,3,1,1,2,2]).map present)) "unitTail"
    | other => throw (IO.userError s!"protected lexical assignment Unit: {reprStr other}")
    let functionTy : TypeSystem.Ty := .function .word .word
    let outer : SourceTypedRuntime.Value := .mapping (.comptime .word) (.mapping (.comptime .word) (.comptime functionTy)) []
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "first"
    let replacement : SourceTypedRuntime.Value := .global key []
    match ← finish compiled "getterFault" [outer,wordValue 3,replacement] fuel initial with
    | .fault (.typeMismatch actual none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == .comptime functionTy) "nested default raw header changed"
      cells initial final [( .mapping .word (.mapping .word functionTy),some outer), present 3,
        (functionTy,some replacement), present 3,present 3,present 3,present 3,present 3,present 3,present 3] "getterFault"
    | other => throw (IO.userError s!"protected lexical assignment default: {reprStr other}")
    match ← finish compiled "bareMixed" [table 10, wordValue 3] fuel initial with
    | .done actual final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue 35)) "mixed bare/projected result changed"
      cells initial final ((mapType,some (table 26)) :: present 3 :: present 9 ::
        ([3,3,4,4,4,4,4,1,1,7,7,7,7,9,9,1,1,9,9,1,1,35,35]).map present) "bareMixed"
    | other => throw (IO.userError s!"protected mixed bare/projected: {reprStr other}")
    for (seed, chosen) in [(3,2), (0,5)] do
      match ← finish compiled "bareBranch" [table 10,wordValue seed] fuel initial with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue 5)) "bare scoped branch result changed"
        cells initial final ((mapType,some (table 14)) ::
          ([seed,seed,seed,5,4,4,4,1,1,4,4,seed,seed,chosen,chosen,5,5]).map present) "bareBranch"
      | other => throw (IO.userError s!"protected bare restored branch: {reprStr other}")
    match ← finish compiled "bareOperandFault" [table 10,wordValue 3] fuel initial with
    | .fault (.invalidAssignmentOperands .add none (some .word)) final =>
      cells initial final ((mapType,some (table 14)) :: present 3 :: (.word,none) ::
        ([1,1,4,4,3,3]).map present) "bareOperandFault"
    | other => throw (IO.userError s!"protected bare fault after projected write: {reprStr other}")
    match ← finish compiled "bareRhsFault" [table 10,wordValue 3] fuel initial with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "bare RHS exact fault binder changed"
      cells initial final ((mapType,some (table 17)) ::
        (([3,3,3,7,4,4,1,1,7,7,7,7,7]).map present ++ [(.word,none)])) "bareRhsFault"
    | other => throw (IO.userError s!"protected bare RHS after retained writes: {reprStr other}")
  IO.println "protected named lexical assignments: recursive bindings/scopes/bare and projected writes, exact ordered cells/raw metadata/duplicates, first faults/retained writes, guarded consumers and resume GREEN"
end Tests.SourceCoreProtectedNamedLexicalAssignments
