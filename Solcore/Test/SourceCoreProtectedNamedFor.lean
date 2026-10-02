import Solcore.SourceSemantics.CoreLowering.NamedImperativeForStatements
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Concrete consumers close named child/body meanings at the actual static
administrative context. Core-only fixtures combine source bindings, nested loop/transfer, scoped
control and bare/projected writes; ordered source cells, raw headers/duplicate keys,
first faults, retained writes and real resume are observed separately. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedFor
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open NamedImperativeForStatements
section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
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
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedImperativeForStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree errors

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem concrete_named_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedImperativeForStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree errors


include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Initializers and the nested body inhabit the same recursive grammar. The
head is followed by its concrete tail with no runtime endpoint premise. -/
theorem concrete_for_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {items post : List ForItemForm}
    {condition : ExpressionId} {statements rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {initialCode body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (initial : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.initializers items condition post statements) expected type initialCode)
    (initialErrors : GenericImperativeFor.Tree.Errors registry faults initial)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode rest) expected type body)
    (tailErrors : GenericImperativeFor.Tree.Errors registry faults tail) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      mode (id :: rest) expected type (LocalLoop.sequence type initialCode body) :=
  concrete_named_preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.forLoop found form initial tail)
    (.forLoop (found := found) (form := form) initialErrors tailErrors)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Completed initializers, finite iterations and post are inverted before the
tail. Break/return skip post and continue/fallthrough run it in source order. -/
theorem concrete_for_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {items post : List ForItemForm}
    {condition : ExpressionId} {statements rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {initialCode body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (initial : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.initializers items condition post statements) expected type initialCode)
    (initialErrors : GenericImperativeFor.Tree.Errors registry faults initial)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode rest) expected type body)
    (tailErrors : GenericImperativeFor.Tree.Errors registry faults tail) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      mode (id :: rest) expected type (LocalLoop.sequence type initialCode body) :=
  concrete_named_reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.forLoop found form initial tail)
    (.forLoop (found := found) (form := form) initialErrors tailErrors)

end Static

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function copied(value: Word) returns (Word) { let local = value; return local; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function bodyCallFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first = copied(0); true; raw[next(0)] += copied(99)) { raw[next(0)] += copied(5); index += copied(1); copied(bad(seed)); } return copied(99); }",
  "function nestedFor(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; let mask = copied(0); mask ~=; mask ~=; for (let outer = copied(0); less(outer, 2); let postLocal = next(outer), copied(postLocal), outer += copied(1)) { for (let inner: Word, inner = copied(0); less(inner, 3); let local = next(inner), copied(local), inner += copied(1)) { index += copied(1); if (less(inner, 1)) { continue; } raw[next(0)] += copied(2); if (less(outer, 1)) { break; } } } return copied(index + raw[next(0)]); }",
  "function forWhile(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let outer = copied(0); less(outer, 2); outer += copied(1)) { let inner = copied(0); while (less(inner, 2)) { inner += copied(1); index += copied(1); if (less(inner, 2)) { continue; } raw[next(0)] += copied(3); break; } } return copied(index + raw[next(0)]); }",
  "function whileFor(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; let outer = copied(0); while (less(outer, 2)) { outer += copied(1); for (let inner = copied(0); less(inner, 2); inner += copied(1)) { index += copied(1); raw[next(0)] += copied(2); if (less(outer, 2)) { continue; } break; } } return copied(index + raw[next(0)]); }",
  "function nestedReturn(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let outer = copied(0); true; let dead = bad(seed)) { while (true) { for (let inner = copied(0); true; let dead = bad(seed)) { raw[next(0)] += copied(4); index += copied(1); return copied(index + raw[next(0)]); } } } return copied(99); }",
  "function bodyBitNot(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let mask = copied(0), mask ~=, mask ~=; less(index, 2); index += copied(1), mask ~=, mask ~=) { mask ~=; mask ~=; raw[next(0)] += copied(2); } return copied(index + raw[next(0)]); }",
  "function bodyBitNotFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let outer = copied(0); true; raw[next(0)] += copied(99)) { let absent: Word; index += copied(1); raw[next(0)] += copied(3); absent ~=; } return copied(99); }",
  "function localsContinue(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first: Word, first = copied(0), let header = next(0), copied(header); less(first, 3); let absent: Word, absent = next(first), let retained = copied(absent), copied(retained), raw[next(0)] += copied(retained), first += copied(1)) { index += copied(1); continue; } return copied(index + raw[next(0)]); }",
  "function localsFallthrough(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first: Word, first = copied(0), let header = next(0), copied(header); less(first, 3); let absent: Word, absent = next(first), let retained = copied(absent), copied(retained), raw[next(0)] += copied(retained), first += copied(1)) { index += copied(1); } return copied(index + raw[next(0)]); }",
  "function postBreak(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first = copied(0); true; let never = bad(seed), raw[next(0)] += copied(99)) { raw[next(0)] += copied(1); break; } return copied(raw[next(0)]); }",
  "function postReturn(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first = copied(0); true; let never = bad(seed), raw[next(0)] += copied(99)) { raw[next(0)] += copied(2); return copied(raw[next(0)]); } return copied(99); }",
  "function bitNot(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let mask = copied(0); less(index, 2); mask ~=, mask ~=, index += next(0)) { raw[next(0)] += copied(1); } return copied(index + raw[next(0)]); }",
  "function postFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first = copied(0); true; let staged = copied(3), raw[next(0)] += copied(staged), let missing: Word, raw[next(0)] += copied(missing), index += copied(9)) { raw[next(0)] += copied(2); index += copied(1); continue; } return copied(99); }",
  "function initialFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (raw[next(0)] += copied(3), let ready = copied(0), let missing: Word, let dead = copied(missing); true; ) { raw[next(0)] += copied(99); } return copied(99); }",
  "function bitNotFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let missing: Word; true; missing ~=, raw[next(0)] += copied(99)) { raw[next(0)] += copied(2); index += copied(1); continue; } return copied(99); }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10, wordValue 7] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected named for resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name binderName : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected named for fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == binderName) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected named for exact fault binder missing")

private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected named for inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected named for missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected named for raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 3]? with
    | some cell => pure cell | none => throw (IO.userError "protected named for missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected named for writes changed {name}"
  match final.heap[initial.heap.length + 2]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected named for captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 1, initial.heap.length])
      s!"protected named for captured source aliases changed {name}"
  | other => throw (IO.userError s!"protected named for lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named for" content
    ["bodyCallFault", "nestedFor", "forWhile", "whileFor", "nestedReturn", "bodyBitNot", "bodyBitNotFault", "localsContinue", "localsFallthrough", "postBreak", "postReturn", "bitNot", "postFault", "initialFault", "bitNotFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let bodyGap ← gapBinder compiled "bad" "gap"
  let postGap ← gapBinder compiled "postFault" "missing"
  let initialGap ← gapBinder compiled "initialFault" "missing"
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated, counter) in [("nestedFor",21,16,5), ("forWhile",20,16,4), ("whileFor",19,16,3), ("nestedReturn",15,14,1), ("bodyBitNot",16,14,2), ("localsContinue",19,16,3), ("localsFallthrough",19,16,3), ("postBreak",11,11,0), ("postReturn",12,12,0), ("bitNot",14,12,2)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"protected named for result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected named for success {name}: {reprStr other}")
    for (name, exactGap, updated, counter) in [("bodyCallFault",bodyGap,15,1), ("postFault",postGap,15,1), ("initialFault",initialGap,13,0)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == exactGap) s!"protected named for exact fault {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected named for failure {name}: {reprStr other}")
    let bodyUnary ← finish compiled "bodyBitNotFault" fuel initial
    match bodyUnary with
    | .fault (.invalidUnaryOperand .bitNot none) final =>
      observe initial final "bodyBitNotFault" 13 1
      current := current ++ [reprStr bodyUnary]
    | other => throw (IO.userError s!"protected named for body unary fault: {reprStr other}")
    let unary ← finish compiled "bitNotFault" fuel initial
    match unary with
    | .fault (.invalidUnaryOperand .bitNot none) final =>
      observe initial final "bitNotFault" 12 1
      current := current ++ [reprStr unary]
    | other => throw (IO.userError s!"protected named for exact absent unary fault: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "protected named for resume changed observations"
  IO.println "protected named for: same statements/initializers grammar, nested for/while/break/continue/return, body/header/post unary, concrete named prefix/post, fresh marked locals, outer entry restoration, continue/fallthrough, break/return skip, seven-slot assignments/unary, exact first faults, raw duplicates/capture aliases and resume GREEN"

end Tests.SourceCoreProtectedNamedFor
