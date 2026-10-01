import Solcore.SourceSemantics.CoreLowering.NamedLexicalStatements
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! The concrete guarded consumer has no runtime child/body meaning premise.
Actual checked Core fixtures retain lexical allocation order, restore outer
bindings, skip unselected/faulted tails and resume with the same source prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedLexical
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open NamedLexicalStatements
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
all runtime child obligations, including after source bindings and condition
slots. The actual protected entry is retained as a runtime boundary. -/
theorem concrete_named_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      context scope mode statements expected type code) :
    ProtectedLexicalStatements.Preserves functions program evidence
      (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedLexicalStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence unique owners uninitialized missing bodyUninitialized bodyMissing tree

include definitions registered extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem concrete_named_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      context scope mode statements expected type code) :
    ProtectedLexicalStatements.Reflects functions program evidence
      (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedLexicalStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence uninitialized missing bodyUninitialized bodyMissing tree

end Static

private def content : String := String.intercalate "\n" [
  "function first(value: Word) returns (Word) { let copied = value; return copied; }",
  "function predicate(value: Word) returns (Bool) { let copied = value; return copied > 0; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function nested(seed: Word) returns (Word) { let saved = first(seed); { let hidden = first(saved + 1); hidden; } if (predicate(saved)) { let chosen = first(saved + 2); chosen; } else { let unused = bad(saved); unused; } return first(saved + 3); }",
  "function shadow(seed: Word) returns (Word) { let saved = first(seed); { let saved = first(4); if (predicate(saved)) { let inside = first(saved + 1); inside; } } return first(saved); }",
  "function branches(seed: Word) returns (Word) { let saved = first(seed); if (predicate(saved)) { return first(9); } else { return first(5); } return bad(saved); }",
  "function initializerFault(seed: Word) returns (Word) { let saved = first(seed); let failed = bad(saved); return first(99); }",
  "function conditionFault(seed: Word) returns (Word) { let saved = first(seed); if (predicate(bad(saved))) { let unreachable = first(99); unreachable; } return first(100); }",
  "function discardedFault(seed: Word) returns (Word) { let saved = first(seed); { let retained = first(4); bad(saved); } return first(99); }",
  "function unitTail(seed: Word) { let saved = first(seed); let gap: Word; { let hidden = first(saved + 1); hidden; } if (predicate(saved)) { first(saved + 2); } else { bad(saved); } }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (wordValue n))

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected lexical resume {name}" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected lexical prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"protected lexical ordered cells {name}: {reprStr final.heap}"

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "bad"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected lexical fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected lexical exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named lexical" content
    ["nested", "shadow", "branches", "initializerFault", "conditionFault", "discardedFault", "unitTail"]
  let seven := wordValue 7
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled
  for fuel in [0, 43, 300000] do
    match ← finish compiled "nested" [seven] fuel initial with
    | .done actual final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue 10)) "protected nested result changed"
      cells initial final (([7, 7, 7, 7, 8, 8, 8, 7, 7, 9, 9, 9, 10, 10]).map present) "nested"
    | other => throw (IO.userError s!"protected nested: {reprStr other}")
    match ← finish compiled "shadow" [seven] fuel initial with
    | .done actual final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr seven) "protected outer scope was not restored"
      cells initial final (([7, 7, 7, 7, 4, 4, 4, 4, 4, 5, 5, 5, 7, 7]).map present) "shadow"
    | other => throw (IO.userError s!"protected shadow restore: {reprStr other}")
    for (seed, result) in [(7, 9), (0, 5)] do
      match ← finish compiled "branches" [wordValue seed] fuel initial with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) "protected branch result changed"
        cells initial final (([seed, seed, seed, seed, seed, seed, result, result]).map present) "branches"
      | other => throw (IO.userError s!"protected selected branch: {reprStr other}")
    for (name, observedCells) in [("initializerFault", [7, 7, 7, 7, 7]), ("conditionFault", [7, 7, 7, 7, 7]),
        ("discardedFault", [7, 7, 7, 7, 4, 4, 4, 7])] do
      match ← finish compiled name [seven] fuel initial with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) s!"protected {name} fault binder changed"
        cells initial final (observedCells.map present ++ [(.word, none)]) name
      | other => throw (IO.userError s!"protected lexical fault {name}: {reprStr other}")
    match ← finish compiled "unitTail" [seven] fuel initial with
    | .done .unit final =>
      cells initial final (([7, 7, 7, 7]).map present ++ [(.word, none)] ++ ([8, 8, 8, 7, 7, 9, 9]).map present) "unitTail"
    | other => throw (IO.userError s!"protected lexical Unit: {reprStr other}")
  IO.println "protected named lexical: concrete guards through real allocations, nested/selected scopes, outer restore, fault prefixes, Unit/fallthrough and resume GREEN"
end Tests.SourceCoreProtectedNamedLexical
