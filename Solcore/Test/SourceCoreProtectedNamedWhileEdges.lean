import Solcore.SourceSemantics.CoreLowering.NamedWhileEdges
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Concrete protected loop-edge consumers and Core-only regressions.
Conditions and lexical bodies call real named code while mutable source cells,
raw duplicate mappings and a pre-existing captured closure remain observable.
Whole while iteration/finish meaning is a later unit. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedWhileEdges
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open TypedScopedStatements (Executes)
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

open NamedWhileEdges
variable {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {type : Ty} {conditionCode bodyCode : Expr} {selfReason : Word}
  {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

include extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- All condition child/body meaning follows from concrete accepted named Trees. -/
theorem concrete_condition_preserves
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason finalMap finalWorld after finalStore :=
  NamedWhileEdges.condition_preserves functions extension faithful observations runtimeViews evidence unique owners uninitialized missing bodyUninitialized bodyMissing tree found valid agrees state trace

include extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
/-- Actual condition completion reconstructs its source trace and retained entry. -/
theorem concrete_condition_reflects
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason finalMap finalWorld after finalStore :=
  NamedWhileEdges.condition_reflects functions extension faithful observations runtimeViews evidence uninitialized missing bodyUninitialized bodyMissing tree found valid agrees state evaluated

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The concrete lexical body closes child meaning at every reached context;
its outer entry and body-local source context are retained separately. -/
theorem concrete_body_preserves
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (tree : NamedLexicalAssignments.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason mapping world before store)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : Executes false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (bodyCode.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after :=
  NamedWhileEdges.body_preserves functions definitions registered extension faithful observations runtimeViews evidence unique owners uninitialized missing bodyUninitialized bodyMissing tree valid agrees reference state trace

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The concrete lexical body closes child meaning at every reached context;
its outer entry and body-local source context are retained separately. -/
theorem concrete_body_reflects
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (tree : NamedLexicalAssignments.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (bodyCode.rename ξ)) value finalStore) :
    ∃ finalContext outcome after finalMap finalWorld,
      Executes false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after :=
  NamedWhileEdges.body_reflects functions definitions registered extension faithful observations runtimeViews evidence unique owners uninitialized missing bodyUninitialized bodyMissing tree valid agrees reference state evaluated

end Static

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function copied(value: Word) returns (Word) { let local = value; return local; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function stopOrFail(value: Word) returns (Bool) { if (value < 2) { return true; } let gap: Word; return gap == value; }",
  "function count(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 3)) { { let delta = next(0); raw[next(0)] += copied(delta); } if (less(index, 1)) { index += next(0); } else { index += next(0); } } return copied(index + raw[next(0)]); }",
  "function conditionFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (stopOrFail(index)) { raw[next(0)] += copied(4); index += next(0); } return copied(99); }",
  "function bodyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 3)) { raw[next(0)] += copied(4); index += next(0); bad(index); } return copied(99); }",
  "function early(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 3)) { raw[next(0)] += copied(4); return copied(raw[next(0)]); } return bad(99); }",
  "function zero(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 0)) { bad(index); } return copied(raw[next(0)]); }",
  "function unitLoop(raw: mapping(Word => Word), seed: Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 2)) { raw[next(0)] += copied(1); index += next(0); copied(index); } }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10, wordValue 7] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected while resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected while fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected while exact fault binder missing")

private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected while inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected while missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected while raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 3]? with
    | some cell => pure cell | none => throw (IO.userError "protected while missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected while writes changed {name}"
  match final.heap[initial.heap.length + 2]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected while captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 1, initial.heap.length])
      s!"protected while captured source aliases changed {name}"
  | other => throw (IO.userError s!"protected while lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let names := ["count", "conditionFault", "bodyFault", "early", "zero", "unitLoop"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named while edges" content names
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let conditionGap ← gapBinder compiled "stopOrFail"
  let bodyGap ← gapBinder compiled "bad"
  let mut baseline : List String := []
  for fuel in [400000, 0, 43] do
    let mut current : List String := []
    for (name, result, updated, counter) in [("count",16,13,3), ("early",14,14,0), ("zero",10,10,0)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"protected while result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected while success {name}: {reprStr other}")
    for (name, fault, updated, counter) in [("conditionFault",conditionGap,18,2), ("bodyFault",bodyGap,14,1)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == fault) s!"protected while fault site {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected while failure {name}: {reprStr other}")
    let completed ← finish compiled "unitLoop" fuel initial
    match completed with
    | .done .unit final =>
      observe initial final "unitLoop" 12 2
      current := current ++ [reprStr completed]
    | other => throw (IO.userError s!"protected while Unit body: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "protected while resume changed exact source observations"
  IO.println "protected named while edges: concrete condition/body consumers, actual hidden slots, raw duplicate mapping writes, captured aliases, first faults/Unit/early return and resume GREEN"

end Tests.SourceCoreProtectedNamedWhileEdges
