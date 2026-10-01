import Solcore.SourceSemantics.CoreLowering.NamedLoopStatements
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
namespace Tests.SourceCoreProtectedNamedLoops
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open NamedLoopStatements
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
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedLoopStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem concrete_named_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode statements expected type code) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedLoopStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
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
    ProtectedWhile.Body.Preserves functions program evidence
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
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) :=
  concrete_named_reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.assignment found form head errors tail)


include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Both the loop body and the enclosing tail belong to this same tree. The
finite native loop proof receives the body IH, not a supplied runtime theorem. -/
theorem concrete_nested_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty}
    {conditionCode loopCode tailCode : Expr} {reason : Word} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type loopCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode loopCode reason) (LocalLoop.resultType type) ambient.definitions)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode rest expected type tailCode) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      mode (id :: rest) expected type (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode reason) tailCode) :=
  concrete_named_preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing
    (.whileLoop found form conditionFound conditionType conditionTree body nativeTyped tail)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- A whole native completion reflects the same recursively certified loop
body and tail, with the source control/fault distinction derived internally. -/
theorem concrete_nested_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty}
    {conditionCode loopCode tailCode : Expr} {reason : Word} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type loopCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode loopCode reason) (LocalLoop.resultType type) ambient.definitions)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode rest expected type tailCode) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      mode (id :: rest) expected type (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode reason) tailCode) :=
  concrete_named_reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing
    (.whileLoop found form conditionFound conditionType conditionTree body nativeTyped tail)

end Static

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function copied(value: Word) returns (Word) { let local = value; return local; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function nested(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 4)) { index += copied(1); if (less(index, 2)) { continue; } let inner = 0; while (less(inner, 4)) { inner += next(0); if (less(inner, 2)) { continue; } raw[next(0)] += copied(1); if (less(1, inner)) { break; } } } return copied(index + raw[next(0)]); }",
  "function outerBreak(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { raw[next(0)] += copied(2); index += next(0); if (less(2, index)) { break; } } return copied(index + raw[next(0)]); }",
  "function nestedFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { index += next(0); let inner = 0; while (less(inner, 3)) { inner += next(0); raw[next(0)] += copied(1); if (less(1, inner)) { bad(index); } } } return copied(99); }",
  "function stopOrFail(value: Word) returns (Bool) { if (value < 3) { return true; } let gap: Word; return gap == value; }",
  "function early(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { index += next(0); let inner = 0; while (less(inner, 4)) { inner += next(0); raw[next(0)] += copied(1); if (less(1, inner)) { return copied(raw[next(0)] + index); } } } return bad(seed); }",
  "function unitLoop(raw: mapping(Word => Word), seed: Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 4)) { index += next(0); if (less(index, 2)) { continue; } { let delta = copied(2); raw[next(0)] += delta; } if (less(2, index)) { break; } } }",
  "function conditionFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (stopOrFail(index)) { raw[next(0)] += copied(3); index += next(0); } return copied(99); }",
  "function keyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { index += next(0); if (less(0, index)) { raw[bad(index)] += copied(99); } } return copied(99); }",
  "function rhsFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { index += next(0); { let chosen = copied(2); raw[next(0)] += chosen; raw[next(0)] += bad(index); } } return copied(99); }",
  "function zero(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 0)) { while (less(index, 4)) { bad(seed); break; } } return copied(raw[next(0)]); }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10, wordValue 7] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected named recursive loops resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected named recursive loops fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected named recursive loops exact fault binder missing")

private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected named recursive loops inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected named recursive loops missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected named recursive loops raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 3]? with
    | some cell => pure cell | none => throw (IO.userError "protected named recursive loops missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected named recursive loops writes changed {name}"
  match final.heap[initial.heap.length + 2]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected named recursive loops captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 1, initial.heap.length])
      s!"protected named recursive loops captured source aliases changed {name}"
  | other => throw (IO.userError s!"protected named recursive loops lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named recursive loops contracts" content
    ["nested", "outerBreak", "nestedFault", "early", "unitLoop", "conditionFault", "keyFault", "rhsFault", "zero"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled "bad"
  let conditionGap ← gapBinder compiled "stopOrFail"
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated, counter) in [("nested",17,13,4), ("outerBreak",19,16,3), ("early",13,12,1), ("zero",10,10,0)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"protected named recursive result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected named recursive success {name}: {reprStr other}")
    let completed ← finish compiled "unitLoop" fuel initial
    match completed with
    | .done .unit final =>
      observe initial final "unitLoop" 14 3
      current := current ++ [reprStr completed]
    | other => throw (IO.userError s!"protected named recursive Unit transfer: {reprStr other}")
    for (name, exactGap, updated, counter) in [("nestedFault",gap,12,1), ("conditionFault",conditionGap,19,3),
        ("keyFault",gap,10,1), ("rhsFault",gap,12,1)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == exactGap) s!"protected named recursive exact fault {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected named recursive failure {name}: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "protected named recursive resume changed observations"
  IO.println "protected named recursive loops contracts: same recursive Tree consumers, nested loops/break/continue/return, condition/key/RHS/body first faults, raw duplicate/capture aliases and resume GREEN"

end Tests.SourceCoreProtectedNamedLoops
