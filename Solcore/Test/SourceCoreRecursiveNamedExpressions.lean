import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Recursive named expressions retain actual call emission, concrete static
body receipts and protected installed closures. These kernel consumers close
child/body semantics; cached source fixtures exercise all admitted parent
positions, ordered arguments, faults, raw metadata and native resume. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup

section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {inner group : ExpressionId} {node innerNode : ExpressionNode}
  {lowered : SourceCoreBasic.LoweredExpr} {entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)}

/-- The named leaf keeps its real accepted Functions action through Emission;
the group wraps it without requiring any source or native body execution. -/
theorem group_of_named_emission
    (named : NamedCallExpressions.Head bodies compilation source context
      (CompatibleExpressionCalls.Entries scope entries) scope inner lowered)
    (children : ∀ child code, (child, code) ∈ entries →
      NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope child code)
    (metadata : CompatibleExpressionPrimitives.Metadata values.checked source group node lowered.type)
    (form : node.form = .group inner)
    (found : source.lookupExpression? inner = some innerNode) (sameType : node.type = innerNode.type) :
    NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope group lowered := by
  apply CompatibleExpressionCalls.Tree.node (entries := [(inner, lowered)])
  · exact .primitive (.group metadata form found sameType ⟨rfl, by simp⟩)
  · intro child code member
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .node (.call named) children

/-- Positional member nodes are retained typed IR (the current surface checker
does not infer ordinary field access). Their exact compatible layout still
composes with an actual accepted named child, without a semantic callback. -/
theorem member_of_named_emission {name : String} {index : Nat} {identity : Core.DataTypeId}
    {branches : List Core.Expr} {result : Core.Ty}
    (named : NamedCallExpressions.Head bodies compilation source context
      (CompatibleExpressionCalls.Entries scope entries) scope inner lowered)
    (children : ∀ child code, (child, code) ∈ entries →
      NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope child code)
    (metadata : CompatibleExpressionPrimitives.Metadata values.checked source group node result)
    (baseMetadata : CompatibleExpressionPrimitives.Metadata values.checked source inner innerNode lowered.type)
    (form : node.form = .member inner name index)
    (layout : CompatibleExpressionMembers.Layout values.checked (.occurrence group.occurrence)
      innerNode.type node.type index identity branches result) :
    NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope group
      ⟨result, SourceCoreDataExpressions.member identity result branches lowered.expression⟩ := by
  apply CompatibleExpressionCalls.Tree.node (entries := [(inner, lowered)])
  · exact .member metadata baseMetadata form layout ⟨rfl, by simp⟩
  · intro child code member
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .node (.call named) children

variable (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (leaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (caller : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context caller)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {id : ExpressionId} {root : ExpressionNode}
  (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope id lowered)
  (found : source.lookupExpression? id = some root)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Core.Environment}
  {before : Dynamic.Heap} {store : Core.Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)

include extension faithful leaves runtimeViews valid uninitialized missing bodyUninitialized bodyMissing
  tree found environments heaps locals agrees typed installed in
/-- An actual named call may occur at any certified data/control/argument
position. Static concrete body receipts and finite tree induction supply all
body and child meaning; installed closure/frame observations stay explicit. -/
theorem tree_preserves (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context caller source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld after finalStore ∧ LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  NamedCallExpressions.Tree.preserves functions extension faithful leaves runtimeViews caller valid
    uninitialized missing bodyUninitialized bodyMissing unique owners tree found
    environments heaps locals agrees typed installed trace

include extension faithful leaves runtimeViews valid uninitialized missing bodyUninitialized bodyMissing
  tree found environments heaps locals agrees typed installed in
/-- Full finite native completion reconstructs the independent source outcome,
including faults reached inside a named child's ordered arguments or body. -/
theorem tree_reflects {value : Core.Value} {finalStore : Core.Store}
    (complete : Evaluates actual store (lowered.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context caller source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld after finalStore ∧ LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  NamedCallExpressions.Tree.reflects functions extension faithful leaves runtimeViews caller valid
    uninitialized missing bodyUninitialized bodyMissing tree found
    environments heaps locals agrees typed installed complete
end Static

private def content : String := String.intercalate "\n" [
  "enum Box { Box(Bool) }",
  "function wordLeaf() returns (Word) { return wordFromInteger(7); }",
  "function wordOther() returns (Word) { return wordFromInteger(3); }",
  "function boolLeaf() returns (Bool) { return integerEq(2, 2); }",
  "function boolOther() returns (Bool) { return integerLt(2, 1); }",
  "function intLeaf() returns (integer) { return integerAdd(2, 3); }",
  "function intOther() returns (integer) { return integerSub(9, 6); }",
  "function take(a: integer, b: integer) returns (integer) { return integerSub(a, b); }",
  "function first(a: Word) returns (integer) { let copied = wordToInteger(a); return copied; }",
  "function fail() returns (integer) { let written = integerAdd(2, 3); let gap: Word; return wordToInteger(gap); }",
  "function boolFail() returns (Bool) { let gap: Bool; return gap; }",
  "function mapLeaf(raw: mapping((Bool, Bool) => Word)) returns (mapping((Bool, Bool) => Word)) { return raw; }",
  "function grouped() returns (Word) { return ((wordLeaf())); }",
  "function paired() returns ((Word, Bool)) { return (wordLeaf(), boolLeaf()); }",
  "function unary() returns (Word) { return ~wordLeaf(); }",
  "function binary() returns (Word) { return wordLeaf() + wordOther(); }",
  "function chosen(flag: Bool) returns (Word) { return flag ? wordLeaf() : wordOther(); }",
  "function boolUnary() returns (Bool) { return !boolOther(); }",
  "function boolBinary() returns (Bool) { return boolLeaf() && !boolOther(); }",
  "function constructed() returns (Box) { return Box(boolLeaf()); }",
  "function indexed(raw: mapping((Bool, Bool) => Word)) returns (Word) { return mapLeaf(raw)[(boolLeaf(), boolOther())]; }",
  "function defaulted() returns (Word) { let empty: mapping((Bool, Bool) => Word); return empty[(boolLeaf(), boolOther())]; }",
  "function builtinArgument() returns (integer) { return integerAdd(intLeaf(), intOther()); }",
  "function namedArguments() returns (integer) { return take(integerAdd(intLeaf(), 1), first(wordLeaf())); }",
  "function ordered() returns (integer) { return take(first(wordLeaf()), first(wordOther())); }",
  "function skipped() returns (Bool) { return false && boolFail(); }",
  "function firstFault() returns (integer) { return take(fail(), first(wordLeaf())); }",
  "function lastFault() returns (integer) { return take(first(wordLeaf()), fail()); }",
  "function rawEcho(raw: mapping((Bool, Bool) => Word)) returns (mapping((Bool, Bool) => Word)) { return mapLeaf(raw); }"
]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"recursive named resume {name}" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"recursive named source prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"recursive named ordered cells changed {label}: {reprStr final.heap}"

private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "recursive named fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "recursive named exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named expressions" content
    ["grouped", "paired", "unary", "binary", "chosen", "boolUnary", "boolBinary", "constructed",
      "indexed", "defaulted", "builtinArgument", "namedArguments", "ordered", "skipped", "firstFault", "lastFault", "rawEcho"]
  let seven : SourceTypedRuntime.Value := .word (Word.ofNatModulo 7)
  let three : SourceTypedRuntime.Value := .word (Word.ofNatModulo 3)
  let key : SourceTypedRuntime.Value := .product (.bool true) (.bool false)
  let keyType : TypeSystem.Ty := .product .bool .bool
  let mapType : TypeSystem.Ty := .mapping keyType .word
  let raw : SourceTypedRuntime.Value := .mapping (.comptime keyType) (.comptime .word)
    [(key, .word (Word.ofNatModulo 37)), (key, .word (Word.ofNatModulo 91))]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (Word.ofNatModulo 819))⟩]}
  let gap ← faultBinder compiled
  let dataType ← SourceCoreUnifiedCorpusSupport.get "recursive named Box"
    (match compiled.sourceProgram.signatures.dataTypes.head? with
     | some dataType => Except.ok dataType | none => Except.error "missing Box")
  let cases : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value) := [
    ("grouped", [], seven), ("paired", [], .product seven (.bool true)),
    ("unary", [], .word ((Word.ofNatModulo 7).bitNot)), ("binary", [], .word (Word.ofNatModulo 10)),
    ("chosen", [.bool true], seven), ("chosen", [.bool false], three),
    ("boolUnary", [], .bool true), ("boolBinary", [], .bool true),
    ("indexed", [raw], .word (Word.ofNatModulo 37)), ("defaulted", [], .word Word.zero),
    ("builtinArgument", [], .integer 8), ("namedArguments", [], .integer (-1)),
    ("ordered", [], .integer 4), ("skipped", [], .bool false), ("rawEcho", [raw], raw)]
  for fuel in [0, 43, 300000] do
    for (name, arguments, expected) in cases do
      match ← finish compiled name arguments fuel initial with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected)
          s!"recursive named result changed {name}: {reprStr actual}"
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
          s!"recursive named result changed inert prefix {name}"
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"recursive named unsafe source heap {name}"
        if name == "ordered" then
          cells initial final [(.word, some seven), (.integer, some (.integer 7)),
            (.word, some three), (.integer, some (.integer 3)),
            (.integer, some (.integer 7)), (.integer, some (.integer 3))] name
        if name == "skipped" then cells initial final [] name
        if name == "rawEcho" then cells initial final [(mapType, some raw), (mapType, some raw)] name
      | other => throw (IO.userError s!"recursive named {name}: {reprStr other}")
    match ← finish compiled "constructed" [] fuel initial with
    | .done (.constructed instantiation [.bool true]) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (instantiation.constructor.dataType == dataType.id)
        "recursive named constructor lost source identity"
      cells initial final [] "constructed"
    | other => throw (IO.userError s!"recursive named constructed: {reprStr other}")
    for name in ["firstFault", "lastFault"] do
      match ← finish compiled name [] fuel initial with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "recursive named fault lost exact source binder"
        let earlier := if name == "lastFault" then [(.word, some seven), (.integer, some (.integer 7))] else []
        cells initial final (earlier ++ [(.integer, some (.integer 5)), (.word, none)]) name
      | other => throw (IO.userError s!"recursive named fault {name}: {reprStr other}")
  IO.println "recursive named expressions: concrete static bodies, whole source outcomes, protected globals/history, data/control/index/argument parents, faults, raw metadata/defaults and resume GREEN"
end Tests.SourceCoreRecursiveNamedExpressions
