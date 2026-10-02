import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderPost
import Solcore.SourceSemantics.CoreLowering.ProtectedForGenericEndpoint
import Solcore.SourceSemantics.CoreLowering.NamedLoopStatements
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Concrete named expression Trees discharge the guarded header child meaning.
Actual marked locals, seven-slot assignments and six-slot post temporaries
retain installed observations and restore the original outer capture. Full
same-family for statement grammar remains a subsequent composition boundary. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedForHeaders
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open CallableAncestryPairedLookup (Checked Base)
open CallableIndexedHistory (NativeFrame)
section Concrete
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
theorem concrete_named_prefix_preserves {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop} {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)) ambient.definitions administrative type continuation
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ tail : ProtectedForHeader.Tail (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  exact ProtectedForHeader.Tree.preserves_prefix functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    faithful observations tree valid environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_prefix_reflects {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop}
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)) ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ProtectedForHeader.Result (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  exact ProtectedForHeader.Tree.reflects functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (fun current currentValid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing)
    faithful observations runtimeViews tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_post_loop_preserves {context : SourceSemantics.Context} {scope : Scope}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {post : List ForItemForm} {reason : Word} {administrative : Core.Context}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type code)
    (postTree : ProtectedForHeader.Tree layouts owner active frame globals onError values source
      (fun context => (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)) ambient.definitions administrative type (TypedForHeader.Fallthrough type)
      context scope post postCode)
    (postErrors : GenericForHeader.Tree.Errors registry faults postTree)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode reason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedFor.Body.LoopPreserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      condition post statements expected type (LocalLoop.iterate type conditionCode code postCode reason) := by
  apply ProtectedFor.Body.loop_preserves functions program evidence
      (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners)
    conditionFound conditionTree nativeTyped unique
    (NamedLoopStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing body)
  · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid
    intro mapping world before after store finalContext finalEnvironment state continued executed
    exact ProtectedForHeader.post_preserves functions definitions registered extension program evidence
      (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
      (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
      (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
        uninitialized missing bodyUninitialized bodyMissing unique owners)
      faithful observations postTree valid agrees reference state continued executed
  · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid
    intro mapping world before after store finalContext reason state continued executed
    exact ProtectedForHeader.post_fault functions definitions registered extension program evidence
      (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
      (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
      (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
        uninitialized missing bodyUninitialized bodyMissing unique owners)
      faithful observations postTree postErrors valid agrees reference state continued executed

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_post_loop_reflects {context : SourceSemantics.Context} {scope : Scope}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {post : List ForItemForm} {reason : Word} {administrative : Core.Context}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type code)
    (postTree : ProtectedForHeader.Tree layouts owner active frame globals onError values source
      (fun context => (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)) ambient.definitions administrative type (TypedForHeader.Fallthrough type)
      context scope post postCode)
    (postErrors : GenericForHeader.Tree.Errors registry faults postTree)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode reason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedFor.Body.LoopReflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      condition post statements expected type (LocalLoop.iterate type conditionCode code postCode reason) := by
  apply ProtectedFor.Body.loop_reflects functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing)
    conditionFound conditionTree nativeTyped
    (NamedLoopStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing body)
    (fun executed => body.control_not_fault unique executed)
  intro actualContext environment canonical actual ξ contextLocation location agrees reference valid
  intro mapping world before store finalStore value state continued evaluated
  exact ProtectedForHeader.post_reflects functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (fun current currentValid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing)
    faithful observations runtimeViews postTree postErrors valid agrees reference state continued evaluated

end Concrete

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function copied(value: Word) returns (Word) { let local = value; return local; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
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
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected for headers resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name binderName : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected for headers fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == binderName) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected for headers exact fault binder missing")

private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected for headers inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected for headers missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected for headers raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 3]? with
    | some cell => pure cell | none => throw (IO.userError "protected for headers missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected for headers writes changed {name}"
  match final.heap[initial.heap.length + 2]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected for headers captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 1, initial.heap.length])
      s!"protected for headers captured source aliases changed {name}"
  | other => throw (IO.userError s!"protected for headers lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected for headers" content
    ["localsContinue", "localsFallthrough", "postBreak", "postReturn", "bitNot", "postFault", "initialFault", "bitNotFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let postGap ← gapBinder compiled "postFault" "missing"
  let initialGap ← gapBinder compiled "initialFault" "missing"
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated, counter) in [("localsContinue",19,16,3), ("localsFallthrough",19,16,3), ("postBreak",11,11,0), ("postReturn",12,12,0), ("bitNot",14,12,2)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"protected for headers result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected for headers success {name}: {reprStr other}")
    for (name, exactGap, updated, counter) in [("postFault",postGap,15,1), ("initialFault",initialGap,13,0)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == exactGap) s!"protected for headers exact fault {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected for headers failure {name}: {reprStr other}")
    let unary ← finish compiled "bitNotFault" fuel initial
    match unary with
    | .fault (.invalidUnaryOperand .bitNot none) final =>
      observe initial final "bitNotFault" 12 1
      current := current ++ [reprStr unary]
    | other => throw (IO.userError s!"protected for headers exact absent unary fault: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "protected for headers resume changed observations"
  IO.println "protected for headers: concrete named prefix/post, fresh marked locals, outer entry restoration, continue/fallthrough, break/return skip, seven-slot assignments/unary, exact first faults, raw duplicates/capture aliases and resume GREEN"

end Tests.SourceCoreProtectedForHeaders
