import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalAssignments
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StatePlaceAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.PlaceAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedBareAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.Frontend.SourceCoreCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues

/-!
# Recursive named expression tests

Recursive named assignments, expressions, builtins, data and tuples.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedAssignmentHeadBounds
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
theorem named_preserves [FunctionCalls.FaultTokens faults] (budget : Nat) {updated : Dynamic.Value} {after : Dynamic.Heap}
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
theorem named_fault [FunctionCalls.FaultTokens faults] (budget : Nat) (errors : head.ReachableErrors registry faults)
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
theorem named_reflects [FunctionCalls.FaultTokens faults] (budget : Nat) (errors : head.ReachableErrors registry faults)
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedAssignmentNativeTyping
/-! Native assignment children are derived from the same static expression
Trees and real entry globals. Actual cached body typing feeds the existing
compiler traversal. Source certificates, support and residual diagnostic
interpretation remain explicit; no execution law is stored in a receipt. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedAssignmentNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory NativeExpressionContextSupport

variable (cached : SourceCoreUnifiedCompilation.Compiled)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
  (member : nativeEntry ∈ cached.indexed.entries)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (definitions : ambient.definitions = cached.indexed.layouts.definitions)
  {headers : Inventory cached.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {header : Header cached.indexed.ancestry values ambient.definitions program}
  (sameCache : header.compiled.closures = cached.indexed.secondPass.closures)
  (complete : Complete headers) (globals : header.globals = cached.indexed.base.globals.length)
  (support : supported (.lambda header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType) header.code) (cached.indexed.base.globals.length + 1) = true)
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include member definitions sameCache in
private theorem original_cached :
    HasType (cached.indexed.base.globals.map (·.referenceType) ++ .cell cached.indexed.ancestry.layout.frame.type ::
      SourceCoreGeneralEntry.nativeInputContext nativeEntry.native.inputTypes)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions := by
  have selected := header.cached
  rw [sameCache] at selected
  have typed := CallableIndexedCachedNativeTyping.prepared_native_closure cached.indexedPrepared member selected
    (CallableIndexedPreparedInventories.cached_global_at cached header.selected)
  simpa only [← definitions] using typed

include member definitions sameCache complete globals support entry in
theorem actual_canonical_body :
    HasType (SourceCoreLocalCell.coreContext (bodyScope header) ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      header.body (LanguageResult.resultType header.output) ambient.definitions :=
  canonical_cached complete globals (original_cached cached member definitions sameCache) support entry

include member definitions sameCache complete globals support in
theorem actual_renamed_body :
    HasType (CallableIndexedParameterTyped.prefixContext header.bindings actualContext)
      (header.body.rename entry.embedding) (LanguageResult.resultType header.output) ambient.definitions :=
  (actual_canonical_body cached member definitions sameCache complete globals support entry).rename
    (TypedLexicalWhile.environment_respects entry.environments.runtime_hasTypes entry.actualTyped entry.lookups)

variable {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

include member definitions sameCache complete globals support entry in
/-- This consumer feeds the real prepared root's native proof into the single
compiler traversal, without requesting body/loop HasType at actual Γ. -/
theorem actual_extraction (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (closed : header.context.typeVariables = []) (residual : header.context.residualTypeVariables = false)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :=
  RecursiveNamedAssignmentNativeCertificates.extract diagnosticPolicy registered prefixEq factory readPolicy binderPolicy allocationPolicy
    expressions assignments unaryPolicy syntaxTree closed residual sourceSignatures declarations
    projection accepted (original_cached cached member definitions sameCache) support complete globals entry

/-- Interpretation is required only for the selected extraction. -/
theorem selected_profile {diagnosticPolicy : AssignmentDiagnosticPolicy} {faults : FunctionCalls.FaultRep}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (interpreted : receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults) :=
  ⟨receipt.profile initialValid interpreted⟩


section Children
variable {readFuel : Nat} {source : TypedSource} {sourceContext : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
  {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
  (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
  (prefixEq : compilation.administrativePrefix = 1)

include registered prefixEq entry in
/-- Neither the context of unused locals nor administrative annotations are
assumed well formed. Used read metadata and actual globals suffice. -/
theorem actual_child_native
    (tree : Expressions headers compilation readFuel source sourceContext solved reasonAt scope id lowered) :
    HasType (SourceCoreLocalCell.coreContext scope ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      lowered.expression (LanguageResult.resultType lowered.type) ambient.definitions := by
  have shaped := CompatibleCatalogNominalCoverage.prepare_shapes registered
  rw [← SourceCoreCompatibleCatalog.prepare_signatures registered] at shaped
  exact (RecursiveNamedExpressionNativeTyping.tree_native_at shaped
    (CompatibleCatalogNominalCoverage.prepare_complete registered)
    (RecursiveNamedAssignmentNativeCertificates.entry_slots prefixEq entry) ambient.basePrefix tree).2

include registered prefixEq entry in
/-- This callback covers only the original RHS and ordered key members.
Native child typing has no separate premise. -/
theorem actual_assignment_children {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp}
    {rhs : ExpressionId} {expression : SourceCoreLoops.ExpressionLowerer} {fuel : Nat}
    (unique : NodeOccurrencesUnique source)
    (typed : SourceAssignmentHasType source sourceContext assignment operator rhs)
    (expressions : ∀ id, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      ∀ node lowered, source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      expression fuel source scope id reasonAt = .ok lowered →
      Expressions headers compilation readFuel source sourceContext solved reasonAt scope id lowered) :
    ∀ id lowered, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧
      Expressions headers compilation readFuel source sourceContext solved reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        lowered.expression (LanguageResult.resultType lowered.type) ambient.definitions := by
  have shaped := CompatibleCatalogNominalCoverage.prepare_shapes registered
  rw [← SourceCoreCompatibleCatalog.prepare_signatures registered] at shaped
  exact RecursiveNamedAssignmentNativeCertificates.assignment_children shaped
    (CompatibleCatalogNominalCoverage.prepare_complete registered)
    (RecursiveNamedAssignmentNativeCertificates.entry_slots prefixEq entry) unique typed expressions
end Children

/-- An absent data definition makes this unused annotation invalid, but a
literal expression still has a native derivation in that exact context. -/
theorem invalid_unused_annotation {binder : Resolved.LocalId} :
    ¬ CompatibleExpressionScalarNativeTyping.ScopeWellFormed [] [(binder, .namedData ⟨0⟩)] := by
  intro wellFormed
  have missing := wellFormed binder 0 (.namedData ⟨0⟩) (by simp [SourceCoreLocalCell.lookup?])
  cases missing with | namedData found => cases found

theorem literal_types_with_unused_annotation {binder : Resolved.LocalId} :
    HasType (SourceCoreLocalCell.coreContext [(binder, .namedData ⟨0⟩)])
      (LanguageResult.success (.bool true)) (LanguageResult.resultType .bool) [] := by
  exact LanguageResult.success_hasType .bool

theorem projection_typing_is_static {catalog : SourceCoreCompatibleCatalog.Catalog}
    {sourceType : TypeSystem.Ty} {native : Ty} (projected : catalog.project sourceType = .ok native) :
    native.WellFormed catalog.definitions :=
  CompatibleExpressionCertificateNativeTyping.project_wellFormed projected

private def content : String := String.intercalate "\n" [
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function truth(flag: Bool) returns (Bool) { return flag; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function assign(x: Word, y: Word) returns (Word) { x = side(y); return x; }",
  "function compound(x: Word, y: Word) returns (Word) { x += side(y); return x; }",
  "function indexed(m: mapping(Bool => Word), y: Word) returns (Word) { m[truth(true)] = side(y); return m[true]; }",
  "function compoundIndex(m: mapping(Bool => Word), y: Word) returns (Word) { m[truth(true)] += side(y); return m[true]; }",
  "function rhsBuiltin(m: mapping(Bool => integer), y: Word) returns (integer) { m[truth(true)] = integerAdd(wordToInteger(side(y)), wordToInteger(side(y))); return m[true]; }",
  "function pairKey(m: mapping((Bool, Bool) => Word), y: Word) returns (Word) { m[(truth(true), truth(false))] = side(y); return m[(true, false)]; }",
  "function rhsFault(m: mapping(Bool => Word), y: Word) returns (Word) { m[truth(true)] = fail(); return m[true]; }",
  "function keyFault(m: mapping(Bool => Word), y: Word) returns (Word) { m[side(fail()) == y] = side(y); return m[true]; }",
  "function lateFault(x: Word, y: Word) returns (Word) { x = side(y); return fail(); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- Inspect the real finite RHS/key list at each accepted assignment site.
Unused invalid locals deliberately make whole-scope WF unavailable. Actual
children are recompiled in that scope so named global offsets also move. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) (names : List String) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "assignment native diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "assignment native parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut sites := 0
  let mut children := 0
  for named in prepared.base.functions do
    let original ← match prepared.base.sourceProgram.signatures.functions.find? (·.id == named.signature.key.declaration) with
      | some signature => pure signature | none => throw (IO.userError "assignment native source signature missing")
    if names.contains original.name then
      let own ← match diagnostics.base.find? named.signature.key with
        | some own => pure own | none => throw (IO.userError "assignment native own diagnostics missing")
      let source := CallableIndexedNamedGeneration.source named
      let compilation := CallableIndexedNamedGeneration.context prepared named
      let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
      let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
      let invalid : Ty := .namedData ⟨prepared.layouts.definitions.length + 100⟩
      let unused : Resolved.LocalId := ⟨source.owner, 100000⟩
      let scopes := [scope, scope ++ [(unused, invalid)]]
      let reasonAt := diagnostics.reasonAt named.signature.key
      let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
        prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics compilation
        prepared.base.callableContext none none
      require (compilation.administrativePrefix == 1) "assignment native argument prefix changed"
      require (!invalid.isWellFormed prepared.layouts.definitions) "unused native annotation unexpectedly valid"
      for (signature, index) in compilation.globals.zipIdx do
        require (prepared.base.functions[index]?.map (·.signature) == some signature)
          "assignment native full global slot changed"
      for node in source.nodes do
        match node with
        | .statement node =>
          match node.form with
          | .assignValue assignment _ rhs =>
            sites := sites + 1
            let ids := rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections
            children := children + ids.length
            for selectedScope in scopes do
              let administrative := named.signature.parameterType :: prepared.base.globals.map (·.referenceType) ++
                [.cell prepared.ancestry.layout.frame.type]
              let nativeContext := SourceCoreLocalCell.coreContext selectedScope ++ administrative
              for id in ids do
                let code ← get "actual assignment child" (lower prepared.fuel source selectedScope id reasonAt)
                for suffix in [[], [.integer, invalid], [OptionalCell.referenceType invalid]] do
                  require (Core.infer? (nativeContext ++ suffix) code.expression prepared.layouts.definitions ==
                    some (LanguageResult.resultType code.type)) "assignment child native typing lost unused suffix"
                require (Core.infer? (.integer :: nativeContext) (code.expression.rename (Renaming.insertion 0))
                  prepared.layouts.definitions == some (LanguageResult.resultType code.type))
                  "assignment child native typing lost actual insertion"
          | _ => pure ()
        | _ => pure ()
  require (sites == names.length && children > sites) "assignment native finite site coverage changed"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "assignment native public resume" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"assignment native old heap changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"assignment native ordered source cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let names := ["assign", "compound", "indexed", "compoundIndex", "rhsBuiltin", "pairKey", "rhsFault", "keyFault", "lateFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "assignment native children" content names
  inspect compiled names
  let mapping : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 31), (.bool true, w 91), (.bool false, w 4)]
  let updated (value : Nat) : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w value), (.bool true, w 91), (.bool false, w 4)]
  let integers : SourceTypedRuntime.Value := .mapping .bool .integer [(.bool true, .integer 31), (.bool true, .integer 91)]
  let integerUpdated : SourceTypedRuntime.Value := .mapping .bool .integer [(.bool true, .integer 14), (.bool true, .integer 91)]
  let key : SourceTypedRuntime.Value := .product (.bool true) (.bool false)
  let pairs : SourceTypedRuntime.Value := .mapping (.product .bool .bool) .word [(key, w 31), (key, w 91)]
  let pairsUpdated : SourceTypedRuntime.Value := .mapping (.product .bool .bool) .word [(key, w 7), (key, w 91)]
  let side : List (TypeSystem.Ty × Option SourceTypedRuntime.Value) := [(.word, some (w 7)), (.word, some (w 7))]
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("assign", [w 3, w 7], w 7, [(.word, some (w 7)), (.word, some (w 7))] ++ side),
    ("compound", [w 3, w 7], w 10, [(.word, some (w 10)), (.word, some (w 7))] ++ side),
    ("indexed", [mapping, w 7], w 7, [(.mapping .bool .word, some (updated 7)), (.word, some (w 7)), (.bool, some (.bool true))] ++ side),
    ("compoundIndex", [mapping, w 7], w 38, [(.mapping .bool .word, some (updated 38)), (.word, some (w 7)), (.bool, some (.bool true))] ++ side),
    ("rhsBuiltin", [integers, w 7], .integer 14, [(.mapping .bool .integer, some integerUpdated), (.word, some (w 7)), (.bool, some (.bool true))] ++ side ++ side),
    ("pairKey", [pairs, w 7], w 7, [(.mapping (.product .bool .bool) .word, some pairsUpdated), (.word, some (w 7)), (.bool, some (.bool true)), (.bool, some (.bool false))] ++ side)]
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("rhsFault", [mapping, w 7], [(.mapping .bool .word, some mapping), (.word, some (w 7)), (.bool, some (.bool true)), (.word, some (w 5)), (.word, none)]),
    ("keyFault", [mapping, w 7], [(.mapping .bool .word, some mapping), (.word, some (w 7)), (.word, some (w 5)), (.word, none)]),
    ("lateFault", [w 3, w 7], [(.word, some (w 7)), (.word, some (w 7))] ++ side ++ [(.word, some (w 5)), (.word, none)])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩, ⟨.bool, some (.bool false)⟩]}
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failed ← failures.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  for fuel in [0, 7, 43, 300000] do
    for (test, baseline) in successes.zip baselines do
      let (name, arguments, expected, expectedCells) := test
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"assignment native complete resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"assignment native result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"assignment native expected completion {name}")
    for (test, baseline) in failures.zip failed do
      let (name, arguments, expectedCells) := test
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"assignment native fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal _) final => cells initial final expectedCells name
      | _ => throw (IO.userError "assignment native lost ordered source fault")
  IO.println "assignment native typing: same Trees, actual RHS/ordered keys/global slots, unused invalid annotations, hidden insertion, full heap/fault/resume GREEN"
end Tests.SourceCoreRecursiveNamedAssignmentNativeTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedBareAssignmentBounds
/-! Fixed-budget bare assignments retain independent source costs and the
original Core continuation size. Concrete named Trees close RHS meaning.
Projected assignments, common Heads, headers and recursive callees are separate
integration boundaries; no static certificate contains a runtime premise. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedBareAssignmentBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup SourceCoreCompatibleDataPlaces
open CompatibleEquality CompatibleHeap CoreProof CompatibleBareAssignment
abbrev ValuesContext := SourceCoreCompatibleValues.Context
section Static
variable {checked : CallableAncestryPairedLookup.Checked} {base : Base checked}
  {installedPlan : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {source : TypedSource} {program : SourceSemantics.Program}
  {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {bodies : NamedCallExpressions.Bodies installedPlan values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
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

variable {targetPrepared : Prepared} {index : Nat} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  (layout : CompatibleBareAssignment.Layout values targetPrepared)
  (bare : assignment.target.projections = [])
  (generated : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope rhs lowered)
  (found : source.lookupExpression? rhs = some node)
  (rhsView : SourceCoreRawMetadata.runtimeType targetPrepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
  (rhsCore : lowered.type = targetPrepared.route.leafType)
  (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType targetPrepared.route.rootSourceType = .word ∨
    SourceCoreRawMetadata.runtimeType targetPrepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
  (slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, targetPrepared.route.rootType))
  (rootTyped : WritableLocal context assignment.target.root targetPrepared.route.rootSourceType)


include extension faithful observations environments heaps locals agrees actualTyped installed valid runtimeViews
  uninitialized missing bodyUninitialized bodyMissing layout bare generated found rhsView rhsCore profile slot rootTyped unique owners in
theorem named_preserves [FunctionCalls.FaultTokens faults] (budget : Nat) {updated : Dynamic.Value} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) (bounded : size ≤ budget) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld slots,
      ValueRep values.checked registry functions finalMap finalWorld targetPrepared.route.rootSourceType updated updatedValue targetPrepared.route.rootType ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext targetPrepared actualContext) ambient.definitions ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute targetPrepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (targetPrepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) :=
  ProtectedBareAssignment.preserves_prefix_bounded budget layout bare extension
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget)
    observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped trace bounded invalid

include extension faithful observations environments heaps locals agrees actualTyped installed valid runtimeViews
  uninitialized missing bodyUninitialized bodyMissing layout bare generated found rhsView rhsCore profile slot rootTyped unique owners in
theorem named_fault [FunctionCalls.FaultTokens faults] (budget : Nat) {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before assignment.target operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (outputType : Ty) (invalid : Word)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute targetPrepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (targetPrepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  ProtectedBareAssignment.preserves_fault_reachable_bounded budget layout bare extension
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget)
    observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped trace bounded next outputType invalid invalidToken

include extension faithful observations environments heaps locals agrees actualTyped installed valid runtimeViews
  uninitialized missing bodyUninitialized bodyMissing layout bare generated found rhsView rhsCore profile slot rootTyped in
theorem named_reflects [FunctionCalls.FaultTokens faults] (budget : Nat) {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid)
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute targetPrepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (targetPrepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) (bounded : size ≤ budget) :
    RecursiveNamedBareAssignmentContracts.ResultAt size values registry functions program context evidence source faults targetPrepared assignment.target operator environment before store mapping world
      rhs actual actualContext ξ next outputType value finalStore :=
  ProtectedBareAssignment.reflects_reachable_bounded budget layout bare extension
    (RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing) budget)
    observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped invalidToken completed bounded

end Static

section SizedResults
variable {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient}
  {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FunctionCalls.FaultRep}
  {prepared : Prepared} {place : PlaceResolution} {operator : Syntax.ValueAssignOp}
  {environment : Dynamic.Environment} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {rhs : ExpressionId}
  {actual : Environment} {actualContext : Core.Context} {ξ : Renaming}
  {next : Expr} {output : Ty} {value : Value} {finalStore : Store} {size budget : Nat}

/-- A successful reflection exposes the original smaller continuation, including
its seven real slots. The reconstructed source cost has no native cost bound. -/
theorem continuation_or_fault
    (result : RecursiveNamedBareAssignmentContracts.ResultAt size values registry functions program context evidence source
      faults prepared place operator environment before store mapping world rhs actual actualContext ξ next output value finalStore)
    (within : size ≤ budget) :
    (∃ sourceSize reason after, SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source
      environment before place operator rhs reason after) ∨
    (∃ sourceSize updated after slots commitStore remainingSize finalWorld,
      SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after ∧
      slots.length = 7 ∧
      RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      remainingSize < size ∧ remainingSize < budget ∧
      EvaluationSize remainingSize (slots ++ actual) commitStore (shift 7 (next.rename ξ)) value finalStore) := by
  cases result with
  | fault trace _ _ _ _ _ _ _ => exact .inl ⟨_, _, _, trace⟩
  | success trace _ _ _ _ _ _ count typed smaller remaining =>
    exact .inr ⟨_, _, _, _, _, _, _, trace, count, typed, smaller, Nat.lt_of_lt_of_le smaller within, remaining⟩

/-- The RHS fault follows the actual successful target prefix, preserving its
heap and both original source child costs. -/
theorem rhs_fault_keeps_prefix {targetSize rhsSize : Nat} {target : Dynamic.ResolvedPlace}
    {middle after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (resolved : SourceExecutionSize.SourcePlaceResolves program targetSize context evidence source environment before place target middle)
    (failed : SourceExecutionSize.ExpressionFaults program rhsSize context evidence source environment middle rhs reason after) :
    ∃ measured, SourceExecutionSize.SourcePlaceAssignmentFaults program measured context evidence source environment before
      place operator rhs reason after ∧ targetSize < measured ∧ rhsSize < measured := by
  exact ⟨_, .rhs resolved failed, SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩
end SizedResults

private def content : String := String.intercalate "\n" [
  "function copy(value: Word) returns (Word) { let copied = value; return copied; }",
  "function rawCopy(value: mapping(Word => Word)) returns (mapping(Word => Word)) { let copied = value; return copied; }",
  "function fail(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function chain(seed: Word) returns (Word) { let root: Word; root = copy(seed); root += copy(2); root = copy(root); return copy(root); }",
  "function shadow(seed: Word) returns (Word) { let root = copy(seed); { let root: Word; root = copy(2); root += copy(3); } root += copy(4); return copy(root); }",
  "function absent(seed: Word) returns (Word) { let root: Word; root += copy(seed); return copy(99); }",
  "function rhsFault(seed: Word) returns (Word) { let root = copy(10); root += fail(seed); return copy(99); }",
  "function afterWrite(seed: Word) returns (Word) { let root = copy(10); root += copy(seed); return fail(root); }",
  "function unitResult(seed: Word) { let root: Word; root = copy(seed); root += copy(2); }",
  "function rawResult(raw: mapping(Word => Word)) returns (mapping(Word => Word)) { let root: mapping(Word => Word); root = rawCopy(raw); return root; }"
]
private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (wordValue n))

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"bounded bare resume {name}" (first.resume 400000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"bounded bare prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue
    (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"bounded bare ordered cells {name}: {reprStr final.heap}"

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "bounded bare gap binder" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "bounded bare exact fault binder missing")

/-- Actual cached compilation is tested separately from the pointwise proofs.
Costs are not equated with runner fuel or compared across source and Core. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "bounded bare assignments" content
    ["chain", "shadow", "absent", "rhsFault", "afterWrite", "unitResult", "rawResult"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled
  for fuel in [0, 43, 211, 400000] do
    for (name, result, numbers) in [("chain", 9, [7,9,7,7,2,2,9,9,9,9]),
        ("shadow", 11, [7,7,7,11,5,2,2,3,3,4,4,11,11])] do
      match ← finish compiled name [wordValue 7] fuel initial with
      | .done value final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr (wordValue result)) s!"bounded bare result {name}"
        cells initial final (numbers.map present) name
      | other => throw (IO.userError s!"bounded bare {name}: {reprStr other}")
    match ← finish compiled "absent" [wordValue 7] fuel initial with
    | .fault (.invalidAssignmentOperands operator left right) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (operator == .add && left == none && right == some .word) "bounded bare operand diagnostics changed"
      cells initial final [present 7, (.word, none), present 7, present 7] "absent"
    | other => throw (IO.userError s!"bounded bare absent compound: {reprStr other}")
    for (name, numbers) in [("rhsFault", [7,10,10,10,7]), ("afterWrite", [7,10,10,17,7,7,17])] do
      match ← finish compiled name [wordValue 7] fuel initial with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) s!"bounded bare fault binder {name}"
        cells initial final (numbers.map present ++ [(.word, none)]) name
      | other => throw (IO.userError s!"bounded bare fault {name}: {reprStr other}")
    match ← finish compiled "unitResult" [wordValue 7] fuel initial with
    | .done .unit final => cells initial final ([7,9,7,7,2,2].map present) "unitResult"
    | other => throw (IO.userError s!"bounded bare Unit: {reprStr other}")
    let raw : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
      [(wordValue 1, wordValue 37), (wordValue 1, wordValue 91)]
    match ← finish compiled "rawResult" [raw] fuel initial with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr raw) "bounded bare raw mapping headers/order changed"
      let copied : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.mapping .word .word, some raw)
      cells initial final [copied, copied, copied, copied] "rawResult"
    | other => throw (IO.userError s!"bounded bare raw mapping: {reprStr other}")
  IO.println "bounded bare assignments: actual seven slots, original smaller continuation, independent source costs, named RHS effects/faults, shadowing, raw copies, prefix and resume GREEN"
end Tests.SourceCoreRecursiveNamedBareAssignmentBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedBareBitNotBounds
/-! The actual unary compiler yields an independent source write/fault and
seven real typed slots. The continuation cost is taken from its original
Core execution, including when it has effects or reads a captured cell. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.SourceCoreRecursiveNamedBareBitNotBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof CompatiblePayload CompatibleEquality CompatibleHeap
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates
open CompatibleRenamedBareBitNot
section Lowering
variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {assignment : AssignmentResolution} {site : SourceCoreElaboration.ErrorSite}
  {expression : ExpressionLowerer} {fuel : Nat} {operator : Syntax.ValueAssignOp} {next lowered : Expr} {output : Ty}
  {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
  {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  {identities : Dynamic.Value → Word → Prop}
  (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
    WritableLocal context assignment.target.root binder.scheme.body)
  (bare : assignment.target.projections = [])
  (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
    SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
  (observations : FunctionObservations compilation.checked.catalog functions identities)
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
    mapping world administrativeContext scope environment canonical)
  (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)

include rootTyped bare profile environments heaps locals agrees

theorem actual_lower_reflects_sized
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      output next reasonAt invalid invalidOperand missing = .ok lowered)
    {faults : FunctionCalls.FaultRep} {value : Value} {finalStore : Store}
    (token : faults (.invalidUnaryOperand .bitNot) invalidOperand)
    {size : Nat} (completed : CoreProof.EvaluationSize size actual store (lowered.rename ξ) value finalStore) :
    ∃ prepared, CompatibleRenamedBareBitNot.ResultAt size compilation.checked registry functions program context evidence source faults prepared assignment.target
      environment before store mapping world actual actualContext ξ next output value finalStore := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  refine ⟨prepared, ?_⟩
  exact CompatibleRenamedBareBitNot.reflects_sized layout bare (view ▸ profile) environments heaps locals agrees actualTyped slot
    (rootEq ▸ rootTyped binder binding) token (lowering ▸ completed)

end Lowering

section Continuation
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {faults : FunctionCalls.FaultRep} {prepared : Prepared} {place : PlaceResolution}
  {environment : Dynamic.Environment} {before : Dynamic.Heap} {store : Store} {mapping : LocationMap}
  {world : StoreTyping} {actual : Core.Environment} {actualContext : Core.Context} {ξ : Renaming}
  {next : Expr} {output : Ty} {value : Core.Value} {finalStore : Store} {size budget : Nat}

/-- Successful reflection selects only a strictly smaller native continuation.
The source size is independent and has no comparison to the native bound. -/
theorem continuation_or_fault
    (receipt : CompatibleRenamedBareBitNot.ResultAt size checked registry functions program context evidence source faults
      prepared place environment before store mapping world actual actualContext ξ next output value finalStore)
    (within : size ≤ budget) :
    (∃ sourceSize reason, SourceExecutionSize.SourcePlaceBitNotFaults program sourceSize context evidence source
      environment before place reason before) ∨
    (∃ sourceSize updated after written slots remainingSize,
      SourceExecutionSize.SourcePlaceSnapshotUpdate program sourceSize context evidence source Dynamic.BitNotSnapshot
        environment before place updated after ∧
      slots.length = 7 ∧
      RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      remainingSize < budget ∧ CoreProof.EvaluationSize remainingSize (slots ++ actual) written
        (shift 7 (next.rename ξ)) value finalStore) := by
  cases receipt with
  | fault trace _ _ _ => exact .inl ⟨_, _, trace⟩
  | success trace _ _ _ _ count typed smaller continuation =>
    exact .inr ⟨_, _, _, _, _, _, trace, count, typed, Nat.lt_of_lt_of_le smaller within, continuation⟩
end Continuation

private def content : String := String.intercalate "\n" [
  "function wordMask(seed: Word) returns (Word) { let root = seed; let read: function() returns (Word) = lam() -> Word { return root; }; root ~=; return read(); }",
  "function doubleLoop(seed: Word) returns (Word) { let root = seed; for (let i = 0; i < 3; i += 1) { root ~=; root ~=; } return root; }",
  "function firstFault(seed: Word) returns (Word) { let root = seed; let gap: Word; root ~=; gap ~=; root = 99; return root; }"
]
private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Core.Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let started ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"unary bound resume {name}" (started.resume 400000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "bounded bare unary update" content
    ["wordMask", "doubleLoop", "firstFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let mask : SourceTypedRuntime.Value := .word (Core.Word.ofNatModulo 7).bitNot
  -- `read` copies `root` and `seed` when it is created, so `root ~=` reaches
  -- only `root` and the call returns the snapshot's 7.
  let cases : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value) := [
    ("wordMask", [wordValue 7], wordValue 7),
    ("doubleLoop", [wordValue 7], wordValue 7)]
  let baselines ← cases.mapM fun (name, arguments, _) => finish compiled name arguments 400000 initial
  let faultBaseline ← finish compiled "firstFault" [wordValue 7] 400000 initial
  for fuel in [0, 37, 400000] do
    for ((name, arguments, expected), baseline) in cases.zip baselines do
      let result ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr result == reprStr baseline)
        s!"unary resume observation changed {name}"
      match result with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"unary result {name}"
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
          s!"unary inert heap prefix {name}"
        SourceCoreUnifiedCorpusSupport.assertTrue
          (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"unary heap/capture safety {name}"
        if name == "wordMask" then
          -- `seed` and `root`, then the snapshot of `root` and `seed`.
          SourceCoreUnifiedCorpusSupport.assertTrue
            (reprStr (((final.heap.drop initial.heap.length).take 4).map (·.value)) ==
              reprStr [some (wordValue 7), some mask, some (wordValue 7), some (wordValue 7)])
            "unary write missed root or reached the captured snapshot"
      | other => throw (IO.userError s!"unary {name}: {reprStr other}")
    let result ← finish compiled "firstFault" [wordValue 7] fuel initial
    SourceCoreUnifiedCorpusSupport.assertTrue (reprStr result == reprStr faultBaseline) "unary fault resume changed"
    match result with
    | .fault (.invalidUnaryOperand .bitNot none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
        "unary fault inert prefix"
      SourceCoreUnifiedCorpusSupport.assertTrue
        (final.heap.any fun cell => match cell.value with
          | some (.word value) => value == (Core.Word.ofNatModulo 7).bitNot
          | _ => false) "unary fault lost prior write"
      SourceCoreUnifiedCorpusSupport.assertTrue (!(SourceCoreUnifiedCorpusSupport.hasWord final 99))
        "unary first fault ran continuation"
    | other => throw (IO.userError s!"unary first fault: {reprStr other}")
  IO.println "bounded bare unary: actual compiler, independent source trace, strict original continuation, seven typed slots, capture snapshot/loops/prior writes/fault/resume GREEN"
end Tests.SourceCoreRecursiveNamedBareBitNotBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedBitNotStatementBounds
/-! The existing bare unary Head exposes the independent source trace and
the actual strict native continuation. No expression child is invented for
the administrative Unit RHS. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedBitNotStatementBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

open SourceSemantics.CoreLowering
open CompatibleBitNotStatements

variable   {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {assignment : AssignmentResolution}
  (head : Head context scope assignment)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include environments heaps locals agrees actualTyped in
/-- The actual Head selects the native continuation below the outer budget;
source reconstruction, heap receipts and seven slots stay in the same branch. -/
theorem header_continuation_below (errors : head.Errors faults) (budget : Nat)
    {next : Expr} {output : Ty} {value : Core.Value} {finalStore : Store} {size : Nat}
    (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore)
    (within : size ≤ budget) :
    (∃ sourceSize reason after, SourceExecutionSize.SourcePlaceBitNotFaults program sourceSize context evidence source
      environment before assignment.target reason after) ∨
    (∃ sourceSize updated after written finalMap finalWorld slots remainingSize,
      SourceExecutionSize.SourcePlaceSnapshotUpdate program sourceSize context evidence source Dynamic.BitNotSnapshot
        environment before assignment.target updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      AdministrativePreserved mapping store finalMap written ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      remainingSize < budget ∧ EvaluationSize remainingSize (slots ++ actual) written
        (shift 7 (next.rename ξ)) value finalStore) := by
  cases Head.reflects_sized functions program evidence head environments heaps locals agrees actualTyped errors completed with
  | inl fault =>
    obtain ⟨sourceSize, reason, token, after, finalMap, finalWorld, trace, _rest⟩ := fault
    exact .inl ⟨sourceSize, reason, after, trace⟩
  | inr success =>
    obtain ⟨sourceSize, updated, after, written, finalMap, finalWorld, slots, remainingSize, trace, heaps, maps, worlds,
      frame, metadata, count, typed, smaller, continuation⟩ := success
    exact .inr ⟨sourceSize, updated, after, written, finalMap, finalWorld, slots, remainingSize, trace, heaps, frame, count,
      typed, Nat.lt_of_lt_of_le smaller within, continuation⟩

end Tests.SourceCoreRecursiveNamedBitNotStatementBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedCachedSupport
/-! Real bootstrap/cached-row consumers discharge the former syntax support
premise. Source syntax, child certificates and diagnostic interpretation remain
explicit; support does not certify source authority or execution. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCachedSupport
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory
open NativeExpressionContextSupport RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

variable (cached : SourceCoreUnifiedCompilation.Compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare cached = .ok recipe)
  (rows : List LambdaRow)
  (cachedRows : cached.indexed.secondPass.closures = rows.map LambdaRow.expression)
  (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
    cached.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
  (member : nativeEntry ∈ cached.indexed.entries)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (definitions : ambient.definitions = cached.indexed.layouts.definitions)
  {headers : Inventory cached.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {header : Header cached.indexed.ancestry values ambient.definitions program}
  (sameCache : header.compiled.closures = cached.indexed.secondPass.closures)
  (complete : Complete headers) (globals : header.globals = cached.indexed.base.globals.length)
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include recipeAccepted cachedRows ordered sameCache in
/-- This is the same selected full cached lambda used by native extraction. -/
theorem actual_support :
    supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code)
      (cached.indexed.base.globals.length + 1) = true :=
  RecursiveNamedCachedSupport.header_supported cached recipeAccepted rows cachedRows ordered sameCache

include member definitions sameCache complete globals recipeAccepted cachedRows ordered entry in
theorem actual_canonical :
    HasType (SourceCoreLocalCell.coreContext (bodyScope header) ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      header.body (LanguageResult.resultType header.output) ambient.definitions :=
  RecursiveNamedCachedSupport.canonical_body cached recipeAccepted rows cachedRows ordered member definitions sameCache complete globals entry

variable {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

include member definitions sameCache complete globals recipeAccepted cachedRows ordered entry in
/-- This consumer feeds the real prepared root's native proof into the single
compiler traversal, without requesting body/loop HasType at actual Γ. -/
theorem actual_extraction (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (closed : header.context.typeVariables = []) (residual : header.context.residualTypeVariables = false)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :=
  RecursiveNamedCachedSupport.extract cached recipeAccepted rows cachedRows ordered member definitions sameCache complete globals entry
    diagnosticPolicy registered prefixEq factory readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy
    syntaxTree closed residual sourceSignatures declarations projection accepted

/-- The selected receipt still owns the diagnostic obligations. -/
theorem actual_profile {diagnosticPolicy : AssignmentDiagnosticPolicy} {faults : FunctionCalls.FaultRep}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (interpreted : receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults) :=
  ⟨receipt.profile initialValid interpreted⟩

/-- Every binding construct lifts the mapping while leaving its own slot fixed. -/
theorem lambda_bound :
    supported ((Expr.lambda .unit .unit (.pair (.var 0) (.var 1))).rename (shift 7)) 8 = true ∧
    supported (.lambda .unit .unit (.pair (.var 0) (.var 1))) 1 = true := by decide

theorem case_bound :
    supported ((Expr.caseE (.var 0) (.pair (.var 0) (.var 1)) (.var 1)).rename (shift 7)) 8 = true ∧
    supported (.caseE (.var 0) (.pair (.var 0) (.var 1)) (.var 1)) 1 = true := by decide

theorem let_bound :
    supported ((Expr.letE (.var 0) (.lambda .unit .unit (.pair (.var 0) (.var 2)))).rename (shift 7)) 8 = true ∧
    supported (.letE (.var 0) (.lambda .unit .unit (.pair (.var 0) (.var 2)))) 1 = true := by decide

theorem match_bound :
    supported ((Expr.matchData ⟨0⟩ .unit (.var 0) [(.var 0), (.pair (.var 0) (.var 1))]).rename (shift 7)) 8 = true ∧
    supported (.matchData ⟨0⟩ .unit (.var 0) [(.var 0), (.pair (.var 0) (.var 1))]) 1 = true := by decide

/-- A collapsing renaming needs the explicit bound-reflection condition. -/
theorem collapsing_renaming :
    supported ((Expr.var 8).rename (fun _ => 0)) 1 = true ∧
    supported (.var 8) 1 = false ∧
    ¬ NativeExpressionRenamingSupport.ReflectsBound (fun _ => 0) 1 1 := by
  refine ⟨rfl, rfl, ?_⟩
  intro bound
  have := bound 8 (by decide)
  omega

/-- Syntactic support does not assert well-formed type annotations. -/
theorem support_is_not_annotation_typing :
    supported (.lambda (.namedData ⟨0⟩) (.namedData ⟨0⟩) (.var 0)) 0 = true ∧
    ¬ (Ty.namedData ⟨0⟩).WellFormed [] := by
  refine ⟨rfl, ?_⟩
  intro typed
  cases typed with
  | namedData found => simp at found

private def content : String := String.intercalate "\n" [
  "function step(n: Word) returns (Word) { return n + 1; }",
  "function self(n: Word) returns (Word) { if (n == 0) { return 0; } return self(n - 1); }",
  "function loop(n: Word) returns (Word) { let total = 0; for (let i = 0; i < n; i += 1) { total += step(i); } return total; }",
  "function down(n: Word) returns (Word) { while (n != 0) { n -= 1; } return n; }",
  "function assign(m: mapping(Bool => Word)) returns (Word) { m[true] = step(6); return m[true]; }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(value: Word) -> Word { seed += value; return seed; }; }",
  "function fail() returns (Word) { let saved = 17; let gap: Word; return gap; }",
  "function zero() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def bootstrap (state : Core.State) : IO (Value × Store) :=
  match runStateful 300000 state with
  | .done value store => pure (value, store)
  | other => throw (IO.userError s!"cached support bootstrap incomplete: {reprStr other}")

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let indexed := compiled.indexed
  let recipe ← get "actual support recipe" (SourceCoreIndexedSession.Recipe.prepare compiled)
  let rows ← indexed.secondPass.closures.mapM fun expression =>
    match expression with
    | .lambda parameter result body => pure (⟨parameter, result, body⟩ : LambdaRow)
    | _ => throw (IO.userError "actual support row not lambda")
  let canonical := initialEnvironment indexed.base.globals indexed.ancestry.layout.frame
  require (canonical.length == indexed.base.globals.length + 1) "support canonical length changed"
  require (rows.length > 1 && rows.length == indexed.base.globals.length) "support full ordered row count changed"
  let expected := RecursiveGlobalInitializationTyping.initialStore indexed.base.globals rows indexed.ancestry.layout.frame
  let (value, store) ← bootstrap (.initial recipe.bootstrap [] [])
  require (reprStr store == reprStr expected) "support complete initialized store changed"
  require (reprStr value == reprStr (Value.inRight .word .unit)) "support bootstrap result changed"
  for (row, slot) in rows.zipIdx do
    let signature ← match indexed.base.globals[slot]? with
      | some signature => pure signature
      | none => throw (IO.userError "support ordered signature missing")
    require (signature.functionType == .function row.parameter row.result) "support complete signature order changed"
    require (supported row.expression canonical.length) "cached lambda exceeds globals/frame support"
    for shiftCount in [0, 1, 7, 19] do
      require (supported (row.expression.rename (shift shiftCount)) (canonical.length + shiftCount))
        "actual cached renamed support lost binder boundary"
    match store.read? (RecursiveNamedCatalogInitialization.location indexed.base.globals slot) with
    | some (.inRight .unit (.closure parameter result body captured)) =>
      require (captured.length == slot + canonical.length) "support actual capture length changed"
      require (reprStr captured == reprStr (List.replicate slot Value.unit ++ canonical))
        "support full actual capture changed"
      require (reprStr body == reprStr (row.body.rename (shift slot).lift)) "support actual stored body changed"
      require (infer? (parameter :: captured.map Value.type) body indexed.layouts.definitions == some result)
        "support actual stored body native typing failed"
      require (supported body (captured.length + 1)) "stored native body support failed"
    | _ => throw (IO.userError "support initialized full closure missing")
  for fuel in [0, 1, 43, 300000] do
    let result ← match runStateful fuel (.initial recipe.bootstrap [] []) with
      | .done value store => pure (value, store)
      | .outOfFuel checkpoint => bootstrap checkpoint
      | other => throw (IO.userError s!"support bootstrap fault: {reprStr other}")
    require (reprStr result == reprStr (value, store)) "support full initialization resume changed"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "cached support public resume" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"support old cells changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"support full ordered cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "actual cached support" content
    ["self", "loop", "down", "assign", "make", "fail", "zero"]
  inspect compiled
  let mapping : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 31), (.bool true, w 91), (.bool false, w 4)]
  let updated : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 7), (.bool true, w 91), (.bool false, w 4)]
  let tests : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("self", [w 2], w 0, [(.word, some (w 2)), (.word, some (w 1)), (.word, some (w 0))]),
    ("loop", [w 2], w 3, [(.word, some (w 2)), (.word, some (w 3)), (.word, some (w 2)), (.word, some (w 0)), (.word, some (w 1))]),
    ("down", [w 2], w 0, [(.word, some (w 0))]),
    ("assign", [mapping], w 7, [(.mapping .bool .word, some updated), (.word, some (w 6))]),
    ("zero", [], .unit, [])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩, ⟨.bool, some (.bool false)⟩]}
  let baselines ← tests.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failed ← finish compiled "fail" [] 300000 initial
  for fuel in [0, 7, 43, 300000] do
    for (test, baseline) in tests.zip baselines do
      let (name, arguments, expected, expectedCells) := test
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"support full public resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"support result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"support expected success {name}")
    let observed ← finish compiled "fail" [] fuel initial
    require (reprStr observed == reprStr failed) "support first fault/resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final => cells initial final [(.word, some (w 17)), (.word, none)] "fail"
    | _ => throw (IO.userError "support first fault lost")
  IO.println "cached support: actual recipe, full ordered caches/captures, binder shifts, recursive/loop/assignment cells, first fault/resume GREEN"

end Tests.SourceCoreRecursiveNamedCachedSupport
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedExpressionBounds
/-! Original ordered argument and call derivations retain their strict child
costs. Concrete builtin lexical bodies discharge the pointwise body interface
at actual catalog entries. Cached executions check order, fault writes, raw
mapping metadata, by-value captures of a copied closure and resume. The whole
recursive expression and called-body correspondence remains a separate proof
boundary. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedExpressionBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds

#check_failure SourceTypedRuntime.run
#check_failure RecursiveNamedCatalog.Header.certificate
#check_failure RecursiveNamedCatalogInvocationBounds.BodyState.mk

section ConcreteBodies
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (body : BuiltinNamedCalls.Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include extension uninitialized missing faithful functionLeaves functionTypes in
/-- Concrete body meaning supplies every source budget, with the real frame
reference recovered from the all-target catalog entry. -/
theorem builtin_body_preserves_at [FunctionCalls.FaultTokens faults] (size : Nat) :
    BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      functions registry (Header.of_body body) faults size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry outcome after trace
  have reference : entry.canonical[(body.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + body.globals]? =
      some (.cellRef prepared.layout.frame.type frameLocation) := by
    simpa only [Header.of_body, List.length_map, List.length_reverse] using entry.reference
  have unmapped := entry.catalog.authority.unmapped
  rw [entry.catalog_frame] at unmapped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _⟩ :=
    body.certificate.preserves functions extension body.definitions_eq body.registered program body.valid body.unique
      uninitialized missing faithful functionLeaves functionTypes entry.environments entry.heaps entry.locals
      entry.lookups entry.actualTyped reference entry.state.read unmapped trace.sound
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata⟩

include extension uninitialized missing faithful functionLeaves functionTypes in
/-- Reflection consumes the original native body completion. The concrete
source derivation receives its own size after it has been reconstructed. -/
theorem builtin_body_reflects_at [FunctionCalls.FaultTokens faults] (size : Nat) :
    BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      functions registry (Header.of_body body) faults size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry value finalStore completed
  have reference : entry.canonical[(body.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + body.globals]? =
      some (.cellRef prepared.layout.frame.type frameLocation) := by
    simpa only [Header.of_body, List.length_map, List.length_reverse] using entry.reference
  have unmapped := entry.catalog.authority.unmapped
  rw [entry.catalog_frame] at unmapped
  obtain ⟨outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _⟩ :=
    body.certificate.reflects functions extension body.definitions_eq body.registered program body.valid body.unique
      uninitialized missing faithful functionLeaves functionTypes entry.environments entry.heaps entry.locals
      entry.lookups entry.actualTyped reference entry.state.read unmapped completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.BodyTrace.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, result, heaps, maps, worlds, frame, metadata⟩

variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {readFuel : Nat}
  {compilation : SourceCoreFunctions.Context}
  (callerValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
/-- One concrete installed body and concrete recursive builtin arguments close
the bounded head, without an external child or body execution premise. -/
theorem builtin_named_preserves_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context
        (CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt)) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionHeadBounds.preserves_at functions budget size within unique owners
  · exact RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed _
        (CompatibleExpressionBuiltins.preserves functions extension faithful functionLeaves functionTypes
          program evidence callerValid unique callerUninitialized callerMissing)) budget
  · intro header member child _
    have same : header = Header.of_body body := by simpa only [List.mem_singleton] using member
    subst header
    intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after trace
    exact builtin_body_preserves_at (headers := [Header.of_body body]) (locations := locations) (capturePrefix := capturePrefix) functions extension body uninitialized missing faithful functionLeaves functionTypes child entry trace

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
/-- Original native completion reflects through the concrete argument and body
proofs; the reconstructed source expression has a separate finite cost. -/
theorem builtin_named_reflects_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context
        (CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt)) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionHeadBounds.reflects_at functions budget size within
  · exact RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed _
        (CompatibleExpressionBuiltins.reflects functions extension faithful functionLeaves functionTypes
          program evidence callerValid callerUninitialized callerMissing)) budget
  · intro header member child _
    have same : header = Header.of_body body := by simpa only [List.mem_singleton] using member
    subst header
    intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore completed
    exact builtin_body_reflects_at (headers := [Header.of_body body]) (locations := locations) (capturePrefix := capturePrefix) functions extension body uninitialized missing faithful functionLeaves functionTypes child entry completed
end ConcreteBodies

section OriginalSource
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {caller invocation : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
  {instantiation : DeclarationInstantiation} {id : ExpressionId} {ids : List ExpressionId}
  {value : Dynamic.Value} {reason : Dynamic.SemanticFault} {first second whole : Nat}

/-- A later argument fault keeps the successful first argument and both
original costs strictly below the containing named expression. -/
theorem later_argument_fault_children
    (head : SourceExecutionSize.ExpressionEvaluates program first context caller source environment before id value middle)
    (tail : SourceExecutionSize.ExpressionsFault program second context caller source environment middle ids reason after)
    (within : SourceExecutionSize.stepSize [first, second] < whole) :
    RecursiveNamedArgumentTraceBounds.TraceAt program context caller invocation source environment before
      (id :: ids) instantiation whole (.fault reason) after ∧ first < whole ∧ second < whole :=
  ⟨.argumentFault (.tail head tail) within,
    Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) within,
    Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) within⟩

/-- Success and body fault share the same ordered argument prefix, while the
retained call outcome supplies a different strictly smaller child. -/
theorem call_children
    {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program first context caller source environment before ids arguments middle)
    (callTrace : RecursiveNamedCallBounds.CallOutcome program second context caller invocation middle
      (.global ⟨instantiation, invocation⟩) arguments outcome after)
    (firstBelow : first < whole) (secondBelow : second < whole) :
    RecursiveNamedArgumentTraceBounds.TraceAt program context caller invocation source environment before
      ids instantiation whole outcome after :=
  .apply argumentsTrace callTrace firstBelow secondBelow
end OriginalSource

private def content : String := String.intercalate "\n" [
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function take(a: Word, b: Word) returns (Word) { return a - b; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function failAfter(a: Word) returns (Word) { let written = a + 10; let gap: Word; return gap; }",
  "function ordered() returns (Word) { return take(side(7), side(3)); }",
  "function firstFault() returns (Word) { return take(fail(), side(7)); }",
  "function laterFault() returns (Word) { return take(side(7), fail()); }",
  "function bodyFault() returns (Word) { return failAfter(side(7)); }",
  "function mapLeaf(raw: mapping((Bool, Bool) => Word)) returns (mapping((Bool, Bool) => Word)) { return raw; }",
  "function rawEcho(raw: mapping((Bool, Bool) => Word)) returns (mapping((Bool, Bool) => Word)) { return mapLeaf(raw); }",
  "function defaulted() returns (Word) { let raw: mapping((Bool, Bool) => Word); return raw[(true, false)]; }",
  "function alias(n: Word) returns (function(Word) returns (Word)) { let captured = n; return lam(x: Word) -> Word { captured += x; return captured; }; }",
  "function aliases(n: Word) returns (Word) { let first = alias(n); let second = first; let a = first(2); return a + second(3); }",
  "function self(n: Word) returns (Word) { return n == 0 ? 2 : self(n - 1) + 1; }",
  "function left(n: Word) returns (Word) { return n == 0 ? 7 : right(n - 1); }",
  "function right(n: Word) returns (Word) { return n == 0 ? 11 : left(n - 1); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"named bound resume {name}" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"named bound prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"named bound ordered cells changed {label}: {reprStr final.heap}"

private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "named bound fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "named bound exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named expression bounds" content
    ["ordered", "firstFault", "laterFault", "bodyFault", "rawEcho", "defaulted", "aliases", "self", "left", "right"]
  let keyType : TypeSystem.Ty := .product .bool .bool
  let mapType : TypeSystem.Ty := .mapping keyType .word
  let key : SourceTypedRuntime.Value := .product (.bool true) (.bool false)
  let raw : SourceTypedRuntime.Value := .mapping (.comptime keyType) (.comptime .word)
    [(key, w 37), (key, w 91)]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 819)⟩]}
  let gap ← faultBinder compiled "fail"
  let afterGap ← faultBinder compiled "failAfter"
  -- `second` copies the closure `first`. Each call starts again from the
  -- snapshot `captured = 5` taken when `alias` created it: 7 + 8.
  let cases : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value) := [
    ("ordered", [], w 4), ("rawEcho", [raw], raw), ("defaulted", [], w 0),
    ("aliases", [w 5], w 15), ("self", [w 3], w 5), ("left", [w 2], w 7), ("right", [w 2], w 11)]
  let completed ← cases.mapM fun (name, arguments, _) => finish compiled name arguments 300000 initial
  let faultNames := ["firstFault", "laterFault", "bodyFault"]
  let faults ← faultNames.mapM fun name => finish compiled name [] 300000 initial
  for fuel in [0, 43, 300000] do
    for ((name, arguments, expected), baseline) in cases.zip completed do
      let observation ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"named bound full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected)
          s!"named bound result changed {name}: {reprStr actual}"
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
          s!"named bound inert prefix changed {name}"
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"named bound unsafe source heap {name}"
        if name == "ordered" then
          cells initial final [(.word, some (w 7)), (.word, some (w 7)),
            (.word, some (w 3)), (.word, some (w 3)), (.word, some (w 7)), (.word, some (w 3))] name
        if name == "rawEcho" then cells initial final [(mapType, some raw), (mapType, some raw)] name
      | other => throw (IO.userError s!"named bound {name}: {reprStr other}")
    for (name, baseline) in faultNames.zip faults do
      let observation ← finish compiled name [] fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"named bound full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == if name == "bodyFault" then afterGap else gap)
          "named bound fault lost exact source binder"
        let earlier := if name == "firstFault" then [] else [(.word, some (w 7)), (.word, some (w 7))]
        let inner := if name == "bodyFault" then [(.word, some (w 7)), (.word, some (w 17))]
          else [(.word, some (w 5))]
        cells initial final (earlier ++ inner ++ [(.word, none)]) name
      | other => throw (IO.userError s!"named bound fault {name}: {reprStr other}")
  IO.println "recursive named expression bounds: original child costs, concrete body budgets, all-target frame restoration, ordered arguments, first faults, raw metadata, by-value closure copies and native resume GREEN"
end Tests.SourceCoreRecursiveNamedExpressionBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedDataExpressionBounds
/-! Concrete named/builtin leaves discharge the inclusive data-head contracts.
Actual constructor/index compilation checks raw metadata, ordered effects and
faults. Positional members use retained typed IR and the actual branch generator;
the surface parser's syntax is not enlarged. Whole Tree/callee closure is later. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedDataExpressionBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds
open CompatibleExpressionTypedCompositions

#check_failure RecursiveNamedDataExpressionHeadBounds.Tree
#check_failure RecursiveNamedDataExpressionHeadBounds.BodyMeaning
#check_failure SourceTypedRuntime.run

section ConcreteBodies
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (body : BuiltinNamedCalls.Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {readFuel : Nat}
  {compilation : SourceCoreFunctions.Context}
  (callerValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))


private def Leaf : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  RecursiveNamedCatalog.Head [Header.of_body body] compilation source context
    (CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt) scope id lowered ∨
  CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
theorem leaf_preserves_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered certificate
  change _ ∨ _ at certificate
  cases certificate with
  | inl named =>
    exact SourceCoreRecursiveNamedExpressionBounds.builtin_named_preserves_at functions extension body uninitialized missing faithful functionLeaves functionTypes
      callerValid unique owners callerUninitialized callerMissing budget size within named
  | inr builtin =>
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed _
        (CompatibleExpressionBuiltins.preserves functions extension faithful functionLeaves functionTypes
          program evidence callerValid unique callerUninitialized callerMissing)) size builtin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
theorem leaf_reflects_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered certificate
  change _ ∨ _ at certificate
  cases certificate with
  | inl named =>
    exact SourceCoreRecursiveNamedExpressionBounds.builtin_named_reflects_at functions extension body uninitialized missing faithful functionLeaves functionTypes
      callerValid callerUninitialized callerMissing budget size within named
  | inr builtin =>
    exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed _
        (CompatibleExpressionBuiltins.reflects functions extension faithful functionLeaves functionTypes
          program evidence callerValid callerUninitialized callerMissing)) size builtin


private def Calls : CompatibleExpressionCalls.CallHeads :=
  RecursiveNamedCatalog.Head [Header.of_body body] compilation source context

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
theorem data_preserves_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedDataExpressionHeadBounds.Certificate
        (Calls body (source := source) (context := context) (compilation := compilation)) values source context reasonAt
        (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedDataExpressionHeadBounds.preserves_at functions extension faithful functionLeaves functionTypes
    program evidence unique callerMissing entry_transport budget size within
  intro child childWithin
  exact leaf_preserves_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid unique owners callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
theorem data_reflects_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedDataExpressionHeadBounds.Certificate
        (Calls body (source := source) (context := context) (compilation := compilation)) values source context reasonAt
        (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedDataExpressionHeadBounds.reflects_at functions extension faithful functionLeaves functionTypes
    program evidence callerMissing entry_transport budget size within
  intro child childWithin
  exact leaf_reflects_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
/-- A primitive parent consumes the same data-head budget. -/
theorem parent_preserves_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source
        (RecursiveNamedDataExpressionHeadBounds.Certificate
          (Calls body (source := source) (context := context) (compilation := compilation)) values source context reasonAt
          (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionCompositionsBounds.Head.preserves_at (faults := faults) functions program evidence entry_transport budget size within unique
  intro child childWithin
  exact data_preserves_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid unique owners callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
theorem parent_reflects_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source
        (RecursiveNamedDataExpressionHeadBounds.Certificate
          (Calls body (source := source) (context := context) (compilation := compilation)) values source context reasonAt
          (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionCompositionsBounds.Head.reflects_at (faults := faults) functions program evidence entry_transport budget size within
  intro child childWithin
  exact data_reflects_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid callerUninitialized callerMissing budget child childWithin
end ConcreteBodies

private def content : String := String.intercalate "\n" [
  "enum Box { Box(Bool) }", "enum Row { Row(Word, Bool) }",
  "enum Key { Key(Bool) }", "enum Missing { Missing(Word) }",
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function truth(flag: Bool) returns (Bool) { let saved = flag; return saved; }",
  "function failWord() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function badBool() returns (Bool) { let written = 19; let gap: Bool; return gap; }",
  "function filled() returns (mapping(Bool => Bool)) { let m: mapping(Bool => Bool); m[true] = true; return m; }",
  "function empty() returns (mapping(Bool => Bool)) { let m: mapping(Bool => Bool); return m; }",
  "function badMap() returns (mapping(Bool => Bool)) { let written = 23; let gap: Word; gap; let m: mapping(Bool => Bool); return m; }",
  "function single() returns (Box) { return Box(truth(true)); }",
  "function row() returns (Row) { return Row(side(7), truth(false)); }",
  "function nominalKey() returns (Bool) { let m: mapping(Key => Bool); return m[Key(truth(true))]; }",
  "function productKey() returns (Bool) { let m: mapping((Bool, Bool) => Bool); return m[(truth(true), truth(false))]; }",
  "function duplicate(m: mapping((Bool, Bool) => Bool)) returns (Bool) { return m[(truth(true), truth(false))]; }",
  "function baseIndex() returns (Bool) { return filled()[truth(true)]; }",
  "function lazyIndex() returns (Bool) { return empty()[truth(true)]; }",
  "function operatorParent() returns (Bool) { return !filled()[truth(true)]; }",
  "function constructorFirstFault() returns (Row) { return Row(failWord(), truth(false)); }",
  "function constructorLaterFault() returns (Row) { return Row(side(7), badBool()); }",
  "function baseFault() returns (Bool) { return badMap()[truth(true)]; }",
  "function keyFault() returns (Bool) { return filled()[badBool()]; }",
  "function defaultFault() returns (Missing) { let m: mapping(Bool => Missing); return m[truth(true)]; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"data bound resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"data bound prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"data bound ordered cells changed {label}: {reprStr final.heap}"
private def constructor (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO DataConstructorInstantiation := do
  let signature ← match compiled.sourceProgram.signatures.dataTypes.filter (·.name == name) with
    | [signature] => pure signature | _ => throw (IO.userError "data bound nominal signature missing")
  let selected ← match signature.constructors with
    | [selected] => pure selected | _ => throw (IO.userError "data bound constructor missing")
  pure ⟨selected.id, [], selected.payloadTypes, .nominal signature.id []⟩
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "data bound fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "data bound exact fault binder missing")

/-- The real cached named call supplies the base. The actual retained member
branch generator selects both fields, with the same complete native store. -/
private def retainedMembers (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "row"
  let entry ← match compiled.indexed.find? key with
    | some entry => pure entry | none => throw (IO.userError "data bound member entry missing")
  let baseCode ← SourceCoreUnifiedCorpusSupport.get "data bound actual named base"
    (SourceCoreCallableIndexedPrograms.assembleCall compiled.indexed.ancestry compiled.indexed.secondPass.closures key ⟨.unit, LanguageResult.success .unit⟩)
  let specialized ← SourceCoreUnifiedCorpusSupport.get "data bound member retained base"
    (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan key)
  let original ← match specialized.function.typedBody.nodes.findSome? fun
    | .expression node => match node.form with | .constructor .. => some node | _ => none
    | _ => none with
    | some node => pure node | none => throw (IO.userError "data bound member source constructor missing")
  let baseline := Core.runStateful 300000 (.initial baseCode [] [])
  let baselineStore ← match baseline with
    | .done (.inRight .word _) store => pure store
    | other => throw (IO.userError s!"data bound member actual base failed: {reprStr other}")
  for (position, result, raw, expected) in [(0, Ty.word, TypeSystem.Ty.word, Value.word (Word.ofNatModulo 7)), (1, Ty.bool, TypeSystem.Ty.bool, Value.bool false)] do
    let member : ExpressionNode := {original with id := ⟨⟨original.id.occurrence.owner, 100000 + position⟩⟩, type := raw, form := .member original.id (toString position) position}
    let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
    let (identity, branches) ← SourceCoreUnifiedCorpusSupport.get "data bound member actual branches"
      (SourceCoreCompatibleDataExpressions.memberBranches values member original.type result position)
    let code := SourceCoreDataExpressions.member identity result branches baseCode
    let native ← SourceCoreUnifiedCorpusSupport.get "data bound member actual Core checker"
      (SourceCoreGeneralEntry.NativeEntry.compile compiled.indexed.layouts.definitions [] result code)
    SourceCoreUnifiedCorpusSupport.assertTrue (entry.native.resultType == .namedData identity)
      "data bound member lost base nominal type"
    for fuel in [0, 43, 300000] do
      let first ← SourceCoreUnifiedCorpusSupport.get "data bound member native call" (native.run [] fuel)
      let completed := match first.checkpoint? with | some checkpoint => checkpoint.resume 300000 | none => first
      match completed.observation with
      | .succeeded actual store =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == expected && reprStr store == reprStr baselineStore)
          "data bound member changed selected value or named effect store"
      | other => throw (IO.userError s!"data bound member native result failed: {reprStr other}")

def run : IO Unit := do
  let names := ["single", "row", "nominalKey", "productKey", "duplicate", "baseIndex", "lazyIndex", "operatorParent",
    "constructorFirstFault", "constructorLaterFault", "baseFault", "keyFault", "defaultFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named data bounds" content names
  let box ← constructor compiled "Box"
  let row ← constructor compiled "Row"
  let key ← constructor compiled "Key"
  let missing ← constructor compiled "Missing"
  let duplicate : SourceTypedRuntime.Value := .mapping (.product .bool .bool) .bool
    [(.product (.bool true) (.bool false), .bool false), (.product (.bool true) (.bool false), .bool true)]
  let filled : SourceTypedRuntime.Value := .mapping .bool .bool [(.bool true, .bool true)]
  let empty : SourceTypedRuntime.Value := .mapping .bool .bool []
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("single", [], .constructed box [.bool true], [(.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("row", [], .constructed row [w 7, .bool false], [(.word, some (w 7)), (.word, some (w 7)), (.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("nominalKey", [], .bool false, [(.mapping key.resultType .bool, some (.mapping key.resultType .bool [])), (.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("productKey", [], .bool false, [(.mapping (.product .bool .bool) .bool, some (.mapping (.product .bool .bool) .bool [])), (.bool, some (.bool true)), (.bool, some (.bool true)), (.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("duplicate", [duplicate], .bool false, [(.mapping (.product .bool .bool) .bool, some duplicate), (.bool, some (.bool true)), (.bool, some (.bool true)), (.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("baseIndex", [], .bool true, [(.mapping .bool .bool, some filled), (.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("lazyIndex", [], .bool false, [(.mapping .bool .bool, some empty), (.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("operatorParent", [], .bool false, [(.mapping .bool .bool, some filled), (.bool, some (.bool true)), (.bool, some (.bool true))])]
  let failures := ["constructorFirstFault", "constructorLaterFault", "baseFault", "keyFault", "defaultFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 819)⟩]}
  let wordGap ← faultBinder compiled "failWord"
  let boolGap ← faultBinder compiled "badBool"
  let mapGap ← faultBinder compiled "badMap"
  let completed ← successes.mapM fun test => finish compiled test.1 test.2.1 300000 initial
  let failed ← failures.mapM fun name => finish compiled name [] 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip completed do
      let (name, arguments, expected, expectedCells) := test
      let observation ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"data bound full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"data bound result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"data bound source heap not deeply safe {name}"
      | other => throw (IO.userError s!"data bound {name}: {reprStr other}")
    for (name, baseline) in failures.zip failed do
      let observation ← finish compiled name [] fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"data bound full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        let expectedId := if name == "constructorFirstFault" then wordGap else if name == "baseFault" then mapGap else boolGap
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == expectedId) "data bound fault lost source binder"
        let expectedCells := match name with
          | "constructorFirstFault" => [(.word, some (w 5)), (.word, none)]
          | "constructorLaterFault" => [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 19)), (.bool, none)]
          | "baseFault" => [(.word, some (w 23)), (.word, none)]
          | _ => [(.mapping .bool .bool, some filled), (.word, some (w 19)), (.bool, none)]
        cells initial final expectedCells name
      | .fault (.typeMismatch raw none) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (name == "defaultFault" && raw == missing.resultType)
          "data bound missing default lost raw nominal metadata"
        cells initial final [(.mapping .bool missing.resultType, some (.mapping .bool missing.resultType [])), (.bool, some (.bool true)), (.bool, some (.bool true))] name
      | other => throw (IO.userError s!"data bound fault {name}: {reprStr other}")
  retainedMembers compiled
  IO.println "recursive named data bounds: original strict children, inclusive single pack, constructors/member/index, raw metadata, first lookup/effects/faults and resume GREEN"
end Tests.SourceCoreRecursiveNamedDataExpressionBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedExpressionCompositionsBounds
/-! Concrete named and builtin leaves discharge pointwise head obligations.
Two applications use the same finite budget, including unchanged group code.
The runtime corpus checks named calls under each composition, short circuit
and first-fault effects. Whole recursive Tree closure is a later unit. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedExpressionCompositionsBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds
open CompatibleExpressionTypedCompositions

#check_failure RecursiveNamedExpressionCompositionsBounds.Through
#check_failure RecursiveNamedExpressionCompositionsBounds.Tree
#check_failure SourceTypedRuntime.run

section ConcreteBodies
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (body : BuiltinNamedCalls.Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {readFuel : Nat}
  {compilation : SourceCoreFunctions.Context}
  (callerValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))


private def Leaf : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  RecursiveNamedCatalog.Head [Header.of_body body] compilation source context
    (CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt) scope id lowered ∨
  CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
theorem leaf_preserves_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered certificate
  change _ ∨ _ at certificate
  cases certificate with
  | inl named =>
    exact SourceCoreRecursiveNamedExpressionBounds.builtin_named_preserves_at functions extension body uninitialized missing faithful functionLeaves functionTypes
      callerValid unique owners callerUninitialized callerMissing budget size within named
  | inr builtin =>
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed _
        (CompatibleExpressionBuiltins.preserves functions extension faithful functionLeaves functionTypes
          program evidence callerValid unique callerUninitialized callerMissing)) size builtin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
theorem leaf_reflects_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered certificate
  change _ ∨ _ at certificate
  cases certificate with
  | inl named =>
    exact SourceCoreRecursiveNamedExpressionBounds.builtin_named_reflects_at functions extension body uninitialized missing faithful functionLeaves functionTypes
      callerValid callerUninitialized callerMissing budget size within named
  | inr builtin =>
    exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed _
        (CompatibleExpressionBuiltins.reflects functions extension faithful functionLeaves functionTypes
          program evidence callerValid callerUninitialized callerMissing)) size builtin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
/-- Head composition consumes concrete leaf proofs at the inclusive budget. -/
theorem composed_preserves_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionCompositionsBounds.Head.preserves_at (faults := faults) functions program evidence
    entry_transport budget size within unique
  intro child childWithin
  exact leaf_preserves_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid unique owners callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
/-- Reflection reconstructs source costs independently of native costs. -/
theorem composed_reflects_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionCompositionsBounds.Head.reflects_at (faults := faults) functions program evidence
    entry_transport budget size within
  intro child childWithin
  exact leaf_reflects_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
/-- A second structural layer keeps the same budget, even for groups. -/
theorem twice_preserves_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source (Head values.checked source
        (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionCompositionsBounds.Head.preserves_at (faults := faults) functions program evidence
    entry_transport budget size within unique
  intro child childWithin
  exact composed_preserves_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid unique owners callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
theorem twice_reflects_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source (Head values.checked source
        (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionCompositionsBounds.Head.reflects_at (faults := faults) functions program evidence
    entry_transport budget size within
  intro child childWithin
  exact composed_reflects_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid callerUninitialized callerMissing budget child childWithin
end ConcreteBodies

private def content : String := String.intercalate "\n" [
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function truth(flag: Bool) returns (Bool) { let saved = flag; return saved; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function badBool() returns (Bool) { let written = 19; let gap: Bool; return gap; }",
  "function grouped() returns (Word) { return ((side(7))); }",
  "function paired() returns ((Word, Word)) { return (side(7), side(3)); }",
  "function unary() returns (Bool) { return !truth(false); }",
  "function strict() returns (Word) { return side(7) - side(3); }",
  "function choose() returns (Word) { return truth(false) ? fail() : side(11); }",
  "function chooseTrue() returns (Word) { return truth(true) ? side(13) : fail(); }",
  "function andSkip() returns (Bool) { return truth(false) && badBool(); }",
  "function andNext() returns (Bool) { return truth(true) && truth(false); }",
  "function orSkip() returns (Bool) { return truth(true) || badBool(); }",
  "function orNext() returns (Bool) { return truth(false) || truth(true); }",
  "function firstFault() returns (Word) { return fail() + side(7); }",
  "function laterFault() returns (Word) { return side(7) + fail(); }",
  "function conditionFault() returns (Word) { return badBool() ? side(13) : side(11); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (fuel : Nat)
    (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"composition bound resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"composition bound prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"composition bound ordered cells changed {label}: {reprStr final.heap}"
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "composition bound fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "composition bound exact fault binder missing")

def run : IO Unit := do
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("grouped", w 7, [(.word, some (w 7)), (.word, some (w 7))]),
    ("paired", .product (w 7) (w 3), [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 3)), (.word, some (w 3))]),
    ("unary", .bool true, [(.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("strict", w 4, [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 3)), (.word, some (w 3))]),
    ("choose", w 11, [(.bool, some (.bool false)), (.bool, some (.bool false)), (.word, some (w 11)), (.word, some (w 11))]),
    ("chooseTrue", w 13, [(.bool, some (.bool true)), (.bool, some (.bool true)), (.word, some (w 13)), (.word, some (w 13))]),
    ("andSkip", .bool false, [(.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("andNext", .bool false, [(.bool, some (.bool true)), (.bool, some (.bool true)), (.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("orSkip", .bool true, [(.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("orNext", .bool true, [(.bool, some (.bool false)), (.bool, some (.bool false)), (.bool, some (.bool true)), (.bool, some (.bool true))])]
  let failures := ["firstFault", "laterFault", "conditionFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named composition bounds" content
    (successes.map (fun test => test.1) ++ failures)
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 819)⟩]}
  let gap ← faultBinder compiled "fail"
  let boolGap ← faultBinder compiled "badBool"
  let completed ← successes.mapM fun test => finish compiled test.1 300000 initial
  let failed ← failures.mapM fun name => finish compiled name 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip completed do
      let (name, expected, expectedCells) := test
      let observation ← finish compiled name fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"composition bound full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"composition bound result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"composition bound unsafe source heap {name}"
      | other => throw (IO.userError s!"composition bound {name}: {reprStr other}")
    for (name, baseline) in failures.zip failed do
      let observation ← finish compiled name fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"composition bound full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == if name == "conditionFault" then boolGap else gap)
          "composition bound fault lost source binder"
        let earlier := if name == "laterFault" then [(.word, some (w 7)), (.word, some (w 7))] else []
        let inner := if name == "conditionFault" then [(.word, some (w 19)), (.bool, none)] else [(.word, some (w 5)), (.word, none)]
        cells initial final (earlier ++ inner) name
      | other => throw (IO.userError s!"composition bound fault {name}: {reprStr other}")
  IO.println "recursive named composition bounds: inclusive structural budgets, original strict source/native children, all five heads, ordered effects, skip/fault and resume GREEN"
end Tests.SourceCoreRecursiveNamedExpressionCompositionsBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedBuiltinBounds
/-! Contracted builtin heads consume concrete named or builtin argument proofs
within one finite bound. Runtime fixtures verify ordered argument writes,
conversion and public faults independently of the formal cost measure. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedBuiltinBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds

#check_failure RecursiveNamedBuiltinHeadBounds.Tree
#check_failure SourceTypedRuntime.run

section ConcreteBodies
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (body : BuiltinNamedCalls.Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {readFuel : Nat}
  {compilation : SourceCoreFunctions.Context}
  (callerValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))


def Leaf : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  RecursiveNamedCatalog.Head [Header.of_body body] compilation source context
    (CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt) scope id lowered ∨
  CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
/-- The argument obligation is closed by the concrete singleton body grammar. -/
theorem contracted_preserves_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (BuiltinCalls.Typed.Head values source (Leaf body (source := source) (context := context) (compilation := compilation)
        (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedBuiltinHeadBounds.Head.preserves_at (functions := functions) (functionLeaves := functionLeaves)
    (program := program) (evidence := evidence) (unique := unique) (transport := entry_transport) budget size within
  intro child childWithin
  exact SourceCoreRecursiveNamedExpressionCompositionsBounds.leaf_preserves_at functions extension body
    uninitialized missing faithful functionLeaves functionTypes callerValid unique owners
    callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
/-- Native argument completion reconstructs an independently sized Source call. -/
theorem contracted_reflects_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (BuiltinCalls.Typed.Head values source (Leaf body (source := source) (context := context) (compilation := compilation)
        (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedBuiltinHeadBounds.Head.reflects_at (functions := functions) (functionLeaves := functionLeaves)
    (program := program) (evidence := evidence) (transport := entry_transport) budget size within
  intro child childWithin
  exact SourceCoreRecursiveNamedExpressionCompositionsBounds.leaf_reflects_at functions extension body
    uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
    budget child childWithin
end ConcreteBodies

private def content : String := String.intercalate "\n" [
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function wordSide(n: Word) returns (Word) { let saved = n; return saved; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function ordered() returns (integer) { return integerSub(wordToInteger(side(7)), wordToInteger(side(3))); }",
  "function converted() returns (integer) { return wordToInteger(wordFromInteger(integerSub(wordToInteger(side(0)), wordToInteger(side(9))))); }",
  "function fromWord() returns (integer) { return wordToInteger(wordSide(11)); }",
  "function nested() returns (integer) { return integerAdd(wordToInteger(wordSide(7)), integerSub(wordToInteger(side(9)), wordToInteger(side(3)))); }",
  "function firstFault() returns (integer) { return integerAdd(wordToInteger(fail()), wordToInteger(side(99))); }",
  "function laterFault() returns (integer) { return integerAdd(wordToInteger(side(7)), wordToInteger(fail())); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (fuel : Nat)
    (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"builtin bound resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"builtin bound prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"builtin bound ordered cells changed {label}: {reprStr final.heap}"
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "builtin bound fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "builtin bound exact fault binder missing")

def run : IO Unit := do
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("ordered", .integer 4, [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 3)), (.word, some (w 3))]),
    ("converted", .integer (Int.ofNat (Word.ofIntModulo (-9)).val), [(.word, some (w 0)), (.word, some (w 0)), (.word, some (w 9)), (.word, some (w 9))]),
    ("fromWord", .integer 11, [(.word, some (w 11)), (.word, some (w 11))]),
    ("nested", .integer 13, [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 9)), (.word, some (w 9)), (.word, some (w 3)), (.word, some (w 3))])]
  let failures := ["firstFault", "laterFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named builtin bounds" content
    (successes.map (fun test => test.1) ++ failures)
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 819)⟩]}
  let gap ← faultBinder compiled
  let completed ← successes.mapM fun test => finish compiled test.1 300000 initial
  let failed ← failures.mapM fun name => finish compiled name 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip completed do
      let (name, expected, expectedCells) := test
      let observation ← finish compiled name fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"builtin bound full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"builtin bound result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"builtin bound unsafe source heap {name}"
      | other => throw (IO.userError s!"builtin bound {name}: {reprStr other}")
    for (name, baseline) in failures.zip failed do
      let observation ← finish compiled name fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"builtin bound full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "builtin bound fault lost source binder"
        let earlier := if name == "laterFault" then [(.word, some (w 7)), (.word, some (w 7))] else []
        cells initial final (earlier ++ [(.word, some (w 5)), (.word, none)]) name
      | other => throw (IO.userError s!"builtin bound fault {name}: {reprStr other}")
  IO.println "recursive named builtin bounds: real contracted arguments, fixed bound, independent Source sizes, ordered effects, first/later faults and resume GREEN"
end Tests.SourceCoreRecursiveNamedBuiltinBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedExpressionExtraChildren
/-! Actual predecessor-fuel receipts feed the existing compiler fold. These
formal consumers retain callee-first order and duplicate arguments. Static
source typing and the indirect head receipt remain separate obligations;
no source execution, stage acceptance or called-body meaning is inferred. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedExpressionExtraChildren
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCallSelectionCertificates
open RecursiveNamedExpressionCompilerCertificates CallableIndirectCallCertificates

/-- Only actual indirect child positions use the new extra admission field. -/
def indirectForm : ExpressionForm → Prop
  | .call _ _ (.indirect _) => True
  | _ => False

def indirectChildren : ExpressionForm → List ExpressionId
  | .call callee arguments (.indirect _) => callee :: arguments
  | _ => []

section ActualReceipt
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreBasic.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered)

/-- The parent uses the successor; all actual vector entries use exactly its
predecessor, including repeated argument IDs and the leading callee. -/
theorem actual_predecessor_fuel :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id reasonAt = .ok lowered ∧
    ∀ child code, (child, code) ∈ receipt.entries →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt = .ok code :=
  ⟨receipt.accepted, receipt.ordered_children.2⟩

theorem actual_ordered_positions : receipt.entries.map Prod.fst = callee :: arguments := by
  have count := receipt.ordered_children.1
  simp only [Receipt.entries, List.map_cons, List.map_fst_zip (Nat.le_of_eq count)]

/-- Full original metadata and policy-read metadata stay distinct. -/
theorem actual_metadata :
    source.lookupExpression? id = some receipt.original ∧
    receipt.original.form = .call callee arguments (.indirect metadata) ∧
    policy.readExpression source id = .ok (receipt.node, receipt.type) ∧
    metadata.argumentCoercions = [] :=
  ⟨receipt.found, receipt.originalForm, receipt.read, receipt.argumentCoercions⟩

theorem actual_branch_receipt {context : SourceSemantics.Context}
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (head : calls (CompatibleExpressionCalls.Entries scope receipt.entries) scope id lowered)
    (sourceTypes : ∀ child code, (child, code) ∈ receipt.entries → ∃ childNode,
      source.lookupExpression? child = some childNode ∧ ExpressionHasType source context child childNode.type) :
    ∃ entries : List (ExpressionId × SourceCoreBasic.LoweredExpr),
      calls (CompatibleExpressionCalls.Entries scope entries) scope id lowered ∧
      entries.map Prod.fst = indirectChildren receipt.original.form ∧
      ∀ child code, (child, code) ∈ entries → ∃ childNode,
        source.lookupExpression? child = some childNode ∧
        ExpressionHasType source context child childNode.type ∧
        SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt = .ok code := by
  refine ⟨receipt.entries, head, ?_, ?_⟩
  · rw [receipt.originalForm]
    exact actual_ordered_positions receipt
  · intro child code member
    obtain ⟨childNode, found, typed⟩ := sourceTypes child code member
    exact ⟨childNode, found, typed, receipt.ordered_children.2 child code member⟩

/-- Actual repeated argument IDs remain three physical ordered vector slots. -/
theorem actual_repeated_positions (argument : ExpressionId) (repeated : arguments = [argument, argument]) :
    receipt.entries.map Prod.fst = [callee, argument, argument] ∧ receipt.entries.length = 3 := by
  constructor
  · rw [actual_ordered_positions receipt, repeated]
  · have count := congrArg List.length (actual_ordered_positions receipt)
    simpa only [List.length_map, repeated, List.length_cons, List.length_nil] using count

/-- Empty arguments retain the actual callee compiler result as the one child. -/
theorem actual_empty_arguments (empty : arguments = []) :
    receipt.entries = [(callee, receipt.calleeCode)] := by
  cases empty
  rfl

theorem actual_admitted_entries {admitted : ExpressionId → Prop}
    (admission : AdmissionWith indirectForm indirectChildren source admitted) (allowed : admitted id) :
    ∀ child code, (child, code) ∈ receipt.entries → admitted child := by
  intro child code member
  have form : indirectForm receipt.original.form := by rw [receipt.originalForm]; trivial
  apply admission.extra_children id receipt.original allowed receipt.found form child
  rw [← (show receipt.entries.map Prod.fst = indirectChildren receipt.original.form from by
    rw [receipt.originalForm]; exact actual_ordered_positions receipt)]
  exact List.mem_map.mpr ⟨(child, code), member, rfl⟩
end ActualReceipt

section Fold
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}

theorem tree_of_actual_indirect_children
    {source : TypedSource} {context : SourceSemantics.Context}
    (callerEvidence : Option Dynamic.EvidenceEnvironment)
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (includeCall : ∀ {children scope id lowered},
      RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context children scope id lowered →
      calls children scope id lowered)
    (projectedCall : ∀ {children scope id lowered node}, calls children scope id lowered →
      source.lookupExpression? id = some node → values.checked.catalog.project node.type = .ok lowered.type)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {admitted : ExpressionId → Prop}
    (admission : AdmissionWith indirectForm indirectChildren source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes headers context)
    (emptyEvidence : SelectedEmptyEvidence headers compilation source admitted)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source context admitted)
    (policyFor : PolicyForWith (headers := headers) callerEvidence policy compilation readFuel values source context scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    (extraReceipts : ∀ childFuel id node lowered, admitted id → source.lookupExpression? id = some node →
      indirectForm node.form → ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (childFuel + 1) compilation source scope id reasonAt = .ok lowered →
      ∃ callee arguments metadata,
        ∃ receipt : Receipt policy body childFuel compilation source scope id callee arguments metadata reasonAt lowered,
          calls (CompatibleExpressionCalls.Entries scope receipt.entries) scope id lowered ∧
          ∀ child code, (child, code) ∈ receipt.entries → ∃ childNode,
            source.lookupExpression? child = some childNode ∧ ExpressionHasType source context child childNode.type)
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered) :
    RuntimeExpressionsFor calls readFuel values source context compilation.solvedRequirements reasonAt scope id lowered := by
  apply tree_of_functions_at_runtime_with_children callerEvidence calls includeCall projectedCall
    indirectForm indirectChildren admission coverage sourceTypes emptyEvidence order unique declarations signatures
    constructorValid fragmentValid selectedValid policyFor native active profile fragmentCoercions coercions
    _ allowed found typed accepted
  intro childFuel child childNode childLowered childAllowed childFound form childTyped childAccepted
  obtain ⟨callee, arguments, metadata, receipt, head, types⟩ :=
    extraReceipts childFuel child childNode childLowered childAllowed childFound form childTyped childAccepted
  have same : receipt.original = childNode := Option.some.inj (receipt.found.symm.trans childFound)
  simpa only [same] using actual_branch_receipt receipt calls head types
end Fold

section Boundaries
variable (callee argument : ExpressionId) (metadata : IndirectCallResolution)
  (calleeCode first second : SourceCoreBasic.LoweredExpr)

/-- Physical vector order retains repeated IDs without sorting or deduplication. -/
theorem repeated_order :
    ([(callee, calleeCode), (argument, first), (argument, second)] :
      List (ExpressionId × SourceCoreBasic.LoweredExpr)).map Prod.fst = [callee, argument, argument] := rfl

theorem callee_first : indirectChildren (.call callee [argument, argument] (.indirect metadata)) =
    [callee, argument, argument] := rfl

/-- The ordinary public child definition remains unchanged. -/
theorem old_indirect_children : evaluationChildren (.call callee [argument, argument] (.indirect metadata)) = [] := rfl

theorem old_empty_admission {extra : ExpressionForm → Prop} {source : TypedSource}
    {admitted : ExpressionId → Prop} (admission : AdmissionFor extra source admitted) :
    AdmissionWith extra (fun _ => []) source admitted := admission.with_empty

abbrev old_compiler := @tree_of_functions_at_runtime_with_calls
end Boundaries
end Tests.SourceCoreRecursiveNamedExpressionExtraChildren
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedExpressionRuntimeBounds
/-! Actual named compiler success returns support for the same complete Tree.
Final bounded consumers use the whole runtime ledger, without caller ordinary
validity or an expression runtime premise. Callee BodyBelow and static source,
policy, coverage and constructor conditions remain explicit at this boundary.
The singleton-body consumers also close BodyBelow from a concrete old body.
Header/Profile/Covers are unchanged. -/
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedExpressionRuntimeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates

abbrev actual_contextual_tree := @RecursiveNamedExpressionCompilerCertificates.tree_of_contextual_at_runtime

section ActualCompilation
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : RecursiveNamedCatalog.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}
  {locations : Locations} {capturePrefix : Nat}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

include extension faithful functionLeaves functionTypes in
theorem actual_functions_preserves_at [FunctionCalls.FaultTokens faults]
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : Admission source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : SourceTypes headers context)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source context admitted)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  have receipt := RecursiveNamedExpressionCompilerCertificates.tree_of_functions_at_runtime
    admission coverage sourceTypes order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active profile fragmentCoercions coercions allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedExpressionTreeBounds.preserves_at_runtime functions extension faithful functionLeaves functionTypes
    evidence unique owners uninitialized missing sameLedger runtime budget size within bodies receipt rootFound


include extension faithful functionLeaves functionTypes in
theorem actual_functions_reflects_at [FunctionCalls.FaultTokens faults]
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : Admission source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : SourceTypes headers context)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source context admitted)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  have receipt := RecursiveNamedExpressionCompilerCertificates.tree_of_functions_at_runtime
    admission coverage sourceTypes order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active profile fragmentCoercions coercions allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedExpressionTreeBounds.reflects_at_runtime functions extension faithful functionLeaves functionTypes
    evidence uninitialized missing sameLedger runtime budget size within bodies receipt rootFound

end ActualCompilation

section ConcreteBodies
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : RecursiveNamedCatalog.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (body : BuiltinNamedCalls.Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {readFuel : Nat}
  {compilation : SourceCoreFunctions.Context}
  (sameLedger : context.solvedRequirements = solved)
  (runtime : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))



include extension uninitialized missing faithful functionLeaves functionTypes sameLedger runtime unique owners callerUninitialized callerMissing in
/-- Every child is supplied by the same recursive Tree; the concrete body
certificate closes the actual remaining body family. -/
theorem concrete_preserves_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RuntimeExpressions [Header.of_body body] compilation readFuel source context solved reasonAt) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionTreeBounds.preserves_at_runtime functions extension faithful functionLeaves functionTypes
    evidence unique owners callerUninitialized callerMissing sameLedger runtime budget size within
  intro header member child _
  have same : header = Header.of_body body := by simpa only [List.mem_singleton] using member
  subst header
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry outcome after trace
  exact SourceCoreRecursiveNamedExpressionBounds.builtin_body_preserves_at
    (headers := [Header.of_body body]) (locations := locations) (capturePrefix := capturePrefix)
    functions extension body uninitialized missing faithful functionLeaves functionTypes child entry trace

include extension uninitialized missing faithful functionLeaves functionTypes sameLedger runtime callerUninitialized callerMissing in
/-- Completed Core code produces an independent source trace; the body is
proved from its finite static certificate rather than supplied as execution. -/
theorem concrete_reflects_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RuntimeExpressions [Header.of_body body] compilation readFuel source context solved reasonAt) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionTreeBounds.reflects_at_runtime functions extension faithful functionLeaves functionTypes
    evidence callerUninitialized callerMissing sameLedger runtime budget size within
  intro header member child _
  have same : header = Header.of_body body := by simpa only [List.mem_singleton] using member
  subst header
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry value finalStore completed
  exact SourceCoreRecursiveNamedExpressionBounds.builtin_body_reflects_at
    (headers := [Header.of_body body]) (locations := locations) (capturePrefix := capturePrefix)
    functions extension body uninitialized missing faithful functionLeaves functionTypes child entry completed
end ConcreteBodies

section Boundaries
/-- Support is attached to the same child proof and emitted code. -/
theorem same_tree {calls : CompatibleExpressionCalls.CallHeads} {fuel : Nat} {values : RecursiveNamedCatalog.ValuesContext}
    {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionCalls.Tree.WithLiterals (calls := calls) (fuel := fuel) (values := values)
      (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code) scope id code) :
    CompatibleExpressionCalls.Tree calls fuel values source context solved reasonAt scope id code := receipt.choose

/-- Full ledger equality retains every unused row at this exact context. -/
theorem unused_row {solved : List SolvedRequirement} {context : SourceSemantics.Context}
    (sameLedger : context.solvedRequirements = solved) {row : SolvedRequirement} (unused : row ∈ solved) :
    row ∈ context.solvedRequirements := by rw [sameLedger]; exact unused

end Boundaries
end Tests.SourceCoreRecursiveNamedExpressionRuntimeBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedExpressionTreeBounds
/-! The unchanged expression Tree closes every structural child at one budget.
A concrete singleton builtin body closes the remaining body family in these
consumers. General catalog/body mutual closure remains a later unit. Actual
mixed code checks recursive parent/argument positions, fault order and resume. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedExpressionTreeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds
#check_failure RecursiveNamedExpressionTreeBounds.Tree
#check_failure RecursiveNamedExpressionTreeBounds.BodyMeaning
#check_failure SourceTypedRuntime.run
section ConcreteBodies
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (body : BuiltinNamedCalls.Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {readFuel : Nat}
  {compilation : SourceCoreFunctions.Context}
  (callerValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))



include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
/-- Every child is supplied by the same recursive Tree; the concrete body
certificate closes the actual remaining body family. -/
theorem concrete_preserves_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        readFuel values source context solved reasonAt) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionTreeBounds.preserves_at functions extension faithful functionLeaves functionTypes
    evidence callerValid unique owners callerUninitialized callerMissing budget size within
  intro header member child _
  have same : header = Header.of_body body := by simpa only [List.mem_singleton] using member
  subst header
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry outcome after trace
  exact SourceCoreRecursiveNamedExpressionBounds.builtin_body_preserves_at
    (headers := [Header.of_body body]) (locations := locations) (capturePrefix := capturePrefix)
    functions extension body uninitialized missing faithful functionLeaves functionTypes child entry trace

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
/-- Completed Core code produces an independent source trace; the body is
proved from its finite static certificate rather than supplied as execution. -/
theorem concrete_reflects_at [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        readFuel values source context solved reasonAt) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionTreeBounds.reflects_at functions extension faithful functionLeaves functionTypes
    evidence callerValid callerUninitialized callerMissing budget size within
  intro header member child _
  have same : header = Header.of_body body := by simpa only [List.mem_singleton] using member
  subst header
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry value finalStore completed
  exact SourceCoreRecursiveNamedExpressionBounds.builtin_body_reflects_at
    (headers := [Header.of_body body]) (locations := locations) (capturePrefix := capturePrefix)
    functions extension body uninitialized missing faithful functionLeaves functionTypes child entry completed
end ConcreteBodies

private def content : String := String.intercalate "\n" [
  "enum Box { Box(Bool) }", "enum Key { Key(Bool) }",
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function truth(flag: Bool) returns (Bool) { let saved = flag; return saved; }",
  "function take(a: Word, b: Word) returns (Word) { return a - b; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function failAfter(n: Word) returns (Word) { let written = n + 10; let gap: Word; return gap; }",
  "function badBool() returns (Bool) { let written = 19; let gap: Bool; return gap; }",
  "function ordered() returns (Word) { return take(side(7), side(3)); }",
  "function grouped() returns (integer) { return ((integerSub(wordToInteger(side(7)), wordToInteger(side(9))))); }",
  "function fromIndex() returns (integer) { let m: mapping(Bool => Word); m[true] = 37; return integerAdd(wordToInteger(m[truth(true)]), wordToInteger(side(5))); }",
  "function choose() returns (integer) { return truth(true) ? integerAdd(wordToInteger(side(7)), wordToInteger(side(9))) : wordToInteger(fail()); }",
  "function boxed() returns (Box) { return Box(truth(integerEq(7, 7))); }",
  "function paired() returns ((Bool, Bool)) { return (truth(integerEq(7, 7)), truth(integerLt(7, 7))); }",
  "function keyData() returns (Bool) { let m: mapping(Key => Bool); return m[Key(truth(integerEq(7, 7)))]; }",
  "function skip() returns (Bool) { return false && truth(integerEq(7, 7)); }",
  "function unary() returns (Bool) { return !truth(false); }",
  "function firstFault() returns (integer) { return integerAdd(wordToInteger(fail()), wordToInteger(side(99))); }",
  "function laterFault() returns (integer) { return integerAdd(wordToInteger(side(7)), wordToInteger(fail())); }",
  "function keyFault() returns (integer) { let m: mapping(Bool => Word); return wordToInteger(m[badBool()]); }",
  "function bodyFault() returns (integer) { return wordToInteger(failAfter(side(7))); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"tree bound resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"tree bound prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"tree bound ordered cells changed {label}: {reprStr final.heap}"
private def constructor (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO DataConstructorInstantiation := do
  let signature ← match compiled.sourceProgram.signatures.dataTypes.filter (·.name == name) with
    | [signature] => pure signature | _ => throw (IO.userError "tree bound nominal signature missing")
  let selected ← match signature.constructors with
    | [selected] => pure selected | _ => throw (IO.userError "tree bound constructor missing")
  pure ⟨selected.id, [], selected.payloadTypes, .nominal signature.id []⟩
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "tree bound fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "tree bound exact fault binder missing")


def run : IO Unit := do
  let names := ["ordered", "grouped", "fromIndex", "choose", "boxed", "paired", "keyData", "skip", "unary",
    "firstFault", "laterFault", "keyFault", "bodyFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named expression Tree bounds" content names
  let box ← constructor compiled "Box"
  let key ← constructor compiled "Key"
  let materialized : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 37)]
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("ordered", w 4, [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 3)), (.word, some (w 3)), (.word, some (w 7)), (.word, some (w 3))]),
    ("grouped", .integer (-2), [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 9)), (.word, some (w 9))]),
    ("fromIndex", .integer 42, [(.mapping .bool .word, some materialized), (.bool, some (.bool true)), (.bool, some (.bool true)), (.word, some (w 5)), (.word, some (w 5))]),
    ("choose", .integer 16, [(.bool, some (.bool true)), (.bool, some (.bool true)), (.word, some (w 7)), (.word, some (w 7)), (.word, some (w 9)), (.word, some (w 9))]),
    ("boxed", .constructed box [.bool true], [(.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("paired", .product (.bool true) (.bool false), [(.bool, some (.bool true)), (.bool, some (.bool true)), (.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("keyData", .bool false, [(.mapping key.resultType .bool, some (.mapping key.resultType .bool [])), (.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("skip", .bool false, []),
    ("unary", .bool true, [(.bool, some (.bool false)), (.bool, some (.bool false))])]
  let failures := ["firstFault", "laterFault", "keyFault", "bodyFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 819)⟩]}
  let firstGap ← faultBinder compiled "fail"
  let keyGap ← faultBinder compiled "badBool"
  let bodyGap ← faultBinder compiled "failAfter"
  let completed ← successes.mapM fun test => finish compiled test.1 [] 300000 initial
  let failed ← failures.mapM fun name => finish compiled name [] 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip completed do
      let (name, expected, expectedCells) := test
      let observation ← finish compiled name [] fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"tree bound full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"tree bound result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"tree bound source heap not deeply safe {name}"
      | other => throw (IO.userError s!"tree bound {name}: {reprStr other}")
    for (name, baseline) in failures.zip failed do
      let observation ← finish compiled name [] fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"tree bound full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        let expected := if name == "keyFault" then keyGap else if name == "bodyFault" then bodyGap else firstGap
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == expected) "tree bound lost first source fault binder"
        let earlier := if name == "laterFault" || name == "bodyFault" then [(.word, some (w 7)), (.word, some (w 7))] else []
        let effects := match name with
          | "keyFault" => [(.mapping .bool .word, some (.mapping .bool .word [])), (.word, some (w 19)), (.bool, none)]
          | "bodyFault" => [(.word, some (w 7)), (.word, some (w 17)), (.word, none)]
          | _ => [(.word, some (w 5)), (.word, none)]
        cells initial final (earlier ++ effects) name
      | other => throw (IO.userError s!"tree bound fault {name}: {reprStr other}")
  IO.println "recursive named expression Tree bounds: unchanged recursive grammar, inclusive structural IH, actual strict callee boundary, mixed parent/arguments, fault order and resume GREEN"
end Tests.SourceCoreRecursiveNamedExpressionTreeBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedExpressions
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
theorem tree_preserves [FunctionCalls.FaultTokens faults] (unique : NodeOccurrencesUnique source)
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
theorem tree_reflects [FunctionCalls.FaultTokens faults] {value : Core.Value} {finalStore : Core.Store}
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedTupleExpressions
/-! Actual named compiler success returns support for the same complete Tree.
Final bounded consumers use the whole runtime ledger, without caller ordinary
validity or an expression runtime premise. Callee BodyBelow and static source,
policy, coverage and constructor conditions remain explicit at this boundary.
Arbitrary tuple arities preserve ordered compiler children; source types and
callee BodyBelow remain independent inputs. Singleton retained IR audits below
do not claim parser or checker provenance. -/
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedTupleExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates

abbrev actual_contextual_tree := @RecursiveNamedExpressionCompilerCertificates.tree_of_contextual_at_runtime_admission

section ActualCompilation
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : RecursiveNamedCatalog.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}
  {locations : Locations} {capturePrefix : Nat}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

include extension faithful functionLeaves functionTypes in
theorem actual_functions_preserves_at [FunctionCalls.FaultTokens faults]
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : RuntimeAdmission source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : SourceTypes headers context)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source context admitted)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  have receipt := RecursiveNamedExpressionCompilerCertificates.tree_of_functions_at_runtime_admission
    admission coverage sourceTypes order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active profile fragmentCoercions coercions allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedExpressionTreeBounds.preserves_at_runtime functions extension faithful functionLeaves functionTypes
    evidence unique owners uninitialized missing sameLedger runtime budget size within bodies receipt rootFound


include extension faithful functionLeaves functionTypes in
theorem actual_functions_reflects_at [FunctionCalls.FaultTokens faults]
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : RuntimeAdmission source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : SourceTypes headers context)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source context admitted)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  have receipt := RecursiveNamedExpressionCompilerCertificates.tree_of_functions_at_runtime_admission
    admission coverage sourceTypes order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active profile fragmentCoercions coercions allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedExpressionTreeBounds.reflects_at_runtime functions extension faithful functionLeaves functionTypes
    evidence uninitialized missing sameLedger runtime budget size within bodies receipt rootFound

end ActualCompilation

section Boundaries
variable (a b c d : ExpressionId)

theorem old_tuple3_negative : ¬ compositionForm (.tuple [a, b, c]) := by
  simp [compositionForm]

theorem runtime_singleton : runtimeCompositionForm (.tuple [a]) := by
  exact Or.inr ⟨[a], rfl⟩

theorem runtime_tuple3 : runtimeCompositionForm (.tuple [a, b, c]) := by
  exact Or.inr ⟨[a, b, c], rfl⟩

theorem runtime_tuple4 : runtimeCompositionForm (.tuple [a, b, c, d]) := by
  exact Or.inr ⟨[a, b, c, d], rfl⟩

theorem old_singleton_negative : ¬ compositionForm (.tuple [a]) := by
  simp [compositionForm]
end Boundaries

private def content : String := String.intercalate "\n" [
  "function side(x: Word) returns (Word) { return x; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function triple() returns ((Word, Bool, Word)) { return (side(7), true, 3 + 4); }",
  "function quadruple() returns ((Word, Bool, Word, Bool)) { return (side(11), false, side(13), true); }",
  "function nested() returns (((Word, Bool, Word), Word, Bool)) { return ((side(17), true, 5 + 6), side(19), false); }",
  "function firstFault() returns ((Word, Word, Word)) { return (fail(), side(91), side(92)); }",
  "function laterFault() returns ((Word, Word, Word, Word)) { return (side(23), side(29), fail(), side(99)); }",
  "function singleton() returns (Word) { return (side(31)); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- Re-enter the actual contextual expression compiler, retaining exact ordered
children, including repeated IDs. Only the last singleton/duplicate audit uses
modified retained IR; it does not claim parser/checker provenance. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) (names : List String) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "tuple diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "tuple parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut triples := 0
  let mut quadruples := 0
  let mut singletons := 0
  let mut duplicates := 0
  for named in prepared.base.functions do
    let original ← match prepared.base.sourceProgram.signatures.functions.find? (·.id == named.signature.key.declaration) with
      | some signature => pure signature | none => throw (IO.userError "tuple original signature missing")
    if names.contains original.name then
      let own ← match diagnostics.base.find? named.signature.key with
        | some own => pure own | none => throw (IO.userError "tuple own diagnostics missing")
      let source := CallableIndexedNamedGeneration.source named
      let compilation := CallableIndexedNamedGeneration.context prepared named
      let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
      let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
      let reasonAt := diagnostics.reasonAt named.signature.key
      let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
        prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics compilation
        prepared.base.callableContext none none
      let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
        prepared.base.globals.map (·.referenceType) ++ [.cell prepared.ancestry.layout.frame.type]
      for item in source.nodes do
        match item with
        | .expression node =>
          match node.form with
          | .tuple ids =>
            let code ← get "actual tuple lowering" (lower prepared.fuel source scope node.id reasonAt)
            let codes ← ids.mapM (fun id => get "ordered tuple child" (lower (prepared.fuel - 1) source scope id reasonAt))
            require (code == SourceCoreCalls.packArguments codes && codes.length == ids.length)
              "tuple actual ordered pack/code vector changed"
            require (Core.infer? nativeContext code.expression prepared.layouts.definitions == some (LanguageResult.resultType code.type))
              "tuple actual native type lost"
            require (node.coercions.isEmpty && node.requirements.isEmpty)
              "tuple parent evidence/coercions changed"
            if ids.length == 3 then triples := triples + 1
            if ids.length == 4 then quadruples := quadruples + 1
          | .group child =>
            if original.name == "singleton" then
              let childNode ← match source.lookupExpression? child with
                | some childNode => pure childNode | none => throw (IO.userError "singleton actual operand missing")
              let retained := {source with nodes := source.nodes.map (fun item => match item with
                | .expression current => if current.id == node.id then
                    .expression {current with form := .tuple [child], type := childNode.type, requirements := [], coercions := []}
                  else item
                | _ => item)}
              let code ← get "retained singleton tuple lowering" (lower prepared.fuel retained scope node.id reasonAt)
              let childCode ← get "retained singleton original child" (lower (prepared.fuel - 1) retained scope child reasonAt)
              require (code == SourceCoreCalls.packArguments [childCode]) "retained singleton exact code changed"
              require (Core.infer? nativeContext code.expression prepared.layouts.definitions == some (LanguageResult.resultType code.type))
                "retained singleton native type lost"
              singletons := singletons + 1
              let repeated := {retained with nodes := retained.nodes.map (fun item => match item with
                | .expression current => if current.id == node.id then
                    .expression {current with form := .tuple [child, child, child], type := TypeSystem.Ty.productMany [childNode.type, childNode.type, childNode.type], requirements := [], coercions := []}
                  else item
                | _ => item)}
              let repeatedCode ← get "retained repeated tuple lowering" (lower prepared.fuel repeated scope node.id reasonAt)
              let repeatedChild ← get "retained repeated tuple child" (lower (prepared.fuel - 1) repeated scope child reasonAt)
              require (repeatedCode == SourceCoreCalls.packArguments [repeatedChild, repeatedChild, repeatedChild])
                "retained repeated IDs/order/code changed"
              require (Core.infer? nativeContext repeatedCode.expression prepared.layouts.definitions == some (LanguageResult.resultType repeatedCode.type))
                "retained repeated tuple native type lost"
              duplicates := duplicates + 1
          | _ => pure ()
        | _ => pure ()
  require (triples == 4 && quadruples == 2 && singletons == 1 && duplicates == 1)
    s!"tuple actual coverage changed {triples}/{quadruples}/{singletons}/{duplicates}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (fuel : Nat)
    (initial : SourceTypedRuntime.RuntimeState) : IO (SourceTypedRuntime.RunResult × String) := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
  let final ← get "tuple actual native resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution | none => throw (IO.userError "tuple original native execution missing")
  let native := execution.completion.result.native.observation
  match native with
  | .succeeded _ store | .failed _ store =>
    require (!store.isEmpty) "tuple full installed store lost"
  | _ => throw (IO.userError "tuple original native completion missing")
  pure (final.observation, reprStr native)

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "tuple original source heap prefix changed"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"tuple full ordered source heap changed: {reprStr final.heap}"

def run : IO Unit := do
  let names := ["triple", "quadruple", "nested", "firstFault", "laterFault", "singleton"]
  let program ← get "tuple actual checked source" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] })
  let keys ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
  let publicCompilation ← get "tuple actual public Core compilation" (SourceCoreCompiler.compileChecked program
    (keys.map (fun key => SourceCoreCompiler.Seed.declaration key.declaration))
    {specializationBudget := 512, compilationFuel := 1000})
  let compiled ← match publicCompilation.artifact? with
    | some compiled => pure compiled | none => throw (IO.userError "tuple actual public compilation has no cached artifact")
  require (compiled.keys == keys) "tuple actual public root order changed"
  inspect compiled names
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("triple", .product (w 7) (.product (.bool true) (w 7)), [(.word, some (w 7))]),
    ("quadruple", .product (w 11) (.product (.bool false) (.product (w 13) (.bool true))),
      [(.word, some (w 11)), (.word, some (w 13))]),
    ("nested", .product (.product (w 17) (.product (.bool true) (w 11))) (.product (w 19) (.bool false)),
      [(.word, some (w 17)), (.word, some (w 19))]),
    ("singleton", w 31, [(.word, some (w 31))])]
  let complete ← successes.mapM (fun test => finish compiled test.1 300000 initial)
  let failed ← ["firstFault", "laterFault"].mapM (fun name => finish compiled name 300000 initial)
  for fuel in [0, 1, 43, 300000] do
    for (test, baseline) in successes.zip complete do
      let (name, expected, expectedCells) := test
      let actual ← finish compiled name fuel initial
      require (reprStr actual == reprStr baseline) "tuple full native/source heap/resume changed"
      match actual.1 with
      | .done result final =>
        require (reprStr result == reprStr expected) "tuple actual product result/order changed"
        cells initial final expectedCells
      | other => throw (IO.userError s!"tuple success changed {reprStr other}")
    for (name, baseline) in ["firstFault", "laterFault"].zip failed do
      let actual ← finish compiled name fuel initial
      require (reprStr actual == reprStr baseline) "tuple full native fault/resume changed"
      match actual.1 with
      | .fault (.uninitializedLocal _) final =>
        let earlier := if name == "laterFault" then [(.word, some (w 23)), (.word, some (w 29))] else []
        cells initial final (earlier ++ [(.word, some (w 5)), (.word, none)])
      | other => throw (IO.userError s!"tuple first/later fault changed {reprStr other}")
  IO.println "recursive named tuples: actual public tuple3/4/nested named+builtin / ordered pack / retained singleton+duplicate IR (parser provenance unproved) / full heap+native store / first-later fault+four resume budgets GREEN"

end Tests.SourceCoreRecursiveNamedTupleExpressions
end
