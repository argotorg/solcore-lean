import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedCalls
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedFunctionLoops
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericAssignments
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedNamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedParameters
import Solcore.Test.SourceSemantics.CoreLowering.Named.Branches
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.LambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinarySequenceCallers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectHistories

/-!
# Named operator tests

Named functions with operators, arguments and calls.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreNamedArguments
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBody.Certificate.mk

/-! Exact packing, independent ordered source arguments and actual cached
named calls. Argument failures skip global/body entry, while completed calls
retain raw mappings, parameter order, lexical fault writes and checkpoints. -/
set_option autoImplicit false
namespace Tests.SourceCoreNamedArguments
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open NamedCalls.Arguments

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"named_arguments", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "named_arguments.solc"⟩, 0, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def node (index : Nat) (value : Bool) : ExpressionNode := {
  id := id index, span, type := .bool, form := .reference (if value then "true" else "false") (.builtinBoolean value) }
private def source : TypedSource := { owner, inputs := [], roots := [], nodes := [.expression (node 0 true), .expression (node 1 false)] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def sourceProgram : SourceSemantics.Program := ⟨signatures, [], []⟩
private def sourceContext : SourceSemantics.Context := .ofSignatures signatures
private def codes : List SourceCoreBasic.LoweredExpr :=
  [⟨.bool, LanguageResult.success (.bool true)⟩, ⟨.bool, LanguageResult.success (.bool false)⟩]

/-- Two independently evaluated source arguments and the actual production
packing helper retain the same order, with arbitrary surrounding stores. -/
theorem ordered_arguments (heap : Dynamic.Heap) (environment : Environment) (store : Store) :
    Dynamic.ExpressionsEvaluate sourceProgram sourceContext [] source [] heap [id 0, id 1]
      [.bool true, .bool false] heap ∧
    Evaluates environment store (SourceCoreCalls.packArguments codes).expression
      (.inRight .word (.pair (.bool true) (.bool false))) store := by
  constructor
  · exact .cons (.intro (node := node 0 true) (lookupExpression?_sound (by rfl)) (.builtinBoolean rfl) .nil)
      (.cons (.intro (node := node 1 false) (lookupExpression?_sound (by rfl)) (.builtinBoolean rfl) .nil) .nil)
  · have first : Evaluates environment store (LanguageResult.success (.bool true)) (.inRight .word (.bool true)) store := .inRight .bool
    have second : Evaluates (.bool true :: environment) store
        ((LanguageResult.success (.bool false)).weakenAt 0) (.inRight .word (.bool false)) store := by
      simp only [LanguageResult.success, Expr.weakenAt]; exact .inRight .bool
    exact LocalSequence.pair_success .bool .bool first second

/-- A failed argument completes the actual call without looking up any
global cell, even if no installed function reference exists in the environment. -/
theorem argument_failure_skips_body (signature : SourceCoreCalls.Signature) (index : Nat)
    (reason internal : Word) (environment : Environment) (store : Store) :
    Evaluates environment store
      (SourceCoreCalls.call signature index (LanguageResult.failure signature.parameterType (.word reason)) internal)
      (.inLeft signature.resultType (.word reason)) store ∧
    (∀ value final, Evaluates environment store
      (SourceCoreCalls.call signature index (LanguageResult.failure signature.parameterType (.word reason)) internal) value final →
      value = .inLeft signature.resultType (.word reason) ∧ final = store) := by
  have failed := SourceCoreCalls.call_argument_failure (signature := signature) (index := index) (internalReason := internal)
    (show Evaluates environment store (LanguageResult.failure signature.parameterType (.word reason))
      (.inLeft signature.parameterType (.word reason)) store from .inLeft .word)
  exact ⟨failed, fun _ _ completed => evaluation_deterministic completed failed⟩

/-- Finite whole helper completion exposes the actual retained body after a
non-Unit packed argument, rather than assuming a native child body execution. -/
theorem packed_body_reflection {signature : SourceCoreCalls.Signature} {index : Nat} {location : Location}
    {caller captured : Environment} {store final : Store} {body arguments : Expr} {argument value : Value}
    (evaluated : Evaluates caller store arguments (.inRight .word argument) store)
    (reference : caller[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (completed : Evaluates caller store (SourceCoreCalls.call signature index arguments Word.zero) value final) :
    Evaluates (argument :: captured) store body value final :=
  body_complete evaluated reference read completed

/-- Actual production acceptance retains the canonical source target and the
ordered child compile receipts. The caller must supply static child trees,
never a semantic body or child execution field. -/
theorem actual_compiler_receipt {compilation : SourceCoreFunctions.Context} {callerSource : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {call callee : ExpressionId} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation} {signature : SourceCoreCalls.Signature}
    {arguments : List SourceCoreBasic.LoweredExpr} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Emission compilation callerSource scope call callee ids instantiation signature arguments lowered) :
    lowered.expression = SourceCoreCalls.call signature
      (scope.length + compilation.administrativePrefix + receipt.index)
      (SourceCoreCalls.packArguments arguments).expression compilation.internalReason ∧
    signature.parameterType = (SourceCoreCalls.packArguments arguments).type ∧
    SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok signature.key ∧
    compilation.globals[receipt.index]? = some signature := receipt.equation

private def content : String := String.intercalate "\n" [
  "enum Item { Item(Bool) }",
  "function identity(value: Bool) returns (Bool) { return value; }",
  "function two(first: Bool, second: Bool) returns (Bool) { return first; }",
  "function accept(item: Item, flag: Bool) returns (Bool) { return flag; }",
  "function fail(value: Bool) returns (Bool) { let written = !value; let gap: Bool; return gap; }",
  "function one(flag: Bool) returns (Bool) { return identity(!flag); }",
  "function many(flag: Bool, raw: mapping(Bool => Bool)) returns (Bool) { let m: mapping(Bool => Bool); return two(m[!flag], raw[flag]); }",
  "function skipped(flag: Bool) returns (Bool) { let m: mapping(Bool => Bool); let gap: Bool; return two(m[flag], gap); }",
  "function missing(flag: Bool) returns (Bool) { let m: mapping(Bool => Item); return accept(m[flag], !flag); }",
  "function fault(flag: Bool) returns (Bool) { return fail(!flag); }",
  "function echo(raw: mapping(Bool => Bool)) returns (mapping(Bool => Bool)) { return raw; }",
  "function forwarded(raw: mapping(Bool => Bool)) returns (mapping(Bool => Bool)) { return echo(raw); }",
  "function through(f: function(Bool) returns (Bool), flag: Bool) returns (function(Bool) returns (Bool)) { return f; }",
  "function callable(f: function(Bool) returns (Bool), flag: Bool) returns (function(Bool) returns (Bool)) { return through(f, !flag); }"
]

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"named argument prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"named argument ordered cells changed {label}: {reprStr final.heap}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  let resumed ← SourceCoreUnifiedCorpusSupport.get s!"named arguments resume {name}" (first.resume 300000)
  pure resumed.observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "named general arguments" content ["one", "many", "skipped", "missing", "fault", "forwarded", "callable"]
  let initialState : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (.word (Word.ofNatModulo 819))⟩]}
  let raw : SourceTypedRuntime.Value := .mapping (.comptime .bool) (.comptime .bool) [(.bool true, .bool true), (.bool true, .bool false)]
  let mappingType : TypeSystem.Ty := .mapping .bool .bool
  let materialized : SourceTypedRuntime.Value := .mapping .bool .bool []
  let identityKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "identity"
  let functionValue : SourceTypedRuntime.Value := .global identityKey []
  let item ← SourceCoreUnifiedCorpusSupport.get "named argument Item"
    (match compiled.sourceProgram.signatures.dataTypes.head? with | some item => Except.ok item | none => Except.error "missing Item")
  for fuel in [0, 43, 300000] do
    match ← finish compiled "one" [.bool true] fuel initialState with
    | .done (.bool false) final => cells initialState final [(.bool, some (.bool true)), (.bool, some (.bool false))] "one"
    | other => throw (IO.userError s!"named one changed: {reprStr other}")
    match ← finish compiled "many" [.bool true, raw] fuel initialState with
    | .done (.bool false) final =>
      cells initialState final
        [(.bool, some (.bool true)), (mappingType, some raw), (mappingType, some materialized), (.bool, some (.bool false)), (.bool, some (.bool true))] "many"
    | other => throw (IO.userError s!"named many changed: {reprStr other}")
    match ← finish compiled "forwarded" [raw] fuel initialState with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr raw) "named forwarded raw header/order changed"
      cells initialState final [(mappingType, some raw), (mappingType, some raw)] "forwarded"
    | other => throw (IO.userError s!"named forwarded changed: {reprStr other}")
    match ← finish compiled "callable" [functionValue, .bool true] fuel initialState with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr functionValue) "named callable identity changed"
      cells initialState final [(.function .bool .bool, some functionValue), (.bool, some (.bool true)), (.function .bool .bool, some functionValue), (.bool, some (.bool false))] "callable"
    | other => throw (IO.userError s!"named callable argument changed: {reprStr other}")
    match ← finish compiled "skipped" [.bool true] fuel initialState with
    | .fault (.uninitializedLocal actual) final =>
      let specialized ← SourceCoreUnifiedCorpusSupport.get "named skipped source" (SourceCompilationPlan.exactSpecialization compiled.validationPlan
        (← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "skipped"))
      let gap ← SourceCoreUnifiedCorpusSupport.get "named skipped gap"
        (match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).find? (·.name == "gap") with
         | some binder => Except.ok binder | none => Except.error "missing gap")
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap.id) "named argument fault lost source binder"
      cells initialState final [(.bool, some (.bool true)), (mappingType, some materialized), (.bool, none)] "skipped"
    | other => throw (IO.userError s!"named argument fault changed: {reprStr other}")
    match ← finish compiled "missing" [.bool true] fuel initialState with
    | .fault (.typeMismatch rawType none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (rawType == .nominal item.id []) "named argument missing default metadata changed"
      cells initialState final [(.bool, some (.bool true)), (.mapping .bool rawType, some (.mapping .bool rawType []))] "missing"
    | other => throw (IO.userError s!"named missing argument changed: {reprStr other}")
    match ← finish compiled "fault" [.bool true] fuel initialState with
    | .fault (.uninitializedLocal actual) final =>
      let specialized ← SourceCoreUnifiedCorpusSupport.get "named body fault source" (SourceCompilationPlan.exactSpecialization compiled.validationPlan
        (← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"))
      let gap ← SourceCoreUnifiedCorpusSupport.get "named body fault gap"
        (match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).find? (·.name == "gap") with
         | some binder => Except.ok binder | none => Except.error "missing gap")
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap.id) "named body fault lost source binder"
      cells initialState final [(.bool, some (.bool true)), (.bool, some (.bool false)), (.bool, some (.bool true)), (.bool, none)] "fault"
    | other => throw (IO.userError s!"named body fault changed: {reprStr other}")
  IO.println "named arguments: actual cached calls, ordered packing, argument/body faults, raw mappings/callables and resume GREEN"

end Tests.SourceCoreNamedArguments
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedBodyReachableDiagnostics
/-! The same named for body and recursive catalog static profile accept reachable
operand diagnostics. Concrete named expression children close the body meaning;
the installed entry and existing callee certificates remain explicit. Actual
equal-only fixtures have no assignment diagnostic entries. Automatic prepared
whole-tree extraction and recursive callee correspondence are separate work. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.NamedForFunctionBody.Certificate.mk
#check_failure Solcore.SourceSemantics.CoreLowering.NamedForFunctionBody.CertificateFor.mk
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.Profile.mk
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.ProfileFor.mk
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.ProfileFor.runtimeMeaning
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.ProfileFor.bodyMeaning
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreNamedBodyReachableDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAncestryPairedLookup NamedForFunctionBody GeneralHeap ReadOnly CompatiblePayload CoreProof

section CompilerConsumers
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
  {function : Dynamic.Closure} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem reachable_body_preserves [FunctionCalls.FaultTokens faults]
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : NamedImperativeForStatements.Tree bodies layouts owner active frameLayout globals onError compilation expressionFuel
      function.source expressionSyntax solved reasonAt administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  let certificate := of_extracted_for accepted projection generated tree errors
  exact certificate.preserves functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem reachable_body_reflects [FunctionCalls.FaultTokens faults]
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : NamedImperativeForStatements.Tree bodies layouts owner active frameLayout globals onError compilation expressionFuel
      function.source expressionSyntax solved reasonAt administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  let certificate := of_extracted_for accepted projection generated tree errors
  exact certificate.reflects functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem reachable_body_finite_iff [FunctionCalls.FaultTokens faults]
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : NamedImperativeForStatements.Tree bodies layouts owner active frameLayout globals onError compilation expressionFuel
      function.source expressionSyntax solved reasonAt administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
:
    (∃ runtimeFuel value finalStore,
      Core.runStateful runtimeFuel (.initial (code.rename ξ) actual store) =
        .done value finalStore) ↔
    (∃ outcome after,
      FunctionCallBody.Trace program function context environment before outcome after) := by
  let certificate := of_extracted_for accepted projection generated tree errors
  exact certificate.finite_iff functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed
end CompilerConsumers

section Catalog
open RecursiveNamedCatalog
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
def reachable_catalog_profile
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeFor.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    ProfileFor .reachable headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  ProfileFor.of_extracted initialValid accepted projection generated tree errors

/-- The old family keeps its original record; both directions retain its fields. -/
theorem strict_family_adapter
    (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop)
    (administrative : Header prepared values ambient.definitions program → Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profiles : Profiles headers compilation expressionFuel expressionSyntax administrative registry faults) :
    Profiles headers compilation expressionFuel expressionSyntax administrative registry faults :=
  ProfilesFor.to_strict headers compilation expressionFuel expressionSyntax administrative registry faults
    (Profiles.to_for headers compilation expressionFuel expressionSyntax administrative registry faults profiles)
end Catalog

/-- Empty exact operand decoding satisfies the reachable equal law. -/
theorem empty_table_equal (token : Word) :
    AssignmentOperandDiagnostics.OperandsLaw
      (GenericAssignmentDiagnostics.OperandRep ⟨[]⟩) .equal token :=
  AssignmentOperandDiagnostics.equal _ token

theorem no_equal_operand_entry (token : Word) :
    ¬ GenericAssignmentDiagnostics.OperandRep ⟨[]⟩ (.invalidAssignmentOperands .equal) token := by
  rintro ⟨diagnostic, raw, found, _⟩
  cases found


open NamedForFunctionBody in
theorem certificate_record_roundtrip
    {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
    {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {source : TypedSource} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {policy : SourceCoreLoops.Policy}
    {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
    (certificate : Certificate bodies layouts owner active frame globals onError compilation expressionFuel
      source expressionSyntax context solved reasonAt administrative registry faults scope statements
      expected type policy fuel fellThrough escaped code) : certificate.to_for.to_strict = certificate := by
  cases certificate
  rfl

open RecursiveNamedCatalog in
theorem profile_record_roundtrip
    {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (certificate : Profile headers header compilation expressionFuel expressionSyntax administrative registry faults) : certificate.to_for.to_strict = certificate := by
  cases certificate
  rfl
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function next(value: Word) returns (Word) { return value + 1; }",
    "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
    "function bad() returns (Word) { let absent: Word; return absent; }",
    "function equalBody(seed: Word) returns (Word) { let result = seed; for (result = next(seed); less(result, 5); result = next(result)) { let inner = 0; while (less(inner, 2)) { inner = next(inner); } if (result == 3) { continue; } if (result == 4) { break; } } return result; }",
    "function unitBody(seed: Word) { let result = seed; for (result = next(seed); less(result, 3); result = next(result)) { } }",
    "function initialFault(seed: Word) returns (Word) { let result = seed; for (result = bad(); false; result = next(result)) { result = next(result); } return result; }",
    "function postFault(seed: Word) returns (Word) { let result = seed; for (result = next(seed); true; result = bad()) { result = next(result); } return result; }",
    "function bodyFault(seed: Word) returns (Word) { let result = seed; let seen: mapping(Bool => Word); for (result = next(seed); true; result = next(result)) { seen[false] = next(result); result = bad(); } return result; }",
    "function self(n: Word) returns (Word) { let result = 1; for (let i = 0; i < n; i = next(i)) { result = result + self(n - 1); } return result; }"
  ]}]
}
open Tests.SourceCompilerFeatureSupport in
private def verify_resume (entry : Entry) : IO Unit := do
  let baseline ← entry.audit [scalar 1]
  let invocation ← entry.invoke [scalar 1]
  for fuel in [0, 7, 43, 199] do
    let suspended ← entry.audit [scalar 1] fuel
    let resumed ← get "reachable body native resume" (suspended.resume 300000)
    require ((← nativeObservation resumed) == (← nativeObservation baseline))
      "reachable body resume changed native result/store"
    let pending ← entry.invoke [scalar 1] {executionOptions with executionFuel := fuel}
    let terminal ← match pending.outcome with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match invocation.outcome, terminal with
    | .succeeded expected, .succeeded actual =>
      require (actual.value == expected.value) "reachable body resume changed result"
    | .failed expected _, .failed actual session =>
      require (actual == expected) "reachable body resume changed fault token"
      require (decide ((← get "resumed diagnostic" (session.diagnostic entry.key actual)) = (← invocation.diagnostic expected)))
        "reachable body resume changed exact diagnostic"
    | _, _ => throw (IO.userError "reachable body resume changed completion")

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let checked ← get "reachable named body checker" (checkProgram workspace)
  for name in ["equalBody", "unitBody", "initialFault", "postFault", "bodyFault", "self"] do
    let entry ← compileNamed checked name
    let item ← get "reachable named source" (SourceCompilationPlan.exactSpecialization entry.cached.validationPlan entry.key)
    let table ← get "equal-only body table" (SourceCoreAssignmentFaultSites.prepare item.function.typedBody Core.wordModulus)
    require table.sites.isEmpty "equal-only named body requested an unreachable operand token"
    require (table.diagnostic? Word.zero == none) "empty named body table decoded a token"
    verify_resume entry
    let result ← entry.invoke [scalar 1]
    match name, result.outcome with
    | "equalBody", .succeeded completed => require (completed.value == scalar 4) "nested named loop result changed"
    | "unitBody", .succeeded completed => require (completed.value == .unit) "named Unit finish changed"
    | "self", .succeeded completed => require (completed.value == scalar 2) "recursive runtime smoke result changed"
    | _, .failed token _ =>
      require (← result.diagnostic token).isSome "named RHS fault lost its diagnostic"
      let audited ← entry.audit [scalar 1]
      let heap := (sourceState audited).heap
      let expected := if name == "initialFault" then 1 else if name == "postFault" then 3 else 2
      let raw ← get "reachable body expected write" (rawData 128 (scalar expected))
      require (reprStr heap[1]? == reprStr (some (SourceTypedRuntime.Cell.mk .word (some raw))))
        "initializer/body/post fault changed prior writes"
      if name == "bodyFault" then
        let rawMapping ← get "reachable body expected mapping write" (rawData 128
          (.mapping .bool .word [(.bool false, scalar 3)]))
        require (reprStr heap[2]? == reprStr (some (SourceTypedRuntime.Cell.mk (.mapping .bool .word) (some rawMapping))))
          "named RHS fault discarded a completed mapping write"
    | _, _ => throw (IO.userError "unexpected reachable named body completion")
  IO.println "named body reachable diagnostics: same concrete for tree/finish, static recursive profiles, empty equal table, named initializer/body/post faults, prior writes and resume GREEN"
end Tests.SourceCoreNamedBodyReachableDiagnostics
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedCalls
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBody.Certificate.mk
#check_failure Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.Compilation.mk

/-! Actual cached nil-call/reference selection, a closed independent named Unit
body and concrete installed frame restoration. Checked calls exercise distinct
slots, lexical writes/faults, named output and native suspension/resumption. -/
set_option autoImplicit false
namespace Tests.SourceCoreNamedCalls
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open NamedCalls

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"named_calls", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "named_calls.solc"⟩, 0, 0⟩
private def syntaxMetadata : Solcore.Syntax.FunctionDecl := {
  span, value := {
    signature := {
      span
      name := ⟨span, "unit"⟩
      genericParameters := none
      parameters := ⟨span, []⟩
      modifiers := ⟨none, none⟩
      returnsClause := none
      whereClause := none }
    body := ⟨span, []⟩ } }
private def signatureMetadata : ProgramFunctionSignature := {
  id := owner, name := "unit", parameters := [], returnTypes := [], returnComptime := false,
  scheme := {parameters := [], predicates := [], body := .function .unit .unit}, source := syntaxMetadata }
private def signatures : ProgramSignatures := ⟨[signatureMetadata], [], [], [], [], []⟩
private def source : TypedSource := {owner, inputs := [], roots := [], nodes := []}
private def definition : BodyDefinition := {
  owner, type := .function .unit .unit, resultType := .unit, returnComptime := false,
  solvedRequirements := [], source }
private def program : SourceSemantics.Program := ⟨signatures, [⟨definition⟩], []⟩
private def instantiation : DeclarationInstantiation := {
  declaration := owner, parameterSubstitution := [], type := .function .unit .unit,
  predicates := [], parameterComptime := [], returnComptime := false }
private def context := declarationContext signatures owner [] [] []
private def bodyInstance : Dynamic.BodyInstance := ⟨context, source, .unit⟩
private def function : Dynamic.Closure := ⟨[], .unit, [], source, [], context, []⟩

private theorem valid : SourceSemantics.DeclarationInstantiation.Valid (Context.ofSignatures signatures) instantiation := by
  apply SourceSemantics.DeclarationInstantiation.Valid.intro signatureMetadata
  · exact .head _
  · rfl
  · exact SourceSemantics.ParameterSubstitution.exact_empty
  · intro _ _ member; cases member
  · rfl
  · rfl
  · rfl
  · rfl
private theorem frame : NamedCalls.SourceFrame program instantiation bodyInstance function := by
  constructor
  · apply Dynamic.FunctionInstantiates.intro (signature := signatureMetadata) (definition := ⟨definition⟩)
    · exact .head _
    · exact .head _
    · rfl
    · rfl
    · exact valid
    · rfl
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact .nil
  · constructor
    · intro _ _ lookup; cases lookup
    · intro _ member; simp [bodyInstance, context, declarationContext, Context.withSolvedRequirements,
        Context.withAssumptions, Context.withResidualTypeVariables, Context.forDeclaration, Context.ofSignatures] at member

/-- The declaration body is independently instantiated and executed. The named
bridge reconstructs the real global application without a fabricated lambda. -/
theorem empty_source_call (before : Dynamic.Heap) :
    NamedCalls.BodyOutcome program bodyInstance [] before [] (.value .unit) before ∧
    FunctionCallBody.Outcome program (Context.ofSignatures signatures) [] [] before
      (.global ⟨instantiation, []⟩) [] (.value .unit) before := by
  have body : NamedCalls.BodyOutcome program bodyInstance [] before [] (.value .unit) before :=
    frame.body_of_trace (MonoBindersExtend.nil context) (Dynamic.BindersAllocate.nil [] before)
      (FunctionCallBody.Trace.unit rfl (Dynamic.FunctionStatementsExecute.nil))
  exact ⟨body, frame.call body⟩

private def emptyCode (fellThrough escaped : Word) : Expr :=
  CompatibleStatements.finish .unit (LocalLoop.fallthrough .unit) fellThrough escaped

private theorem empty_lowering (policy : SourceCoreLoops.Policy) (fuel : Nat) (bodySource : TypedSource)
    (fellThrough escaped : Word) (reasonAt : ExpressionId → Word) :
    SourceCoreLoops.lowerStatementsWithPolicy policy fuel bodySource [] [] .unit reasonAt fellThrough escaped =
      .ok (emptyCode fellThrough escaped) := by
  simp only [SourceCoreLoops.lowerStatementsWithPolicy, SourceCoreLoops.lowerFlowStatementsWithPolicy]
  rfl

/-- Actual cached success supplies an empty-body syntax receipt. No source or
native body execution is stored in the predicate consumed by the compiler. -/
theorem cached_empty_named
    {checked : SourceCoreCompatibleCatalog.Checked} (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    {slot : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : prepared.base.functions[slot]? = some named)
    (roots : named.specialized.function.typedBody.roots = [])
    (inputs : named.inputs = []) (result : named.signature.resultType = .unit)
    {parents : List SourceCoreLocalEvidence.Prepared} {own : SourceCoreProgramFaultSites.Function}
    (parentReceipt : SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : ∀ diagnostic, prepared.base.diagnostics = some diagnostic →
      (match prepared.base.callableContext with
        | none => diagnostic.program
        | some native => {diagnostic.program with rootTable := native.diagnostics.rootTable}).base.find? named.signature.key = some own)
    (allocate : SourceCoreSourceCells.Allocator)
    (allocator : ((SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts).atContext
      named.signature.key []).expressions.sourceCells = some allocate) :
    ∃ diagnostic code,
      prepared.base.diagnostics = some diagnostic ∧ prepared.secondPass.closures[slot]? = some code ∧
      Nonempty (NamedCompilationReceipt.Receipt prepared.base.sourceProgram
        (SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
        prepared.base.sourceProgram.signatures prepared.base.plan prepared.base.globals
        (match prepared.base.callableContext with
          | none => diagnostic.program
          | some native => {diagnostic.program with rootTable := native.diagnostics.rootTable})
        prepared.base.locals prepared.base.callableContext parents own named [] prepared.fuel allocate
        (fun body => body = emptyCode own.fellThroughReason own.table.escapedReason) code) := by
  obtain ⟨diagnostic, code, available, cached, compiled⟩ := NamedCalls.compiled_at prepared selected
  refine ⟨diagnostic, code, available, cached, ?_⟩
  apply NamedCompilationReceipt.of_accepted roots parentReceipt (diagnosticReceipt diagnostic available) allocator ?_ compiled
  intro body accepted
  unfold NamedCompilationReceipt.bodyRequest at accepted
  rw [inputs, result] at accepted
  simp only [List.reverse_nil, List.map_nil] at accepted
  rw [empty_lowering] at accepted
  exact (Except.ok.inj accepted).symm

private theorem empty_evaluates (fellThrough escaped : Word) (environment : Environment) (store : Store) :
    Evaluates environment store (emptyCode fellThrough escaped) (.inRight .word .unit) store := by
  apply LocalControl.finish_fallthrough .unit
  · exact LocalLoop.toControl_normal _ escaped (LocalLoop.fallthrough_evaluates _ _ _)
  · simpa [LanguageResult.success, Expr.weakenAt] using
      (show Evaluates (.unit :: .inLeft .unit .unit :: environment) store (.inRight .word .unit) (.inRight .word .unit) store from .inRight .unit)

/-- The actual cached installation preserves argument zero and moves the
named hook's administrative reference by the physical global slot count. -/
theorem installed_hook_slot (count globals : Nat) (parameter result : Ty)
    (layout : SourceCoreCallableIndexedFrames.Layout) (index : Int) (body : Expr) :
    SourceCoreCompatibleOutputs.installedTemplate count
      (.lambda parameter (LanguageResult.resultType result)
        (SourceCoreCallableIndexedFrames.withFrame (.var (globals + 1))
          (SourceCoreCallableIndexedDispatch.literal layout (.state index)) body)) =
    .lambda parameter (LanguageResult.resultType result)
      (SourceCoreCallableIndexedFrames.withFrame (.var (count + globals + 1))
        (SourceCoreCallableIndexedDispatch.literal layout (.state index))
        (body.rename (NamedCalls.installationRenaming count).lift)) := by
  rw [NamedCalls.installed_lambda, NamedCalls.withFrame_rename, Expr.rename,
    NamedCalls.installation_reference, CallableIndexedRenaming.literal]

/-- A real accepted indexed hook for the closed Unit body installs its selected
frame and restores the caller. Installation renames the whole hook, including
the administrative reference, at any authentic global slot. -/
theorem empty_installed_call
    {checked : SourceCoreCallableIndexedAncestry.Checked} {base : SourceCoreCallableIndexedAncestry.Base checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
    (fellThrough escaped : Word)
    (accepted : SourceCoreCallableIndexedAncestry.namedBody ancestry named (emptyCode fellThrough escaped) = .ok code)
    {signature : SourceCoreCalls.Signature} {caller captured : Environment} {store : Store}
    {globalIndex frameLocation globalLocation : Nat} {saved : Value}
    (reference : (.unit :: captured)[ξ (base.globals.length + 1)]? =
      some (.cellRef ancestry.layout.frame.type frameLocation))
    (savedRead : store.read? frameLocation = some saved)
    (globalReference : caller[globalIndex]? = some (.cellRef (OptionalCell.cellType signature.functionType) globalLocation))
    (globalRead : store.read? globalLocation = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) (code.rename ξ) captured))) :
    ∃ origin index metadata,
      ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      CallableIndexedHistory.Carries ancestry.graph.inputs ancestry.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates caller store (SourceCoreCalls.call signature globalIndex (SourceCoreCalls.packArguments []).expression Word.zero)
        (.inRight .word .unit) store := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history ancestry accepted
  have ground : (emptyCode fellThrough escaped).rename ξ = emptyCode fellThrough escaped := by
    simp [emptyCode, CompatibleStatements.finish, LocalControl.finish, LocalLoop.toControl,
      LocalLoop.fallthrough, LanguageResult.success, LanguageResult.failure, LanguageResult.bind,
      Expr.weakenAt, Expr.rename, Renaming.lift]
  have next := CallableIndexedContextFrames.literal_evaluates ancestry.layout.frame (.state index) (saved :: .unit :: captured) store
  rw [← CallableIndexedRenaming.literal ancestry.layout.frame (.state index) (Renaming.insertion 0), Expr.rename_insertion] at next
  have body := empty_evaluates fellThrough escaped (.unit :: saved :: .unit :: captured)
    (store.set frameLocation (SourceCoreCallableIndexedFrames.encode ancestry.layout.frame (.state index)))
  have shifted : ((emptyCode fellThrough escaped).weakenAt 0).weakenAt 0 = emptyCode fellThrough escaped := by
    simp [emptyCode, CompatibleStatements.finish, LocalControl.finish, LocalLoop.toControl,
      LocalLoop.fallthrough, LanguageResult.success, LanguageResult.failure, LanguageResult.bind, Expr.weakenAt]
  have evaluated := CallableContextFrames.withFrame_evaluates (body := emptyCode fellThrough escaped)
    (.var reference) savedRead next (shifted.symm ▸ body)
  have restored : (store.set frameLocation (SourceCoreCallableIndexedFrames.encode ancestry.layout.frame (.state index))).set frameLocation saved = store := by
    rw [List.set_set]
    obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp savedRead
    rw [← same, List.set_getElem_self bound]
  have bodyEvaluation : Evaluates (.unit :: captured) store (code.rename ξ) (.inRight .word .unit) store := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal, ground]
    simpa only [restored] using evaluated
  exact ⟨origin, index, metadata, owned, history, (NamedCalls.installed_call_agreement globalReference globalRead).wrap bodyEvaluation⟩

private def content : String := String.intercalate "\n" [
  "enum Item { Item(Bool) }",
  "function empty() {}",
  "function first() returns (Bool) { return true; }",
  "function middle() returns (Bool) { return first(); }",
  "function unit() { let outer: Word; { let inner = first(); } }",
  "function missing() returns (Bool) { let m: mapping(Bool => Item); let failed = m[true]; return false; }",
  "function last() returns (Bool) { let before = middle(); if (before) { let nested = first(); return nested; } return false; }",
  "function get() returns (function(Unit) returns (Bool)) { return first; }",
  "function through() returns (Bool) { let f = first; return f(); }",
  "function fault() returns (Bool) { let written = first(); let gap: Bool; let failed = gap; return false; }"
]

private def check (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (expected : SourceTypedRuntime.Value) (cells : List (TypeSystem.Ty × Option SourceTypedRuntime.Value))
    (initial : SourceTypedRuntime.RuntimeState) : IO Unit := do
  for fuel in [0, 41, 300000] do
    let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
    let completed ← SourceCoreUnifiedCorpusSupport.get "named call resume" (first.resume 300000)
    match completed.observation with
    | .done value state =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr expected) s!"nil named value changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (state.heap.take initial.heap.length) == reprStr initial.heap) s!"named prefix changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((state.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr cells)
        s!"named lexical cells changed {name}: {reprStr state.heap}"
    | other => throw (IO.userError s!"named nil call failed {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "named nil calls" content ["first", "middle", "unit", "missing", "last", "get", "fault", "through", "empty"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (.word (Word.ofNatModulo 731))⟩]}
  check compiled "empty" .unit [] initial
  let emptyKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "empty"
  let emptySpecialized ← SourceCoreUnifiedCorpusSupport.get "named actual empty specialization"
    (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan emptyKey)
  SourceCoreUnifiedCorpusSupport.assertTrue (emptySpecialized.function.typedBody.roots.isEmpty && emptySpecialized.function.typedBody.inputs.isEmpty)
    "actual cached empty-body receipt preconditions changed"
  check compiled "first" (.bool true) [] initial
  check compiled "middle" (.bool true) [] initial
  check compiled "unit" .unit [(.word, none), (.bool, some (.bool true))] initial
  check compiled "last" (.bool true) [(.bool, some (.bool true)), (.bool, some (.bool true))] initial
  let firstKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "first"
  check compiled "get" (.global firstKey []) [] initial
  check compiled "through" (.bool true) [(.function .unit .bool, some (.global firstKey []))] initial
  let item ← SourceCoreUnifiedCorpusSupport.get "named missing Item"
    (match compiled.sourceProgram.signatures.dataTypes.head? with | some item => Except.ok item | none => Except.error "no Item")
  for fuel in [0, 41, 300000] do
    let result ← SourceCoreUnifiedCorpusSupport.execute compiled "missing" [] fuel initial
    let resumed ← SourceCoreUnifiedCorpusSupport.get "named missing resume" (result.resume 300000)
    match resumed.observation with
    | .fault (.typeMismatch raw none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (raw == .nominal item.id []) "named missing-default metadata changed"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) ==
        reprStr ([(TypeSystem.Ty.mapping .bool raw, some (SourceTypedRuntime.Value.mapping .bool raw []))] : List (TypeSystem.Ty × Option SourceTypedRuntime.Value))) "named missing-default heap changed"
    | other => throw (IO.userError s!"nil named missing-default fault changed: {reprStr other}")
  for fuel in [0, 41, 300000] do
    let result ← SourceCoreUnifiedCorpusSupport.execute compiled "fault" [] fuel initial
    let resumed ← SourceCoreUnifiedCorpusSupport.get "named fault resume" (result.resume 300000)
    let specialized ← SourceCoreUnifiedCorpusSupport.get "named fault source" (SourceCompilationPlan.exactSpecialization compiled.validationPlan (← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fault"))
    let binders := SourceCoreDataPlaces.declaredBinders specialized.function.typedBody
    match resumed.observation, binders.find? (·.name == "gap") with
    | .fault (.uninitializedLocal actual) final, some gap =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap.id) "nil named fault lost source binder"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) ==
        reprStr ([ (TypeSystem.Ty.bool, some (SourceTypedRuntime.Value.bool true)), (.bool, none)] : List (TypeSystem.Ty × Option SourceTypedRuntime.Value))) "nil named fault lost prior writes"
    | other, _ => throw (IO.userError s!"nil named fault changed: {reprStr other}")
  IO.println "named nil calls: actual selection/cached hook, source Unit bridge, installed slot shifts, lexical writes/fault and resume GREEN"

end Tests.SourceCoreNamedCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedCompilationReceipt
#check_failure Solcore.SourceSemantics.CoreLowering.NamedCompilationReceipt.Receipt.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! The generic compiler receipt is instantiated with a concrete static empty
body shape. The typed-prefix consumer uses successful real parameter lowering,
represented arguments and initial environment typing, without final typing or
semantic body assumptions. Native regressions retain captures, raw metadata,
parameter allocation order and checkpoint resumption. -/
set_option autoImplicit false
namespace Tests.SourceCoreNamedCompilationReceipt
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning

private theorem empty_request
    (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (signatures : ProgramSignatures) (plan : SourceSpecializationWorklist.Plan)
    (globals : List SourceCoreCalls.Signature) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (locals : SourceCoreLocalPolymorphism.Catalog) (native : Option SourceCoreGeneralFunctions.CallableContext)
    (parents : List SourceCoreLocalEvidence.Prepared) (own : SourceCoreProgramFaultSites.Function)
    (named : SourceCoreGeneralFunctions.Function) (resultType : named.signature.resultType = .unit) :
    NamedCompilationReceipt.bodyRequest program representation signatures plan globals diagnostics locals native parents own
      named [] 10 = .ok (CompatibleStatements.finish .unit (LocalLoop.fallthrough .unit)
        own.fellThroughReason own.table.escapedReason) := by
  simp only [NamedCompilationReceipt.bodyRequest, resultType]
  rfl

/-- Only static compiler receipts precede this extraction. The certificate
identifies the actual empty body, independently of its runtime execution. -/
theorem empty_compilation_receipt
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {plan : SourceSpecializationWorklist.Plan}
    {globals : List SourceCoreCalls.Signature} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {locals : SourceCoreLocalPolymorphism.Catalog} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parents : List SourceCoreLocalEvidence.Prepared} {own : SourceCoreProgramFaultSites.Function}
    {named : SourceCoreGeneralFunctions.Function} {allocate : SourceCoreSourceCells.Allocator} {code : Expr}
    (roots : named.specialized.function.typedBody.roots = []) (resultType : named.signature.resultType = .unit)
    (parentReceipt : SourceCoreStageCodebook.prepareContexts program plan
      (locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : diagnostics.base.find? named.signature.key = some own)
    (allocator : (representation.atContext named.signature.key []).expressions.sourceCells = some allocate)
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation program representation signatures plan globals
      diagnostics locals native 10 named = .ok code) :
    Nonempty (NamedCompilationReceipt.Receipt program representation signatures plan globals diagnostics locals native parents own
      named [] 10 allocate (fun body => body = CompatibleStatements.finish .unit (LocalLoop.fallthrough .unit)
        own.fellThroughReason own.table.escapedReason) code) := by
  apply NamedCompilationReceipt.of_accepted roots parentReceipt diagnosticReceipt allocator ?_ accepted
  intro body lowered
  have empty := empty_request program representation signatures plan globals diagnostics locals native parents own named resultType
  exact Except.ok.inj (lowered.symm.trans empty)

/-- Two real parameters retain their two projection temporaries as well as
both source references. No continuation body is executed to derive this type. -/
theorem two_parameter_body_typed
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} (left right : TypedBinder) (leftType rightType : Ty) {output : Ty} {body code : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner [] onError))
      source [] [(left, leftType), (right, rightType)] output SourceCoreFunctions.argumentProjection body = .ok code)
    (inputs : source.inputs = [left, right])
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions) (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {first second : Dynamic.Value} {firstNative secondNative : Value}
    (leftRep : model.Represents mapping world left.scheme.body first firstNative leftType)
    (rightRep : model.Represents mapping world right.scheme.body second secondNative rightType)
    {administrative actualContext : Core.Context} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative [] [] canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (agrees : EnvironmentsAgree ξ (.pair firstNative secondNative :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalActual finalStore finalWorld embedding,
      RuntimeEnvironmentHasTypes finalWorld finalActual
        (OptionalCell.referenceType rightType :: rightType :: OptionalCell.referenceType leftType :: leftType :: actualContext)
        nativeDefinitions ∧ WorldExtends world finalWorld ∧
      ContinuationAgreement actual store (code.rename ξ) finalActual finalStore (body.rename embedding) := by
  have arguments : Arguments model mapping world [(left, leftType), (right, rightType)]
      [first, second] [firstNative, secondNative] := .cons leftRep (.cons rightRep .nil)
  obtain ⟨_, _, _, finalActual, finalStore, _, finalWorld, embedding, _, _, _, _, worlds, _, _, typed, agreement⟩ :=
    CallableIndexedParameterTyped.named_prefix onError accepted inputs definitions registered arguments environments heaps
      agrees actualTyped reference read unmapped
  exact ⟨finalActual, finalStore, finalWorld, embedding, typed, worlds, agreement⟩

example (initial : Core.Context) (binder : TypedBinder) :
    CallableIndexedParameterTyped.prefixContext [(binder, .function .word (LanguageResult.resultType .word))] initial =
      OptionalCell.referenceType (.function .word (LanguageResult.resultType .word)) ::
      .function .word (LanguageResult.resultType .word) :: initial := rfl

private def content : String := String.intercalate "\n" [
  "function empty(flag: Bool, value: Word) { }",
  "function selected(flag: Bool, value: Word, values: mapping(Word => Word)) returns (Word) { return flag ? values[value] : value; }",
  "function duplicate(values: mapping(Word => Word), key: Word) returns (Word) { return values[key]; }",
  "function captured(seed: Word) returns (function(Word) returns (Word)) { let total = seed; return lam(delta: Word) -> Word { total += delta; return total; }; }",
  "function identity(value: Word) returns (Word) { return value; }",
  "function invoke(f: function(Word) returns (Word), delta: Word) returns (Word) { return f(delta); }"
]

private def check (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (expected : SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) : IO Unit := do
  for fuel in [0, 23, 300000] do
    let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
    let resumed ← SourceCoreUnifiedCorpusSupport.get "static receipt resumption" (SourceCoreUnifiedCompilation.Result.resume first 300000)
    match resumed.observation with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr expected) s!"typed named receipt result {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
        s!"typed named receipt changed initial prefix {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue
        (reprStr ((final.heap.drop initial.heap.length).take arguments.length |>.map (·.value)) == reprStr (arguments.map some))
        s!"typed named receipt parameter order {name}"
    | other => throw (IO.userError s!"typed named receipt failed {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "generic named receipt" content
    ["empty", "selected", "duplicate", "captured", "identity", "invoke"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩]}
  let seven : SourceTypedRuntime.Value := .word (Word.ofNatModulo 7)
  let key : SourceTypedRuntime.Value := .word (Word.ofNatModulo 2)
  let mapping : SourceTypedRuntime.Value := .mapping (.comptime .word) .word
    [(key, seven), (key, .word (Word.ofNatModulo 99))]
  check compiled "empty" [.bool false, seven] .unit initial
  check compiled "selected" [.bool true, key, mapping] seven initial
  check compiled "selected" [.bool false, key, mapping] key initial
  check compiled "duplicate" [mapping, key] seven initial
  let identity ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "identity"
  check compiled "invoke" [.global identity [], seven] seven initial
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled "captured" [seven] 300000 initial
  match first.observation with
  | .done (.closure _ _ _ _ _ captures _) final =>
    SourceCoreUnifiedCorpusSupport.assertTrue (captures.length > 0) "returned closure lost parameter/local captures"
    -- The parameter and the local, then the lambda's snapshot copies of both.
    SourceCoreUnifiedCorpusSupport.assertTrue (final.heap.length == initial.heap.length + 4) "closure parameter/local/snapshot cell count"
  | other => throw (IO.userError s!"closure payload receipt failed: {reprStr other}")
  IO.println "generic named compilation receipt and typed parameter environments: ordered cells, indices, raw mapping, closure and resume GREEN"

end Tests.SourceCoreNamedCompilationReceipt
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsSource
/-! Original checker receipts for primitive Word comparison and subtraction.
Literal requirements retain their actual builtin implementation evidence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read

private theorem builtin_word_evidence (context : SourceSemantics.Context) :
    RetainedEvidenceValid context.assumptions context.signatures.resolutionRules
      (ProgramSignatures.builtinIntPredicate .word)
      (.implementation (.byImpl (ProgramSignatures.builtinIntPredicate .word) (.builtin .intWord) [])) := by
  apply RetainedEvidenceValid.intro (.implementation (.byImpl .nil))
  exact .implementation (rule := ProgramSignatures.builtinIntWordRule) (by simp [ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]) rfl
    (.intro ⟨[], []⟩ ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩ rfl rfl) .nil

structure Literal (function : CheckedFunction) where
  node : ExpressionNode
  spelling : Syntax.CoreLiteralValue
  resolution : IntegerLiteralResolution
  validated : SourceCoreElaboration.WordIntegerLiteral
  found : function.typedBody.lookupExpression? node.id = some node
  form : node.form = .integerLiteral spelling resolution
  raw : node.rawType = .word
  accepted : SourceCoreElaboration.validateWordIntegerLiteral function.solvedRequirements node spelling resolution = .ok validated

theorem Literal.typed {function : CheckedFunction} (literal : Literal function)
    {context : SourceSemantics.Context} (word : TypeAdmissible context .word)
    (ledger : context.solvedRequirements = function.solvedRequirements) :
    ExpressionHasType function.typedBody context literal.node.id .word := by
  have metadata := SourceCoreElaboration.validateWordIntegerLiteral_sound literal.accepted
  obtain ⟨row, selected, predicate, evidence⟩ := CoreLowering.NumericLiteralEvidenceReceipts.word literal.accepted
  have member : row ∈ function.solvedRequirements.filter (fun row => decide (row.id = literal.resolution.requirement)) := by
    rw [selected]; simp
  obtain ⟨member, identity⟩ := List.mem_filter.mp member
  have proves : RequirementProves context literal.resolution.requirement
      (ProgramSignatures.builtinIntPredicate literal.resolution.targetType) := by
    refine ⟨row, ⟨ledger ▸ member, of_decide_eq_true identity⟩, predicate, .intro ?_⟩
    rw [evidence, predicate]
    change RetainedEvidenceValid _ _ (ProgramSignatures.builtinIntPredicate literal.resolution.targetType) _
    rw [metadata.targetType]
    simpa only [IntegerLiteralResolution.predicate, metadata.targetType] using builtin_word_evidence context
  have valid : IntegerLiteralValid context literal.spelling literal.resolution :=
    .word metadata.meaning metadata.targetType proves
  have typed : ExpressionHasType function.typedBody context literal.node.id literal.node.type := by
    refine .intro (lookupExpression?_sound literal.found)
      (literal.form ▸ ExpressionFormHasRawType.integerLiteral valid)
      (literal.raw.trans metadata.targetType.symm) (metadata.targetType.symm ▸ word)
      (metadata.nodeType.symm ▸ word) ?_
    rw [metadata.requirements, metadata.coercions, metadata.targetType, metadata.nodeType]
    exact .ordinary (by intro id member; have same := List.mem_singleton.mp member; exact same ▸ valid.requirement_valid) (.nil _) rfl
  exact metadata.nodeType ▸ typed

structure Binary (source : TypedSource) (left right : ExpressionId)
    (operator : Syntax.BinaryOp) (result : TypeSystem.Ty) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  form : node.form = .binary left operator right
  raw : node.rawType = result
  type : node.type = result
  requirements : node.requirements = []
  coercions : node.coercions = []

theorem Binary.typed {source : TypedSource} {left right : ExpressionId}
    {operator : Syntax.BinaryOp} {result : TypeSystem.Ty}
    (binary : Binary source left right operator result)
    {context : SourceSemantics.Context} (resultAdmissible : TypeAdmissible context result)
    (leftTyped : ExpressionHasType source context left .word)
    (rightTyped : ExpressionHasType source context right .word)
    (profile : BinaryOperatorHasType context operator .word .word result []) :
    ExpressionHasType source context binary.node.id result := by
  have typed : ExpressionHasType source context binary.node.id binary.node.type := by
    refine .intro (lookupExpression?_sound binary.found)
      (binary.form ▸ ExpressionFormHasRawType.binary leftTyped rightTyped profile)
      binary.raw resultAdmissible (binary.type.symm ▸ resultAdmissible) ?_
    rw [binary.requirements, binary.coercions, binary.type]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context binary.node.id type) binary.type) typed

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  conditionRead : Read function.typedBody binder .word
  zero : Literal function
  comparison : Binary function.typedBody conditionRead.node.id zero.node.id .greater .bool
  argumentRead : Read function.typedBody binder .word
  one : Literal function
  difference : Binary function.typedBody argumentRead.node.id one.node.id .subtract .word
  finalRead : Read function.typedBody binder .word
  assignment : StatementNode
  resolution : AssignmentResolution
  loop : StatementNode
  statement : StatementNode
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  binderOwner : binder.id.owner = function.typedBody.owner
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  roots : function.typedBody.roots = [.statement loop.id, .statement statement.id]
  zeroValue : zero.resolution.rawValue = 0
  oneValue : one.resolution.rawValue = 1
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal difference.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = binder.id
  targetType : resolution.target.type = .word
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  loopFound : function.typedBody.lookupStatement? loop.id = some loop
  loopForm : loop.form = .whileLoop comparison.node.id [assignment.id]
  loopType : loop.type = .unit
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some finalRead.node.id)
  statementType : statement.type = .word

def FactoryShape.body {function signature} (shape : FactoryShape function signature) : List StatementId :=
  [shape.loop.id, shape.statement.id]

def FactoryShape.nodeList {function signature} (shape : FactoryShape function signature) : List SourceInference.Node :=
  [.expression shape.conditionRead.node, .expression shape.zero.node, .expression shape.comparison.node,
    .expression shape.argumentRead.node, .expression shape.one.node, .expression shape.difference.node,
    .statement shape.assignment, .statement shape.loop,
    .expression shape.finalRead.node, .statement shape.statement]

private theorem statementRoots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]

theorem FactoryShape.statementTyping
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : FactoryShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.loop.id, shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton facts), rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons binderScheme binderExtended tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, binderExtended.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have bool : TypeAdmissible lexical .bool := ⟨binders, .builtin .bool⟩
    have ledger : lexical.solvedRequirements = function.solvedRequirements := by cases binderExtended; rfl
    have conditionRead := shape.conditionRead.typed binderScheme shape.binderRequirements word
      binderExtended.local_self binderExtended.local_scheme_requirements_self
    have argumentRead := shape.argumentRead.typed binderScheme shape.binderRequirements word
      binderExtended.local_self binderExtended.local_scheme_requirements_self
    have finalRead := shape.finalRead.typed binderScheme shape.binderRequirements word
      binderExtended.local_self binderExtended.local_scheme_requirements_self
    have comparison := shape.comparison.typed bool conditionRead (shape.zero.typed word ledger) (.wordComparison .greater)
    have difference := shape.difference.typed word argumentRead (shape.one.typed word ledger) (.wordArithmetic .subtract)
    have writable : WritableLocal lexical shape.resolution.target.root .word := by
      rw [shape.targetRoot]
      exact .intro binderExtended.local_self (binderScheme.symm ▸ SchemeWellFormed.monoAdmissible word)
        (by rw [binderScheme]; rfl) (by rw [binderScheme]; rfl)
    have assignmentTyped : SourceAssignmentHasType function.typedBody lexical shape.resolution .equal shape.difference.node.id :=
      .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) difference shape.assignmentRequirements
    have assigned : StatementHasType function.typedBody ⟨.word, 1⟩ lexical shape.assignment.id lexical ordinary :=
      .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
    have loopTyped := StatementHasType.whileLoop (control := ⟨.word, 0⟩)
      (lookupStatement?_sound shape.loopFound) shape.loopForm comparison (.singleton assigned) shape.loopType
    have returned := StatementHasType.returnValue (control := ⟨.word, 0⟩)
      (lookupStatement?_sound shape.statementFound) shape.statementForm finalRead shape.statementType
    exact ⟨lexical, .cons loopTyped (.singleton returned)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function drain(n: Word) returns (Word) { while (n > 0) { n = n - 1; } return n; }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeRead (source : TypedSource) (binder : TypedBinder) (node : ExpressionNode) : IO (Read source binder .word) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "read lookup"
  let ⟨form⟩ ← observed (node.form = .reference binder.name (.local binder.id)) "read binder"
  let ⟨raw⟩ ← observed (node.rawType = .word) "read raw Word"
  let ⟨type⟩ ← observed (node.type = .word) "read Word"
  let ⟨requirements⟩ ← observed (node.requirements = []) "read requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "read coercions"
  return { node, found, form, raw, type, requirements, coercions }

def observeLiteral (function : CheckedFunction) (node : ExpressionNode) : IO (Literal function) := do
  match form : node.form with
  | .integerLiteral spelling resolution =>
    match accepted : SourceCoreElaboration.validateWordIntegerLiteral function.solvedRequirements node spelling resolution with
    | .error error => throw (IO.userError (reprStr error))
    | .ok validated =>
      let ⟨found⟩ ← observed (function.typedBody.lookupExpression? node.id = some node) "literal lookup"
      let ⟨raw⟩ ← observed (node.rawType = .word) "literal raw Word"
      return ⟨node, spelling, resolution, validated, found, form, raw, accepted⟩
  | _ => throw (IO.userError "integer literal expected")

def observeBinary (source : TypedSource) (left right : ExpressionId) (operator : Syntax.BinaryOp)
    (result : TypeSystem.Ty) (node : ExpressionNode) : IO (Binary source left right operator result) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "binary lookup"
  let ⟨form⟩ ← observed (node.form = .binary left operator right) "binary operation"
  let ⟨raw⟩ ← observed (node.rawType = result) "binary raw type"
  let ⟨type⟩ ← observed (node.type = result) "binary type"
  let ⟨requirements⟩ ← observed (node.requirements = []) "primitive binary requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "primitive binary coercions"
  return { node, found, form, raw, type, requirements, coercions }

def observeShape (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (FactoryShape function signature) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "named operator inputs")
  let [.expression condition, .expression zeroNode, .expression compareNode,
      .expression argument, .expression oneNode, .expression subtractNode,
      .statement assignment, .statement loop, .expression result, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "named operator graph")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "bare Word assignment")
  let conditionRead ← observeRead function.typedBody binder condition
  let zero ← observeLiteral function zeroNode
  let comparison ← observeBinary function.typedBody conditionRead.node.id zero.node.id .greater .bool compareNode
  let argumentRead ← observeRead function.typedBody binder argument
  let one ← observeLiteral function oneNode
  let difference ← observeBinary function.typedBody argumentRead.node.id one.node.id .subtract .word subtractNode
  let finalRead ← observeRead function.typedBody binder result
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "named operator binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "named operator binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "named operator binderOrdinary"
  let ⟨binderOwner⟩ ← observed (binder.id.owner = function.typedBody.owner) "named operator binderOwner"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "named operator parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "named operator inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "named operator returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "named operator inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement loop.id, .statement statement.id]) "named operator roots"
  let ⟨zeroValue⟩ ← observed (zero.resolution.rawValue = 0) "named operator zeroValue"
  let ⟨oneValue⟩ ← observed (one.resolution.rawValue = 1) "named operator oneValue"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "named operator assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal difference.node.id) "named operator assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "named operator assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "named operator targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "named operator targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "named operator targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "named operator assignmentRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "named operator loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .whileLoop comparison.node.id [assignment.id]) "named operator loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "named operator loopType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "named operator statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalRead.node.id)) "named operator statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "named operator statementType"
  return { binder, conditionRead, zero, comparison, argumentRead, one, difference, finalRead, assignment, resolution, loop, statement, binderScheme, binderRequirements, binderOrdinary, binderOwner, parameters, inputTypes, returns, inputs, roots, zeroValue, oneValue, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, loopFound, loopForm, loopType, statementFound, statementForm, statementType }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : program.functions = [function]
  signatures : program.signatures.functions = [signature]
  methods : program.methods = []
  sourceShape : FactoryShape function signature
  nodes : function.typedBody.nodes = sourceShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [function], [signature] =>
      let sourceShape ← observeShape function signature
      if methods : program.methods = [] then
        let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
          functions := by
            intro actual member candidate candidateMember _accepted
            have sameFunction : actual = function := by simpa only [functions, List.mem_singleton] using member
            have sameSignature : candidate = signature := by simpa only [signatures, List.mem_singleton] using candidateMember
            subst actual candidate
            exact sourceShape.statementTyping program.signatures
          methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
        let ⟨nodes⟩ ← observed (function.typedBody.nodes = sourceShape.nodeList) "complete named operators graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected named operators methods")
    | _, _ => throw (IO.userError "named operators declaration count")

end Tests.SourceCoreNamedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsFixture
/-! Actual compilation, selected inventory and static loop observations for
one named Word function with primitive comparison, subtraction and a finite loop. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics

private def observeFact (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture extends CheckedFixture where
  seeds : List SourceCompiler.Seed
  options : SourceCompiler.Options
  facadeCompiled : SourceCompiler.Compiled
  accepted : SourceCompiler.compileChecked program seeds options = .ok facadeCompiled
  recipe : SourceCoreIndexedSession.Recipe
  issued : CoreLowering.RecursiveNamedPreparedStageContracts.PublicRecipe facadeCompiled recipe
  sameProgram : recipe.compiled.sourceProgram = program
  recipePrepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe

def compiledFixture : IO CompiledFixture := do
  let checked ← checkedFixture
  let signature :: _ := checked.program.signatures.functions
    | throw (IO.userError "factory signature missing")
  let seeds := [SourceCompiler.Seed.declaration signature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 100}
  match generated : SourceCoreCompiler.compileChecked checked.program seeds options with
  | .error error => throw (IO.userError (reprStr error))
  | .ok source =>
    match selected : source.artifact? with
    | none => throw (IO.userError "factory cached artifact missing")
    | some cached =>
      match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
      | .error error => throw (IO.userError (reprStr error))
      | .ok recipe =>
        match facade : SourceCoreExecution.prepare source with
        | .error error => throw (IO.userError (reprStr error))
        | .ok facadeCompiled =>
          have accepted : SourceCompiler.compileChecked checked.program seeds options = .ok facadeCompiled := by
            simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError,
              bind, Except.bind] using facade
          have sameProgram : recipe.compiled.sourceProgram = checked.program :=
            (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
              ((source.artifact_fields selected).1.trans (SourceCoreCompiler.compileChecked_program generated))
          return {
            toCheckedFixture := checked
            seeds := seeds
            options := options
            facadeCompiled := facadeCompiled
            accepted := accepted
            recipe := recipe
            issued := CoreLowering.RecursiveNamedPreparedStageContracts.public_preparation selected prepared facade
            sameProgram := sameProgram
            recipePrepared := by rw [SourceCoreIndexedSession.Recipe.prepare_compiled prepared]; exact prepared }

theorem CompiledFixture.prepared (fixture : CompiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ fixture.recipe.compiled.validationPlan.specializations) :
    Nonempty (CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row) :=
  CoreLowering.RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.issued member

theorem CompiledFixture.source_wellFormed (fixture : CompiledFixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  rw [fixture.sameProgram]
  exact fixture.wellFormed

structure ActualHeader (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) where
  prepared : CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row
  header : CoreLowering.CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
    (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  aligned : CoreLowering.RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
    (CoreLowering.CallableNamedMetadata.instantiation row) header
  diagnostic : CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared



open CoreLowering

structure ObservedFactory (fixture : CompiledFixture) where
  row : SourceSpecialization.SpecializedFunction
  shape : FactoryShape row.function fixture.signature
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = fixture.signature.id
  parameters : row.parameterSubstitution = []
  closed : row.assumptions = []
  ordinary : row.function.returnComptime = false
  resultType : row.function.inferredBodyType = .word
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  nodes : row.function.typedBody.nodes = shape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries

abbrev ObservedFactory.inputs {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.inputs
abbrev ObservedFactory.roots {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.roots
abbrev ObservedFactory.binder {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.binder
abbrev ObservedFactory.binderScheme {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.binderScheme

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observeFact (key = row.key) "captured factory exact key"
    return ⟨by rw [accepted, same]⟩

def observeFactory (fixture : CompiledFixture) : IO (ObservedFactory fixture) := do
  match rows : fixture.recipe.compiled.validationPlan.specializations with
  | [row] =>
    let shape ← observeShape row.function fixture.signature
    match entries : fixture.recipe.compiled.indexed.entries with
    | [entry] =>
      let ⟨sourceOwner⟩ ← observeFact (row.function.typedBody.owner = fixture.signature.id) "named operators source owner"
      let ⟨parameters⟩ ← observeFact (row.parameterSubstitution = []) "named operators substitution"
      let ⟨closed⟩ ← observeFact (row.assumptions = []) "named operators assumptions"
      let ⟨resultType⟩ ← observeFact (row.function.inferredBodyType = .word) "named operators result type"
      let ⟨ordinary⟩ ← observeFact (row.function.returnComptime = false) "named operators ordinary result"
      let ⟨target⟩ ← observeTarget fixture row
      let ⟨nodes⟩ ← observeFact (row.function.typedBody.nodes = shape.nodeList) "named operators nodes"
      let ⟨noLocals⟩ ← observeFact (fixture.recipe.compiled.indexed.base.locals.bindings = []) "named operators local catalog"
      let ⟨profile⟩ ← observeFact (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "named operators profile"
      return {
        row, shape, sourceOwner, parameters, closed, ordinary, resultType, target, nodes, noLocals, profile, entry
        member := by rw [rows]; exact .head []
        entryMember := by rw [entries]; exact .head [] }
    | _ => throw (IO.userError "named operators entry count")
  | _ => throw (IO.userError "named operators specialization count")

/-- The staged selection is obtained from the retained callable table and
original sidecar of the concrete compiler result. -/
structure ObservedStages (fixture : CompiledFixture)
    (observed : ObservedFactory fixture) where
  singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      if singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1 then
        match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
            (.named observed.row.key) with
        | .error error => throw (IO.userError (reprStr error))
        | .ok descriptor => return ⟨singletonGlobal, descriptor, native, present, sidecar, issued⟩
      else throw (IO.userError "factory global count")

def ObservedStages.registry {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem ActualHeader.complete {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [actual.header] := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled actual.prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : actual.prepared.index = 0 := by omega
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [stages.singletonGlobal] at bound
  have indexZero : index = 0 := by omega
  refine ⟨actual.header, .head [], actual.aligned.slot.trans (zero.trans indexZero.symm), ?_⟩
  rw [actual.aligned.named]
  rw [zero] at selected
  rw [indexZero] at found
  exact Option.some.inj (selected.symm.trans found)

theorem bootstrap_zero (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled)) :
    owner.key.capturePrefix = 0 := by
  have bound := owner.position.isLt
  change owner.position.val < 1 at bound
  have zero : owner.position.val = 0 := by omega
  simp only [CallableIndexedOwnedFunctionValues.OwnedKey.key,
    CallableIndexedOwnedPreparedBootstrapRootState.keys,
    CallableIndexedOwnedPreparedBootstrapRootState.key, zero, List.getElem_cons_zero]


theorem ObservedStages.inventory {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row, actual.header = packet.header := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  have target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation observed.row) = .ok prepared.named.signature.key := by
    rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
    exact observed.target
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : prepared.index = 0 := by omega
  have globals : fixture.recipe.compiled.indexed.base.globals = [prepared.named.signature] := by
    obtain ⟨first, single⟩ := List.length_eq_one_iff.mp stages.singletonGlobal
    rw [single, zero] at selected
    have same : first = prepared.named.signature := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
    exact single.trans (congrArg (fun value => [value]) same)
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := by
      intro binder member
      rw [observed.inputs] at member
      have same := List.mem_singleton.mp member
      exact same ▸ observed.shape.binderOrdinary
    target := target
    slot := by simp only [CallableNamedMetadata.Slot, globals, zero]; simp }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl⟩



theorem ObservedStages.source_of_cached {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 1 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using stages.singletonGlobal
  have before := (List.getElem?_eq_some_iff.mp actual.prepared.selected).1
  have after := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at before after
  have same : index = actual.prepared.index := by omega
  rw [same, actual.prepared.selected] at selected
  cases Option.some.inj selected
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

theorem CompiledFixture.signature_member (fixture : CompiledFixture) :
    fixture.signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions := by
  rw [fixture.sameProgram, fixture.signatures]
  exact .head []

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same


theorem ActualHeader.body {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.body = observed.shape.body := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = [observed.shape.loop.id, observed.shape.statement.id]
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.roots] at accepted
  exact (Except.ok.inj accepted).symm

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

end Tests.SourceCoreNamedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsFacts
/-! Finite observations identify every original read, literal and binary operation.
They establish compiler coverage without an execution or body-meaning premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.input_types {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.shape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.shape.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.result_type {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

theorem ActualHeader.output {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.result_type] at projected
  exact (Except.ok.inj projected).symm

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

theorem ObservedFactory.expression_cases {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node) :
    node = observed.shape.conditionRead.node ∨ node = observed.shape.zero.node ∨ node = observed.shape.comparison.node ∨ node = observed.shape.argumentRead.node ∨ node = observed.shape.one.node ∨ node = observed.shape.difference.node ∨ node = observed.shape.finalRead.node := by
  have member := found.1
  rw [observed.nodes] at member
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton, Node.expression.injEq,
    reduceCtorEq, List.not_mem_nil, false_or, or_false] using member

theorem ObservedFactory.no_lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node)
    {parameters result body} (form : node.form = .lambda parameters result body) : False := by
  rcases observed.expression_cases found with same | same | same | same | same | same | same
  all_goals subst node
  · rw [observed.shape.conditionRead.form] at form; cases form
  · rw [observed.shape.zero.form] at form; cases form
  · rw [observed.shape.comparison.form] at form; cases form
  · rw [observed.shape.argumentRead.form] at form; cases form
  · rw [observed.shape.one.form] at form; cases form
  · rw [observed.shape.difference.form] at form; cases form
  · rw [observed.shape.finalRead.form] at form; cases form

theorem ObservedFactory.binder_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.binder.id = .ok observed.shape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.conditionRead.form, observed.shape.zero.form, observed.shape.comparison.form, observed.shape.argumentRead.form, observed.shape.one.form, observed.shape.difference.form, observed.shape.finalRead.form,
    observed.shape.assignmentForm, observed.shape.loopForm, observed.shape.statementForm,
    observed.shape.binderOwner, observed.shape.binderScheme, TypeSystem.Scheme.mono, observed.shape.binderRequirements]

theorem ActualHeader.statements {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.function.body = [observed.shape.loop.id, observed.shape.statement.id] := actual.body

end Tests.SourceCoreNamedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsMetadata
/-! Actual finite Source observations retain numeric-literal evidence while
excluding special contextual hooks and indirect calls in this program. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ObservedFactory.no_calls {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : observed.row.function.typedBody.lookupExpression? id = some node)
    {callee arguments resolution} (form : node.form = .call callee arguments (.indirect resolution)) : False := by
  rcases observed.expression_cases (lookupExpression?_sound found) with same | same | same | same | same | same | same
  all_goals subst node
  · rw [observed.shape.conditionRead.form] at form; cases form
  · rw [observed.shape.zero.form] at form; cases form
  · rw [observed.shape.comparison.form] at form; cases form
  · rw [observed.shape.argumentRead.form] at form; cases form
  · rw [observed.shape.one.form] at form; cases form
  · rw [observed.shape.difference.form] at form; cases form
  · rw [observed.shape.finalRead.form] at form; cases form

theorem ObservedFactory.metadata {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.NativeMetadataFor
      fixture.recipe.compiled.indexed named observed.row.function.typedBody := by
  constructor
  · intro id _tree node found
    rcases observed.expression_cases (lookupExpression?_sound found) with same | same | same | same | same | same | same
    all_goals subst node
    · exact .inl observed.shape.conditionRead.requirements
    · exact .inr ⟨_, _, observed.shape.zero.form⟩
    · exact .inl observed.shape.comparison.requirements
    · exact .inl observed.shape.argumentRead.requirements
    · exact .inr ⟨_, _, observed.shape.one.form⟩
    · exact .inl observed.shape.difference.requirements
    · exact .inl observed.shape.finalRead.requirements
  · intro id _tree node found
    rcases observed.expression_cases (lookupExpression?_sound found) with same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.shape.conditionRead.coercions
    · exact (SourceCoreElaboration.validateWordIntegerLiteral_sound observed.shape.zero.accepted).coercions
    · exact observed.shape.comparison.coercions
    · exact observed.shape.argumentRead.coercions
    · exact (SourceCoreElaboration.validateWordIntegerLiteral_sound observed.shape.one.accepted).coercions
    · exact observed.shape.difference.coercions
    · exact observed.shape.finalRead.coercions
  · intro id _tree
    simp only [observed.noLocals, List.find?_nil]
  · intro id _tree node found callee arguments resolution form
    exact False.elim (observed.no_calls found form)
  · intro id _tree node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

end Tests.SourceCoreNamedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsRuntime
/-! Actual public calls execute three iterations and then zero iterations of the accepted arithmetic loop.
The second call consumes the exact session returned by the first. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def firstValue : Core.Word := Core.Word.ofNatModulo 3
def secondValue : Core.Word := Core.Word.ofNatModulo 0

def zero : Core.Word := Core.Word.ofNatModulo 0

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

structure ObservedCall {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (value : Core.Word) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word value] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word value] runOptions (.ok (.succeeded completion))
  returned : completion.value = .word zero

def observeCall {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (value : Core.Word) : IO (ObservedCall observed session value) := do
  match started : session.start observed.row.key [.word value] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt observed.row.key [.word value] runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "named operators failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "named operators exhausted its execution budget")
    | .ok (.succeeded completion) =>
      if returned : completion.value = .word zero then
        return ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "named operators returned an unexpected Word")

structure ObservedInitial (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : ObservedCall observed session firstValue

def observeInitial (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedInitial fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "named operators bootstrap exhausted")
  | .ready session =>
    let call ← observeCall observed session firstValue
    return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready, call⟩

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  initial : ObservedInitial fixture observed
  next : ObservedCall observed initial.call.completion.session secondValue

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let initial ← observeInitial fixture observed
  let next ← observeCall observed initial.call.completion.session secondValue
  return ⟨initial, next⟩

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem ObservedInitial.start_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedInitial fixture observed) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      executed.session.IndexedAt session ∧ executed.call.checkpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.word firstValue]
        runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.call.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩

theorem ObservedInitial.metadata_at_start {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedInitial fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.word firstValue]
      runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  apply started.simple_registry (booted.registry_at initial)
  intro value member
  have same := List.mem_singleton.mp member
  exact same ▸ SourceCoreIndexedSession.SimplePublic.word firstValue

end Tests.SourceCoreNamedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsSyntax
/-! The original typed loop supplies comparison, subtraction, assignment and return.
Recursive expression syntax retains both actual validated integer-literal children. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact original

private theorem returning {source : TypedSource} {context final : SourceSemantics.Context}
    {binder : TypedBinder} {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (read : Read source binder .word)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some read.node.id))
    (annotation : node.type = .word) (leaf : approved read.node.id)
    (typed : StatementHasType source {returnType := .word} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation read.found read.type
        (by simpa only [read.type] using value) leaf)

private theorem assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder : TypedBinder} {payload : TypeSystem.Ty} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    {rhs : ExpressionId} {rhsNode : ExpressionNode}
    (rhsFound : source.lookupExpression? rhs = some rhsNode) (rhsType : rhsNode.type = payload)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal rhs)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved rhs)
    (typed : SourceAssignmentHasType source context assignment .equal rhs)
    (remaining : GenericImperativeMatch.Syntax source approved context (.statements mode rest) .word) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  cases typed with
  | wordCompound operator _ _ _ => cases operator
  | equal target rhs _requirements =>
      cases target with
      | intro writable projections target =>
          apply GenericImperativeMatch.Syntax.assign found form
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [scheme, bare, targetType]
            exact .nil _
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [bare] at projections
            cases projections
            have word := target.symm.trans targetType
            simpa only [word, scheme, TypeSystem.Scheme.mono] using writable
          · simpa only [target] using rhs
          · exact .inl rfl
          · intro child member
            simp only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
            subst child
            exact ⟨leaf, rhsNode, rhsFound, by simpa only [← target, targetType, rhsType] using rhs⟩
          · exact remaining

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.row.function.typedBody true observed.shape.body :=
  .whileLoop observed.shape.loopFound observed.shape.loopForm
    (.assign observed.shape.assignmentFound observed.shape.assignmentForm (.inl rfl) observed.shape.targetBare .nil)
    (.returnValue [] observed.shape.statementFound observed.shape.statementForm)

def ObservedFactory.readIds {fixture : CompiledFixture} (observed : ObservedFactory fixture) : List ExpressionId :=
  [observed.shape.comparison.node.id, observed.shape.difference.node.id, observed.shape.finalRead.node.id]

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context observed.shape.body final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true observed.shape.body) .word := by
  have leaf : ∀ id, id ∈ observed.readIds → approved id := leaves
  obtain ⟨middle, headFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.shape.loopFound first
  rw [observed.shape.loopForm] at firstForm
  cases firstForm with
  | whileLoop conditionTyped bodyTyped =>
    apply GenericImperativeMatch.Syntax.whileLoop observed.shape.loopFound observed.shape.loopForm
      observed.shape.comparison.found observed.shape.comparison.type
      (by simpa only [observed.shape.comparison.type] using conditionTyped) (leaf _ (by simp [readIds]))
    · obtain ⟨_, _, _, assignedHead, _⟩ := head_tail bodyTyped
      have assignment := form_at unique observed.shape.assignmentFound assignedHead
      rw [observed.shape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        exact assigned observed.shape.difference.found observed.shape.difference.type observed.shape.assignmentFound observed.shape.assignmentForm
          (by rw [observed.shape.targetRoot]; exact observed.binder_declaration)
          observed.shape.binderScheme observed.shape.targetBare observed.shape.targetType
          (leaf _ (by simp [readIds])) assignmentTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail tail
      exact returning unique observed.shape.finalRead observed.shape.statementFound observed.shape.statementForm
        observed.shape.statementType (leaf _ (by simp [readIds])) returningHead

theorem ActualHeader.syntax {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    GenericImperativeMatch.Syntax actual.header.function.source
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax actual.header.function.source)
      actual.header.context (.statements true actual.header.function.body) actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.shape.roots, actual.result_type] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [actual.source, actual.body, actual.result_type]
  apply observed.body_syntax (actual.source ▸ actual.header.unique) _ typed
  intro id member
  simp only [ObservedFactory.readIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .binary observed.shape.comparison.found observed.shape.comparison.form
      (.leaf (.read observed.shape.conditionRead.found observed.shape.conditionRead.form))
      (.leaf (.literal observed.shape.zero.found (observed.shape.zero.form ▸ .integer _ _)))
  · exact .binary observed.shape.difference.found observed.shape.difference.form
      (.leaf (.read observed.shape.argumentRead.found observed.shape.argumentRead.form))
      (.leaf (.literal observed.shape.one.found (observed.shape.one.form ▸ .integer _ _)))
  · exact .leaf (.read observed.shape.finalRead.found observed.shape.finalRead.form)

theorem ActualHeader.branching_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.body]
  exact observed.body_shape

def ActualHeader.branching_body {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := row, prepared := actual.prepared, instantiation := CallableNamedMetadata.instantiation row
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .branching receipt }

end Tests.SourceCoreNamedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsSupports
/-! The complete authentic singleton catalog selects the named branching
compiler packet and derives all static children from actual recursive comparison/subtraction/literal lowering. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  input : Input fixture.recipe.compiled
  packet : Issued input
  actual : ActualHeader fixture observed.row
  headerEq : actual.header = packet.header
  rows : Inventory [input]
  rowsEq : rows = .cons packet .nil
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  terminals : ∀ header, header ∈ headers rows → Body header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named actual.header.named.signature.key)

 theorem StaticSupportPackage.header_list {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) : headers support.rows = [support.actual.header] := by
  rw [support.rowsEq, support.headerEq]
  rfl


theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header)
    (rootHeaders : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) rootHeaders)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingSupport.Support rootHeaders
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  apply Nonempty.intro
  apply CallableIndexedOwnedPreparedNamedBranchingCollectors.of_imperative_compiler actual.prepared actual.aligned
    fixture.recipePrepared actual.diagnostic fixture.source_wellFormed complete (bootstrap_zero fixture.recipe.compiled)
    observed.entryMember receipt
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.operands_of_diagnostic
      actual.prepared actual.aligned actual.diagnostic receiver)
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.unary_of_diagnostic
      actual.prepared actual.aligned actual.diagnostic receiver) _ actual.syntax.prepared
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType _native
  obtain ⟨root⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalOperatorRoots.of_accepted
    actual.prepared actual.aligned actual.diagnostic receiver fixture.source_wellFormed
    (by rw [actual.source]; exact observed.metadata actual.prepared.named)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).evidence selected) fields
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact declarations)
    (by intro id node found callee arguments resolution form
        exact observed.no_calls (by simpa only [actual.source] using found) form)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact approved)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact found)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact typed)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact accepted)
  exact .recursive root

theorem static_supports (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨input, _row, packet, actual, sameHeader⟩ := stages.inventory
  let rows : Inventory [input] := .cons packet .nil
  have headerList : headers rows = [actual.header] := by simp only [rows, headers, sameHeader]
  have complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows) := by
    rw [headerList]; exact actual.complete stages
  obtain ⟨receipt⟩ := actual.branching_receipt
  let body := actual.branching_body receipt
  obtain ⟨supported⟩ := actual.support receipt (headers rows) complete (registry := registry) receiver
  let terminals : ∀ header, header ∈ headers rows → Body header := fun header member => by
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    exact same ▸ body
  have supports : ∀ header (member : header ∈ headers rows),
      Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
        (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
    intro header member
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    subst header
    simpa only [terminals, body, ActualHeader.branching_body, Support] using supported
  have family : ∀ {mapping world function native bindings parameter result}
      (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        mapping world function native bindings parameter result),
      CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association := by
    intro mapping world function native bindings parameter result association
    cases association with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      have found := code.sourceFound
      rw [support.source.trans (stages.source_of_cached actual support.caller.selected)] at found
      exact False.elim (observed.no_lambda (lookupExpression?_sound found) code.sourceForm)
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact False.elim (fixture.no_principal support.principal)
  exact ⟨{
    input := input
    packet := packet
    actual := actual
    headerEq := sameHeader
    rows := rows
    rowsEq := rfl
    complete := complete
    terminals := terminals
    supports := supports
    family := family
    descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreNamedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsCommon
/-! Retained callers connect the exact sessions and Source heaps of both named calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers support.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiving.result.context.registry
    support.actual.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.actual.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreNamedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsSeed
/-! The initial nonempty-loop call derives its Source trace, Word result and reusable
empty history from actual bootstrap, input encoding and public completion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver) (stages : ObservedStages fixture observed)
    (first : ObservedInitial fixture observed) :
    ∃ state : RetainedState support first.call.completion.session [],
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.word firstValue] (.value (.word zero)) state.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  have startupRegistry := first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word firstValue] [.word firstValue] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩
      ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.actual.header support.input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.packet.header.named.specialized support.input.prepared.available)) := by
    rw [support.headerEq]
    exact support.packet.sourceAt
  obtain ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      returnedCaller, added, handles, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_collects
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
      first.call.started first.call.executed .skip support.descriptor
  have empty : added = [] := List.map_eq_nil_iff.mp handles
  subst added
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.actual.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans first.call.returned) support.actual.output result
  let state : RetainedState support first.call.completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := returnedAt
    atRecipe := started.recipe_eq
    receiving := receiver.completion
    issued := receiver.issued
    extension := .refl _
    registry := receiver.registry.symm ▸ returnedRegistry
    history := retained }
  exact ⟨state, support.input.prepared.available, _, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreNamedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsStep
/-! The zero-iteration loop starts from the exact session and heap reached by the nonempty loop. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.drain {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session []) {value : Core.Word}
    (call : ObservedCall observed session value) (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session [],
      SourceCall support support.actual.header invocation state.heap [.word value]
        (.value (.word zero)) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.actual.header := by
    have singleton : ∀ header, header ∈ headers support.rows → header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact singleton _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word value] [.word value] := by
    rw [selectedHeader, support.actual.input_types]
    exact .cons (.data
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil
  have registry := request.started.simple_registry state.registry (by
    intro publicValue member
    have same : publicValue = .word value := List.mem_singleton.mp member
    subst publicValue
    exact .word value)
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selectedHeader]; exact support.descriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (extension := state.receiving.result.extension) (semantic := semantic)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := request.sourceAt)
      (invocation := invocation) call.started call.executed descriptor
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.actual.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans call.returned) (by rw [selectedHeader]; exact support.actual.output) result
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState support call.completion.session [] := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := retained }
  refine ⟨next, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · rw [← selectedHeader]; exact request.sourceAt
  · simpa only [outcomeValue] using trace

end Tests.SourceCoreNamedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsInitialForward
/-! The independent nonempty-loop trace determines both public fuel bounds at its
original checkpoint. Every sufficient resume returns Word11 and the same heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedInitial fixture observed) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        completion.value = .word zero ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedInitial fixture observed)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation ⟨[]⟩ [.word firstValue] (.value (.word zero)) after) :
    InitialForwardAt support first after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body)) [.word firstValue] [.word firstValue] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩
      ⟨.word firstValue, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word firstValue⟩)) .nil
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals)
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened)
      (fresh := first.fresh) (ready := .single first.ready) (authority := first.authority)
      (atSession := sessionAt) (atCheckpoint := checkpointAt) (started := started)
      (inputReceipts := inputs) (sourceAt := sourceAt) applied
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult, support.actual.result_type] at requested
  have nativeWord : _payload = .word zero := by
    have represented := _fullResult.2.1
    rw [support.actual.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr ready, returned, rfl⟩


end Tests.SourceCoreNamedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {value : Core.Word} (call : ObservedCall observed session value)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = .word zero ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_drain {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session []) {value : Core.Word}
    (call : ObservedCall observed session value) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation state.heap
      [.word value] (.value (.word zero)) after) :
    ForwardAt support call after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.actual.header := by
    have singleton : ∀ header, header ∈ headers support.rows → header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact singleton _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word value] [.word value] := by
    rw [selectedHeader, support.actual.input_types]
    exact .cons (.data
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.actual.result_type] at requested
  have nativeWord : payload = .word zero := by
    have represented := fullResult.2.1
    rw [selectedHeader, support.actual.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

end Tests.SourceCoreNamedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreNamedOperatorsPublicExecution
/-! An independently checked and compiled arithmetic loop executes three iterations
and then zero iterations through two public calls. Its real returned session carries the first
heap into the second call; each Source trace also entails sufficient public
execution and output fuel at that call's original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver)
      (first : RetainedState support sequence.initial.call.completion.session [])
      (second : RetainedState support sequence.next.completion.session []),
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.word firstValue] (.value (.word zero)) first.heap ∧
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        first.heap [.word secondValue] (.value (.word zero)) second.heap ∧
      InitialForwardAt support sequence.initial first.heap ∧
      ForwardAt support sequence.next second.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  obtain ⟨first, initialTrace⟩ := first_meaning support stages sequence.initial
  obtain ⟨second, nextTrace⟩ := first.drain sequence.next
    (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
  have initialReady : sequence.initial.session.ExportsReady :=
    (show sequence.initial.bootstrap.ReadyAt 100000 sequence.initial.session from .single sequence.initial.ready).exportsReady
      sequence.initial.authority
  have firstReady := sequence.initial.call.executed.exportsReady initialReady
  exact ⟨receiver, support, first, second, initialTrace, nextTrace,
    forward_initial support sequence.initial initialTrace,
    forward_drain first sequence.next firstReady nextTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed stages sequence
  IO.println "Actual arithmetic loop: 3→0 then0→0, exact Source histories and sufficient public fuel for both calls proved"

end Tests.SourceCoreNamedOperators
end
