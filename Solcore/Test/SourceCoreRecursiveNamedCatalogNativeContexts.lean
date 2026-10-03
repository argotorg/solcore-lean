import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfileFactory
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual cached loops with named globals certify their free-slot support.
Formal consumers retain exact code, real body state and arbitrary actual
embedding. Remaining source/child/diagnostic laws are not inferred from native
or runtime types. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCatalogNativeContexts
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
theorem actual_extraction (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
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
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) lowered.expression
          (LanguageResult.resultType lowered.type) ambient.definitions)
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
  RecursiveNamedCatalogProfileFactory.extract diagnosticPolicy factory readPolicy binderPolicy allocationPolicy
    expressions assignments unaryPolicy assignmentExpressions syntaxTree closed residual sourceSignatures declarations
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

theorem unused_suffix_changes (suffix : Core.Context) :
    HasType (.word :: suffix) (.var 0) .word [] := by
  exact prefix_typing (leading := [.word]) (sourceSuffix := [.bool, .integer])
    (targetSuffix := suffix) (.var rfl) rfl

theorem used_suffix_not_supported : supported (.var 1) 1 = false := rfl

theorem used_suffix_cannot_disappear : ¬ HasType [.word] (.var 1) .bool [] := by
  intro typed
  cases typed with | var found => cases found

theorem bound_under_lambda : supported (.lambda .word .word (.var 0)) 0 = true := rfl

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function step(value: Word) returns (Word) { return value + 1; }",
    "function loop(flag: Bool, seed: Word) returns (Word) { let result = seed; for (let i = 0; i < 3; i = step(i)) { let j = 0; while (j < 2) { result = step(result); j = step(j); } } if (flag) { return step(result); } return result; }",
    "function recursive(value: Word) returns (Word) { if (value == 0) { return 1; } return step(recursive(value - 1)); }",
    "function order(first: Word, flag: Bool, last: Word) returns (Word) { if (flag) { return step(first); } return step(last); }",
    "function make(seed: Word) returns (function(Word) returns (Word)) { let extra = step(seed); return lam(value: Word) -> Word { let i = 0; while (i < 2) { extra = step(extra); i = step(i); } return extra + value; }; }"
  ]}] }

open Tests.SourceCompilerFeatureSupport in
private def checkSupport (entry : Entry) : IO Unit := do
  let prepared := entry.cached.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "actual named diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "actual named parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let leading := prepared.base.globals.map (·.referenceType) ++ [.cell prepared.ancestry.layout.frame.type]
  require (!prepared.entries.isEmpty && !prepared.base.globals.isEmpty) "actual checked roots/globals missing"
  require (prepared.base.globals.length == prepared.base.functions.length) "full inventory order mismatch"
  for (named, index) in prepared.base.functions.zipIdx do
    let own ← match diagnostics.base.find? named.signature.key with
      | some own => pure own | none => throw (IO.userError "actual named diagnostic function missing")
    let statements ← get "actual named roots" ((CallableIndexedNamedGeneration.source named).roots.mapM
      (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "actual named source body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    let parameters ← get "actual parameter allocation"
      (SourceCoreSourceCells.bindParameters (CallableIndexedNamedGeneration.allocator prepared named)
        (CallableIndexedNamedGeneration.source named) [] named.inputs named.signature.resultType
        SourceCoreFunctions.argumentProjection body)
    let output ← get "actual named frame hook"
      (SourceCoreCallableIndexedAncestry.namedBody prepared.ancestry named parameters)
    let code ← match prepared.secondPass.closures[index]? with
      | some code => pure code | none => throw (IO.userError "actual cached closure missing")
    require (prepared.base.globals[index]? == some named.signature) "ordered complete signature mismatch"
    require (code == .lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output)
      "body action did not reproduce the actual cached lambda"
    require (supported code leading.length) "actual cached code reads a hidden wrapper input"
    let bodyLeading := SourceCoreLocalCell.coreContext (named.inputs.reverse.map (fun b => (b.1.id, b.2))) ++
      named.signature.parameterType :: leading
    require (supported body bodyLeading.length) "actual body support escaped parameters/global/frame prefix"
    for root in prepared.entries do
      let wrapper := SourceCoreGeneralEntry.nativeInputContext root.native.inputTypes
      for suffix in [wrapper, [], [.integer, .bool, .function .unit .word]] do
        require (Core.infer? (leading ++ suffix) code prepared.layouts.definitions == some named.signature.functionType)
          "cached closure native typing changed with unused suffix"
        require (Core.infer? (bodyLeading ++ suffix) body prepared.layouts.definitions ==
          some (LanguageResult.resultType named.signature.resultType)) "actual named body lost canonical prefix typing"
    -- Original arguments remain before globals; an actual inserted slot uses syntax renaming.
    let hidden := [.integer, .bool]
    let shifted := code.rename (Renaming.insertion 0)
    require (Core.infer? (.integer :: leading ++ hidden) shifted prepared.layouts.definitions == some named.signature.functionType)
      "actual hidden insertion lost native cached typing"

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let checked ← get "native context source checker" (checkProgram workspace)
  for (name, arguments, expected) in [
      ("loop", [(.bool true : SourceCoreExecution.Value), scalar 2], scalar 9),
      ("loop", [(.bool false : SourceCoreExecution.Value), scalar 7], scalar 13),
      ("recursive", [scalar 4], scalar 5),
      ("order", [scalar 11, (.bool false : SourceCoreExecution.Value), scalar 17], scalar 18)] do
    let entry ← compileNamed checked name
    checkSupport entry
    require ((← entry.run arguments) == expected) "actual source result changed"
    for fuel in [0, 7, 43] do entry.checkResume arguments expected fuel
  let entry ← compileNamed checked "make"
  checkSupport entry
  let invocation ← entry.invoke [scalar 5]
  let done ← match invocation.outcome with
    | .succeeded done => pure done | _ => throw (IO.userError "actual closure creation failed")
  let handle ← match done.value with
    | .function handle => pure handle | _ => throw (IO.userError "actual closure result missing")
  let completed ← get "actual captured closure invocation" (← done.session.invokePacked handle (scalar 3) executionOptions)
  let final ← match completed with
    | .succeeded final => pure final | _ => throw (IO.userError "actual captured closure failed")
  require (final.value == scalar 11) "actual capture or global call changed"
  let baseline ← get "actual final snapshot" (← final.session.snapshot 2048)
  for fuel in [0, 7, 43] do
    let pending ← get "actual captured suspension"
      (← done.session.invokePacked handle (scalar 3) {executionOptions with executionFuel := fuel})
    let resumed ← match pending with
      | .outOfFuel pending => pending.resume 300000 2048 | complete => pure complete
    match resumed with
    | .succeeded actual =>
      let snapshot ← get "resumed final snapshot" (← actual.session.snapshot 2048)
      require (actual.value == final.value && reprStr snapshot.cells == reprStr baseline.cells)
        "resume changed captured values or ordered heap cells"
    | _ => throw (IO.userError "actual capture resume failed")
  IO.println "catalog native contexts: actual cached support, full global slots, canonical body/actual embedding, altered unused suffixes, loop/global/closure execution and resume GREEN"

end Tests.SourceCoreRecursiveNamedCatalogNativeContexts
