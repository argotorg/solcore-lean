import Solcore.SourceSemantics.CoreLowering.RecursiveNamedAssignmentNativeCertificates
import Solcore.Test.SourceCoreUnifiedCorpusSupport

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
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (interpreted : receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults) :=
  ⟨receipt.profile interpreted⟩


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
