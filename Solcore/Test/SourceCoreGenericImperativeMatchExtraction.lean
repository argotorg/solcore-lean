import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchExtraction
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual flow extraction now retains all fixed match ledgers. The formal
consumer builds Ready from source context validity and the unchanged diagnostic
obligations, without a caller-supplied ledger tree or runtime child premise. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreGenericImperativeMatchExtraction
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GenericMatchChildren BuiltinImperativeMatch GeneralHeap CompatiblePayload CompatibleEquality ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"generic_match", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "generic_match.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def scrutinee : ExpressionId := ⟨⟨owner, 1⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 0⟩
private def pattern : TypedMatchPattern := {source := .wildcard span span, type := .unit, resolution := .wildcard}
private def arm : TypedMatchCase := ⟨span, pattern, []⟩
private def resolution : MatchResolution := ⟨scrutinee, hidden, [arm, arm], some [], []⟩
private def scrutineeNode : ExpressionNode := {id := scrutinee, span, type := .unit, form := .tuple []}
private def statementNode : StatementNode := ⟨site, span, .unit, .matchWith resolution⟩
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement site]
  nodes := [.statement statementNode, .expression scrutineeNode]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def control : ControlContext := ⟨.unit, 0⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.get catalogExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [⟨[.unit]⟩]
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some ambient.definitions⟩
private def lowerExpression : SourceCoreCompatibleDataMatches.ExpressionLowerer := fun _ _ _ _ _ =>
  .ok ⟨.unit, LanguageResult.success .unit⟩
private def lowerBody : SourceCoreCompatibleDataMatches.BodyLowerer := fun _ _ _ _ _ _ _ => .ok (LocalLoop.fallthrough .unit)
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def compiled : Expr := match SourceCoreCompatibleDataMatches.lowerWithReasons compilation lowerExpression lowerBody
    20 source [] site resolution .unit reasonAt Word.zero with | .ok code => code | .error _ => .unit
private theorem accepted : SourceCoreCompatibleDataMatches.lowerWithReasons compilation lowerExpression lowerBody
    20 source [] site resolution .unit reasonAt Word.zero = .ok compiled := by rfl

/-- Even equal request data appears three times: both source arms and default. -/
theorem finite_actual_children : ∃ requests,
    CompatibleMatchCertificates.Certificate compilation source [] site resolution .unit Word.zero
      (fun _ _ lowered => lowered = ⟨.unit, LanguageResult.success .unit⟩) (Occurs requests) compiled ∧
    requests.length = 3 ∧ ∀ request ∈ requests, ∃ fuel,
      lowerBody fuel source request.scope request.statements .unit reasonAt Word.zero = .ok request.code := by
  simpa only [resolution, List.length_cons, List.length_nil, Option.isSome_some, ↓reduceIte] using
    finite_of_lower (fun _ _ generated => Except.ok.inj generated.symm) accepted

private def request : Request := ⟨[(hidden, .unit)], [], LocalLoop.fallthrough .unit⟩
private def compiledPattern : SourceCoreCompatibleDataMatches.Pattern :=
  ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
example : armRequests [(hidden, .unit)] resolution.cases
    [(compiledPattern, LocalLoop.fallthrough .unit), (compiledPattern, LocalLoop.fallthrough .unit)] ++
    fallbackRequests [(hidden, .unit)] resolution.defaultBody (LocalLoop.fallthrough .unit) =
      [request, request, request] := rfl

private theorem patternTyped : TypedMatchPatternHasType context pattern .unit [] 0 :=
  ⟨rfl, .wildcard, .wildcard, ⟨by simp, by simp⟩⟩
private theorem casesTyped : MatchCasesHaveType source control context .unit resolution.cases
    [BodyFacts.empty, BodyFacts.empty] := by
  exact .cons (.intro patternTyped (.nil _) (.nil _ _))
    (.cons (.intro patternTyped (.nil _) (.nil _ _)) (.nil _ _ _))
private theorem sourceSelected : Dynamic.MatchCasesSelect context .unit resolution.cases resolution.defaultBody (.arm [] []) :=
  .head (.intro .wildcard .wildcard)

theorem selected_context_is_source : ContextFor source context .unit resolution.cases resolution.defaultBody request context :=
  ContextFor.selected_arm_at request rfl casesTyped sourceSelected (.nil _)

private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem scrutineeTyped : ExpressionHasType source context scrutinee .unit := by
  have admitted : TypeAdmissible context .unit := .unit (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures])
  apply ExpressionHasType.ofOrdinary (node := scrutineeNode) (rawType := .unit) (lookupExpression?_sound (by cbv))
    (.tuple (.nil _)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private abbrev expressionSyntax := CompatibleExpressionBuiltins.Syntax source
private theorem unitSyntax : expressionSyntax scrutinee :=
  .fragment (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := scrutineeNode) rfl .unit)))))))
private theorem syntaxTree (mode : Bool) : GenericImperativeMatch.Syntax source expressionSyntax context (.statements mode [site]) .unit := by
  apply GenericImperativeMatch.Syntax.matchWith (expressionSyntax := expressionSyntax) (node := statementNode) (scrutineeNode := scrutineeNode)
    (control := control) (caseFacts := [BodyFacts.empty, BodyFacts.empty]) rfl rfl (.inl rfl) rfl scrutineeTyped unitSyntax casesTyped
  · intro statements selected
    have same : statements = [] := Option.some.inj selected.symm
    subst statements
    exact ⟨context, _, .nil _ _⟩
  · rfl
  · intro arm member binder found; rfl
  · intro request childContext selected
    have empty : request.statements = [] := by
      cases selected with
      | @arm actualArm binders arity childContext member same typed extended =>
        have armEq : actualArm = arm := by simpa [resolution] using member
        exact same.trans (congrArg TypedMatchCase.body armEq)
      | default same => exact Option.some.inj same.symm
    rw [empty]
    exact .body (.nil (.inl rfl))
  · exact .body (.nil (.inr rfl))

private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def environment : Dynamic.Environment := []
private def before : Dynamic.Heap := ⟨[]⟩
private def after : Dynamic.Heap := ⟨[{type := .unit, value := some .unit}]⟩
private def functionCompilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def expressionPolicy (native : SourceCoreGeneralFunctions.CallableContext) : SourceCoreFunctions.Policy :=
  {SourceCoreCompatibleDataExpressions.functionPolicy 100 values with callables := SourceCoreGeneralFunctions.callablePolicy (some native) []}
private theorem noCoercions : ∀ id node, source.lookupExpression? id = some node → node.coercions = [] := by
  intro id node found
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  subst member
  rfl
private theorem sourceTrace (mode : Bool) : TypedScopedStatements.Executes mode program context [] source environment before
    [site] context (.fallthrough environment) after := by
  have evaluated : Dynamic.ExpressionEvaluates program context [] source environment before scrutinee .unit before :=
    .intro (lookupExpression?_sound (show source.lookupExpression? scrutinee = some scrutineeNode from rfl)) (.tuple rfl .nil .nil) .nil
  have matched : Dynamic.StatementExecutes program context [] source environment before site context (.fallthrough environment) after :=
    .matchArm (lookupStatement?_sound (node := statementNode) rfl) rfl (lookupExpression?_sound (node := scrutineeNode) rfl)
      evaluated .append sourceSelected rfl rfl (.nil _) (.nil _ _) .nil
  exact TypedScopedStatements.prepend (lookupStatement?_sound (node := statementNode) rfl)
    (by intro _ _ _ impossible; cases impossible) matched (by cases mode <;> exact .control .nil)

private theorem hiddenSourceFresh : GenericImperativeMatch.MatchHiddenFresh source := by
  intro id node actualResolution found form
  have sameNode : node = statementNode := by
    have member := (lookupStatement?_sound found).1
    simpa [source] using member
  subst node
  have sameResolution : actualResolution = resolution := StatementForm.matchWith.inj form.symm
  subst actualResolution
  simp [SourceCoreDataPlaces.declaredBinders, SourceCoreDataPlaces.patternBinders,
    source, statementNode, scrutineeNode, resolution, arm, pattern]

section CompilerBridge
variable {layouts : SourceCoreAllocationLayouts.Prepared} {specialization : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {administrative : Core.Context} {definitions : DataEnvironment} {loopPolicy : SourceCoreLoops.Policy}
  (nativeContext : SourceCoreGeneralFunctions.CallableContext)
  (expressionPolicy : loopPolicy.lowerExpression = fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy (expressionPolicy nativeContext) noBody fuel functionCompilation source scope id reasonAt)
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingReason : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (matched : CompatibleAssignmentStatements.AssignmentPolicy loopPolicy values invalidProjection invalidOperand missingReason)
  (unaryPolicy : CompatibleBitNotStatements.Policy loopPolicy values invalidProjection invalidUnary missingReason)
  (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    loopPolicy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
  (allocationPolicy : loopPolicy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  (nativeChildren : ∀ current scope fuel id node lowered,
    current.typeVariables = [] → current.residualTypeVariables = false →
    current.signatures = values.checked.signatures → CompatibleExpressionReads.ScopeDeclarations source scope current →
    CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → ExpressionHasType source current id node.type →
    loopPolicy.lowerExpression fuel source scope id reasonAt = .ok lowered →
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
  {matchCompilation : SourceCoreCompatibleDataMatches.Context}
  (matchPolicy : loopPolicy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
  (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
  (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  {scope : SourceCoreLocalCell.Scope}
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  {mode : Bool} {fuel : Nat} {selfReason : Word} {code : Expr} {nativeType : Ty}
  (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy loopPolicy fuel source scope [site] .unit reasonAt mode selfReason = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include matchPolicy matchValues matchDefinitions matchAllocator expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped in
/-- Every builtin child is extracted from the actual expression lowerer. Only
source typing and actual native checker facts remain as static conditions. -/
theorem extracted : Nonempty (GenericImperativeMatch.Extraction layouts specialization active frame globals onError values source
    expressionSyntax (fun current => CompatibleExpressionBuiltins.Tree 100 values source current [] reasonAt)
    definitions administrative matchCompilation.solvedRequirements context scope (.statements mode [site]) .unit .unit code) := by
  apply GenericImperativeMatch.extraction_of_typed_flow (certificates := fun current => CompatibleExpressionBuiltins.Tree 100 values source current [] reasonAt) matchPolicy matchValues matchDefinitions matchAllocator (GenericImperativeMatch.MatchChildStatic.of_hidden (matchCompilation := matchCompilation) (certificates := fun current => CompatibleExpressionBuiltins.Tree 100 values source current [] reasonAt) (definitions := definitions) (administrative := administrative) hiddenSourceFresh) matched.read binderPolicy allocationPolicy ?_ matched unaryPolicy unique ?_
    (syntaxTree mode) rfl rfl rfl declarations (by cbv) accepted (infer_sound nativeTyped)
  · intro current closed residual signatures scope budget expression node lowered declarations syntaxValue found typed generated
    exact CompatibleExpressionBuiltins.tree_of_functions unique declarations signatures closed residual
      ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ nativeContext [] rfl
      (fun _ _ _ found => noCoercions _ _ found) syntaxValue found typed (expressionPolicy ▸ generated)
  · intro current scope budget expression lowered closed residual signatures declarations syntaxValue node found typed generated
    exact ⟨CompatibleExpressionBuiltins.tree_of_functions unique declarations signatures closed residual
      ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ nativeContext [] rfl
      (fun _ _ _ found => noCoercions _ _ found) syntaxValue found typed (expressionPolicy ▸ generated),
      nativeChildren current scope budget expression node lowered closed residual signatures declarations syntaxValue found typed generated⟩

include matchPolicy matchValues matchDefinitions matchAllocator expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped in
/-- The actual compiler receipt yields the match ledger at every recursive site.
Only diagnostic interpretation is deferred; there is no SiteLedgers or Ready input. -/
theorem accepted_ready_factory
    (sameLedger : matchCompilation.solvedRequirements = [])
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (valid : CompatibleExpressionLiterals.ContextValid [] context []) :
    ∃ certificate : GenericImperativeMatch.Extraction layouts specialization active frame globals onError values source
      expressionSyntax (fun current => CompatibleExpressionBuiltins.Tree 100 values source current [] reasonAt)
      definitions administrative matchCompilation.solvedRequirements context scope (.statements mode [site]) .unit .unit code,
      certificate.diagnostics registry faults → GenericImperativeMatch.Tree.Ready registry faults certificate.tree := by
  obtain ⟨certificate⟩ := extracted nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren
    matchPolicy matchValues matchDefinitions matchAllocator declarations accepted nativeTyped
  exact ⟨certificate, fun diagnostics => certificate.ready diagnostics (sameLedger.symm ▸ valid) rfl⟩

end CompilerBridge

/-- The ledger used by the real fixed match policy is definitionally the caller's
ledger, even when the values catalog and emitted empty bodies are identical. -/
theorem actual_policy_ledger (solved : List SolvedRequirement)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (expression : SourceCoreLoops.ExpressionLowerer)
    (sourceCells : Option SourceCoreSourceCells.Allocator) (definitions : Option DataEnvironment) :
    let policy := SourceCoreCompatibleDataMatches.loopPolicy values solved assignments diagnostics ⟨owner, []⟩ expression sourceCells definitions
    let compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, solved, sourceCells, definitions⟩
    policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons compilation) ∧
      compilation.solvedRequirements = solved := by
  exact ⟨rfl, rfl⟩

private def extractionWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Choice { Left(Word), Right(Word) }",
    "function sharedArms(seed: Word) returns (integer) { for (let i = 0; integerLt(wordToInteger(i), 2); i += 1) { match (Choice.Left(seed)) { case .Left(x) {} case .Right(y) {} default {} } } return wordToInteger(seed); }",
    "function scoped(seed: Word) returns (integer) { let total = seed; for (let i = 0; integerLt(wordToInteger(i), 2); i += 1) { match (Choice.Left(i)) { case .Left(0) { let x = 7; total += x; continue; } case .Left(x) { let y = x; total += y; } case .Right(y) {} default {} } } return wordToInteger(total); }"
  ]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "match extraction checker" (checkProgram extractionWorkspace)
  let shared ← SourceCompilerFeatureSupport.compileNamed checked "sharedArms"
  let scopeEntry ← SourceCompilerFeatureSupport.compileNamed checked "scoped"
  for seed in [0, 3] do
    let args := [SourceCompilerFeatureSupport.scalar seed]
    SourceCompilerFeatureSupport.require ((← shared.run args) == .integer seed) "equal empty arm bodies changed their source scopes"
    SourceCompilerFeatureSupport.require ((← scopeEntry.run args) == .integer (seed + 8)) "nested match/let/continue order changed"
    for fuel in [0, 7, 43] do
      shared.checkResume args (.integer seed) fuel
      scopeEntry.checkResume args (.integer (seed + 8)) fuel
  IO.println "match extraction: exact fixed ledger, duplicate empty arm scopes, lexical for/continue and resume GREEN"

end Tests.SourceCoreGenericImperativeMatchExtraction
