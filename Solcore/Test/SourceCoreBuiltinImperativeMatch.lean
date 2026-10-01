import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatch
import Solcore.Test.SourceCoreGenericImperativeMatch
import Solcore.Test.SourceCompilerFeatureSupport

/-! Finite actual match children preserve duplicate occurrence order. The
recursive statement receipt admits matches inside loops and restores source
contexts from declarative pattern typing, independently of native type equality.
The final concrete builtin consumer closes match body and child expression meaning,
while source declarations, native checker receipts and pattern contexts remain static. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreBuiltinImperativeMatch
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
  (childStatic : GenericImperativeMatch.MatchChildStatic matchCompilation source
    (fun context => CompatibleExpressionBuiltins.Tree 100 values source context [] reasonAt) definitions administrative)
  {scope : SourceCoreLocalCell.Scope}
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  {mode : Bool} {fuel : Nat} {selfReason : Word} {code : Expr} {nativeType : Ty}
  (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy loopPolicy fuel source scope [site] .unit reasonAt mode selfReason = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include matchPolicy matchValues matchDefinitions matchAllocator childStatic expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped in
/-- Every builtin child is extracted from the actual expression lowerer. Only
source typing and actual native checker facts remain as static conditions. -/
theorem certified : BuiltinImperativeMatch.Tree layouts specialization active frame globals onError 100 values source [] reasonAt
    definitions administrative context scope (.statements mode [site]) .unit .unit code := by
  apply GenericImperativeMatch.tree_of_typed_flow matchPolicy matchValues matchDefinitions matchAllocator childStatic matched.read binderPolicy allocationPolicy ?_ matched unaryPolicy unique ?_
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

variable {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (sameDefinitions : definitions = ambient.definitions)
  (layoutDefinitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  (valid : CompatibleExpressionLiterals.ContextValid [] context []) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (errors : GenericImperativeMatch.Tree.Ready registry faults (certified nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren matchPolicy matchValues matchDefinitions matchAllocator childStatic declarations accepted nativeTyped))
  {mapping : LocationMap} {world : StoreTyping} {canonical actual : Environment} {actualContext : Core.Context}
  {store : Store} {ξ : Renaming} {location : Location} {native : CallableIndexedHistory.NativeFrame}
  (environments : DataHeap.EnvRepresents (storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type location))
  (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native))
  (unmapped : location ∉ mapping)

include matchPolicy matchValues matchDefinitions matchAllocator childStatic expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped sameDefinitions layoutDefinitions registered extension catalogValid valid uninitialized missing faithful observations runtimeViews errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_preserves :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      TypedLexicalWhile.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .unit .unit (.fallthrough environment) value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment context after := by
  cases sameDefinitions
  exact (certified nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren matchPolicy matchValues matchDefinitions matchAllocator childStatic declarations accepted nativeTyped).preserves functions layoutDefinitions registered catalogValid extension program []
    uninitialized missing faithful observations runtimeViews errors valid unique environments heaps locals agrees typed reference read unmapped (sourceTrace mode)

include matchPolicy matchValues matchDefinitions matchAllocator childStatic expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped sameDefinitions layoutDefinitions registered extension catalogValid valid uninitialized missing faithful observations runtimeViews errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_reflects {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ finalContext outcome sourceHeap finalMap finalWorld,
      TypedScopedStatements.Executes mode program context [] source environment before [site] finalContext outcome sourceHeap ∧
      TypedLexicalWhile.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .unit .unit outcome value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld sourceHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before sourceHeap ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext sourceHeap := by
  cases sameDefinitions
  exact (certified nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren matchPolicy matchValues matchDefinitions matchAllocator childStatic declarations accepted nativeTyped).reflects functions layoutDefinitions registered catalogValid extension program []
    uninitialized missing faithful observations runtimeViews errors valid unique environments heaps locals agrees typed reference read unmapped completed
end CompilerBridge

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function emptyDefault(seed: Word) returns (integer) { match (seed) { case 0 {} default {} } return wordToInteger(seed); }",
    "function constructed(seed: Word) returns (integer) { match (Box((seed, 7))) { case .Box((0, x)) { return integerAdd(wordToInteger(x), 1); } case .Box((x, y)) { for (let i = 0; integerLt(wordToInteger(i), 2); i += 1) { match (i) { case 0 { continue; } default { return integerAdd(wordToInteger(x), wordToInteger(y)); } } } } } return 99; }",
    "function scrutineeFault(seed: Word) returns (integer) { let seen: mapping(Bool => Word); let missing: Word; match (wordFromInteger(integerAdd(wordToInteger(seen[false]), wordToInteger(missing)))) { case x { return wordToInteger(x); } default { return 99; } } return 0; }"
  ]}] }
private def nonExhaustive : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function incomplete(seed: Word) returns (integer) { match (seed) { case 0 {} } return wordToInteger(seed); }"}] }
private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCompilerFeatureSupport.Value) : IO Unit := do
  let complete ← entry.invoke arguments
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "match scrutinee unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "match scrutinee lost its diagnostic"
  for fuel in [0, 7, 43] do
    let started ← SourceCompilerFeatureSupport.get "match suspension"
      (← complete.initial.run complete.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
    | .failed actual _ => SourceCompilerFeatureSupport.require (actual == token) "resumed match fault changed its token"
    | _ => throw (IO.userError "resumed match fault executed its continuation")

/-- The checked runtime fixtures use the same recursive grammar with builtin
children, nested loops, ordered patterns, shadowed binders and exact fault cells. -/
def run : IO Unit := do
  Tests.SourceCoreGenericImperativeMatch.run
  match checkProgram nonExhaustive with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "non-exhaustive match unexpectedly passed the existing checker")
  let checked ← SourceCompilerFeatureSupport.get "builtin match checker" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  let emptyDefault ← SourceCompilerFeatureSupport.compileNamed checked "emptyDefault"
  for n in [0, 3] do
    SourceCompilerFeatureSupport.require ((← emptyDefault.run [w n]) == .integer n) "empty-default match changed fallthrough"
    for fuel in [0, 7, 43] do emptyDefault.checkResume [w n] (.integer n) fuel
  let constructed ← SourceCompilerFeatureSupport.compileNamed checked "constructed"
  for (n, expected) in [(0, 8), (3, 10)] do
    SourceCompilerFeatureSupport.require ((← constructed.run [w n]) == .integer expected) "constructor match/for/return changed branch ordering"
    for fuel in [0, 7, 43] do constructed.checkResume [w n] (.integer expected) fuel
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "scrutineeFault"
  faultResume failed [w 0]
  failed.checkCells [w 0] [(.word, some (w 0)), (.mapping .bool .word, some (.mapping .bool .word [])), (.word, none)]
  IO.println "builtin imperative match: independent source/Core consumers, constructor branches, empty-default fallthrough, scrutinee fault effects and resume GREEN"
end Tests.SourceCoreBuiltinImperativeMatch
