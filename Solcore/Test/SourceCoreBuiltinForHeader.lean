import Solcore.SourceSemantics.CoreLowering.BuiltinForHeader
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! A real for-item callback and native checker receipt produce a builtin
header certificate. The independent nested builtin trace closes its source
prefix and restored post environment. Checked loops exercise initialized and
absent headers, fresh post locals, earlier effects on failure and suspension. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreBuiltinForHeader
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality GeneralHeap ReadOnly CompatibleExpressionBuiltins
open TypedForHeader (Tail Result Fallthrough)
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"builtin_lexical", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "builtin_lexical.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "x", .mono .word, [], false, none⟩
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def assignment : AssignmentResolution := ⟨⟨binder.id, [], .word⟩, []⟩
private def scope : SourceCoreLocalCell.Scope := [(binder.id, .word)]
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[{type := .word, value := none}]⟩
private def after : Dynamic.Heap := ⟨[{type := .word, value := some (.word (Word.ofNatModulo 7))}]⟩
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def literalNode : ExpressionNode := {
  id := id 0, span, type := .word, form := .literal (.decimal "7")}
private def toNode : ExpressionNode := {
  id := id 1, span, type := BuiltinFunctionId.wordToInteger.type,
  form := .reference "wordToInteger" (.builtinFunction .wordToInteger)}
private def innerNode : ExpressionNode := {
  id := id 2, span, type := .integer, form := .call (id 1) [id 0] (.builtinFunction .wordToInteger)}
private def fromNode : ExpressionNode := {
  id := id 3, span, type := BuiltinFunctionId.wordFromInteger.type,
  form := .reference "wordFromInteger" (.builtinFunction .wordFromInteger)}
private def outerNode : ExpressionNode := {
  id := id 4, span, type := .word, form := .call (id 3) [id 2] (.builtinFunction .wordFromInteger)}
private def groupNode : ExpressionNode := {id := id 5, span, type := .word, form := .group (id 4)}
private def returned : StatementNode := ⟨⟨⟨owner, 10⟩⟩, span, .word, .returnStmt (some (id 5))⟩
private def source : TypedSource := {
  owner, inputs := [binder], roots := [.statement returned.id], nodes := [.expression literalNode, .expression toNode,
    .expression innerNode, .expression fromNode, .expression outerNode, .expression groupNode, .statement returned]}
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def policy (native : SourceCoreGeneralFunctions.CallableContext) : SourceCoreFunctions.Policy :=
  {SourceCoreCompatibleDataExpressions.functionPolicy 100 values with callables := SourceCoreGeneralFunctions.callablePolicy (some native) []}
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem wordAdmitted : TypeAdmissible context .word := .word (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures, Context.withLocal])
private theorem integerAdmitted : TypeAdmissible context .integer := .integer (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures, Context.withLocal])
private theorem literalTyped : ExpressionHasType source context (id 0) .word := by
  apply ExpressionHasType.ofOrdinary (node := literalNode) (rawType := .word) (lookupExpression?_sound (by rfl))
    (.literal (.intro (numericLiteralValue?_sound (value := 7) (by rfl)))) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem innerTyped : ExpressionHasType source context (id 2) .integer := by
  apply ExpressionHasType.ofOrdinary (node := innerNode) (rawType := .integer) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := toNode) (by cbv)) rfl rfl rfl rfl)
      (.cons literalTyped (.nil _))) integerAdmitted integerAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem outerTyped : ExpressionHasType source context (id 4) .word := by
  apply ExpressionHasType.ofOrdinary (node := outerNode) (rawType := .word) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := fromNode) (by cbv)) rfl rfl rfl rfl)
      (.cons innerTyped (.nil _))) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem groupTyped : ExpressionHasType source context (id 5) .word := by
  apply ExpressionHasType.ofOrdinary (node := groupNode) (rawType := .word) (lookupExpression?_sound (by cbv))
    (.group outerTyped) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem literalSyntax : CompatibleExpressionGeneral.Syntax source (id 0) :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literalNode) (by rfl) (.word _)))))))
private theorem innerSyntax : Syntax source (id 2) :=
  .builtin (node := innerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact .fragment literalSyntax)
private theorem outerSyntax : Syntax source (id 4) :=
  .builtin (node := outerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact innerSyntax)
private theorem syntaxTree : Syntax source (id 5) := .group (node := groupNode) (by cbv) rfl outerSyntax
private theorem noCoercions : ∀ expression node, source.lookupExpression? expression = some node → node.coercions = [] := by
  intro expression node found
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private def functions (ambient : AmbientDefinitions checked.catalog.definitions) : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def identities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful identities := ⟨fun impossible => False.elim impossible, fun impossible => False.elim impossible⟩
private theorem functionLeaves (ambient : AmbientDefinitions checked.catalog.definitions) : CompatibleEquality.FunctionObservations checked.catalog (functions ambient) identities := fun impossible => False.elim impossible
private theorem functionTypes (ambient : AmbientDefinitions checked.catalog.definitions) : FunctionRuntimeViews (functions ambient) := fun impossible => False.elim impossible
private def faults : FunctionCalls.FaultRep := fun reason token =>
  (∃ location, reason = .uninitializedLocation location ∧ token = Word.zero) ∨
  (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ reason = .missingMappingDefault value ∧ token = Word.zero.add tag) ∨
  (reason = .invalidAssignmentOperands .equal ∧ token = Word.zero)
private theorem uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id) :=
  fun _ location => .inl ⟨location, rfl, rfl⟩
private theorem missing : ∀ id key value tag, MetadataRep values.registry (.mapping key value) tag →
  faults (.missingMappingDefault value) ((reasonAt id).add tag) :=
  fun _ key value tag owned => .inr (.inl ⟨key, value, tag, owned, rfl, rfl⟩)
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures, Context.withLocal]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem innerTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source environment before (id 2) (.value (.integer 7)) before :=
  BuiltinCalls.source_intro (checked := checked) (type := .integer) ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl
    (.apply (.cons (.intro (lookupExpression?_sound (node := literalNode) (by rfl))
      (.literal rfl (.word (numericLiteralValue?_sound (value := 7) (by rfl)))) .nil) .nil)
      (.value (.builtin (.wordToInteger (Word.ofNatModulo 7)))))
private theorem outerTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source environment before (id 4) (.value (.word (Word.ofNatModulo 7))) before := by
  cases innerTrace with
  | value evaluated =>
    exact BuiltinCalls.source_intro (checked := checked) (type := .word)
      ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl (.apply (.cons evaluated .nil) (.value (.builtin (.wordFromInteger 7))))
private theorem sourceTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source environment before (id 5) (.value (.word (Word.ofNatModulo 7))) before := by
  cases outerTrace with
  | value evaluated => exact .value (.intro (lookupExpression?_sound (node := groupNode) (by cbv)) (.group rfl evaluated) .nil)

private theorem writable : WritableLocal context binder.id .word := by
  apply WritableLocal.withLocal_mono_admissible
  exact .word (by simp [TypeParameterBindersWellFormed, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])

private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope context := by
  intro localId declared index native selected binding
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst localId
    have sameBinder := Except.ok.inj ((show SourceCoreDataPlaces.rootBinder source binder.id = .ok binder from rfl).symm.trans binding)
    subst declared
    exact .head
  · cases selected

private theorem sourceAssigned : Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
    environment before assignment.target (id 5) (.word (Word.ofNatModulo 7)) after := by
  have read : Dynamic.Heap.Reads before ⟨0⟩ {type := .word, value := none} := .intro .head
  have initial : Dynamic.RootInitialValue {type := .word, value := none} none :=
    .uninitialized (by rintro ⟨key, value, impossible⟩; cases impossible)
  refine .intro (targetHeap := before) (rhsHeap := before) (rightValue := .word (Word.ofNatModulo 7))
    (target := ⟨⟨0⟩, .word, .word, [], none⟩) ?_ ?_ ?_
  · exact Dynamic.SourcePlaceResolves.intro (place := assignment.target) (environment := environment) .head read .nil read initial .nil
  · cases sourceTrace with | value evaluated => exact evaluated
  · exact .intro read rfl initial (.leaf (.equal none (.word (Word.ofNatModulo 7)))) (.intro read .head)

private def items : List ForItemForm := [.expression (id 5), .assignValue assignment .equal (id 5)]
private theorem headerSyntax : BuiltinForHeader.Syntax source context items := by
  apply GenericForHeader.Syntax.discard (expressionNode := groupNode) (by cbv) groupTyped syntaxTree
  apply GenericForHeader.Syntax.assign
  · intro actual binding
    have same := Except.ok.inj ((show SourceCoreDataPlaces.rootBinder source binder.id = .ok binder from rfl).symm.trans binding)
    subst actual
    exact .nil _
  · intro actual binding
    have same := Except.ok.inj ((show SourceCoreDataPlaces.rootBinder source binder.id = .ok binder from rfl).symm.trans binding)
    subst actual
    exact writable
  · exact groupTyped
  · exact .inl rfl
  · intro expression member
    have same : expression = id 5 := by simpa only [assignment, DataPlaceKeyOrder.sourceKeys, List.mem_singleton] using member
    subst expression
    exact ⟨syntaxTree, groupNode, by cbv, groupTyped⟩
  · exact .nil

private theorem headerTrace : Dynamic.ForItemsExecute program context [] source environment before items context environment after := by
  cases sourceTrace with
  | value trace => exact .cons (.expression trace) (.cons (.assignValue sourceAssigned) .nil)

section CompilerBridge
variable {layouts : SourceCoreAllocationLayouts.Prepared} {specialization : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {administrative : Core.Context} {definitions : DataEnvironment} {loopPolicy : SourceCoreLoops.Policy}
  (nativeContext : SourceCoreGeneralFunctions.CallableContext)
  (expressionPolicy : loopPolicy.lowerExpression = fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy (policy nativeContext) noBody fuel compilation source scope id reasonAt)
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
  {fuel : Nat} {site : SourceCoreElaboration.ErrorSite} {code : Expr} {nativeType : Ty}
  (accepted : SourceCoreLoops.lowerForItems loopPolicy site fuel source scope items .word reasonAt
    (fun _ => .ok (LocalLoop.fallthrough .word)) = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren accepted nativeTyped in
/-- Actual lowering closes concrete expression certificates; remaining inputs
are independent source typing and real Core checker facts. -/
theorem certified : BuiltinForHeader.Tree layouts specialization active frame globals onError 100 values source [] reasonAt
    definitions administrative .word (Fallthrough .word) context scope items code := by
  apply GenericForHeader.tree_of_lowerForItems binderPolicy allocationPolicy matched unaryPolicy unique ?_
    (fun _ _ _ _ _ _ _ generated => Except.ok.inj generated.symm) headerSyntax rfl rfl rfl declarations accepted (infer_sound nativeTyped)
  intro current scope budget expression nodeCode closed residual sourceSignatures declarations syntaxValue expressionNode found typed generated
  exact ⟨CompatibleExpressionBuiltins.tree_of_functions unique declarations sourceSignatures closed residual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ nativeContext [] rfl
    (fun _ _ _ found => noCoercions _ _ found) syntaxValue found typed (expressionPolicy ▸ generated),
    nativeChildren current scope budget expression expressionNode nodeCode closed residual sourceSignatures declarations syntaxValue found typed generated⟩

variable {ambient : AmbientDefinitions checked.catalog.definitions}
  (sameDefinitions : definitions = ambient.definitions)
  (layoutDefinitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  (errors : GenericForHeader.Tree.Errors values.registry faults
    (certified nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren accepted nativeTyped))
  {mapping : LocationMap} {world : StoreTyping} {canonical actual : Environment} {actualContext : Core.Context}
  {store : Store} {ξ : Renaming} {location : Location} {native : CallableIndexedHistory.NativeFrame}
  (environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleHeap.HeapRepresents checked values.registry (functions ambient) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type location))
  (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native))
  (unmapped : location ∉ mapping)

include expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren accepted nativeTyped sameDefinitions layoutDefinitions registered environments heaps locals agrees actualTyped reference read unmapped in
theorem compiled_post_restores :
    ∃ tail : Tail (values := values) values.registry (functions ambient) source [] [] administrative frame globals location native (Fallthrough .word) context environment after,
      Evaluates actual store (code.rename ξ) (LocalLoop.fallthroughValue .word) tail.store ∧
      CompatibleHeap.HeapRepresents checked values.registry (functions ambient) tail.mapping tail.world after tail.store ∧
      DataHeap.EnvRepresents (storageCatalog checked.catalog) tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧ RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions := by
  subst definitions
  have tree := certified nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren accepted nativeTyped
  obtain ⟨tail, _, _, _, _, evaluated, outer, restored, typed⟩ := BuiltinForHeader.Tree.preserves_post
    (values := values) (ambient := ambient) (functions ambient) layoutDefinitions registered (.refl _) program [] uninitialized missing faithful
    (functionLeaves ambient) (functionTypes ambient) tree valid unique environments heaps locals agrees actualTyped reference read unmapped headerTrace
  exact ⟨tail, evaluated, tail.heaps, outer, restored, typed⟩

include expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren accepted nativeTyped sameDefinitions layoutDefinitions registered errors environments heaps locals agrees actualTyped reference read unmapped in
theorem compiled_post_reflects {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    Result (values := values) values.registry (functions ambient) program source [] [] administrative frame globals location native .word faults (Fallthrough .word)
      context environment before items mapping world store value finalStore := by
  subst definitions
  have tree := certified nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren accepted nativeTyped
  exact BuiltinForHeader.Tree.reflects (values := values) (ambient := ambient) (functions ambient) layoutDefinitions registered (.refl _) program []
    uninitialized missing faithful (functionLeaves ambient) (functionTypes ambient) tree errors valid unique
    environments heaps locals agrees actualTyped reference read unmapped completed
end CompilerBridge

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function mixed(seed: Word) returns (integer) { let sum = 0; for (let i: Word, i = wordFromInteger(wordToInteger(seed)), let flag: Bool = integerEq(wordToInteger(seed), wordToInteger(seed)); i < 3; let copy = wordFromInteger(wordToInteger(i)), i = wordFromInteger(integerAdd(wordToInteger(copy), 1))) { if (flag) { sum += i; } } return wordToInteger(sum); }",
    "function shadow(seed: Word) returns (integer) { let i = 17; for (let i = wordFromInteger(wordToInteger(seed)); i < 2; let copy = wordFromInteger(wordToInteger(i)), i = copy + 1) { continue; } return wordToInteger(i); }",
    "function falseFirst(seed: Word) returns (integer) { for (let i = wordFromInteger(integerAdd(wordToInteger(seed), 5)); false; let never = wordToInteger(seed)) { return wordToInteger(seed); } return 5; }",
    "function breaks(seed: Word) returns (integer) { for (let i = wordFromInteger(wordToInteger(seed)); true; let never = wordToInteger(seed)) { break; } return 1; }",
    "function returns(seed: Word) returns (integer) { for (let i = wordFromInteger(wordToInteger(seed)); true; let never = wordToInteger(seed)) { return wordToInteger(i); } return 1; }",
    "function initializerFault(seed: Word) returns (integer) { let gap: Word; let seen: mapping(Bool => Word); for (let ready = wordFromInteger(integerAdd(wordToInteger(seed), 1)), let dead = integerAdd(wordToInteger(seen[false]), wordToInteger(gap)); true; ) { return 0; } return 1; }",
    "function postFault(seed: Word) returns (integer) { let gap: Word; let seen: mapping(Bool => Word); for (let i = wordFromInteger(wordToInteger(seed)); true; let copy = wordFromInteger(wordToInteger(i)), i = wordFromInteger(integerAdd(wordToInteger(seen[false]), wordToInteger(gap))), let never = wordToInteger(seed)) { continue; } return 1; }",
    "function postAbsent(seed: Word) returns (integer) { for (let i = wordFromInteger(wordToInteger(seed)); true; let absent: Word, i = wordFromInteger(wordToInteger(absent))) { continue; } return 1; }"
  ]}] }
private def escape : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function main(seed: Word) returns (integer) { for (let i = seed; false; let copy = wordToInteger(i)) { } return copy; }"}] }
private def arguments : List SourceCompilerFeatureSupport.Value := [.word Word.zero]
private def inputCells : List (TypeSystem.Ty × Option SourceCompilerFeatureSupport.Value) := [(.word, some (.word Word.zero))]
private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke arguments
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "builtin header fixture unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "builtin header fault lost source diagnostic"
  for fuel in [0, 10, 35, 100] do
    let started ← SourceCompilerFeatureSupport.get "builtin header suspension"
      (← complete.initial.run complete.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed, complete.outcome with
    | .failed actual heap, .failed expected initial =>
        SourceCompilerFeatureSupport.require (actual == expected && heap.heapSize == initial.heapSize)
          "builtin header resume changed fault or allocated past failure"
    | _, _ => throw (IO.userError "builtin header resume changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "builtin for header checker" (checkProgram workspace)
  for (name, result) in [("mixed", 3), ("shadow", 17), ("falseFirst", 5), ("breaks", 1), ("returns", 0)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let expected : SourceCompilerFeatureSupport.Value := .integer result
    SourceCompilerFeatureSupport.require ((← entry.run arguments) == expected) s!"{name}: builtin header value changed"
    entry.checkResume arguments expected
  let mixed ← SourceCompilerFeatureSupport.compileNamed checked "mixed"
  mixed.checkCells arguments (inputCells ++ [(.word, some (SourceCompilerFeatureSupport.scalar 3)), (.word, some (SourceCompilerFeatureSupport.scalar 3)),
    (.bool, some (.bool true)), (.word, some (SourceCompilerFeatureSupport.scalar 0)),
    (.word, some (SourceCompilerFeatureSupport.scalar 1)), (.word, some (SourceCompilerFeatureSupport.scalar 2))])
  let shadow ← SourceCompilerFeatureSupport.compileNamed checked "shadow"
  shadow.checkCells arguments (inputCells ++ [(.word, some (SourceCompilerFeatureSupport.scalar 17)), (.word, some (SourceCompilerFeatureSupport.scalar 2)),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 1))])
  for (name, stored) in [("falseFirst", 5), ("breaks", 0), ("returns", 0)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    entry.checkCells arguments (inputCells ++ [(.word, some (SourceCompilerFeatureSupport.scalar stored))])
  let initializer ← SourceCompilerFeatureSupport.compileNamed checked "initializerFault"
  failureResume initializer
  initializer.checkCells arguments (inputCells ++ [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 1))])
  let post ← SourceCompilerFeatureSupport.compileNamed checked "postFault"
  failureResume post
  post.checkCells arguments (inputCells ++ [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 0))])
  let absent ← SourceCompilerFeatureSupport.compileNamed checked "postAbsent"
  failureResume absent
  absent.checkCells arguments (inputCells ++ [(.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, none)])
  SourceCompilerFeatureSupport.require (checkProgram escape).toOption.isNone "builtin post local escaped its lexical scope"
  IO.println "builtin for headers: concrete children, marked prefix, post scope restoration, fault effects and resume GREEN"
end Tests.SourceCoreBuiltinForHeader
