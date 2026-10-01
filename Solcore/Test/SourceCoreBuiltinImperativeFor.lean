import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeFor
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! A concrete nested builtin condition in actual for lowering closes all
expression semantics against an independent source trace. Runtime fixtures exercise repeated/nested
iterations, scoped allocations, transfers, fault ordering and resumption. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreBuiltinImperativeFor
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open BuiltinImperativeFor GeneralHeap CompatiblePayload CompatibleEquality ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"assignment_statement", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "assignment_statement.solc"⟩, 0, 1⟩
private def id (n : Nat) : ExpressionId := ⟨⟨owner, n⟩⟩
private def expression : ExpressionId := id 4
private def statement (n : Nat) : StatementId := ⟨⟨owner, n + 10⟩⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "x", .mono .bool, [], false, none⟩
private def assignment : AssignmentResolution := ⟨⟨binder.id, [], .bool⟩, []⟩
private def literalNode : ExpressionNode := { id := id 0, span, type := .word, form := .literal (.decimal "7") }
private def toNode : ExpressionNode := {
  id := id 1, span, type := BuiltinFunctionId.wordToInteger.type,
  form := .reference "wordToInteger" (.builtinFunction .wordToInteger) }
private def innerNode : ExpressionNode := { id := id 2, span, type := .integer, form := .call (id 1) [id 0] (.builtinFunction .wordToInteger) }
private def equalNode : ExpressionNode := {
  id := id 3, span, type := BuiltinFunctionId.integerEq.type,
  form := .reference "integerEq" (.builtinFunction .integerEq) }
private def literal : ExpressionNode := { id := expression, span, type := .bool, form := .call (id 3) [id 2, id 2] (.builtinFunction .integerEq) }
private def assigned : StatementNode := ⟨statement 0, span, .unit, .assignValue assignment .equal expression⟩
private def returned : StatementNode := ⟨statement 1, span, .bool, .returnStmt (some expression)⟩
private def breakNode : StatementNode := ⟨statement 2, span, .unit, .breakStmt⟩
private def loopNode : StatementNode := ⟨statement 3, span, .unit, .forLoop [.expression expression] expression [.assignValue assignment .equal expression] [statement 0, statement 2]⟩
private def statements := [statement 3, statement 1]
private def source : TypedSource := {
  owner := owner
  inputs := [binder]
  roots := statements.map .statement
  nodes := [.expression literalNode, .expression toNode, .expression innerNode, .expression equalNode, .expression literal, .statement assigned, .statement returned, .statement breakNode, .statement loopNode]
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[{type := .bool, value := none}]⟩
private def after : Dynamic.Heap := ⟨[{type := .bool, value := some (.bool true)}]⟩
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer, .bool]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer, .bool]).toOption.get checkExists
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
private theorem booleanTyped : ExpressionHasType source context expression .bool := by
  have admitted : TypeAdmissible context .bool := .bool (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures, Context.withLocal])
  apply ExpressionHasType.ofOrdinary (node := literal) (rawType := .bool) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := equalNode) (by cbv)) rfl rfl rfl rfl)
      (.cons innerTyped (.cons innerTyped (.nil _)))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem writable : WritableLocal context binder.id .bool := by
  apply WritableLocal.withLocal_mono_admissible
  exact .bool (by simp [TypeParameterBindersWellFormed, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
private theorem literalSyntax : CompatibleExpressionGeneral.Syntax source (id 0) :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literalNode) (by rfl) (.word _)))))))
private theorem innerSyntax : CompatibleExpressionBuiltins.Syntax source (id 2) :=
  .builtin (node := innerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact .fragment literalSyntax)
private theorem booleanSyntax : CompatibleExpressionBuiltins.Syntax source expression :=
  .builtin (node := literal) (by cbv) rfl (by
    intro child member
    have same : child = id 2 := by simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, or_self] using member
    subst child
    exact innerSyntax)
private theorem noCoercions : ∀ expression node, source.lookupExpression? expression = some node → node.coercions = [] := by
  intro expression node found
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem children : ∀ child, child ∈ expression :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
    CompatibleExpressionBuiltins.Syntax source child ∧ ∃ node, source.lookupExpression? child = some node ∧ ExpressionHasType source context child node.type := by
  intro child member
  have same : child = expression := by simpa only [assignment, DataPlaceKeyOrder.sourceKeys, List.mem_singleton] using member
  subst child
  exact ⟨booleanSyntax, literal, by cbv, booleanTyped⟩
private theorem assignmentSyntax {rest : List ForItemForm} (remaining : GenericForHeader.Syntax source (CompatibleExpressionBuiltins.Syntax source) context rest) :
    GenericForHeader.Syntax source (CompatibleExpressionBuiltins.Syntax source) context (.assignValue assignment .equal expression :: rest) := by
  apply GenericForHeader.Syntax.assign
  · intro actual found
    have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
    cases Except.ok.inj (this.symm.trans found)
    exact .nil _
  · intro actual found
    have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
    cases Except.ok.inj (this.symm.trans found)
    exact writable
  · exact booleanTyped
  · exact .inl rfl
  · exact children
  · exact remaining
private theorem syntaxTree (mode : Bool) : BuiltinImperativeFor.Syntax source context (.statements mode statements) .bool := by
  apply GenericImperativeFor.Syntax.forLoop (node := loopNode) rfl rfl rfl
  · apply GenericImperativeFor.Syntax.initializerDiscard (expressionNode := literal) rfl booleanTyped booleanSyntax
    apply GenericImperativeFor.Syntax.initializersDone (conditionNode := literal) rfl rfl booleanTyped booleanSyntax
    · apply GenericImperativeFor.Syntax.assign (node := assigned) rfl rfl
      · intro actual found
        have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
        cases Except.ok.inj (this.symm.trans found)
        exact .nil _
      · intro actual found
        have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
        cases Except.ok.inj (this.symm.trans found)
        exact writable
      · exact booleanTyped
      · exact .inl rfl
      · exact children
      · exact .breaking (node := breakNode) rfl rfl
    · exact assignmentSyntax .nil
  · exact .body (.returnValue [] rfl rfl rfl rfl rfl booleanTyped booleanSyntax)

private theorem booleanTrace (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context [] source environment heap expression (.bool true) heap := by
  have child : Dynamic.ExpressionEvaluatesOutcome program context [] source environment heap (id 2) (.value (.integer 7)) heap :=
    BuiltinCalls.source_intro (checked := checked) (type := .integer) ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl
      (.apply (.cons (.intro (lookupExpression?_sound (node := literalNode) (by rfl))
        (.literal rfl (.word (numericLiteralValue?_sound (value := 7) (by rfl)))) .nil) .nil)
        (.value (.builtin (.wordToInteger (Word.ofNatModulo 7)))))
  cases child with
  | value evaluated =>
    have complete : Dynamic.ExpressionEvaluatesOutcome program context [] source environment heap expression (.value (.bool true)) heap :=
      BuiltinCalls.source_intro (checked := checked) (type := .bool) ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl
        (.apply (.cons evaluated (.cons evaluated .nil)) (.value (.builtin (.integerEq 7 7))))
    cases complete with | value trace => exact trace
private theorem sourceAssigned : Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
    environment before assignment.target expression (.bool true) after := by
  have read : Dynamic.Heap.Reads before ⟨0⟩ {type := .bool, value := none} := .intro .head
  have initial : Dynamic.RootInitialValue {type := .bool, value := none} none :=
    .uninitialized (by rintro ⟨key, value, impossible⟩; cases impossible)
  refine .intro (targetHeap := before) (rhsHeap := before) (rightValue := .bool true)
    (target := ⟨⟨0⟩, .bool, .bool, [], none⟩) ?_ ?_ ?_
  · exact Dynamic.SourcePlaceResolves.intro (place := assignment.target) (environment := environment) .head read .nil read initial .nil
  · exact booleanTrace _
  · exact .intro read rfl initial (.leaf (.equal none (.bool true))) (.intro read .head)

private theorem sourceTrace (mode : Bool) : TypedScopedStatements.Executes mode program context [] source environment before
    statements context (.returned (.bool true)) after := by
  have assignedTrace : Dynamic.StatementExecutes program context [] source environment before (statement 0) context (.fallthrough environment) after :=
    .assignValue (lookupStatement?_sound rfl) rfl sourceAssigned
  have loopTrace : Dynamic.StatementExecutes program context [] source environment before (statement 3) context (.fallthrough environment) after := by
    apply Dynamic.StatementExecutes.forLoop (outcome := .fallthrough environment) (lookupStatement?_sound (node := loopNode) rfl) rfl
      (.cons (.expression (booleanTrace _)) .nil)
    apply Dynamic.ForLoopExecutes.breaks
    · exact booleanTrace _
    · exact .cons assignedTrace (.terminal (.breakStmt (lookupStatement?_sound (node := breakNode) rfl) rfl) (.breaking environment))
  have last : Dynamic.StatementExecutes program context [] source environment after (statement 1) context (.returned (.bool true)) after :=
    .returnValue (lookupStatement?_sound rfl) rfl (booleanTrace _)
  exact TypedScopedStatements.prepend (lookupStatement?_sound (show source.lookupStatement? (statement 3) = some loopNode from rfl))
    (by intro _ _ _ impossible; cases impossible) loopTrace
    (TypedLexicalControl.terminal_outcome program [] (show source.lookupStatement? (statement 1) = some returned from rfl)
      (by intro expression impossible; cases impossible) (.control last) (.returned _))

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
  {scope : SourceCoreLocalCell.Scope}
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  {mode : Bool} {fuel : Nat} {selfReason : Word} {code : Expr} {nativeType : Ty}
  (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy loopPolicy fuel source scope statements .bool reasonAt mode selfReason = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped in
/-- Every builtin child is extracted from the actual expression lowerer. Only
source typing and actual native checker facts remain as static conditions. -/
theorem certified : BuiltinImperativeFor.Tree layouts specialization active frame globals onError 100 values source [] reasonAt
    definitions administrative context scope (.statements mode statements) .bool .bool code := by
  apply GenericImperativeFor.tree_of_typed_flow matched.read binderPolicy allocationPolicy ?_ matched unaryPolicy unique ?_
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
  (valid : CompatibleExpressionLiterals.ContextValid [] context []) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (errors : GenericImperativeFor.Tree.Errors registry faults (certified nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped))
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

include expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations runtimeViews errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_preserves :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      TypedLexicalWhile.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .bool .bool (.returned (.bool true)) value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment context after := by
  subst definitions
  exact (certified nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped).preserves functions layoutDefinitions registered extension program []
    uninitialized missing faithful observations runtimeViews errors valid unique environments heaps locals agrees typed reference read unmapped (sourceTrace mode)

include expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations runtimeViews errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_reflects {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ finalContext outcome sourceHeap finalMap finalWorld,
      TypedScopedStatements.Executes mode program context [] source environment before statements finalContext outcome sourceHeap ∧
      TypedLexicalWhile.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .bool .bool outcome value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld sourceHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before sourceHeap ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext sourceHeap := by
  subst definitions
  exact (certified nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped).reflects functions layoutDefinitions registered extension program []
    uninitialized missing faithful observations runtimeViews errors valid unique environments heaps locals agrees typed reference read unmapped completed
end CompilerBridge

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Word) }",
    "function nested(seed: Word) returns (integer) { let sum = wordFromInteger(wordToInteger(seed)); let m: mapping(Bool => Word); for (let i: Word, i = wordFromInteger(wordToInteger(seed)); integerLt(wordToInteger(i), 3); let copy = wordFromInteger(wordToInteger(i)), i = wordFromInteger(integerAdd(wordToInteger(copy), 1))) { let j = 0; while (integerLt(wordToInteger(j), 2)) { j = wordFromInteger(integerAdd(wordToInteger(j), 1)); if (integerEq(wordToInteger(j), 1)) { continue; } for (let k = 0; integerLt(wordToInteger(k), 2); k = wordFromInteger(integerAdd(wordToInteger(k), 1))) { m[integerEq(wordToInteger(i), wordToInteger(i))] = wordFromInteger(integerAdd(integerAdd(integerMul(wordToInteger(i), 10), wordToInteger(j)), wordToInteger(k))); sum += k; } } } return integerAdd(wordToInteger(m[true]), wordToInteger(sum)); }",
    "function unary(seed: Word) returns (integer) { let x = seed; for (let i = wordFromInteger(wordToInteger(seed)); integerLt(wordToInteger(i), 2); x ~=, i = wordFromInteger(integerAdd(wordToInteger(i), 1))) { x ~=; } return wordToInteger(x); }",
    "function transfers(seed: Word) returns (integer) { let sum = wordFromInteger(wordToInteger(seed)); for (let i = 0; integerLt(wordToInteger(i), 5); let copy = wordFromInteger(wordToInteger(i)), i = wordFromInteger(integerAdd(wordToInteger(copy), 1))) { if (integerEq(wordToInteger(i), 1)) { continue; } { let copy = i; sum += copy; } if (integerEq(wordToInteger(i), 3)) { break; } } return wordToInteger(sum); }",
    "function early(seed: Word) returns (integer) { for (let i = 0; true; let copy = wordFromInteger(wordToInteger(i)), i = wordFromInteger(integerAdd(wordToInteger(copy), 1))) { for (let j = 0; j < 2; j += 1) { if (integerEq(wordToInteger(i), 2)) { return integerAdd(wordToInteger(i), wordToInteger(j)); } } } return 99; }",
    "function falseFirst(seed: Word) returns (integer) { let i = 17; for (let i = 3; false; let never = 99) { return 0; } return wordToInteger(i); }",
    "function bodyFault(seed: Word) returns (integer) { let m: mapping(Bool => Word); let keys: mapping(Bool => Bool); let lazy: mapping(Bool => Word); let missing: Word; for (let i = 0; i < 2; let never = 99) { i += 1; m[keys[true]] = wordFromInteger(integerAdd(wordToInteger(lazy[false]), wordToInteger(missing))); } return 0; }",
    "function postFault(seed: Word) returns (integer) { let missing: Word; let seen: mapping(Bool => Word); for (let i = 0; true; let copy = i, i = wordFromInteger(integerAdd(wordToInteger(seen[false]), wordToInteger(missing))), let never = 99) { continue; } return 1; }",
    "function initializerFault(seed: Word) returns (integer) { let missing: Word; let seen: mapping(Bool => Word); for (let ready = wordFromInteger(integerAdd(wordToInteger(seed), 1)), let dead = wordFromInteger(integerAdd(wordToInteger(seen[false]), wordToInteger(missing))); true; ) { return 0; } return 1; }",
    "function conditionFault(seed: Word) returns (integer) { let missing: Bool; let seen: mapping(Bool => Bool); for (let ready = wordFromInteger(integerAdd(wordToInteger(seed), 1)); seen[false] || missing; let never = 99) { return 0; } return 1; }"
  ]}] }
private def escape : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function main() returns (integer) { for (let i = 0; false; let copy = i) { } return copy; }"}] }
private def arguments : List SourceCompilerFeatureSupport.Value := [.word Word.zero]
private def inputCells : List (TypeSystem.Ty × Option SourceCompilerFeatureSupport.Value) := [(.word, some (.word Word.zero))]
private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke arguments
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "for fixture unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "for failure lost its diagnostic"
  for fuel in [0, 10, 35, 100] do
    let started ← SourceCompilerFeatureSupport.get "for suspension"
      (← complete.initial.run complete.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed, complete.outcome with
    | .failed actual heap, .failed expected initial =>
        SourceCompilerFeatureSupport.require (actual == expected && heap.heapSize == initial.heapSize)
          "for resume changed failure or executed unreachable allocation"
    | _, _ => throw (IO.userError "for resume changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "imperative for checker" (checkProgram workspace)
  for (name, result) in [("nested", 26), ("unary", 0), ("transfers", 5), ("early", 2), ("falseFirst", 17)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let expected : SourceCompilerFeatureSupport.Value := .integer result
    SourceCompilerFeatureSupport.require ((← entry.run arguments) == expected) s!"{name}: mixed for/while result changed"
    entry.checkResume arguments expected
  let transfers ← SourceCompilerFeatureSupport.compileNamed checked "transfers"
  transfers.checkCells arguments (inputCells ++ [(.word, some (SourceCompilerFeatureSupport.scalar 5)), (.word, some (SourceCompilerFeatureSupport.scalar 3)),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 0)),
    (.word, some (SourceCompilerFeatureSupport.scalar 1)), (.word, some (SourceCompilerFeatureSupport.scalar 2)),
    (.word, some (SourceCompilerFeatureSupport.scalar 2)), (.word, some (SourceCompilerFeatureSupport.scalar 3))])
  let falseFirst ← SourceCompilerFeatureSupport.compileNamed checked "falseFirst"
  falseFirst.checkCells arguments (inputCells ++ [(.word, some (SourceCompilerFeatureSupport.scalar 17)), (.word, some (SourceCompilerFeatureSupport.scalar 3))])
  let body ← SourceCompilerFeatureSupport.compileNamed checked "bodyFault"
  failureResume body
  body.checkCells arguments (inputCells ++ [(.mapping .bool .word, none), (.mapping .bool .bool, some (.mapping .bool .bool [])),
    (.mapping .bool .word, some (.mapping .bool .word [])), (.word, none), (.word, some (SourceCompilerFeatureSupport.scalar 1))])
  let post ← SourceCompilerFeatureSupport.compileNamed checked "postFault"
  failureResume post
  post.checkCells arguments (inputCells ++ [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 0))])
  let initializer ← SourceCompilerFeatureSupport.compileNamed checked "initializerFault"
  failureResume initializer
  initializer.checkCells arguments (inputCells ++ [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 1))])
  let condition ← SourceCompilerFeatureSupport.compileNamed checked "conditionFault"
  failureResume condition
  condition.checkCells arguments (inputCells ++ [(.bool, none), (.mapping .bool .bool, some (.mapping .bool .bool [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 1))])
  SourceCompilerFeatureSupport.require (match checkProgram escape with | .error _ => true | .ok _ => false) "for post local escaped its scope"
  IO.println "builtin imperative for: actual compiler certificates, mixed/nested loops, scoped headers/post, transfer/fault effects and resume GREEN"
end Tests.SourceCoreBuiltinImperativeFor
