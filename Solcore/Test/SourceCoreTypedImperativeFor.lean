import Solcore.SourceSemantics.CoreLowering.TypedImperativeForCertificates
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForMeaning
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Mixed for/while consumes actual lowering and whole-code typing,
with an independent source trace. Runtime fixtures exercise repeated/nested
iterations, scoped allocations, transfers, fault ordering and resumption. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreTypedImperativeFor
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedImperativeFor GeneralHeap CompatiblePayload CompatibleEquality ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"assignment_statement", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "assignment_statement.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (n : Nat) : StatementId := ⟨⟨owner, n + 1⟩⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "x", .mono .bool, [], false, none⟩
private def assignment : AssignmentResolution := ⟨⟨binder.id, [], .bool⟩, []⟩
private def literal : ExpressionNode := { id := expression, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def assigned : StatementNode := ⟨statement 0, span, .unit, .assignValue assignment .equal expression⟩
private def returned : StatementNode := ⟨statement 1, span, .bool, .returnStmt (some expression)⟩
private def breakNode : StatementNode := ⟨statement 2, span, .unit, .breakStmt⟩
private def loopNode : StatementNode := ⟨statement 3, span, .unit, .forLoop [.expression expression] expression [.assignValue assignment .equal expression] [statement 0, statement 2]⟩
private def statements := [statement 3, statement 1]
private def source : TypedSource := {
  owner := owner
  inputs := [binder]
  roots := statements.map .statement
  nodes := [.expression literal, .statement assigned, .statement returned, .statement breakNode, .statement loopNode]
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[{type := .bool, value := none}]⟩
private def after : Dynamic.Heap := ⟨[{type := .bool, value := some (.bool true)}]⟩
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem booleanTyped : ExpressionHasType source context expression .bool := by
  have admissible : TypeAdmissible context .bool := .bool (by
    simp [TypeParameterBindersWellFormed, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
  apply ExpressionHasType.ofOrdinary (node := literal) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.builtinBoolean true)) admissible admissible
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem writable : WritableLocal context binder.id .bool := by
  apply WritableLocal.withLocal_mono_admissible
  exact .bool (by simp [TypeParameterBindersWellFormed, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
private theorem booleanSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literal) rfl (.bool _ _)))))))
private theorem assignmentSyntax {rest : List ForItemForm} (remaining : TypedForHeader.Syntax source context rest) :
    TypedForHeader.Syntax source context (.assignValue assignment .equal expression :: rest) := by
  apply TypedForHeader.Syntax.assign
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
  · exact remaining
private theorem syntaxTree (mode : Bool) : TypedImperativeFor.Syntax source context (.statements mode statements) .bool := by
  apply TypedImperativeFor.Syntax.forLoop (node := loopNode) rfl rfl rfl
  · apply TypedImperativeFor.Syntax.initializerDiscard (expressionNode := literal) rfl booleanTyped booleanSyntax
    apply TypedImperativeFor.Syntax.initializersDone (conditionNode := literal) rfl rfl booleanTyped booleanSyntax
    · apply TypedImperativeFor.Syntax.assign (node := assigned) rfl rfl
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
      · exact .breaking (node := breakNode) rfl rfl
    · exact assignmentSyntax .nil
  · exact .body (.body (.returnValue [] rfl rfl rfl rfl rfl booleanTyped booleanSyntax))

private theorem sourceAssigned : Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
    environment before assignment.target expression (.bool true) after := by
  have read : Dynamic.Heap.Reads before ⟨0⟩ {type := .bool, value := none} := .intro .head
  have initial : Dynamic.RootInitialValue {type := .bool, value := none} none :=
    .uninitialized (by rintro ⟨key, value, impossible⟩; cases impossible)
  refine .intro (targetHeap := before) (rhsHeap := before) (rightValue := .bool true)
    (target := ⟨⟨0⟩, .bool, .bool, [], none⟩) ?_ ?_ ?_
  · exact Dynamic.SourcePlaceResolves.intro (place := assignment.target) (environment := environment) .head read .nil read initial .nil
  · exact .intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
  · exact .intro read rfl initial (.leaf (.equal none (.bool true))) (.intro read .head)

private theorem sourceTrace (mode : Bool) : TypedScopedStatements.Executes mode program context [] source environment before
    statements context (.returned (.bool true)) after := by
  have assignedTrace : Dynamic.StatementExecutes program context [] source environment before (statement 0) context (.fallthrough environment) after :=
    .assignValue (lookupStatement?_sound rfl) rfl sourceAssigned
  have loopTrace : Dynamic.StatementExecutes program context [] source environment before (statement 3) context (.fallthrough environment) after := by
    apply Dynamic.StatementExecutes.forLoop (outcome := .fallthrough environment) (lookupStatement?_sound (node := loopNode) rfl) rfl
      (.cons (.expression (.intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil)) .nil)
    apply Dynamic.ForLoopExecutes.breaks
    · exact .intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
    · exact .cons assignedTrace (.terminal (.breakStmt (lookupStatement?_sound (node := breakNode) rfl) rfl) (.breaking environment))
  have last : Dynamic.StatementExecutes program context [] source environment after (statement 1) context (.returned (.bool true)) after :=
    .returnValue (lookupStatement?_sound rfl) rfl (.intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil)
  exact TypedScopedStatements.prepend (lookupStatement?_sound (show source.lookupStatement? (statement 3) = some loopNode from rfl))
    (by intro _ _ _ impossible; cases impossible) loopTrace
    (TypedLexicalControl.terminal_outcome program [] (show source.lookupStatement? (statement 1) = some returned from rfl)
      (by intro expression impossible; cases impossible) (.control last) (.returned _))

section CompilerBridge
variable {layouts : SourceCoreAllocationLayouts.Prepared} {specialization : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {definitions : DataEnvironment}
  {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {missingReason : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (matched : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingReason)
  (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
  (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  (sourceSignatures : context.signatures = values.checked.signatures)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (expressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
    sourceContext.signatures = values.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
  {mode : Bool} {fuel : Nat} {selfReason : Word} {code : Expr} {nativeType : Ty}
  (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements .bool reasonAt mode selfReason = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped in
/-- A single whole-code checker receipt supplies both loop typing and the
assignment continuation. The remaining premises are static source certificates. -/
theorem certified : Tree layouts specialization active frame globals onError readFuel values source solved reasonAt definitions administrative
    context scope (.statements mode statements) .bool .bool code := by
  apply tree_of_typed_flow matched.read binderPolicy allocationPolicy ?_ matched unique expressions
    (syntaxTree mode) rfl rfl sourceSignatures declarations (by rfl) accepted (infer_sound nativeTyped)
  intro sourceContext closed residual signatures scope fuel id node lowered declarations syntaxValue found typed generated
  obtain ⟨_, _, tree, _⟩ := expressions sourceContext scope fuel id lowered closed residual signatures declarations generated
  exact tree

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (sameDefinitions : definitions = ambient.definitions)
  (layoutDefinitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (valid : CompatibleExpressionLiterals.ContextValid solved context []) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  (errors : Tree.Errors registry faults (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped))
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

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
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
  exact (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).preserves functions layoutDefinitions registered extension program []
    uninitialized missing faithful observations errors valid unique environments heaps locals agrees typed reference read unmapped (sourceTrace mode)

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_reflects (runtimeViews : FunctionRuntimeViews functions) {value : Value} {finalStore : Store}
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
  exact (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).reflects functions layoutDefinitions registered extension program []
    uninitialized missing faithful observations runtimeViews errors valid unique environments heaps locals agrees typed reference read unmapped completed
end CompilerBridge

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Word) }",
    "function nested() returns (Word) { let sum = 0; let m: mapping(Bool => Word); for (let i: Word, i = 0; i < 3; let copy = i, i = copy + 1) { let j = 0; while (j < 2) { j += 1; if (j == 1) { continue; } for (let k = 0; k < 2; k += 1) { m[true] = i * 10 + j + k; sum += k; } } } return m[true] + sum; }",
    "function transfers() returns (Word) { let sum = 0; for (let i = 0; i < 5; let copy = i, i = copy + 1) { if (i == 1) { continue; } { let copy = i; sum += copy; } if (i == 3) { break; } } return sum; }",
    "function early() returns (Word) { for (let i = 0; true; let copy = i, i = copy + 1) { for (let j = 0; j < 2; j += 1) { if (i == 2) { return i + j; } } } return 99; }",
    "function falseFirst() returns (Word) { let i = 17; for (let i = 3; false; let never = 99) { return 0; } return i; }",
    "function bodyFault() returns (Word) { let m: mapping(Bool => Word); let keys: mapping(Bool => Bool); let lazy: mapping(Bool => Word); let missing: Word; for (let i = 0; i < 2; let never = 99) { i += 1; m[keys[true]] = lazy[false] + missing; } return 0; }",
    "function postFault() returns (Word) { let missing: Word; let seen: mapping(Bool => Word); for (let i = 0; true; let copy = i, i = seen[false] + missing, let never = 99) { continue; } return 1; }",
    "function initializerFault() returns (Word) { let missing: Word; let seen: mapping(Bool => Word); for (let ready = 1, let dead = seen[false] + missing; true; ) { return 0; } return 1; }",
    "function conditionFault() returns (Word) { let missing: Bool; let seen: mapping(Bool => Bool); for (let ready = 1; seen[false] || missing; let never = 99) { return 0; } return 1; }"
  ]}] }
private def escape : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function main() returns (Word) { for (let i = 0; false; let copy = i) { } return copy; }"}] }
private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke []
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "for fixture unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "for failure lost its diagnostic"
  for fuel in [0, 10, 35, 100] do
    let started ← SourceCompilerFeatureSupport.get "for suspension"
      (← complete.initial.run complete.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
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
  for (name, result) in [("nested", 26), ("transfers", 5), ("early", 2), ("falseFirst", 17)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let expected := SourceCompilerFeatureSupport.scalar result
    SourceCompilerFeatureSupport.require ((← entry.run []) == expected) s!"{name}: mixed for/while result changed"
    entry.checkResume [] expected
  let transfers ← SourceCompilerFeatureSupport.compileNamed checked "transfers"
  transfers.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 5)), (.word, some (SourceCompilerFeatureSupport.scalar 3)),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 0)),
    (.word, some (SourceCompilerFeatureSupport.scalar 1)), (.word, some (SourceCompilerFeatureSupport.scalar 2)),
    (.word, some (SourceCompilerFeatureSupport.scalar 2)), (.word, some (SourceCompilerFeatureSupport.scalar 3))]
  let falseFirst ← SourceCompilerFeatureSupport.compileNamed checked "falseFirst"
  falseFirst.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 17)), (.word, some (SourceCompilerFeatureSupport.scalar 3))]
  let body ← SourceCompilerFeatureSupport.compileNamed checked "bodyFault"
  failureResume body
  body.checkCells [] [(.mapping .bool .word, none), (.mapping .bool .bool, some (.mapping .bool .bool [])),
    (.mapping .bool .word, some (.mapping .bool .word [])), (.word, none), (.word, some (SourceCompilerFeatureSupport.scalar 1))]
  let post ← SourceCompilerFeatureSupport.compileNamed checked "postFault"
  failureResume post
  post.checkCells [] [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 0))]
  let initializer ← SourceCompilerFeatureSupport.compileNamed checked "initializerFault"
  failureResume initializer
  initializer.checkCells [] [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 1))]
  let condition ← SourceCompilerFeatureSupport.compileNamed checked "conditionFault"
  failureResume condition
  condition.checkCells [] [(.bool, none), (.mapping .bool .bool, some (.mapping .bool .bool [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 1))]
  SourceCompilerFeatureSupport.require (match checkProgram escape with | .error _ => true | .ok _ => false) "for post local escaped its scope"
  IO.println "typed imperative for: actual compiler certificates, mixed/nested loops, scoped headers/post, transfer/fault effects and resume GREEN"
end Tests.SourceCoreTypedImperativeFor
