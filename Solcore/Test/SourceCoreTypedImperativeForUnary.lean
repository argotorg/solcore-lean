import Solcore.SourceSemantics.CoreLowering.TypedImperativeForUnaryCertificates
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForMeaning
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Bare unary assignments preserve source order at every recursive loop
position. Actual code receipts and an independent two-write source trace close
the theorem consumers; runtime fixtures also cover missing operands and resume. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreTypedImperativeForUnary
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedImperativeFor GeneralHeap CompatiblePayload CompatibleEquality ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"unary_for", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "unary_for.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (n : Nat) : StatementId := ⟨⟨owner, n + 1⟩⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "x", .mono .word, [], false, none⟩
private def assignment : AssignmentResolution := ⟨⟨binder.id, [], .word⟩, []⟩
private def literal : ExpressionNode := { id := expression, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def assigned : StatementNode := ⟨statement 0, span, .unit, .assignBitNot assignment⟩
private def returned : StatementNode := ⟨statement 1, span, .bool, .returnStmt (some expression)⟩
private def breakNode : StatementNode := ⟨statement 2, span, .unit, .breakStmt⟩
private def loopNode : StatementNode := ⟨statement 3, span, .unit, .forLoop [.assignBitNot assignment] expression [.assignBitNot assignment] [statement 0, statement 2]⟩
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
private def before : Dynamic.Heap := ⟨[{type := .word, value := some (.word Word.zero)}]⟩
private def middle : Dynamic.Heap := ⟨[{type := .word, value := some (.word Word.zero.bitNot)}]⟩
private def after : Dynamic.Heap := ⟨[{type := .word, value := some (.word Word.zero.bitNot.bitNot)}]⟩
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem booleanTyped : ExpressionHasType source context expression .bool := by
  have admissible : TypeAdmissible context .bool := .bool (by
    simp [TypeParameterBindersWellFormed, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
  apply ExpressionHasType.ofOrdinary (node := literal) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.builtinBoolean true)) admissible admissible
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem writable : WritableLocal context binder.id .word := by
  apply WritableLocal.withLocal_mono_admissible
  exact .word (by simp [TypeParameterBindersWellFormed, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal])
private theorem rootWritable : ∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
    WritableLocal context assignment.target.root actual.scheme.body := by
  intro actual found
  have : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := rfl
  cases Except.ok.inj (this.symm.trans found)
  exact writable
private theorem booleanSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literal) rfl (.bool _ _)))))))
private theorem syntaxTree (mode : Bool) : TypedImperativeFor.UnarySyntax source context (.statements mode statements) .bool := by
  apply TypedImperativeFor.UnarySyntax.forLoop (node := loopNode) rfl rfl rfl
  · apply TypedImperativeFor.UnarySyntax.initializerBitNot rootWritable rfl (.inl rfl)
    apply TypedImperativeFor.UnarySyntax.initializersDone (conditionNode := literal) rfl rfl booleanTyped booleanSyntax
    · exact .bitNot (node := assigned) rfl rfl rootWritable rfl (.inl rfl) (.breaking (node := breakNode) rfl rfl)
    · exact .bitNot rootWritable rfl (.inl rfl) .nil
  · exact .body (.body (.returnValue [] rfl rfl rfl rfl rfl booleanTyped booleanSyntax))

private theorem sourceFlipped (value : Word) : Dynamic.SourcePlaceSnapshotUpdate program context [] source Dynamic.BitNotSnapshot
    environment ⟨[{type := .word, value := some (.word value)}]⟩ assignment.target (.word value.bitNot)
      ⟨[{type := .word, value := some (.word value.bitNot)}]⟩ := by
  have read : Dynamic.Heap.Reads ⟨[{type := .word, value := some (.word value)}]⟩ ⟨0⟩
      {type := .word, value := some (.word value)} := .intro .head
  refine .intro (selectedHeap := ⟨[{type := .word, value := some (.word value)}]⟩) (target := ⟨⟨0⟩, .word, .word, [], some (.word value)⟩) ?_ ?_
  · exact Dynamic.SourcePlaceResolves.intro (place := assignment.target) (environment := environment) .head read .nil read .initialized .nil
  · exact .intro read rfl .initialized (.leaf (.word value)) (.intro read .head)

private theorem sourceTrace (mode : Bool) : TypedScopedStatements.Executes mode program context [] source environment before
    statements context (.returned (.bool true)) after := by
  have assignedTrace : Dynamic.StatementExecutes program context [] source environment middle (statement 0) context (.fallthrough environment) after :=
    .assignBitNot (lookupStatement?_sound rfl) rfl (sourceFlipped Word.zero.bitNot)
  have loopTrace : Dynamic.StatementExecutes program context [] source environment before (statement 3) context (.fallthrough environment) after := by
    apply Dynamic.StatementExecutes.forLoop (outcome := .fallthrough environment) (lookupStatement?_sound (node := loopNode) rfl) rfl
      (.cons (.assignBitNot (sourceFlipped Word.zero)) .nil)
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
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingReason : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (matched : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingReason)
  (unary : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingReason)
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

include matched unary binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped in
/-- A single whole-code checker receipt supplies both loop typing and the
assignment continuation. The remaining premises are static source certificates. -/
theorem certified : Tree layouts specialization active frame globals onError readFuel values source solved reasonAt definitions administrative
    context scope (.statements mode statements) .bool .bool code := by
  apply tree_of_typed_flow_withBitNot matched.read binderPolicy allocationPolicy ?_ matched unary unique expressions
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
  (errors : Tree.Errors registry faults (certified matched unary binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped))
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

include matched unary binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
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
  exact (certified matched unary binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).preserves functions layoutDefinitions registered extension program []
    uninitialized missing faithful observations errors valid unique environments heaps locals agrees typed reference read unmapped (sourceTrace mode)

include matched unary binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
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
  exact (certified matched unary binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).reflects functions layoutDefinitions registered extension program []
    uninitialized missing faithful observations runtimeViews errors valid unique environments heaps locals agrees typed reference read unmapped completed
end CompilerBridge

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function nested() returns (Word) { let x = 7; for (x ~=, let i = 0; i < 2; x ~=, i += 1) { { x ~=; } let j = 0; while (j < 2) { x ~=; j += 1; } } return x; }",
    "function transfer() returns (Word) { let x = 5; for (x ~=, let i = 0; true; x ~=, i += 1) { if (i == 0) { continue; } { x ~=; break; } } return x; }",
    "function early() returns (Word) { let x = 9; for (x ~=; true; x ~=) { x ~=; return x; } return 0; }",
    "function falseFirst() returns (Word) { let x = 2; for (x ~=; false; x ~=) { x ~=; } return x; }",
    "function postFault() returns (Word) { let missing: Word; let seen = 0; for (let i = 0; true; let copy = i, seen = 8, missing ~=, let never = 99) { seen = 3; continue; } return 1; }",
    "function initializerFault() returns (Word) { let missing: Word; let seen = 0; for (seen = 6, missing ~=, let never = 99; true; ) { seen = 3; } return 1; }",
    "function bodyFault() returns (Word) { let missing: Word; let seen = 0; for (seen = 6; true; seen = 7) { { missing ~=; } seen = 8; } return 1; }"
  ]}] }
private def rejected : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function rejected(value: integer) returns (integer) { for (value ~=; false; ) { } return value; }"}] }
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
  let checked ← SourceCompilerFeatureSupport.get "unary for checker" (checkProgram workspace)
  for (name, value) in [("nested", (Word.ofNatModulo 7).bitNot), ("transfer", (Word.ofNatModulo 5).bitNot),
      ("early", Word.ofNatModulo 9), ("falseFirst", (Word.ofNatModulo 2).bitNot)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let expected : SourceCorePublicValues.Value := .word value
    SourceCompilerFeatureSupport.require ((← entry.run []) == expected) s!"{name}: unary loop ordering changed"
    entry.checkResume [] expected
  for (name, seen) in [("initializerFault", 6), ("bodyFault", 6)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    failureResume entry
    entry.checkCells [] [(.word, none), (.word, some (SourceCompilerFeatureSupport.scalar seen))]
  let post ← SourceCompilerFeatureSupport.compileNamed checked "postFault"
  failureResume post
  post.checkCells [] [(.word, none), (.word, some (SourceCompilerFeatureSupport.scalar 8)),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 0))]
  SourceCompilerFeatureSupport.require (match checkProgram rejected with | .error _ => true | .ok _ => false)
    "Integer unary compound source admission changed"
  IO.println "typed imperative unary: actual certificates/source trace, every for position, nested effects/faults/resume GREEN"
end Tests.SourceCoreTypedImperativeForUnary
