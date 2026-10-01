import Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementMeaning
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Assignment spines consume actual compatible flow receipts and retain all
source effects before failure. Runtime fixtures combine projected and bare
writes with lexical tails, early return, captured cells and suspension. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCompatibleAssignmentStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleAssignmentStatements GeneralHeap CompatiblePayload CompatibleEquality ReadOnly
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
private def source : TypedSource := {
  owner := owner
  inputs := [binder]
  roots := [.statement (statement 0), .statement (statement 1)]
  nodes := [.expression literal, .statement assigned, .statement returned]
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
private theorem syntaxTree (mode : Bool) : CompatibleAssignmentStatements.Syntax source context mode [statement 0, statement 1] .bool := by
  apply CompatibleAssignmentStatements.Syntax.assign (node := assigned) rfl rfl
  · intro actual found
    have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
    have same := Except.ok.inj (this.symm.trans found)
    cases same
    exact .nil _
  · intro actual found
    have : SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder := rfl
    have same := Except.ok.inj (this.symm.trans found)
    cases same
    exact writable
  · exact booleanTyped
  · exact .inl rfl
  · exact .tail (.body (.returnValue [] rfl rfl rfl rfl rfl booleanTyped (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal rfl (.bool "true" true))))))))))

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
    [statement 0, statement 1] context (.returned (.bool true)) after := by
  have first : Dynamic.StatementExecutes program context [] source environment before (statement 0) context (.fallthrough environment) after :=
    .assignValue (lookupStatement?_sound rfl) rfl sourceAssigned
  have last : Dynamic.StatementExecutes program context [] source environment after (statement 1) context (.returned (.bool true)) after :=
    .returnValue (lookupStatement?_sound rfl) rfl (.intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil)
  exact TypedScopedStatements.prepend (lookupStatement?_sound (show source.lookupStatement? (statement 0) = some assigned from rfl))
    (by intro _ _ _ impossible; cases impossible) first
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
  (matched : AssignmentPolicy policy values invalidProjection invalidOperand missingReason)
  (sourceSignatures : context.signatures = values.checked.signatures)
  (expressions : ∀ fuel id lowered, policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
    source.lookupExpression? id = some node ∧ CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope id lowered ∧
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
  (sites : ∀ {fuel statements type mode selfReason code},
    SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code →
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code (LocalLoop.resultType type) definitions)
  (tails : ∀ {mode statements expected fuel type selfReason code},
    TypedLexicalControl.Syntax source context mode statements expected →
    SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code →
    TypedLexicalControl.Tree layouts specialization active frame globals onError readFuel values source solved reasonAt context scope mode statements expected type code)
  {mode : Bool} {fuel : Nat} {selfReason : Word} {code : Expr}
  (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope [statement 0, statement 1] .bool reasonAt mode selfReason = .ok code)

include matched sourceSignatures expressions sites tails accepted in
theorem certified : Tree layouts specialization active frame globals onError readFuel values source solved reasonAt
    context scope administrative definitions mode [statement 0, statement 1] .bool .bool code :=
  tree_of_flow matched unique sourceSignatures expressions sites tails (syntaxTree mode) accepted

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
  (errors : Tree.Errors registry faults (certified matched sourceSignatures expressions sites tails accepted))
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

include matched sourceSignatures expressions sites tails sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_preserves :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      TypedScopedStatements.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .bool .bool (.returned (.bool true)) value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment context after := by
  subst definitions
  exact (certified matched sourceSignatures expressions sites tails accepted).preserves functions layoutDefinitions registered extension program [] valid
    uninitialized missing faithful observations errors unique environments heaps locals agrees typed reference read unmapped (sourceTrace mode)

include matched sourceSignatures expressions sites tails sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_reflects (runtimeViews : FunctionRuntimeViews functions) {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ finalContext outcome sourceHeap finalMap finalWorld,
      TypedScopedStatements.Executes mode program context [] source environment before [statement 0, statement 1] finalContext outcome sourceHeap ∧
      TypedScopedStatements.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .bool .bool outcome value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld sourceHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before sourceHeap ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext sourceHeap := by
  subst definitions
  exact (certified matched sourceSignatures expressions sites tails accepted).reflects functions layoutDefinitions registered extension program [] valid
    uninitialized missing faithful observations runtimeViews errors unique environments heaps locals agrees typed reference read unmapped completed
end CompilerBridge

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Word) }",
    "function bare() returns (Word) { let x: Word; x = 3; x += 4; x *= 2; x -= 1; return x; }",
    "function mapping() returns (Word) { let m: mapping(Bool => Word); m[true] = 3; m[true] += 4; m[false] = m[true] * 2; { let answer = m[false]; return answer; } return 0; }",
    "function nested() returns (Word) { let m: mapping(Bool => mapping(Bool => Word)); let keys: mapping(Bool => Bool); m[keys[true]][keys[false]] = 5; m[false][false] += 2; return m[false][false]; }",
    "function captured() returns (Word) { let x = 1; let read = lam() { return x; }; x += 8; return read(); }",
    "function missing() returns (Word) { let x: Word; let rhs: mapping(Bool => Word); x += rhs[true] + 2; let never = true; return 0; }",
    "function rhsFault() returns (Word) { let m: mapping(Bool => Word); let keys: mapping(Bool => Bool); let rhs: mapping(Bool => Word); let missing: Word; m[keys[true]] = rhs[false] + missing; let never = true; return 0; }",
    "function targetFault() returns (Word) { let m: mapping(Bool => Box); let keys: mapping(Bool => Bool); let rhs: mapping(Bool => Word); m[keys[true]] = .Box(rhs[false]); let never = true; return 0; }",
    "function early() returns (Word) { let x: Word; x = 11; if (true) { return x; } x = 99; return x; }"
  ]}] }

private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke []
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "assignment fixture unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "assignment failure lost its diagnostic"
  for fuel in [0, 10, 35, 100] do
    let started ← SourceCompilerFeatureSupport.get "assignment suspension"
      (← complete.initial.run complete.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed, complete.outcome with
    | .failed actual heap, .failed expected initial =>
        SourceCompilerFeatureSupport.require (actual == expected && heap.heapSize == initial.heapSize)
          "assignment resume changed fault or executed unreachable allocation"
    | _, _ => throw (IO.userError "assignment resume changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "assignment statement checker" (checkProgram workspace)
  for (name, result) in [("bare", 13), ("mapping", 14), ("nested", 7), ("captured", 9), ("early", 11)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let expected : SourceCompilerFeatureSupport.Value := .word (Word.ofNatModulo result)
    SourceCompilerFeatureSupport.require ((← entry.run []) == expected) s!"{name}: assignment statement value changed"
    entry.checkResume [] expected
  let bare ← SourceCompilerFeatureSupport.compileNamed checked "bare"
  bare.checkCells [] [(.word, some (.word (Word.ofNatModulo 13)))]
  let missing ← SourceCompilerFeatureSupport.compileNamed checked "missing"
  failureResume missing
  missing.checkCells [] [(.word, none), (.mapping .bool .word, some (.mapping .bool .word []))]
  let rhs ← SourceCompilerFeatureSupport.compileNamed checked "rhsFault"
  failureResume rhs
  rhs.checkCells [] [(.mapping .bool .word, none), (.mapping .bool .bool, some (.mapping .bool .bool [])),
    (.mapping .bool .word, some (.mapping .bool .word [])), (.word, none)]
  let target ← SourceCompilerFeatureSupport.compileNamed checked "targetFault"
  failureResume target
  let cells := (SourceCompilerFeatureSupport.sourceState (← target.audit [])).heap
  SourceCompilerFeatureSupport.require ((match cells with | [first, _, third] => first.value.isNone && third.value.isNone | _ => false))
    "target fault executed RHS or continuation"
  IO.println "assignment statements: bare/projected spines, compound updates, lazy key/RHS fault order, lexical tails, capture and resume GREEN"
end Tests.SourceCoreCompatibleAssignmentStatements
