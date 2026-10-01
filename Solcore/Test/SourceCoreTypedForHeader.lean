import Solcore.SourceSemantics.CoreLowering.TypedForHeaderPost
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual for-item lowering, whole native typing and an independent source
header trace feed the concrete post theorems. Runtime fixtures preserve mixed
header allocations, post scopes, transfers, fault effects and resumption. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreTypedForHeader
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedForHeader GeneralHeap CompatiblePayload CompatibleEquality ReadOnly
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
private def loopNode : StatementNode := ⟨statement 3, span, .unit, .whileLoop expression [statement 0, statement 2]⟩
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
private def items : List ForItemForm := [.expression expression, .assignValue assignment .equal expression]
private theorem syntaxTree : TypedForHeader.Syntax source context items := by
  apply TypedForHeader.Syntax.discard (expressionNode := literal) rfl booleanTyped booleanSyntax
  apply TypedForHeader.Syntax.assign
  · intro actual found
    have expected : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := rfl
    have same := Except.ok.inj (expected.symm.trans found)
    cases same
    exact .nil _
  · intro actual found
    have expected : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := rfl
    have same := Except.ok.inj (expected.symm.trans found)
    cases same
    exact writable
  · exact booleanTyped
  · exact .inl rfl
  · exact .nil

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

private theorem sourceTrace : Dynamic.ForItemsExecute program context [] source environment before items context environment after :=
  .cons (.expression (.intro (node := literal) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil))
    (.cons (.assignValue sourceAssigned) .nil)

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
  {fuel : Nat} {site : SourceCoreElaboration.ErrorSite} {code : Expr} {nativeType : Ty}
  (accepted : SourceCoreLoops.lowerForItems policy site fuel source scope items .bool reasonAt
    (fun _ => .ok (LocalLoop.fallthrough .bool)) = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped in
/-- Static child extraction and one actual checker receipt determine every
allocation/assignment header node; no child evaluation is a premise. -/
theorem certified : Tree layouts specialization active frame globals onError readFuel values source solved reasonAt definitions administrative
    .bool (Fallthrough .bool) context scope items code := by
  exact tree_of_lowerForItems binderPolicy allocationPolicy matched unique expressions
    (fun _ _ _ _ _ _ _ accepted => Except.ok.inj accepted.symm) syntaxTree rfl rfl sourceSignatures declarations
      accepted (infer_sound nativeTyped)

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
theorem compiled_post_restores :
    ∃ tail : Tail registry functions source solved [] administrative frame globals location native (Fallthrough .bool) context environment after,
      Evaluates actual store (code.rename ξ) (LocalLoop.fallthroughValue .bool) tail.store ∧
      CompatibleHeap.HeapRepresents values.checked registry functions tail.mapping tail.world after tail.store ∧
      DataHeap.EnvRepresents (storageCatalog values.checked.catalog) tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions := by
  subst definitions
  obtain ⟨tail, maps, worlds, preservation, metadata, evaluated, outer, restored, actualTyped⟩ :=
    (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).preserves_post
      functions layoutDefinitions registered extension program [] uninitialized missing faithful observations
      valid unique environments heaps locals agrees typed reference read unmapped sourceTrace
  exact ⟨tail, evaluated, tail.heaps, outer, restored, actualTyped⟩

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_post_reflects (runtimeViews : FunctionRuntimeViews functions) {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    Result registry functions program source solved [] administrative frame globals location native .bool faults (Fallthrough .bool)
      context environment before items mapping world store value finalStore := by
  subst definitions
  exact (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).reflects
    functions layoutDefinitions registered extension program [] uninitialized missing faithful observations runtimeViews
    errors valid unique environments heaps locals agrees typed reference read unmapped completed

include matched binderPolicy allocationPolicy sourceSignatures declarations expressions nativeTyped sameDefinitions layoutDefinitions registered extension valid uninitialized missing faithful observations errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_post_shape (runtimeViews : FunctionRuntimeViews functions) {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    value = LocalLoop.fallthroughValue .bool ∨ ∃ token, value = .inLeft (LocalLoop.controlType .bool) (.word token) := by
  subst definitions
  rcases (certified matched binderPolicy allocationPolicy sourceSignatures declarations expressions accepted nativeTyped).reflects_post
      functions layoutDefinitions registered extension program [] uninitialized missing faithful observations runtimeViews
      errors valid unique environments heaps locals agrees typed reference read unmapped completed with done | fault
  · obtain ⟨_, _, _, _, _, same, _⟩ := done
    exact .inl same
  · obtain ⟨_, _, token, _, _, _, _, same, _⟩ := fault
    exact .inr ⟨token, same⟩
end CompilerBridge

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function mixed() returns (Word) { let sum = 0; for (let i: Word, i = 0, let flag: Bool = true; i < 3; let copy = i, i = copy + 1) { if (flag) { sum += i; } } return sum; }",
    "function shadow() returns (Word) { let i = 17; for (let i = 0; i < 2; let copy = i, i = copy + 1) { continue; } return i; }",
    "function falseFirst() returns (Word) { for (let i = 5; false; let never = 99) { return 0; } return 5; }",
    "function breaks() returns (Word) { for (let i = 0; true; let never = 99) { break; } return 1; }",
    "function returns() returns (Word) { for (let i = 0; true; let never = 99) { return i; } return 1; }",
    "function initializerFault() returns (Word) { let missing: Word; let seen: mapping(Bool => Word); for (let ready = 1, let dead = seen[false] + missing; true; ) { return 0; } return 1; }",
    "function postFault() returns (Word) { let missing: Word; let seen: mapping(Bool => Word); for (let i = 0; true; let copy = i, i = seen[false] + missing, let never = 99) { continue; } return 1; }",
    "function postAbsent() returns (Word) { for (let i = 0; true; let absent: Word, i = absent) { continue; } return 1; }"
  ]}] }
private def escape : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function main() returns (Word) { for (let i = 0; false; let copy = i) { } return copy; }"}] }
private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke []
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "header fixture unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "header failure lost its diagnostic"
  for fuel in [0, 10, 35, 100] do
    let started ← SourceCompilerFeatureSupport.get "header suspension"
      (← complete.initial.run complete.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed, complete.outcome with
    | .failed actual heap, .failed expected initial =>
        SourceCompilerFeatureSupport.require (actual == expected && heap.heapSize == initial.heapSize)
          "header resume changed fault or allocated after failure"
    | _, _ => throw (IO.userError "header resume changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "for header checker" (checkProgram workspace)
  for (name, result) in [("mixed", 3), ("shadow", 17), ("falseFirst", 5), ("breaks", 1), ("returns", 0)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let expected := SourceCompilerFeatureSupport.scalar result
    SourceCompilerFeatureSupport.require ((← entry.run []) == expected) s!"{name}: for header value changed"
    entry.checkResume [] expected
  let mixed ← SourceCompilerFeatureSupport.compileNamed checked "mixed"
  mixed.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 3)), (.word, some (SourceCompilerFeatureSupport.scalar 3)),
    (.bool, some (.bool true)), (.word, some (SourceCompilerFeatureSupport.scalar 0)),
    (.word, some (SourceCompilerFeatureSupport.scalar 1)), (.word, some (SourceCompilerFeatureSupport.scalar 2))]
  let shadow ← SourceCompilerFeatureSupport.compileNamed checked "shadow"
  shadow.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 17)), (.word, some (SourceCompilerFeatureSupport.scalar 2)),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 1))]
  for (name, stored) in [("falseFirst", 5), ("breaks", 0), ("returns", 0)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    entry.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar stored))]
  let initializer ← SourceCompilerFeatureSupport.compileNamed checked "initializerFault"
  failureResume initializer
  initializer.checkCells [] [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 1))]
  let post ← SourceCompilerFeatureSupport.compileNamed checked "postFault"
  failureResume post
  post.checkCells [] [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, some (SourceCompilerFeatureSupport.scalar 0))]
  let absent ← SourceCompilerFeatureSupport.compileNamed checked "postAbsent"
  failureResume absent
  absent.checkCells [] [(.word, some (SourceCompilerFeatureSupport.scalar 0)), (.word, none)]
  SourceCompilerFeatureSupport.require (checkProgram escape).toOption.isNone "post local escaped its lexical scope"
  IO.println "typed for headers: mixed allocations, post scope restoration, transfer ordering, fault effects and resume GREEN"

end Tests.SourceCoreTypedForHeader
