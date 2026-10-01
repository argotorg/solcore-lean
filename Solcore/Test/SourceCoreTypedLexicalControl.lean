import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlMeaning
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! A scoped block lazily initializes a mapping and allocates three locals before
an initializer fails. The fault restores the outer context but preserves every
preceding heap effect; actual checked programs cover nested branch bindings. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreTypedLexicalControl
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedLexicalControl TypedScopedStatements CompatiblePayload GeneralHeap ReadOnly CallableIndexedHistory
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_mixed_binding", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "typed_mixed.solc"⟩, 0, 1⟩
private def expression (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .bool, [], false, none⟩
private def mappingType : TypeSystem.Ty := .mapping .bool .bool
private def inputBinder : TypedBinder := ⟨⟨owner, 0⟩, "input", .mono mappingType, [], false, none⟩
private def inputNode : ExpressionNode := {id := expression 0, span, type := mappingType, form := .reference "input" (.local inputBinder.id)}
private def keyNode : ExpressionNode := {id := expression 2, span, type := .bool, form := .reference "true" (.builtinBoolean true)}
private def indexNode : ExpressionNode := {id := expression 3, span, type := .bool, form := .index (expression 0) (expression 2)}
private def missingNode : ExpressionNode := {id := expression 1, span, type := .bool, form := .reference "missing" (.local (binder 2).id)}
private def first : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 1) (some (expression 3))⟩
private def second : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 2) none⟩
private def third : StatementNode := ⟨statement 2, span, .unit, .letDecl (binder 3) (some (expression 3))⟩
private def fourth : StatementNode := ⟨statement 3, span, .unit, .letDecl (binder 4) (some (expression 1))⟩
private def returned : StatementNode := ⟨statement 4, span, .unit, .returnStmt none⟩
private def innerStatements := [statement 0, statement 1, statement 2, statement 3, statement 4]
private def scopedBlock : StatementNode := ⟨statement 5, span, .unit, .block innerStatements⟩
private def statements := [statement 5]
private def source : TypedSource := {
  owner, inputs := [inputBinder], roots := statements.map .statement,
  nodes := [.expression inputNode, .expression missingNode, .expression keyNode, .expression indexNode, .statement first, .statement second,
    .statement third, .statement fourth, .statement returned, .statement scopedBlock] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal inputBinder.id inputBinder.scheme
private def context1 := initial.withLocal (binder 1).id (binder 1).scheme
private def context2 := context1.withLocal (binder 2).id (binder 2).scheme
private def context3 := context2.withLocal (binder 3).id (binder 3).scheme
private def context4 := context3.withLocal (binder 4).id (binder 4).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def reason := Word.ofNatModulo 37
private theorem extend {context : SourceSemantics.Context} (index : Nat)
    (binders : TypeParameterBindersWellFormed context) (fresh : LocalFresh context (binder index).id) :
    BinderExtends owner context (binder index) (context.withLocal (binder index).id (binder index).scheme) := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · exact fresh
private theorem extension1 : BinderExtends owner initial (binder 1) context1 := by
  apply extend 1
  · simp [TypeParameterBindersWellFormed, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder, inputBinder]
private theorem extension2 : BinderExtends owner context1 (binder 2) context2 := by
  apply extend 2
  · simp [TypeParameterBindersWellFormed, context1, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder, inputBinder]
private theorem extension3 : BinderExtends owner context2 (binder 3) context3 := by
  apply extend 3
  · simp [TypeParameterBindersWellFormed, context1, context2, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, context2, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder, inputBinder]
private theorem extension4 : BinderExtends owner context3 (binder 4) context4 := by
  apply extend 4
  · simp [TypeParameterBindersWellFormed, context1, context2, context3, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, signatures]
  · simp [LocalFresh, context1, context2, context3, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder, inputBinder]
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem localTyped {context : SourceSemantics.Context} {node : ExpressionNode} {index : Nat}
    (found : source.lookupExpression? node.id = some node)
    (form : node.form = .reference "input" (.local (binder index).id) ∨ node.form = .reference "missing" (.local (binder index).id))
    (type : node.type = .bool) (requirements : node.requirements = []) (coercions : node.coercions = [])
    (binders : TypeParameterBindersWellFormed context)
    (lookup : Resolved.LocalScope.Lookup context.locals (binder index).id (binder index).scheme)
    (schemes : context.LocalSchemeRequirementsLookup (binder index).id []) :
    ExpressionHasType source context node.id node.type := by
  have admitted : TypeAdmissible context .bool := .bool binders
  rcases form with form | form
  all_goals
    apply ExpressionHasType.ofOrdinary (rawType := .bool) (owned := []) (lookupExpression?_sound found)
    · rw [form]
      exact .reference (.local lookup schemes (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible admitted) []
        .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
        (by simp) (by intro _ member; cases member) .nil))
    · exact admitted
    · exact type ▸ admitted
    · intro requirement member; cases member
    · rw [coercions, type]; exact .nil _
    · simp [requirements, coercions, coercionRequirementIds]
private theorem inputTyped {context : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed context)
    (lookup : Resolved.LocalScope.Lookup context.locals inputBinder.id inputBinder.scheme)
    (schemes : context.LocalSchemeRequirementsLookup inputBinder.id []) :
    ExpressionHasType source context (expression 0) mappingType := by
  have admitted : TypeAdmissible context mappingType := .mapping (.bool binders) (.bool binders)
  apply ExpressionHasType.ofOrdinary (node := inputNode) (rawType := mappingType) (lookupExpression?_sound rfl)
    (.reference (.local lookup schemes (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible admitted) []
      .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
      (by simp) (by intro _ member; cases member) .nil))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped {context : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed context)
    (lookup : Resolved.LocalScope.Lookup context.locals inputBinder.id inputBinder.scheme)
    (schemes : context.LocalSchemeRequirementsLookup inputBinder.id []) :
    ExpressionHasType source context (expression 3) .bool := by
  have admitted : TypeAdmissible context .bool := .bool binders
  have key : ExpressionHasType source context (expression 2) .bool := by
    apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := .bool) (lookupExpression?_sound rfl)
      (.reference (.builtinBoolean true)) admitted admitted
    · intro requirement member; cases member
    · exact .nil _
    · rfl
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool) (lookupExpression?_sound rfl)
    (.index (inputTyped binders lookup schemes) key) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem inputInitial : ExpressionHasType source initial (expression 3) .bool :=
  indexTyped ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _) .head .head
private theorem inputSecond : ExpressionHasType source context2 (expression 3) .bool :=
  indexTyped ((((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _).withLocal _ _).withLocal _ _)
    (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
private theorem missingThird : ExpressionHasType source context3 (expression 1) .bool := by
  apply localTyped (node := missingNode) (index := 2) rfl (.inr rfl) rfl rfl rfl
  · exact ((((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _).withLocal _ _).withLocal _ _).withLocal _ _
  · exact .tail (by decide) .head
  · exact .tail (by decide) .head
private theorem inputSyntax : CompatibleExpressionTyped.Syntax source (expression 3) :=
  .index (node := indexNode) (keyNode := keyNode) rfl rfl rfl .bool
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := inputNode) rfl rfl)))))))
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := keyNode) rfl (.bool _ _))))))))
private theorem missingSyntax : CompatibleExpressionTyped.Syntax source (expression 1) :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := missingNode) rfl rfl))))))
private theorem innerSyntax : TypedLexicalControl.Syntax source initial false innerStatements .unit :=
  .initialized (node := first) (initializerNode := indexNode) rfl rfl rfl rfl extension1 (by decide)
    rfl rfl inputInitial inputSyntax
    (.uninitialized (node := second) rfl rfl rfl rfl extension2 (by decide)
      (.initialized (node := third) (initializerNode := indexNode) rfl rfl rfl rfl extension3 (by decide)
        rfl rfl inputSecond inputSyntax
        (.initialized (node := fourth) (initializerNode := missingNode) rfl rfl rfl rfl extension4 (by decide)
          rfl rfl missingThird missingSyntax (.body (.returnUnit (node := returned) [] rfl rfl rfl)))))
private theorem syntaxTree (mode : Bool) : TypedLexicalControl.Syntax source initial mode statements .unit :=
  .block (node := scopedBlock) rfl rfl rfl innerSyntax (.body (.nil (.inr rfl)))
private theorem valid : CompatibleExpressionLiterals.ContextValid [] initial [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member
    simp [initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType, .bool, .unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType, .bool, .unit]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private theorem nativeExists : (checked.catalog.project mappingType).toOption.isSome = true := by cbv
private def nativeType := (checked.catalog.project mappingType).toOption.get nativeExists
private def scope : SourceCoreLocalCell.Scope := [(inputBinder.id, nativeType)]
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def expressionPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 10 values
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope initial := by
  intro id declared index type selected authentic
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst id
    have found : SourceCoreDataPlaces.rootBinder source inputBinder.id = .ok inputBinder := rfl
    rw [found] at authentic; cases authentic
    exact .head
  · simp at selected
private theorem metadata {id : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

private theorem certified {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {mode : Bool} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) mode reason = .ok code) :
    TypedLexicalControl.Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source [] (fun _ => reason)
      initial scope mode statements .unit .unit code := by
  apply tree_of_flow rfl (fun _ _ _ => rfl) rfl ?_ (syntaxTree mode) rfl rfl rfl declarations rfl accepted
  intro current closed residual sameSignatures currentScope budget id node lowered declared childSyntax found typed generated
  exact CompatibleExpressionTyped.tree_of_functions unique declared sameSignatures closed residual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ (fun _ _ _ found => metadata found)
    childSyntax found typed generated

private def sourceEnvironment : Dynamic.Environment := [(inputBinder.id, ⟨0⟩)]
private def environment1 : Dynamic.Environment := ((binder 1).id, ⟨1⟩) :: sourceEnvironment
private def environment2 : Dynamic.Environment := ((binder 2).id, ⟨2⟩) :: environment1
private def environment3 : Dynamic.Environment := ((binder 3).id, ⟨3⟩) :: environment2
private def sourceHeap : Dynamic.Heap := ⟨[⟨mappingType, none, none⟩]⟩
private def initializedHeap : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping .bool .bool []), none⟩]⟩
private def heap1 : Dynamic.Heap := ⟨initializedHeap.cells ++ [⟨.bool, some (.bool false), none⟩]⟩
private def heap2 : Dynamic.Heap := ⟨heap1.cells ++ [⟨.bool, none, none⟩]⟩
private def heap3 : Dynamic.Heap := ⟨heap2.cells ++ [⟨.bool, some (.bool false), none⟩]⟩
private theorem firstIndex : Dynamic.ExpressionEvaluates program initial [] source sourceEnvironment sourceHeap
    (expression 3) (.bool false) initializedHeap := by
  apply Dynamic.ExpressionEvaluates.intro (node := indexNode) (raw := .bool false) (middle := initializedHeap) (lookupExpression?_sound rfl)
  · apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (node := inputNode) (lookupExpression?_sound rfl)
        (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil
    · exact .intro (node := keyNode) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
    · exact .nil
    · exact .bool
  · exact .nil
private theorem thirdIndex : Dynamic.ExpressionEvaluates program context2 [] source environment2 heap2
    (expression 3) (.bool false) heap2 := by
  apply Dynamic.ExpressionEvaluates.intro (node := indexNode) (raw := .bool false) (middle := heap2) (lookupExpression?_sound rfl)
  · apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (node := inputNode) (lookupExpression?_sound rfl)
        (.local rfl (.tail (by decide) (.tail (by decide) .head)) (.intro .head) rfl rfl) .nil
    · exact .intro (node := keyNode) (lookupExpression?_sound rfl) (.builtinBoolean rfl) .nil
    · exact .nil
    · exact .bool
  · exact .nil
private theorem innerFailure : Dynamic.StatementsFault program initial [] source sourceEnvironment sourceHeap
    innerStatements context3 (.uninitializedLocation ⟨2⟩) heap3 := by
  apply Dynamic.StatementsFault.tail
    (Dynamic.StatementExecutes.letInitialized (node := first) (lookupStatement?_sound rfl) rfl firstIndex
      rfl extension1 .append)
  apply Dynamic.StatementsFault.tail
    (Dynamic.StatementExecutes.letUninitialized (node := second) (lookupStatement?_sound rfl) rfl rfl extension2 .append)
  apply Dynamic.StatementsFault.tail
    (Dynamic.StatementExecutes.letInitialized (node := third) (lookupStatement?_sound rfl) rfl thirdIndex
      rfl extension3 .append)
  apply Dynamic.StatementsFault.head
  apply Dynamic.StatementFaults.letInitializer (node := fourth) (lookupStatement?_sound rfl) rfl rfl
  apply Dynamic.ExpressionFaults.form (node := missingNode) (lookupExpression?_sound rfl)
  exact .localUninitialized (owned := []) (coercions := []) (cell := ⟨.bool, none, none⟩)
    rfl (.tail (by decide) .head) (.intro (.tail (.tail .head))) rfl rfl
      (by rintro ⟨key, value, impossible⟩; cases impossible)

private theorem sourceFailure (mode : Bool) : Executes mode program initial [] source sourceEnvironment sourceHeap
    statements initial (.fault (.uninitializedLocation ⟨2⟩)) heap3 := by
  exact TypedScopedStatements.head_fault mode [] (.block (lookupStatement?_sound (node := scopedBlock) rfl) rfl innerFailure)

private def faults : FunctionCalls.FaultRep := fun error token =>
  ((∃ location, error = .uninitializedLocation location) ∧ token = reason) ∨
  (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ error = .missingMappingDefault value ∧ token = reason.add tag)
private theorem uninitialized : ∀ (id : ExpressionId) location, faults (.uninitializedLocation location) ((fun _ => reason) id) :=
  fun _ location => .inl ⟨⟨location, rfl⟩, rfl⟩
private theorem missing : ∀ (id : ExpressionId) key value tag, MetadataRep values.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((fun _ => reason) id).add tag) :=
  fun _ key value tag owned => .inr ⟨key, value, tag, owned, rfl, rfl⟩

private theorem failureContext_ne_full : context3 ≠ context4 := by
  intro same
  have impossible : 4 = 5 := congrArg (fun context => context.locals.length) same
  omega

/-- Actual completed scoped flow reconstructs its independent source trace
and result-dependent lexical environment. -/
theorem compiled_reflects {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {mode : Bool} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) mode reason = .ok code)
    {mapping world administrative actualContext canonical actual heap store ξ contextLocation native value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap initial.locals sourceEnvironment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program initial [] source sourceEnvironment heap
        statements resultContext outcome after ∧
      TypedScopedStatements.FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld
        faults .unit .unit outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner
        initial scope sourceEnvironment resultContext after := by
  have tree := certified accepted
  exact TypedLexicalControl.Tree.reflects (values := values) (ambient := ambient) (faults := faults)
    functions definitions registered (.refl _) program [] uninitialized missing
    tree valid environments heaps locals agrees typed reference read unmapped completed

theorem compiled_failure_preserves {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {mode : Bool} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (policy layouts frame globals) fuel source scope
      statements .unit (fun _ => reason) mode reason = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation native}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world sourceHeap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      TypedScopedStatements.FlowRep (values := values) (registry := values.registry) functions finalMap finalWorld
        faults .unit .unit (.fault (.uninitializedLocation ⟨2⟩)) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld heap3 finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend sourceHeap heap3 ∧
      LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner
        initial scope sourceEnvironment initial heap3 := by
  have tree := certified accepted
  exact TypedLexicalControl.Tree.preserves (values := values) (ambient := ambient) (faults := faults)
    functions definitions registered (.refl _) program [] uninitialized missing
    tree valid unique environments heaps (.cons (.intro .head) rfl (.ordinary rfl rfl) .nil)
    agrees typed reference read unmapped (sourceFailure mode)

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }",
    "function nested(take: Bool) returns (Bool) { let x = true; let m: mapping(Bool => Bool); if (take) { let x = m[true]; { let y = !x; y; } } else { let x = !m[false]; { let y: Bool; x; } } let out = x; return out; }",
    "function shadow() returns (Bool) { let x = true; { let x = false; { let x = true; x; } x; } return x; }",
    "function fail() returns (Bool) { let m: mapping(Bool => Bool); { let a = m[true]; let missing: Bool; if (true) { let b = !m[false]; let failed = (m[true], missing); let never = false; } } return true; }",
    "function missingDefault() returns (Bool) { let m: mapping(Bool => Box); if (false) { let skip = false; } else { let a = true; { let gap: Word; let failed = m[true]; } } return true; }",
    "function early() returns (Bool) { let m: mapping(Bool => Bool); { let x = m[true]; if (!x) { let hidden: Word; return !x; } } let unreachable = false; return false; }",
    "function boxed() returns (Box) { { let unused: Word; } if (true) { let flag = true; return Box(flag); } return Box(false); }"]}] }

private def requireFailureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let invocation ← entry.invoke []
  match invocation.outcome with
  | .failed token complete =>
      SourceCompilerFeatureSupport.require (← invocation.diagnostic token).isSome "lexical initializer fault diagnostic missing"
      let suspended ← SourceCompilerFeatureSupport.get "lexical suspension"
        (← invocation.initial.run invocation.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := 13})
      let checkpoint ← match suspended with
        | .outOfFuel checkpoint => pure checkpoint
        | _ => throw (IO.userError "lexical fixture did not suspend")
      match ← checkpoint.resume 300000 1024 with
      | .failed resumed finished =>
          SourceCompilerFeatureSupport.require (resumed == token && finished.heapSize == complete.heapSize)
            "lexical resumption changed failure or allocated an unreachable binding"
      | _ => throw (IO.userError "lexical checkpoint changed outcome")
  | _ => throw (IO.userError "lexical initializer unexpectedly succeeded")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "typed lexical checker" (checkProgram rawWorkspace)
  let nested ← SourceCompilerFeatureSupport.compileNamed checked "nested"
  for take in [false, true] do
    SourceCompilerFeatureSupport.require ((← nested.run [.bool take]) == .bool true)
      "scoped branch did not restore its outer binding"
    nested.checkCells [.bool take] [(.bool, some (.bool take)), (.bool, some (.bool true)),
      (.mapping .bool .bool, some (.mapping .bool .bool [])), (.bool, some (.bool (!take))),
      (.bool, if take then some (.bool true) else none), (.bool, some (.bool true))]
    nested.checkResume [.bool take] (.bool true)
  let shadow ← SourceCompilerFeatureSupport.compileNamed checked "shadow"
  SourceCompilerFeatureSupport.require ((← shadow.run []) == .bool true) "nested shadowing leaked its scope"
  shadow.checkCells [] [(.bool, some (.bool true)), (.bool, some (.bool false)), (.bool, some (.bool true))]
  shadow.checkResume [] (.bool true)
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "fail"
  requireFailureResume failed
  failed.checkCells [] [(.mapping .bool .bool, some (.mapping .bool .bool [])),
    (.bool, some (.bool false)), (.bool, none), (.bool, some (.bool true))]
  let missingDefault ← SourceCompilerFeatureSupport.compileNamed checked "missingDefault"
  requireFailureResume missingDefault
  let invocation ← missingDefault.invoke []
  match invocation.outcome with
  | .failed token _ =>
      match ← invocation.diagnostic token with
      | some {error := .typeMismatch _ none, span := some _, ..} => pure ()
      | _ => throw (IO.userError "scoped missing-default initializer lost raw metadata/span")
  | _ => throw (IO.userError "scoped missing-default initializer did not fail")
  let cells := (SourceCompilerFeatureSupport.sourceState (← missingDefault.audit [])).heap
  match cells with
  | [mapping, first, gap] =>
      SourceCompilerFeatureSupport.require ((match first.value with | some (.bool true) => true | _ => false) && gap.type == .word && gap.value.isNone)
        "scoped initializer fault changed preceding allocation order"
      match mapping.value with
      | some (.mapping .bool _ []) => pure ()
      | _ => throw (IO.userError "scoped initializer fault lost lazy root initialization")
  | _ => throw (IO.userError "scoped initializer fault allocated a failed or skipped branch binding")
  let early ← SourceCompilerFeatureSupport.compileNamed checked "early"
  SourceCompilerFeatureSupport.require ((← early.run []) == .bool true) "scoped early return was discarded"
  early.checkCells [] [(.mapping .bool .bool, some (.mapping .bool .bool [])), (.bool, some (.bool false)), (.word, none)]
  early.checkResume [] (.bool true)
  let boxed ← SourceCompilerFeatureSupport.compileNamed checked "boxed"
  match ← boxed.run [] with
  | .constructed _ [.bool true] => pure ()
  | _ => throw (IO.userError "typed lexical nominal return changed")
  IO.println "typed lexical control: mixed bindings, scoped restoration, both branches, shadowing, index effects/faults, early return and resume GREEN"
end Tests.SourceCoreTypedLexicalControl
