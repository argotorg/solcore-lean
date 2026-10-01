import Solcore.SourceSemantics.CoreLowering.BuiltinAssignmentStatements
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Real place lowering supplies a concrete nested-builtin assignment head.
Independent source execution gives its finite native prefix; arbitrary completed
native prefixes reflect source effects. Checked fixtures additionally cover
builtin keys/RHS, latest roots, fault ordering, raw data and suspension. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreBuiltinAssignmentStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality GeneralHeap ReadOnly CompatibleExpressionBuiltins
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

private def expression (native : SourceCoreGeneralFunctions.CallableContext) : SourceCoreCompatibleDataPlaces.ExpressionLowerer :=
  fun fuel source scope id reasonAt => SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody fuel compilation source scope id reasonAt

/-- No builtin callee occurrence is spuriously required to be a standalone
source expression in the fragment: the actual bare callback compiles its RHS. -/
theorem accepted_head (native : SourceCoreGeneralFunctions.CallableContext)
    {fuel : Nat} {next code : Expr} {output : Ty} {administrative : Core.Context} {definitions : DataEnvironment}
    (accepted : SourceCoreCompatibleDataPlaces.lower values signatures (expression native) fuel source scope (.declaration owner)
      assignment .equal (some (id 5)) output next reasonAt Word.zero Word.zero (fun _ => Word.zero) = .ok code) :
    ∃ head : BuiltinAssignmentStatements.Head 100 values source context [] reasonAt scope administrative definitions assignment .equal (id 5),
      code = head.emit next output := by
  apply GenericAssignmentStatements.Head.of_lower_bare rfl unique ?_ groupTyped (.inl rfl) ?_ accepted
  · intro actual binding
    have same := Except.ok.inj ((show SourceCoreCompatibleDataPlaces.rootBinder source binder.id = .ok binder from rfl).symm.trans binding)
    subst actual
    exact writable
  · intro lowered generated
    refine ⟨groupNode, by cbv, ?_⟩
    exact CompatibleExpressionBuiltins.tree_of_functions unique declarations rfl rfl rfl
      ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ native [] rfl
      (fun _ _ _ found => noCoercions _ _ found) syntaxTree (by cbv) groupTyped generated

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

section Meaning
variable {ambient : AmbientDefinitions checked.catalog.definitions}
  {administrative : Core.Context} {mapping : LocationMap} {world : StoreTyping}
  {canonical actual : Environment} {actualContext : Core.Context} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleHeap.HeapRepresents checked values.registry (functions ambient) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include environments heaps locals agrees actualTyped in
theorem accepted_preserves (native : SourceCoreGeneralFunctions.CallableContext)
    {fuel : Nat} {next code : Expr} {output : Ty}
    (accepted : SourceCoreCompatibleDataPlaces.lower values signatures (expression native) fuel source scope (.declaration owner)
      assignment .equal (some (id 5)) output next reasonAt Word.zero Word.zero (fun _ => Word.zero) = .ok code) :
    ∃ head : BuiltinAssignmentStatements.Head 100 values source context [] reasonAt scope administrative ambient.definitions assignment .equal (id 5),
      code = head.emit next output ∧ ∃ finalStore finalMap finalWorld slots,
      CompatibleHeap.HeapRepresents checked values.registry (functions ambient) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ∀ next output, CoreProof.ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (SourceCoreDataPlaces.shift 7 (next.rename ξ)) := by
  obtain ⟨head, codeEq⟩ := accepted_head native accepted
  exact ⟨head, codeEq, BuiltinAssignmentStatements.Head.preserves_prefix (values := values) (ambient := ambient) (functions ambient) (SourceCoreRawMetadata.Extends.refl values.registry) program [] valid unique
    uninitialized missing faithful (functionLeaves ambient) (functionTypes ambient) head environments heaps locals agrees actualTyped sourceAssigned⟩

include environments heaps locals agrees actualTyped in
/-- Any completion of a certified assignment reflects source effects. The
source trace is constructed by the theorem, including fault alternatives. -/
theorem completed_reflects
    (head : BuiltinAssignmentStatements.Head 100 values source context [] reasonAt scope administrative ambient.definitions assignment .equal (id 5))
    (errors : head.Errors values.registry faults) {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token sourceHeap finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context [] source environment before assignment.target .equal (id 5) reason sourceHeap ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      CompatibleHeap.HeapRepresents checked values.registry (functions ambient) finalMap finalWorld sourceHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before sourceHeap) ∨
    (∃ updated sourceHeap written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
        environment before assignment.target (id 5) updated sourceHeap ∧
      CompatibleHeap.HeapRepresents checked values.registry (functions ambient) finalMap finalWorld sourceHeap written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before sourceHeap ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      Evaluates (slots ++ actual) written (SourceCoreDataPlaces.shift 7 (next.rename ξ)) value finalStore) :=
  BuiltinAssignmentStatements.Head.reflects (values := values) (ambient := ambient) (functions ambient) (SourceCoreRawMetadata.Extends.refl values.registry) program [] valid unique uninitialized missing faithful
    (functionLeaves ambient) (functionTypes ambient) head environments heaps locals agrees actualTyped errors completed
end Meaning

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Word) }",
    "function bare(a: Word, b: Word) returns (integer) { let x: Word; x = wordFromInteger(integerAdd(wordToInteger(a), wordToInteger(b))); x += wordFromInteger(wordToInteger(a)); return wordToInteger(x); }",
    "function keys(a: Word, b: Word) returns (integer) { let m: mapping(Bool => Word); let keys: mapping(Bool => Word); m[integerEq(wordToInteger(keys[true]), wordToInteger(keys[false]))] = wordFromInteger(integerAdd(wordToInteger(b), wordToInteger(a))); return wordToInteger(m[true]); }",
    "function nested(a: Word, b: Word) returns (integer) { let m: mapping(Bool => mapping(Bool => Word)); m[integerLt(wordToInteger(a), wordToInteger(b))][integerEq(wordToInteger(a), wordToInteger(a))] = wordFromInteger(wordToInteger(a)); return wordToInteger(m[true][true]); }",
    "function sameRoot(a: Word, b: Word) returns (integer) { let m: mapping(Bool => Word); m[true] = wordFromInteger(integerAdd(wordToInteger(m[false]), wordToInteger(a))); return wordToInteger(m[true]); }",
    "function missing(a: Word, b: Word) returns (integer) { let x: Word; let rhs: mapping(Bool => Word); x += wordFromInteger(wordToInteger(rhs[true])); let never = true; return 0; }",
    "function rhsFault(a: Word, b: Word) returns (integer) { let m: mapping(Bool => Word); let keys: mapping(Bool => Word); let rhs: mapping(Bool => Word); let gap: Word; m[integerEq(wordToInteger(keys[true]), wordToInteger(a))] = wordFromInteger(integerAdd(wordToInteger(rhs[false]), wordToInteger(gap))); let never = true; return 0; }",
    "function targetFault(a: Word, b: Word) returns (integer) { let m: mapping(Bool => Box); let keys: mapping(Bool => Word); let rhs: mapping(Bool => Word); m[integerEq(wordToInteger(keys[true]), wordToInteger(a))] = .Box(wordFromInteger(wordToInteger(rhs[false]))); let never = true; return 0; }",
    "function keyFault(a: Word, b: Word) returns (integer) { let m: mapping(Bool => Word); let keys: mapping(Bool => Word); let gap: Word; let rhs: mapping(Bool => Word); m[integerEq(wordToInteger(keys[true]), wordToInteger(gap))] = wordFromInteger(wordToInteger(rhs[false])); let never = true; return 0; }"
  ]}] }

private def arguments : List SourceCompilerFeatureSupport.Value := [.word (Word.ofNatModulo 3), .word (Word.ofNatModulo 4)]
private def inputCells : List (TypeSystem.Ty × Option SourceCompilerFeatureSupport.Value) :=
  [(.word, some (.word (Word.ofNatModulo 3))), (.word, some (.word (Word.ofNatModulo 4)))]

private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke arguments
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "builtin assignment fixture unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "builtin assignment lost its diagnostic"
  for fuel in [0, 10, 35, 100] do
    let started ← SourceCompilerFeatureSupport.get "builtin assignment suspension"
      (← complete.initial.run complete.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed, complete.outcome with
    | .failed actual heap, .failed expected initial =>
        SourceCompilerFeatureSupport.require (actual == expected && heap.heapSize == initial.heapSize)
          "builtin assignment resume changed fault or ran unreachable allocation"
    | _, _ => throw (IO.userError "builtin assignment resume changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "builtin assignment checker" (checkProgram workspace)
  for (name, result) in [("bare", 10), ("keys", 7), ("nested", 3), ("sameRoot", 3)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    let expected : SourceCompilerFeatureSupport.Value := .integer (Int.ofNat result)
    SourceCompilerFeatureSupport.require ((← entry.run arguments) == expected) s!"{name}: builtin assignment value changed"
    entry.checkResume arguments expected
  let bare ← SourceCompilerFeatureSupport.compileNamed checked "bare"
  bare.checkCells arguments (inputCells ++ [(.word, some (.word (Word.ofNatModulo 10)))])
  let latest ← SourceCompilerFeatureSupport.compileNamed checked "sameRoot"
  latest.checkCells arguments (inputCells ++ [(.mapping .bool .word, some (.mapping .bool .word [(.bool true, .word (Word.ofNatModulo 3))]))])
  let missing ← SourceCompilerFeatureSupport.compileNamed checked "missing"
  failureResume missing
  missing.checkCells arguments (inputCells ++ [(.word, none), (.mapping .bool .word, some (.mapping .bool .word []))])
  let rhs ← SourceCompilerFeatureSupport.compileNamed checked "rhsFault"
  failureResume rhs
  rhs.checkCells arguments (inputCells ++ [(.mapping .bool .word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.mapping .bool .word, some (.mapping .bool .word [])), (.word, none)])
  let target ← SourceCompilerFeatureSupport.compileNamed checked "targetFault"
  failureResume target
  let cells := (SourceCompilerFeatureSupport.sourceState (← target.audit arguments)).heap
  SourceCompilerFeatureSupport.require ((match cells with | [_, _, first, second, third] => first.value.isNone && second.value.isSome && third.value.isNone | _ => false))
    "builtin target fault executed RHS or continuation"
  let key ← SourceCompilerFeatureSupport.compileNamed checked "keyFault"
  failureResume key
  key.checkCells arguments (inputCells ++ [(.mapping .bool .word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, none), (.mapping .bool .word, none)])
  IO.println "builtin assignment: concrete child closure, nested keys/RHS, ordered faults, retained heap and resume GREEN"
end Tests.SourceCoreBuiltinAssignmentStatements
