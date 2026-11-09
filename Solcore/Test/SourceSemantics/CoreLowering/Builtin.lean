import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinImperative
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConditionals
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinCalls
import Solcore.Test.SourceSemantics.CoreLowering.OperatorCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedCanonicalSupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.Test.SourceSemantics.CoreLowering.Foundations.ReachableDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinBodies
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport

/-!
# Builtin lowering tests

Builtin calls, builtin bodies and nested builtins in assignments, loops, matches and lexical statements.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinAssignmentStatements
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
  ((∃ location, reason = .uninitializedLocation location ∧ token = Word.zero) ∨
   (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ reason = .missingMappingDefault value ∧ token = Word.zero.add tag) ∨
   (reason = .invalidAssignmentOperands .equal ∧ token = Word.zero)) ∨
  ∃ code, reason = .panic code ∧ token = Solcore.Frontend.SourceCorePanics.reason code
/-- Every panic fails with its code's reason. -/
private instance : FunctionCalls.FaultTokens faults := ⟨fun code => .inr ⟨code, rfl, rfl⟩⟩
private theorem uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id) :=
  fun _ location => .inl (.inl ⟨location, rfl, rfl⟩)
private theorem missing : ∀ id key value tag, MetadataRep values.registry (.mapping key value) tag →
  faults (.missingMappingDefault value) ((reasonAt id).add tag) :=
  fun _ key value tag owned => .inl (.inr (.inl ⟨key, value, tag, owned, rfl, rfl⟩))
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinBodyMeaning
/-! The real seven builtin bodies retain arbitrary captures and stores. A
selected argument allocates once before invocation; completed executions recover
the independent source primitive result and exactly that post-argument store. -/
set_option autoImplicit false
namespace Tests.SourceCoreBuiltinBodyMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open BuiltinBodyMeaning

private def effectfulArgument : Expr :=
  .letE (.newCell .integer (.integer 37)) (.pair (.integer (-9)) (.integer 4))

private theorem argument_meaning (environment : Environment) (store : Store) :
    Evaluates environment store effectfulArgument (.pair (.integer (-9)) (.integer 4))
      (store ++ [.integer 37]) :=
  .letE (.newCell .integer) (.pair .integer .integer)

/-- The primitive body uses the selected packed argument after its allocation,
even when arbitrary ambient values are captured by the actual compiler closure. -/
theorem effectful_sub_preserves (environment : Environment) (store : Store) :
    Evaluates environment store
      (.apply (SourceCoreInteger.builtinClosure .integerSub) effectfulArgument)
      (.inRight .word (.integer (-13))) (store ++ [.integer 37]) := by
  obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ :=
    (InputRep.integerSub (-9) 4).closure_preserves (argument_meaning environment store)
  cases applied
  cases related
  exact evaluated

/-- Completion alone determines the source result, retains the argument effect,
and preserves the entire supplied native store prefix. -/
theorem effectful_sub_reflects {environment : Environment} {store finalStore : Store}
    {result : Value}
    (completed : Evaluates environment store
      (.apply (SourceCoreInteger.builtinClosure .integerSub) effectfulArgument)
      result finalStore) :
    Dynamic.BuiltinApplies .integerSub [.integer (-9), .integer 4] (.integer (-13)) ∧
      result = .inRight .word (.integer (-13)) ∧ finalStore = store ++ [.integer 37] := by
  obtain ⟨sourceResult, nativeResult, applied, related, resultEq, storeEq⟩ :=
    (InputRep.integerSub (-9) 4).closure_reflects (argument_meaning environment store) completed
  cases applied
  cases related
  exact ⟨.integerSub (-9) 4, resultEq, storeEq⟩

private def huge : Int := (2 : Int) ^ 1024 + 17
private def ambient : Value := .closure .integer .integer (.loadCell (.var 1)) [.cellRef .integer 1]
private def environment : Environment := [.integer 999, ambient]
private def store : Store := [ambient, .integer huge]

private def cases : List (BuiltinFunctionId × Expr × Value) := [
  (.integerSub, .pair (.integer (-huge)) (.integer 19), .integer (-huge - 19)),
  (.integerAdd, .pair (.integer huge) (.integer (-19)), .integer (huge - 19)),
  (.integerMul, .pair (.integer huge) (.integer (-huge)), .integer (-(huge * huge))),
  (.integerEq, .pair (.integer huge) (.integer huge), .bool true),
  (.integerEq, .pair (.integer huge) (.integer (-huge)), .bool false),
  (.integerLt, .pair (.integer (-huge)) (.integer 0), .bool true),
  (.integerLt, .pair (.integer huge) (.integer 0), .bool false),
  (.wordFromInteger, .integer (-huge), .word (Word.ofIntModulo (-huge))),
  (.wordFromInteger, .integer huge, .word (Word.ofIntModulo huge)),
  (.wordToInteger, .word (Word.ofNatModulo (wordModulus - 1)), .integer (Int.ofNat (wordModulus - 1)))
]

private def check (function : BuiltinFunctionId) (argument : Expr) (expected : Value) : IO Unit := do
  let argument := Expr.letE (.newCell .integer (.integer 37)) argument
  let initial : Core.State := ⟨.eval (.apply (SourceCoreInteger.builtinClosure function) argument) environment, [], store⟩
  let complete := runStateful 1000 initial
  SourceCompilerFeatureSupport.require
    (complete == .done (.inRight .word expected) (store ++ [.integer 37]))
    "actual builtin body changed its result, captures, store prefix, or argument allocation"
  for fuel in [0, 3, 9, 15] do
    match runStateful fuel initial with
    | .outOfFuel checkpoint =>
        SourceCompilerFeatureSupport.require (runStateful 1000 checkpoint == complete)
          "actual builtin resume repeated argument effects or changed result/store"
    | .done value finalStore =>
        SourceCompilerFeatureSupport.require
          (StatefulRunResult.done value finalStore == complete) "completed builtin prefix differed"
    | _ => throw (IO.userError "actual builtin prefix became stuck")

def run : IO Unit := do
  for (function, argument, expected) in cases do
    check function argument expected
  IO.println "actual builtin bodies: seven independent meanings, captures, argument effects, integers and resume GREEN"
end Tests.SourceCoreBuiltinBodyMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCalls
/-! Actual tagged/contracted builtin invocation retains argument effects and
skips later arguments after a source failure. Independent source application
and static compiler selection are exercised without a source evaluator. -/
set_option autoImplicit false
namespace Tests.SourceCoreBuiltinCalls
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open BuiltinBodyMeaning BuiltinCalls.Protocol

private def identity : Word := Word.ofNatModulo 9
private def contract : Word := Word.ofNatModulo 17
private def unknown : Word := Word.ofNatModulo 29
private def arguments : Expr :=
  .letE (.newCell .integer (.integer 37))
    (LanguageResult.success (.pair (.integer (-9)) (.integer 4)))

private theorem argument_meaning (environment : Environment) (store : Store) :
    Evaluates (.unit :: contractedValue .integerSub identity contract environment :: environment) store
      ((arguments.weakenAt 0).weakenAt 0) (.inRight .word (.pair (.integer (-9)) (.integer 4)))
      (store ++ [.integer 37]) := by
  simp only [arguments, Expr.weakenAt, LanguageResult.success]
  exact .letE (.newCell .integer) (.inRight (.pair .integer .integer))

theorem contracted_sub_preserves (environment : Environment) (store : Store) :
    Evaluates environment store
      (CallableContract.call [⟨contract, none, none⟩] unknown .integer
        (contracted .integerSub identity contract) arguments)
      (.inRight .word (.integer (-13))) (store ++ [.integer 37]) := by
  obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ :=
    contracted_preserves (InputRep.integerSub (-9) 4) (argument_meaning environment store)
  cases applied
  cases related
  exact evaluated

theorem contracted_sub_reflects {environment : Environment} {store finalStore : Store} {result : Value}
    (completed : Evaluates environment store
      (CallableContract.call [⟨contract, none, none⟩] unknown .integer
        (contracted .integerSub identity contract) arguments) result finalStore) :
    Dynamic.BuiltinApplies .integerSub [.integer (-9), .integer 4] (.integer (-13)) ∧
      result = .inRight .word (.integer (-13)) ∧ finalStore = store ++ [.integer 37] := by
  obtain ⟨sourceResult, nativeResult, applied, related, resultEq, storeEq⟩ :=
    contracted_reflects (InputRep.integerSub (-9) 4) (argument_meaning environment store) completed
  cases applied
  cases related
  exact ⟨.integerSub (-9) 4, resultEq, storeEq⟩

private def huge : Int := (2 : Int) ^ 1024 + 17
private def ambient : Value := .closure .integer .integer (.loadCell (.var 1)) [.cellRef .integer 1]
private def store : Store := [ambient, .integer huge]
private def environment : Environment := [.integer 99, ambient]

private def checkNative (code : Expr) (result : Value) (after : Store) : IO Unit := do
  let initial : Core.State := ⟨.eval code environment, [], store⟩
  let complete := runStateful 1000 initial
  SourceCompilerFeatureSupport.require (complete == .done result after)
    "builtin call changed argument order/effects, result or ambient store"
  for fuel in [0, 5, 11, 23, 37] do
    match runStateful fuel initial with
    | .outOfFuel checkpoint =>
        SourceCompilerFeatureSupport.require (runStateful 1000 checkpoint == complete)
          "builtin checkpoint/resume changed argument effects or result/store"
    | .done value finalStore =>
        SourceCompilerFeatureSupport.require (StatefulRunResult.done value finalStore == complete)
          "completed builtin prefix changed result/store"
    | _ => throw (IO.userError "builtin call became stuck")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function sub(a: integer, b: integer) returns (integer) { return integerSub(a, b); }",
    "function add(a: integer, b: integer) returns (integer) { return integerAdd(a, b); }",
    "function mul(a: integer, b: integer) returns (integer) { return integerMul(a, b); }",
    "function eq(a: integer, b: integer) returns (Bool) { return integerEq(a, b); }",
    "function lt(a: integer, b: integer) returns (Bool) { return integerLt(a, b); }",
    "function from(a: integer) returns (Word) { return wordFromInteger(a); }",
    "function to(a: Word) returns (integer) { return wordToInteger(a); }"]}] }

def run : IO Unit := do
  checkNative (TaggedFunction.call .integer (tagged .integerSub identity) arguments)
    (.inRight .word (.integer (-13))) (store ++ [.integer 37])
  checkNative (CallableContract.call [⟨contract, none, none⟩] unknown .integer
    (contracted .integerSub identity contract) arguments)
    (.inRight .word (.integer (-13))) (store ++ [.integer 37])
  let reason := Word.ofNatModulo 41
  let failed : Expr := .letE (.newCell .integer (.integer 37)) (LanguageResult.failure .integer (.word reason))
  let later : Expr := .letE (.newCell .integer (.integer 73)) (LanguageResult.success (.integer 4))
  let failedArguments := LocalSequence.pair .integer .integer failed later
  checkNative (TaggedFunction.call .integer (tagged .integerSub identity) failedArguments)
    (.inLeft .integer (.word reason)) (store ++ [.integer 37])
  checkNative (CallableContract.call [⟨contract, none, none⟩] unknown .integer
    (contracted .integerSub identity contract) failedArguments)
    (.inLeft .integer (.word reason)) (store ++ [.integer 37])
  let checked ← SourceCompilerFeatureSupport.get "builtin actual source checker" (checkProgram workspace)
  let cases : List (String × List SourceCoreExecution.Value × SourceCoreExecution.Value) := [
    ("sub", [.integer (-huge), .integer 19], .integer (-huge - 19)),
    ("add", [.integer huge, .integer (-19)], .integer (huge - 19)),
    ("mul", [.integer huge, .integer (-huge)], .integer (-(huge * huge))),
    ("eq", [.integer huge, .integer huge], .bool true),
    ("eq", [.integer huge, .integer (-huge)], .bool false),
    ("lt", [.integer (-huge), .integer 0], .bool true),
    ("lt", [.integer huge, .integer 0], .bool false),
    ("from", [.integer (-huge)], .word (Word.ofIntModulo (-huge))),
    ("from", [.integer huge], .word (Word.ofIntModulo huge)),
    ("to", [.word (Word.ofNatModulo (wordModulus - 1))], .integer (Int.ofNat (wordModulus - 1)))
  ]
  for (name, inputs, expected) in cases do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    SourceCompilerFeatureSupport.require ((← entry.run inputs) == expected)
      "actual cached compiler builtin call changed fixed signature, identity, code or scalar result"
    entry.checkResume inputs expected
  IO.println "actual builtin calls: compiler receipts, pure gates, ordered argument effects, failures and resume GREEN"
end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics
structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  read : ExpressionNode
  innerReturn : StatementNode
  expression : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.function .unit .word]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  readFound : function.typedBody.lookupExpression? read.id = some read
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  readForm : read.form = .reference binder.name (.local binder.id)
  readRaw : read.rawType = .word
  readType : read.type = .word
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  innerReturnForm : innerReturn.form = .returnStmt (some read.id)
  innerReturnType : innerReturn.type = .word
  lambda : expression.form = .lambda [] .word [innerReturn.id]
  expressionRaw : expression.rawType = .function .unit .word
  expressionType : expression.type = .function .unit .word
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = .function .unit .word

private theorem statementRoots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]

theorem FactoryShape.statementTyping
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : FactoryShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {
    type := .function .unit .word
    hasValue := true
    sawReturn := true
    control := .returned }
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables,
        shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have callable : TypeAdmissible lexical (.function .unit .word) :=
      ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
    have instantiation : LocalSchemeInstantiationValid lexical shape.binder .word [] := by
      refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.binderRequirements)
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible word) [] ?_ ?_ ?_ (by simp) ?_ ?_
      · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
      · intro metavariable replacement member; cases member
      · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
      · intro id member; cases member
      · rw [instantiateLocalSchemePredicates, shape.binderRequirements]
        exact .nil
    have readTyped : ExpressionHasType function.typedBody lexical shape.read.id .word := by
      rw [← shape.readType]
      refine .intro (lookupExpression?_sound shape.readFound)
        (shape.readForm ▸ ExpressionFormHasRawType.reference
          (.local head.local_self head.local_scheme_requirements_self instantiation))
        shape.readRaw word (shape.readType ▸ word) ?_
      · rw [shape.readRequirements, shape.readCoercions, shape.readType]
        exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have expressionTyped : ExpressionHasType function.typedBody lexical shape.expression.id
        (.function .unit .word) := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
          (.singleton (.returnValue (lookupStatement?_sound shape.innerReturnFound)
            shape.innerReturnForm readTyped shape.innerReturnType))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw
        callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.returnStatement expressionTyped shape.statementType)⟩

private def workspace_variant : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function identity(value: Word) returns (Word) { return value; } function make(seed: Word) returns (function() returns (Word)) { return lam() { return seed; }; } function relay(seed: Word) returns (function() returns (Word)) { return make(identity(seed) + wordFromInteger(0)); }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def shape (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (FactoryShape function signature) := do
  let [binder] := function.typedBody.inputs
    | throw (IO.userError "captured factory input shape")
  let [Node.expression read, Node.statement innerReturn,
      Node.expression expression, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "captured factory occurrence shape")
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "captured factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "captured factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function .unit .word]) "captured factory returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "captured factory inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "captured factory binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "captured factory roots"
  let ⟨readFound⟩ ← observed (function.typedBody.lookupExpression? read.id = some read) "captured factory readFound"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "captured factory innerReturnFound"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "captured factory expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "captured factory statementFound"
  let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "captured factory readForm"
  let ⟨readRaw⟩ ← observed (read.rawType = .word) "captured factory readRaw"
  let ⟨readType⟩ ← observed (read.type = .word) "captured factory readType"
  let ⟨readRequirements⟩ ← observed (read.requirements = []) "captured factory readRequirements"
  let ⟨readCoercions⟩ ← observed (read.coercions = []) "captured factory readCoercions"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some read.id)) "captured factory innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "captured factory innerReturnType"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [] .word [innerReturn.id]) "captured factory lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = .function .unit .word) "captured factory expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = .function .unit .word) "captured factory expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "captured factory requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "captured factory coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "captured factory returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = .function .unit .word) "captured factory statementType"
  return { binder, read, innerReturn, expression, statement, parameters, inputTypes, returns, inputs, binderRequirements, roots, readFound, innerReturnFound, expressionFound, statementFound, readForm, readRaw, readType, readRequirements, readCoercions, innerReturnForm, innerReturnType, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType }


abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev TypedNode := Tests.SourceCoreOperatorCalls.TypedNode
abbrev IdentityShape := Tests.SourceCoreOperatorCalls.IdentityShape
abbrev closureType : TypeSystem.Ty := .function .unit .word

private theorem parameter_nil (type : TypeSystem.Ty) :
    TypeSystem.ParameterSubstitution.apply [] type = type := by
  induction type <;> simp_all [TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?]

/-- Exact original metadata of a monomorphic direct call. -/
structure DirectCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (argument : ExpressionId) (expected : TypeSystem.Ty) where
  callee : TypedNode source (.function .word expected)
  value : TypedNode source expected
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : value.node.form = .call callee.node.id [argument] (.declaration instantiation)
  scheme : signature.scheme = ⟨[], [], .function .word expected⟩
  inputs : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [expected]
  exact : instantiation = ⟨signature.id, [], .function .word expected, [],
    signature.parameterComptime, signature.returnComptime⟩

theorem DirectCall.typed {source : TypedSource} {signature : ProgramFunctionSignature}
    {argument : ExpressionId} {expected : TypeSystem.Ty}
    (call : DirectCall source signature argument expected) {context : SourceSemantics.Context}
    (member : signature ∈ context.signatures.functions)
    (admissible : TypeAdmissible context expected)
    (argumentTyped : ExpressionHasType source context argument .word) :
    ExpressionHasType source context call.value.node.id expected := by
  have valid : SourceSemantics.DeclarationInstantiation.Admissible context call.instantiation := by
    rw [call.exact]
    refine .intro signature member rfl ?_ ?_ ?_ ?_ rfl rfl
    · simpa only [call.scheme] using ParameterSubstitution.exact_empty
    · intro parameter replacement contained; cases contained
    · simp [call.scheme, parameter_nil]
    · simp [call.scheme]
  have application : DeclarationApplicationValid context call.instantiation [.word] expected [] := by
    refine .intro member valid ?_ ?_ ?_ ?_ ?_
    · simp [call.exact]
    · simp [call.exact, call.inputs]
    · simp [call.exact, call.returns, TypeSystem.Ty.productMany, parameter_nil]
    · simp [call.exact, TypeSystem.Ty.productMany]
    · simp [call.exact]
  have callee : DirectDeclarationCalleeValid context source call.callee.node.id call.instantiation :=
    .intro (lookupExpression?_sound call.callee.found) call.calleeForm valid
      (call.callee.type.trans (by rw [call.exact])) call.callee.requirements call.callee.coercions
  have typed : ExpressionHasType source context call.value.node.id call.value.node.type := by
    refine .intro (lookupExpression?_sound call.value.found)
      (call.form ▸ ExpressionFormHasRawType.directCall callee application (.cons argumentTyped (.nil _)))
      call.value.raw admissible (call.value.type.symm ▸ admissible) ?_
    rw [call.value.requirements, call.value.coercions, call.value.type]
    exact .directCall (.intro (.nil _) (.nil _) .nil rfl rfl)
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

private theorem builtin_integer_evidence (context : SourceSemantics.Context) :
    RetainedEvidenceValid context.assumptions context.signatures.resolutionRules
      (ProgramSignatures.builtinIntPredicate .integer)
      (.implementation (.byImpl (ProgramSignatures.builtinIntPredicate .integer) (.builtin .intInteger) [])) := by
  apply RetainedEvidenceValid.intro (.implementation (.byImpl .nil))
  exact .implementation (rule := ProgramSignatures.builtinIntIntegerRule) (by simp [ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]) rfl
    (.intro ⟨[], []⟩ ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩ rfl rfl) .nil

structure IntegerLiteral (function : CheckedFunction) where
  node : ExpressionNode
  spelling : Syntax.CoreLiteralValue
  resolution : IntegerLiteralResolution
  validated : SourceCoreElaboration.NativeIntegerLiteral
  found : function.typedBody.lookupExpression? node.id = some node
  form : node.form = .integerLiteral spelling resolution
  raw : node.rawType = .integer
  accepted : SourceCoreElaboration.validateNativeIntegerLiteral function.solvedRequirements node spelling resolution = .ok validated

theorem IntegerLiteral.typed {function : CheckedFunction} (literal : IntegerLiteral function)
    {context : SourceSemantics.Context} (word : TypeAdmissible context .integer)
    (ledger : context.solvedRequirements = function.solvedRequirements) :
    ExpressionHasType function.typedBody context literal.node.id .integer := by
  have metadata := SourceCoreElaboration.validateNativeIntegerLiteral_sound literal.accepted
  obtain ⟨row, selected, predicate, evidence⟩ := CoreLowering.NumericLiteralEvidenceReceipts.integer literal.accepted
  have member : row ∈ function.solvedRequirements.filter (fun row => decide (row.id = literal.resolution.requirement)) := by
    rw [selected]; simp
  obtain ⟨member, identity⟩ := List.mem_filter.mp member
  have proves : RequirementProves context literal.resolution.requirement
      (ProgramSignatures.builtinIntPredicate literal.resolution.targetType) := by
    refine ⟨row, ⟨ledger ▸ member, of_decide_eq_true identity⟩, predicate, .intro ?_⟩
    rw [evidence, predicate]
    change RetainedEvidenceValid _ _ (ProgramSignatures.builtinIntPredicate literal.resolution.targetType) _
    rw [metadata.targetType]
    simpa only [IntegerLiteralResolution.predicate, metadata.targetType] using builtin_integer_evidence context
  have valid : IntegerLiteralValid context literal.spelling literal.resolution :=
    .integer metadata.meaning metadata.targetType proves
  have typed : ExpressionHasType function.typedBody context literal.node.id literal.node.type := by
    refine .intro (lookupExpression?_sound literal.found)
      (literal.form ▸ ExpressionFormHasRawType.integerLiteral valid)
      (literal.raw.trans metadata.targetType.symm) (metadata.targetType.symm ▸ word)
      (metadata.nodeType.symm ▸ word) ?_
    rw [metadata.requirements, metadata.coercions, metadata.targetType, metadata.nodeType]
    exact .ordinary (by intro id member; have same := List.mem_singleton.mp member; exact same ▸ valid.requirement_valid) (.nil _) rfl
  exact metadata.nodeType ▸ typed

/-- Actual compiler-provided builtin callee and ordered argument metadata. -/
structure BuiltinCall (source : TypedSource) (function : BuiltinFunctionId)
    (argument : ExpressionId) where
  callee : TypedNode source function.type
  value : TypedNode source function.returnType
  name : String
  calleeForm : callee.node.form = .reference name (.builtinFunction function)
  form : value.node.form = .call callee.node.id [argument] (.builtinFunction function)

theorem BuiltinCall.typed {source : TypedSource} {function : BuiltinFunctionId}
    {argument : ExpressionId} (call : BuiltinCall source function argument)
    {context : SourceSemantics.Context} {parameter : TypeSystem.Ty}
    (parameters : function.parameterTypes = [parameter])
    (admissible : TypeAdmissible context function.returnType)
    (argumentTyped : ExpressionHasType source context argument parameter) :
    ExpressionHasType source context call.value.node.id function.returnType := by
  have callee : DirectBuiltinCalleeValid source call.callee.node.id function :=
    .intro (lookupExpression?_sound call.callee.found) call.calleeForm
      call.callee.type call.callee.requirements call.callee.coercions
  have arguments : ExpressionsHaveTypes source context [argument] function.parameterTypes := by
    rw [parameters]
    exact .cons argumentTyped (.nil _)
  have typed : ExpressionHasType source context call.value.node.id call.value.node.type := by
    refine .intro (lookupExpression?_sound call.value.found)
      (call.form ▸ ExpressionFormHasRawType.builtinCall callee arguments)
      call.value.raw admissible (call.value.type.symm ▸ admissible) ?_
    rw [call.value.requirements, call.value.coercions, call.value.type]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

private def observeBuiltin (source : TypedSource) (function : BuiltinFunctionId)
    (argument : ExpressionId) (calleeNode valueNode : ExpressionNode) :
    IO (BuiltinCall source function argument) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source calleeNode function.type
  let value ← Tests.SourceCoreOperatorCalls.observeNode source valueNode function.returnType
  let .reference name (.builtinFunction _) := calleeNode.form
    | throw (IO.userError "builtin callee original form")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.builtinFunction function)) "builtin callee metadata"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [argument] (.builtinFunction function)) "builtin call metadata"
  return {callee, value, name, calleeForm, form}

structure RelayShape (function : CheckedFunction) (signature identity maker : ProgramFunctionSignature) where
  binder : TypedBinder
  read : Read function.typedBody binder .word
  inner : DirectCall function.typedBody identity read.node.id .word
  zero : IntegerLiteral function
  converted : BuiltinCall function.typedBody .wordFromInteger zero.node.id
  sum : TypedNode function.typedBody .word
  sumForm : sum.node.form = .binary inner.value.node.id .add converted.value.node.id
  outer : DirectCall function.typedBody maker sum.node.id closureType
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [closureType]
  inputs : function.typedBody.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some outer.value.node.id)
  statementType : statement.type = closureType

def RelayShape.nodeList {function signature identity maker} (shape : RelayShape function signature identity maker) : List Node :=
  [.expression shape.read.node, .expression shape.inner.callee.node, .expression shape.inner.value.node,
   .expression shape.zero.node, .expression shape.converted.callee.node,
   .expression shape.converted.value.node, .expression shape.sum.node,
   .expression shape.outer.callee.node, .expression shape.outer.value.node, .statement shape.statement]

theorem RelayShape.statementTyping {function signature identity maker}
    (shape : RelayShape function signature identity maker) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) (makeMember : maker ∈ signatures.functions) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := closureType, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by
      rw [head.context_fields.1]
      rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have callable : TypeAdmissible lexical closureType := ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
    have read := shape.read.typed scheme shape.binderRequirements word head.local_self head.local_scheme_requirements_self
    have inner := shape.inner.typed (fields ▸ identityMember) word read
    have integer : TypeAdmissible lexical .integer := ⟨binders, .builtin .integer⟩
    have ledger : lexical.solvedRequirements = function.solvedRequirements := by cases head; rfl
    have zero := shape.zero.typed integer ledger
    have converted := shape.converted.typed rfl word zero
    have sum := shape.sum.ordinary word (shape.sumForm ▸ .binary inner converted (.wordArithmetic .add))
    have outer := shape.outer.typed (fields ▸ makeMember) callable sum
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm outer shape.statementType)⟩

def observeDirect (source : TypedSource) (signature : ProgramFunctionSignature)
    (argument : ExpressionId) (callee value : ExpressionNode) (expected : TypeSystem.Ty) :
    IO (DirectCall source signature argument expected) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function .word expected)
  let value ← Tests.SourceCoreOperatorCalls.observeNode source value expected
  let .reference name (.declaration instantiation) := callee.node.form
    | throw (IO.userError "direct synthetic declaration callee")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "direct callee"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [argument] (.declaration instantiation)) "direct call"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[], [], .function .word expected⟩) "direct signature"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [.word]) "direct parameter"
  let ⟨returns⟩ ← observed (signature.returnTypes = [expected]) "direct return"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id, [], .function .word expected, [],
    signature.parameterComptime, signature.returnComptime⟩) "direct exact metadata"
  return {callee, value, name, instantiation, calleeForm, form, scheme, inputs, returns, exact}

def observeIntegerLiteral (function : CheckedFunction) (node : ExpressionNode) : IO (IntegerLiteral function) := do
  match form : node.form with
  | .integerLiteral spelling resolution =>
    match accepted : SourceCoreElaboration.validateNativeIntegerLiteral function.solvedRequirements node spelling resolution with
    | .error error => throw (IO.userError (reprStr error))
    | .ok validated =>
      let ⟨found⟩ ← observed (function.typedBody.lookupExpression? node.id = some node) "literal lookup"
      let ⟨raw⟩ ← observed (node.rawType = .integer) "literal raw Integer"
      return ⟨node, spelling, resolution, validated, found, form, raw, accepted⟩
  | _ => throw (IO.userError "integer literal expected")

def relayShape (function : CheckedFunction) (signature identity maker : ProgramFunctionSignature) :
    IO (RelayShape function signature identity maker) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "relay input")
  let [.expression read, .expression innerCallee, .expression innerValue,
      .expression zeroNode, .expression convertedCallee,
      .expression convertedValue, .expression sumNode,
      .expression outerCallee, .expression outerValue, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "relay original nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder read .word
  let inner ← observeDirect function.typedBody identity read.node.id innerCallee innerValue .word
  let zero ← observeIntegerLiteral function zeroNode
  let converted ← observeBuiltin function.typedBody .wordFromInteger zero.node.id convertedCallee convertedValue
  let sum ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody sumNode .word
  let ⟨sumForm⟩ ← observed (sum.node.form = .binary inner.value.node.id .add converted.value.node.id) "relay sum form"
  let outer ← observeDirect function.typedBody maker sum.node.id outerCallee outerValue closureType
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "relay parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "relay inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [closureType]) "relay returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "relay inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "relay binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "relay binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "relay binderOrdinary"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "relay roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "relay statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some outer.value.node.id)) "relay statementForm"
  let ⟨statementType⟩ ← observed (statement.type = closureType) "relay statementType"
  return {binder, read, inner, zero, converted, sum, sumForm, outer, statement, parameters, inputTypes, returns, inputs, binderScheme, binderRequirements, binderOrdinary, roots, statementFound, statementForm, statementType}

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace_variant 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  identityFunction : CheckedFunction
  makeFunction : CheckedFunction
  relayFunction : CheckedFunction
  identitySignature : ProgramFunctionSignature
  makeSignature : ProgramFunctionSignature
  relaySignature : ProgramFunctionSignature
  functions : program.functions = [identityFunction, makeFunction, relayFunction]
  signatures : program.signatures.functions = [identitySignature, makeSignature, relaySignature]
  methods : program.methods = []
  identityDeclaration : identityFunction.declaration = identitySignature.id
  makeDeclaration : makeFunction.declaration = makeSignature.id
  relayDeclaration : relayFunction.declaration = relaySignature.id
  identityMake : identitySignature.id ≠ makeSignature.id
  identityRelay : identitySignature.id ≠ relaySignature.id
  makeRelay : makeSignature.id ≠ relaySignature.id
  identityShape : IdentityShape identityFunction identitySignature
  makeShape : FactoryShape makeFunction makeSignature
  relayShape : RelayShape relayFunction relaySignature identitySignature makeSignature
  identityNodes : identityFunction.typedBody.nodes = identityShape.nodeList
  makeNodes : makeFunction.typedBody.nodes = [.expression makeShape.read,
    .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]
  relayNodes : relayFunction.typedBody.nodes = relayShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace_variant 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [identityFunction, makeFunction, relayFunction], [identitySignature, makeSignature, relaySignature] =>
      let identityShape ← Tests.SourceCoreOperatorCalls.observeIdentity identityFunction identitySignature
      let makeShape ← shape makeFunction makeSignature
      let relayShape ← relayShape relayFunction relaySignature identitySignature makeSignature
      let ⟨methods⟩ ← observed (program.methods = []) "direct fixture methods"
      let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id) "direct fixture identityDeclaration"
      let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "direct fixture makeDeclaration"
      let ⟨relayDeclaration⟩ ← observed (relayFunction.declaration = relaySignature.id) "direct fixture relayDeclaration"
      let ⟨identityMake⟩ ← observed (identitySignature.id ≠ makeSignature.id) "direct fixture identityMake"
      let ⟨identityRelay⟩ ← observed (identitySignature.id ≠ relaySignature.id) "direct fixture identityRelay"
      let ⟨makeRelay⟩ ← observed (makeSignature.id ≠ relaySignature.id) "direct fixture makeRelay"
      let ⟨identityNodes⟩ ← observed (identityFunction.typedBody.nodes = identityShape.nodeList) "direct fixture identityNodes"
      let ⟨makeNodes⟩ ← observed (makeFunction.typedBody.nodes = [.expression makeShape.read, .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]) "direct fixture makeNodes"
      let ⟨relayNodes⟩ ← observed (relayFunction.typedBody.nodes = relayShape.nodeList) "direct fixture relayNodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl | rfl <;> rcases candidateMember with rfl | rfl | rfl
          · exact identityShape.statementTyping program.signatures
          · exact False.elim (identityMake (identityDeclaration.symm.trans identity))
          · exact False.elim (identityRelay (identityDeclaration.symm.trans identity))
          · exact False.elim (identityMake (identity.symm.trans makeDeclaration))
          · exact makeShape.statementTyping program.signatures
          · exact False.elim (makeRelay (makeDeclaration.symm.trans identity))
          · exact False.elim (identityRelay (identity.symm.trans relayDeclaration))
          · exact False.elim (makeRelay (identity.symm.trans relayDeclaration))
          · exact relayShape.statementTyping program.signatures (by simp [signatures]) (by simp [signatures])
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {
        program := program
        checked := checked
        wellFormed := programWellFormed_ofCheckProgram_statements checked deep
        identityFunction := identityFunction
        makeFunction := makeFunction
        relayFunction := relayFunction
        identitySignature := identitySignature
        makeSignature := makeSignature
        relaySignature := relaySignature
        functions := functions
        signatures := signatures
        methods := methods
        identityDeclaration := identityDeclaration
        makeDeclaration := makeDeclaration
        relayDeclaration := relayDeclaration
        identityMake := identityMake
        identityRelay := identityRelay
        makeRelay := makeRelay
        identityShape := identityShape
        makeShape := makeShape
        relayShape := relayShape
        identityNodes := identityNodes
        makeNodes := makeNodes
        relayNodes := relayNodes
      }
    | _, _ => throw (IO.userError "direct fixture declaration count")

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics

structure CompiledFixture extends CheckedFixture where
  seeds : List SourceCompiler.Seed
  options : SourceCompiler.Options
  facadeCompiled : SourceCompiler.Compiled
  accepted : SourceCompiler.compileChecked program seeds options = .ok facadeCompiled
  recipe : SourceCoreIndexedSession.Recipe
  issued : CoreLowering.RecursiveNamedPreparedStageContracts.PublicRecipe facadeCompiled recipe
  sameProgram : recipe.compiled.sourceProgram = program
  recipePrepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe

def compiledFixture : IO CompiledFixture := do
  let checked ← checkedFixture
  let seeds := [SourceCompiler.Seed.declaration checked.identitySignature.id,
    SourceCompiler.Seed.declaration checked.makeSignature.id, SourceCompiler.Seed.declaration checked.relaySignature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 100}
  match generated : SourceCoreCompiler.compileChecked checked.program seeds options with
  | .error error => throw (IO.userError (reprStr error))
  | .ok source =>
    match selected : source.artifact? with
    | none => throw (IO.userError "factory cached artifact missing")
    | some cached =>
      match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
      | .error error => throw (IO.userError (reprStr error))
      | .ok recipe =>
        match facade : SourceCoreExecution.prepare source with
        | .error error => throw (IO.userError (reprStr error))
        | .ok facadeCompiled =>
          have accepted : SourceCompiler.compileChecked checked.program seeds options = .ok facadeCompiled := by
            simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError,
              bind, Except.bind] using facade
          have sameProgram : recipe.compiled.sourceProgram = checked.program :=
            (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
              ((source.artifact_fields selected).1.trans (SourceCoreCompiler.compileChecked_program generated))
          return {
            toCheckedFixture := checked
            seeds := seeds
            options := options
            facadeCompiled := facadeCompiled
            accepted := accepted
            recipe := recipe
            issued := CoreLowering.RecursiveNamedPreparedStageContracts.public_preparation selected prepared facade
            sameProgram := sameProgram
            recipePrepared := by rw [SourceCoreIndexedSession.Recipe.prepare_compiled prepared]; exact prepared }

theorem CompiledFixture.prepared (fixture : CompiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ fixture.recipe.compiled.validationPlan.specializations) :
    Nonempty (CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row) :=
  CoreLowering.RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.issued member

theorem CompiledFixture.source_wellFormed (fixture : CompiledFixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  rw [fixture.sameProgram]
  exact fixture.wellFormed

structure ActualHeader (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) where
  prepared : CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row
  header : CoreLowering.CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
    (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  aligned : CoreLowering.RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
    (CoreLowering.CallableNamedMetadata.instantiation row) header
  diagnostic : CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared



open CoreLowering

theorem ActualHeader.terminal {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) (expression : ExpressionId) (statement : StatementNode)
    (roots : row.function.typedBody.roots = [.statement statement.id])
    (found : row.function.typedBody.lookupStatement? statement.id = some statement)
    (form : statement.form = .returnStmt (some expression)) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared ∧
      terminal.expression = expression ∧ terminal.certificate =
        CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
          (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          terminal.expression terminal.receipt.child := by
  have source : actual.header.function.source = row.function.typedBody := by
    rw [actual.aligned.function]
    exact congrArg (fun specialized => specialized.function.typedBody) actual.prepared.same
  have body : actual.header.function.body = [statement.id] := by
    rw [actual.aligned.function]
    change actual.prepared.compilation.statements = [statement.id]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, roots] at accepted
    exact (Except.ok.inj accepted).symm
  have terminalShape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      actual.header.function.source expression actual.header.function.body := by
    rw [source, body]
    exact .returning [] found form
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rw [actual.aligned.policy]; rfl) terminalShape actual.aligned.accepted
  let terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header := {
    row := row
    prepared := actual.prepared
    instantiation := CallableNamedMetadata.instantiation row
    aligned := actual.aligned
    layouts := actual.aligned.layouts
    expression := expression
    receipt := receipt
    certificate := CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression receipt.child
    certifies := by
      intro child generated
      have same : child = receipt.child := Except.ok.inj (generated.symm.trans receipt.generated)
      exact ⟨rfl, rfl, same⟩ }
  exact ⟨terminal, actual.diagnostic, rfl, rfl⟩



/-- Each observation refers to an actual compiler row, unique physical slot,
entry, and original source declaration. No semantic body certificate is supplied. -/
structure ObservedRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = signature.id
  parameters : row.parameterSubstitution = []
  assumptions : row.assumptions = []
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = row.key
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  entryKey : entry.key = row.key

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observed (key = row.key) "reuse exact key"
    return ⟨by rw [accepted, same]⟩

def observeRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) :
    IO (ObservedRow fixture signature) := do
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "reuse specialization missing")
  | some row =>
    let ⟨sourceOwner⟩ ← observed (row.function.typedBody.owner = signature.id) "reuse source owner"
    let ⟨parameters⟩ ← observed (row.parameterSubstitution = []) "reuse substitution"
    let ⟨assumptions⟩ ← observed (row.assumptions = []) "direct row assumptions"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "reuse return marker"
    let ⟨ordinaryInputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "reuse parameter markers"
    let ⟨target⟩ ← observeTarget fixture row
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = row.key) "reuse global key"
      match entryFound : fixture.recipe.compiled.indexed.entries.find? (fun entry => decide (entry.key = row.key)) with
      | none => throw (IO.userError "reuse entry missing")
      | some entry =>
        let ⟨entryKey⟩ ← observed (entry.key = row.key) "reuse entry key"
        return {
          row := row
          member := List.mem_of_find?_eq_some found
          sourceOwner := sourceOwner
          parameters := parameters
          assumptions := assumptions
          ordinary := ordinary
          inputsOrdinary := by
            intro binder member
            have selected := List.all_eq_true.mp ordinaryInputs binder member
            cases same : binder.comptime <;> simp_all
          target := target
          global := global
          index := index
          slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
          globalKey := globalKey
          entry := entry
          entryMember := List.mem_of_find?_eq_some entryFound
          entryKey := entryKey }
    | _ => throw (IO.userError "reuse unique global slot")

structure ObservedProgram (fixture : CompiledFixture) where
  identityRow : ObservedRow fixture fixture.identitySignature
  makeRow : ObservedRow fixture fixture.makeSignature
  relayRow : ObservedRow fixture fixture.relaySignature
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 3
  identityMake : identityRow.index ≠ makeRow.index
  identityRelay : identityRow.index ≠ relayRow.index
  makeRelay : makeRow.index ≠ relayRow.index
  identityShape : IdentityShape identityRow.row.function fixture.identitySignature
  makeShape : FactoryShape makeRow.row.function fixture.makeSignature
  relayShape : RelayShape relayRow.row.function fixture.relaySignature fixture.identitySignature fixture.makeSignature
  identityNodes : identityRow.row.function.typedBody.nodes = identityShape.nodeList
  makeNodes : makeRow.row.function.typedBody.nodes = [.expression makeShape.read,
    .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]
  relayNodes : relayRow.row.function.typedBody.nodes = relayShape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let identityRow ← observeRow fixture fixture.identitySignature
  let makeRow ← observeRow fixture fixture.makeSignature
  let relayRow ← observeRow fixture fixture.relaySignature
  let identityShape ← Tests.SourceCoreOperatorCalls.observeIdentity identityRow.row.function fixture.identitySignature
  let makeShape ← shape makeRow.row.function fixture.makeSignature
  let relayShape ← relayShape relayRow.row.function fixture.relaySignature fixture.identitySignature fixture.makeSignature
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 3) "direct compiled globalsLength"
  let ⟨identityMake⟩ ← observed (identityRow.index ≠ makeRow.index) "direct compiled identityMake"
  let ⟨identityRelay⟩ ← observed (identityRow.index ≠ relayRow.index) "direct compiled identityRelay"
  let ⟨makeRelay⟩ ← observed (makeRow.index ≠ relayRow.index) "direct compiled makeRelay"
  let ⟨identityNodes⟩ ← observed (identityRow.row.function.typedBody.nodes = identityShape.nodeList) "direct compiled identityNodes"
  let ⟨makeNodes⟩ ← observed (makeRow.row.function.typedBody.nodes = [.expression makeShape.read, .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]) "direct compiled makeNodes"
  let ⟨relayNodes⟩ ← observed (relayRow.row.function.typedBody.nodes = relayShape.nodeList) "direct compiled relayNodes"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "direct compiled noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "direct compiled profile"
  return {identityRow, makeRow, relayRow, identityShape, makeShape, relayShape, globalsLength, identityMake, identityRelay, makeRelay, identityNodes, makeNodes, relayNodes, noLocals, profile}

/-- The actual unique global slot identifies the complete prepared signature
and index, without choosing a new prepared row. -/
theorem ObservedRow.prepared_slot {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled observed.row) :
    prepared.named.signature = observed.global ∧ prepared.index = observed.index := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = observed.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
    simp only [observed.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared,
      decide_true]
  rw [observed.slot] at member
  exact Prod.mk.inj (List.mem_singleton.mp member)

/-- Issue exactly one authentic Header with its matching diagnostic receipt. -/
theorem ObservedRow.issue {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row,
        actual.header = packet.header ∧ actual.header.slot = observed.index ∧
        actual.header.named.signature = observed.global := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  obtain ⟨signatureEq, indexEq⟩ := observed.prepared_slot prepared
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := observed.inputsOrdinary
    target := by
      rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
      exact observed.target
    slot := by rw [signatureEq, indexEq]; exact observed.slot }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl, actual.aligned.slot.trans indexEq,
    (congrArg (·.signature) actual.aligned.named).trans signatureEq⟩

/-- All three real issuer packets cover every physical global slot. -/
theorem ObservedProgram.inventory {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∃ (identityInput makeInput relayInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      identityInput.row = observed.identityRow.row ∧ makeInput.row = observed.makeRow.row ∧ relayInput.row = observed.relayRow.row ∧
      ∃ (identityPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued identityInput)
        (makePacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued makeInput)
        (relayPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued relayInput),
      ∃ (identityHeader : ActualHeader fixture observed.identityRow.row)
        (makeHeader : ActualHeader fixture observed.makeRow.row)
        (relayHeader : ActualHeader fixture observed.relayRow.row),
        identityHeader.header = identityPacket.header ∧ makeHeader.header = makePacket.header ∧ relayHeader.header = relayPacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers
            (.cons identityPacket (.cons makePacket (.cons relayPacket .nil)))) := by
  obtain ⟨identityInput, identityRow, identityPacket, identityHeader, identityEq, identitySlot, identitySignature⟩ := observed.identityRow.issue
  obtain ⟨makeInput, makeRow, makePacket, makeHeader, makeEq, makeSlot, makeSignature⟩ := observed.makeRow.issue
  obtain ⟨relayInput, relayRow, relayPacket, relayHeader, relayEq, relaySlot, relaySignature⟩ := observed.relayRow.issue
  refine ⟨identityInput, makeInput, relayInput, identityRow, makeRow, relayRow,
    identityPacket, makePacket, relayPacket, identityHeader, makeHeader, relayHeader,
    identityEq, makeEq, relayEq, ?_⟩
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have relayBound := (List.getElem?_eq_some_iff.mp observed.relayRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound relayBound
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index ∨ index = observed.relayRow.index := by
    have im := observed.identityMake
    have ir := observed.identityRelay
    have mr := observed.makeRelay
    omega
  rcases casesIndex with same | same | same
  · refine ⟨identityHeader.header, ?_, identitySlot.trans same.symm, ?_⟩
    · rw [identityEq]; exact .head _
    · rw [same, observed.identityRow.slot.selected] at found
      exact identitySignature.trans (Option.some.inj found)
  · refine ⟨makeHeader.header, ?_, makeSlot.trans same.symm, ?_⟩
    · rw [makeEq]; exact .tail _ (.head _)
    · rw [same, observed.makeRow.slot.selected] at found
      exact makeSignature.trans (Option.some.inj found)
  · refine ⟨relayHeader.header, ?_, relaySlot.trans same.symm, ?_⟩
    · rw [relayEq]; exact .tail _ (.tail _ (.head _))
    · rw [same, observed.relayRow.slot.selected] at found
      exact relaySignature.trans (Option.some.inj found)

structure ObservedStages (fixture : CompiledFixture)
    {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
          (.named observed.row.key) with
      | .error error => throw (IO.userError (reprStr error))
      | .ok descriptor => return ⟨descriptor, native, present, sidecar, issued⟩

def ObservedStages.registry {fixture : CompiledFixture} {signature : ProgramFunctionSignature} {observed : ObservedRow fixture signature}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {signature : ProgramFunctionSignature} {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem bootstrap_zero (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled)) :
    owner.key.capturePrefix = 0 := by
  have bound := owner.position.isLt
  change owner.position.val < 1 at bound
  have zero : owner.position.val = 0 := by omega
  simp only [CallableIndexedOwnedFunctionValues.OwnedKey.key,
    CallableIndexedOwnedPreparedBootstrapRootState.keys,
    CallableIndexedOwnedPreparedBootstrapRootState.key, zero, List.getElem_cons_zero]

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

def seed : Core.Word := Core.Word.ofNatModulo 10

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its exported handle is not manufactured. -/
structure ObservedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed] runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observePublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "factory bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [.word seed] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed _ _) => throw (IO.userError "factory public run failed")
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "factory public run exhausted")
      | .ok (.succeeded completion) =>
        match returned : completion.value with
        | .function handle =>
          return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
            checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
        | _ => throw (IO.userError "factory output was not a function handle")


theorem ObservedProgram.identity_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.identityRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.identityNodes, Tests.SourceCoreOperatorCalls.IdentityShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · cases same; rw [observed.identityShape.read.form] at form; cases form
  · cases same

theorem ObservedProgram.relay_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.relayRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.relayNodes, RelayShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same | same | same | same | same
  all_goals try cases same
  · rw [observed.relayShape.read.form] at form; cases form
  · rw [observed.relayShape.inner.calleeForm] at form; cases form
  · rw [observed.relayShape.inner.form] at form; cases form
  · rw [observed.relayShape.zero.form] at form; cases form
  · rw [observed.relayShape.converted.calleeForm] at form; cases form
  · rw [observed.relayShape.converted.form] at form; cases form
  · rw [observed.relayShape.sumForm] at form; cases form
  · rw [observed.relayShape.outer.calleeForm] at form; cases form
  · rw [observed.relayShape.outer.form] at form; cases form

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

/-- Any later actual public startup on this compiled artifact recovers its
same recipe, exact indexed session, checkpoint, input encoding and store. -/
theorem CompiledFixture.actual_start (fixture : CompiledFixture)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (opened : publicArtifact.CompiledAt fixture.facadeCompiled)
    (started : publicSession.start key arguments fuel = .ok publicCheckpoint) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      publicArtifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      publicSession.IndexedAt session ∧ publicCheckpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session key arguments fuel
        checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      atArtifact, prepared, _program, sessionAt, checkpointAt, startReceipt⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted opened started
  have same := recipe_unique atArtifact.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    atArtifact, prepared, sessionAt, checkpointAt, startReceipt⟩

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsIdentitySupport
/-! The actual identity row is a compiler-produced read body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreBuiltinCalls
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem identity_expression {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.identityRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.identityShape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.identityNodes] at present
  simpa only [Tests.SourceCoreOperatorCalls.IdentityShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.identity_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rw [identity_expression observed found]
    exact observed.identityShape.read.requirements
  · intro id _ node found
    rw [actual.source] at found
    rw [identity_expression observed found]
    exact observed.identityShape.read.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rw [identity_expression observed found, observed.identityShape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.identity_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source observed.identityShape.read.node.id := by
  rw [actual.source]
  exact .leaf (.read observed.identityShape.read.found observed.identityShape.read.form)

/-- All finite metadata, original typing and selected scope premises of the
compiler producer are derived from this concrete checked/compiled fixture. -/
theorem ActualHeader.identity_support_at {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.identityShape.read.node.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (ActualHeader.identity_metadata observed actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.identity_syntax observed actual) stagePrepared point

/-- The actual terminal lowering supplies its own Point certificate and
preparation packet before the concrete support producer is invoked. -/
theorem ActualHeader.identity_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.identityShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.identityShape.read.node.id
    observed.identityShape.statement observed.identityShape.roots observed.identityShape.statementFound observed.identityShape.statementForm
  exact ⟨terminal, expression, ActualHeader.identity_support_at observed actual terminal diagnostic expression point receiver stagePrepared⟩

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsMakeSupport
/-! Concrete make support and the complete closure family for the three-function
checked program. The actual compiler observations produce every body premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ObservedMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  owned : observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    observed.makeRow.row.function.typedBody observed.makeShape.expression.id = .ok (observed.makeShape.expression, reported)
  binderScheme : observed.makeShape.binder.scheme = .mono .word

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) := do
  if accepted : proposition then return ⟨accepted⟩
  else throw (IO.userError label)

def observeMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) : IO (ObservedMake fixture observed) := do
  let ⟨owned⟩ ← confirm (observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner) "reuse lambda owner"
  let ⟨binderScheme⟩ ← confirm (observed.makeShape.binder.scheme = .mono .word) "reuse seed type"
  match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      observed.makeRow.row.function.typedBody observed.makeShape.expression.id with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (node, reported) =>
    let ⟨same⟩ ← confirm (node = observed.makeShape.expression) "reuse exact lambda read"
    return ⟨owned, reported, by simpa only [same] using read, binderScheme⟩

theorem ActualHeader.make_formation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context
      actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedReturnLambdaFormation.of_terminal terminal
    fixture.recipePrepared diagnostic fixture.source_wellFormed observed.profile (stages.selected actual)
    observed.makeRow.entryMember
    (node := observed.makeShape.expression) (reported := extra.reported)
  · rw [actual.source, expression]; exact observed.makeShape.expressionFound
  · exact observed.makeShape.lambda
  · rw [actual.source, expression]; exact extra.owned
  · exact observed.makeShape.requirements
  · exact observed.makeShape.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact extra.read
  · rw [actual.source]; exact observed.makeShape.innerReturnFound
  · exact observed.makeShape.innerReturnForm
  · exact observed.makeShape.innerReturnType

theorem ActualHeader.make_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) headers)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.make_formation extra stages terminal diagnostic expression
  exact ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual headers
    (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point complete
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.identityRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.relayRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 3 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have relayBound := (List.getElem?_eq_some_iff.mp observed.relayRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound relayBound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index ∨ index = observed.relayRow.index := by
    have im := observed.identityMake
    have ir := observed.identityRelay
    have mr := observed.makeRelay
    omega
  rcases casesIndex with same | same | same
  · left
    have actualIndex := (observed.identityRow.prepared_slot identityHeader.prepared).2
    rw [same, ← actualIndex, identityHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) identityHeader.prepared.same
  · right; left
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) makeHeader.prepared.same
  · right; right
    have actualIndex := (observed.relayRow.prepared_slot relayHeader.prepared).2
    rw [same, ← actualIndex, relayHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) relayHeader.prepared.same

theorem ObservedProgram.make_lambda_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = .word ∧ body = [observed.makeShape.innerReturn.id] := by
  have member := (lookupExpression?_sound found).1
  rw [observed.makeNodes] at member
  rcases List.mem_cons.mp member with same | rest
  · have nodeEq := Node.expression.inj same
    rw [nodeEq, observed.makeShape.readForm] at form
    cases form
  · rcases List.mem_cons.mp rest with impossible | rest
    · cases impossible
    · rcases List.mem_cons.mp rest with same | rest
      · have nodeEq := Node.expression.inj same
        rw [nodeEq, observed.makeShape.lambda] at form
        obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
        exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩
      · rcases List.mem_cons.mp rest with impossible | empty
        · cases impossible
        · cases empty

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.sequence
    have sameSource : function.source = observed.makeRow.row.function.typedBody := by
      rcases observed.cached_source identityHeader makeHeader relayHeader support.caller.selected with original | original | original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.identity_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
      · exact support.source.trans original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.relay_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
    have found := code.sourceFound
    rw [sameSource] at found
    have bodyShape := (observed.make_lambda_shape found code.sourceForm).2.2
    exact CallableIndexedOwnedPreparedStagedSingleReadSequence.sequence stagePrepared code support provenance
      receiver fixture.source_wellFormed
      (by rw [sameSource]; exact observed.makeNodes) observed.makeShape.lambda bodyShape
      (by rw [sameSource]; exact observed.makeShape.innerReturnFound) observed.makeShape.innerReturnForm
      (by rw [sameSource]; exact observed.makeShape.readFound) observed.makeShape.readForm
      observed.makeShape.readRequirements observed.makeShape.readCoercions observed.noLocals
      fixture.makeSignature (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _))
      (by rw [sameSource]; exact observed.makeRow.sourceOwner)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)


theorem ActualHeader.make_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.makeShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    extra.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

def ActualHeader.descriptor {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsReadSupport
/-! Finite original Source facts for nested named calls and a real builtin sibling. The
synthetic callee references carry static catalog metadata; only the original
ordered argument expressions are evaluated recursively. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreBuiltinCalls
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private theorem relay_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.relayRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.relayShape.read.node ∨
    node = observed.relayShape.inner.callee.node ∨
    node = observed.relayShape.inner.value.node ∨
    node = observed.relayShape.zero.node ∨
    node = observed.relayShape.converted.callee.node ∨
    node = observed.relayShape.converted.value.node ∨
    node = observed.relayShape.sum.node ∨
    node = observed.relayShape.outer.callee.node ∨
    node = observed.relayShape.outer.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.relayNodes] at present
  simpa only [RelayShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.relay_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayRow.row)
    (named : CallableIndexedNamedGeneration.Named)
    (same : named.specialized = observed.relayRow.row) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rcases relay_expressions observed found with same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact .inl observed.relayShape.read.requirements
    · exact .inl observed.relayShape.inner.callee.requirements
    · exact .inl observed.relayShape.inner.value.requirements
    · exact .inr ⟨_, _, observed.relayShape.zero.form⟩
    · exact .inl observed.relayShape.converted.callee.requirements
    · exact .inl observed.relayShape.converted.value.requirements
    · exact .inl observed.relayShape.sum.requirements
    · exact .inl observed.relayShape.outer.callee.requirements
    · exact .inl observed.relayShape.outer.value.requirements
  · intro id _ node found
    rw [actual.source] at found
    rcases relay_expressions observed found with same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.relayShape.read.coercions
    · exact observed.relayShape.inner.callee.coercions
    · exact observed.relayShape.inner.value.coercions
    · exact (SourceCoreElaboration.validateNativeIntegerLiteral_sound observed.relayShape.zero.accepted).coercions
    · exact observed.relayShape.converted.callee.coercions
    · exact observed.relayShape.converted.value.coercions
    · exact observed.relayShape.sum.coercions
    · exact observed.relayShape.outer.callee.coercions
    · exact observed.relayShape.outer.value.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rcases relay_expressions observed found with same | same | same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.relayShape.read.form] at form
      cases form
    · rw [observed.relayShape.inner.calleeForm] at form
      cases form
    · rw [observed.relayShape.inner.form] at form
      cases form
    · rw [observed.relayShape.zero.form] at form
      cases form
    · rw [observed.relayShape.converted.calleeForm] at form
      cases form
    · rw [observed.relayShape.converted.form] at form
      cases form
    · rw [observed.relayShape.sumForm] at form
      cases form
    · rw [observed.relayShape.outer.calleeForm] at form
      cases form
    · rw [observed.relayShape.outer.form] at form
      cases form
  · intro _ _ _ _ _ _ _ _
    rw [same]
    exact observed.relayRow.assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.relay_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayRow.row) :
    GeneralSyntax actual.header.function.source observed.relayShape.outer.value.node.id := by
  rw [actual.source]
  refine .direct observed.relayShape.outer.value.found observed.relayShape.outer.form ?_ ?_
  · rw [observed.relayShape.outer.exact]
    exact ⟨rfl, rfl⟩
  · intro child member
    cases List.mem_singleton.mp member
    refine .binary observed.relayShape.sum.found observed.relayShape.sumForm ?_ ?_
    · refine .direct observed.relayShape.inner.value.found observed.relayShape.inner.form ?_ ?_
      · rw [observed.relayShape.inner.exact]
        exact ⟨rfl, rfl⟩
      · intro child member
        cases List.mem_singleton.mp member
        exact .leaf (.read observed.relayShape.read.found observed.relayShape.read.form)
    · refine .builtin observed.relayShape.converted.value.found observed.relayShape.converted.form ?_
      intro child member
      cases List.mem_singleton.mp member
      exact .leaf (.literal observed.relayShape.zero.found (observed.relayShape.zero.form ▸ .integer _ _))

/-- The same authentic finite inventory supplies every reached direct-call
port. No called-body law or current globals value is a static premise. -/
theorem ActualHeader.relay_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.relayShape.outer.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.relayShape.outer.value.node.id
    observed.relayShape.statement observed.relayShape.roots observed.relayShape.statementFound observed.relayShape.statementForm
  have same : terminal.prepared.named.specialized = observed.relayRow.row :=
    (congrArg (·.specialized) (terminal.aligned.named.symm.trans actual.aligned.named)).trans actual.prepared.same
  exact ⟨terminal, expression, CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport.of_actual_native
    terminal diagnostic receiver fixture.source_wellFormed (actual.relay_metadata observed terminal.prepared.named same)
    (by rw [expression]; exact actual.relay_syntax observed) rows complete
    (bootstrap_zero fixture.recipe.compiled) stagePrepared point⟩

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsRuntime
/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20
def interveningSeed : Core.Word := Core.Word.ofNatModulo 30

structure ObservedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))

def observeCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedCall session key arguments) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "captured reuse public call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "captured reuse public call exhausted")
    | .ok (.succeeded completion) =>
      return ⟨checkpoint, started, completion, result ▸ executed.property⟩

structure ObservedFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) extends ObservedCall session key arguments where
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedFunctionCall session key arguments) := do
  let call ← observeCall session key arguments
  match returned : call.completion.value with
  | .function handle => return ⟨call, handle, returned⟩
  | _ => throw (IO.userError "captured reuse expected a function export")

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle argument runOptions (.ok (.succeeded completion))

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) : IO (ObservedInvocation session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle argument runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "direct issued call failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "direct issued call exhausted")
  | .ok (.succeeded completion) => pure ⟨completion, result ▸ executed.property⟩


structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.relayRow
  second : ObservedFunctionCall first.completion.session observed.relayRow.row.key [.word secondSeed]
  distinct : first.handle ≠ second.handle
  firstRead : ObservedInvocation second.completion.session first.handle .unit
  firstValue : firstRead.completion.value = .word seed
  intervening : ObservedFunctionCall firstRead.completion.session observed.relayRow.row.key [.word interveningSeed]
  secondRead : ObservedInvocation intervening.completion.session second.handle .unit
  secondValue : secondRead.completion.value = .word secondSeed
  repeatedRead : ObservedInvocation secondRead.completion.session first.handle .unit
  repeatedValue : repeatedRead.completion.value = .word seed

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.relayRow
  let second ← observeFunctionCall first.completion.session observed.relayRow.row.key [.word secondSeed]
  if distinct : first.handle ≠ second.handle then
    let firstRead ← observeInvocation second.completion.session first.handle .unit
    if firstValue : firstRead.completion.value = .word seed then
      let intervening ← observeFunctionCall firstRead.completion.session observed.relayRow.row.key [.word interveningSeed]
      let secondRead ← observeInvocation intervening.completion.session second.handle .unit
      if secondValue : secondRead.completion.value = .word secondSeed then
        let repeatedRead ← observeInvocation secondRead.completion.session first.handle .unit
        if repeatedValue : repeatedRead.completion.value = .word seed then
          return {first, second, distinct, firstRead, firstValue, intervening, secondRead, secondValue, repeatedRead, repeatedValue}
        else throw (IO.userError "direct relay first capture changed after later calls")
      else throw (IO.userError "direct relay second capture not20")
    else throw (IO.userError "direct relay first capture not10")
  else throw (IO.userError "direct relay lost distinct captures")

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ActualHeader.key {fixture : CompiledFixture}
    {row : SourceSpecialization.SpecializedFunction} (actual : ActualHeader fixture row) :
    actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

theorem ObservedRow.keys_ne {fixture : CompiledFixture} {leftSignature rightSignature : ProgramFunctionSignature}
    (left : ObservedRow fixture leftSignature) (right : ObservedRow fixture rightSignature)
    (distinct : left.index ≠ right.index) : left.row.key ≠ right.row.key := by
  intro same
  have globals : left.global.key = right.global.key := left.globalKey.trans (same.trans right.globalKey.symm)
  exact distinct (left.slot.unique right.slot globals).2

private theorem selected_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {root : SourceCoreIndexedSession.Root compiled}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (selected : RootSelection (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers root header) :
    header.named.signature.key = root.key := by
  obtain ⟨_, entry, _, shape, found⟩ := selected
  obtain ⟨named, index, first, namedKey, rootKey, _⟩ := shape
  obtain ⟨namedEq, _⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans first))
  rw [namedEq]
  exact namedKey.trans rootKey.symm

theorem selected_relay_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [identityHeader.header, makeHeader.header, relayHeader.header] root header)
    (key : root.key = observed.relayRow.row.key) : header = relayHeader.header := by
  have headerKey := (selected_key selected).trans key
  rcases List.mem_cons.mp selected.member with same | rest
  · rw [same, identityHeader.key] at headerKey
    exact False.elim (observed.identityRow.keys_ne observed.relayRow observed.identityRelay headerKey)
  · rcases List.mem_cons.mp rest with same | rest
    · rw [same, makeHeader.key] at headerKey
      exact False.elim (observed.makeRow.keys_ne observed.relayRow observed.makeRelay headerKey)
    · exact List.mem_singleton.mp rest

private theorem cast_key {left right : SourceCoreUnifiedCompilation.Compiled}
    (same : left = right) (root : SourceCoreIndexedSession.Root left) :
    (same ▸ root).key = root.key := by
  cases same
  rfl

private theorem started_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {recipe : SourceCoreIndexedSession.Recipe}
    {prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe}
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    (request : Started headers prepared publicCheckpoint session key arguments fuel world store) :
    request.root.key = key := by
  have keyEq := of_decide_eq_true (List.find?_some
    (p := fun root : SourceCoreIndexedSession.Root recipe.compiled => decide (root.key = key))
    request.started.selected)
  exact (cast_key (SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm request.root).symm.trans keyEq

theorem selected_relay_at {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [identityHeader.header, makeHeader.header, relayHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.relayRow.row.key arguments fuel world store) : request.header = relayHeader.header := by
  subst headers
  exact selected_relay_root identityHeader makeHeader relayHeader request.selected (started_key request)

theorem ObservedRow.source_types {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (signatureMember : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions)
    (actual : ActualHeader fixture observed.row) :
    observed.row.function.typedBody.inputs.map (fun binder => binder.scheme.body) = signature.parameterTypes ∧
      observed.row.function.inferredBodyType = TypeSystem.Ty.productMany signature.returnTypes := by
  obtain ⟨request, original, generic, originalMember, genericMember, _, accepted⟩ := actual.prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have body := RecursiveNamedSpecializationBodyFacts.body accepted
  have owner := congrArg (fun source => source.owner) body
  change observed.row.function.typedBody.owner = generic.typedBody.owner at owner
  have originalEq : original = signature :=
    eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids originalMember signatureMember
      (identities.1.trans (identities.2.1.symm.trans (owner.symm.trans observed.sourceOwner)))
  subst original
  have valid := fixture.source_wellFormed.functions_valid (FunctionDefinition.ofChecked generic)
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩)
  cases valid with
  | @intro typedSignature facts typedMember typedOwner bodyValid =>
    have same : typedSignature = signature :=
      eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids typedMember signatureMember
        (typedOwner.symm.trans identities.1.symm)
    subst typedSignature
    cases bodyValid with
    | intro _ _ _ _ _ result _ _ _ extended _ _ _ _ _ _ =>
      have inputs := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      have fields := (CallableCoercionBodyProvenance.specialization_fields accepted).1
      rw [fields, observed.parameters]
      simp only [SourceSpecialization.applyCheckedFunction, SourceSpecialization.applyTypedSource,
        List.map_map, Function.comp_def, SourceSpecialization.applyBinder,
        SourceSpecialization.applyScheme, parameter_nil]
      exact ⟨inputs, result⟩

theorem ActualHeader.identity_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.identityRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).1
  rw [observed.identityShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.identity_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.identity_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.identity_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.function.resultType = .word := by
  have result := (observed.identityRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.identityShape.returns]
  rfl

theorem ActualHeader.make_input_types_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).1
  rw [observed.makeShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.make_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.make_input_types_source
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.make_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.function.resultType = closureType := by
  have result := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.makeShape.returns]
  rfl

theorem ActualHeader.relay_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.relayRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _))) actual).1
  rw [observed.relayShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.relay_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.relay_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.relay_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) : actual.header.function.resultType = closureType := by
  have result := (observed.relayRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _))) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.relayShape.returns]
  rfl

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsSupports
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedNamedBodySupport (Support)

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  identityInput : Input fixture.recipe.compiled
  makeInput : Input fixture.recipe.compiled
  relayInput : Input fixture.recipe.compiled
  identityRow : identityInput.row = observed.identityRow.row
  makeRow : makeInput.row = observed.makeRow.row
  relayRow : relayInput.row = observed.relayRow.row
  identityPacket : Issued identityInput
  makePacket : Issued makeInput
  relayPacket : Issued relayInput
  identityHeader : ActualHeader fixture observed.identityRow.row
  makeHeader : ActualHeader fixture observed.makeRow.row
  relayHeader : ActualHeader fixture observed.relayRow.row
  identityEq : identityHeader.header = identityPacket.header
  makeEq : makeHeader.header = makePacket.header
  relayEq : relayHeader.header = relayPacket.header
  rows : Inventory [identityInput, makeInput, relayInput]
  rowsEq : rows = .cons identityPacket (.cons makePacket (.cons relayPacket .nil))
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([identityInput, makeInput, relayInput].map (fun input => input.prepared.index)).Nodup
  terminals : ∀ header, header ∈ headers rows → Terminal header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  identityDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named identityHeader.header.named.signature.key)
  makeDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named makeHeader.header.named.signature.key)
  relayDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named relayHeader.header.named.signature.key)

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    headers support.rows = [support.identityHeader.header, support.makeHeader.header, support.relayHeader.header] := by
  rw [support.rowsEq]
  simp only [headers, support.identityEq, support.makeEq, support.relayEq]

private def selectThree {compiled : SourceCoreUnifiedCompilation.Compiled}
    {first second third : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (firstSecond : first.slot ≠ second.slot) (firstThird : first.slot ≠ third.slot)
    (secondThird : second.slot ≠ third.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (firstValue : property first) (secondValue : property second) (thirdValue : property third) :
    ∀ header, header ∈ [first, second, third] → property header := by
  intro header member
  if firstSlot : header.slot = first.slot then
    have same : header = first := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · exact same
      · have other := congrArg (·.slot) same
        exact False.elim (firstSecond (firstSlot.symm.trans other))
      · have other := congrArg (·.slot) same
        exact False.elim (firstThird (firstSlot.symm.trans other))
    exact same.symm ▸ firstValue
  else if secondSlot : header.slot = second.slot then
    have same : header = second := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · exact False.elim (firstSlot (congrArg (·.slot) same))
      · exact same
      · have other := congrArg (·.slot) same
        exact False.elim (secondThird (secondSlot.symm.trans other))
    exact same.symm ▸ secondValue
  else
    have same : header = third := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · exact False.elim (firstSlot (congrArg (·.slot) same))
      · exact False.elim (secondSlot (congrArg (·.slot) same))
      · exact same
    exact same.symm ▸ thirdValue

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨identityInput, makeInput, relayInput, identityRow, makeRow, relayRow,
    identityPacket, makePacket, relayPacket, identityHeader, makeHeader, relayHeader,
    identityEq, makeEq, relayEq, complete⟩ := observed.inventory
  let rows : Inventory [identityInput, makeInput, relayInput] :=
    .cons identityPacket (.cons makePacket (.cons relayPacket .nil))
  have headerList : headers rows = [identityHeader.header, makeHeader.header, relayHeader.header] := by
    simp only [rows, headers, identityEq, makeEq, relayEq]
  have identityIndex : identityHeader.header.slot = observed.identityRow.index :=
    identityHeader.aligned.slot.trans (observed.identityRow.prepared_slot identityHeader.prepared).2
  have identityInputIndex : identityHeader.header.slot = identityInput.prepared.index := by
    rw [identityEq]; exact identityPacket.aligned.slot
  have makeIndex : makeHeader.header.slot = observed.makeRow.index :=
    makeHeader.aligned.slot.trans (observed.makeRow.prepared_slot makeHeader.prepared).2
  have makeInputIndex : makeHeader.header.slot = makeInput.prepared.index := by
    rw [makeEq]; exact makePacket.aligned.slot
  have relayIndex : relayHeader.header.slot = observed.relayRow.index :=
    relayHeader.aligned.slot.trans (observed.relayRow.prepared_slot relayHeader.prepared).2
  have relayInputIndex : relayHeader.header.slot = relayInput.prepared.index := by
    rw [relayEq]; exact relayPacket.aligned.slot
  have identityMake : identityHeader.header.slot ≠ makeHeader.header.slot := by
    rw [identityIndex, makeIndex]
    exact observed.identityMake
  have identityMakeInput : identityInput.prepared.index ≠ makeInput.prepared.index := by
    rw [← identityInputIndex, ← makeInputIndex]
    exact identityMake
  have identityRelay : identityHeader.header.slot ≠ relayHeader.header.slot := by
    rw [identityIndex, relayIndex]
    exact observed.identityRelay
  have identityRelayInput : identityInput.prepared.index ≠ relayInput.prepared.index := by
    rw [← identityInputIndex, ← relayInputIndex]
    exact identityRelay
  have makeRelay : makeHeader.header.slot ≠ relayHeader.header.slot := by
    rw [makeIndex, relayIndex]
    exact observed.makeRelay
  have makeRelayInput : makeInput.prepared.index ≠ relayInput.prepared.index := by
    rw [← makeInputIndex, ← relayInputIndex]
    exact makeRelay
  obtain ⟨makeTerminal, makeDiagnostic, makeExpression, makePoint⟩ := makeHeader.terminal
    observed.makeShape.expression.id observed.makeShape.statement observed.makeShape.roots
    observed.makeShape.statementFound observed.makeShape.returnStatement
  obtain ⟨makeSupport⟩ := makeHeader.make_support extra makeStages (headers rows) complete
    makeTerminal makeDiagnostic makeExpression makePoint (registry := registry)
    (faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  obtain ⟨identityTerminal, _identityExpression, identitySupport⟩ :=
    identityHeader.identity_support observed receiver (actualStagePrepared fixture)
  obtain ⟨identitySupport⟩ := identitySupport
  obtain ⟨relayTerminal, _relayExpression, relaySupport⟩ :=
    relayHeader.relay_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨relaySupport⟩ := relaySupport
  let property := fun header => Σ terminal : Terminal header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectThree identityMake identityRelay makeRelay property
      ⟨identityTerminal, .recursive identitySupport⟩ ⟨makeTerminal, makeSupport⟩
      ⟨relayTerminal, .canonical relaySupport⟩ header (headerList ▸ member)
  exact ⟨{
    identityInput := identityInput
    makeInput := makeInput
    relayInput := relayInput
    identityRow := identityRow
    makeRow := makeRow
    relayRow := relayRow
    identityPacket := identityPacket
    makePacket := makePacket
    relayPacket := relayPacket
    identityHeader := identityHeader
    makeHeader := makeHeader
    relayHeader := relayHeader
    identityEq := identityEq
    makeEq := makeEq
    relayEq := relayEq
    rows := rows
    complete := complete
    rowsEq := rfl
    distinct := by simp [identityMakeInput, identityRelayInput, makeRelayInput]
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := fun association => observed.family identityHeader makeHeader relayHeader (actualStagePrepared fixture) receiver association
    identityDescriptor := identityHeader.descriptor identityStages
    makeDescriptor := makeHeader.descriptor makeStages
    relayDescriptor := relayHeader.descriptor relayStages }⟩

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsCommon
/-! Genuine initial diagnostics and current retained public sessions. No
independent native execution is used to construct the semantic receiver. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

/-- The receiver is built directly at the genuine initial metadata registry. -/
theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.relayRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩


abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers support.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiving.result.context.registry
    support.relayHeader.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.relayHeader.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsInvocation
/-! Collected closure handles use the current metadata receiver.
Each returned state retains that receiver for the following public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (arguments : List Dynamic.Value) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.relayHeader.header.function.context before source arguments outcome after

/-- Current history supplies the callee; literal input rows supply its argument.
No registry equality, arbitrary receiving table or metadata extension is assumed. -/
theorem invoke_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function parameter .word)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.relayHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value (.word word)) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
      after, finalMap, finalWorld, reached, contextAt, issued, extended, _diagnostics,
      started, _parameterView, _resultView, succeeded, actualAt, packing, trace, result,
      _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryReflection.public_invoke_succeeded
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      support.supports fixture.source_wellFormed state.history entry member entryType
      input state.atRecipe state.registry state.atSession
      (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function parameter .word := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  let next : RetainedState support call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := retained }
  exact ⟨sources, next, packing, sourceSize, by simpa only [outcomeValue] using trace⟩


/-- Successful intervening execution retains the complete old history even
when its new result is left unselected. The actual Source value is still kept. -/
theorem invoke_success {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.relayHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (source : Dynamic.Value)
      (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value source) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source, payload, after,
    finalMap, finalWorld, reached, added, contextAt, issued, extended, _diagnostics, _started, _parameterView, _resultView,
    _succeeded, actualAt, packing, trace, _resultAt, _nativeValue, selected, _handles, _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryOutputCollection.public_invoke_succeeded_collects
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      support.supports fixture.source_wellFormed state.history entry member entryType input state.atRecipe
      state.registry state.atSession (by simpa only [entryHandle] using call.executed) .skip invocation
  have addedNil : added = [] := by
    simpa only [RecursiveNamedPublicNestedOutputSelections.Selection.handles, List.map_eq_nil_iff] using _handles
  subst added
  let next : RetainedState support call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := by simpa only [List.append_nil, PublicSupports.functions] using retained }
  exact ⟨sources, source, next, packing, sourceSize, trace⟩

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsRelayStep
/-! A genuine successful public factory call extends the current retained
history with its actual new closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact} {entries : List Entry}

/-- An actual public relay call constructs Source execution and the next history.
Every older entry remains in order, followed by this call's exported handle. -/
theorem RetainedState.relay_typed_handle
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.relayRow.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .unit .word ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.relayHeader.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.makeInput, support.relayInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selected := selected_relay_at support.identityHeader support.makeHeader support.relayHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [selected, support.relayHeader.relay_input_types]
    exact .cons (.data
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩) .nil
  have registryAt : request.encodedValues.registry =
      state.receiving.result.context.registry := by
    apply request.started.simple_registry state.registry
    intro value member
    have same : value = .word word := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word word
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.relayDescriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, nativeValue, finalStore, capture,
    sourceSize, outcome, heap, mapping, world, succeeded, valueEq, typeEq, budgetEq,
    returnedAt, trace, result, caller, source, payload, sourceValue, nativePayload, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_remembers
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := state.receiving)
      (receiver := state.issued)
      (profile := observed.profile)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := state.receiving.result.extension)
      (semantic := semantic)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (invocation := invocation) (inputReceipts := inputs)
      (metadata := by rw [registryAt]; exact .refl _)
      (sourceAt := request.sourceAt)
      call.started call.executed call.returned descriptor
  let entry : Entry := ⟨request.header.function.resultType, source, call.handle, payload,
    request.header.output, runOptions.outputValidationFuel⟩
  let after : RetainedState support call.completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := mapping
    world := world
    heap := heap
    store := finalStore
    caller := caller
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := by
      have registered := request.started.returned_registry succeeded
      rw [registryAt] at registered
      exact registered
    history := continued }
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selected, support.relayHeader.relay_result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  refine ⟨entry, ?_, rfl, handleType, after, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · change request.header.function.resultType = .function .unit .word
    rw [selected]
    exact support.relayHeader.relay_result_type
  · exact selected ▸ request.sourceAt
  · simpa only [entry, after, sourceValue] using trace

/-- Preserve the original continuation API for clients that only need the
Source value and the new retained history. -/
theorem RetainedState.relay
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.relayRow.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.relayHeader.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, after, trace⟩ :=
    state.relay_typed_handle call invocation
  exact ⟨entry, sourceType, handle, after, trace⟩

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsSeed
/-! Actual initialization and the first public relay(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (relayStages : ObservedStages fixture observed.relayRow)
    (first : ObservedPublicRun fixture observed.relayRow) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      first.handle.sourceType = .function .unit .word ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.relayHeader.header
          (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ :=
    fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 100000 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply started.simple_registry (booted.registry_at initial)
    intro value member
    have same : value = .word seed := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.relayHeader.header := by
    apply selected_relay_root (fixture := fixture) (observed := observed)
      support.identityHeader support.makeHeader support.relayHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.relayRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.relayHeader.header.function.context
      (support.relayHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.relayHeader.relay_input_types]
    exact .cons (.leaf (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.relayHeader.header support.relayInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.relayPacket.header.named.specialized support.relayInput.prepared.available)) := by
    rw [support.relayEq]
    exact support.relayPacket.sourceAt
  obtain ⟨caller, returnedCompletion, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, _fullResult,
      returnedCaller, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_remembers
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture)
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
      first.started first.executed first.returned support.relayDescriptor
  let entry : Entry := ⟨support.relayHeader.header.function.resultType, source, first.handle,
    payload, support.relayHeader.header.output, runOptions.outputValidationFuel⟩
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  let state : RetainedState support first.completion.session [entry] := {
    artifact := artifact
    session := returnedCompletion.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := returnedAt
    atRecipe := started.recipe_eq
    receiving := receiver.completion
    issued := receiver.issued
    extension := .refl _
    registry := receiver.registry.symm ▸ returnedRegistry
    history := retained }
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.relayHeader.relay_result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans first.returned)
  refine ⟨entry, support.relayHeader.relay_result_type, rfl, handleType, state, ?_⟩
  exact ⟨support.relayInput.prepared.available, _, sourceSize, sourceAt, sourceValue ▸ trace⟩

/-- The original factory theorem remains available when the public handle's
raw type is not needed by the caller. -/
theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (relayStages : ObservedStages fixture observed.relayRow)
    (first : ObservedPublicRun fixture observed.relayRow) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.relayHeader.header
          (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, state, trace⟩ :=
    first_meaning_typed_handle support relayStages first
  exact ⟨entry, sourceType, handle, state, trace⟩

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsPublicExecution
/-! Three actual nested named/builtin factory calls and three later handle calls keep
all returned sessions and captured Source heaps in one ordered history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  second : Entry
  intervening : Entry
  firstType : first.sourceType = closureType
  secondType : second.sourceType = closureType
  interveningType : intervening.sourceType = closureType
  firstHandle : first.handle = sequence.first.handle
  secondHandle : second.handle = sequence.second.handle
  interveningHandle : intervening.handle = sequence.intervening.handle
  distinct : first.handle ≠ second.handle
  initial : RetainedState support sequence.first.completion.session [first]
  secondState : RetainedState support sequence.second.completion.session [first, second]
  firstReadState : RetainedState support sequence.firstRead.completion.session [first, second]
  interveningState : RetainedState support sequence.intervening.completion.session [first, second, intervening]
  secondReadState : RetainedState support sequence.secondRead.completion.session [first, second, intervening]
  finalState : RetainedState support sequence.repeatedRead.completion.session [first, second, intervening]
  firstTrace : SourceCall support support.relayHeader.header
    (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
    ⟨[]⟩ [.word seed] (.value first.source) initial.heap
  secondTrace : SourceCall support support.relayHeader.header
    (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
    initial.heap [.word secondSeed] (.value second.source) secondState.heap
  firstArguments : List Dynamic.Value
  firstPacking : Dynamic.ValuesPack firstArguments .unit
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
    secondState.heap first.source firstArguments (.value (.word seed)) firstReadState.heap
  interveningTrace : SourceCall support support.relayHeader.header
    (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
    firstReadState.heap [.word interveningSeed] (.value intervening.source) interveningState.heap
  secondArguments : List Dynamic.Value
  secondPacking : Dynamic.ValuesPack secondArguments .unit
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
    interveningState.heap second.source secondArguments (.value (.word secondSeed)) secondReadState.heap
  repeatedArguments : List Dynamic.Value
  repeatedPacking : Dynamic.ValuesPack repeatedArguments .unit
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
    secondReadState.heap first.source repeatedArguments (.value (.word seed)) finalState.heap

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness relayStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports (completion := receiver.completion)
    fixture observed extra identityStages makeStages relayStages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle support relayStages sequence.first
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    initial.relay_typed_handle sequence.second scope
  have unitInput : ∀ entries, RecursiveNamedPublicFunctionHistoryInputs.Input
      entries support.relayHeader.header.function.context .unit .unit .unit := fun _ =>
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨firstArguments, firstReadState, firstPacking, firstReadTrace⟩ := invoke_word secondState first
    (by simp) firstType firstHandle firstHandleType (unitInput _) sequence.firstRead sequence.firstValue scope
  obtain ⟨intervening, interveningType, interveningHandle, _interveningHandleType, interveningState, interveningTrace⟩ :=
    firstReadState.relay_typed_handle sequence.intervening scope
  obtain ⟨secondArguments, secondReadState, secondPacking, secondReadTrace⟩ := invoke_word interveningState second
    (by simp) secondType secondHandle secondHandleType (unitInput _) sequence.secondRead sequence.secondValue scope
  obtain ⟨repeatedArguments, finalState, repeatedPacking, repeatedReadTrace⟩ := invoke_word secondReadState first
    (by simp) firstType firstHandle firstHandleType (unitInput _) sequence.repeatedRead sequence.repeatedValue scope
  exact ⟨{
    support, first, second, intervening, firstType, secondType, interveningType,
    firstHandle, secondHandle, interveningHandle,
    distinct := by rw [firstHandle, secondHandle]; exact sequence.distinct
    initial, secondState, firstReadState, interveningState, secondReadState, finalState,
    firstTrace, secondTrace, firstArguments, firstPacking, firstReadTrace,
    interveningTrace, secondArguments, secondPacking, secondReadTrace,
    repeatedArguments, repeatedPacking, repeatedReadTrace }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness relayStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed extra identityStages makeStages relayStages sequence receiver⟩

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsInitialForward
/-! Independent nested named/builtin Source success gives execution and export bounds
at the real first checkpoint, with the exact returned heap and a usable handle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The returned public value reimports to the exact represented Source result. -/
def ReturnedValue {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} (completion : SourceCoreExecution.Completion artifact)
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support completion.session entries) (source : Dynamic.Value) (fuel : Nat) : Prop :=
  ∃ payload nativeType,
    state.session.EncodesAt fuel closureType completion.value payload ∧
    CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked state.receiving.result.context.registry
      support.functions state.mapping state.world closureType source payload nativeType

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.relayRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        ∃ handle, completion.value = .function handle ∧ handle.sourceType = closureType ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after ∧ ReturnedValue completion returned source outputFuel

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.relayRow)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.relayHeader.header invocation ⟨[]⟩ [.word seed] (.value source) after) :
    InitialForwardAt support first source after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.relayHeader.header := by
    apply selected_relay_root (fixture := fixture) (observed := observed)
      support.identityHeader support.makeHeader support.relayHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.relayRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.relayHeader.header.function.context
      (support.relayHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.relayHeader.relay_input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened)
      (fresh := first.fresh) (ready := .single first.ready) (authority := first.authority)
      (atSession := sessionAt) (atCheckpoint := checkpointAt) (started := started)
      (inputReceipts := inputs) (sourceAt := sourceAt) applied
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult, support.relayHeader.relay_result_type] at requested
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single first.ready).exportsReady first.authority
  have checkpointReady := started.original.initial_registry.exportsReady (sessionAt.exportsReady_iff.mp initialReady)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  let returned : RetainedState support completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded checkpointAt resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions _finalMap _finalWorld closureType source _payload support.relayHeader.header.output := by
    have result := _fullResult.2.1
    rw [support.relayHeader.relay_result_type] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, handle, functionValue, handleType,
    actualAt.2.2.2.exportsReady_iff.mpr ready, returned, rfl, _payload, _, encoded, represented⟩



end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinCallsForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreBuiltinCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry} {value : Core.Word}
    (call : ObservedFunctionCall session observed.relayRow.row.key [.word value])
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        ∃ handle, completion.value = .function handle ∧ handle.sourceType = closureType ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after ∧
          ReturnedValue completion returned source outputFuel

theorem forward_relay {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries) {value : Core.Word}
    (call : ObservedFunctionCall session observed.relayRow.row.key [.word value]) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.relayHeader.header invocation state.heap
      [.word value] (.value source) after) :
    ForwardAt (entries := entries) support call source after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.makeInput, support.relayInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader := selected_relay_at support.identityHeader support.makeHeader support.relayHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word value] [.word value] := by
    rw [selectedHeader, support.relayHeader.relay_input_types]
    exact .cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.relayHeader.relay_result_type] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  let returned : RetainedState support completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions finalMap finalWorld closureType source payload request.header.output := by
    have result := fullResult.2.1
    have rawType : request.header.function.resultType = closureType := by rw [selectedHeader]; exact support.relayHeader.relay_result_type
    rw [rawType] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, handle, functionValue, handleType,
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl, payload, _, encoded, represented⟩


/-- All three nested named/builtin factory executions have independent Source-to-public
bounds, at their exact original checkpoints and current captured heaps. -/
def ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {relayStages : ObservedStages fixture observed.relayRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness relayStages sequence receiver) : Prop :=
  InitialForwardAt meaning.support sequence.first meaning.first.source meaning.initial.heap ∧
  ForwardAt (entries := [meaning.first]) meaning.support sequence.second meaning.second.source meaning.secondState.heap ∧
  ForwardAt (entries := [meaning.first, meaning.second]) meaning.support sequence.intervening
    meaning.intervening.source meaning.interveningState.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {relayStages : ObservedStages fixture observed.relayRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness relayStages sequence receiver) : ForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have secondReady := sequence.second.executed.exportsReady firstReady
  have readReady := sequence.firstRead.executed.exportsReady secondReady
  exact ⟨forward_initial meaning.support sequence.first meaning.firstTrace,
    forward_relay meaning.initial sequence.second firstReady meaning.secondTrace,
    forward_relay meaning.firstReadState sequence.intervening readReady meaning.interveningTrace⟩

theorem closed_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness relayStages sequence receiver, ForwardMeaning meaning := by
  obtain ⟨receiver, meaning⟩ := closed_sequence_meaning fixture observed extra identityStages makeStages relayStages sequence
  obtain ⟨meaning⟩ := meaning
  exact ⟨receiver, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let identityStages ← observeStages fixture observed.identityRow
  let makeStages ← observeStages fixture observed.makeRow
  let relayStages ← observeStages fixture observed.relayRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_forward_meaning fixture observed extra identityStages makeStages relayStages sequence
  IO.println "Named identity/make and builtin wordFromInteger(0): relay10/relay20/A10/relay30/B20/A10, exact Source heaps and histories, all three relay public fuel bounds proved"

end Tests.SourceCoreBuiltinCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinForHeader
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
  ((∃ location, reason = .uninitializedLocation location ∧ token = Word.zero) ∨
   (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ reason = .missingMappingDefault value ∧ token = Word.zero.add tag) ∨
   (reason = .invalidAssignmentOperands .equal ∧ token = Word.zero)) ∨
  ∃ code, reason = .panic code ∧ token = Solcore.Frontend.SourceCorePanics.reason code
/-- Every panic fails with its code's reason. -/
private instance : FunctionCalls.FaultTokens faults := ⟨fun code => .inr ⟨code, rfl, rfl⟩⟩
private theorem uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id) :=
  fun _ location => .inl (.inl ⟨location, rfl, rfl⟩)
private theorem missing : ∀ id key value tag, MetadataRep values.registry (.mapping key value) tag →
  faults (.missingMappingDefault value) ((reasonAt id).add tag) :=
  fun _ key value tag owned => .inl (.inr (.inl ⟨key, value, tag, owned, rfl, rfl⟩))
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinImperativeFor
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
theorem compiled_preserves [FunctionCalls.FaultTokens faults] :
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
theorem compiled_reflects [FunctionCalls.FaultTokens faults] {value : Value} {finalStore : Store}
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinImperativeMatch
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
theorem certified : BuiltinImperativeMatch.Tree layouts specialization active frame globals onError 100 values source [] reasonAt
    definitions administrative context scope (.statements mode [site]) .unit .unit code := by
  apply GenericImperativeMatch.tree_of_typed_flow (certificates := fun current => CompatibleExpressionBuiltins.Tree 100 values source current [] reasonAt) matchPolicy matchValues matchDefinitions matchAllocator (GenericImperativeMatch.MatchChildStatic.of_hidden (matchCompilation := matchCompilation) (certificates := fun current => CompatibleExpressionBuiltins.Tree 100 values source current [] reasonAt) (definitions := definitions) (administrative := administrative) hiddenSourceFresh) matched.read binderPolicy allocationPolicy ?_ matched unaryPolicy unique ?_
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
  (errors : GenericImperativeMatch.Tree.Ready registry faults (certified nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren matchPolicy matchValues matchDefinitions matchAllocator declarations accepted nativeTyped))
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

include matchPolicy matchValues matchDefinitions matchAllocator expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped sameDefinitions layoutDefinitions registered extension catalogValid valid uninitialized missing faithful observations runtimeViews errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_preserves [FunctionCalls.FaultTokens faults] :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      TypedLexicalWhile.FlowRep (values := values) (registry := registry) functions finalMap finalWorld faults .unit .unit (.fallthrough environment) value ∧
      CompatibleHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment context after := by
  cases sameDefinitions
  exact (certified nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren matchPolicy matchValues matchDefinitions matchAllocator declarations accepted nativeTyped).preserves functions layoutDefinitions registered catalogValid extension program []
    uninitialized missing faithful observations runtimeViews errors valid unique environments heaps locals agrees typed reference read unmapped (sourceTrace mode)

include matchPolicy matchValues matchDefinitions matchAllocator expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped sameDefinitions layoutDefinitions registered extension catalogValid valid uninitialized missing faithful observations runtimeViews errors environments heaps locals agrees typed reference read unmapped in
theorem compiled_reflects [FunctionCalls.FaultTokens faults] {value : Value} {finalStore : Store}
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
  exact (certified nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren matchPolicy matchValues matchDefinitions matchAllocator declarations accepted nativeTyped).reflects functions layoutDefinitions registered catalogValid extension program []
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinImperativeMatchBody
/-! The real compiler equations feed the function-body factory and concrete
finite call consumers. Core-only fixtures cover Unit fallthrough, loop control,
match returns and retained faults under suspension and resumption. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchBody.Certificate.mk
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreBuiltinImperativeMatchBody
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open BuiltinImperativeMatchBody GeneralHeap ReadOnly CompatiblePayload CoreProof

section CompilerConsumers
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  (program : SourceSemantics.Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_preserves [FunctionCalls.FaultTokens faults]
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : BuiltinImperativeMatch.Tree layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeMatch.Tree.Ready registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  let certificate := of_extracted accepted projection generated tree
  exact certificate.preserves functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    errors environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_reflects [FunctionCalls.FaultTokens faults]
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : BuiltinImperativeMatch.Tree layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeMatch.Tree.Ready registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  let certificate := of_extracted accepted projection generated tree
  exact certificate.reflects functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    errors environments heaps locals agrees actualTyped reference read unmapped evaluated
end CompilerConsumers

/-- Escaped control uses its escaped token for every native result type. -/
theorem break_finish {type : Ty} {environment : Environment} {store : Store}
    (fellThrough escaped : Word) :
    Evaluates environment store
      (CompatibleStatements.finish type (LocalLoop.breaking type) fellThrough escaped)
      (.inLeft type (.word escaped)) store :=
  LocalControl.finish_failure type
    (LocalLoop.toControl_transfer type escaped
      (LocalLoop.breaking_evaluates type environment store))

theorem continue_finish {type : Ty} {environment : Environment} {store : Store}
    (fellThrough escaped : Word) :
    Evaluates environment store
      (CompatibleStatements.finish type (LocalLoop.continuing type) fellThrough escaped)
      (.inLeft type (.word escaped)) store :=
  LocalControl.finish_failure type
    (LocalLoop.toControl_transfer type escaped
      (LocalLoop.continuing_evaluates type environment store))

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "enum Box<T> { Box(T) }",
      "function unitComposite(seed: Word) { let cursor = seed; for (let i = 0; i < 2; i += 1) { match (i) { case 0 { continue; } default { cursor += 1; } } } while (cursor < 2) { cursor += 1; match (cursor) { case 2 { break; } default {} } } match (cursor) { case 0 {} default { let shadow = cursor; shadow; } } }",
      "function returnedComposite(seed: Word) returns (integer) { for (let i = 0; true; i += 1) { match (Box((seed, i))) { case .Box((0, x)) { return integerSub(wordToInteger(x), 3); } case .Box((x, y)) { while (integerLt(wordToInteger(y), 2)) { y += 1; } return integerAdd(wordToInteger(x), wordToInteger(y)); } } } return 99; }",
      "function failedComposite(seed: Word) returns (integer) { let seen: mapping(Bool => Word); let gap: Word; for (let i = 0; true; i += 1) { match (seed) { case 0 { seen[false] = seed + 5; return wordToInteger(gap); } default { seen[true] = seed; return integerSub(wordToInteger(gap), 1); } } } return 0; }"
    ]}] }

private def fault_resume (entry : SourceCompilerFeatureSupport.Entry)
    (arguments : List SourceCompilerFeatureSupport.Value) : IO Unit := do
  let complete ← entry.invoke arguments
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "imperative body fault unexpectedly succeeded")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome
    "imperative body fault lost its diagnostic"
  for fuel in [0, 11, 89] do
    let started ← SourceCompilerFeatureSupport.get "imperative body suspension"
      (← complete.initial.run complete.key arguments
        {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
    | .failed actual _ =>
      SourceCompilerFeatureSupport.require (actual == token)
        "resumed imperative body fault changed its token"
    | _ => throw (IO.userError "resumed imperative body fault ran its continuation")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "imperative body checker"
    (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  let unitBody ← SourceCompilerFeatureSupport.compileNamed checked "unitComposite"
  for n in [0, 3] do
    SourceCompilerFeatureSupport.require ((← unitBody.run [w n]) == .unit)
      "imperative Unit body changed fallthrough"
    for fuel in [0, 11, 89] do unitBody.checkResume [w n] .unit fuel
  let returned ← SourceCompilerFeatureSupport.compileNamed checked "returnedComposite"
  for (n, expected) in [(0, -3), (3, 5)] do
    SourceCompilerFeatureSupport.require ((← returned.run [w n]) == .integer expected)
      "imperative body return changed its value"
    for fuel in [0, 11, 89] do returned.checkResume [w n] (.integer expected) fuel
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "failedComposite"
  for n in [0, 3] do fault_resume failed [w n]
  failed.checkCells [w 0]
    [(.word, some (w 0)), (.mapping .bool .word, some (.mapping .bool .word [(.bool false, w 5)])),
      (.word, none), (.word, some (w 0)), (.word, some (w 0))]
  IO.println "builtin imperative function body: actual compiler consumers, Unit fallthrough, returned values, escaped Core control, retained fault writes and resume GREEN"
end Tests.SourceCoreBuiltinImperativeMatchBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinLexicalStatements
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual production return lowering and independent nested builtin trace are
connected by the generic statement interface. Checked source fixtures cover
initializers, discard/tail, nested lexical scopes, both branches and fault writes.
Public checkpoint tests exercise the same cached Core artifact. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreBuiltinLexicalStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly CompatibleExpressionBuiltins CallableIndexedHistory
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"builtin_lexical", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "builtin_lexical.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
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
  owner, inputs := [], roots := [.statement returned.id], nodes := [.expression literalNode, .expression toNode,
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
private theorem wordAdmitted : TypeAdmissible context .word := .word (.ofSignatures signatures)
private theorem integerAdmitted : TypeAdmissible context .integer := .integer (.ofSignatures signatures)
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
  ((∃ location, reason = .uninitializedLocation location ∧ token = Word.zero) ∨
   (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ reason = .missingMappingDefault value ∧ token = Word.zero.add tag)) ∨
  ∃ code, reason = .panic code ∧ token = Solcore.Frontend.SourceCorePanics.reason code
/-- Every panic fails with its code's reason. -/
private instance : FunctionCalls.FaultTokens faults := ⟨fun code => .inr ⟨code, rfl, rfl⟩⟩
private theorem uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id) :=
  fun _ location => .inl (.inl ⟨location, rfl, rfl⟩)
private theorem missing : ∀ id key value tag, MetadataRep values.registry (.mapping key value) tag →
  faults (.missingMappingDefault value) ((reasonAt id).add tag) :=
  fun _ key value tag owned => .inl (.inr ⟨key, value, tag, owned, rfl, rfl⟩)
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem innerTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 2) (.value (.integer 7)) ⟨[]⟩ :=
  BuiltinCalls.source_intro (checked := checked) (type := .integer) ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl
    (.apply (.cons (.intro (lookupExpression?_sound (node := literalNode) (by rfl))
      (.literal rfl (.word (numericLiteralValue?_sound (value := 7) (by rfl)))) .nil) .nil)
      (.value (.builtin (.wordToInteger (Word.ofNatModulo 7)))))
private theorem outerTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 4) (.value (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases innerTrace with
  | value evaluated =>
    exact BuiltinCalls.source_intro (checked := checked) (type := .word)
      ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl (.apply (.cons evaluated .nil) (.value (.builtin (.wordFromInteger 7))))
private theorem sourceTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 5) (.value (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases outerTrace with
  | value evaluated => exact .value (.intro (lookupExpression?_sound (node := groupNode) (by cbv)) (.group rfl evaluated) .nil)

private def statements : List StatementId := [returned.id]
private theorem statementSyntax : BuiltinLexicalStatements.Syntax source context true statements .word :=
  .returnValue (node := returned) [] (by cbv) rfl rfl (by cbv) rfl groupTyped syntaxTree
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def loopPolicy (native : SourceCoreGeneralFunctions.CallableContext)
    (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt => SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }

private theorem certified (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout} {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (loopPolicy native layouts frame globals) fuel source []
      statements .word reasonAt true Word.zero = .ok code) :
    BuiltinLexicalStatements.Tree layouts ⟨owner, []⟩ [] frame globals onError 100 values source [] reasonAt context [] true statements .word .word code := by
  apply GenericLexicalStatements.tree_of_flow rfl (by intros; rfl) rfl ?_ statementSyntax rfl rfl rfl
    (by intro actual declared index native selected; cases selected) rfl accepted
  intro current currentClosed currentResidual currentSignatures scope budget expression expressionNode lowered declarations syntaxValue found typed generated
  exact CompatibleExpressionBuiltins.tree_of_functions unique declarations currentSignatures currentClosed currentResidual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ native [] rfl
    (fun _ _ _ found => noCoercions _ _ found) syntaxValue found typed generated

private theorem statementTrace : TypedScopedStatements.Executes true program context [] source [] ⟨[]⟩
    statements context (.returned (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases sourceTrace with
  | value child =>
    exact TypedScopedStatements.terminal_intro true [] (lookupStatement?_sound (node := returned) (by cbv))
      (by intro expression; simp [returned]) (.returnValue (lookupStatement?_sound (by cbv)) rfl child) (.returned _)

/-- The real emitted return flow preserves the independent nested builtin
trace. No semantic expression or body premise is supplied. -/
theorem compiled_preserves (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout} {globals fuel : Nat} {code : Expr}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (loopPolicy native layouts frame globals) fuel source []
      statements .word reasonAt true Word.zero = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation current}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) mapping world ⟨[]⟩ store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame current))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      TypedScopedStatements.FlowRep (values := values) (registry := values.registry) (functions ambient) finalMap finalWorld faults .word .word (.returned (.word (Word.ofNatModulo 7))) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) finalMap finalWorld ⟨[]⟩ finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ ⟨[]⟩ ∧
      TypedLexicalControl.LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner context [] [] context ⟨[]⟩ :=
  BuiltinLexicalStatements.Tree.preserves (values := values) (ambient := ambient) (faults := faults)
    (functions ambient) definitions registered (.refl _) faithful (functionLeaves ambient) (functionTypes ambient) program [] uninitialized missing
    (certified native accepted) unique valid environments heaps .nil agrees typed reference read unmapped statementTrace

/-- A completed actual return flow constructs the independent source trace,
using concrete builtin reflection and the real frame/capture environment. -/
theorem compiled_reflects (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout} {globals fuel : Nat} {code : Expr}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (loopPolicy native layouts frame globals) fuel source []
      statements .word reasonAt true Word.zero = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation current value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) mapping world ⟨[]⟩ store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame current))
    (unmapped : contextLocation ∉ mapping)
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      TypedScopedStatements.Executes true program context [] source [] ⟨[]⟩ statements resultContext outcome after ∧
      TypedScopedStatements.FlowRep (values := values) (registry := values.registry) (functions ambient) finalMap finalWorld faults .word .word outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      TypedLexicalControl.LexicalResult checked ambient.definitions finalMap finalWorld administrative source.owner context [] [] resultContext after :=
  BuiltinLexicalStatements.Tree.reflects (values := values) (ambient := ambient) (faults := faults)
    (functions ambient) definitions registered (.refl _) faithful (functionLeaves ambient) (functionTypes ambient) program [] uninitialized missing
    (certified native accepted) valid environments heaps .nil agrees typed reference read unmapped completed


private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }",
    "function initialized(a: Word, b: Word) returns (integer) { let sum = integerAdd(wordToInteger(a), wordToInteger(b)); { let sum = integerSub(sum, wordToInteger(a)); sum; } return sum; }",
    "function branches(a: Word, b: Word) returns (integer) { if (integerLt(wordToInteger(a), wordToInteger(b))) { let out = integerAdd(wordToInteger(a), wordToInteger(b)); return out; } else { let out = integerSub(wordToInteger(a), wordToInteger(b)); return out; } return wordToInteger(a); }",
    "function discarded(a: Word) returns (integer) { integerEq(wordToInteger(a), wordToInteger(a)); let out = integerAdd(wordToInteger(a), wordToInteger(a)); return out; }",
    "function tail(a: Word) returns (integer) { { let hidden = wordToInteger(a); hidden; } integerAdd(wordToInteger(a), wordToInteger(a)) }",
    "function lazy(a: Word) returns (integer) { let m: mapping(Bool => Word); { let out = wordToInteger(m[integerEq(wordToInteger(a), wordToInteger(a))]); out; } return wordToInteger(a); }",
    "function failed(a: Word) returns (integer) { let m: mapping(Bool => Word); { let before = wordToInteger(m[integerEq(wordToInteger(a), wordToInteger(a))]); let gap: Word; let failed = integerAdd(before, wordToInteger(gap)); let unreachable = wordToInteger(a); } return wordToInteger(a); }",
    "function missing(a: Word) returns (integer) { let m: mapping(Bool => Box); if (integerEq(wordToInteger(a), wordToInteger(a))) { let prior = integerAdd(wordToInteger(a), wordToInteger(a)); let failed = (m[true], prior); } return wordToInteger(a); }"]}]}

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let complete ← entry.invoke arguments
  let (reason, heapSize) ← match complete.outcome with
    | .failed reason session => pure (reason, session.heapSize)
    | _ => throw (IO.userError "builtin lexical fault fixture did not fail")
  SourceCompilerFeatureSupport.require (← complete.diagnostic reason).isSome "builtin lexical fault lost its source diagnostic"
  for fuel in [0, 43] do
    let pending ← SourceCompilerFeatureSupport.get "builtin lexical suspension"
      (← complete.initial.run complete.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let checkpoint ← match pending with
      | .outOfFuel checkpoint => pure checkpoint
      | _ => throw (IO.userError "builtin lexical small budget did not suspend")
    match ← checkpoint.resume 300000 1024 with
    | .failed resumed finished =>
      SourceCompilerFeatureSupport.require (resumed == reason && finished.heapSize == heapSize)
        "builtin lexical resume changed the fault or allocated unreachable cells"
    | _ => throw (IO.userError "builtin lexical fault checkpoint changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "builtin lexical checker" (checkProgram workspace)
  let seven : SourceCoreExecution.Value := .word (Word.ofNatModulo 7)
  let nine : SourceCoreExecution.Value := .word (Word.ofNatModulo 9)
  let initialized ← SourceCompilerFeatureSupport.compileNamed checked "initialized"
  SourceCompilerFeatureSupport.require ((← initialized.run [seven, seven]) == .integer 14) "builtin lexical shadowing leaked its scope"
  initialized.checkCells [seven, seven] [(.word, some (.word (Word.ofNatModulo 7))), (.word, some (.word (Word.ofNatModulo 7))), (.integer, some (.integer 14)), (.integer, some (.integer 7))]
  initialized.checkResume [seven, seven] (.integer 14)
  let branches ← SourceCompilerFeatureSupport.compileNamed checked "branches"
  for (arguments, expected) in [([seven, nine], 16), ([nine, seven], 2)] do
    SourceCompilerFeatureSupport.require ((← branches.run arguments) == .integer expected) "builtin lexical branch result changed"
    branches.checkResume arguments (.integer expected)
  let discarded ← SourceCompilerFeatureSupport.compileNamed checked "discarded"
  SourceCompilerFeatureSupport.require ((← discarded.run [seven]) == .integer 14) "discarded builtin altered the body result"
  discarded.checkCells [seven] [(.word, some (.word (Word.ofNatModulo 7))), (.integer, some (.integer 14))]
  discarded.checkResume [seven] (.integer 14)
  let tail ← SourceCompilerFeatureSupport.compileNamed checked "tail"
  SourceCompilerFeatureSupport.require ((← tail.run [seven]) == .integer 14) "builtin lexical function tail was discarded"
  tail.checkCells [seven] [(.word, some (.word (Word.ofNatModulo 7))), (.integer, some (.integer 7))]
  tail.checkResume [seven] (.integer 14)
  let lazy ← SourceCompilerFeatureSupport.compileNamed checked "lazy"
  SourceCompilerFeatureSupport.require ((← lazy.run [seven]) == .integer 7) "builtin mapping key changed its default"
  lazy.checkCells [seven] [(.word, some (.word (Word.ofNatModulo 7))), (.mapping .bool .word, some (.mapping .bool .word [])), (.integer, some (.integer 0))]
  lazy.checkResume [seven] (.integer 7)
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "failed"
  faultResume failed [seven]
  failed.checkCells [seven] [(.word, some (.word (Word.ofNatModulo 7))), (.mapping .bool .word, some (.mapping .bool .word [])), (.integer, some (.integer 0)), (.word, none)]
  let missing ← SourceCompilerFeatureSupport.compileNamed checked "missing"
  faultResume missing [seven]
  let actual ← missing.invoke [seven]
  match actual.outcome with
  | .failed reason _ =>
    match ← actual.diagnostic reason with
    | some {error := .typeMismatch _ none, span := some _, ..} => pure ()
    | _ => throw (IO.userError "builtin condition/default fault lost raw metadata/span")
  | _ => throw (IO.userError "builtin condition/default fixture did not fail")
  let cells := (SourceCompilerFeatureSupport.sourceState (← missing.audit [seven])).heap
  match cells with
  | [input, mapping, prior] =>
    SourceCompilerFeatureSupport.require (input.type == .word && prior.type == .integer && (match prior.value with | some (.integer 14) => true | _ => false))
      "builtin lexical initializer fault changed prior source cells"
    match mapping.value with
    | some (.mapping .bool _ []) => pure ()
    | _ => throw (IO.userError "builtin lexical missing default failed to materialize its mapping")
  | _ => throw (IO.userError "builtin lexical missing default allocated its failed initializer")
  IO.println "builtin lexical statements: generic static extraction, nested calls, let/discard/tail, both scoped branches, default/fault writes and resume GREEN"

end Tests.SourceCoreBuiltinLexicalStatements
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinNamedCalls
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
#check_failure Solcore.SourceSemantics.CoreLowering.TypedMixedNamedParameters.Entry.mk
/-! Actual body lowering, nested builtin source traces and the real finish
helper close a concrete named body. Cached checked calls exercise argument/body
faults, scoped return/fallthrough, raw metadata and shared heap checkpoints. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreBuiltinNamedCalls
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly CompatibleExpressionBuiltins CallableIndexedHistory
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"builtin_lexical", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "builtin_lexical.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
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
  owner, inputs := [], roots := [.statement returned.id], nodes := [.expression literalNode, .expression toNode,
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
private theorem wordAdmitted : TypeAdmissible context .word := .word (.ofSignatures signatures)
private theorem integerAdmitted : TypeAdmissible context .integer := .integer (.ofSignatures signatures)
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
  ((∃ location, reason = .uninitializedLocation location ∧ token = Word.zero) ∨
   (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ reason = .missingMappingDefault value ∧ token = Word.zero.add tag)) ∨
  ∃ code, reason = .panic code ∧ token = Solcore.Frontend.SourceCorePanics.reason code
/-- Every panic fails with its code's reason. -/
private instance : FunctionCalls.FaultTokens faults := ⟨fun code => .inr ⟨code, rfl, rfl⟩⟩
private theorem uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id) :=
  fun _ location => .inl (.inl ⟨location, rfl, rfl⟩)
private theorem missing : ∀ id key value tag, MetadataRep values.registry (.mapping key value) tag →
  faults (.missingMappingDefault value) ((reasonAt id).add tag) :=
  fun _ key value tag owned => .inl (.inr ⟨key, value, tag, owned, rfl, rfl⟩)
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem innerTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 2) (.value (.integer 7)) ⟨[]⟩ :=
  BuiltinCalls.source_intro (checked := checked) (type := .integer) ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl
    (.apply (.cons (.intro (lookupExpression?_sound (node := literalNode) (by rfl))
      (.literal rfl (.word (numericLiteralValue?_sound (value := 7) (by rfl)))) .nil) .nil)
      (.value (.builtin (.wordToInteger (Word.ofNatModulo 7)))))
private theorem outerTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 4) (.value (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases innerTrace with
  | value evaluated =>
    exact BuiltinCalls.source_intro (checked := checked) (type := .word)
      ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl (.apply (.cons evaluated .nil) (.value (.builtin (.wordFromInteger 7))))
private theorem sourceTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 5) (.value (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases outerTrace with
  | value evaluated => exact .value (.intro (lookupExpression?_sound (node := groupNode) (by cbv)) (.group rfl evaluated) .nil)

private def statements : List StatementId := [returned.id]
private theorem statementSyntax : BuiltinLexicalStatements.Syntax source context true statements .word :=
  .returnValue (node := returned) [] (by cbv) rfl rfl (by cbv) rfl groupTyped syntaxTree
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def loopPolicy (native : SourceCoreGeneralFunctions.CallableContext)
    (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt => SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }

private theorem certified (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout} {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (loopPolicy native layouts frame globals) fuel source []
      statements .word reasonAt true Word.zero = .ok code) :
    BuiltinLexicalStatements.Tree layouts ⟨owner, []⟩ [] frame globals onError 100 values source [] reasonAt context [] true statements .word .word code := by
  apply GenericLexicalStatements.tree_of_flow rfl (by intros; rfl) rfl ?_ statementSyntax rfl rfl rfl
    (by intro actual declared index native selected; cases selected) rfl accepted
  intro current currentClosed currentResidual currentSignatures scope budget expression expressionNode lowered declarations syntaxValue found typed generated
  exact CompatibleExpressionBuiltins.tree_of_functions unique declarations currentSignatures currentClosed currentResidual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ native [] rfl
    (fun _ _ _ found => noCoercions _ _ found) syntaxValue found typed generated

private theorem statementTrace : TypedScopedStatements.Executes true program context [] source [] ⟨[]⟩
    statements context (.returned (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases sourceTrace with
  | value child =>
    exact TypedScopedStatements.terminal_intro true [] (lookupStatement?_sound (node := returned) (by cbv))
      (by intro expression; simp [returned]) (.returnValue (lookupStatement?_sound (by cbv)) rfl child) (.returned _)

private def closure : Dynamic.Closure := ⟨[], .word, statements, source, [], context, []⟩
private theorem bodyTrace : FunctionCallBody.Trace program closure context [] ⟨[]⟩
    (.value (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases statementTrace with
  | control executed => exact .returned executed

/-- The real finish/body traversal supplies the sealed static certificate.
The independent source trace is not a field of that certificate. -/
theorem accepted_body_certificate (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      source [] statements .word reasonAt Word.zero Word.zero = .ok code) :
    Nonempty (BuiltinNamedBody.Certificate layouts ⟨owner, []⟩ [] frame globals onError 100 values source context []
      reasonAt [] statements .word .word (loopPolicy native layouts frame globals) fuel Word.zero Word.zero code) := by
  have original := accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  cases generated : SourceCoreLoops.lowerFlowStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      source [] statements .word reasonAt true Word.zero with
  | error error =>
    rw [generated] at accepted
    change (Except.error error : Except SourceCoreLoops.Error Expr) = .ok code at accepted
    cases accepted
  | ok flow =>
    simp [generated] at accepted
    cases accepted
    exact BuiltinNamedBody.of_tree original rfl statementSyntax rfl (certified native generated)

theorem accepted_body_preserves (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      source [] statements .word reasonAt Word.zero Word.zero = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation current}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) mapping world ⟨[]⟩ store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame current))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked values.registry (functions ambient))
        finalMap finalWorld .word .word faults (.value (.word (Word.ofNatModulo 7))) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) finalMap finalWorld ⟨[]⟩ finalStore ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  obtain ⟨certificate⟩ := accepted_body_certificate native accepted
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, preserved, metadata, reached⟩ :=
    BuiltinNamedBody.Certificate.preserves (function := closure) (values := values) (ambient := ambient) (registry := values.registry) (functions ambient) (.refl _) definitions registered program valid unique uninitialized missing
      faithful (functionLeaves ambient) (functionTypes ambient) certificate environments heaps .nil agrees typed reference read unmapped bodyTrace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, preserved⟩

/-- Whole finish completion constructs its independent source body trace.
Neither a native child evaluation nor a universal body meaning is assumed. -/
theorem accepted_body_reflects (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      source [] statements .word reasonAt Word.zero Word.zero = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation current value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) mapping world ⟨[]⟩ store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame current))
    (unmapped : contextLocation ∉ mapping)
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program closure context [] ⟨[]⟩ outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked values.registry (functions ambient))
        finalMap finalWorld .word .word faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) finalMap finalWorld after finalStore ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  obtain ⟨certificate⟩ := accepted_body_certificate native accepted
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, preserved, metadata, reached⟩ :=
    BuiltinNamedBody.Certificate.reflects (function := closure) (values := values) (ambient := ambient) (registry := values.registry) (functions ambient) (.refl _) definitions registered program valid unique uninitialized missing
      faithful (functionLeaves ambient) (functionTypes ambient) certificate environments heaps .nil agrees typed reference read unmapped completed
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, preserved⟩

/-- The actual independent declaration dispatch has one source BodyInstance.
The checked program's well-formed source catalog, not Core typing, supplies the
owner-identity condition. -/
theorem source_body_unique {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
    {left right : Dynamic.BodyInstance} (wellFormed : ProgramWellFormed program)
    (first : Dynamic.FunctionInstantiates program instantiation left)
    (second : Dynamic.FunctionInstantiates program instantiation right) : left = right :=
  BuiltinNamedCalls.instantiation_unique_of_wellFormed wellFormed first second

/-- Whole native call completion enters the exact installed closure body after
its real packed arguments. Captures are retained as values, not reconstructed
from function types. -/
theorem installed_body_completion {signature : SourceCoreCalls.Signature} {index : Nat} {location : Location}
    {caller captured : Environment} {store middle final : Store} {body arguments : Expr} {argument value : Value}
    (evaluated : Evaluates caller store arguments (.inRight .word argument) middle)
    (reference : caller[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : middle.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (completed : Evaluates caller store (SourceCoreCalls.call signature index arguments Word.zero) value final) :
    Evaluates (argument :: captured) middle body value final :=
  NamedCalls.Arguments.body_complete evaluated reference read completed

private def content : String := String.intercalate "\n" [
  "enum Item { Item(Bool) }",
  "function compute(a: Word, b: Word) returns (integer) { let sum = integerAdd(wordToInteger(a), wordToInteger(b)); { let shadow = integerSub(sum, wordToInteger(a)); shadow; } if (integerLt(wordToInteger(a), wordToInteger(b))) { return integerAdd(sum, wordToInteger(a)); } return integerSub(sum, wordToInteger(b)); }",
  "function caller(a: Word, b: Word) returns (integer) { return compute(a, b); }",
  "function arguments(a: Word, b: Word) returns (integer) { return compute(wordFromInteger(wordToInteger(a)), wordFromInteger(wordToInteger(b))); }",
  "function failBody(a: Word) returns (integer) { let m: mapping(Bool => Word); let first = wordToInteger(m[integerEq(wordToInteger(a), wordToInteger(a))]); let written = integerAdd(first, wordToInteger(a)); let gap: Word; return wordToInteger(gap); }",
  "function failed(a: Word) returns (integer) { return failBody(wordFromInteger(wordToInteger(a))); }",
  "function skipped(a: Word) returns (integer) { let m: mapping(Bool => Word); let gap: Word; return compute(m[integerEq(wordToInteger(a), wordToInteger(a))], wordFromInteger(wordToInteger(gap))); }",
  "function missingBody(a: Word) returns (integer) { let m: mapping(Bool => Item); let written = wordToInteger(a); let failed = (m[integerEq(wordToInteger(a), wordToInteger(a))], written); return written; }",
  "function missing(a: Word) returns (integer) { return missingBody(a); }",
  "function unitHelper() { { let value = wordFromInteger(0); value; } }",
  "function unitCaller() { unitHelper(); }",
  "function tailHelper(a: Word) returns (integer) { let x = wordToInteger(a); { let y = integerSub(x, x); y; } integerAdd(x, x) }",
  "function tail(a: Word) returns (integer) { return tailHelper(a); }",
  "function rawEcho(raw: mapping(Bool => Word)) returns (mapping(Bool => Word)) { let flag = integerEq(0, 0); if (flag) { return raw; } return raw; }",
  "function raw(raw: mapping(Bool => Word)) returns (mapping(Bool => Word)) { return rawEcho(raw); }"
]

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"builtin named prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"builtin named ordered cells changed {label}: {reprStr final.heap}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  let resumed ← SourceCoreUnifiedCorpusSupport.get s!"builtin named resume {name}" (first.resume 300000)
  pure resumed.observation

private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name localName : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "builtin named fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == localName) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "builtin named exact binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "builtin named calls" content
    ["caller", "arguments", "failed", "skipped", "missing", "unitCaller", "tail", "raw"]
  let initialState : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (Word.ofNatModulo 819))⟩]}
  let seven : SourceTypedRuntime.Value := .word (Word.ofNatModulo 7)
  let nine : SourceTypedRuntime.Value := .word (Word.ofNatModulo 9)
  let mapType : TypeSystem.Ty := .mapping .bool .word
  let materialized : SourceTypedRuntime.Value := .mapping .bool .word []
  let raw : SourceTypedRuntime.Value := .mapping (.comptime .bool) (.comptime .word)
    [(.bool true, seven), (.bool true, nine)]
  let gap ← faultBinder compiled "failBody" "gap"
  let skippedGap ← faultBinder compiled "skipped" "gap"
  let item ← SourceCoreUnifiedCorpusSupport.get "builtin named Item"
    (match compiled.sourceProgram.signatures.dataTypes.head? with
     | some item => Except.ok item | none => Except.error "missing Item")
  for fuel in [0, 43, 300000] do
    for name in ["caller", "arguments"] do
      for (first, second, expected, shadow) in [(seven, nine, 23, 9), (nine, seven, 9, 7)] do
        match ← finish compiled name [first, second] fuel initialState with
        | .done (.integer actual) final =>
          SourceCoreUnifiedCorpusSupport.assertTrue (actual == expected) s!"builtin named branch changed {name}"
          cells initialState final
            [(.word, some first), (.word, some second), (.word, some first), (.word, some second),
              (.integer, some (.integer 16)), (.integer, some (.integer shadow))] name
          SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
            s!"builtin named unsafe result heap {name}"
        | other => throw (IO.userError s!"builtin named {name} changed: {reprStr other}")
    match ← finish compiled "tail" [seven] fuel initialState with
    | .done (.integer 14) final =>
      cells initialState final
        [(.word, some seven), (.word, some seven), (.integer, some (.integer 7)), (.integer, some (.integer 0))] "tail"
    | other => throw (IO.userError s!"builtin named tail changed: {reprStr other}")
    match ← finish compiled "unitCaller" [] fuel initialState with
    | .done .unit final => cells initialState final [(.word, some (.word Word.zero))] "unitCaller"
    | other => throw (IO.userError s!"builtin named unit finish changed: {reprStr other}")
    match ← finish compiled "raw" [raw] fuel initialState with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr raw) "builtin named raw header/order changed"
      cells initialState final [(mapType, some raw), (mapType, some raw), (.bool, some (.bool true))] "raw"
    | other => throw (IO.userError s!"builtin named raw result changed: {reprStr other}")
    match ← finish compiled "failed" [seven] fuel initialState with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "builtin named body fault lost source binder"
      cells initialState final [(.word, some seven), (.word, some seven), (mapType, some materialized),
        (.integer, some (.integer 0)), (.integer, some (.integer 7)), (.word, none)] "failed"
    | other => throw (IO.userError s!"builtin named body fault changed: {reprStr other}")
    match ← finish compiled "skipped" [seven] fuel initialState with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == skippedGap) "builtin named argument fault lost source binder"
      cells initialState final [(.word, some seven), (mapType, some materialized), (.word, none)] "skipped"
    | other => throw (IO.userError s!"builtin named argument fault entered body: {reprStr other}")
    match ← finish compiled "missing" [seven] fuel initialState with
    | .fault (.typeMismatch rawType none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (rawType == .nominal item.id []) "builtin named missing-default raw metadata changed"
      cells initialState final [(.word, some seven), (.word, some seven),
        (.mapping .bool rawType, some (.mapping .bool rawType [])), (.integer, some (.integer 7))] "missing"
    | other => throw (IO.userError s!"builtin named missing default changed: {reprStr other}")
  IO.println "builtin named calls: actual body/finish/prefix/installed call, nested arguments/bodies, source dispatch, scopes/fault writes, raw defaults/order and resume GREEN"

end Tests.SourceCoreBuiltinNamedCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreBuiltinNativeTyping
/-! An actual builtin compiler result is typed without a lowering tree or a
native argument-typing premise. Its literal child is extracted from its real
callback. The existing builtin IO suites cover effects, ordering and resume. -/
set_option autoImplicit false
namespace Tests.SourceCoreBuiltinNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionScalarNativeTyping BuiltinCallNativeTyping

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"native_builtin", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "native_builtin.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def literalNode : ExpressionNode := {
  id := id 0, span, type := .word, form := .literal (.decimal "7")}
private def calleeNode : ExpressionNode := {
  id := id 1, span, type := BuiltinFunctionId.wordToInteger.type,
  form := .reference "wordToInteger" (.builtinFunction .wordToInteger)}
private def callNode : ExpressionNode := {
  id := id 2, span, type := .integer,
  form := .call (id 1) [id 0] (.builtinFunction .wordToInteger)}
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression (id 2)],
  nodes := [.expression literalNode, .expression calleeNode, .expression callNode]}
private theorem checkedExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer]).toOption.get checkedExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def policy (native : SourceCoreGeneralFunctions.CallableContext) : SourceCoreFunctions.Policy :=
  {SourceCoreCompatibleDataExpressions.functionPolicy 100 values with
    callables := SourceCoreGeneralFunctions.callablePolicy (some native) []}

/-- The accepted compiler action fixes the exact callee, argument callback,
packed parameter check and gate. Hidden contexts and definitions are arbitrary. -/
theorem accepted_literal_builtin_native
    (native : SourceCoreGeneralFunctions.CallableContext)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin .wordToInteger))
    {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 3 compilation source [] (id 2) reasonAt = .ok code)
    (definitions : DataEnvironment) (administrative : Core.Context) :
    NativeTyping definitions administrative code := by
  apply of_functions native [] rfl descriptor (by rfl) (by rfl) (by cbv) (by rfl) (by rfl) _ accepted
  intro child member lowered generated
  have same : child = id 0 := by simpa using member
  subst child
  have literal := CompatibleExpressionLiterals.of_functions (values := values) (node := literalNode) (by rfl)
    (.word _) (by intro absent; cases absent) (by intros; rfl) rfl rfl generated
  obtain ⟨node, found, scalar⟩ := literal
  exact ⟨node, found, literal_native scalar definitions administrative⟩

/-- Every contracted builtin body is typed in an arbitrary surrounding
context; only the exact parameter bundle is used by the generated closure. -/
theorem every_builtin_contract_native (function : BuiltinFunctionId) (identity contract : Word)
    (definitions : DataEnvironment) (context : Core.Context) :
    HasType context (BuiltinCalls.Protocol.contracted function identity contract)
      (LanguageResult.resultType (CallableContract.functionType
        (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function))) definitions :=
  contracted_native function identity contract definitions context

end Tests.SourceCoreBuiltinNativeTyping
end
