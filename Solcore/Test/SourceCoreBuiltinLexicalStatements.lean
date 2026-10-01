import Solcore.SourceSemantics.CoreLowering.BuiltinLexicalStatements
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.ProgramChecking

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
  (∃ location, reason = .uninitializedLocation location ∧ token = Word.zero) ∨
  (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ reason = .missingMappingDefault value ∧ token = Word.zero.add tag)
private theorem uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id) :=
  fun _ location => .inl ⟨location, rfl, rfl⟩
private theorem missing : ∀ id key value tag, MetadataRep values.registry (.mapping key value) tag →
  faults (.missingMappingDefault value) ((reasonAt id).add tag) :=
  fun _ key value tag owned => .inr ⟨key, value, tag, owned, rfl, rfl⟩
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
