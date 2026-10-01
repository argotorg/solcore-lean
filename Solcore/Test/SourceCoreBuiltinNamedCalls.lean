import Solcore.SourceSemantics.CoreLowering.BuiltinNamedCallMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.ProgramChecking

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
