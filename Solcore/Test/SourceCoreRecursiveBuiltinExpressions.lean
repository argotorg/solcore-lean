import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualBuiltins
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.ProgramChecking

/-! A nested builtin inside an ordinary parent extracts its complete tree from
actual lowering and independent source typing. Both directions close every
child meaning; runtime fixtures cover data, control, and index parents. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreRecursiveBuiltinExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly CompatibleExpressionBuiltins

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"recursive_builtin", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "recursive_builtin.solc"⟩, 0, 1⟩
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
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression (id 5)], nodes := [.expression literalNode, .expression toNode,
    .expression innerNode, .expression fromNode, .expression outerNode, .expression groupNode]}
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
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem certified (native : SourceCoreGeneralFunctions.CallableContext) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 6 compilation source [] (id 5) reasonAt = .ok code) :
    Tree 100 values source context [] reasonAt [] (id 5) code :=
  tree_of_functions unique (by intro actual declared index native selected; cases selected) rfl rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ native [] rfl
    (fun _ _ _ found => noCoercions _ _ found) syntaxTree (by cbv) groupTyped accepted
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ []
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def identities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful identities := ⟨fun impossible => False.elim impossible, fun impossible => False.elim impossible⟩
private theorem functionLeaves : CompatibleEquality.FunctionObservations checked.catalog functions identities := fun impossible => False.elim impossible
private theorem functionTypes : FunctionRuntimeViews functions := fun impossible => False.elim impossible
private def model := CompatibleAmbientHeap.payloadModel checked values.registry functions
private def faults : FunctionCalls.FaultRep := fun _ _ => True
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

theorem accepted_preserves (native : SourceCoreGeneralFunctions.CallableContext) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 6 compilation source [] (id 5) reasonAt = .ok code)
    {actual : Environment} {actualContext : Core.Context} (typed : RuntimeEnvironmentHasTypes [] actual actualContext ambient.definitions) :
    ∃ value finalStore finalMap finalWorld, Evaluates actual [] (code.expression.rename Renaming.id) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .word code.type faults (.value (.word (Word.ofNatModulo 7))) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld ⟨[]⟩ finalStore ∧ LocationMap.Extends [] finalMap ∧ WorldExtends [] finalWorld ∧
      AdministrativePreserved [] [] finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ ⟨[]⟩ :=
  preserves (values := values) (faults := faults) (node := groupNode) functions (.refl _) faithful functionLeaves functionTypes program [] valid unique
    (by intros; trivial) (by intros; trivial) (certified native accepted) (by cbv) (.nil .nil) .empty .nil (by intro _ _ absent; cases absent) typed sourceTrace

theorem accepted_reflects (native : SourceCoreGeneralFunctions.CallableContext) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 6 compilation source [] (id 5) reasonAt = .ok code)
    {actual : Environment} {actualContext : Core.Context} {value : Value} {finalStore : Store}
    (typed : RuntimeEnvironmentHasTypes [] actual actualContext ambient.definitions)
    (completed : Evaluates actual [] (code.expression.rename Renaming.id) value finalStore) :
    ∃ outcome after finalMap finalWorld, Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 5) outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .word code.type faults outcome value ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends [] finalWorld ∧ AdministrativePreserved [] [] finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after :=
  reflects (values := values) (faults := faults) (node := groupNode) functions (.refl _) faithful functionLeaves functionTypes program [] valid
    (by intros; trivial) (by intros; trivial) (certified native accepted) (by cbv) (.nil .nil) .empty .nil (by intro _ _ absent; cases absent) typed completed

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }",
    "function nested(a: Word, b: Word) returns (integer) { return wordToInteger(wordFromInteger(integerAdd(wordToInteger(a), wordToInteger(b)))); }",
    "function binary(a: integer, b: integer) returns (Bool) { return integerEq(a, b) && !integerLt(a, b); }",
    "function choose(a: Word, b: Word) returns (integer) { return integerEq(wordToInteger(a), wordToInteger(b)) ? wordToInteger(a) : wordToInteger(b); }",
    "function pair(a: integer, b: integer) returns ((Bool, Bool)) { return (integerEq(a, b), integerLt(a, b)); }",
    "function construct(a: integer, b: integer) returns (Box) { return Box(integerEq(a, b)); }",
    "function key(m: mapping((Bool, Bool) => Word), a: integer, b: integer) returns (integer) { return wordToInteger(m[(integerEq(a, b), integerLt(a, b))]); }",
    "function skipped(a: integer) returns (integer) { let missing: Word; return true ? integerAdd(a, a) : wordToInteger(missing); }",
    "function failed(a: Word) returns (integer) { let missing: Word; return integerAdd(wordToInteger(a), wordToInteger(missing)); }"]}]}

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "recursive builtin checker" (checkProgram workspace)
  let seven : SourceCoreExecution.Value := .word (Word.ofNatModulo 7)
  let pair : SourceCoreExecution.Value := .product (.bool true) (.bool false)
  let mapping : SourceCoreExecution.Value := .mapping (.product .bool .bool) .word [(pair, .word (Word.ofNatModulo 37))]
  let cases : List (String × List SourceCoreExecution.Value × SourceCoreExecution.Value) := [
    ("nested", [seven, seven], .integer 14), ("binary", [.integer 7, .integer 7], .bool true),
    ("choose", [seven, .word (Word.ofNatModulo 9)], .integer 9), ("pair", [.integer 10, .integer 3], .product (.bool false) (.bool false)),
    ("key", [mapping, .integer 7, .integer 7], .integer 37), ("skipped", [.integer 7], .integer 14)]
  for (name, inputs, expected) in cases do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    SourceCompilerFeatureSupport.require ((← entry.run inputs) == expected) "recursive builtin parent changed result"
    entry.checkResume inputs expected
  let construct ← SourceCompilerFeatureSupport.compileNamed checked "construct"
  match ← construct.run [.integer 7, .integer 7] with
  | .constructed _ [.bool true] => pure ()
  | _ => throw (IO.userError "builtin constructor payload changed")
  let failed ← SourceCompilerFeatureSupport.compileNamed checked "failed"
  match (← failed.invoke [seven]).outcome with
  | .failed _ _ => pure ()
  | _ => throw (IO.userError "nested builtin fault changed")
  IO.println "recursive builtin grammar: nested calls and data/control/index parent positions GREEN"
end Tests.SourceCoreRecursiveBuiltinExpressions
