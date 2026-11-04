import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualBuiltins
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinNativeTyping
import Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.SourceSemantics.CoreLowering.RecursiveStageArguments
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientStageOrigins
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingReadMeaning
import Solcore.Frontend.SourceCoreCallableIndexedLedger
import Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingTupleMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveStagePrimitiveMeaning
import Solcore.Test.SourceCoreCompatibleGeneralRuntimeExtraction
import Solcore.Test.SourceSemantics.CompiledOrigins
import Solcore.SourceSemantics.CoreLowering.RecursiveStageTupleMeaning

/-!
# Recursive stage tests

Staged primitives, mappings, tuples and builtins inside recursive bodies, and global initialization.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveBuiltinExpressions
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveBuiltinNativeTyping
/-! Nested contracted builtins close every native child obligation from the
actual recursive static tree. The concrete fixture uses a production codebook;
root/parent consumers retain independent source typing and factory acceptance. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveBuiltinNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionBuiltins CompatibleExpressionScalarNativeTyping
open CompatibleExpressionBuiltinNativeTyping CompatibleCatalogNominalCoverage

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
  simp only [source, List.mem_cons, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem certified (native : SourceCoreGeneralFunctions.CallableContext) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 6 compilation source [] (id 5) reasonAt = .ok code) :
    Tree 100 values source context [] reasonAt [] (id 5) code :=
  tree_of_functions unique (by intro actual declared index native selected; cases selected) rfl rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ native [] rfl
    (fun _ _ _ found => noCoercions _ _ found) syntaxTree (by cbv) groupTyped accepted
private theorem actual_factory : SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer] = .ok checked := by cbv

/-- A builtin inside another builtin and a group uses all real child receipts;
no native typing callback for either call argument is provided. -/
theorem accepted_nested_builtins_native (native : SourceCoreGeneralFunctions.CallableContext)
    {code : SourceCoreBasic.LoweredExpr} {definitions : DataEnvironment} (administrative : Core.Context)
    (extension : checked.catalog.definitions.Extends definitions)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 6 compilation source [] (id 5)
      reasonAt = .ok code) : NativeTyping definitions administrative code := by
  have shaped := prepare_shapes actual_factory
  rw [← SourceCoreCompatibleCatalog.prepare_signatures actual_factory] at shaped
  exact builtins_native_at shaped (prepare_complete actual_factory) (.empty _) administrative extension (certified native accepted)

theorem actual_contextual_builtins_native
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {readFuel : Nat} {reasonAt : ExpressionId → Word}
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment} (administrative : Core.Context)
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (unique : SourceSemantics.NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionBuiltins.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : SourceSemantics.ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation (some native) parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  CompatibleExpressionBuiltinNativeTyping.contextual_native visibleTypes administrative registered ordinary unique closed residual declarations sourceSignatures
    syntaxTree found sourceTyped readPolicy lowerPolicy leafPolicy accepted extension

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function roundtrip(a: Word) returns (integer) { return wordToInteger(wordFromInteger(wordToInteger(a))); }"}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "recursive builtin native checker" (checkProgram workspace)
  let entry ← SourceCompilerFeatureSupport.compileNamed program "roundtrip"
  let native ← match entry.cached.indexed.base.callableContext with
    | some native => pure native
    | none => throw (IO.userError "actual compiler did not prepare a builtin codebook")
  let code ← SourceCompilerFeatureSupport.get "actual nested builtin fragment"
    (SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 6 compilation source [] (id 5) reasonAt)
  let administrative : Core.Context := [.integer, .function .unit .word]
  SourceCompilerFeatureSupport.require (code.type == .word &&
    Core.infer? administrative code.expression checked.catalog.definitions == some (LanguageResult.resultType .word))
      "nested builtin code lost native typing under hidden slots"
  entry.checkResume [.word (Word.ofNatModulo 7)] (.integer 7) 13
  IO.println "recursive builtin native typing: actual codebook, nested arguments, parent, hidden slots and resume GREEN"

end Tests.SourceCoreRecursiveBuiltinNativeTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveGlobalInitializationMeaning
/-! The real compiler-owned cache supplies every lambda row. Formal consumers
close the actual success-Unit continuation and reflect exact bootstrap values
and stores. Native IO checks all full cached templates, captured environments,
physical slot reads, initial prefix and complete machine resumption. No source
body correspondence or initial catalog Authority is inferred from these facts. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveGlobalInitializationMeaning
open Solcore Core Frontend SourceSemantics.CoreLowering
open RecursiveGlobalInitializationMeaning

variable {checked : SourceCoreCompatibleCatalog.Checked}
  (compiled : SourceCoreCallableIndexedPrograms.Prepared checked)
  (rows : List LambdaRow)
  (cached : compiled.secondPass.closures = rows.map LambdaRow.expression)
  (environment : Environment) (store : Store) (locations : Nat → Location)
  (references : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row →
    (reserve compiled.base.globals.reverse store environment).2[i]? =
      some (.cellRef (OptionalCell.cellType (.function row.parameter row.result)) (locations i)))
  (bounds : ∀ i, i < rows.length → locations i < (reserve compiled.base.globals.reverse store environment).1.length)

include cached references bounds in
/-- The cache's exact equation supplies the installed code. No native or
source function-body execution law is an input to initialization. -/
theorem actual_cached_bootstrap :
    Evaluates environment store (SourceCoreRecursiveEntry.allocateGlobals compiled.base.globals.reverse
      (SourceCoreRecursiveEntry.installFunctions compiled.secondPass.closures (LanguageResult.success .unit)))
      (.inRight .word .unit)
      (installStore rows locations (reserve compiled.base.globals.reverse store environment).2
        (reserve compiled.base.globals.reverse store environment).1 0) := by
  rw [cached]
  exact bootstrap_evaluates compiled.base.globals.reverse rows environment store locations references bounds

include cached references bounds in
/-- Any actual native completion is precisely the closed bootstrap result and
store. The saved closure environments come from the real emitted Unit binders. -/
theorem actual_cached_bootstrap_reflects {value : Value} {finalStore : Store}
    (completed : Evaluates environment store (SourceCoreRecursiveEntry.allocateGlobals compiled.base.globals.reverse
      (SourceCoreRecursiveEntry.installFunctions compiled.secondPass.closures (LanguageResult.success .unit))) value finalStore) :
    value = .inRight .word .unit ∧ finalStore =
      installStore rows locations (reserve compiled.base.globals.reverse store environment).2
        (reserve compiled.base.globals.reverse store environment).1 0 :=
  evaluation_deterministic completed (actual_cached_bootstrap compiled rows cached environment store locations references bounds)

include cached in
/-- With an ordered static cache receipt, even the physical references and
bounds are derived from real allocation. No runtime law is part of the receipt. -/
theorem actual_ordered_cached_bootstrap
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      compiled.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result) :
    Evaluates environment store (SourceCoreRecursiveEntry.allocateGlobals compiled.base.globals.reverse
      (SourceCoreRecursiveEntry.installFunctions compiled.secondPass.closures (LanguageResult.success .unit)))
      (.inRight .word .unit)
      (installStore rows (fun index => store.length + (compiled.base.globals.length - 1 - index))
        (reserve compiled.base.globals.reverse store environment).2
        (reserve compiled.base.globals.reverse store environment).1 0) := by
  rw [cached]
  simpa only [List.reverse_reverse, List.length_reverse] using
    ordered_bootstrap_evaluates compiled.base.globals.reverse rows environment store (by simpa using ordered)

private def content : String := String.intercalate "\n" [
  "function self(n: Word) returns (Word) { if (n == 0) { return 2; } return self(n - 1); }",
  "function left(n: Word) returns (Bool) { if (n == 0) { return true; } return right(n - 1); }",
  "function right(n: Word) returns (Bool) { let current = n; while (current != 0) { current -= 1; return left(current); } return false; }",
  "function closure(n: Word) returns (Word) { let shared = n; let f = lam(step: Word) -> Word { shared += step; return shared; }; return f(3); }",
  "function empty() {}"
]
private def rowsOf (closures : List Expr) : IO (List LambdaRow) := closures.mapM fun expression =>
  match expression with
  | .lambda parameter result body => pure ⟨parameter, result, body⟩
  | _ => throw (IO.userError "initialization cache contains a non-lambda")
private def completed (state : State) : IO (Value × Store) :=
  match runStateful 300000 state with
  | .done value store => pure (value, store)
  | other => throw (IO.userError s!"initialization machine did not complete: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive global initialization" content
    ["self", "left", "right", "closure", "empty"]
  let indexed := compiled.indexed
  let rows ← rowsOf indexed.secondPass.closures
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (rows.map LambdaRow.expression) == reprStr indexed.secondPass.closures)
    "initialization full cached row reconstruction changed"
  SourceCoreUnifiedCorpusSupport.assertTrue (rows.length == indexed.base.globals.length)
    "initialization cache/global inventory length changed"
  for (row, index) in rows.zipIdx do
    let signature ← match indexed.base.globals[index]? with
      | some signature => pure signature
      | none => throw (IO.userError "initialization ordered signature missing")
    SourceCoreUnifiedCorpusSupport.assertTrue (signature.functionType == .function row.parameter row.result)
      s!"initialization static cache-to-signature receipt changed {index}"
  let recipe ← SourceCoreUnifiedCorpusSupport.get "actual initialization recipe" (SourceCoreIndexedSession.Recipe.prepare compiled)
  let cache ← SourceCoreUnifiedCorpusSupport.get "actual installed cache" (SourceCoreCallableIndexedTemplates.prepare indexed)
  let emitted := SourceCoreCallableIndexedFrames.allocate indexed.ancestry.layout.frame
    (SourceCoreRecursiveEntry.allocateGlobals indexed.base.globals.reverse
      (SourceCoreRecursiveEntry.installFunctions indexed.secondPass.closures (LanguageResult.success .unit)))
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr emitted == reprStr recipe.bootstrap)
    "initialization actual recipe emission changed"
  let prefixes : List Store := [[], [.word (Word.ofNatModulo 859), .inRight .unit (.bool false)]]
  for oldStore in prefixes do
    let frame := SourceCoreCallableIndexedFrames.encode indexed.ancestry.layout.frame .empty
    let reserved := reserve indexed.base.globals.reverse (oldStore ++ [frame]) [.cellRef indexed.ancestry.layout.frame.type oldStore.length]
    let locations := fun index => oldStore.length + 1 + rows.length - 1 - index
    let expected := installStore rows locations reserved.2 reserved.1 0
    let (value, actual) ← completed (.initial recipe.bootstrap [] oldStore)
    SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr (Value.inRight .word .unit))
      "initialization bootstrap result changed"
    SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected)
      "initialization all ordered writes/code/captured environments changed"
    SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (actual.take oldStore.length) == reprStr oldStore)
      "initialization old native prefix changed"
    SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (actual[oldStore.length]?) == reprStr (some frame))
      "initialization overwritten initial frame"
    for (row, index) in rows.zipIdx do
      let expectedValue := Value.inRight .unit (installedValue reserved.2 index row)
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (actual[locations index]?) == reprStr (some expectedValue))
        s!"initialization exact cached slot changed {index}"
    if oldStore.isEmpty then
      SourceCoreUnifiedCorpusSupport.assertTrue
        (SourceCoreCallableNativeSlots.checkPreparedGlobals cache.nativeGlobals cache.nativeGlobalsGenerated actual).isOk
        "initialization actual cache authentication failed"
    for fuel in [0, 1, 43, 300000] do
      let observed := runStateful fuel (.initial recipe.bootstrap [] oldStore)
      let final ← match observed with
        | .done value store => pure (value, store)
        | .outOfFuel state => completed state
        | other => throw (IO.userError s!"initialization internal fault {reprStr other}")
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr final == reprStr (value, actual))
        s!"initialization complete native resume changed {fuel}"
  IO.println "recursive global initialization: actual reserved slots, full cached code/captures, protected prefix/frame and complete bootstrap resume GREEN"

end Tests.SourceCoreRecursiveGlobalInitializationMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveStageAmbientGuards
/-! Actual guard rows under one ambient value model. Function provenance is a
separate static supply obligation at function leaves; ordinary data and the
entire heap continue to use their original compatible representation. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveStageAmbientGuards
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly
open CompatiblePayload RecursiveNamedPreparedStageContracts

variable {checked : SourceCoreCompatibleCatalog.Checked} {rawRegistry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}

/-- This condition records actual origin receipts only for represented function
leaves. It contains no heap relation or execution premise. -/
def FunctionOrigins (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (sidecar : SourceCoreStageContracts.Sidecar)
    (site : SourceCoreCallableContracts.Callsite) : Prop :=
  CompatibleAmbientStageOrigins.FunctionOrigins functions registry sidecar site

/-- Refinement affects only function leaves. Its value properties and all
world extensions are inherited from the same ambient function model. -/
def with_origins (functions : FunctionModel checked.catalog ambient)
    (sidecar : SourceCoreStageContracts.Sidecar) (site : SourceCoreCallableContracts.Callsite) :
    FunctionModel checked.catalog ambient :=
  CompatibleAmbientStageOrigins.with_origins functions sidecar site

theorem supplied_origins : FunctionOrigins (with_origins functions sidecar site) rawRegistry sidecar site :=
  CompatibleAmbientStageOrigins.supplied_origins

/-- Forgetting provenance never strengthens a value relation. -/
theorem forget_origin {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (represented : (with_origins functions sidecar site).Represents rawRegistry mapping world sourceType source carrier type) :
    functions.Represents rawRegistry mapping world sourceType source carrier type :=
  CompatibleAmbientStageOrigins.forget_origin represented

/-- The converse requires the static origin supply for this exact function
model. It is not inferred from a related heap or native typing. -/
theorem refinement_iff (origins : FunctionOrigins functions rawRegistry sidecar site)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty} :
    (with_origins functions sidecar site).Represents rawRegistry mapping world sourceType source carrier type ↔
      functions.Represents rawRegistry mapping world sourceType source carrier type :=
  CompatibleAmbientStageOrigins.refinement_iff origins

theorem related_origin
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (represented : ValueRep checked rawRegistry functions mapping world sourceType source carrier type)
    (callable : Staging.CallBoundary.UserCallable source) :
    CallableLedger.OriginRep sidecar.plan site.table source carrier :=
  CompatibleAmbientStageOrigins.related_origin origins represented callable

theorem covers_from_rows {call : ExpressionId} {arguments : List ExpressionId}
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    (rows : CallableLedger.Rows sidecar site call arguments)
    (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      (CallableLedger.frame sidecar) site call arguments sourceType type :=
  CompatibleAmbientStageOrigins.covers_from_rows origins rows sourceType type

/-- The real public artifact supplies every original guard row. Only actual
function-leaf provenance remains separate from that compiler receipt. -/
theorem actual_coverage {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiled native)
    {context : SourceCoreFunctions.Context} {node : ExpressionNode}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (issued : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      (CallableLedger.frame sidecar) site node.id arguments sourceType type :=
  CompatibleAmbientStageOrigins.actual_coverage prepared issued caller contains form origins sourceType type

/-- Actual source selection and descriptor preparation supply the extra
function-leaf receipt while its original code/capture relation stays explicit. -/
theorem actual_named_leaf {program : CheckedProgram}
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {key : SourceCoreStageCodebook.Key} {function : Dynamic.GlobalFunction}
    (accepted : SourceCoreStageCodebook.prepareWithProjection program sidecar.plan project limits firstId = .ok site.table)
    (descriptor : SourceCoreCallableContracts.Descriptor site.table (.named key))
    (selected : SourceCompilationPlan.exactInstantiationKey sidecar.plan function.instantiation = .ok key)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {raw : Value} {type : Ty}
    (represented : functions.Represents rawRegistry mapping world sourceType (.global function)
      (.pair raw (.word descriptor.id)) type) :
    (with_origins functions sidecar site).Represents rawRegistry mapping world sourceType (.global function)
      (.pair raw (.word descriptor.id)) type :=
  CompatibleAmbientStageOrigins.actual_named_leaf accepted descriptor selected represented

theorem actual_lambda_origin {program : CheckedProgram}
    {plan : SourceCoreStageCodebook.Plan}
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat} {table : SourceCoreStageCodebook.Table}
    {owner : SourceCoreStageCodebook.Key} {id : ExpressionId} {active : TypeSystem.Substitution}
    {function : Dynamic.Closure} {view : TypedSource} {node : ExpressionNode}
    (accepted : SourceCoreStageCodebook.prepareWithProjection program plan project limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda owner id active))
    (receipt : LambdaSourceAlignment.SourceReceipt program plan owner active function.source)
    (metadata : LambdaMetadataViews.MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (found : view.lookupExpression? id = some node)
    (form : node.form = .lambda function.parameters function.resultType function.body) (raw : Value) :
    CallableLedger.OriginRep plan table (.closure function) (.pair raw (.word descriptor.id)) :=
  CompatibleAmbientStageOrigins.actual_lambda_origin accepted descriptor receipt metadata unique found form raw

abbrev actual_builtin_origin := @RecursiveStageProjection.builtin_origin

/-- Actual preparation covers the refined function model without adding an
origin condition to data or requiring a separate function-origin callback. -/
theorem refined_actual_coverage {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiled native)
    {context : SourceCoreFunctions.Context} {node : ExpressionNode}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (issued : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor
      (CompatibleAmbientHeap.payloadModel checked rawRegistry (with_origins functions sidecar site))
      (CallableLedger.frame sidecar) site node.id arguments sourceType type :=
  CompatibleAmbientStageOrigins.actual_coverage prepared issued caller contains form
    CompatibleAmbientStageOrigins.supplied_origins sourceType type

abbrev callee_fault := @RecursiveStageMeaning.preserves_callee_fault_for
abbrev plain_guard_rejection := @CallStageBoundary.preserves_rejection_for

/-- Ordinary data remains representable without any callable origin. -/
theorem data_without_origin (mapping : LocationMap) (world : StoreTyping) :
    (CompatibleAmbientHeap.payloadModel checked rawRegistry functions).Represents mapping world
      (.product .word .unit) (.product (.word Word.zero) .unit) (.pair (.word Word.zero) .unit) (.product .word .unit) ∧
    ¬ CallableLedger.OriginRep sidecar.plan site.table
      (.product (.word Word.zero) .unit) (.pair (.word Word.zero) .unit) := by
  exact ⟨.product (.word _) .unit, by intro impossible; cases impossible⟩

theorem builtin_has_no_user_contract (function : Dynamic.BuiltinFunction)
    (contract : Staging.CallGuard.Contract) :
    ¬ (CallableLedger.frame sidecar).Binds (.builtin function) contract := by
  intro impossible
  cases impossible

section Prefixes
open RecursiveStageMeaning
local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "catalog" => CompatibleEquality.storageCatalog checked.catalog

theorem guard_rejection
    {program : SourceSemantics.Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {certificate : Certificate} {faults : FaultRep} {site : SourceCoreCallableContracts.Callsite}
    {call callee : ExpressionId} {arguments : List ExpressionId} {scope : SourceCoreLocalCell.Scope}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (childMeaning : PreservesFor model program registry frame context certificate faults)
    (sameGuards : frame.guards = CallableLedger.frame sidecar)
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    (rows : CallableLedger.Rows sidecar site call arguments)
    (reasonMeaning : ∀ reason token, CallStageBoundary.ReasonRepresents site reason token →
      faults (.stage frame call reason) token)
    (unknown : Word) (result : Ty) (argumentCode : Expr)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {callable : Dynamic.Value} {reason : Staging.CallGuard.Fault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (child : Staging.Recursive.Expression program registry frame context environment before callee (.value callable) after)
    (rejected : Staging.CallBoundary.GuardRejects frame.guards call arguments callable reason) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown result (lowered.expression.rename ξ) argumentCode)
        (.inLeft result (.word token)) finalStore ∧
      faults (.stage frame call reason) token ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have coverage : CallStageBoundary.CoversFor model frame.guards site call arguments node.type lowered.type := by
    rw [sameGuards]
    exact covers_from_rows origins rows node.type lowered.type
  exact RecursiveStageMeaning.preserves_rejection_for certified found childMeaning coverage reasonMeaning
    unknown result argumentCode environments heaps locals layout child rejected

variable {program : SourceSemantics.Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : RecursiveStageMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}
open RecursiveStageMeaning
open DataExpressionSequence (Tree)

theorem argument_fault
    {site : SourceCoreCallableContracts.Callsite} {call callee : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : PreservesFor model program registry frame context certificate faults)
    (sameGuards : frame.guards = CallableLedger.frame sidecar)
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    (rows : CallableLedger.Rows sidecar site call ids)
    (unknown : Word) (resultType : Ty)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before middle after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {callable : Dynamic.Value} {contract : Staging.CallGuard.Contract}
    {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (child : Staging.Recursive.Expression program registry frame context environment before callee (.value callable) middle)
    (bound : frame.guards.Binds callable contract)
    (accepted : Staging.CallBoundary.GuardAccepts frame.guards call ids callable)
    (arguments : Staging.Recursive.Expressions program registry frame context environment middle ids (.fault failure) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown resultType (lowered.expression.rename ξ)
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)) (.inLeft resultType (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have coverage : CallStageBoundary.CoversFor model frame.guards site call ids node.type lowered.type := by
    rw [sameGuards]
    exact covers_from_rows origins rows node.type lowered.type
  exact RecursiveStageArguments.preserves_call_argument_fault_for certified found tree meaning coverage unknown resultType
    environments heaps locals layout child bound accepted arguments

end Prefixes

end Tests.SourceCoreRecursiveStageAmbientGuards
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveStageMappingReadMeaning
/-! Actual accepted mapping-read consumers. Static declaration and source
annotation facts remain independent of the native projection and execution. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
namespace Tests.SourceCoreRecursiveStageMappingReadMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload
open CompatibleMapping.VirtualRoot

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
  {declared : TypedBinder} {key value : TypeSystem.Ty}
  (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id) = .ok lowered.expression)
  (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
  (unique : NodeOccurrencesUnique source)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (typed : ExpressionHasType source context id node.type)
  (form : node.form = .reference name (.local binder))
  (declaration : SourceCoreDataPlaces.rootBinder source binder = .ok declared)
  (declaredType : declared.scheme.body = .mapping key value)
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {faults : FunctionCalls.FaultRep}

include accepted read unique declarations typed form declaration declaredType sameSource extension in
/-- The actual successful compiler and independently typed source declaration
close the reflection certificate. Only the original completed native run is
left as an execution premise. -/
theorem actual_reflects :
    RecursiveStagePrimitiveMeaning.Reflects functions (registry := registry) program stages invocation context
      (fun current occurrence code => current = scope ∧ occurrence = id ∧ code = lowered) faults := by
  intro current occurrence code receipt
  obtain ⟨rfl, rfl, rfl⟩ := receipt
  exact RecursiveStageMappingReadMeaning.reflects functions program stages invocation sameSource extension
    (RecursiveStageMappingReadMeaning.of_accepted accepted read unique declarations typed form declaration declaredType)

include accepted read unique declarations typed form declaration declaredType sameSource extension in
/-- Successful source evaluation and semantic failure use the same actual read
receipt. The complete source and native stores are related after initialization. -/
theorem actual_preserves
    (uninitialized : ∀ expression location, faults (.uninitializedLocation location) (reasonAt expression))
    {root : ExpressionNode} (found : invocation.source.lookupExpression? id = some root)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.Outcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Staging.Recursive.Expression program stages invocation context environment before id outcome after) :
    ∃ native finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) native finalStore ∧
      RecursiveStagePrimitiveMeaning.Result functions (registry := registry) finalMap finalWorld root.type lowered.type faults outcome native ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact RecursiveStageMappingReadMeaning.preserves functions program stages invocation sameSource extension unique uninitialized
    (RecursiveStageMappingReadMeaning.of_accepted accepted read unique declarations typed form declaration declaredType)
    found environments heaps locals agrees trace

/-- Inversion records the original initialization write, including its target,
result and complete final store. No constructed native execution is used. -/
theorem original_empty_write {environment : Core.Environment} {before after : Core.Store}
    {index target : Nat} {type : Core.Ty} {empty result : Core.Value} {literal : Core.Expr}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : before.read? target = some (.inLeft type .unit)) (quoted : Quoted empty literal)
    (evaluated : Evaluates environment before
      (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal) result after) :
    result = .inRight .word empty ∧ before.write? target (.inRight .unit empty) = some after := by
  rcases RecursiveStageMappingReadMeaning.read_completed lookup read quoted evaluated with
    ⟨_, _, impossible, _⟩ | ⟨_, _, sameOptional, resultEq, written⟩
  · cases impossible
  · cases sameOptional
    exact ⟨resultEq, written⟩

/-- A later read of an initialized mapping keeps the entire native store. -/
theorem original_present {environment : Core.Environment} {before after : Core.Store}
    {index target : Nat} {type : Core.Ty} {empty present result : Core.Value} {literal : Core.Expr}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : before.read? target = some (.inRight .unit present)) (quoted : Quoted empty literal)
    (evaluated : Evaluates environment before
      (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal) result after) :
    result = .inRight .word present ∧ after = before := by
  rcases RecursiveStageMappingReadMeaning.read_completed lookup read quoted evaluated with
    ⟨_, _, sameOptional, resultEq, storeEq⟩ | ⟨_, _, impossible, _⟩
  · cases sameOptional
    exact ⟨resultEq, storeEq⟩
  · cases impossible

/-- Initialization preserves every other native cell, including unused
administrative cells outside the source location map. -/
theorem original_empty_preserves_other {environment : Core.Environment} {before after : Core.Store}
    {index target other : Nat} {type : Core.Ty} {empty result : Core.Value} {literal : Core.Expr}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : before.read? target = some (.inLeft type .unit)) (quoted : Quoted empty literal)
    (evaluated : Evaluates environment before
      (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal) result after)
    (different : other ≠ target) : after.read? other = before.read? other :=
  Store.write?_preserves_other (original_empty_write lookup read quoted evaluated).2 different

end Tests.SourceCoreRecursiveStageMappingReadMeaning

namespace Tests.SourceCoreRecursiveStageMappingReadMeaning.NativeReads
open Solcore Solcore.Frontend SourceInference Core

private abbrev get := @SourceCoreUnifiedCorpusSupport.get
private abbrev require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def w (n : Nat) : Core.Value := .word (Word.ofNatModulo n)
private def mapType : TypeSystem.Ty := .mapping .word .word
private def nestedType : TypeSystem.Ty := .mapping .word (.mapping (.proxy .word) .word)
private def empty : SourceTypedRuntime.Value := .mapping .word .word []
private def nestedEmpty : SourceTypedRuntime.Value := .mapping .word (.mapping (.proxy .word) .word) []
private def populated : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) .word [(word 1, word 7), (word 1, word 9)]

private def content := String.intercalate "\n" [
  "function fresh() returns (mapping(Word => Word)) { let table: mapping(Word => Word); return table; }",
  "function repeat() returns ((mapping(Word => Word), mapping(Word => Word))) { let table: mapping(Word => Word); let alias = table; let second = table; return (alias, second); }",
  "function input(table: mapping(Word => Word)) returns (mapping(Word => Word)) { let alias = table; return alias; }",
  "function nested() returns (mapping(Word => mapping(@Word => Word))) { let table: mapping(Word => mapping(@Word => Word)); return table; }",
  "function afterFault() returns (mapping(Word => Word)) { let marker: Word = 7; let table: mapping(Word => Word); let alias = table; let gap: Word; let late: mapping(Word => Word); let stop = gap; return late; }"
]

private def nativeFinish (code : Core.Expr) (environment : Core.Environment)
    (store : Core.Store) (fuel : Nat) : IO (Core.Value × Core.Store) := do
  let first := Core.runStateful fuel (.initial code environment store)
  let final := match first with
    | .outOfFuel checkpoint => Core.runStateful 300000 checkpoint
    | other => other
  match final with
  | .done value after => pure (value, after)
  | other => throw (IO.userError s!"mapping native leaf did not finish: {reprStr other}")

private def wholeFinish (compiled : SourceCoreUnifiedCompilation.Compiled)
    (name : String) (arguments : List SourceTypedRuntime.Value) (fuel : Nat)
    (initial : SourceTypedRuntime.RuntimeState) :
    IO (SourceTypedRuntime.RunResult × String) := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  let final ← get "mapping actual native resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution
    | none => throw (IO.userError "mapping native execution receipt missing")
  let store := SourceCoreCallableIndexedLedger.store execution.completion
  require (!store.isEmpty) "mapping native store missing"
  if name == "afterFault" then
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
    let selected ← get "mapping native fault source" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
    let missing ← match selected.function.typedBody.nodes.filterMap (fun item => match item with
        | .expression node => match node.form with
          | .reference "gap" (.local binder) => some (node, binder)
          | _ => none
        | _ => none) with
      | [missing] => pure missing
      | _ => throw (IO.userError "mapping original fault occurrence changed")
    match execution.completion.result.native.observation with
    | .failed reason _ =>
      let diagnostic ← match execution.completion.result.diagnostics.diagnostic? reason with
        | some diagnostic => pure diagnostic
        | none => throw (IO.userError "mapping native fault has no diagnostic")
      require (diagnostic.error == .uninitializedLocal missing.2 &&
        diagnostic.site == .occurrence missing.1.id.occurrence && diagnostic.span == some missing.1.span)
        "mapping native reason/original occurrence/span changed"
    | _ => throw (IO.userError "mapping native first fault was not returned")
  pure (final.observation, reprStr (execution.completion.result.native.observation, store))

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    "mapping source prefix changed"
  require (reprStr ((final.heap.drop initial.heap.length).map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"mapping full ordered source heap changed: {reprStr final.heap}"

private def whole (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let initial : SourceTypedRuntime.RuntimeState := {
    heap := [⟨.comptime .word, none⟩, ⟨.word, some (word 983)⟩] }
  let tests : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value ×
      List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("fresh", [], empty, [(mapType, some empty)]),
    ("repeat", [], .product empty empty, List.replicate 3 (mapType, some empty)),
    ("input", [populated], populated, List.replicate 2 (mapType, some populated)),
    ("nested", [], nestedEmpty, [(nestedType, some nestedEmpty)])]
  let success ← tests.mapM fun (name, args, _, _) => wholeFinish compiled name args 300000 initial
  let failure ← wholeFinish compiled "afterFault" [] 300000 initial
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "afterFault"
  let selected ← get "mapping fault specialization" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  let gap ← match (SourceCoreDataPlaces.declaredBinders selected.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "mapping actual missing binder changed")
  for fuel in [0, 1, 17, 300000] do
    for ((name, args, expected, expectedCells), baseline) in tests.zip success do
      let actual ← wholeFinish compiled name args fuel initial
      require (reprStr actual == reprStr baseline) "mapping whole native store/source heap/resume changed"
      match actual.1 with
      | .done value final =>
        require (reprStr value == reprStr expected) s!"mapping whole result changed: {name}: {reprStr value}"
        cells initial final expectedCells
        require (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          "mapping whole heap is not deeply safe"
      | other => throw (IO.userError s!"mapping unexpected success result {name}: {reprStr other}")
    let actual ← wholeFinish compiled "afterFault" [] fuel initial
    require (reprStr actual == reprStr failure) "mapping first fault/full native store/resume changed"
    match actual.1 with
    | .fault (.uninitializedLocal binder) final =>
      require (binder == gap) "mapping actual first-fault binder changed"
      cells initial final [(.word, some (word 7)), (mapType, some empty), (mapType, some empty),
        (.word, none), (mapType, none)]
    | other => throw (IO.userError s!"mapping first fault changed: {reprStr other}")

private def leaves (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
  let mut count := 0
  for name in ["fresh", "repeat", "input", "nested", "afterFault"] do
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
    let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
      | [named] => pure named
      | _ => throw (IO.userError "mapping root cache row changed")
    let selected ← get "mapping exact full specialization" (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan key)
    require (selected == named.specialized) "mapping full specialization/ledger changed"
    let source := selected.function.typedBody
    let ledger := selected.function.solvedRequirements
    for item in source.nodes do
      match item with
      | .expression node =>
        match node.form with
        | .reference _ (.local binder) =>
          let declared ← get "mapping actual binder" (SourceCoreDataPlaces.rootBinder source binder)
          match declared.scheme.body with
          | .mapping keyType valueType =>
            require (declared.scheme.quantified.isEmpty && declared.schemeRequirements.isEmpty &&
              node.requirements.isEmpty && node.coercions.isEmpty) "mapping read is not ordinary"
            let type ← get "mapping native projection" (values.checked.catalog.project declared.scheme.body)
            let scope := [(binder, type)]
            let reason := Word.ofNatModulo (4000 + node.id.occurrence.index)
            let code ← get "mapping actual lowerRead" (SourceCoreCompatibleDataExpressions.lowerRead 100 values source scope node.id reason)
            let rawEmpty : SourceCoreCompatibleValues.Value := .mapping keyType valueType []
            let encoded ← get "mapping empty/default carrier" (SourceCoreCompatibleValues.encode 100 values declared.scheme.body rawEmpty)
            require (encoded.context.registry.entries == values.registry.entries) "mapping default changed runtime registry"
            let populatedValue : SourceCoreCompatibleValues.Value := if declared.scheme.body == mapType then
              .mapping (.comptime .word) .word [(.word (Word.ofNatModulo 1), .word (Word.ofNatModulo 7)),
                (.word (Word.ofNatModulo 1), .word (Word.ofNatModulo 9))] else rawEmpty
            let full ← get "mapping initialized payload" (SourceCoreCompatibleValues.encode 100 values declared.scheme.body populatedValue)
            require (full.context.registry.entries.take values.registry.entries.length == values.registry.entries) "mapping initialized value changed registry"
            let captured := Core.Value.closure .unit .word (.var 1) [w 97, w 101]
            let initialCells : Core.Store := [captured, w 103]
            let suffix : Core.Store := [.pair (w 107) captured]
            let environment : Core.Environment := [.cellRef (OptionalCell.cellType type) initialCells.length, captured]
            let absent := initialCells ++ [.inLeft type .unit] ++ suffix
            let initialized := initialCells ++ [.inRight .unit encoded.value] ++ suffix
            let present := initialCells ++ [.inRight .unit full.value] ++ suffix
            let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ =>
              .error (.unsupportedExpression node.id node.form)
            let compilation : SourceCoreFunctions.Context := {
              plan := compiled.indexed.base.plan, owner := key, globals := compiled.indexed.base.globals,
              administrativePrefix := 1, solvedRequirements := ledger, internalReason := Word.zero }
            let lower := fun current => SourceCoreFunctions.lowerExpressionWithPolicy
              (SourceCoreCompatibleDataExpressions.functionPolicy 100 values) noBody 100
              {compilation with solvedRequirements := current} source scope node.id (fun _ => reason)
            let actual ← get "mapping actual whole expression callback" (lower ledger)
            require (actual.expression == code && actual.type == type) "mapping callback/leaf code changed"
            let rows := match ledger with
              | [] => [ledger]
              | first :: _ =>
                let extra := {first with id := ⟨(ledger.map (fun (row : SolvedRequirement) => row.id.index)).foldl max 0 + 1⟩, evidence := .assumption first.predicate}
                [ledger, extra :: ledger, ledger ++ [extra]]
            for complete in rows do
              let same ← get "mapping full unused ledger" (lower complete)
              require (same == actual) "mapping unused ordered rows changed native code"
            for fuel in [0, 1, 17, 300000] do
              let first ← nativeFinish code environment absent fuel
              require (first == (.inRight .word encoded.value, initialized)) "mapping empty first read/full write changed"
              let again ← nativeFinish code environment first.2 fuel
              require (again == first) "mapping second read wrote/allocated a different cell"
              let existing ← nativeFinish code environment present fuel
              require (existing == (.inRight .word full.value, present)) "mapping present read/default metadata/full store changed"
            count := count + 1
          | _ => pure ()
        | .integerLiteral literal resolution =>
          let _ ← get "mapping retained marker Selected" (SourceCoreElaboration.validateWordIntegerLiteral ledger node literal resolution)
          require (node.requirements == [resolution.requirement]) "mapping marker full row changed"
        | _ => pure ()
      | _ => pure ()
  require (count == 10) s!"mapping actual ordinary read count changed: {count}"

/-- New leaf and whole-source IO only; this does not call an older runner. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "staged local mapping reads" content
    ["fresh", "repeat", "input", "nested", "afterFault"]
  require (compiled.keys.length == 5 && compiled.indexed.base.functions.length == 5 &&
    compiled.indexed.secondPass.closures.length == 5) "mapping full actual root inventory changed"
  leaves compiled
  whole compiled
  IO.println "staged mapping reads: actual first write/repeat/alias/input/nested defaults/raw keys/first fault/full ledger/full stores/four resume budgets GREEN"

end Tests.SourceCoreRecursiveStageMappingReadMeaning.NativeReads

namespace Tests.SourceCoreRecursiveStageMappingReadMeaning

/-- Independent new mapping-read cases, registered once by the test runner. -/
def run : IO Unit := NativeReads.run

end Tests.SourceCoreRecursiveStageMappingReadMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveStageMappingTupleMeaning
/-! Actual ordered tuple lowering composes concrete mapping and primitive
receipts. Full final heap and first-fault observations are checked at real
compiled roots; the new runner does not invoke an older runner. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveStageMappingTupleMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly RecursiveStageMappingTupleMeaning
abbrev FaultRep := RecursiveStageTupleMeaning.FaultRep

section Accepted
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {budget fuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {node : ExpressionNode} {ids : List ExpressionId} {reasonAt : ExpressionId → Word}
  {code : SourceCoreBasic.LoweredExpr}
  (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
  (form : node.form = .tuple ids) (typed : ExpressionHasType source context id node.type)
  (special : ∀ child remaining, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child remaining source scope id reasonAt) = .ok none)
  (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
  (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (budget + 1) compilation source scope id reasonAt = .ok code)
  (extract : ∀ child, child ∈ ids → ∀ childNode lowered, source.lookupExpression? child = some childNode →
    ExpressionHasType source context child childNode.type →
    SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope child reasonAt = .ok lowered →
    Certificate fuel values source context compilation.solvedRequirements reasonAt scope child lowered)

include unique found form typed special readPolicy leafPolicy accepted extract in
theorem accepted_root : Certificate fuel values source context compilation.solvedRequirements reasonAt scope id code :=
  of_functions unique found form typed special readPolicy leafPolicy accepted extract

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ child location, faults (.uninitializedLocation location) (reasonAt child))

include unique found form typed special readPolicy leafPolicy accepted extract sameSource sameLedger extension runtime uninitialized in
theorem accepted_reflects
    {mapping : LocationMap} {world : StoreTyping} {admin : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      admin scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expression program stages invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type code.type (FaultRep faults) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects functions program stages invocation sameSource sameLedger extension runtime uninitialized
    (accepted_root unique found form typed special readPolicy leafPolicy accepted extract)
    (sameSource ▸ found) environments heaps locals agrees evaluated

include unique found form typed special readPolicy leafPolicy accepted extract sameSource sameLedger extension runtime uninitialized in
theorem accepted_preserves
    {mapping : LocationMap} {world : StoreTyping} {admin : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.Outcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      admin scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Staging.Recursive.Expression program stages invocation context environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type code.type (FaultRep faults) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves functions program stages invocation sameSource sameLedger extension runtime uninitialized unique
    (accepted_root unique found form typed special readPolicy leafPolicy accepted extract)
    (sameSource ▸ found) environments heaps locals agrees trace
end Accepted

/-- Repeated mapping occurrences retain the same actual read receipt three
 times. The second and third reads observe the first read's initialized cell. -/
theorem repeated_mapping {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id child : ExpressionId} {node childNode : ExpressionNode}
    {code : SourceCoreBasic.LoweredExpr}
    (header : CompatibleExpressionTuples.Header values source id node [child, child, child]
      [childNode.type, childNode.type, childNode.type] [code, code, code])
    (found : source.lookupExpression? child = some childNode)
    (selected : RecursiveStageMappingReadMeaning.Supported (fuel := fuel) (values := values) (source := source)
      (context := context) (reasonAt := reasonAt) scope child code) :
    Certificate fuel values source context solved reasonAt scope id (SourceCoreCalls.packArguments [code, code, code]) := by
  let entries := [(child, code)]
  have sequence : DataExpressionSequence.Tree source (RecursiveStageTupleMeaning.Entries scope entries) scope
      [child, child, child] [childNode.type, childNode.type, childNode.type] [code, code, code] :=
    .cons found ⟨rfl, by simp [entries]⟩ (.cons found ⟨rfl, by simp [entries]⟩ (.single found ⟨rfl, by simp [entries]⟩))
  have children : ∀ current lowered, (current, lowered) ∈ entries →
      Certificate fuel values source context solved reasonAt scope current lowered := by
    intro current lowered member
    have same : current = child ∧ lowered = code := by simpa [entries, Prod.mk.injEq] using member
    rcases same with ⟨rfl, rfl⟩
    exact RecursiveStageMappingTupleMeaning.mapping selected
  exact .tuple header sequence children

/-- Concrete tuple composition never represents a rejected nested stage as
successful native completion. -/
theorem no_stage_result {faults : FunctionCalls.FaultRep} {scope : Staging.Recursive.Scope}
    {id : ExpressionId} {reason : Staging.CallGuard.Fault} {token : Word} :
    ¬ FaultRep faults (.stage scope id reason) token := by intro impossible; exact impossible

private abbrev get := @SourceCoreUnifiedCorpusSupport.get
private abbrev require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def mapType : TypeSystem.Ty := .mapping .word .word
private def empty : SourceTypedRuntime.Value := .mapping .word .word []
private def populated : SourceTypedRuntime.Value := .mapping (.comptime .word) .word [(word 1, word 7), (word 1, word 9)]
private def content := String.intercalate "\n" [
  "function triple() returns ((mapping(Word => Word), Word, mapping(Word => Word))) { let table: mapping(Word => Word); return (table, 7, table); }",
  "function nested() returns (((mapping(Word => Word), mapping(Word => Word)), mapping(Word => Word))) { let a: mapping(Word => Word); let b: mapping(Word => Word); return ((a, b), a); }",
  "function input(table: mapping(Word => Word)) returns ((mapping(Word => Word), mapping(Word => Word), mapping(Word => Word))) { return (table, table, table); }",
  "function firstFault() returns ((Word, mapping(Word => Word))) { let gap: Word; let late: mapping(Word => Word); return (gap, late); }",
  "function laterFault() returns ((mapping(Word => Word), Word, mapping(Word => Word))) { let table: mapping(Word => Word); let gap: Word; let late: mapping(Word => Word); return (table, gap, late); }"
]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO (SourceTypedRuntime.RunResult × String) := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  let final ← get "mapping tuple actual resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution
    | none => throw (IO.userError "mapping tuple native receipt absent")
  let store := SourceCoreCallableIndexedLedger.store execution.completion
  require (!store.isEmpty) "mapping tuple native store absent"
  if name == "firstFault" || name == "laterFault" then
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
    let selected ← get "mapping tuple exact specialization" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
    let missing ← match selected.function.typedBody.nodes.filterMap (fun item => match item with
      | .expression node => match node.form with | .reference "gap" (.local binder) => some (node, binder) | _ => none
      | _ => none) with
      | [missing] => pure missing
      | _ => throw (IO.userError "mapping tuple original gap occurrence absent")
    match execution.completion.result.native.observation with
    | .failed reason _ =>
      let diagnostic ← match execution.completion.result.diagnostics.diagnostic? reason with
        | some diagnostic => pure diagnostic
        | none => throw (IO.userError "mapping tuple native diagnostic absent")
      require (diagnostic.error == .uninitializedLocal missing.2 &&
        diagnostic.site == .occurrence missing.1.id.occurrence && diagnostic.span == some missing.1.span)
        "mapping tuple original first fault occurrence/span changed"
    | _ => throw (IO.userError "mapping tuple native fault missing")
    match final.observation with
    | .fault (.uninitializedLocal binder) _ =>
      require (binder == missing.2) "mapping tuple decoded original fault binder changed"
    | _ => throw (IO.userError "mapping tuple decoded first fault missing")
  pure (final.observation, reprStr (execution.completion.result.native.observation, store))

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "mapping tuple source prefix changed"
  require (reprStr ((final.heap.drop initial.heap.length).map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"mapping tuple full ordered heap changed: {reprStr final.heap}"

/-- Five actual roots audit nary/nested/repeated reads, raw initialized keys,
first and later faults, full source/native heaps and original checkpoint resume. -/
def run : IO Unit := do
  let names := ["triple", "nested", "input", "firstFault", "laterFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "staged tuples with mapping leaves" content names
  require (compiled.keys.length == 5 && compiled.indexed.base.functions.length == 5 &&
    compiled.indexed.secondPass.closures.length == 5) "mapping tuple full root inventory changed"
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (word 983)⟩]}
  let tests : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value ×
      List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("triple", [], .product empty (.product (word 7) empty), [(mapType, some empty)]),
    ("nested", [], .product (.product empty empty) empty, List.replicate 2 (mapType, some empty)),
    ("input", [populated], .product populated (.product populated populated), [(mapType, some populated)])]
  let successes ← tests.mapM fun (name, args, _, _) => finish compiled name args 300000 initial
  let failures ← ["firstFault", "laterFault"].mapM fun name => finish compiled name [] 300000 initial
  for fuel in [0, 1, 17, 300000] do
    for ((name, args, expected, expectedCells), baseline) in tests.zip successes do
      let actual ← finish compiled name args fuel initial
      require (reprStr actual == reprStr baseline) "mapping tuple full native/source heap or checkpoint changed"
      match actual.1 with
      | .done value final =>
        require (reprStr value == reprStr expected) s!"mapping tuple result changed: {name} {reprStr value}"
        cells initial final expectedCells
        require (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          "mapping tuple source heap not deeply safe"
      | other => throw (IO.userError s!"mapping tuple unexpected success {reprStr other}")
    for (name, baseline) in ["firstFault", "laterFault"].zip failures do
      let actual ← finish compiled name [] fuel initial
      require (reprStr actual == reprStr baseline) "mapping tuple fault full native store/checkpoint changed"
      match actual.1 with
      | .fault (.uninitializedLocal _) final =>
        cells initial final (if name == "firstFault" then [(.word, none), (mapType, none)]
          else [(mapType, some empty), (.word, none), (mapType, none)])
      | other => throw (IO.userError s!"mapping tuple first fault changed {reprStr other}")
  IO.println "staged mapping tuples: actual nary/nested/repeated/raw keys/first-later faults/full heaps/four resume budgets GREEN"

end Tests.SourceCoreRecursiveStageMappingTupleMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveStagePrimitiveMeaning
/-! Actual literal acceptance builds two ordered occurrences of the same static
leaf, then the closed staged primitive theorem supplies reflection. Real native
subtree audits retain all ledger rows and every native cell. Unit is an actual
empty-tuple leaf; mapping initialization and generalized reads remain boundaries. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 32768
namespace Tests.SourceCoreRecursiveStagePrimitiveMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly CompatibleExpressionPrimitives
open RecursiveStagePrimitiveMeaning

abbrev actual_preserves := @RecursiveStagePrimitiveMeaning.preserves
abbrev actual_ordinary_read := @RecursiveStagePrimitiveMeaning.read_reflects

section Accepted
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel readFuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id pairId : ExpressionId} {node pairNode : ExpressionNode} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  (found : source.lookupExpression? id = some node) (atomic : CompatibleExpressionLiterals.Atomic node.form)
  (stageAtomic : Staging.Recursive.AtomicForm node.form)
  (unitType : node.form = .tuple [] → node.type = .unit)
  (special : ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
  (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
  (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
  (metadata : Metadata values.checked source pairId pairNode (.product lowered.type lowered.type))
  (form : pairNode.form = .tuple [id, id]) (pairType : pairNode.type = .product node.type node.type)

include found atomic stageAtomic unitType special readPolicy leafPolicy accepted metadata form pairType in
theorem accepted_pair :
    ∃ tree : Tree readFuel values source context compilation.solvedRequirements reasonAt scope pairId
      ⟨.product lowered.type lowered.type, LocalSequence.pair lowered.type lowered.type lowered.expression lowered.expression⟩,
      Supported tree := by
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted
  have leaf : LiteralSupported (source := source) (solved := compilation.solvedRequirements) id lowered := by
    obtain ⟨other, otherFound, literal, selected⟩ := receipt
    have same := Option.some.inj (otherFound.symm.trans found)
    subst other
    exact ⟨node, found, literal, selected, stageAtomic⟩
  exact ⟨.pair metadata form found found pairType (.product (.literal receipt.forget)) (.product (.literal receipt.forget)),
    .pair metadata form found found pairType _ _ (.product _ (.literal receipt.forget leaf)) (.product _ (.literal receipt.forget leaf))⟩

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ child location, faults (.uninitializedLocation location) (reasonAt child))

include readFuel sameSource uninitialized sameLedger runtime found atomic stageAtomic unitType special readPolicy leafPolicy accepted metadata form pairType in
theorem actual_pair_reflects :
    ReflectsCode functions program stages invocation (context := context) (registry := registry) (faults := faults) scope pairId
      ⟨.product lowered.type lowered.type, LocalSequence.pair lowered.type lowered.type lowered.expression lowered.expression⟩ := by
  obtain ⟨tree, supported⟩ := accepted_pair (readFuel := readFuel) (context := context) (reasonAt := reasonAt)
    found atomic stageAtomic unitType special readPolicy leafPolicy accepted metadata form pairType
  exact RecursiveStagePrimitiveMeaning.reflects functions program stages invocation sameSource uninitialized sameLedger runtime supported
end Accepted

section Unit
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel readFuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {node : ExpressionNode} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  (found : source.lookupExpression? id = some node) (form : node.form = .tuple [])
  (type : node.type = .unit)
  (special : ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
  (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
  (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)

include readFuel found form type special readPolicy leafPolicy accepted in
theorem accepted_unit :
    ∃ tree : Tree readFuel values source context compilation.solvedRequirements reasonAt scope id lowered,
      Supported tree := by
  have atomic : CompatibleExpressionLiterals.Atomic node.form := form ▸ .unit
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic (fun _ => type)
    special readPolicy leafPolicy accepted
  exact ⟨.product (.literal receipt.forget), .product _ (.literal receipt.forget (literal_of_certificate receipt))⟩

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ child location, faults (.uninitializedLocation location) (reasonAt child))

include readFuel found form type special readPolicy leafPolicy accepted sameSource sameLedger runtime uninitialized in
theorem actual_unit_reflects :
    ReflectsCode functions program stages invocation (context := context) (registry := registry)
      (faults := faults) scope id lowered := by
  obtain ⟨tree, supported⟩ := accepted_unit (readFuel := readFuel) (context := context)
    found form type special readPolicy leafPolicy accepted
  exact RecursiveStagePrimitiveMeaning.reflects functions program stages invocation sameSource uninitialized sameLedger runtime supported

include readFuel found form type special readPolicy leafPolicy accepted sameSource sameLedger runtime uninitialized in
theorem actual_unit_preserves (unique : NodeOccurrencesUnique source)
    (extension : SourceCoreRawMetadata.Extends values.registry registry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.Outcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Staging.Recursive.Expression program stages invocation context environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      Result functions (registry := registry) finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨tree, supported⟩ := accepted_unit (readFuel := readFuel) (context := context)
    found form type special readPolicy leafPolicy accepted
  exact RecursiveStagePrimitiveMeaning.preserves functions program stages invocation sameSource unique uninitialized
    extension sameLedger runtime supported (sameSource ▸ found) environments heaps locals agrees trace
end Unit

/-- The independent source unit rule preserves the complete source heap. -/
theorem source_unit {program : SourceSemantics.Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode}
    (contains : ContainsExpression invocation.source id node) (form : node.form = .tuple [])
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    Staging.Recursive.Expression program stages invocation context environment heap id (.value .unit) heap := by
  apply Staging.Recursive.Expression.atomicValue contains (form ▸ .unit) coercions
  rw [form, requirements]
  exact .tuple rfl .nil .nil

/-- Native unit construction also leaves arbitrary captured values and cells untouched. -/
theorem native_unit {environment : Environment} {store : Store} :
    Evaluates environment store (LanguageResult.success .unit) (.inRight .word .unit) store :=
  .inRight .unit

section Boundaries

theorem nonempty_tuple_not_literal_supported {source : TypedSource} {solved : List SolvedRequirement}
    {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    {first : ExpressionId} {rest : List ExpressionId}
    (found : source.lookupExpression? id = some node) (tuple : node.form = .tuple (first :: rest)) :
    ¬ LiteralSupported (source := source) (solved := solved) id code := by
  intro supported
  have impossible := literal_tuple_empty supported found tuple
  cases impossible

theorem mapping_read_not_supported {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Word}
    {context : SourceSemantics.Context} {code : SourceCoreBasic.LoweredExpr} {declared : TypedBinder}
    {key value : TypeSystem.Ty}
    (declaration : SourceCoreDataPlaces.rootBinder source declared.id = .ok declared)
    (mapping : declared.scheme.body = .mapping key value)
    (actual : ∀ receipt : CompatibleExpressionReads.Certificate fuel values source scope id reason code.expression,
      receipt.binder = declared.id) :
    ¬ ReadSupported (fuel := fuel) (values := values) (source := source) (context := context)
      (reasonAt := fun _ => reason) (scope := scope) id code := by
  rintro ⟨receipt, _, _, ordinary⟩
  have same : receipt.declared = declared := Except.ok.inj ((actual receipt ▸ receipt.declaration).symm.trans declaration)
  exact ordinary ⟨key, value, same ▸ mapping⟩

theorem generalized_cell_excluded {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : Core.DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {value : Core.Value} {type : Core.Ty}
    (represented : GenericHeap.CellRepresents model mapping world cell value type) : cell.generalized = none :=
  represented.ordinary

theorem staged_result_has_no_rejection {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {faults : FunctionCalls.FaultRep}
    {invocation : Staging.Recursive.Scope} {id : ExpressionId} {reason : Staging.CallGuard.Fault} {value : Value} :
    ¬ Result functions (registry := registry) mapping world sourceType type faults (.fault (.stage invocation id reason)) value := by
  intro impossible
  cases impossible

abbrev full_unused_ledger := @Tests.SourceCoreCompatibleGeneralRuntimeExtraction.accepted_reflects
end Boundaries

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def w (n : Nat) : Core.Value := .word (Word.ofNatModulo n)
private def content := String.intercalate "\n" [
  "function pairRead(a: Word, b: Word) returns ((Word, Word)) { return (a + 3, ~b); }",
  "function shortRead(gate: Bool) returns (Bool) { let absent: Bool; return gate && absent; }",
  "function firstFault() returns (Word) { let first: Word; let second: Word; return first + second; }",
  "function secondFault() returns (Word) { let first: Word = 9; let second: Word; return first + second; }",
  "function unitRoot() { let unused: Word = 13; return (); }"
]

private def finish (code : Core.Expr) (environment : Core.Environment) (store : Core.Store) (fuel : Nat) : IO (Core.Value × Core.Store) := do
  let first := Core.runStateful fuel (.initial code environment store)
  let result := match first with
    | .outOfFuel checkpoint => Core.runStateful 300000 checkpoint
    | other => other
  match result with
  | .done value after => pure (value, after)
  | other => throw (IO.userError s!"native primitive incomplete: {reprStr other}")

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut roots := 0
  let mut reads := 0
  let mut literals := 0
  let mut units := 0
  for name in ["pairRead", "shortRead", "firstFault", "secondFault", "unitRoot"] do
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
    let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
      | [named] => pure named
      | _ => throw (IO.userError "actual primitive root not unique")
    let selected ← get "same full primitive specialization" (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (selected == named.specialized) "primitive full metadata changed"
    let source := selected.function.typedBody
    let binders := (SourceCoreDataPlaces.declaredBinders source).reverse
    let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
    let mut scope : SourceCoreLocalCell.Scope := []
    let mut native : List Core.Value := []
    let mut fields : Core.Store := []
    let captured := Core.Value.closure .unit .word (.var 1) [w 97, w 101]
    let initialCells : Core.Store := [captured, w 103]
    for binder in binders do
      let type ← get "ordinary read actual type" (values.checked.catalog.project binder.scheme.body)
      require (match binder.scheme.body with | .mapping .. => false | _ => true) "mapping branch entered supported audit"
      scope := scope ++ [(binder.id, type)]
      native := native ++ [.cellRef (OptionalCell.cellType type) (initialCells.length + fields.length)]
      let payload : Option Core.Value := if binder.name == "a" then some (w 11) else if binder.name == "b" then some (w 5)
        else if binder.name == "gate" then some (.bool false)
        else if binder.name == "first" && name == "secondFault" then some (w 9) else none
      fields := fields ++ [match payload with | some value => .inRight .unit value | none => .inLeft type .unit]
    native := native ++ [captured]
    let store := initialCells ++ fields
    let reasonAt := fun id : ExpressionId => Word.ofNatModulo (1000 + id.occurrence.index)
    let policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
    let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .error (.unsupportedExpression ⟨⟨source.owner,0⟩⟩ (.tuple []))
    let mut results : List ExpressionId := []
    for item in source.nodes do
      match item with
      | .statement statement => if let .returnStmt (some id) := statement.form then results := results ++ [id]
      | .expression node =>
        match node.form with
        | .reference _ (.local binder) =>
          let _ ← get "actual lowerRead" (SourceCoreCompatibleDataExpressions.lowerRead 100 values source scope node.id (reasonAt node.id))
          let declared ← get "actual rootBinder" (SourceCoreDataPlaces.rootBinder source binder)
          require (declared.scheme.quantified.isEmpty && declared.schemeRequirements.isEmpty) "read generalized metadata changed"
          reads := reads + 1
        | .integerLiteral literal resolution =>
          let _ ← get "selected numeric Word row" (SourceCoreElaboration.validateWordIntegerLiteral selected.function.solvedRequirements node literal resolution)
          require (node.requirements == [resolution.requirement]) "numeric leaf ownership changed"
          literals := literals + 1
        | .tuple [] =>
          require (node.type == .unit && node.requirements.isEmpty && node.coercions.isEmpty) "unit full source metadata changed"
          units := units + 1
        | .unary .. | .binary .. | .tuple .. => require (node.requirements.isEmpty && node.coercions.isEmpty) "primitive parent metadata changed"
        | _ => pure ()
    require (results.length == 1) "primitive return occurrence changed"
    for id in results do
      let ledger := selected.function.solvedRequirements
      let rows := match ledger with
        | [] => [ledger]
        | first :: _ =>
          let extra := {first with id := ⟨(ledger.map (fun (row : SolvedRequirement) => row.id.index)).foldl max 0 + 1⟩, evidence := .assumption first.predicate}
          [ledger, extra :: ledger, ledger ++ [extra]]
      let compilation : SourceCoreFunctions.Context := {
        plan := compiled.indexed.base.plan
        owner := named.signature.key
        globals := compiled.indexed.base.globals
        administrativePrefix := 1
        solvedRequirements := ledger
        internalReason := Word.zero }
      let base ← get "actual primitive root lowering" (SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 100 compilation source scope id reasonAt)
      if name == "unitRoot" then
        require (!ledger.isEmpty && rows.length == 3) "unit unused full ledger coverage lost"
        require (base.type == .unit && base.expression == LanguageResult.success .unit) "actual unit lowering changed"
      for complete in rows do
        let lowered ← get "same full ledger primitive root" (SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 100
          {compilation with solvedRequirements := complete} source scope id reasonAt)
        require (lowered == base) "unused ledger changed actual native code"
        let baseline ← finish lowered.expression native store 300000
        for fuel in [0, 1, 17, 300000] do
          let result ← finish lowered.expression native store fuel
          require (result == baseline && result.2 == store) "original whole native store/resume changed"
        match name, baseline.1 with
        | "unitRoot", .inRight .word .unit => pure ()
        | "pairRead", .inRight .word (.pair (.word first) (.word second)) =>
          require (first == Word.ofNatModulo 14 && second == (Word.ofNatModulo 5).bitNot) "ordered pair primitive result changed"
        | "shortRead", .inRight .word (.bool false) =>
          let gateIndex ← match binders.zipIdx.filterMap (fun (binder, index) => if binder.name == "gate" then some index else none) with
            | [index] => pure index
            | _ => throw (IO.userError "actual short circuit binder changed")
          let activeStore := store.set (initialCells.length + gateIndex) (.inRight .unit (.bool true))
          let missing ← match source.nodes.filterMap (fun item =>
            match item with
            | .expression node =>
              match node.form with
              | .reference "absent" (.local _) => some node.id
              | _ => none
            | _ => none) with
            | [child] => pure child
            | _ => throw (IO.userError "actual short circuit missing occurrence changed")
          for fuel in [0, 1, 17, 300000] do
            let active ← finish lowered.expression native activeStore fuel
            require (active == (.inLeft .bool (.word (reasonAt missing)), activeStore))
              "actual right branch fault/store changed"
        | "firstFault", .inLeft .word (.word reason) | "secondFault", .inLeft .word (.word reason) =>
          let expectedName := if name == "firstFault" then "first" else "second"
          let candidates := source.nodes.filterMap fun item =>
            match item with
            | .expression node =>
              match node.form with
              | .reference name (.local _) => if name == expectedName then some node.id else none
              | _ => none
            | _ => none
          let missing ← match candidates with
            | [child] => pure child
            | _ => throw (IO.userError "exact missing read identity changed")
          require (reason == reasonAt missing) "original first/later fault token changed"
        | _, other => throw (IO.userError s!"primitive subtree result changed {reprStr other}")
      roots := roots + 1
  require (roots == 5 && reads == 8 && literals == 3 && units == 1) s!"actual primitive coverage {roots}/{reads}/{literals}/{units}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "native staged primitives" content ["pairRead", "shortRead", "firstFault", "secondFault", "unitRoot"]
  inspect compiled
  IO.println "staged native primitives: actual unit/read/operator leaves/Selected rows/full unused ledger/ordered pair/short circuit/exact fault/whole native store/resume GREEN"
end Tests.SourceCoreRecursiveStagePrimitiveMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveStageAmbientArguments
/-! The actual primitive receipts supply the staged child meanings for an
ambient argument pack. No child execution premise is added. Ordered effects and
the original semantic fault survive; stage guards remain a separate interface. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 32768
namespace Tests.SourceCoreRecursiveStageAmbientArguments
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly

abbrev semanticFaults (faults : FunctionCalls.FaultRep) : RecursiveStageMeaning.FaultRep
  | .semantic reason, token => faults reason token
  | .stage _ _ _, _ => False

def Children (fuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate := fun scope id code =>
  ∃ tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id code,
    RecursiveStagePrimitiveMeaning.Supported tree

section Actual
variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = solved)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include sameSource sameLedger runtime uninitialized in
theorem primitive_reflects :
    RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Children fuel values source context solved reasonAt) (semanticFaults faults) := by
  intro scope id code certified node found mapping world admin environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  obtain ⟨tree, supported⟩ := certified
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, metadata⟩ :=
    RecursiveStagePrimitiveMeaning.reflects functions program stages invocation sameSource uninitialized sameLedger runtime
      supported found environments heaps locals agrees evaluated
  refine ⟨outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds, preserved, metadata⟩
  cases represented with
  | value payload => exact .value payload
  | fault reason => exact .fault reason

include sameSource sameLedger runtime uninitialized in
theorem primitive_preserves (unique : NodeOccurrencesUnique source)
    (extension : SourceCoreRawMetadata.Extends values.registry registry) :
    RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Children fuel values source context solved reasonAt) (semanticFaults faults) := by
  intro scope id code certified node found mapping world admin environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  obtain ⟨tree, supported⟩ := certified
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata⟩ :=
    RecursiveStagePrimitiveMeaning.preserves functions program stages invocation sameSource unique uninitialized
      extension sameLedger runtime supported found environments heaps locals agrees trace
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, preserved, metadata⟩
  cases represented with
  | value payload => exact .value payload
  | fault reason => exact .fault reason

variable {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}
  (tree : DataExpressionSequence.Tree invocation.source (Children fuel values source context solved reasonAt) scope ids types codes)

include sameSource sameLedger runtime uninitialized tree in
theorem pack_reflects
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expressions program stages invocation context environment before ids outcome after ∧
      RecursiveStageArguments.ResultFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld types codes (semanticFaults faults) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  RecursiveStageArguments.reflects_for tree
    (primitive_reflects functions program stages invocation sameSource sameLedger runtime uninitialized)
    environments heaps locals agrees evaluated

include sameSource sameLedger runtime uninitialized tree in
theorem pack_preserves (unique : NodeOccurrencesUnique source)
    (extension : SourceCoreRawMetadata.Extends values.registry registry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.ValuesOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Staging.Recursive.Expressions program stages invocation context environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      RecursiveStageArguments.ResultFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld types codes (semanticFaults faults) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, preserved, metadata⟩ :=
    RecursiveStageArguments.preserves_for tree
      (primitive_preserves functions program stages invocation sameSource sameLedger runtime uninitialized unique extension)
      environments heaps locals agrees trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, preserved, metadata⟩
end Actual

section Static
variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode} {code : SourceCoreBasic.LoweredExpr}

theorem literal_child (receipt : CompatibleExpressionLiteralRuntime.Certificate solved source id code) :
    Children fuel values source context solved reasonAt scope id code :=
  ⟨.product (.literal receipt.forget), .product _ (.literal receipt.forget
    (RecursiveStagePrimitiveMeaning.literal_of_certificate receipt))⟩

/-- Successful production lowering supplies the same numeric selection receipt. -/
theorem accepted_child {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {budget : Nat} {compilation : SourceCoreFunctions.Context}
    (found : source.lookupExpression? id = some node) (atomic : CompatibleExpressionLiterals.Atomic node.form)
    (unitType : node.form = .tuple [] → node.type = .unit)
    (special : ∀ child remaining, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child remaining source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt = .ok code) :
    Children fuel values source context compilation.solvedRequirements reasonAt scope id code :=
  literal_child (CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted)

theorem empty_children :
    DataExpressionSequence.Tree source (Children fuel values source context solved reasonAt) scope [] [] [] := .nil

theorem singleton_child (found : source.lookupExpression? id = some node)
    (child : Children fuel values source context solved reasonAt scope id code) :
    DataExpressionSequence.Tree source (Children fuel values source context solved reasonAt) scope [id] [node.type] [code] :=
  .single found child

theorem repeated_children (found : source.lookupExpression? id = some node)
    (child : Children fuel values source context solved reasonAt scope id code) :
    DataExpressionSequence.Tree source (Children fuel values source context solved reasonAt) scope
      [id, id, id] [node.type, node.type, node.type] [code, code, code] :=
  .cons found child (.cons found child (.single found child))
end Static

section Legacy
variable {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty}
  {faults : RecursiveStageMeaning.FaultRep} {source : Dynamic.Value} {value : Value}

theorem old_value (represented : model.Represents mapping world sourceType source value type) :
    RecursiveStageMeaning.ResultRepresents model mapping world sourceType type faults (.value source) (.inRight .word value) :=
  RecursiveStageMeaning.ResultRepresents.value represented

theorem old_fault {failure : Staging.Recursive.Failure} {token : Word} (represented : faults failure token) :
    RecursiveStageMeaning.ResultRepresents model mapping world sourceType type faults (.fault failure) (.inLeft type (.word token)) :=
  RecursiveStageMeaning.ResultRepresents.fault represented

theorem old_values {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {sources : List Dynamic.Value} {values : List Value}
    (represented : DataExpressionSequence.Values model mapping world types (codes.map (·.type)) sources values) :
    RecursiveStageArguments.Result model mapping world types codes faults (.values sources)
      (.inRight .word (DataPatternValues.packValues values)) :=
  RecursiveStageArguments.Result.values represented

theorem old_argument_fault {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {reason : Staging.Recursive.Failure} {token : Word} (represented : faults reason token) :
    RecursiveStageArguments.Result model mapping world types codes faults (.fault reason)
      (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) :=
  RecursiveStageArguments.Result.fault represented

abbrev legacy_rejection := @RecursiveStageMeaning.preserves_rejection
abbrev legacy_argument_fault := @RecursiveStageArguments.preserves_call_argument_fault
end Legacy

theorem stage_fault_excluded {faults : FunctionCalls.FaultRep} {scope : Staging.Recursive.Scope}
    {call : ExpressionId} {reason : Staging.CallGuard.Fault} {token : Word} :
    ¬ semanticFaults faults (.stage scope call reason) token := by
  intro impossible
  exact impossible

def run : IO Unit := do
  SourceRecursiveStageTupleExpressions.run
  SourceCoreRecursiveStagePrimitiveMeaning.run
  IO.println "ambient staged packs: existing actual ordered tuple/primitive full-ledger, whole-heap fault and resume audits reused GREEN"

end Tests.SourceCoreRecursiveStageAmbientArguments
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveStageTupleMeaning
/-! Actual tuple acceptance retains the ordered child receipts. These static
obligations are explicit; the staged meanings of the children come from the
single supported-tree proof. The runtime audit retains every ledger row and cell. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 32768
namespace Tests.SourceCoreRecursiveStageTupleMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly RecursiveStageTupleMeaning

section Accepted
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {budget fuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {node : ExpressionNode} {ids : List ExpressionId} {reasonAt : ExpressionId → Word}
  {code : SourceCoreBasic.LoweredExpr}
  (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
  (form : node.form = .tuple ids) (typed : ExpressionHasType source context id node.type)
  (special : ∀ child remaining, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child remaining source scope id reasonAt) = .ok none)
  (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
  (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (budget + 1) compilation source scope id reasonAt = .ok code)
  (extract : ∀ child, child ∈ ids → ∀ childNode lowered, source.lookupExpression? child = some childNode →
    ExpressionHasType source context child childNode.type →
    SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope child reasonAt = .ok lowered →
    Certificate fuel values source context compilation.solvedRequirements reasonAt scope child lowered)

include unique found form typed special readPolicy leafPolicy accepted extract in
theorem accepted_root : Certificate fuel values source context compilation.solvedRequirements reasonAt scope id code :=
  of_functions unique found form typed special readPolicy leafPolicy accepted extract

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ child location, faults (.uninitializedLocation location) (reasonAt child))

include unique found form typed special readPolicy leafPolicy accepted extract sameSource sameLedger runtime uninitialized in
theorem accepted_reflects
    {mapping : LocationMap} {world : StoreTyping} {admin : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      admin scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expression program stages invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type code.type (FaultRep faults) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects functions program stages invocation sameSource sameLedger runtime uninitialized
    (accepted_root unique found form typed special readPolicy leafPolicy accepted extract)
    (sameSource ▸ found) environments heaps locals agrees evaluated

include unique found form typed special readPolicy leafPolicy accepted extract sameSource sameLedger runtime uninitialized in
theorem accepted_preserves (extension : SourceCoreRawMetadata.Extends values.registry registry)
    {mapping : LocationMap} {world : StoreTyping} {admin : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.Outcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      admin scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Staging.Recursive.Expression program stages invocation context environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type code.type (FaultRep faults) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves functions program stages invocation sameSource sameLedger runtime uninitialized unique extension
    (accepted_root unique found form typed special readPolicy leafPolicy accepted extract)
    (sameSource ▸ found) environments heaps locals agrees trace
end Accepted

section Static
variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id child : ExpressionId} {node childNode : ExpressionNode}
  {code : SourceCoreBasic.LoweredExpr}

theorem accepted_leaf {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {budget : Nat} {compilation : SourceCoreFunctions.Context}
    (found : source.lookupExpression? id = some node) (atomic : CompatibleExpressionLiterals.Atomic node.form)
    (unitType : node.form = .tuple [] → node.type = .unit)
    (special : ∀ action remaining, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation action remaining source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt = .ok code) :
    Certificate fuel values source context compilation.solvedRequirements reasonAt scope id code :=
  literal (CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted)

/-- Three occurrences retain the same real leaf receipt three times, in order. -/
theorem repeated_three
    (header : CompatibleExpressionTuples.Header values source id node [child, child, child]
      [childNode.type, childNode.type, childNode.type] [code, code, code])
    (found : source.lookupExpression? child = some childNode)
    (leaf : Certificate fuel values source context solved reasonAt scope child code) :
    Certificate fuel values source context solved reasonAt scope id (SourceCoreCalls.packArguments [code, code, code]) := by
  obtain ⟨tree, sites⟩ := leaf
  let entries := [(child, code)]
  have sequence : DataExpressionSequence.Tree source (Entries scope entries) scope
      [child, child, child] [childNode.type, childNode.type, childNode.type] [code, code, code] :=
    .cons found ⟨rfl, by simp [entries]⟩ (.cons found ⟨rfl, by simp [entries]⟩ (.single found ⟨rfl, by simp [entries]⟩))
  have children : ∀ current lowered, (current, lowered) ∈ entries → Tree fuel values source context solved reasonAt scope current lowered := by
    intro current lowered member
    have same : current = child ∧ lowered = code := by simpa [entries, Prod.mk.injEq] using member
    rcases same with ⟨rfl, rfl⟩
    exact tree
  have support : ∀ current lowered (member : (current, lowered) ∈ entries), Supported (children current lowered member) := by
    intro current lowered member
    have same : current = child ∧ lowered = code := by simpa [entries, Prod.mk.injEq] using member
    rcases same with ⟨rfl, rfl⟩
    exact sites
  exact ⟨.tuple header sequence children, .tuple header sequence children support⟩

theorem empty_tuple
    (header : CompatibleExpressionTuples.Header values source id node [] [] []) :
    Certificate fuel values source context solved reasonAt scope id (SourceCoreCalls.packArguments []) := by
  have children : ∀ child code, (child, code) ∈ ([] : List (ExpressionId × SourceCoreBasic.LoweredExpr)) →
      Tree fuel values source context solved reasonAt scope child code := by simp
  exact ⟨.tuple header .nil children, .tuple header .nil children (by simp)⟩

abbrev original_source_inversion := @RecursiveStageTupleMeaning.source_inv
abbrev old_unit := @Tests.SourceCoreRecursiveStagePrimitiveMeaning.source_unit
abbrev old_pair := @Tests.SourceRecursiveStageTupleExpressions.old_pair
abbrev singleton_source := @Tests.SourceRecursiveStageTupleExpressions.singleton
abbrev first_source_fault := @Tests.SourceRecursiveStageTupleExpressions.stage_at_head
abbrev later_source_fault := @Tests.SourceRecursiveStageTupleExpressions.stage_after_prefix
end Static

section Boundaries
theorem no_stage_result {faults : FunctionCalls.FaultRep} {scope : Staging.Recursive.Scope}
    {id : ExpressionId} {reason : Staging.CallGuard.Fault} {token : Word} :
    ¬ FaultRep faults (.stage scope id reason) token := by intro impossible; exact impossible

abbrev nonempty_not_atomic := @Tests.SourceRecursiveStageTupleExpressions.nonempty_tuple_not_atomic
abbrev required_parent := @Tests.SourceRecursiveStageTupleExpressions.required_parent_excluded
abbrev coerced_parent := @Tests.SourceRecursiveStageTupleExpressions.coerced_parent_excluded
end Boundaries

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def w (n : Nat) : Core.Value := .word (Word.ofNatModulo n)
private def content := String.intercalate "\n" [
  "function empty() { let unused: Word = 13; return (); }",
  "function single() returns (Word) { return (7); }",
  "function pair(a: Word, b: Word) returns ((Word, Word)) { return (a + 3, ~b); }",
  "function triple(a: Word, b: Word) returns ((Word, Bool, Word)) { return (a + 3, true, ~b); }",
  "function nested(a: Word, b: Word) returns (((Word, Bool, Word), Word, Bool)) { return ((a, true, 3), b, false); }",
  "function firstFault() returns ((Word, Word, Word)) { let first: Word; let second: Word; return (first, second, 3); }",
  "function laterFault() returns ((Word, Word, Word)) { let first: Word = 9; let second: Word; return (first, second, 3); }"
]

private def finish (code : Core.Expr) (environment : Core.Environment) (store : Core.Store) (fuel : Nat) : IO (Core.Value × Core.Store) := do
  let first := Core.runStateful fuel (.initial code environment store)
  let result := match first with
    | .outOfFuel checkpoint => Core.runStateful 300000 checkpoint
    | other => other
  match result with
  | .done value after => pure (value, after)
  | other => throw (IO.userError s!"native staged tuple incomplete: {reprStr other}")

/-- The singleton and repeated-three cases are retained IR mutations of an
actual checked group; all other root tuples come directly from the checker. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut cases := 0
  let mut lengths : List Nat := []
  for name in ["empty", "single", "pair", "triple", "nested", "firstFault", "laterFault"] do
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
    let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
      | [named] => pure named
      | _ => throw (IO.userError "actual tuple root not unique")
    let selected ← get "same full tuple specialization" (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (selected == named.specialized) "tuple full metadata changed"
    let original := selected.function.typedBody
    let binders := (SourceCoreDataPlaces.declaredBinders original).reverse
    let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
    let captured := Core.Value.closure .unit .word (.var 1) [w 97, w 101]
    let initialCells : Core.Store := [captured, w 103]
    let mut scope : SourceCoreLocalCell.Scope := []
    let mut native : Core.Environment := []
    let mut fields : Core.Store := []
    for binder in binders do
      let type ← get "tuple ordinary read actual type" (values.checked.catalog.project binder.scheme.body)
      require (binder.scheme.quantified.isEmpty && binder.schemeRequirements.isEmpty) "tuple read generalized"
      scope := scope ++ [(binder.id, type)]
      native := native ++ [.cellRef (OptionalCell.cellType type) (initialCells.length + fields.length)]
      let payload : Option Core.Value := if binder.name == "a" then some (w 11) else if binder.name == "b" then some (w 5)
        else if binder.name == "first" && name == "laterFault" then some (w 9) else none
      fields := fields ++ [match payload with | some value => .inRight .unit value | none => .inLeft type .unit]
    native := native ++ [captured]
    let store := initialCells ++ fields
    let reasonAt := fun id : ExpressionId => Word.ofNatModulo (2000 + id.occurrence.index)
    let policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
    let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .error (.unsupportedExpression ⟨⟨original.owner, 0⟩⟩ (.tuple []))
    let results := original.nodes.filterMap fun item => match item with
      | .statement statement => match statement.form with | .returnStmt (some id) => some id | _ => none
      | _ => none
    let id ← match results with | [id] => pure id | _ => throw (IO.userError "tuple return occurrence changed")
    let node ← match original.lookupExpression? id with | some node => pure node | none => throw (IO.userError "tuple node absent")
    let variants ← if name == "single" then do
      let child ← match node.form with | .group child => pure child | _ => throw (IO.userError "checked singleton group changed")
      let childNode ← match original.lookupExpression? child with | some child => pure child | none => throw (IO.userError "group child absent")
      pure ([1, 3].map fun count =>
        let ids := List.replicate count child
        {original with nodes := original.nodes.map fun item => match item with
          | .expression current => if current.id == id then .expression {current with
              form := .tuple ids, type := TypeSystem.Ty.productMany (List.replicate count childNode.type), requirements := [], coercions := []} else item
          | _ => item})
      else pure [original]
    for source in variants do
      require (source.owner == original.owner && source.inputs == original.inputs && source.roots == original.roots)
        "tuple retained source fields changed"
      let root ← match source.lookupExpression? id with | some root => pure root | none => throw (IO.userError "tuple root absent")
      let ids ← match root.form with | .tuple ids => pure ids | _ => throw (IO.userError "tuple root form changed")
      require (root.requirements.isEmpty && root.coercions.isEmpty) "tuple parent not ordinary"
      for item in source.nodes do
        match item with
        | .expression current =>
          match current.form with
          | .integerLiteral literal resolution =>
            let _ ← get "tuple actual Selected full row" (SourceCoreElaboration.validateWordIntegerLiteral selected.function.solvedRequirements current literal resolution)
            require (current.requirements == [resolution.requirement]) "tuple numeric ownership changed"
          | .reference _ (.local _) =>
            let _ ← get "tuple actual ordinary read" (SourceCoreCompatibleDataExpressions.lowerRead 100 values source scope current.id (reasonAt current.id))
          | .tuple .. | .unary .. | .binary .. =>
            require (current.requirements.isEmpty && current.coercions.isEmpty) "tuple primitive parent metadata changed"
          | _ => pure ()
        | _ => pure ()
      let ledger := selected.function.solvedRequirements
      let rows ← match ledger with
        | [] => throw (IO.userError "tuple full ledger unexpectedly empty")
        | first :: _ =>
          let extra := {first with id := ⟨(ledger.map (fun (row : SolvedRequirement) => row.id.index)).foldl max 0 + 1⟩, evidence := .assumption first.predicate}
          pure [ledger, extra :: ledger, ledger ++ [extra]]
      let compilation : SourceCoreFunctions.Context := {
        plan := compiled.indexed.base.plan, owner := named.signature.key, globals := compiled.indexed.base.globals,
        administrativePrefix := 1, solvedRequirements := ledger, internalReason := Word.zero }
      let lower := fun fuel compilation child => SourceCoreFunctions.lowerExpressionWithPolicy policy noBody fuel compilation source scope child reasonAt
      let base ← get "actual tuple root" (lower 100 compilation id)
      let originalChildren ← ids.mapM fun child => get "actual ordered tuple child" (lower 99 compilation child)
      require (base == SourceCoreCalls.packArguments originalChildren && originalChildren.length == ids.length)
        "tuple actual pack/minfuel/code/order changed"
      for complete in rows do
        let lowered ← get "tuple full unused ledger" (lower 100 {compilation with solvedRequirements := complete} id)
        require (lowered == base) "tuple full unused ledger changed code"
        let expected ← if name == "firstFault" || name == "laterFault" then do
          let missingName := if name == "firstFault" then "first" else "second"
          let missing ← match source.nodes.filterMap (fun item => match item with
              | .expression current => match current.form with
                | .reference binderName (.local _) => if binderName == missingName then some current.id else none
                | _ => none
              | _ => none) with
            | [missing] => pure missing | _ => throw (IO.userError "actual tuple missing occurrence changed")
          pure (Core.Value.inLeft lowered.type (.word (reasonAt missing)))
          else do
            let payload := if name == "empty" then Core.Value.unit
              else if name == "single" then if ids.length == 1 then w 7 else .pair (w 7) (.pair (w 7) (w 7))
              else if name == "pair" then .pair (w 14) (.word (Word.ofNatModulo 5).bitNot)
              else if name == "triple" then .pair (w 14) (.pair (.bool true) (.word (Word.ofNatModulo 5).bitNot))
              else .pair (.pair (w 11) (.pair (.bool true) (w 3))) (.pair (w 5) (.bool false))
            pure (.inRight .word payload)
        for fuel in [0, 1, 17, 300000] do
          let result ← finish lowered.expression native store fuel
          require (result == (expected, store)) "tuple result/first fault/full captured store/resume changed"
      lengths := lengths ++ [ids.length]
      cases := cases + 1
  require (cases == 8 && lengths == [0, 1, 3, 2, 3, 3, 3, 3]) s!"tuple native scope changed {cases}/{lengths}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "native staged tuples" content
    ["empty", "single", "pair", "triple", "nested", "firstFault", "laterFault"]
  inspect compiled
  IO.println "staged native tuples: actual ordered code/0-1-2-3/nested/duplicate/full Selected rows/unused ledger/first-later fault/full captured heap/resume GREEN"

end Tests.SourceCoreRecursiveStageTupleMeaning
end
