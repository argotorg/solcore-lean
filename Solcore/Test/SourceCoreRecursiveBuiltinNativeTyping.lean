import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinNativeTyping
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.ProgramChecking

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
