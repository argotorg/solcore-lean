import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralNativeTyping

/-! Actual lowering of a logical operation above product-key indexing closes its
base and both key components without native child callbacks. Hidden slots and
ambient definitions remain arbitrary. The existing recursive/general IO suites
exercise the production compiler's tags, lazy initialization, faults and resume. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreGeneralExpressionNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionGeneral CompatibleExpressionScalarNativeTyping
open CompatibleExpressionGeneralNativeTyping CompatibleCatalogNominalCoverage

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"index_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "index_meaning.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def keyType : TypeSystem.Ty := .product .bool .bool
private def mappingType : TypeSystem.Ty := .mapping keyType .bool
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono mappingType, [], false, none⟩
private def baseNode : ExpressionNode := { id := id 0, span, type := mappingType, form := .reference "table" (.local binder.id) }
private def trueNode : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def falseNode : ExpressionNode := { id := id 2, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def keyNode : ExpressionNode := { id := id 3, span, type := keyType, form := .tuple [id 1, id 2] }
private def indexNode : ExpressionNode := { id := id 4, span, type := .bool, form := .index (id 0) (id 3) }
private def unaryNode : ExpressionNode := { id := id 5, span, type := .bool, form := .unary .logicalNot (id 4) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression (id 5)], nodes := [.expression baseNode, .expression trueNode, .expression falseNode, .expression keyNode, .expression indexNode, .expression unaryNode] }
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem keyAdmitted : TypeAdmissible context keyType := .product boolAdmitted boolAdmitted
private theorem mappingAdmitted : TypeAdmissible context mappingType := .mapping keyAdmitted boolAdmitted
private theorem baseTyped : ExpressionHasType source context (id 0) mappingType := by
  apply ExpressionHasType.ofOrdinary (node := baseNode) (rawType := mappingType) (lookupExpression?_sound (by rfl))
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible mappingAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply mappingType)
      (by simp) (by intro _ member; cases member) (.nil)))) mappingAdmitted mappingAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem trueTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := trueNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem falseTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := falseNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean false)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem keyTyped : ExpressionHasType source context (id 3) keyType := by
  apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := keyType)
    (lookupExpression?_sound (by cbv)) (.tuple (.cons trueTyped (.cons falseTyped (.nil _)))) keyAdmitted keyAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped : ExpressionHasType source context (id 4) .bool := by
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.index baseTyped keyTyped) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem unaryTyped : ExpressionHasType source context (id 5) .bool := by
  apply ExpressionHasType.ofOrdinary (node := unaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.unary indexTyped .logicalNot) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexSyntax : CompatibleExpressionGeneral.Syntax source (id 4) :=
  .index (node := indexNode) (keyNode := keyNode) (by cbv) rfl (by cbv)
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := baseNode) (by cbv) rfl)))))))
    (.pair (node := keyNode) (by cbv) rfl
      (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := trueNode) (by cbv) (.bool _ _))))))))
      (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := falseNode) (by cbv) (.bool _ _)))))))))
private theorem syntaxTree : CompatibleExpressionGeneral.Syntax source (id 5) :=
  .unary (node := unaryNode) (by cbv) rfl indexSyntax
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private theorem nativeExists : (checked.catalog.project mappingType).toOption.isSome = true := by cbv
private def nativeType := (checked.catalog.project mappingType).toOption.get nativeExists
private theorem projected : checked.catalog.project mappingType = .ok nativeType := by cbv
private def scope : SourceCoreLocalCell.Scope := [(binder.id, nativeType)]
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope context := by
  intro actual declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst actual
    have actual : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := by rfl
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected
private abbrev policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
private theorem certified {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason) = .ok code) :
    Tree 100 values source context [] (fun _ => reason) scope (id 5) code :=
  tree_of_functions unique declarations (by rfl) rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) unaryTyped accepted

private theorem actual_factory : SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType] = .ok checked := by cbv

private theorem visibleTypes : ScopeWellFormed checked.catalog.definitions scope := by
  apply ScopeWellFormed.prepend (.empty _) binder.id
  exact Ty.isWellFormed_sound (by cbv)

/-- Independent source typing, actual lowering and factory acceptance close
all native base/key/parent obligations for this compound-key example. -/
theorem product_key_below_unary_native {code : SourceCoreBasic.LoweredExpr} {definitions : DataEnvironment}
    (administrative : Core.Context)
    (extension : checked.catalog.definitions.Extends definitions)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5)
      (fun _ => reason) = .ok code) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) code := by
  have shaped := prepare_shapes actual_factory
  rw [← SourceCoreCompatibleCatalog.prepare_signatures actual_factory] at shaped
  exact general_native_at shaped (prepare_complete actual_factory) visibleTypes administrative extension (certified accepted)

private def compiledAction := SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope
  (id 5) (fun _ => reason)

theorem actual_contextual_general_native
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
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment} (administrative : Core.Context)
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (ordinary : CompatibleExpressionGeneral.Ordinary source locals compilation.owner)
    (unique : SourceSemantics.NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionGeneral.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : SourceSemantics.ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  CompatibleExpressionGeneralNativeTyping.contextual_native visibleTypes administrative registered ordinary unique closed residual declarations sourceSignatures
    syntaxTree found sourceTyped readPolicy lowerPolicy leafPolicy accepted extension


def run : IO Unit := do
  match compiledAction with
  | .error error => throw (IO.userError s!"product-key native fixture failed to compile: {repr error}")
  | .ok code =>
    if code.type != .bool then throw (IO.userError "product-key parent result type changed")
    if Core.infer? (SourceCoreLocalCell.coreContext scope ++ [.integer, .function .unit .word])
        code.expression checked.catalog.definitions != some (LanguageResult.resultType .bool) then
      throw (IO.userError "product-key native fixture failed native type inference under hidden slots")
  IO.println "general expression native typing: actual product-key parent, hidden slots and native inference GREEN"

end Tests.SourceCoreGeneralExpressionNativeTyping
