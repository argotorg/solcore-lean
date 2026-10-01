import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewIndexedTrees
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualGeneral
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualTyped
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewIndexedTrees
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionGeneral
open CallableLambdaViewEdits CallableLambdaBodyReachability
namespace ProductKey

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_index_view", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_index_view.solc"⟩, 0, 4⟩
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
private def parentNode : ExpressionNode := {id := id 6, span, type := .function .unit .bool, form := .lambda [] .bool []}
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression (id 5)], nodes := [.expression baseNode, .expression trueNode, .expression falseNode, .expression keyNode, .expression indexNode, .expression unaryNode, .expression parentNode] }
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
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

private def view := SourceCoreEvidence.withNode source {parentNode with type := .unit}
private def footprint : List NodeId := ([0, 1, 2, 3, 4, 5] : List Nat).map (fun n => .expression (id n))
private theorem edited : LocalView source view [parentNode.id] :=
  withNode unique (by rfl) rfl rfl
private theorem reference_closed {expression : ExpressionId} {node : ExpressionNode}
    (member : NodeId.expression expression ∈ footprint) (found : source.lookupExpression? expression = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp only [footprint, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, NodeId.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
    subst node
    simp only [baseNode, trueNode, falseNode, keyNode, indexNode, unaryNode,
      ExpressionForm.references, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at edge <;>
      rcases edge with rfl | rfl <;> simp [footprint, id]
private theorem reached_member {node : NodeId} (reached : Reaches source source.roots node) : node ∈ footprint := by
  induction reached with
  | @root rootId member =>
    have same : rootId = NodeId.expression (id 5) := by simpa [source] using member
    rw [same]
    simp [footprint]
  | expression _ found edge ih => exact reference_closed ih found edge
  | statement _ _ _ ih => simp [footprint] at ih
private theorem avoids : Avoids source source.roots [parentNode.id] := by
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  have impossible := reached_member reached
  simp [parentNode, footprint, id] at impossible

/-- The product-key comparator is retained exactly; no scalar-key premise is
introduced when transporting a successfully compiled general expression. -/
theorem accepted_product_key {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason) = .ok code) :
    source ≠ view ∧ Tree 100 values view context [] (fun _ => reason) scope (id 5) code :=
  ⟨by decide, CallableLambdaViewIndexedTrees.general edited avoids (certified accepted) (.root (by simp [source]))⟩

theorem original_product_key {code : SourceCoreBasic.LoweredExpr}
    (tree : Tree 100 values view context [] (fun _ => reason) scope (id 5) code) :
    Tree 100 values source context [] (fun _ => reason) scope (id 5) code :=
  CallableLambdaViewIndexedTrees.general_original edited avoids tree (.root (by simp [source]))

theorem product_key_is_not_scalar : ¬ CompatibleExpressionIndices.SourceScalar keyType := by
  intro scalar
  cases scalar

end ProductKey

/-- Actual ordinary typed lowering at a view yields the canonical Tree under
reachability. Independent typing and syntax refer to that actual view; the
conclusion does not assert canonical compiler acceptance or canonical typing. -/
theorem typed_original_from_contextual
    {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    {values : SourceCoreCompatibleValues.Context} {readFuel : Nat} {context : SourceSemantics.Context}
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {compilation : SourceCoreFunctions.Context} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {skip : Option ExpressionId}
    {fuel : Nat} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {code : SourceCoreBasic.LoweredExpr}
    (ordinary : CompatibleExpressionTyped.Ordinary view locals compilation.owner) (unique : NodeOccurrencesUnique view)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations view scope context)
    (signatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionTyped.Syntax view id) (found : view.lookupExpression? id = some node)
    (typed : ExpressionHasType view context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (reached : Reaches source roots (.expression id))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation values.checked.signatures locals parents
      assignments diagnostics compilation native parent skip fuel view scope id reasonAt = .ok code) :
    CompatibleExpressionTyped.Tree readFuel values source context compilation.solvedRequirements reasonAt scope id code :=
  CallableLambdaViewIndexedTrees.typed_original edited avoids
    (CompatibleExpressionTyped.tree_of_contextual ordinary unique closed residual declarations signatures syntaxTree found typed
      readPolicy lowerPolicy leafPolicy accepted) reached

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α :=
  SourceCompilerFeatureSupport.get label
private def require := SourceCompilerFeatureSupport.require
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function scalar() returns (function() returns (Bool)) { return lam() -> Bool { let m: mapping(Bool => Bool); return !m[true]; }; }",
    "function product() returns (function() returns (Bool)) { return lam() -> Bool { let m: mapping((Bool, Bool) => Bool); return m[(true, false)] || !m[(false, true)]; }; }",
    "function skipped() returns (function() returns (Bool)) { return lam() -> Bool { let m: mapping(Bool => Bool); let n: mapping(Bool => Bool); return true ? !m[false] : n[true]; }; }",
    "function before_fault() returns (function() returns (Bool)) { return lam() -> Bool { let m: mapping(Bool => Bool); let missing: Bool; return m[false] || missing; }; }",
    "function no_default() returns (function() returns (Box<Word>)) { return lam() -> Box<Word> { let m: mapping(Bool => Box<Word>); return m[true]; }; }",
    "function proxy() returns (function() returns (Bool)) { return lam() -> Bool { let m: mapping(@Word => Bool); return m[@Word]; }; }"]}] }

private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | budget + 1, source, id => match source.lookupExpression? id with
    | none => []
    | some node => node :: (match node.form with
      | .index base key => reached budget source base ++ reached budget source key
      | .group inner | .unary _ inner | .member inner _ _ => reached budget source inner
      | .binary left _ right => reached budget source left ++ reached budget source right
      | .conditional condition first second => reached budget source condition ++ reached budget source first ++ reached budget source second
      | .tuple ids | .constructor _ ids => ids.flatMap (reached budget source)
      | _ => [])

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (header : ExpressionNode)
    (name : String) (expression : ExpressionId) : IO Unit := do
  let nodes := reached 100 source expression
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for id in ids do
    let binder ← get "index view binder" (SourceCoreDataPlaces.rootBinder source id)
    let native ← get "index view binder projection" (checked.catalog.project binder.scheme.body)
    let (initializer, expected) ← match binder.scheme.body with
      | .mapping key result => do
        let encoded ← get "index view empty mapping" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key result []))
        values := encoded.context
        pure (OptionalCell.allocate native, some encoded.value)
      | .bool => pure (OptionalCell.allocate native, none)
      | other => throw (IO.userError s!"index view unexpected binder {reprStr other}")
    bindings := bindings ++ [(binder, native, initializer, expected)]
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "index view diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := [], internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let policy := SourceCoreCompatibleDataExpressions.functionPolicy 150 values
  let modified := SourceCoreEvidence.withNode source {header with type := .unit}
  let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
  let before := SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 150 compilation source scope expression reasonAt
  let after := SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 150 compilation modified scope expression reasonAt
  let lowered ← get s!"index view actual compiler {name}" before
  let same ← get s!"index view modified compiler {name}" after
  require (reprStr lowered == reprStr same) "index view changed accepted code/header/comparator"
  require (source != modified) "index view header was unchanged"
  let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
  let adminType := Ty.function .unit frame.type
  let adminExpr := Expr.lambda .unit frame.type (SourceCoreCallableIndexedFrames.empty frame)
  let body := bindings.foldl (fun body (_, _, initializer, _) => Expr.letE initializer body)
    (.letE (.integer 99) (lowered.expression.weakenAt 0))
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
    .letE (.newCell adminType adminExpr) body, checked.catalog.definitions ++ [frame.definition]⟩
  require native.check s!"index view {name} failed Core checker"
  for fuel in [0, 5, 50, 1000] do
    let completed := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 30000 checkpoint
      | other => other
    match completed with
    | .done result store =>
      require (store[0]? == some (.closure .unit frame.type (SourceCoreCallableIndexedFrames.empty frame) []))
        "index view comparator changed ambient closure"
      if name == "before_fault" then
        let failed ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "index view missing first fault")
        require (result == .inLeft lowered.type (.word (reasonAt failed.id))) "index view first fault changed"
      else if name == "no_default" then
        let indexed ← match source.lookupExpression? expression with
          | some node => pure node | none => throw (IO.userError "index view indexed root missing")
        let .index base _ := indexed.form | throw (IO.userError "index view root is not index")
        let baseNode ← match source.lookupExpression? base with
          | some node => pure node | none => throw (IO.userError "index view mapping metadata missing")
        let .mapping key value := baseNode.type | throw (IO.userError "index view raw mapping type missing")
        let tag ← match values.registry.id? (.mapping key value) with
          | some tag => pure tag | none => throw (IO.userError "index view raw mapping header missing")
        require (result == .inLeft lowered.type (.word ((reasonAt expression).add tag))) "index view missing-default token changed"
      else
        require (result == .inRight .word (.bool (name != "proxy"))) "index view success changed"
      for ((binder, type, _, expected), position) in bindings.zipIdx do
        let expectedCell := match expected with
          | some value => if binder.name == "n" then Value.inLeft type .unit else .inRight .unit value
          | none => .inLeft type .unit
        require (store[bindings.length - position]? == some expectedCell)
          s!"index view {name} changed lazy initialization at {binder.name}"
    | other => throw (IO.userError s!"index view {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let program ← get "index view checker" (checkProgram workspace)
  let requests := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program requests 500 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"index view specialization: {reprStr other}")
  let automatic ← get "index view base factory" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let indexed ← get "index view indexed factory" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let mut count := 0
  for template in indexed.ancestry.templates.lambdas do
    let source := template.context.inventory.source
    let .lambda _ _ statements := template.node.form | throw (IO.userError "index view lambda form missing")
    let expression ← match statements.findSome? fun id => match source.lookupStatement? id with
      | some node => match node.form with | .returnStmt (some expression) => some expression | _ => none
      | none => none with
      | some expression => pure expression | none => throw (IO.userError "index view lambda return missing")
    let name := (program.signatures.functions.find? (·.id == template.owner.declaration)).map (·.name) |>.getD ""
    inspect automatic.prepared source template.owner template.node name expression
    count := count + 1
  require (count == 6) s!"index view lambda cases missing: {count}"
  IO.println "lambda indexed views: scalar/product/proxy keys, exact comparator/default metadata, lazy effects, failures, typed hidden slot and resume GREEN"

end Tests.SourceCoreCallableLambdaViewIndexedTrees
