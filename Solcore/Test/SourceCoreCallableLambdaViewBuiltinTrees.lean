import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinTrees
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualBuiltins
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewBuiltinTrees
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionBuiltins CallableLambdaViewEdits CallableLambdaBodyReachability
namespace Nested
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_builtin_view", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_builtin_view.solc"⟩, 0, 1⟩
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
private def parentNode : ExpressionNode := {id := id 6, span, type := .function .unit .word, form := .lambda [] .word []}
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression (id 5)], nodes := [.expression literalNode, .expression toNode,
    .expression innerNode, .expression fromNode, .expression outerNode, .expression groupNode, .expression parentNode]}
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
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem certified (native : SourceCoreGeneralFunctions.CallableContext) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 6 compilation source [] (id 5) reasonAt = .ok code) :
    Tree 100 values source context [] reasonAt [] (id 5) code :=
  tree_of_functions unique (by intro actual declared index native selected; cases selected) rfl rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ native [] rfl
    (fun _ _ _ found => noCoercions _ _ found) syntaxTree (by cbv) groupTyped accepted

private def view := SourceCoreEvidence.withNode source {parentNode with type := .unit}
private def footprint : List NodeId := ([0, 1, 2, 3, 4, 5] : List Nat).map (fun n => .expression (id n))
private theorem edited : LocalView source view [parentNode.id] := withNode unique (by rfl) rfl rfl
private theorem reference_closed {expression : ExpressionId} {node : ExpressionNode}
    (member : NodeId.expression expression ∈ footprint) (found : source.lookupExpression? expression = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp only [footprint, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, NodeId.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
    subst node
    simp only [literalNode, toNode, innerNode, fromNode, outerNode, groupNode,
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

/-- The actual builtin lowering retains both ordered conversions and contracted
callee code while the enclosing lambda header really changes. -/
theorem accepted_nested (native : SourceCoreGeneralFunctions.CallableContext) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 6 compilation source [] (id 5) reasonAt = .ok code) :
    source ≠ view ∧ Tree 100 values view context [] reasonAt [] (id 5) code :=
  ⟨by decide, CallableLambdaViewBuiltinTrees.builtins edited avoids (certified native accepted) (.root (by simp [source]))⟩

theorem original_nested {code : SourceCoreBasic.LoweredExpr}
    (tree : Tree 100 values view context [] reasonAt [] (id 5) code) :
    Tree 100 values source context [] reasonAt [] (id 5) code :=
  CallableLambdaViewBuiltinTrees.builtins_original edited avoids tree (.root (by simp [source]))

/-- Actual argument/callee reachability cannot be silently excluded. -/
theorem changed_operand_rejected : ¬ Avoids source source.roots [literalNode.id] := by
  intro fresh
  have grouped : Reaches source source.roots (.expression (id 5)) := .root (by simp [source])
  have outer : Reaches source source.roots (.expression (id 4)) :=
    .expression grouped (by rfl) (by simp [groupNode, ExpressionForm.references])
  have inner : Reaches source source.roots (.expression (id 2)) :=
    .expression outer (by rfl) (by simp [outerNode, ExpressionForm.references])
  have argument : Reaches source source.roots (.expression literalNode.id) :=
    .expression inner (by rfl) (by simp [innerNode, ExpressionForm.references, literalNode])
  exact fresh literalNode.id (by simp) argument

end Nested

/-- Actual ordinary typed lowering at a view yields the canonical Tree under
reachability. Independent typing and syntax refer to that actual view; the
conclusion does not assert canonical compiler acceptance or canonical typing. -/
theorem builtin_original_from_contextual
    {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    {values : SourceCoreCompatibleValues.Context} {readFuel : Nat} {context : SourceSemantics.Context}
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {compilation : SourceCoreFunctions.Context} {native : SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {skip : Option ExpressionId}
    {fuel : Nat} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {code : SourceCoreBasic.LoweredExpr}
    (ordinary : CompatibleExpressionBuiltins.Ordinary view locals compilation.owner) (unique : NodeOccurrencesUnique view)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations view scope context)
    (signatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionBuiltins.Syntax view id) (found : view.lookupExpression? id = some node)
    (typed : ExpressionHasType view context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (reached : Reaches source roots (.expression id))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation values.checked.signatures locals parents
      assignments diagnostics compilation (some native) parent skip fuel view scope id reasonAt = .ok code) :
    CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt scope id code :=
  CallableLambdaViewBuiltinTrees.builtins_original edited avoids
    (CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures syntaxTree found typed
      readPolicy lowerPolicy leafPolicy accepted) reached

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α :=
  SourceCompilerFeatureSupport.get label
private def require := SourceCompilerFeatureSupport.require
/-- The enclosing integer result uses the existing staged admission profile.
Each lambda is explicitly monomorphic and really emitted by the indexed factory. -/
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function nested(a: Word, b: Word) returns (integer) { let f: function() returns (integer) = lam() -> integer { return integerSub(integerAdd(wordToInteger(a), wordToInteger(b)), wordToInteger(b)); }; return 0; }",
    "function parents(a: Word, b: Word) returns (integer) { let f: function() returns (integer) = lam() -> integer { return integerSub(wordToInteger(a), wordToInteger(b)); }; return 0; }",
    "function compared(a: Word, b: Word) returns (integer) { let f: function() returns (Bool) = lam() -> Bool { return integerEq(wordToInteger(a), wordToInteger(a)) && !integerLt(wordToInteger(a), wordToInteger(b)); }; return 0; }",
    "function construct(a: Word, b: Word) returns (integer) { let f: function() returns (Box<integer>) = lam() -> Box<integer> { return Box(integerSub(wordToInteger(a), wordToInteger(b))); }; return 0; }",
    "function member(a: Word, b: Word) returns (integer) { let f: function() returns (Box<integer>) = lam() -> Box<integer> { return Box(integerSub(wordToInteger(a), wordToInteger(b))); }; return 0; }",
    "function key(a: Word, b: Word) returns (integer) { let f: function() returns (integer) = lam() -> integer { let m: mapping((Bool, Bool) => Word); return wordToInteger(m[(integerEq(wordToInteger(b), wordToInteger(b)), integerLt(wordToInteger(b), wordToInteger(b)))]); }; return 0; }",
    "function skipped(a: Word, b: Word) returns (integer) { let f: function() returns (integer) = lam() -> integer { let n: mapping(Bool => Word); return integerEq(wordToInteger(a), wordToInteger(a)) ? integerSub(wordToInteger(a), wordToInteger(b)) : wordToInteger(n[true]); }; return 0; }",
    "function failed() returns (integer) { let f: function() returns (integer) = lam() -> integer { let m: mapping(Bool => Word); let missing: Word; return integerSub(wordToInteger(m[false]), wordToInteger(missing)); }; return 0; }"]}] }

private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | budget + 1, source, id => match source.lookupExpression? id with
    | none => []
    | some node => node :: (match node.form with
      | .index base key => reached budget source base ++ reached budget source key
      | .group inner | .unary _ inner | .member inner _ _ => reached budget source inner
      | .binary left _ right => reached budget source left ++ reached budget source right
      | .conditional condition first second => reached budget source condition ++ reached budget source first ++ reached budget source second
      | .tuple ids | .constructor _ ids | .call _ ids _ => ids.flatMap (reached budget source)
      | _ => [])

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (callables : SourceCoreGeneralFunctions.CallableContext) (original : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (header : ExpressionNode)
    (name : String) (originalExpression : ExpressionId) : IO Unit := do
  let originalRoot ← match original.lookupExpression? originalExpression with
    | some node => pure node | none => throw (IO.userError "builtin view original root missing")
  let (source, expression) := if name == "member" then
    let member : ExpressionNode := {id := ⟨⟨original.owner, 100000⟩⟩, span := originalRoot.span, type := .integer, form := .member originalExpression "0" 0}
    ({original with roots := [.expression member.id], nodes := original.nodes ++ [.expression member]}, member.id)
    else if name == "parents" then
      let negated : ExpressionNode := {id := ⟨⟨original.owner, 100000⟩⟩, span := originalRoot.span, type := .integer, form := .unary .bitNot originalExpression}
      let pair : ExpressionNode := {id := ⟨⟨original.owner, 100001⟩⟩, span := originalRoot.span, type := .product .integer .integer, form := .tuple [negated.id, originalExpression]}
      let group : ExpressionNode := {id := ⟨⟨original.owner, 100002⟩⟩, span := originalRoot.span, type := pair.type, form := .group pair.id}
      ({original with roots := [.expression group.id], nodes := original.nodes ++ [negated, pair, group].map Node.expression}, group.id)
    else (original, originalExpression)
  let nodes := reached 100 source expression
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for id in ids do
    let binder ← get "builtin view binder" (SourceCoreDataPlaces.rootBinder source id)
    let native ← get "builtin view binder projection" (checked.catalog.project binder.scheme.body)
    let (initializer, expected) ← match binder.scheme.body with
      | .mapping key result => do
        let encoded ← get "builtin view empty mapping" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key result []))
        values := encoded.context
        pure (OptionalCell.allocate native, some encoded.value)
      | .word =>
        if binder.name == "missing" then pure (OptionalCell.allocate native, none)
        else
          let word := Word.ofNatModulo (if binder.name == "a" then 7 else 3)
          pure (OptionalCell.allocateInitialized native (.word word), some (.word word))
      | other => throw (IO.userError s!"builtin view unexpected binder {reprStr other}")
    bindings := bindings ++ [(binder, native, initializer, expected)]
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "builtin view diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := [], internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let policy := {SourceCoreCompatibleDataExpressions.functionPolicy 150 values with
    callables := SourceCoreGeneralFunctions.callablePolicy (some callables) []}
  let modified := SourceCoreEvidence.withNode source {header with type := .unit}
  let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
  let before := SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 150 compilation source scope expression reasonAt
  let after := SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 150 compilation modified scope expression reasonAt
  let lowered ← get s!"builtin view actual compiler {name}" before
  let same ← get s!"builtin view modified compiler {name}" after
  require (reprStr lowered == reprStr same) "builtin view changed code, operand order or contract"
  require (source != modified) "builtin view header was unchanged"
  let rootNode ← match source.lookupExpression? expression with
    | some node => pure node | none => throw (IO.userError "builtin view selected root missing")
  let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
  let adminType := Ty.function .unit frame.type
  let adminExpr := Expr.lambda .unit frame.type (SourceCoreCallableIndexedFrames.empty frame)
  let body := bindings.foldl (fun body (_, _, initializer, _) => Expr.letE initializer body)
    (.letE (.integer 99) (lowered.expression.weakenAt 0))
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
    .letE (.newCell adminType adminExpr) body, checked.catalog.definitions ++ [frame.definition]⟩
  require native.check s!"builtin view {name} failed Core checker"
  for fuel in [0, 5, 50, 1000] do
    let completed := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 30000 checkpoint
      | other => other
    match completed with
    | .done result store =>
      require (store.length ≥ bindings.length + 1) "builtin view lost the retained input store prefix"
      require (store[0]? == some (.closure .unit frame.type (SourceCoreCallableIndexedFrames.empty frame) []))
        "builtin view changed ambient closure"
      if name == "failed" then
        let failed ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "builtin view missing first fault")
        require (result == .inLeft lowered.type (.word (reasonAt failed.id))) "builtin view first fault changed"
      else
        let payload ← match result with
          | .inRight .word payload => pure payload
          | _ => throw (IO.userError s!"builtin view {name} did not succeed: {reprStr result}")
        let decoded ← get "builtin view decoded output" (SourceCoreCompatibleValues.decode 100 values rootNode.type payload)
        match name, decoded with
        | "nested", .integer 7 | "member", .integer 4 | "skipped", .integer 4 | "key", .integer 0
        | "parents", .product (.integer (-5)) (.integer 4) | "compared", .bool true => pure ()
        | "construct", .constructed retained [.integer 4] =>
          let .constructor instantiation _ := originalRoot.form | throw (IO.userError "builtin view constructor source missing")
          require (retained == instantiation) "builtin view erased raw constructor metadata"
        | _, other => throw (IO.userError s!"builtin view {name} changed output: {reprStr other}")
      for ((binder, type, _, expected), position) in bindings.zipIdx do
        let expectedCell := match expected with
          | some value => if binder.name == "n" then Value.inLeft type .unit else .inRight .unit value
          | none => .inLeft type .unit
        require (store[bindings.length - position]? == some expectedCell)
          s!"builtin view {name} changed ordered/lazy effects at {binder.name}"
    | other => throw (IO.userError s!"builtin view {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let program ← get "builtin view checker" (checkProgram workspace)
  let requests := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program requests 500 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"builtin view specialization: {reprStr other}")
  let automatic ← get "builtin view base factory" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let indexed ← get "builtin view indexed factory" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let mut count := 0
  for template in indexed.ancestry.templates.lambdas do
    let source := template.context.inventory.source
    let .lambda _ _ statements := template.node.form | throw (IO.userError "builtin view lambda form missing")
    let expression ← match statements.findSome? fun id => match source.lookupStatement? id with
      | some node => match node.form with | .returnStmt (some expression) => some expression | _ => none
      | none => none with
      | some expression => pure expression | none => throw (IO.userError "builtin view lambda return missing")
    let name := (program.signatures.functions.find? (·.id == template.owner.declaration)).map (·.name) |>.getD ""
    inspect automatic.prepared indexed.ancestry.graph.inputs.callable source template.owner template.node name expression
    count := count + 1
  require (count == 8) s!"builtin view lambda cases missing: {count}"
  IO.println "lambda builtin views: nested ordered calls, operator/constructor/member/product-key parents, raw headers, lazy/fault effects, actual typed slots and resume GREEN"

end Tests.SourceCoreCallableLambdaViewBuiltinTrees
