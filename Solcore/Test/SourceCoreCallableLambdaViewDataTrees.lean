import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewRecursiveTrees
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualRecursive

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewDataTrees
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionRecursive
open CallableLambdaViewEdits CallableLambdaBodyReachability

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_data_view", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_data_view.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def sourceType : TypeSystem.Ty := .nominal owner []
private def firstSignature : ProgramDataConstructorSignature :=
  ⟨⟨owner, 0⟩, "First", [.bool, .bool], ⟨span, ⟨[], ⟨span, "First"⟩, none⟩⟩⟩
private def secondSignature : ProgramDataConstructorSignature :=
  ⟨⟨owner, 1⟩, "Second", [.bool, .bool], ⟨span, ⟨[], ⟨span, "Second"⟩, none⟩⟩⟩
private def signature : ProgramDataSignature := {
  id := owner, name := "Row", parameters := [], constructors := [firstSignature, secondSignature]
  source := ⟨span, ⟨none, ⟨span, "Row"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def instantiation : DataConstructorInstantiation := ⟨secondSignature.id, [], [.bool, .bool], sourceType⟩
private def boolean : ExpressionNode := { id := id 0, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def constructorNode : ExpressionNode := { id := id 1, span, type := sourceType, form := .constructor instantiation [id 0, id 0] }
private def memberNode : ExpressionNode := { id := id 2, span, type := .bool, form := .member (id 1) "1" 1 }
private def unaryNode : ExpressionNode := { id := id 3, span, type := .bool, form := .unary .logicalNot (id 2) }
private def wrappedNode : ExpressionNode := { id := id 4, span, type := sourceType, form := .constructor instantiation [id 3, id 2] }
private def selectedNode : ExpressionNode := { id := id 5, span, type := .bool, form := .member (id 4) "0" 0 }
private def conditionalNode : ExpressionNode := { id := id 6, span, type := sourceType, form := .conditional (id 5) (id 4) (id 1) }
private def pairedNode : ExpressionNode := { id := id 7, span, type := .product sourceType .bool, form := .tuple [id 6, id 5] }
private def parent : ExpressionNode := {id := id 8, span, type := .function .unit .bool, form := .lambda [] .bool []}
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 7)], nodes := [.expression boolean, .expression constructorNode, .expression memberNode,
      .expression unaryNode, .expression wrappedNode, .expression selectedNode, .expression conditionalNode, .expression pairedNode, .expression parent] }
private def context : SourceSemantics.Context := .ofSignatures signatures
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index native selected; cases selected
private theorem instanceValid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation := by
  refine .intro signature secondSignature (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    (by simp [signature]) rfl rfl ⟨by simp [signature], by simp [ParameterSubstitution.domain, instantiation, signature]⟩ ?_ rfl rfl
  intro parameter replacement member; cases member
private theorem nominalAdmitted : TypeAdmissible context sourceType :=
  ⟨TypeParameterBindersWellFormed.ofSignatures signatures,
    .nominal signature [] (by simp [context, SourceSemantics.Context.ofSignatures, signatures]) rfl .nil⟩
private theorem boolAdmitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
private theorem boolTyped : ExpressionHasType source context (id 0) .bool := by
  apply ExpressionHasType.ofOrdinary (node := boolean) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem constructorTyped : ExpressionHasType source context (id 1) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := constructorNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.constructor instanceValid.toAdmissible (.cons boolTyped (.cons boolTyped (.nil _)))) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem projection (index : Nat) (inBounds : index = 0 ∨ index = 1) : UniformMemberProjection context sourceType index .bool := by
  refine .intro (dataType := signature) (substitution := []) (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    ⟨by simp [signature], by simp [ParameterSubstitution.domain, signature]⟩ rfl nominalAdmitted boolAdmitted (by simp [signature]) ?_ ?_
  · intro constructor member
    simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rcases inBounds with rfl | rfl <;> rfl
  · intro actual admissible resultType
    cases admissible with
    | intro dataType constructor dataMember constructorMember _ _ _ _ payloads _ =>
      have same : dataType = signature := by simpa [context, SourceSemantics.Context.ofSignatures, signatures] using dataMember
      subst dataType
      simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at constructorMember
      rcases constructorMember with rfl | rfl <;> rw [payloads] <;> rcases inBounds with rfl | rfl <;> rfl
private theorem memberTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := memberNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.member constructorTyped (projection 1 (.inr rfl))) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem unaryTyped : ExpressionHasType source context (id 3) .bool := by
  apply ExpressionHasType.ofOrdinary (node := unaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.unary memberTyped .logicalNot) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem wrappedTyped : ExpressionHasType source context (id 4) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := wrappedNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.constructor instanceValid.toAdmissible (.cons unaryTyped (.cons memberTyped (.nil _)))) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem selectedTyped : ExpressionHasType source context (id 5) .bool := by
  apply ExpressionHasType.ofOrdinary (node := selectedNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.member wrappedTyped (projection 0 (.inl rfl))) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem conditionalTyped : ExpressionHasType source context (id 6) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := conditionalNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.conditional selectedTyped wrappedTyped constructorTyped) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem pairedTyped : ExpressionHasType source context (id 7) (.product sourceType .bool) := by
  have admitted : TypeAdmissible context (.product sourceType .bool) := .product nominalAdmitted boolAdmitted
  apply ExpressionHasType.ofOrdinary (node := pairedNode) (rawType := .product sourceType .bool)
    (lookupExpression?_sound (by cbv)) (.tuple (.cons conditionalTyped (.cons selectedTyped (.nil _)))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem originalSyntax : Syntax source (id 1) := by
  refine .constructor (node := constructorNode) (by cbv) rfl ?_
  intro child member
  have same : child = id 0 := by simpa using member
  subst child
  exact .fragment (.fragment (.fragment (.primitive (.product (.literal (node := boolean) (by cbv) (.bool _ _))))))
private theorem memberSyntax : Syntax source (id 2) :=
  .member (node := memberNode) (by cbv) rfl originalSyntax
private theorem wrappedSyntax : Syntax source (id 4) := by
  refine .constructor (node := wrappedNode) (by cbv) rfl ?_
  intro child member
  have alternatives : child = id 3 ∨ child = id 2 := by simpa using member
  rcases alternatives with rfl | rfl
  · exact .unary (node := unaryNode) (by cbv) rfl memberSyntax
  · exact memberSyntax
private theorem selectedSyntax : Syntax source (id 5) :=
  .member (node := selectedNode) (by cbv) rfl wrappedSyntax
private theorem syntaxTree : Syntax source (id 7) :=
  .pair (node := pairedNode) (by cbv) rfl
    (.conditional (node := conditionalNode) (by cbv) rfl selectedSyntax wrappedSyntax originalSyntax)
    selectedSyntax
variable {checked : SourceCoreCompatibleCatalog.Checked}
private abbrev values (checked : SourceCoreCompatibleCatalog.Checked) := SourceCoreCompatibleValues.Context.initial checked
private abbrev policy (checked : SourceCoreCompatibleCatalog.Checked) := SourceCoreCompatibleDataExpressions.functionPolicy 20 (values checked)
private theorem certified (catalogSignatures : checked.signatures = signatures) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 30 compilation source [] (id 7) (fun _ => reason) = .ok code) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 7) code :=
  tree_of_functions (values := values checked) unique declarations catalogSignatures.symm rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) pairedTyped accepted

private def view := SourceCoreEvidence.withNode source {parent with type := .unit}
private def footprint : List NodeId := ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map (fun n => .expression (id n))
private theorem edited : LocalView source view [parent.id] :=
  withNode unique (by rfl) rfl rfl

private theorem reference_closed {expression : ExpressionId} {node : ExpressionNode}
    (member : NodeId.expression expression ∈ footprint) (found : source.lookupExpression? expression = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp only [footprint, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, NodeId.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
    subst node
    simp only [boolean, constructorNode, memberNode, unaryNode, wrappedNode, selectedNode,
      conditionalNode, pairedNode, ExpressionForm.references,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at edge <;>
      rcases edge with rfl | rfl | rfl <;> simp [footprint, id]

private theorem reached_member {node : NodeId} (reached : Reaches source source.roots node) : node ∈ footprint := by
  induction reached with
  | @root rootId member =>
    have same : rootId = NodeId.expression (id 7) := by simpa [source] using member
    rw [same]
    simp [footprint]
  | expression _ found edge ih => exact reference_closed ih found edge
  | statement _ _ _ ih => simp [footprint] at ih

private theorem avoids : Avoids source source.roots [parent.id] := by
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  have impossible := reached_member reached
  simp [parent, footprint, id] at impossible

/-- Actual accepted lowering, independently supplied typing and catalog
metadata build the original tree before the unrelated header is edited. -/
theorem accepted_view (catalogSignatures : checked.signatures = signatures) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 30 compilation source [] (id 7) (fun _ => reason) = .ok code) :
    source ≠ view ∧ Tree 20 (values checked) view context [] (fun _ => reason) [] (id 7) code :=
  ⟨by decide, CallableLambdaViewRecursiveTrees.recursive edited avoids
    (certified catalogSignatures accepted) (.root (by simp [source]))⟩

theorem recover_original {code : SourceCoreBasic.LoweredExpr}
    (tree : Tree 20 (values checked) view context [] (fun _ => reason) [] (id 7) code) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 7) code :=
  CallableLambdaViewRecursiveTrees.recursive_original edited avoids tree (.root (by simp [source]))

/-- A reached constructor cannot be listed as an irrelevant header edit. -/
theorem reached_constructor : ¬ Avoids source source.roots [constructorNode.id] := by
  intro fresh
  have pairReached : Reaches source source.roots (.expression pairedNode.id) := .root (by simp [source, pairedNode])
  have conditionReached : Reaches source source.roots (.expression conditionalNode.id) :=
    .expression pairReached (by rfl) (by simp [pairedNode, ExpressionForm.references, conditionalNode])
  have constructorReached : Reaches source source.roots (.expression constructorNode.id) :=
    .expression conditionReached (by rfl) (by simp [conditionalNode, ExpressionForm.references, constructorNode])
  exact fresh constructorNode.id (by simp) constructorReached

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Row { First(Bool, Bool), Second(Bool, Bool) }",
    "function make(seed: Bool) returns (function() returns (Row)) { return lam() -> Row { return .Second(seed, true); }; }",
    "function fail() returns (function() returns (Row)) { return lam() -> Row { let missing: Bool; return .First(missing, true); }; }"]}] }

private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | fuel + 1, source, expression => match source.lookupExpression? expression with
    | none => []
    | some node => node :: (match node.form with
      | .unary _ operand => reached fuel source operand
      | .binary left _ right => reached fuel source left ++ reached fuel source right
      | .conditional condition thenId elseId => reached fuel source condition ++ reached fuel source thenId ++ reached fuel source elseId
      | .member base _ _ => reached fuel source base
      | .group inner => reached fuel source inner
      | .tuple ids | .constructor _ ids => ids.flatMap (reached fuel source)
      | _ => [])

private def inspect {catalog : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (original : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (header : ExpressionNode)
    (name : String) (expression : ExpressionId) : IO Unit := do
  let contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "data view diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := [], internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let originalRoot ← match original.lookupExpression? expression with
    | some node => pure node | none => throw (IO.userError "data view original root missing")
  let .constructor constructor _ := originalRoot.form | throw (IO.userError "data view original constructor missing")
  let newId := fun index => (⟨⟨original.owner, 100000 + index⟩⟩ : ExpressionId)
  let member : ExpressionNode := {id := newId 0, span := originalRoot.span, type := .bool, form := .member expression "0" 0}
  let negated : ExpressionNode := {id := newId 1, span := originalRoot.span, type := .bool, form := .unary .logicalNot member.id}
  let wrapped : ExpressionNode := {id := newId 2, span := originalRoot.span, type := originalRoot.type, form := .constructor constructor [negated.id, member.id]}
  let selected : ExpressionNode := {id := newId 3, span := originalRoot.span, type := .bool, form := .member wrapped.id "0" 0}
  let selectedRow : ExpressionNode := {id := newId 4, span := originalRoot.span, type := originalRoot.type, form := .conditional selected.id wrapped.id originalRoot.id}
  let disjunction : ExpressionNode := {id := newId 5, span := originalRoot.span, type := .bool, form := .binary selected.id .logicalOr member.id}
  let paired : ExpressionNode := {id := newId 6, span := originalRoot.span, type := .product originalRoot.type .bool, form := .tuple [selectedRow.id, disjunction.id]}
  let grouped : ExpressionNode := {id := newId 7, span := originalRoot.span, type := paired.type, form := .group paired.id}
  let source := {original with roots := [.expression grouped.id], nodes := original.nodes ++
    [member, negated, wrapped, selected, selectedRow, disjunction, paired, grouped].map Node.expression}
  let ids := ((reached 100 source grouped.id).filterMap fun node =>
    match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let bindings ← ids.mapM fun binder => do
    let declared ← get "data view binder" (SourceCoreDataPlaces.rootBinder source binder)
    let type ← get "data view binder type" (catalog.catalog.project declared.scheme.body)
    assertTrue (type == .bool) "data view fixture binder is not Boolean"
    let initializer := if declared.name == "missing" then OptionalCell.allocate type
      else OptionalCell.allocateInitialized type (.bool true)
    pure (binder, type, initializer)
  let scope := bindings.map fun (binder, type, _) => (binder, type)
  let modified := SourceCoreEvidence.withNode source {header with type := .unit}
  let actualPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 150 contextValues
  let before := SourceCoreFunctions.lowerExpressionWithPolicy actualPolicy noBody 150 compilation source scope grouped.id reasonAt
  let after := SourceCoreFunctions.lowerExpressionWithPolicy actualPolicy noBody 150 compilation modified scope grouped.id reasonAt
  let lowered ← get s!"data view lowering {name}" before
  let same ← get s!"data view modified lowering {name}" after
  assertTrue (reprStr lowered == reprStr same) "data view changed accepted code, type or metadata header"
  assertTrue (source != modified) "data view fixture did not change the source header"
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"data view {name} failed native checker"
  for fuel in [0, 3, 15, 1000] do
    let finished := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 10000 checkpoint
      | other => other
    match finished with
    | .done value store =>
      assertTrue (store.length == bindings.length + 1) "data view composition allocated unexpected cells"
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "data view composition changed administrative closure"
      if name == "fail" then
        let faultNode ← match original.nodes.findSome? fun
          | .expression node => match node.form with | .reference "missing" (.local _) => some node | _ => none
          | _ => none with
          | some node => pure node | none => throw (IO.userError "data view fault occurrence missing")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt faultNode.id))) "data view composition changed first fault"
      else
        let payload ← match value with
          | .inRight .word payload => pure payload
          | _ => throw (IO.userError s!"data view {name} did not succeed: {reprStr value}")
        let decoded ← get "data view decode" (SourceCoreCompatibleValues.decode 100 contextValues grouped.type payload)
        match decoded with
        | .product (.constructed retained [.bool true, .bool true]) (.bool true) =>
            assertTrue (retained == constructor) "data view composition erased raw constructor metadata"
        | other => throw (IO.userError s!"data view result changed: {reprStr other}")
    | other => throw (IO.userError s!"data view {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let checkedProgram ← get "data view checker" (checkProgram workspace)
  let requests := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram requests 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"data view specialization: {reprStr other}")
  let automatic ← get "data view factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let indexed ← get "data view indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let mut seen := 0
  for template in indexed.ancestry.templates.lambdas do
    let original := template.context.inventory.source
    let name := (checkedProgram.signatures.functions.find? (·.id == template.owner.declaration)).map (·.name) |>.getD ""
    let constructor ← match original.nodes.findSome? fun
      | .expression node => match node.form with | .constructor _ _ => some node.id | _ => none
      | _ => none with
      | some expression => pure expression | none => throw (IO.userError "data view original constructor missing")
    inspect automatic.prepared original template.owner template.node name constructor
    seen := seen + 1
  assertTrue (seen == 2) "data view actual lambda fixtures missing"
  IO.println "lambda data views: exact constructor/member/control trees, raw headers, accepted code, fault order, ambient store and resume GREEN"

end Tests.SourceCoreCallableLambdaViewDataTrees
