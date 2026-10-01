import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualRecursive
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Recursive constructor/member/control composition is checked against actual
lowering, independent source typing, and both finite execution directions.
Positional members are introduced in retained typed IR. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionRecursive
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionRecursive CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"recursive_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "recursive_meaning.solc"⟩, 0, 4⟩
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
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 7)], nodes := [.expression boolean, .expression constructorNode, .expression memberNode,
      .expression unaryNode, .expression wrappedNode, .expression selectedNode, .expression conditionalNode, .expression pairedNode] }
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private def faults : FunctionCalls.FaultRep := fun error token =>
  (∃ location, error = .uninitializedLocation location) ∧ token = reason
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
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
    simp only [signature, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rcases inBounds with rfl | rfl <;> rfl
  · intro actual admissible resultType
    cases admissible with
    | intro dataType constructor dataMember constructorMember _ _ _ _ payloads _ =>
      have same : dataType = signature := by simpa [context, SourceSemantics.Context.ofSignatures, signatures] using dataMember
      subst dataType
      simp only [signature, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at constructorMember
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
private theorem contextValid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures]
  · intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; simp [context, SourceSemantics.Context.ofSignatures] at member
variable {checked : SourceCoreCompatibleCatalog.Checked}
private abbrev values (checked : SourceCoreCompatibleCatalog.Checked) := SourceCoreCompatibleValues.Context.initial checked
private abbrev policy (checked : SourceCoreCompatibleCatalog.Checked) := SourceCoreCompatibleDataExpressions.functionPolicy 20 (values checked)
private theorem certified (catalogSignatures : checked.signatures = signatures) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 30 compilation source [] (id 7) (fun _ => reason) = .ok code) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 7) code :=
  tree_of_functions (values := values checked) unique declarations catalogSignatures.symm rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) pairedTyped accepted

theorem contextual_certificate
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {lowered : SourceCoreBasic.LoweredExpr}
    (catalogSignatures : checked.signatures = signatures)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead 20 (values checked))
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer (values checked))
    (generated : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures ⟨[]⟩ parents assignments
      diagnostics compilation native parent none 30 source [] (id 7) (fun _ => reason) = .ok lowered) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 7) lowered := by
  exact tree_of_contextual (values := values checked)
    ⟨fun _ _ _ found => (metadata found).1, fun _ _ _ found => (metadata found).2, by intros; rfl, by intros; rfl⟩
    unique rfl rfl declarations catalogSignatures.symm syntaxTree (by cbv) pairedTyped readPolicy lowerPolicy leafPolicy generated

theorem actual_preserves {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked (values checked).registry functions)
      program context [] source (Tree 20 (values checked) source context [] (fun _ => reason)) faults :=
  preserves (values := values checked) functions (.refl _) program [] contextValid unique (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)
theorem actual_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked (values checked).registry functions)
      program context [] source (Tree 20 (values checked) source context [] (fun _ => reason)) faults :=
  reflects (values := values checked) functions (.refl _) program [] contextValid (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Row { First(Bool, Bool), Second(Bool, Bool) }",
    "function nested() returns (Row) { return .Second(true, true); }",
    "function child_fault() returns (Row) { let missing: Bool; return .First(missing, true); }",
    "function parent(seed: Bool) returns (Row) { let f = lam(item) -> Row { return .Second(seed, true); }; return f(true); }"]}] }

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
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (name : String) (expression : ExpressionId) : IO Unit := do
  let contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let representation := SourceCoreCompatibleFunctions.representation contextValues 150
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "recursive diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "recursive root diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let originalRoot ← match original.lookupExpression? expression with
    | some node => pure node | none => throw (IO.userError "recursive original root missing")
  let .constructor constructor _ := originalRoot.form | throw (IO.userError "recursive original constructor missing")
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
    let declared ← get "recursive binder" (SourceCoreDataPlaces.rootBinder source binder)
    let type ← get "recursive binder type" (catalog.catalog.project declared.scheme.body)
    assertTrue (type == .bool) "recursive fixture binder is not Boolean"
    let initializer := if declared.name == "missing" then OptionalCell.allocate type
      else OptionalCell.allocateInitialized type (.bool true)
    pure (binder, type, initializer)
  let scope := bindings.map fun (binder, type, _) => (binder, type)
  let lowered ← get s!"actual contextual recursive {name}" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
    representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
    parent none 150 source scope grouped.id reasonAt)
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"recursive {name} failed native checker"
  for fuel in [0, 3, 15, 1000] do
    let finished := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 10000 checkpoint
      | other => other
    match finished with
    | .done value store =>
      assertTrue (store.length == bindings.length + 1) "recursive composition allocated unexpected cells"
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "recursive composition changed administrative closure"
      if name == "child_fault" then
        let faultNode ← match original.nodes.findSome? fun
          | .expression node => match node.form with | .reference "missing" (.local _) => some node | _ => none
          | _ => none with
          | some node => pure node | none => throw (IO.userError "recursive fault occurrence missing")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt faultNode.id))) "recursive composition changed first fault"
      else
        let payload ← match value with
          | .inRight .word payload => pure payload
          | _ => throw (IO.userError s!"recursive {name} did not succeed: {reprStr value}")
        let decoded ← get "recursive decode" (SourceCoreCompatibleValues.decode 100 contextValues grouped.type payload)
        match decoded with
        | .product (.constructed retained [.bool true, .bool true]) (.bool true) =>
            assertTrue (retained == constructor) "recursive composition erased raw constructor metadata"
        | other => throw (IO.userError s!"recursive result changed: {reprStr other}")
    | other => throw (IO.userError s!"recursive {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let checkedProgram ← get "recursive checker" (checkProgram workspace)
  let roots := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"recursive specialization: {reprStr other}")
  let automatic ← get "recursive factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      let source := function.specialized.function.typedBody
      let expression ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some expression => pure expression | none => throw (IO.userError "recursive return missing")
      inspect automatic.prepared source function.signature.key none function.specialized.function.solvedRequirements name expression
      rootsSeen := rootsSeen + 1
  let mut parentsSeen := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      for entry in parent.source.nodes do
        match entry with
        | .expression node => match node.form with
          | .constructor _ _ =>
            inspect automatic.prepared parent.source parent.caller.key (some parent) parent.caller.function.solvedRequirements "parent" node.id
            parentsSeen := parentsSeen + 1
          | _ => pure ()
        | _ => pure ()
  assertTrue (rootsSeen == 2) s!"recursive root cases missing: {rootsSeen}"
  assertTrue (parentsSeen > 0) "recursive full parent case missing"
  IO.println "recursive data/control composition: member inside constructor, outer member, nominal conditional, primitive, product, raw header, fault, ambient parent and resume GREEN"

end Tests.SourceCoreCompatibleExpressionRecursive
