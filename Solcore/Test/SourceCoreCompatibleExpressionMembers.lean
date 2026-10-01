import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualMembers
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Member syntax is retained typed IR, with independent uniform-field typing.
Actual checked catalogs and contextual compilation exercise native selection;
no claim is made that the surface parser admits positional member expressions. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionMembers
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionMembers CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"member_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "member_meaning.solc"⟩, 0, 4⟩
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
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 2)], nodes := [.expression boolean, .expression constructorNode, .expression memberNode] }
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
  rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
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
private theorem projection : UniformMemberProjection context sourceType 1 .bool := by
  refine .intro (dataType := signature) (substitution := []) (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    ⟨by simp [signature], by simp [ParameterSubstitution.domain, signature]⟩ rfl nominalAdmitted boolAdmitted (by simp [signature]) ?_ ?_
  · intro constructor member
    simp only [signature, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro actual admissible resultType
    cases admissible with
    | intro dataType constructor dataMember constructorMember _ _ _ _ payloads _ =>
      have same : dataType = signature := by simpa [context, SourceSemantics.Context.ofSignatures, signatures] using dataMember
      subst dataType
      simp only [signature, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at constructorMember
      rcases constructorMember with rfl | rfl <;> rw [payloads] <;> rfl
private theorem memberTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := memberNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.member constructorTyped projection) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem syntaxTree : CompatibleExpressionMembers.Syntax source (id 2) := by
  refine .member (node := memberNode) (by cbv) rfl (.fragment (.constructor (node := constructorNode) (by cbv) rfl ?_))
  intro child member
  have same : child = id 0 := by simpa using member
  subst child
  exact .fragment (.primitive (.product (.literal (node := boolean) (by cbv) (.bool _ _))))
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
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 5 compilation source [] (id 2) (fun _ => reason) = .ok code) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 2) code :=
  tree_of_functions (values := values checked) unique declarations catalogSignatures.symm rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) memberTyped accepted

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
      diagnostics compilation native parent none 5 source [] (id 2) (fun _ => reason) = .ok lowered) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 2) lowered := by
  exact tree_of_contextual (values := values checked)
    ⟨fun _ _ _ found => (metadata found).1, fun _ _ _ found => (metadata found).2, by intros; rfl, by intros; rfl⟩
    unique rfl rfl declarations catalogSignatures.symm syntaxTree (by cbv) memberTyped readPolicy lowerPolicy leafPolicy generated

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

theorem accepted_member_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (catalogSignatures : checked.signatures = signatures)
    {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 5 compilation source [] (id 2) (fun _ => reason) = .ok code)
    {mapping world administrative environment canonical actual before store ξ value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
      administrative [] environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked (values checked).registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (completed : Evaluates actual store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source environment before (id 2) outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked (values checked).registry functions)
        finalMap finalWorld memberNode.type code.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked (values checked).registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  actual_reflects functions (certified catalogSignatures accepted) (by cbv) environments heaps locals agrees completed

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)


private def sources : List String := [
  "enum Row<T> { First(T, Bool), Second(T, Bool) }",
  "enum Box<T> { Box(T) }",
  "function first() returns (Row<Word>) { return .First(7, true); }",
  "function second() returns (Row<Word>) { return .Second(9, false); }",
  "function flag() returns (Row<Word>) { return .Second(9, false); }",
  "function nested() returns (Box<Row<Word>>) { return .Box(.Second(9, false)); }",
  "function nominal() returns (Box<Row<Word>>) { return .Box(.First(7, true)); }",
  "function first_fault() returns (Row<Word>) { let missing: Word; return .First(missing, true); }",
  "function base_fault() returns (Row<Word>) { let missing: Row<Word>; return missing; }",
  "function map_success() returns (Row<mapping(Word => Word)>) { let m: mapping(Word => Word); return .First(m, false); }",
  "function map_fault() returns (Row<mapping(Word => Word)>) { let m: mapping(Word => Word); let missing: Bool; return .First(m, missing); }",
  "function parent(seed: Word) returns (Row<Word>) { let f = lam(item) -> Row<Word> { return .First(~seed, true); }; return f(true); }"]
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" sources}] }

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
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (name : String) (expression : ExpressionId) : IO Unit := do
  let contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let representation := SourceCoreCompatibleFunctions.representation contextValues 150
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "member diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "member root diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let originalRoot ← match source.lookupExpression? expression with
    | some node => pure node | none => throw (IO.userError "member original root missing")
  let path := if name == "nested" then [0, 0] else if name == "flag" then [1] else [0]
  let mut source := source
  let mut expression := expression
  let mut expectedRaw := originalRoot.type
  for (index, position) in path.zipIdx do
    let (declaration, arguments) ← match SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType expectedRaw) with
      | some parts => pure parts | none => throw (IO.userError "member fixture nominal path missing")
    let signature ← match catalog.signatures.dataTypes.find? (·.id == declaration) with
      | some signature => pure signature | none => throw (IO.userError "member fixture signature missing")
    let first ← match signature.constructors with
      | first :: _ => pure first | [] => throw (IO.userError "member fixture empty declaration")
    let payloads := first.payloadTypes.map
      (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip arguments))
    let field ← match payloads[index]? with
      | some type => pure type | none => throw (IO.userError "member fixture index absent")
    let next : ExpressionId := ⟨⟨source.owner, 100000 + position⟩⟩
    let node : ExpressionNode := { id := next, span := originalRoot.span, type := field, form := .member expression (toString index) index }
    source := {source with roots := [.expression next], nodes := source.nodes ++ [.expression node]}
    expression := next
    expectedRaw := field
  let nodes := reached 100 source expression
  for node in nodes do
    assertTrue node.coercions.isEmpty "member fixture acquired an output coercion"
    match node.form with
    | .unary .. | .binary .. | .conditional .. => assertTrue node.requirements.isEmpty "member fixture acquired method dispatch evidence"
    | _ => pure ()
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let bindings ← ids.mapM fun binder => do
    let declared ← get "member binder" (SourceCoreDataPlaces.rootBinder source binder)
    let type ← get "member binder projection" (catalog.catalog.project declared.scheme.body)
    let initializer ← if declared.name == "missing" || declared.name == "otherMissing" then pure (OptionalCell.allocate type)
      else match declared.scheme.body with
      | .bool => pure (OptionalCell.allocateInitialized type (.bool true))
      | .word => pure (OptionalCell.allocateInitialized type (.word (Word.ofNatModulo (if declared.name == "b" then 3 else 7))))
      | .integer => pure (OptionalCell.allocateInitialized type (.integer (if declared.name == "b" then 3 else -7)))
      | .mapping .. => pure (OptionalCell.allocate type)
      | other => throw (IO.userError s!"unexpected member scope: {reprStr other}")
    pure (binder, type, initializer)
  let scope := bindings.map fun (id, type, _) => (id, type)
  let lowered ← get s!"actual contextual member {name}" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
    representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
    parent none 150 source scope expression reasonAt)
  if name == "first" then
    for malformed in [(.member originalRoot.id "2" 2, .word), (.member originalRoot.id "0" 0, .bool)] do
      let forged := { source with nodes := source.nodes.map fun
        | .expression node => if node.id == expression then .expression {node with form := malformed.1, type := malformed.2} else .expression node
        | other => other }
      match SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation catalog.signatures
        prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext parent none 150 forged scope expression reasonAt with
      | .ok _ => throw (IO.userError "malformed member metadata accepted")
      | .error _ => pure ()
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"actual contextual member {name} failed native checker"
  let mappingValue ← if name.startsWith "map_" then do
    let encoded ← get "expected empty mapping" (SourceCoreCompatibleValues.encode 100 contextValues
      (.mapping .word .word) (.mapping .word .word []))
    pure encoded.value
    else pure .unit
  for fuel in [0, 3, 15, 1000] do
    let finished := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 3000 checkpoint
      | other => other
    match finished with
    | .done value store =>
      assertTrue (store.length == bindings.length + 1) "member allocated unexpected cells"
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "member changed administrative closure"
      if name.endsWith "fault" then
        let faultNode ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "fault fixture lacks missing occurrence")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt faultNode.id))) s!"member {name} fault reason/order changed"
      else
        let payload ← match value with
          | .inRight .word payload => pure payload
          | _ => throw (IO.userError s!"member {name} did not succeed: {reprStr value}")
        let root ← match source.lookupExpression? expression with
          | some node => pure node | none => throw (IO.userError "root source metadata missing")
        let decoded ← get "actual member decode" (SourceCoreCompatibleValues.decode 100 contextValues root.type payload)
        match name, decoded with
        | "first", .word value => assertTrue (value == Word.ofNatModulo 7) "first constructor selected wrong field"
        | "second", .word value | "nested", .word value => assertTrue (value == Word.ofNatModulo 9) "second constructor selected wrong field"
        | "flag", .bool false => pure ()
        | "nominal", .constructed retained [.word value, .bool true] =>
          let expected ← match nodes.find? (fun node => match node.form with | .constructor _ ids => ids.length == 2 | _ => false) with
            | some node => pure node | none => throw (IO.userError "nested original header missing")
          let .constructor original _ := expected.form | throw (IO.userError "expected source constructor")
          assertTrue (retained == original && value == Word.ofNatModulo 7) "member erased selected raw constructor header"
        | "map_success", .mapping .word .word [] => pure ()
        | "parent", .word value => assertTrue (value == (Word.ofNatModulo 7).bitNot) "parent member selected wrong payload"
        | _, _ => throw (IO.userError s!"unexpected member {name}: {reprStr decoded}")
      for (position, (binder, type, _)) in bindings.zipIdx.map (fun (binding, position) => (position, binding)) do
        if (match (← get "member binder metadata" (SourceCoreDataPlaces.rootBinder source binder)).scheme.body with | .mapping .. => true | _ => false) then
          let declared ← get "mapping branch binder" (SourceCoreDataPlaces.rootBinder source binder)
          let expectedCell := if declared.name == "m" then Value.inRight .unit mappingValue else .inLeft type .unit
          assertTrue (store[bindings.length - position]? == some expectedCell)
            "member initialized the skipped mapping or lost the selected mapping"
    | other => throw (IO.userError s!"member {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let checkedProgram ← get "member checker" (checkProgram workspace)
  let roots := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"member specialization: {reprStr other}")
  let automatic ← get "actual member factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      let source := function.specialized.function.typedBody
      let expression ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some expression => pure expression | none => throw (IO.userError "member return missing")
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
  assertTrue (rootsSeen == 9) s!"member cases missing: {rootsSeen}"
  assertTrue (parentsSeen > 0) "full parent substitution member case missing"
  IO.println "actual contextual members: both tags, chained/raw nominal field, base/child fault, lazy mapping effects, parent context, ambient closure and resume GREEN"

end Tests.SourceCoreCompatibleExpressionMembers
