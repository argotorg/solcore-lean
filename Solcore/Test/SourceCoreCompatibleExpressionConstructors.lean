import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualConstructors
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual accepted constructor lowering supplies a recursive static tree. The
kernel consumers require no child runtime hypothesis; checked-source executions
exercise exact raw metadata, first-fault ordering and administrative stores. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionConstructors
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionConstructors CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"constructor_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "constructor_meaning.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def sourceType : TypeSystem.Ty := .nominal owner []
private def leafSignature : ProgramDataConstructorSignature :=
  ⟨⟨owner, 0⟩, "Leaf", [.bool], ⟨span, ⟨[], ⟨span, "Leaf"⟩, none⟩⟩⟩
private def branchSignature : ProgramDataConstructorSignature :=
  ⟨⟨owner, 1⟩, "Branch", [sourceType, sourceType], ⟨span, ⟨[], ⟨span, "Branch"⟩, none⟩⟩⟩
private def signature : ProgramDataSignature := {
  id := owner, name := "Tree", parameters := [], constructors := [leafSignature, branchSignature]
  source := ⟨span, ⟨none, ⟨span, "Tree"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def leaf : DataConstructorInstantiation := ⟨leafSignature.id, [], [.bool], sourceType⟩
private def branch : DataConstructorInstantiation := ⟨branchSignature.id, [], [sourceType, sourceType], sourceType⟩
private def boolean : ExpressionNode := { id := id 0, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def leafNode : ExpressionNode := { id := id 1, span, type := sourceType, form := .constructor leaf [id 0] }
private def branchNode : ExpressionNode := { id := id 2, span, type := sourceType, form := .constructor branch [id 1, id 1] }
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 2)],
    nodes := [.expression boolean, .expression leafNode, .expression branchNode] }
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
  intro binder declared index native selected
  cases selected
private theorem leafValid : SourceSemantics.DataConstructorInstantiation.Valid context leaf := by
  refine .intro signature leafSignature (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    (by simp [signature]) rfl rfl ⟨by simp [signature], by simp [ParameterSubstitution.domain, leaf, signature]⟩ ?_ rfl rfl
  intro parameter replacement member; cases member
private theorem branchValid : SourceSemantics.DataConstructorInstantiation.Valid context branch := by
  refine .intro signature branchSignature (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    (by simp [signature]) rfl rfl ⟨by simp [signature], by simp [ParameterSubstitution.domain, branch, signature]⟩ ?_ rfl rfl
  intro parameter replacement member; cases member
private theorem nominalAdmitted : TypeAdmissible context sourceType :=
  ⟨TypeParameterBindersWellFormed.ofSignatures signatures,
    .nominal signature [] (by simp [context, SourceSemantics.Context.ofSignatures, signatures]) rfl .nil⟩
private theorem boolTyped : ExpressionHasType source context (id 0) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := boolean) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem leafTyped : ExpressionHasType source context (id 1) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := leafNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.constructor leafValid.toAdmissible (.cons boolTyped (.nil _))) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem branchTyped : ExpressionHasType source context (id 2) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := branchNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.constructor branchValid.toAdmissible (.cons leafTyped (.cons leafTyped (.nil _)))) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem syntaxTree : CompatibleExpressionConstructors.Syntax source (id 2) := by
  refine .constructor (node := branchNode) (by cbv) rfl ?_
  intro child member
  have same : child = id 1 := by simpa using member
  subst child
  refine .constructor (node := leafNode) (by cbv) rfl ?_
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
private theorem certified {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 5 compilation source [] (id 2) (fun _ => reason) = .ok code) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 2) code :=
  tree_of_functions unique declarations rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) branchTyped accepted

/-- The authentic contextual dispatcher equation supplies the same tree for
root and prepared-parent calls; no child compiler/semantic premise remains. -/
theorem contextual_certificate
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {lowered : SourceCoreBasic.LoweredExpr}
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead 20 (values checked))
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer (values checked))
    (generated : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures ⟨[]⟩ parents assignments
      diagnostics compilation native parent none 5 source [] (id 2) (fun _ => reason) = .ok lowered) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 2) lowered := by
  exact tree_of_contextual
    ⟨fun _ _ _ found => (metadata found).1, fun _ _ _ found => (metadata found).2, by intros; rfl, by intros; rfl⟩
    unique rfl rfl declarations syntaxTree (by cbv) branchTyped readPolicy lowerPolicy leafPolicy generated

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

theorem accepted_constructor_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
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
        finalMap finalWorld branchNode.type code.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked (values checked).registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  actual_reflects functions (certified accepted) (by cbv) environments heaps locals agrees completed

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)


private def sources : List String := [
  "enum Tree<T> { Empty(), Leaf(T), Branch(Tree<T>, Tree<T>) }",
  "enum Pair<A,B> { Pair(A,B) }",
  "function empty() returns (Tree<Word>) { return .Empty(); }",
  "function literal() returns (Tree<Word>) { return .Leaf(7); }",
  "function nested() returns (Tree<Word>) { return .Branch(.Leaf((true ? 7 : 9) + 3), .Leaf(~3)); }",
  "function first_fault() returns (Pair<Word,Word>) { let missing: Word; let otherMissing: Word; return .Pair(missing, otherMissing); }",
  "function second_fault() returns (Pair<Word,Word>) { let missing: Word; return .Pair(7, missing); }",
  "function nested_fault() returns (Tree<Word>) { let missing: Word; let otherMissing: Word; return .Branch(.Leaf(missing), .Leaf(otherMissing)); }",
  "function map_success() returns (Pair<mapping(Word => Word), Bool>) { let m: mapping(Word => Word); return .Pair(m, false ? false : true); }",
  "function map_fault() returns (Pair<mapping(Word => Word), Pair<Bool, mapping(Word => Word)>>) { let m: mapping(Word => Word); let other: mapping(Word => Word); let missing: Bool; return .Pair(m, .Pair(missing, other)); }",
  "function parent(seed: Word) returns (Tree<Word>) { let f = lam(item) -> Tree<Word> { return .Leaf(true ? ~seed : seed + 3); }; return f(true); }"]
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
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "constructor diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "constructor root diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let nodes := reached 100 source expression
  for node in nodes do
    assertTrue node.coercions.isEmpty "constructor fixture acquired an output coercion"
    match node.form with
    | .unary .. | .binary .. | .conditional .. => assertTrue node.requirements.isEmpty "constructor fixture acquired method dispatch evidence"
    | _ => pure ()
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let bindings ← ids.mapM fun binder => do
    let declared ← get "constructor binder" (SourceCoreDataPlaces.rootBinder source binder)
    let type ← get "constructor binder projection" (catalog.catalog.project declared.scheme.body)
    let initializer ← if declared.name == "missing" || declared.name == "otherMissing" then pure (OptionalCell.allocate type)
      else match declared.scheme.body with
      | .bool => pure (OptionalCell.allocateInitialized type (.bool true))
      | .word => pure (OptionalCell.allocateInitialized type (.word (Word.ofNatModulo (if declared.name == "b" then 3 else 7))))
      | .integer => pure (OptionalCell.allocateInitialized type (.integer (if declared.name == "b" then 3 else -7)))
      | .mapping .. => pure (OptionalCell.allocate type)
      | other => throw (IO.userError s!"unexpected constructor scope: {reprStr other}")
    pure (binder, type, initializer)
  let scope := bindings.map fun (id, type, _) => (id, type)
  let lowered ← get s!"actual contextual constructor {name}" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
    representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
    parent none 150 source scope expression reasonAt)
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"actual contextual constructor {name} failed native checker"
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
      assertTrue (store.length == bindings.length + 1) "constructor allocated unexpected cells"
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "constructor changed administrative closure"
      if name.endsWith "fault" then
        let faultNode ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "fault fixture lacks missing occurrence")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt faultNode.id))) s!"constructor {name} fault reason/order changed"
      else
        let payload ← match value with
          | .inRight .word payload => pure payload
          | _ => throw (IO.userError s!"constructor {name} did not succeed: {reprStr value}")
        let root ← match source.lookupExpression? expression with
          | some node => pure node | none => throw (IO.userError "root source metadata missing")
        let decoded ← get "actual constructor decode" (SourceCoreCompatibleValues.decode 100 contextValues root.type payload)
        match root.form, decoded with
        | .constructor original _, .constructed retained fields =>
          assertTrue (original == retained) "constructor lost its exact original metadata header"
          match name, fields with
          | "empty", [] => pure ()
          | "literal", [.word seven] => assertTrue (seven == Word.ofNatModulo 7) "literal payload changed"
          | "nested", [.constructed _ [.word ten], .constructed _ [.word inverted]] =>
            assertTrue (ten == Word.ofNatModulo 10 && inverted == (Word.ofNatModulo 3).bitNot) "nested constructor argument order changed"
          | "map_success", [.mapping .word .word [], .bool true] => pure ()
          | "parent", [.word inverted] => assertTrue (inverted == (Word.ofNatModulo 7).bitNot) "parent constructor captured wrong source context"
          | _, _ => throw (IO.userError s!"unexpected constructor {name} fields: {reprStr fields}")
        | _, _ => throw (IO.userError "constructor result did not retain raw source header")
      for (position, (binder, type, _)) in bindings.zipIdx.map (fun (binding, position) => (position, binding)) do
        if type != .bool && type != .word && type != .integer then
          let declared ← get "mapping branch binder" (SourceCoreDataPlaces.rootBinder source binder)
          let expectedCell := if declared.name == "m" then Value.inRight .unit mappingValue else .inLeft type .unit
          assertTrue (store[bindings.length - position]? == some expectedCell)
            "constructor initialized the skipped mapping or lost the selected mapping"
    | other => throw (IO.userError s!"constructor {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let checkedProgram ← get "constructor checker" (checkProgram workspace)
  let roots := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"constructor specialization: {reprStr other}")
  let automatic ← get "actual constructor factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      let source := function.specialized.function.typedBody
      let expression ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some expression => pure expression | none => throw (IO.userError "constructor return missing")
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
  assertTrue (rootsSeen == 8) s!"constructor cases missing: {rootsSeen}"
  assertTrue (parentsSeen > 0) "full parent substitution constructor case missing"
  IO.println "actual contextual constructors: nullary/nested payloads, first fault, lazy mapping effects, raw headers, parent context, ambient closure and resume GREEN"

end Tests.SourceCoreCompatibleExpressionConstructors
