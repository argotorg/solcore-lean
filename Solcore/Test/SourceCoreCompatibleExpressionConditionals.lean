import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualConditionals
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! The kernel tests consume actual compiler results and independent source
shape typing. Runtime tests cover a lazy mapping read before a right-hand
fault, inserted slots, a full parent context, and administrative closures. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionConditionals
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionConditionals CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_products", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "products.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def boolean (index : Nat) (value : Bool) : ExpressionNode :=
  { id := id index, span, type := .bool, form := .reference "boolean" (.builtinBoolean value) }
private def unaryNode : ExpressionNode := { id := id 2, span, type := .bool, form := .unary .logicalNot (id 0) }
private def binaryNode : ExpressionNode := { id := id 3, span, type := .bool, form := .binary (id 2) .logicalOr (id 1) }
private def grouped : ExpressionNode := { id := id 4, span, type := .bool, form := .group (id 6) }
private def paired : ExpressionNode := { id := id 5, span, type := .product .bool .bool, form := .tuple [id 4, id 1] }
private def conditionalNode : ExpressionNode := { id := id 6, span, type := .bool, form := .conditional (id 3) (id 0) (id 1) }
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 5)],
    nodes := [.expression (boolean 0 true), .expression (boolean 1 false), .expression unaryNode, .expression binaryNode, .expression grouped, .expression paired, .expression conditionalNode] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
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
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index native selected
  cases selected
private theorem syntaxTree : CompatibleExpressionConditionals.Syntax source (id 5) :=
  .pair (node := paired) (by cbv) rfl
    (.group (node := grouped) (by cbv) rfl
      (.conditional (node := conditionalNode) (by cbv) rfl
        (.primitive (.binary (node := binaryNode) (by cbv) rfl
          (.unary (node := unaryNode) (by cbv) rfl (.product (.literal (node := boolean 0 true) (by cbv) (.bool _ _))))
          (.product (.literal (node := boolean 1 false) (by cbv) (.bool _ _)))))
        (.primitive (.product (.literal (node := boolean 0 true) (by cbv) (.bool _ _))))
        (.primitive (.product (.literal (node := boolean 1 false) (by cbv) (.bool _ _))))))
    (.primitive (.product (.literal (node := boolean 1 false) (by cbv) (.bool _ _))))
private theorem boolTyped {index : Nat} {value : Bool}
    (found : source.lookupExpression? (id index) = some (boolean index value)) :
    ExpressionHasType source context (id index) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := boolean index value) (rawType := .bool)
    (lookupExpression?_sound found) (.reference (.builtinBoolean value)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem unaryTyped : ExpressionHasType source context (id 2) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := unaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.unary (boolTyped (value := true) (by cbv)) .logicalNot) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem binaryTyped : ExpressionHasType source context (id 3) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := binaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.binary unaryTyped (boolTyped (value := false) (by cbv)) .booleanOr) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem conditionalTyped : ExpressionHasType source context (id 6) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := conditionalNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.conditional binaryTyped
      (boolTyped (value := true) (by cbv)) (boolTyped (value := false) (by cbv))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem groupedTyped : ExpressionHasType source context (id 4) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := grouped) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.group conditionalTyped) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem pairedTyped : ExpressionHasType source context (id 5) (.product .bool .bool) := by
  have boolAdmitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  have admitted : TypeAdmissible context (.product .bool .bool) := .product boolAdmitted boolAdmitted
  apply ExpressionHasType.ofOrdinary (node := paired) (rawType := .product .bool .bool)
    (lookupExpression?_sound (by cbv)) (.tuple (.cons groupedTyped (.cons (boolTyped (value := false) (by cbv)) (.nil _)))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures]
  · intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; simp [context, SourceSemantics.Context.ofSignatures] at member
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.product .bool .bool]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.product .bool .bool]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def policy := SourceCoreCompatibleDataExpressions.functionPolicy 20 values
private def unaryCode := LocalPrimitiveResults.unary .boolNot (LanguageResult.success (.bool true))
private def binaryCode := SourceCorePrimitive.binary .logicalOr unaryCode (LanguageResult.success (.bool false))
private def conditionalCode := LocalControl.choose .bool binaryCode
  (LanguageResult.success (.bool true)) (LanguageResult.success (.bool false))
private def code : SourceCoreBasic.LoweredExpr :=
  ⟨.product .bool .bool, LocalSequence.pair .bool .bool conditionalCode (LanguageResult.success (.bool false))⟩
private theorem boolAccepted (fuel index : Nat) (value : Bool)
    (found : source.lookupExpression? (id index) = some (boolean index value))
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id index) = .ok (boolean index value, .bool))
    (basic : SourceCoreBasic.lowerExpression (fuel + 1) source [] (id index) reason =
      .ok ⟨.bool, LanguageResult.success (.bool value)⟩) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 1) compilation source [] (id index) (fun _ => reason) =
      .ok ⟨.bool, LanguageResult.success (.bool value)⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id index).occurrence.owner = source.owner := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure]
  simp only [boolean]
  rw [read]
  simp only [bind, Except.bind, boolean]
  unfold SourceCoreCompatibleDataExpressions.leafLowerer
  rw [read]
  exact basic
private theorem unaryAccepted (fuel : Nat) : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 2) compilation source [] (id 2) (fun _ => reason) = .ok ⟨.bool, unaryCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 2).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 2) = some unaryNode := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 2) = .ok (unaryNode, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, unaryNode]
  rw [read]
  simp only [bind, Except.bind, unaryNode]
  have childEq := boolAccepted fuel 0 true rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at childEq
  rw [childEq]
  rfl
private theorem binaryAccepted (fuel : Nat) : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 3) compilation source [] (id 3) (fun _ => reason) = .ok ⟨.bool, binaryCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 3).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 3) = some binaryNode := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 3) = .ok (binaryNode, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, binaryNode]
  rw [read]
  simp only [bind, Except.bind, binaryNode]
  have firstEq := unaryAccepted fuel
  have secondEq := boolAccepted (fuel + 1) 1 false rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at firstEq secondEq
  rw [firstEq]
  simp only [bind, Except.bind]
  rw [secondEq]
  rfl
private theorem conditionalAccepted (fuel : Nat) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 4) compilation source [] (id 6) (fun _ => reason) =
      .ok ⟨.bool, conditionalCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 6).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 6) = some conditionalNode := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 6) = .ok (conditionalNode, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, conditionalNode]
  rw [read]
  simp only [bind, Except.bind, conditionalNode]
  have conditionEq := binaryAccepted fuel
  have thenEq := boolAccepted (fuel + 2) 0 true rfl rfl rfl
  have elseEq := boolAccepted (fuel + 2) 1 false rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at conditionEq thenEq elseEq
  rw [conditionEq]
  change (do
    let thenCode ← SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 3) compilation source [] (id 0) (fun _ => reason)
    let elseCode ← SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 3) compilation source [] (id 1) (fun _ => reason)
    SourceCoreBasic.ensureType _ .bool thenCode.type
    SourceCoreBasic.ensureType _ .bool elseCode.type
    pure (⟨.bool, LocalControl.choose .bool binaryCode thenCode.expression elseCode.expression⟩ : SourceCoreBasic.LoweredExpr)) = _
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure]
  rw [thenEq]
  simp only [bind, Except.bind]
  rw [elseEq]
  rfl
private theorem groupAccepted (fuel : Nat) : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 5) compilation source [] (id 4) (fun _ => reason) = .ok ⟨.bool, conditionalCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 4).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 4) = some grouped := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 4) = .ok (grouped, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, grouped]
  rw [read]
  simp only [bind, Except.bind, grouped]
  have childEq := conditionalAccepted fuel
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at childEq
  rw [childEq]
  rfl
private theorem accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 7 compilation source [] (id 5) (fun _ => reason) = .ok code := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 5).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 5) = some paired := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 5) = .ok (paired, (.product .bool .bool)) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, paired]
  rw [read]
  simp only [bind, Except.bind, paired]
  have firstEq := groupAccepted 1
  have secondEq := boolAccepted 5 1 false rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at firstEq secondEq
  rw [firstEq]
  simp only [bind, Except.bind]
  rw [secondEq]
  rfl
private theorem certified : Tree 20 values source context [] (fun _ => reason) [] (id 5) code :=
  tree_of_functions unique declarations ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) pairedTyped accepted

/-- The actual production contextual dispatcher is also the source of the
static tree; the compilation equation is the only compiler-result premise. -/
theorem contextual_certificate
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {lowered : SourceCoreBasic.LoweredExpr}
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead 20 values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (generated : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures ⟨[]⟩ parents assignments
      diagnostics compilation native parent none 7 source [] (id 5) (fun _ => reason) = .ok lowered) :
    Tree 20 values source context [] (fun _ => reason) [] (id 5) lowered := by
  exact tree_of_contextual
    ⟨fun _ _ _ found => (metadata found).1, fun _ _ _ found => (metadata found).2, by intros; rfl, by intros; rfl⟩
    unique declarations syntaxTree (by cbv) pairedTyped readPolicy lowerPolicy leafPolicy generated

/-- Both directions use the whole tree induction. No child evaluator proof is
supplied, even when the ambient heap contains captures of fresh nominal frames. -/
theorem actual_preserves {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked values.registry functions)
      program context [] source (Tree 20 values source context [] (fun _ => reason)) faults :=
  preserves (values := values) (source := source) (fuel := 20) (reasonAt := fun _ => reason) (faults := faults) functions (.refl _) program [] valid unique (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)
theorem actual_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked values.registry functions)
      program context [] source (Tree 20 values source context [] (fun _ => reason)) faults :=
  reflects (values := values) (source := source) (fuel := 20) (reasonAt := fun _ => reason) (faults := faults) functions (.refl _) program [] valid (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)

theorem accepted_conditional_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {mapping world administrative environment canonical actual before store ξ value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
      administrative [] environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (completed : Evaluates actual store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source environment before (id 5) outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked values.registry functions)
        finalMap finalWorld paired.type code.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  actual_reflects functions certified (by cbv) environments heaps locals agrees completed


private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)


private def sources : List String := [
  "function true_skip() returns (Word) { let missing: Word; return true ? 7 : missing; }",
  "function false_skip() returns (Word) { let missing: Word; return false ? missing : 3; }",
  "function condition_fault() returns (Word) { let missing: Bool; let otherMissing: Word; return missing ? otherMissing : 1; }",
  "function true_fault() returns (Word) { let missing: Word; let otherMissing: Word; return true ? missing : otherMissing; }",
  "function false_fault() returns (Word) { let missing: Word; let otherMissing: Word; return false ? otherMissing : missing; }",
  "function nested() returns (Bool) { let missing: Bool; return !(false ? (true && missing) : (true ? false : missing)); }",
  "function arithmetic() returns (Word) { let missing: Word; return (true ? 7 : missing) + (false ? missing : 3); }",
  "function map_true() returns (mapping(Word => Word)) { let m: mapping(Word => Word); let other: mapping(Word => Word); return true ? m : other; }",
  "function map_false() returns (mapping(Word => Word)) { let m: mapping(Word => Word); let other: mapping(Word => Word); return false ? other : m; }",
  "function map_skip() returns ((mapping(Word => Word), Bool)) { let m: mapping(Word => Word); let missing: Bool; return (m, false ? missing : true); }",
  "function map_fault() returns ((mapping(Word => Word), Bool)) { let m: mapping(Word => Word); let other: mapping(Word => Word); let missing: Bool; return true ? (m, missing) : (other, false); }",
  "function parent(seed: Word) returns ((Word, Bool)) { let f = lam(flag) { return (true ? ~seed : seed + 3, flag); }; return f(true); }"]
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
      | .tuple ids => ids.flatMap (reached fuel source)
      | _ => [])
private def expected (name : String) (mapping : Value) : Option Value := match name with
  | "true_skip" => some (.word (Word.ofNatModulo 7))
  | "false_skip" => some (.word (Word.ofNatModulo 3))
  | "nested" => some (.bool true)
  | "arithmetic" => some (.word (Word.ofNatModulo 10))
  | "map_true" | "map_false" => some mapping
  | "map_skip" => some (.pair mapping (.bool true))
  | "parent" => some (.pair (.word (Word.ofNatModulo 7).bitNot) (.bool true))
  | _ => none
private def inspect {catalog : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (name : String) (expression : ExpressionId) : IO Unit := do
  let contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let representation := SourceCoreCompatibleFunctions.representation contextValues 150
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "conditional diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "conditional root diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let nodes := reached 100 source expression
  for node in nodes do
    assertTrue node.coercions.isEmpty "conditional fixture acquired an output coercion"
    match node.form with
    | .unary .. | .binary .. | .conditional .. => assertTrue node.requirements.isEmpty "conditional fixture acquired method dispatch evidence"
    | _ => pure ()
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let bindings ← ids.mapM fun binder => do
    let declared ← get "conditional binder" (SourceCoreDataPlaces.rootBinder source binder)
    let type ← get "conditional binder projection" (catalog.catalog.project declared.scheme.body)
    let initializer ← if declared.name == "missing" || declared.name == "otherMissing" then pure (OptionalCell.allocate type)
      else match declared.scheme.body with
      | .bool => pure (OptionalCell.allocateInitialized type (.bool true))
      | .word => pure (OptionalCell.allocateInitialized type (.word (Word.ofNatModulo (if declared.name == "b" then 3 else 7))))
      | .integer => pure (OptionalCell.allocateInitialized type (.integer (if declared.name == "b" then 3 else -7)))
      | .mapping .. => pure (OptionalCell.allocate type)
      | other => throw (IO.userError s!"unexpected conditional scope: {reprStr other}")
    pure (binder, type, initializer)
  let scope := bindings.map fun (id, type, _) => (id, type)
  let lowered ← get s!"actual contextual conditional {name}" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
    representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
    parent none 150 source scope expression reasonAt)
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"actual contextual conditional {name} failed native checker"
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
      assertTrue (store.length == bindings.length + 1) "conditional allocated unexpected cells"
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "conditional changed administrative closure"
      match expected name mappingValue with
      | some expected => assertTrue (value == .inRight .word expected) s!"conditional {name} wrong result: {reprStr value}"
      | none =>
        let faultNode ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "fault fixture lacks missing occurrence")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt faultNode.id))) s!"conditional {name} fault reason/order changed"
      for (position, (binder, type, _)) in bindings.zipIdx.map (fun (binding, position) => (position, binding)) do
        if type != .bool && type != .word && type != .integer then
          let declared ← get "mapping branch binder" (SourceCoreDataPlaces.rootBinder source binder)
          let expectedCell := if declared.name == "m" then Value.inRight .unit mappingValue else .inLeft type .unit
          assertTrue (store[bindings.length - position]? == some expectedCell)
            "conditional initialized the skipped mapping or lost the selected mapping"
    | other => throw (IO.userError s!"conditional {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let checkedProgram ← get "conditional checker" (checkProgram workspace)
  let roots := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"conditional specialization: {reprStr other}")
  let automatic ← get "actual conditional factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      let source := function.specialized.function.typedBody
      let expression ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some expression => pure expression | none => throw (IO.userError "conditional return missing")
      inspect automatic.prepared source function.signature.key none function.specialized.function.solvedRequirements name expression
      rootsSeen := rootsSeen + 1
  let mut parentsSeen := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      for entry in parent.source.nodes do
        match entry with
        | .expression node => match node.form with
          | .tuple [_, _] =>
            inspect automatic.prepared parent.source parent.caller.key (some parent) parent.caller.function.solvedRequirements "parent" node.id
            parentsSeen := parentsSeen + 1
          | _ => pure ()
        | _ => pure ()
  assertTrue (rootsSeen == 11) s!"conditional cases missing: {rootsSeen}"
  assertTrue (parentsSeen > 0) "full parent substitution conditional case missing"
  IO.println "actual contextual conditionals: lazy branches, nested primitives/products, fault order, mapping effects, ambient closure and resume GREEN"

end Tests.SourceCoreCompatibleExpressionConditionals
