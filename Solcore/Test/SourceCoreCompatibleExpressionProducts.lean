import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualProducts
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
namespace Tests.SourceCoreCompatibleExpressionProducts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionProducts CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_products", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "products.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def boolean (index : Nat) (value : Bool) : ExpressionNode :=
  { id := id index, span, type := .bool, form := .reference "boolean" (.builtinBoolean value) }
private def grouped : ExpressionNode := { id := id 2, span, type := .bool, form := .group (id 0) }
private def paired : ExpressionNode := { id := id 3, span, type := .product .bool .bool, form := .tuple [id 2, id 1] }
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 3)],
    nodes := [.expression (boolean 0 true), .expression (boolean 1 false), .expression grouped, .expression paired] }
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
  rcases member with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index native selected
  cases selected
private theorem syntaxTree : CompatibleExpressionProducts.Syntax source (id 3) :=
  .pair (node := paired) (by cbv) rfl
    (.group (node := grouped) (by cbv) rfl (.literal (node := boolean 0 true) (by cbv) (.bool _ _)))
    (.literal (node := boolean 1 false) (by cbv) (.bool _ _))
private theorem boolTyped {index : Nat} {value : Bool}
    (found : source.lookupExpression? (id index) = some (boolean index value)) :
    ExpressionHasType source context (id index) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := boolean index value) (rawType := .bool)
    (lookupExpression?_sound found) (.reference (.builtinBoolean value)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem groupedTyped : ExpressionHasType source context (id 2) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := grouped) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.group (boolTyped (value := true) (by cbv))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem pairedTyped : ExpressionHasType source context (id 3) (.product .bool .bool) := by
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
private def code : SourceCoreBasic.LoweredExpr :=
  ⟨.product .bool .bool, LocalSequence.pair .bool .bool (LanguageResult.success (.bool true)) (LanguageResult.success (.bool false))⟩
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
private theorem groupAccepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 9 compilation source [] (id 2) (fun _ => reason) =
    .ok ⟨.bool, LanguageResult.success (.bool true)⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 2).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 2) = some grouped := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 2) = .ok (grouped, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, grouped]
  rw [read]
  simp only [bind, Except.bind, grouped]
  have childEq := boolAccepted 7 0 true rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at childEq
  rw [childEq]
  rfl
private theorem accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 10 compilation source [] (id 3) (fun _ => reason) = .ok code := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 3).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 3) = some paired := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 3) = .ok (paired, .product .bool .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, paired]
  rw [read]
  simp only [bind, Except.bind, paired]
  have firstEq := groupAccepted
  have secondEq := boolAccepted 8 1 false rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at firstEq secondEq
  rw [firstEq]
  simp only [bind, Except.bind]
  rw [secondEq]
  rfl
private theorem certified : Tree 20 values source context [] (fun _ => reason) [] (id 3) code :=
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
      diagnostics compilation native parent none 10 source [] (id 3) (fun _ => reason) = .ok lowered) :
    Tree 20 values source context [] (fun _ => reason) [] (id 3) lowered := by
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

theorem accepted_pair_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {mapping world administrative environment canonical actual before store ξ value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
      administrative [] environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (completed : Evaluates actual store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source environment before (id 3) outcome after ∧
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
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function constants() returns ((Bool, Bool)) { return ((true), false); }",
    "function inputs(flag: Bool) returns ((Bool, Bool)) { return ((flag), true); }",
    "function lazyFault() returns ((mapping(Word => Word), Bool)) { let m: mapping(Word => Word); let b: Bool; return ((m), b); }",
    "function lazySuccess() returns ((mapping(Word => Word), Bool)) { let m: mapping(Word => Word); return ((m), true); }",
    "function parent(seed: Word) returns ((Word, Bool)) { let pairer = lam(flag) { return ((seed), flag); }; return pairer(true); }"
  ]}] }

private def selectedIds : Nat → TypedSource → ExpressionId → List Resolved.LocalId
  | 0, _, _ => []
  | fuel + 1, source, expression => match source.lookupExpression? expression with
    | none => []
    | some node => match node.form with
      | .reference _ (.local binder) => [binder]
      | .group inner => selectedIds fuel source inner
      | .tuple ids => ids.flatMap (selectedIds fuel source)
      | _ => []

private def inspect {catalog : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (faulting : Bool) (constantRight : Bool := true) : IO Nat := do
  let contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let representation := SourceCoreCompatibleFunctions.representation contextValues 100
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "product diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "product root diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let mut count := 0
  for entry in source.nodes do
    match entry with
    | .expression node =>
      match node.form with
      | .tuple [_, _] =>
        let ids := (selectedIds 100 source node.id).eraseDups
        let bindings ← ids.mapM fun binder => do
          let declared ← get "product binder" (SourceCoreDataPlaces.rootBinder source binder)
          let type ← get "product binder projection" (catalog.catalog.project declared.scheme.body)
          let initializer ← match declared.scheme.body with
            | .bool => pure (if faulting then OptionalCell.allocate type else OptionalCell.allocateInitialized type (.bool true))
            | .word => pure (OptionalCell.allocateInitialized type (.word (Word.ofNatModulo 5)))
            | .mapping .. => pure (OptionalCell.allocate type)
            | other => throw (IO.userError s!"unexpected pair scope: {reprStr other}")
          pure (binder, type, initializer)
        let scope := bindings.map fun (id, type, _) => (id, type)
        let lowered ← get "actual contextual pair" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
          representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
          parent none 100 source scope node.id reasonAt)
        let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
        let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
        let adminType := Ty.function .unit frameLayout.type
        let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
        let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
        let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
          .letE (.newCell adminType adminExpr) body, definitions⟩
        assertTrue native.check "actual contextual pair failed native checker"
        for fuel in [0, 3, 15, 1000] do
          let finished := match native.runStateful fuel with
            | .outOfFuel checkpoint => Core.runStateful 2000 checkpoint
            | other => other
          match finished with
          | .done value store =>
            assertTrue (store.length == bindings.length + 1) "pair allocated unexpected cells"
            assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
              "pair changed administrative closure"
            if faulting then
              match value with
              | .inLeft _ (.word token) =>
                let boolId ← match source.nodes.findSome? fun
                  | .expression node => match node.form with
                    | .reference _ (.local binder) => if (ids.contains binder && node.type == .bool) then some node.id else none
                    | _ => none
                  | _ => none with
                  | some id => pure id | none => throw (IO.userError "fault read missing")
                assertTrue (token == reasonAt boolId) "right fault lost occurrence token"
              | _ => throw (IO.userError "uninitialized right child did not fault")
            else
              let expectedLeft ← match node.type with
                | .product .bool .bool => pure (.bool true)
                | .product .word .bool => pure (.word (Word.ofNatModulo 5))
                | .product (.mapping key payload) .bool => do
                  let encoded ← get "expected empty mapping" (SourceCoreCompatibleValues.encode 100 contextValues
                    (.mapping key payload) (.mapping key payload []))
                  pure encoded.value
                | other => throw (IO.userError s!"unexpected product raw type: {reprStr other}")
              assertTrue (value == .inRight .word (.pair expectedLeft (.bool constantRight))) "pair success value/order changed"
            for (position, (_, type, _)) in bindings.zipIdx.map (fun (binding, position) => (position, binding)) do
              if type != .bool && type != .word then
                let location := bindings.length - position
                match store[location]? with
                | some (.inRight .unit _) => pure ()
                | _ => throw (IO.userError "left mapping effect missing after right completion")
          | other => throw (IO.userError s!"pair failed to finish: {reprStr other}")
        count := count + 1
      | _ => pure ()
    | _ => pure ()
  pure count

def run : IO Unit := do
  let checkedProgram ← get "product checker" (checkProgram workspace)
  let roots ← ["constants", "inputs", "lazyFault", "lazySuccess", "parent"].mapM fun name =>
    match checkedProgram.signatures.functions.find? (·.name == name) with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
    | none => throw (IO.userError s!"product root missing: {name}")
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"product specialization: {reprStr other}")
  let automatic ← get "actual product factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 300)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      rootsSeen := rootsSeen + (← inspect automatic.prepared function.specialized.function.typedBody
        function.signature.key none function.specialized.function.solvedRequirements (name == "lazyFault") (name != "constants"))
  let mut parentsSeen := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      parentsSeen := parentsSeen + (← inspect automatic.prepared parent.source parent.caller.key
        (some parent) parent.caller.function.solvedRequirements false)
  assertTrue (rootsSeen == 4) "root group/pair cases missing"
  assertTrue (parentsSeen > 0) "full parent substitution group/pair missing"
  IO.println "actual contextual group/pair: left effects, right fault, ambient closure, parent and resume GREEN"

end Tests.SourceCoreCompatibleExpressionProducts
