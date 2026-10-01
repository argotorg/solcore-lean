import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualIndices
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual scalar-key indexing discharges its own child meanings. The theorem
fixture has an ambient closure and a typed hidden Integer slot; generated
comparators allocate after that prefix while lazy source initialization persists. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionIndices
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionIndices CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"index_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "index_meaning.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def mappingType : TypeSystem.Ty := .mapping .bool .bool
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono mappingType, [], false, none⟩
private def baseNode : ExpressionNode := { id := id 0, span, type := mappingType, form := .reference "table" (.local binder.id) }
private def keyNode : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def indexNode : ExpressionNode := { id := id 2, span, type := .bool, form := .index (id 0) (id 1) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression (id 2)], nodes := [.expression baseNode, .expression keyNode, .expression indexNode] }
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem mappingAdmitted : TypeAdmissible context mappingType := .mapping boolAdmitted boolAdmitted
private theorem baseTyped : ExpressionHasType source context (id 0) mappingType := by
  apply ExpressionHasType.ofOrdinary (node := baseNode) (rawType := mappingType) (lookupExpression?_sound (by rfl))
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible mappingAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply mappingType)
      (by simp) (by intro _ member; cases member) (.nil)))) mappingAdmitted mappingAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem keyTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.index baseTyped keyTyped) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem syntaxTree : CompatibleExpressionIndices.Syntax source (id 2) :=
  .index (node := indexNode) (keyNode := keyNode) (by cbv) rfl (by cbv) .bool
    (.fragment (.fragment (.fragment (.primitive (.product (.read (node := baseNode) (by cbv) rfl))))))
    (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := keyNode) (by cbv) (.bool _ _)))))))
private theorem contextValid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
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
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 2) (fun _ => reason) = .ok code) :
    Tree 100 values source context [] (fun _ => reason) scope (id 2) code :=
  tree_of_functions unique declarations (by rfl) rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) indexTyped accepted

private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def model := CompatibleAmbientHeap.payloadModel checked values.registry functions
private def faults : FunctionCalls.FaultRep := fun error token =>
  ((∃ location, error = .uninitializedLocation location) ∧ token = reason) ∨
  (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ error = .missingMappingDefault value ∧ token = reason.add tag)
private theorem uninitialized : ∀ (id : ExpressionId) location, faults (.uninitializedLocation location) ((fun _ => reason) id) :=
  fun _ location => .inl ⟨⟨location, rfl⟩, rfl⟩
private theorem missing : ∀ (id : ExpressionId) key value tag, MetadataRep values.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((fun _ => reason) id).add tag) :=
  fun _ key value tag owned => .inr ⟨key, value, tag, owned, rfl, rfl⟩
private def administrativeType : Ty := .function .unit frameLayout.type
private def administrativeValue : Value := .closure .unit frameLayout.type (.var 1) [SourceCoreCallableIndexedFrames.encode frameLayout .empty]
private theorem frameRegistered : frameLayout.Registered ambient.definitions := by
  constructor
  simp [ambient, AmbientDefinitions.append, frameLayout]
private theorem administrativeTyped : RuntimeValueHasType [] administrativeValue administrativeType ambient.definitions :=
  .closure (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty) .nil) (.var rfl)
private def world : StoreTyping := [administrativeType, OptionalCell.cellType nativeType]
private def store : Store := [administrativeValue, .inLeft nativeType .unit]
private def environment : Environment := [.cellRef (OptionalCell.cellType nativeType) 1]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[⟨mappingType, none, none⟩]⟩
private def after : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping .bool .bool []), none⟩]⟩
private theorem initial : GenericHeap.HeapRepresents model [1] world before store ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [1] world [] scope sourceEnvironment environment ambient.definitions := by
  have empty := (GenericHeap.HeapRepresents.empty (model := model)).allocate_administrative administrativeTyped
  obtain ⟨heap, reference⟩ := empty.allocate (.uninitialized projected) Dynamic.Heap.Allocates.append
  exact ⟨heap, .cons reference (.nil .nil)⟩
private theorem locals : Dynamic.EnvironmentAgrees before context.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem actualTyped : RuntimeEnvironmentHasTypes world (.integer 99 :: administrativeValue :: environment)
    [.integer, administrativeType, .cell (OptionalCell.cellType nativeType)] ambient.definitions :=
  .cons .integer (.cons (administrativeTyped.weaken ⟨world, rfl⟩) (.cons (.cellRef rfl) .nil))
private def ξ : Renaming := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
private theorem agrees : EnvironmentsAgree ξ environment (.integer 99 :: administrativeValue :: environment) :=
  GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (show EnvironmentsAgree Renaming.id environment environment from fun {_ _} found => found) administrativeValue) (.integer 99)
private theorem sourceTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 2) (.value (.bool false)) after := by
  apply Dynamic.ExpressionEvaluatesOutcome.value
  apply Dynamic.ExpressionEvaluates.intro (raw := .bool false) (middle := after) (lookupExpression?_sound (node := indexNode) (by cbv))
  · change Dynamic.ExpressionFormEvaluates program context [] source sourceEnvironment before (.index (id 0) (id 1)) [] [] (.bool false) after
    apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (lookupExpression?_sound (node := baseNode) (by rfl))
        (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil
    · exact .intro (lookupExpression?_sound (node := keyNode) (by cbv)) (.builtinBoolean rfl) .nil
    · exact .nil
    · exact .bool
  · exact .nil

/-- A real accepted expression constructs its own comparator execution after
source initialization, retaining an ambient closure that is not base-typable. -/
theorem accepted_lazy_preserves {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 2) (fun _ => reason) = .ok code) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (.integer 99 :: administrativeValue :: environment) store (code.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .bool code.type faults (.value (.bool false)) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves (values := values) functions (.refl _) program [] contextValid unique uninitialized missing (certified accepted)
    (show source.lookupExpression? (id 2) = some indexNode by cbv) initial.2 initial.1 locals agrees actualTyped sourceTrace

/-- Source traces and effects follow from completion alone; no source run or
helper evaluation is supplied as a premise. -/
theorem accepted_index_reflects {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 2) (fun _ => reason) = .ok code)
    {value : Value} {finalStore : Store} (completed : Evaluates (.integer 99 :: administrativeValue :: environment) store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 2) outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .bool code.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects (values := values) functions (.refl _) program [] contextValid uninitialized missing (certified accepted)
    (show source.lookupExpression? (id 2) = some indexNode by cbv) initial.2 initial.1 locals agrees actualTyped completed

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def sources : List String := [
  "enum Empty { Missing(Word) }",
  "function word_duplicate(m: mapping(Word => Word)) returns (Word) { return m[1]; }",
  "function word_default(m: mapping(Word => Word)) returns (Word) { return m[9]; }",
  "function bool_alias(m: mapping(Bool => Bool)) returns (Bool) { return m[true]; }",
  "function nested(m: mapping(Bool => mapping(Bool => Bool))) returns (Bool) { return m[true][false]; }",
  "function nested_default(m: mapping(Bool => mapping(Bool => Bool))) returns (Bool) { return m[false][true]; }",
  "function missing_default(m: mapping(Bool => Empty)) returns (Empty) { return m[true]; }",
  "function key_fault() returns (Word) { let m: mapping(Word => Word); let missing: Word; return m[missing]; }",
  "function base_fault() returns (Word) { let m: mapping(Bool => mapping(Word => Word)); let missing: Bool; return m[missing][1]; }",
  "function lazy_skip() returns (Bool) { let m: mapping(Bool => Bool); let missing: Bool; return m[false && missing]; }",
  "function parent(seed: Word) returns (Word) { let f = lam(item) -> Word { let m: mapping(Word => Word); return m[~seed]; }; return f(true); }"]
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
      | .index base key => reached fuel source base ++ reached fuel source key
      | .group inner => reached fuel source inner
      | .tuple ids | .constructor _ ids => ids.flatMap (reached fuel source)
      | _ => [])
private def initialMapping (name : String) (type : TypeSystem.Ty) : SourceCoreCompatibleValues.Value :=
  if name == "word_duplicate" then .mapping .word .word [(.word (Word.ofNatModulo 1), .word (Word.ofNatModulo 7)), (.word (Word.ofNatModulo 1), .word (Word.ofNatModulo 9))]
  else if name == "bool_alias" then .mapping (.comptime .bool) .bool [(.bool true, .bool true), (.bool true, .bool false)]
  else if name == "integer_duplicate" then .mapping .integer .integer [(.integer (-1), .integer (-7)), (.integer (-1), .integer 99)]
  else if name == "nested" || name == "nested_default" then
    .mapping .bool (.mapping .bool .bool) [(.bool true, .mapping .bool .bool [(.bool false, .bool true), (.bool false, .bool false)])]
  else match type with | .mapping key value => .mapping key value [] | _ => .unit
private def inspect {catalog : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (name : String) (expression : ExpressionId) : IO Unit := do
  let mut contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "index diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "index owner diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let nodes := reached 100 source expression
  for node in nodes do
    assertTrue node.coercions.isEmpty "index fixture acquired an output coercion"
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let mut bindings : List (Resolved.LocalId × Ty × Expr × Option Value) := []
  for binderId in ids do
    let declared ← get "index binder" (SourceCoreDataPlaces.rootBinder source binderId)
    let type ← get "index binder projection" (catalog.catalog.project declared.scheme.body)
    let (initializer, expected) ← if declared.name == "missing" then pure (OptionalCell.allocate type, none)
      else if declared.name == "seed" then pure (OptionalCell.allocateInitialized type (.word (Word.ofNatModulo 7)), some (.word (Word.ofNatModulo 7)))
      else if name == "key_fault" || name == "base_fault" || name == "lazy_skip" || name == "parent" then do
        let encoded ← get "expected initialized empty mapping" (SourceCoreCompatibleValues.encode 150 contextValues declared.scheme.body (initialMapping "empty" declared.scheme.body))
        contextValues := encoded.context
        pure (OptionalCell.allocate type, some encoded.value)
      else do
        let encoded ← get "index input encoding" (SourceCoreCompatibleValues.encode 150 contextValues declared.scheme.body (initialMapping name declared.scheme.body))
        contextValues := encoded.context
        let literal ← match SourceCoreCompatibleDataExpressions.quote encoded.value with
          | some literal => pure literal
          | none => throw (IO.userError "mapping input is not quotable")
        pure (OptionalCell.allocateInitialized type literal, some encoded.value)
    bindings := bindings ++ [(binderId, type, initializer, expected)]
  let scope := bindings.map fun (id, type, _, _) => (id, type)
  let representation := SourceCoreCompatibleFunctions.representation contextValues 150
  let lowered ← get s!"actual contextual index {name}" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
    representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
    parent none 150 source scope expression reasonAt)
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer, _) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"actual contextual index {name} failed native checker"
  let root ← match source.lookupExpression? expression with
    | some node => pure node | none => throw (IO.userError "index root missing")
  let malformed : TypedSource := {source with nodes := source.nodes.map fun
    | .expression node => if node.id == expression then .expression {node with type := .unit} else .expression node
    | other => other}
  match SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation catalog.signatures prepared.locals prepared.contexts
    own.assignments diagnostics compilation prepared.callableContext parent none 150 malformed scope expression reasonAt with
  | .ok _ => throw (IO.userError "index mismatched result type accepted")
  | .error _ => pure ()
  for fuel in [0, 3, 15, 1000] do
    let finished := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 30000 checkpoint
      | other => other
    match finished with
    | .done value store =>
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "index changed administrative prefix"
      if name == "key_fault" || name == "base_fault" then
        let missing ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "index missing occurrence absent")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt missing.id))) s!"index {name} changed fault order"
        assertTrue (store.length == bindings.length + 1) "index prepared comparator before successful key"
      else if name == "missing_default" then
        let input ← get "missing-default expected carrier" (SourceCoreCompatibleValues.encode 150 contextValues
          (match root.form with | .index base _ => (source.lookupExpression? base).map (·.type) |>.getD .unit | _ => .unit)
          (initialMapping name (match root.form with | .index base _ => (source.lookupExpression? base).map (·.type) |>.getD .unit | _ => .unit)))
        let .pair (.word tag) _ := input.value | throw (IO.userError "missing-default carrier shape")
        assertTrue (value == .inLeft lowered.type (.word ((reasonAt root.id).add tag))) "index missing-default token lost raw header"
        assertTrue (store.length > bindings.length + 1) "index skipped comparator allocation"
      else
        let .inRight .word payload := value | throw (IO.userError s!"index {name} unexpectedly failed: {reprStr value}")
        let decoded ← get "index result decode" (SourceCoreCompatibleValues.decode 150 contextValues root.type payload)
        let expected := match name with
          | "word_duplicate" => SourceCoreDataValues.Value.word (Word.ofNatModulo 7)
          | "word_default" | "parent" => .word Word.zero
          | "bool_alias" | "nested" => .bool true
          | "integer_duplicate" => .integer (-7)
          | _ => .bool false
        assertTrue (decoded == expected) s!"index {name} wrong selection/default: {reprStr decoded}"
        assertTrue (store.length > bindings.length + 1) "index comparator did not allocate its typed cells"
      for ((_, _, _, expected), position) in bindings.zipIdx do
        match expected with
        | some payload => assertTrue (store[bindings.length - position]? == some (.inRight .unit payload)) "index lost base/key prefix effects"
        | none => pure ()
    | other => throw (IO.userError s!"index {name} failed to finish: {reprStr other}")
/-- Integer is exercised as retained IR; the surface checker does not expose
an Integer type name. The compiler and independent static profile do support it. -/
private def inspectIntegerIR : IO Unit := do
  let checked ← get "Integer retained catalog" (SourceCoreCompatibleCatalog.prepare signatures 100 [.mapping .integer .integer])
  let values := SourceCoreCompatibleValues.Context.initial checked
  let encoded ← get "Integer retained input" (SourceCoreCompatibleValues.encode 100 values (.mapping .integer .integer)
    (initialMapping "integer_duplicate" (.mapping .integer .integer)))
  let values := encoded.context
  let native ← get "Integer retained projection" (checked.catalog.project (.mapping .integer .integer))
  let tableBinder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono (.mapping .integer .integer), [], false, none⟩
  let keyBinder : TypedBinder := ⟨⟨owner, 1⟩, "key", .mono .integer, [], false, none⟩
  let tableNode : ExpressionNode := {id := id 0, span, type := .mapping .integer .integer, form := .reference "table" (.local tableBinder.id)}
  let keyNode : ExpressionNode := {id := id 1, span, type := .integer, form := .reference "key" (.local keyBinder.id)}
  let root : ExpressionNode := {id := id 2, span, type := .integer, form := .index (id 0) (id 1)}
  let source : TypedSource := {owner, inputs := [tableBinder, keyBinder], roots := [.expression root.id], nodes := [.expression tableNode, .expression keyNode, .expression root]}
  let scope := [(tableBinder.id, native), (keyBinder.id, Ty.integer)]
  let code ← get "Integer retained actual lowering" (SourceCoreFunctions.lowerExpressionWithPolicy
    (SourceCoreCompatibleDataExpressions.functionPolicy 100 values) noBody 20 compilation source scope root.id (fun _ => reason))
  let literal ← match SourceCoreCompatibleDataExpressions.quote encoded.value with
    | some expression => pure expression | none => throw (IO.userError "Integer input quote failed")
  let body := Expr.letE (OptionalCell.allocateInitialized .integer (.integer (-1)))
    (.letE (OptionalCell.allocateInitialized native literal) code.expression)
  let program : Core.Program := ⟨LanguageResult.resultType code.type, body, checked.catalog.definitions⟩
  assertTrue program.check "Integer retained index failed Core checker"
  match program.runStateful 30000 with
  | .done (.inRight .word (.integer value)) store =>
    assertTrue (value == -7 && store.length > 2) "Integer retained duplicate selection/comparator allocation failed"
  | other => throw (IO.userError s!"Integer retained index failed: {reprStr other}")

def run : IO Unit := do
  inspectIntegerIR
  let checkedProgram ← get "index checker" (checkProgram workspace)
  let roots := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"index specialization: {reprStr other}")
  let automatic ← get "actual index factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      let source := function.specialized.function.typedBody
      let expression ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some expression => pure expression | none => throw (IO.userError "index return missing")
      inspect automatic.prepared source function.signature.key none function.specialized.function.solvedRequirements name expression
      rootsSeen := rootsSeen + 1
  let mut parentsSeen := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      for entry in parent.source.nodes do
        match entry with
        | .expression node => match node.form with
          | .index _ _ =>
            inspect automatic.prepared parent.source parent.caller.key (some parent) parent.caller.function.solvedRequirements "parent" node.id
            parentsSeen := parentsSeen + 1
          | _ => pure ()
        | _ => pure ()
  assertTrue (rootsSeen == 9) s!"index cases missing: {rootsSeen}"
  assertTrue (parentsSeen > 0) "full parent substitution index case missing"
  IO.println "actual contextual indices: scalar keys, duplicates, defaults, nested/raw header, ordered faults, lazy effects, parent, ambient comparator closures and resume GREEN"

end Tests.SourceCoreCompatibleExpressionIndices
