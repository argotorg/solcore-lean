import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualGeneral
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralMeaning
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! General product-key indexing discharges its own child meanings. The theorem
fixture has an ambient closure and a typed hidden Integer slot; generated
comparators allocate after that prefix while lazy source initialization persists. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleGeneralExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionGeneral CompatiblePayload GeneralHeap ReadOnly

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
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
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
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason) = .ok code) :
    Tree 100 values source context [] (fun _ => reason) scope (id 5) code :=
  tree_of_functions unique declarations (by rfl) rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) unaryTyped accepted

private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def identities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful identities :=
  ⟨fun impossible => False.elim impossible, fun impossible => False.elim impossible⟩
private theorem functionLeaves : CompatibleEquality.FunctionObservations checked.catalog functions identities :=
  fun impossible => False.elim impossible
private theorem functionTypes : CompatiblePayload.FunctionRuntimeViews functions := fun impossible => False.elim impossible

/-- Raw staging aliases remain distinct values even when their projected native
types coincide; the independently specified equality retains that distinction. -/
theorem proxy_aliases_distinct :
    ¬ Dynamic.ValueEquivalent (.proxy (.comptime .word)) (.proxy .word) := by
  rintro ⟨same, _⟩
  cases same

/-- Mapping contents have no comparable source-value witness. -/
theorem mapping_keys_unmatched {key value : TypeSystem.Ty}
    {entries : List (Dynamic.Value × Dynamic.Value)} {other : Dynamic.Value} :
    ¬ Dynamic.ValueEquivalent (.mapping key value entries) other := by
  rintro ⟨_, comparable⟩
  cases comparable
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
private def after : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping keyType .bool []), none⟩]⟩
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
private theorem indexTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 4) (.value (.bool false)) after := by
  apply Dynamic.ExpressionEvaluatesOutcome.value
  apply Dynamic.ExpressionEvaluates.intro (raw := .bool false) (middle := after) (lookupExpression?_sound (node := indexNode) (by cbv))
  · change Dynamic.ExpressionFormEvaluates program context [] source sourceEnvironment before (.index (id 0) (id 3)) [] [] (.bool false) after
    apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (lookupExpression?_sound (node := baseNode) (by rfl))
        (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil
    · exact .intro (lookupExpression?_sound (node := keyNode) (by cbv))
        (.tuple rfl (.cons (.intro (lookupExpression?_sound (node := trueNode) (by cbv)) (.builtinBoolean rfl) .nil)
          (.cons (.intro (lookupExpression?_sound (node := falseNode) (by cbv)) (.builtinBoolean rfl) .nil) .nil))
          (.cons (.singleton _))) .nil
    · exact .nil
    · exact .bool
  · exact .nil

private theorem sourceTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before
    (id 5) (.value (.bool true)) after := by
  cases indexTrace with
  | value trace =>
    exact .value (.intro (lookupExpression?_sound (node := unaryNode) (by cbv))
      (.unary (owned := []) rfl trace (.primitive (.logicalNot false))) .nil)

/-- A real accepted expression constructs its own comparator execution after
source initialization, retaining an ambient closure that is not base-typable. -/
theorem accepted_lazy_preserves {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason) = .ok code) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (.integer 99 :: administrativeValue :: environment) store (code.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .bool code.type faults (.value (.bool true)) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves (values := values) functions (.refl _) faithful functionLeaves functionTypes program [] contextValid unique uninitialized missing (certified accepted)
    (show source.lookupExpression? (id 5) = some unaryNode by cbv) initial.2 initial.1 locals agrees actualTyped sourceTrace

/-- Source traces and effects follow from completion alone; no source run or
helper evaluation is supplied as a premise. -/
theorem accepted_index_reflects {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason) = .ok code)
    {value : Value} {finalStore : Store} (completed : Evaluates (.integer 99 :: administrativeValue :: environment) store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 5) outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .bool code.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects (values := values) functions (.refl _) faithful functionLeaves functionTypes program [] contextValid uninitialized missing (certified accepted)
    (show source.lookupExpression? (id 5) = some unaryNode by cbv) initial.2 initial.1 locals agrees actualTyped completed


private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Key { Key(Bool) }",
    "enum Missing { Missing(Word) }",
    "enum Box { Box(Bool) }",
    "function product(m: mapping((Bool, Bool) => Bool)) returns (Bool) { return m[(true, false)]; }",
    "function lazyProduct() returns (Bool) { let m: mapping((Bool, Bool) => Bool); return m[(true, false)]; }",
    "function nestedProduct(m: mapping(((Bool, Bool), Word) => Bool)) returns (Bool) { return m[((true, false), 7)]; }",
    "function nestedGeneral(m: mapping((Bool, Bool) => mapping(@Word => Bool))) returns (Bool) { return m[(true, false)][@Word]; }",
    "function proxy(m: mapping(@Word => Bool)) returns (Bool) { return m[@Word]; }",
    "function nominal(m: mapping(Key => Bool)) returns (Bool) { return m[Key(true)]; }",
    "function mappingKey(m: mapping(mapping(Bool => Bool) => Bool), k: mapping(Bool => Bool)) returns (Bool) { return m[k]; }",
    "function operator(m: mapping((Bool, Bool) => Bool)) returns (Bool) { return !m[(true, false)] || m[(false, true)]; }",
    "function paired(m: mapping((Bool, Bool) => Bool)) returns ((Bool, Bool)) { return (m[(true, false)], !m[(false, true)]); }",
    "function choose(m: mapping((Bool, Bool) => Bool)) returns (Bool) { return m[(true, false)] ? m[(false, true)] : !m[(true, false)]; }",
    "function construct(m: mapping((Bool, Bool) => Bool)) returns (Box) { return Box(!m[(true, false)]); }",
    "function keyIndex(m: mapping((Bool, Bool) => Bool), n: mapping(Bool => Bool)) returns (Bool) { return n[m[(true, false)]]; }",
    "function skipped() returns (Box) { let m: mapping((Bool, Bool) => Bool); let missing: Bool; return Box(false && m[(true, missing)]); }",
    "function constructorFault() returns (Box) { let m: mapping((Bool, Bool) => Bool); let missing: Bool; return Box(m[(true, missing)]); }",
    "function parent(seed: Bool) returns (Box) { let make = lam(item) -> Box { let m: mapping((Bool, Bool) => Bool); return Box(!m[(seed, item)]); }; return make(false); }",
    "function keyFault() returns (Bool) { let m: mapping((Bool, Bool) => Bool); let missing: Bool; return m[(true, missing)]; }",
    "function defaultFault() returns (Missing) { let m: mapping((Bool, Bool) => Missing); return m[(true, false)]; }"]}] }

def run : IO Unit := do
  let code ← SourceCompilerFeatureSupport.get "general index actual lowering"
    (SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason))
  let state : Core.State := ⟨.eval (code.expression.rename ξ) (.integer 99 :: administrativeValue :: environment), [], store⟩
  let complete := Core.runStateful 30000 state
  match Core.LanguageResult.observeResult complete with
  | .succeeded (.bool true) finalStore =>
      SourceCompilerFeatureSupport.require (finalStore[0]? == some administrativeValue) "general index changed ambient closure"
  | _ => throw (IO.userError "general index static fixture failed")
  for fuel in [0, 5, 23] do
    match Core.runStateful fuel state with
    | .outOfFuel suspended =>
        SourceCompilerFeatureSupport.require (Core.runStateful 30000 suspended == complete) "general index resume changed native result/store"
    | _ => throw (IO.userError "general index prefix unexpectedly completed")
  let checked ← SourceCompilerFeatureSupport.get "general index source checker" (checkProgram rawWorkspace)
  let product ← SourceCompilerFeatureSupport.compileNamed checked "product"
  let pair : SourceCoreExecution.Value := .product (.bool true) (.bool false)
  let duplicate : SourceCoreExecution.Value := .mapping keyType .bool [(pair, .bool true), (pair, .bool false)]
  SourceCompilerFeatureSupport.require ((← product.run [duplicate]) == .bool true) "compound key lost first duplicate"
  product.checkResume [duplicate] (.bool true)
  let empty : SourceCoreExecution.Value := .mapping keyType .bool []
  SourceCompilerFeatureSupport.require ((← product.run [empty]) == .bool false) "compound key lost default"
  product.checkResume [empty] (.bool false)
  for name in ["operator", "choose"] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    for (input, expected) in [(duplicate, false), (empty, true)] do
      SourceCompilerFeatureSupport.require ((← entry.run [input]) == .bool expected)
        "general index under primitive/conditional changed result"
      entry.checkResume [input] (.bool expected)
  let paired ← SourceCompilerFeatureSupport.compileNamed checked "paired"
  let pairResult : SourceCoreExecution.Value := .product (.bool true) (.bool true)
  SourceCompilerFeatureSupport.require ((← paired.run [duplicate]) == pairResult) "general index tuple slots changed"
  paired.checkResume [duplicate] pairResult
  let boxDeclaration : ProgramDataSignature ← match checked.signatures.dataTypes.find? (·.name == "Box") with
    | some declaration => pure declaration | none => throw (IO.userError "general recursive Box absent")
  let boxConstructor : ProgramDataConstructorSignature ← match boxDeclaration.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "general recursive Box constructor absent")
  let boxMetadata : DataConstructorInstantiation := ⟨boxConstructor.id, [], [.bool], .nominal boxDeclaration.id []⟩
  let construct ← SourceCompilerFeatureSupport.compileNamed checked "construct"
  let boxTrue : SourceCoreExecution.Value := .constructed boxMetadata [.bool true]
  SourceCompilerFeatureSupport.require ((← construct.run [empty]) == boxTrue) "constructor lost general index payload"
  construct.checkResume [empty] boxTrue
  let skipped ← SourceCompilerFeatureSupport.compileNamed checked "skipped"
  let boxFalse : SourceCoreExecution.Value := .constructed boxMetadata [.bool false]
  SourceCompilerFeatureSupport.require ((← skipped.run []) == boxFalse) "short circuit ran general index child"
  skipped.checkResume [] boxFalse
  skipped.checkCells [] [(mappingType, none), (.bool, none)]
  let parent ← SourceCompilerFeatureSupport.compileNamed checked "parent"
  SourceCompilerFeatureSupport.require ((← parent.run [.bool true]) == boxTrue) "contextual lambda lost general index child"
  parent.checkResume [.bool true] boxTrue
  let keyIndex ← SourceCompilerFeatureSupport.compileNamed checked "keyIndex"
  let boolMap : SourceCoreExecution.Value := .mapping .bool .bool [(.bool true, .bool true)]
  SourceCompilerFeatureSupport.require ((← keyIndex.run [duplicate, boolMap]) == .bool true) "index key lost recursive general child"
  keyIndex.checkResume [duplicate, boolMap] (.bool true)
  let lazy ← SourceCompilerFeatureSupport.compileNamed checked "lazyProduct"
  SourceCompilerFeatureSupport.require ((← lazy.run []) == .bool false) "compound key lost lazy initialization"
  lazy.checkResume [] (.bool false)
  lazy.checkCells [] [(mappingType, some empty)]
  let nested ← SourceCompilerFeatureSupport.compileNamed checked "nestedProduct"
  let nestedKey : SourceCoreExecution.Value := .product pair (.word (Word.ofNatModulo 7))
  let nestedInput : SourceCoreExecution.Value := .mapping (.product keyType .word) .bool [(nestedKey, .bool true)]
  SourceCompilerFeatureSupport.require ((← nested.run [nestedInput]) == .bool true) "nested compound key changed equality"
  nested.checkResume [nestedInput] (.bool true)
  let nestedGeneral ← SourceCompilerFeatureSupport.compileNamed checked "nestedGeneral"
  let nestedGeneralInput : SourceCoreExecution.Value := .mapping keyType (.mapping (.proxy .word) .bool)
    [(pair, .mapping (.proxy .word) .bool [(.proxy .word, .bool true)])]
  SourceCompilerFeatureSupport.require ((← nestedGeneral.run [nestedGeneralInput]) == .bool true)
    "general index chain lost its intermediate mapping metadata"
  nestedGeneral.checkResume [nestedGeneralInput] (.bool true)
  let proxy ← SourceCompilerFeatureSupport.compileNamed checked "proxy"
  let proxyInput : SourceCoreExecution.Value := .mapping (.proxy (.comptime .word)) .bool
    [(.proxy (.comptime .word), .bool true), (.proxy .word, .bool false), (.proxy .word, .bool true)]
  SourceCompilerFeatureSupport.require ((← proxy.run [proxyInput]) == .bool false) "proxy key collapsed distinct raw metadata"
  proxy.checkResume [proxyInput] (.bool false)
  let declaration : ProgramDataSignature ← match checked.signatures.dataTypes.find? (·.name == "Key") with
    | some declaration => pure declaration | none => throw (IO.userError "general index nominal declaration missing")
  let constructor : ProgramDataConstructorSignature ← match declaration.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "general index nominal constructor missing")
  let metadata : DataConstructorInstantiation := ⟨constructor.id, [], [.bool], .nominal declaration.id []⟩
  let nominal ← SourceCompilerFeatureSupport.compileNamed checked "nominal"
  let nominalInput : SourceCoreExecution.Value := .mapping metadata.resultType .bool
    [(.constructed metadata [.bool true], .bool true), (.constructed metadata [.bool true], .bool false)]
  SourceCompilerFeatureSupport.require ((← nominal.run [nominalInput]) == .bool true) "nominal key lost constructor payload/duplicate order"
  nominal.checkResume [nominalInput] (.bool true)
  let mapping ← SourceCompilerFeatureSupport.compileNamed checked "mappingKey"
  let keyMapping : SourceCoreExecution.Value := .mapping .bool .bool [(.bool true, .bool false)]
  let mappingInput : SourceCoreExecution.Value := .mapping (.mapping .bool .bool) .bool [(keyMapping, .bool true)]
  SourceCompilerFeatureSupport.require ((← mapping.run [mappingInput, keyMapping]) == .bool false) "noncomparable mapping key incorrectly matched"
  mapping.checkResume [mappingInput, keyMapping] (.bool false)
  for name in ["keyFault", "constructorFault", "defaultFault"] do
    let failed ← SourceCompilerFeatureSupport.compileNamed checked name
    let invocation ← failed.invoke []
    match invocation.outcome with
    | .failed token _ =>
        match ← invocation.diagnostic token with
        | some {error := .uninitializedLocal _, span := some _, ..} =>
            SourceCompilerFeatureSupport.require (name == "keyFault" || name == "constructorFault") "general key failure diagnostic changed"
        | some {error := .typeMismatch _ none, span := some _, ..} =>
            SourceCompilerFeatureSupport.require (name == "defaultFault") "general default failure diagnostic changed"
        | _ => throw (IO.userError "general index lost exact failure diagnostic")
    | _ => throw (IO.userError "general index fault did not fail")
    if name == "keyFault" || name == "constructorFault" then
      failed.checkCells [] [(mappingType, some empty), (.bool, none)]
  IO.println "general recursive expressions: typed compound keys, metadata, duplicate order, lazy effects, faults and resume GREEN"
end Tests.SourceCoreCompatibleGeneralExpressions
