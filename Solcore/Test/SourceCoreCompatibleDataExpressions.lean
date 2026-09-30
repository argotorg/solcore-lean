import Solcore.Frontend.SourceCoreCompatibleDataExpressions
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Actual checked source leaves, compiled by the compatible policy, execute
in ordinary Core. Injected child effects test the callback composition order;
they are not a claim of whole-program source correspondence. Native helper
allocations are retained in the Core store and remain outside source heap
export until the compiler's marker policy is connected. -/

set_option autoImplicit false

namespace Tests.SourceCoreCompatibleDataExpressions
open Solcore Solcore.Frontend
open Solcore.Frontend.SourceInference (TypedSource ExpressionId ExpressionNode DataConstructorInstantiation)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def literal (value : Core.Value) : IO Core.Expr :=
  match SourceCoreCompatibleDataExpressions.quote value with
  | some expression => pure expression | none => throw (IO.userError "compatible test literal contains capability")
private def encoded (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty) (value : SourceCoreCompatibleValues.Value) :
    IO (SourceCoreCompatibleValues.Encoded 400 context type value) :=
  match SourceCoreCompatibleValues.encode 400 context type value with
  | .ok receipt => pure receipt | .error error => throw (IO.userError s!"compatible test encode failed: {reprStr error}")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "enum Tree<T> { Leaf(T), Branch(Tree<T>, Tree<T>) }",
    "function boxed(value: Word) returns (Box<Word>) { return .Box(value); }",
    "function branch(left: Tree<Word>, right: Tree<Word>, marker: Word) returns (Tree<Word>) { return .Branch(left, right); }",
    "function proxyValue() returns (@Word) { return @Word; }",
    "function find(marker: Word, table: mapping(@Word => Word), key: @Word) returns (Word) { return table[key]; }",
    "function defaultValue(table: mapping(Word => @Word), key: Word) returns (@Word) { return table[key]; }",
    "function missing(table: mapping(Word => Box<Word>), key: Word) returns (Box<Word>) { return table[key]; }",
    "function empty(key: Word) returns (Word) { let table: mapping(Word => Word); return table[key]; }",
    "function echo(value: Box<Word>) returns (Box<Word>) { return value; }"
  ]}] }

private def sourceFor (program : CheckedProgram) (name : String) : IO TypedSource := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature | _ => throw (IO.userError s!"compatible function missing: {name}")
  let request : SourceSpecializationWorklist.Request := ⟨signature.id, []⟩
  match SourceSpecializationWorklist.run program [request] 100 with
  | .ok (.complete plan) => match plan.specializations with
      | [specialized] => pure specialized.function.typedBody
      | _ => throw (IO.userError "compatible fixture specialization count changed")
  | result => throw (IO.userError s!"compatible specialization failed: {reprStr result}")

private def rootExpression (source : TypedSource) : IO ExpressionId :=
  match source.roots.filterMap (fun
    | .statement id => (source.lookupStatement? id).bind fun node => match node.form with
        | .returnStmt (some expression) => some expression | _ => none
    | _ => none) with
  | [root] => pure root | _ => throw (IO.userError "compatible fixture must have one top-level return")

private def scopeFor (context : SourceCoreCompatibleValues.Context) (source : TypedSource) : IO SourceCoreCompatibleDataExpressions.Scope := do
  let scope ← source.inputs.mapM fun binder =>
    match context.checked.catalog.project binder.scheme.body with
    | .ok type => pure (binder.id, type) | .error error => throw (IO.userError s!"compatible input projection failed: {reprStr error}")
  pure scope.reverse

private def localChild (context : SourceCoreCompatibleValues.Context) : SourceCoreCompatibleDataExpressions.ExpressionLowerer :=
  fun fuel source scope id reasonAt => do
    let (_, type) ← SourceCoreCompatibleDataExpressions.readExpression context.checked source id
    pure ⟨type, ← SourceCoreCompatibleDataExpressions.lowerRead fuel context source scope id (reasonAt id)⟩

private def effectChild (context : SourceCoreCompatibleValues.Context) : SourceCoreCompatibleDataExpressions.ExpressionLowerer :=
  fun fuel source scope id reasonAt => do
    let lowered ← localChild context fuel source scope id reasonAt
    let node ← match source.lookupExpression? id with
      | some node => pure node | none => throw (.missingExpression id)
    let digit := match node.form with
      | .reference "table" _ => 1 | .reference "key" _ => 2 | _ => 0
    pure ⟨lowered.type, .letE
      (.storeCell (.var 2) (.inRight .unit (.binary .wordAdd
        (.binary .wordMul (.caseE (.loadCell (.var 2)) (.word Core.Word.zero) (.var 0)) (.word (word 10)))
        (.word (word digit))))) (lowered.expression.weakenAt 0)⟩

private def keyFailure (context : SourceCoreCompatibleValues.Context) : SourceCoreCompatibleDataExpressions.ExpressionLowerer :=
  fun fuel source scope id reasonAt => do
    let (node, type) ← SourceCoreCompatibleDataExpressions.readExpression context.checked source id
    match node.form with
    | .reference "key" _ => pure ⟨type, Core.LanguageResult.failure type (.word (word 71))⟩
    | _ => effectChild context fuel source scope id reasonAt

private def branchFailure (context : SourceCoreCompatibleValues.Context) : SourceCoreCompatibleDataExpressions.ExpressionLowerer :=
  fun fuel source scope id reasonAt => do
    let (node, type) ← SourceCoreCompatibleDataExpressions.readExpression context.checked source id
    match node.form with
    | .reference "left" _ => pure ⟨type, Core.LanguageResult.failure type (.word (word 72))⟩
    | .reference "right" _ =>
        let lowered ← localChild context fuel source scope id reasonAt
        pure ⟨type, .letE (.storeCell (.var 0) (.inRight .unit (.word (word 999)))) (lowered.expression.weakenAt 0)⟩
    | _ => localChild context fuel source scope id reasonAt

private def bind (inputs : List (Core.Ty × Core.Value)) (body : Core.Expr) : IO Core.Expr := do
  let inputs ← inputs.mapM fun (type, value) => do pure (type, ← literal value)
  pure (inputs.foldr (fun (type, value) tail =>
    .letE (Core.OptionalCell.allocateInitialized type value) tail) body)

private def lower (context : SourceCoreCompatibleValues.Context) (source : TypedSource) (child : SourceCoreCompatibleDataExpressions.ExpressionLowerer)
    (arguments : List Core.Value) : IO Core.Program := do
  let scope ← scopeFor context source
  let root ← rootExpression source
  let lowered ← match SourceCoreCompatibleDataExpressions.lowerWithReasons 200 context child source scope root (fun _ => word 70) with
    | .ok lowered => pure lowered | .error error => throw (IO.userError s!"compatible source leaf failed: {reprStr error}")
  assertTrue (arguments.length == source.inputs.length) "compatible test input arity mismatch"
  let body ← bind ((scope.reverse.map Prod.snd).zip arguments) lowered.expression
  pure ⟨Core.LanguageResult.resultType lowered.type, body, context.checked.catalog.definitions⟩

private def completes (program : Core.Program) (expected : Core.Value) : IO Core.Store := do
  assertTrue program.check "compatible generated expression failed Core checking"
  match program.runStateful 100000 with
  | .done actual store => assertTrue (actual == expected) s!"compatible expression result changed: {reprStr actual}"; pure store
  | result => throw (IO.userError s!"compatible expression failed: {reprStr result}")

private def compare (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty) (left right : Core.Expr)
    (expected : Bool) : IO Unit := do
  let comparator ← match SourceCoreCompatibleDataEquality.prepare 300 context.checked type with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"compatible comparator failed: {reprStr error}")
  discard <| completes ⟨.bool, .apply comparator.expression (.pair left right), context.checked.catalog.definitions⟩ (.bool expected)

private def modify (source : TypedSource) (id : ExpressionId) (f : ExpressionNode → ExpressionNode) : TypedSource :=
  {source with nodes := source.nodes.map fun
    | .expression node => .expression (if node.id = id then f node else node)
    | node => node}

example {context : SourceCoreCompatibleValues.Context} {environment : Core.Context} (accepted : SourceCoreCompatibleDataExpressions.Certified context environment) :
    Core.HasType environment accepted.lowered.expression (Core.LanguageResult.resultType accepted.lowered.type)
      context.checked.catalog.definitions := accepted.typed

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"compatible leaf fixture rejected: {reprStr error}")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some signature => pure signature | none => throw (IO.userError "compatible Box missing")
  let tree ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some signature => pure signature | none => throw (IO.userError "compatible Tree missing")
  let boxType := TypeSystem.Ty.nominal box.id [.word]
  let treeType := TypeSystem.Ty.nominal tree.id [.word]
  let proxyType := TypeSystem.Ty.proxy .word
  let proxyMap := TypeSystem.Ty.mapping proxyType .word
  let defaultMap := TypeSystem.Ty.mapping .word proxyType
  let nominalMap := TypeSystem.Ty.mapping .word boxType
  let functionType := TypeSystem.Ty.function .word .word
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 200
      [boxType, treeType, proxyType, .proxy (.comptime .word), proxyMap, defaultMap, nominalMap,
        .mapping .word .word, functionType] with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"compatible leaf catalog failed: {reprStr error}")
  let context := SourceCoreCompatibleValues.Context.initial checked
  let boxConstructor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "compatible Box constructor missing")
  let leafConstructor ← match tree.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "compatible Leaf constructor missing")
  let boxMetadata : DataConstructorInstantiation := ⟨boxConstructor.id,
    box.parameters.zip [.word], [.word], boxType⟩
  let stagedBox : DataConstructorInstantiation := ⟨boxConstructor.id,
    box.parameters.zip [.comptime .word], [.comptime .word], .nominal box.id [.comptime .word]⟩
  let ordinaryBox ← encoded context boxType (.constructed boxMetadata [.word (word 7)])
  let stageBox ← encoded ordinaryBox.context boxType (.constructed stagedBox [.word (word 7)])
  let proxy ← encoded stageBox.context proxyType (.proxy .word)
  let stageProxy ← encoded proxy.context proxyType (.proxy (.comptime .word))
  let mapping ← encoded stageProxy.context proxyMap (.mapping proxyType .word [
    (.proxy (.comptime .word), .word (word 7)), (.proxy (.comptime .word), .word (word 99))])
  let defaults ← encoded mapping.context defaultMap (.mapping .word (.proxy (.comptime .word)) [])
  let missing ← encoded defaults.context nominalMap (.mapping .word boxType [])
  let context := missing.context

  let boxedSource ← sourceFor program "boxed"
  let boxed ← lower context boxedSource (localChild context) [.word (word 7)]
  discard <| completes boxed (.inRight .word ordinaryBox.value)
  let proxyProgram ← lower context (← sourceFor program "proxyValue") (localChild context) []
  discard <| completes proxyProgram (.inRight .word proxy.value)
  let findSource ← sourceFor program "find"
  let find ← lower context findSource (effectChild context) [.word Core.Word.zero, mapping.value, stageProxy.value]
  let findStore ← completes find (.inRight .word (.word (word 7)))
  assertTrue (findStore[0]? == some (.inRight .unit (.word (word 12)))) "compatible base/key order changed"
  let canonicalFind ← lower context findSource (localChild context) [.word Core.Word.zero, mapping.value, proxy.value]
  discard <| completes canonicalFind (.inRight .word (.word Core.Word.zero))
  let failedKey ← lower context findSource (keyFailure context) [.word Core.Word.zero, mapping.value, stageProxy.value]
  let failedKeyStore ← completes failedKey (.inLeft .word (.word (word 71)))
  assertTrue (failedKeyStore.length == 3 && failedKeyStore[0]? == some (.inRight .unit (.word (word 1))))
    "failed key evaluated comparator or changed failure effects"
  let defaultProgram ← lower context (← sourceFor program "defaultValue") (localChild context) [defaults.value, .word (word 123)]
  discard <| completes defaultProgram (.inRight .word stageProxy.value)
  let missingProgram ← lower context (← sourceFor program "missing") (localChild context) [missing.value, .word (word 123)]
  let missingType ← match checked.catalog.project boxType with
    | .ok type => pure type | .error _ => throw (IO.userError "compatible Box projection missing")
  let header ← match missing.value with
    | .pair (.word id) _ => pure id | _ => throw (IO.userError "compatible missing header malformed")
  discard <| completes missingProgram (.inLeft missingType (.word ((word 70).add header)))

  let leafMeta : DataConstructorInstantiation := ⟨leafConstructor.id, tree.parameters.zip [.word], [.word], treeType⟩
  let leaf ← encoded context treeType (.constructed leafMeta [.word (word 8)])
  let failedBranch ← lower leaf.context (← sourceFor program "branch") (branchFailure leaf.context)
    [leaf.value, leaf.value, .word Core.Word.zero]
  let treeNative ← match checked.catalog.project treeType with
    | .ok type => pure type | .error _ => throw (IO.userError "compatible Tree projection missing")
  let branchStore ← completes failedBranch (.inLeft treeNative (.word (word 72)))
  assertTrue (branchStore.length == 3 && branchStore[2]? == some (.inRight .unit (.word Core.Word.zero)))
    "constructor failure executed a later child mutation"

  let emptySource ← sourceFor program "empty"
  let binding ← match (SourceCoreDataPlaces.declaredBinders emptySource).filter (·.name == "table") with
    | [binding] => pure binding | _ => throw (IO.userError "compatible empty binder missing")
  let mapType ← match checked.catalog.project binding.scheme.body with
    | .ok type => pure type | .error _ => throw (IO.userError "compatible empty projection missing")
  let root ← rootExpression emptySource
  let emptyBody ← match SourceCoreCompatibleDataExpressions.lowerWithReasons 200 context (localChild context)
      emptySource ((binding.id, mapType) :: (← scopeFor context emptySource)) root (fun _ => word 70) with
    | .ok lowered => pure lowered.expression | .error error => throw (IO.userError s!"compatible empty lower failed: {reprStr error}")
  let emptyProgram : Core.Program := ⟨Core.LanguageResult.resultType .word,
    .letE (Core.OptionalCell.allocateInitialized .word (.word (word 9)))
      (.letE (Core.OptionalCell.allocate mapType) emptyBody), checked.catalog.definitions⟩
  let emptyStore ← completes emptyProgram (.inRight .word (.word Core.Word.zero))
  let emptyValue ← encoded context binding.scheme.body (.mapping .word .word [])
  assertTrue (emptyStore[1]? == some (.inRight .unit emptyValue.value)) "uninitialized mapping did not retain its declared raw header"

  -- Retained member metadata selects stored fields and keeps the raw prefix
  -- out of the source-visible payload index. This constructed IR leaf does
  -- not assert that a new source spelling is accepted by the checker.
  let echoSource ← sourceFor program "echo"
  let echoRoot ← rootExpression echoSource
  let echoNode ← match echoSource.lookupExpression? echoRoot with
    | some node => pure node | none => throw (IO.userError "compatible echo base missing")
  let memberId : ExpressionId := ⟨{echoRoot.occurrence with index := echoRoot.occurrence.index + echoSource.nodes.length + 1}⟩
  let memberNode := {echoNode with
    id := memberId
    type := .word
    form := .member echoRoot "field" 0
    requirements := []
    coercions := []}
  let memberSource := {echoSource with nodes := echoSource.nodes ++ [.expression memberNode]}
  let memberCode ← match SourceCoreCompatibleDataExpressions.lowerWithReasons 200 context (localChild context)
      memberSource (← scopeFor context echoSource) memberId (fun _ => word 70) with
    | .ok lowered => pure lowered.expression | .error error => throw (IO.userError s!"compatible member leaf failed: {reprStr error}")
  discard <| completes ⟨Core.LanguageResult.resultType .word,
      ← bind [(missingType, stageBox.value)] memberCode, checked.catalog.definitions⟩ (.inRight .word (.word (word 7)))

  -- Bare mapping materialization follows the raw declared cell type. An
  -- outer staging wrapper still has the same native type, but its absent
  -- source cell is an uninitialized-local failure rather than a fresh map.
  let stagedDeclared := {emptySource with nodes := emptySource.nodes.map fun
    | .statement node => .statement (match node.form with
        | .letDecl binder initial =>
            let stagedBinder := {binder with scheme := {binder.scheme with body := .comptime binder.scheme.body}}
            {node with form := .letDecl stagedBinder initial}
        | _ => node)
    | node => node}
  let stagedDeclaredCode ← match SourceCoreCompatibleDataExpressions.lowerWithReasons 200 context (localChild context)
      stagedDeclared ((binding.id, mapType) :: (← scopeFor context emptySource)) root (fun _ => word 70) with
    | .ok lowered => pure lowered.expression | .error error => throw (IO.userError s!"compatible staged raw cell failed: {reprStr error}")
  let stagedDeclaredProgram : Core.Program := ⟨Core.LanguageResult.resultType .word,
    .letE (Core.OptionalCell.allocateInitialized .word (.word (word 9)))
      (.letE (Core.OptionalCell.allocate mapType) stagedDeclaredCode), checked.catalog.definitions⟩
  let stagedDeclaredStore ← completes stagedDeclaredProgram (.inLeft .word (.word (word 70)))
  assertTrue (stagedDeclaredStore.length == 2 && stagedDeclaredStore[1]? == some (.inLeft mapType .unit))
    "outer staging wrapper on a declared cell incorrectly materialized a mapping"

  compare context proxyType (← literal proxy.value) (← literal proxy.value) true
  compare context proxyType (← literal proxy.value) (← literal stageProxy.value) false
  compare context boxType (← literal ordinaryBox.value) (← literal ordinaryBox.value) true
  compare context boxType (← literal ordinaryBox.value) (← literal stageBox.value) false
  compare context treeType (← literal leaf.value) (← literal leaf.value) true
  compare context proxyMap (← literal mapping.value) (← literal mapping.value) false
  let closure : Core.Expr := .lambda .word (Core.LanguageResult.resultType .word) (Core.LanguageResult.success (.var 0))
  let named := Core.CallableContract.wrap (word 41) (Core.TaggedFunction.identified (word 7) closure)
  let namedOtherContract := Core.CallableContract.wrap (word 42) (Core.TaggedFunction.identified (word 7) closure)
  let anonymous := Core.CallableContract.wrap (word 41) (Core.TaggedFunction.anonymous closure)
  compare context functionType named namedOtherContract true
  compare context functionType anonymous anonymous false
  for fuel in List.range 70 do
    match find.runStateful fuel with
    | .outOfFuel checkpoint =>
        match Core.runStateful 100000 checkpoint with
        | .done result _ => assertTrue (result == .inRight .word (.word (word 7))) "compatible resume changed result"
        | _ => throw (IO.userError "compatible resume failed")
    | .done result _ => assertTrue (result == .inRight .word (.word (word 7))) "compatible finite run changed result"
    | .fault error _ => throw (IO.userError s!"compatible fuel reached a machine fault: {reprStr error}")

  let boxedRoot ← rootExpression boxedSource
  let forged := modify boxedSource boxedRoot fun node => match node.form with
    | .constructor instantiation children => {node with form := .constructor {instantiation with payloadTypes := [.bool]} children}
    | _ => node
  match SourceCoreCompatibleDataExpressions.lowerWithReasons 200 context (localChild context) forged (← scopeFor context boxedSource) boxedRoot (fun _ => word 70) with
  | .error _ => pure () | .ok _ => throw (IO.userError "compatible constructor metadata forgery accepted")
  let proxySource ← sourceFor program "proxyValue"
  let proxyRoot ← rootExpression proxySource
  let undiscovered := modify proxySource proxyRoot fun node => {node with
    type := .proxy (.comptime (.comptime .word)),
    form := .proxy (.comptime (.comptime .word))}
  match SourceCoreCompatibleDataExpressions.lowerWithReasons 200 context (localChild context) undiscovered [] proxyRoot (fun _ => word 70) with
  | .error _ => pure () | .ok _ => throw (IO.userError "compatible leaf silently extended the frozen metadata inventory")
  let foreign := {boxedRoot with occurrence := {boxedRoot.occurrence with owner := {boxedSource.owner with declarationIndex := 999}}}
  match SourceCoreCompatibleDataExpressions.readExpression checked boxedSource foreign with
  | .error _ => pure () | .ok _ => throw (IO.userError "compatible foreign expression occurrence accepted")
  IO.println "compatible expression leaves, raw comparison, ordering and resume GREEN"

end Tests.SourceCoreCompatibleDataExpressions
