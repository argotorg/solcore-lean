import Solcore.Frontend.SourceCore.CompatibleFunctions
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceCore.Compatible
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PatternsAndArms
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MatchPrefixes
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalStatements
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MatchSelection
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality

/-!
# Compatible match tests

Compatible matches, patterns, composite data and paths.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleDataControl
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Checked source paths and pattern trees use the independent compatible
profile. These fragment programs check against their actual ambient definitions;
marked matcher allocations test lexical captures and source allocation order.
Public compiler routing and whole source heap export are separate integrations. -/

set_option autoImplicit false
namespace Tests.SourceCoreCompatibleDataControl
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference

private def w (value : Nat) : Word := Word.ofNatModulo value
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def quote (value : Value) : IO Expr :=
  match SourceCoreCompatibleDataExpressions.quote value with
  | some expression => pure expression | none => throw (IO.userError "compatible control literal contains capability")
private def encode (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty)
    (value : SourceCoreCompatibleValues.Value) : IO (SourceCoreCompatibleValues.Encoded 500 context type value) :=
  match SourceCoreCompatibleValues.encode 500 context type value with
  | .ok encoded => pure encoded | .error error => throw (IO.userError s!"compatible control encode failed: {reprStr error}")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function ordered(table: mapping(@Word => Word), key: @Word) returns (mapping(@Word => Word)) { table[key] += 3; return table; }",
    "function nested(table: mapping(Word => mapping(@Word => Word)), key: @Word) returns (mapping(Word => mapping(@Word => Word))) { table[1][key] += 5; return table; }",
    "function lazy() returns (mapping(Word => Word)) { let table: mapping(Word => Word); table[1] = 7; return table; }",
    "function rhsFailure() returns (Word) { let table: mapping(Word => Word); let absent: Word; table[1] += absent; return 0; }",
    "function missing(table: mapping(Word => Box<Word>), key: Word) returns (Word) { table[key] = .Box(7); return 7; }",
    "function choose(value: Box<Word>) returns (Word) { match (value) { case .Box(bound) { return bound; } default { return 99; } } }",
    "function tuple(value: (Box<Word>, (Bool, Word))) returns (Word) { match (value) { case (.Box(bound), (flag, right)) { return flag ? bound + right : right; } default { return 99; } } }",
    "function scrutineeFailure(value: Box<Word>) returns (Word) { let absent: Box<Word>; match (absent) { case .Box(bound) { return bound; } default { return 99; } } }",
    "function member(value: Box<Word>) returns (Box<Word>) { value = value; return value; }"
  ]}] }

private def planFor (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Plan := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature | _ => throw (IO.userError s!"compatible control function missing: {name}")
  match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 100 with
  | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"compatible control specialization failed: {reprStr result}")

private def single (plan : SourceSpecializationWorklist.Plan) : IO SourceSpecialization.SpecializedFunction :=
  match plan.specializations with
  | [specialized] => pure specialized | _ => throw (IO.userError "compatible control plan count changed")

private def bindInputs (inputs : List (Ty × Value)) (body : Expr) : IO Expr := do
  let inputs ← inputs.mapM fun (type, value) => do pure (type, ← quote value)
  pure (inputs.foldr (fun (type, value) next => .letE (OptionalCell.allocateInitialized type value) next) body)

private def bodyLowerer (values : SourceCoreCompatibleValues.Context)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (owner : SourceSpecialization.SpecializationKey)
    (sourceCells : Option SourceCoreSourceCells.Allocator) (definitions : DataEnvironment) : SourceCoreFunctions.BodyLowerer :=
  fun child fuel source scope statements result reasonAt fellThrough escaped =>
    let assignments := (diagnostics.base.find? owner).map (·.assignments) |>.getD ⟨[]⟩
    SourceCoreLoops.lowerStatementsWithPolicy
      (SourceCoreCompatibleDataMatches.loopPolicy values [] assignments diagnostics owner child sourceCells (some definitions))
      fuel source scope statements result reasonAt fellThrough escaped

private def lower (values : SourceCoreCompatibleValues.Context) (plan : SourceSpecializationWorklist.Plan)
    (arguments : List Value) (sourceCells : Option SourceCoreSourceCells.Allocator := none)
    (ambient : Option DataEnvironment := none) : IO (Core.Program × SourceCoreCompatibleDataPlaceFaultSites.Program values) := do
  let specialized ← single plan
  let source := specialized.function.typedBody
  let diagnostics ← match SourceCoreCompatibleDataPlaceFaultSites.prepare values plan specialized.key with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"compatible control diagnostics failed: {reprStr error}")
  let definitions := ambient.getD values.checked.catalog.definitions
  let context : SourceCoreFunctions.Context := {
    plan, owner := specialized.key, globals := [], administrativePrefix := 0,
    solvedRequirements := specialized.function.solvedRequirements, internalReason := w 250 }
  let lowerBody := bodyLowerer values diagnostics.program specialized.key sourceCells definitions
  let functions := {SourceCoreCompatibleDataExpressions.functionPolicy 200 values with sourceCells}
  let child : SourceCoreFunctions.ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy functions lowerBody fuel context source scope id reasonAt
  let types ← source.inputs.mapM fun binder => match values.checked.catalog.project binder.scheme.body with
    | .ok type => pure type | .error error => throw (IO.userError s!"compatible input projection failed: {reprStr error}")
  let scope := (source.inputs.map (·.id) |>.zip types).reverse
  let roots := source.roots.filterMap fun | .statement id => some id | _ => none
  let result ← match values.checked.catalog.project specialized.function.inferredBodyType with
    | .ok type => pure type | .error error => throw (IO.userError s!"compatible result projection failed: {reprStr error}")
  let flow := SourceCoreCompatibleDataMatches.loopPolicy values specialized.function.solvedRequirements
    ((diagnostics.program.base.find? specialized.key).map (·.assignments) |>.getD ⟨[]⟩)
    diagnostics.program specialized.key child sourceCells (some definitions)
  let code ← match SourceCoreLoops.lowerStatementsWithPolicy flow 200 source scope roots result
      (diagnostics.program.reasonAt specialized.key) Word.zero (w 251) with
    | .ok code => pure code | .error error => throw (IO.userError s!"compatible control lowering failed: {reprStr error}")
  let code ← bindInputs (types.zip arguments) code
  pure (⟨LanguageResult.resultType result, code, definitions⟩, diagnostics)

private def done (program : Core.Program) (expected : Value) : IO Store := do
  assertTrue program.check "compatible control generated program failed native checking"
  match program.runStateful 150000 with
  | .done actual store => assertTrue (actual == expected) s!"compatible control result changed: {reprStr actual}"; pure store
  | result => throw (IO.userError s!"compatible control execution failed: {reprStr result}")

example {context : SourceCoreCompatibleDataMatches.Context} {environment : Core.Context} {result : Ty}
    (certified : SourceCoreCompatibleDataMatches.Certified context environment result) :
    HasType environment certified.expression (LocalLoop.resultType result) context.definitions := certified.typed

private def firstAssignment (source : TypedSource) : IO (StatementNode × AssignmentResolution) :=
  match source.nodes.filterMap (fun
    | .statement node => match node.form with
      | .assignValue assignment _ _ => some (node, assignment) | _ => none
    | _ => none) with
  | [found] => pure found | _ => throw (IO.userError "compatible assignment fixture count changed")

private def firstMatch (source : TypedSource) : IO (StatementNode × MatchResolution) :=
  match source.nodes.filterMap (fun
    | .statement node => match node.form with
      | .matchWith resolution => some (node, resolution) | _ => none
    | _ => none) with
  | [found] => pure found | _ => throw (IO.userError "compatible match fixture count changed")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"compatible control source rejected: {reprStr error}")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some signature => pure signature | none => throw (IO.userError "compatible Box missing")
  let ctor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "compatible Box constructor missing")
  let boxType := TypeSystem.Ty.nominal box.id [.word]
  let proxyType := TypeSystem.Ty.proxy .word
  let mapType := TypeSystem.Ty.mapping proxyType .word
  let nestedType := TypeSystem.Ty.mapping .word mapType
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 200
      [boxType, .nominal box.id [.comptime .word], mapType, nestedType, .mapping .word .word,
       .mapping .word boxType, .proxy (.comptime .word)] with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"compatible control catalog failed: {reprStr error}")
  let initial := SourceCoreCompatibleValues.Context.initial checked
  let canonical : DataConstructorInstantiation := ⟨ctor.id, box.parameters.zip [.word], [.word], boxType⟩
  let staged : DataConstructorInstantiation := ⟨ctor.id, box.parameters.zip [.comptime .word], [.comptime .word], .nominal box.id [.comptime .word]⟩
  let boxValue ← encode initial boxType (.constructed canonical [.word (w 7)])
  let stagedBox ← encode boxValue.context boxType (.constructed staged [.word (w 7)])
  let key ← encode stagedBox.context proxyType (.proxy (.comptime .word))
  let rawMap ← encode key.context mapType (.mapping (.proxy (.comptime .word)) (.comptime .word)
    [(.proxy (.comptime .word), .word (w 1)), (.proxy (.comptime .word), .word (w 2)), (.proxy .word, .word (w 4))])
  let updatedMap ← encode rawMap.context mapType (.mapping (.proxy (.comptime .word)) (.comptime .word)
    [(.proxy (.comptime .word), .word (w 4)), (.proxy (.comptime .word), .word (w 2)), (.proxy .word, .word (w 4))])
  let nestedValue ← encode updatedMap.context nestedType (.mapping .word mapType
    [(.word (w 1), .mapping (.proxy (.comptime .word)) (.comptime .word) [(.proxy (.comptime .word), .word (w 10))])])
  let nestedUpdated ← encode nestedValue.context nestedType (.mapping .word mapType
    [(.word (w 1), .mapping (.proxy (.comptime .word)) (.comptime .word) [(.proxy (.comptime .word), .word (w 15))])])
  let values := nestedUpdated.context
  let (ordered, _) ← lower values (← planFor program "ordered") [rawMap.value, key.value]
  discard <| done ordered (.inRight .word updatedMap.value)
  let (nested, _) ← lower values (← planFor program "nested") [nestedValue.value, key.value]
  discard <| done nested (.inRight .word nestedUpdated.value)

  -- A real retained path supplies the authenticated route. Injected RHS
  -- effects replace the root header and an unrelated key after the snapshot.
  let orderedPlan ← planFor program "ordered"
  let orderedSource := (← single orderedPlan).function.typedBody
  let (assignmentNode, assignment) ← firstAssignment orderedSource
  let route ← match SourceCoreCompatibleDataPlaces.describe values checked.signatures orderedSource
      (.occurrence assignmentNode.id.occurrence) assignment with
    | .ok route => pure route | .error error => throw (IO.userError s!"snapshot route failed: {reprStr error}")
  let prepared ← match SourceCoreCompatibleDataPlaces.prepare values 200 route (w 201) (fun _ => w 5000) with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"snapshot path preparation failed: {reprStr error}")
  let changedRoot ← encode values mapType (.mapping proxyType .word
    [(.proxy (.comptime .word), .word (w 10)), (.proxy .word, .word (w 100))])
  let expectedRoot ← encode changedRoot.context mapType (.mapping proxyType .word
    [(.proxy (.comptime .word), .word (w 4)), (.proxy .word, .word (w 100))])
  let rhs : Expr := .letE (.storeCell (.var 0) (.inRight .unit (← quote changedRoot.value)))
    (.letE (.storeCell (.var 2) (.inRight .unit (.word (w 9)))) (LanguageResult.success (.word (w 3))))
  let snapshotCode := SourceCoreCompatibleDataPlaces.execute prepared (.var 0)
    ⟨key.type, LanguageResult.success (← quote key.value)⟩ rhs
    (LanguageResult.success (.loadCell (.var 0))) (OptionalCell.cellType rawMap.type) (some .wordAdd) false (w 202)
  let snapshot : Core.Program := ⟨LanguageResult.resultType (OptionalCell.cellType rawMap.type),
    ← bindInputs [(.word, .word Word.zero), (rawMap.type, rawMap.value)] snapshotCode, checked.catalog.definitions⟩
  let snapshotStore ← done snapshot (.inRight .word (.inRight .unit expectedRoot.value))
  assertTrue (snapshotStore[0]? == some (.inRight .unit (.word (w 9))))
    "snapshot update lost the RHS side effect"

  -- Structural member updates retain the actual raw instantiation, even when
  -- its runtime type equals the canonical source declaration. This retained
  -- IR projection test does not extend the source checker's accepted spelling.
  let memberSource := (← single (← planFor program "member")).function.typedBody
  let (memberNode, memberAssignment) ← firstAssignment memberSource
  let memberAssignment := {memberAssignment with target := {memberAssignment.target with
    projections := [.member "field" 0], type := .word}}
  let memberRoute ← match SourceCoreCompatibleDataPlaces.describe values checked.signatures memberSource
      (.occurrence memberNode.id.occurrence) memberAssignment with
    | .ok route => pure route | .error error => throw (IO.userError s!"member route failed: {reprStr error}")
  let memberPrepared ← match SourceCoreCompatibleDataPlaces.prepare values 200 memberRoute (w 201) (fun _ => w 5000) with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"member path preparation failed: {reprStr error}")
  let modifiedBox ← encode expectedRoot.context boxType (.constructed staged [.word (w 3)])
  let memberCode := SourceCoreCompatibleDataPlaces.execute memberPrepared (.var 0)
    ⟨.unit, LanguageResult.success .unit⟩ (LanguageResult.success (.word (w 3)))
    (LanguageResult.success (.loadCell (.var 0))) (OptionalCell.cellType stagedBox.type) none false (w 202)
  discard <| done ⟨LanguageResult.resultType (OptionalCell.cellType stagedBox.type),
    ← bindInputs [(stagedBox.type, stagedBox.value)] memberCode, checked.catalog.definitions⟩
    (.inRight .word (.inRight .unit modifiedBox.value))
  let empty ← encode values (.mapping .word .word) (.mapping .word .word [(.word (w 1), .word (w 7))])
  let values := empty.context
  let (lazy, _) ← lower values (← planFor program "lazy") []
  let lazyStore ← done lazy (.inRight .word empty.value)
  assertTrue (lazyStore[0]? == some (.inRight .unit empty.value)) "lazy place did not commit the declared empty mapping after success"

  let (rhsFailure, _) ← lower values (← planFor program "rhsFailure") []
  assertTrue rhsFailure.check "compatible RHS failure failed native checking"
  match rhsFailure.runStateful 150000 with
  | .done (.inLeft .word (.word _)) store =>
      let mapTy ← match checked.catalog.project (.mapping .word .word) with
        | .ok type => pure type | _ => throw (IO.userError "mapping projection lost")
      assertTrue (store[0]? == some (.inLeft mapTy .unit)) "RHS failure prematurely materialized root mapping"
  | result => throw (IO.userError s!"compatible RHS failure result changed: {reprStr result}")

  -- The static code reserves the whole raw-header range before any input
  -- extends the registry. Both expression and place ranges remain disjoint.
  let missingPlan ← planFor program "missing"
  let missingSpecialized ← single missingPlan
  let diagnostics ← match SourceCoreCompatibleDataPlaceFaultSites.prepare values missingPlan missingSpecialized.key with
    | .ok receipt => pure receipt | .error error => throw (IO.userError s!"missing ranges failed: {reprStr error}")
  let rawValueType := TypeSystem.Ty.comptime boxType
  let dynamic ← encode values (.mapping .word boxType) (.mapping (.comptime .word) rawValueType [])
  let header ← match dynamic.context.registry.id? (.mapping (.comptime .word) rawValueType) with
    | some header => pure header | none => throw (IO.userError "dynamic mapping header disappeared")
  let (missingNode, missingAssignment) ← firstAssignment missingSpecialized.function.typedBody
  let base := diagnostics.program.placeReason missingSpecialized.key (.occurrence missingNode.id.occurrence)
    missingAssignment.target.root (some boxType)
  let token := base.add header
  let (missingProgram, _) ← lower values missingPlan [dynamic.value, .word (w 1)]
  discard <| done missingProgram (.inLeft .word (.word token))
  assertTrue ((diagnostics.program.rootTable.diagnostic? token).isNone)
    "static table invented a diagnostic for an undiscovered header"
  let diagnostic ← match diagnostics.diagnostic? dynamic.context.registry dynamic.preserves token with
    | .ok (some diagnostic) => pure diagnostic | result => throw (IO.userError s!"dynamic raw header diagnostic missing: {reprStr result}")
  assertTrue (decide (diagnostic.error = .typeMismatch rawValueType none) && diagnostic.span == some missingNode.span)
    "dynamic missing default lost its raw value type or assignment span"
  let tokens := (← match diagnostics.tableForRegistry dynamic.context.registry dynamic.preserves with
    | .ok table => pure table | .error error => throw (IO.userError s!"extended diagnostic table failed: {reprStr error}"))
    |>.additional.map (·.1)
  assertTrue (decide tokens.Nodup) "compatible program diagnostic ranges collided"
  assertTrue (tokens.all (fun token => token.val < diagnostics.nextReason))
    "compatible diagnostics exceeded the advertised high-water mark"
  assertTrue ((← match diagnostics.diagnostic? dynamic.context.registry dynamic.preserves (w diagnostics.nextReason) with
    | .ok diagnostic => pure diagnostic | .error error => throw (IO.userError s!"unknown diagnostic check failed: {reprStr error}")).isNone)
    "unknown compatible diagnostic token accepted"

  let duplicateInventory ← match SourceCoreCompatibleDataPlaceFaultSites.prepare values missingPlan missingSpecialized.key
      [(missingSpecialized.key, missingSpecialized.function.typedBody)] with
    | .ok receipt => pure receipt | .error error => throw (IO.userError s!"repeated contextual inventory failed: {reprStr error}")
  assertTrue (duplicateInventory.nextReason == diagnostics.nextReason &&
      duplicateInventory.program.places.length == diagnostics.program.places.length)
    "same contextual occurrence reserved a second diagnostic range"
  assertTrue (decide (duplicateInventory.program.rootTable.additional.map Prod.fst).Nodup)
    "repeated contextual inventory duplicated fault tokens"
  let principalType := TypeSystem.Ty.mapping proxyType (.variable ⟨0⟩)
  let principalSource := {orderedSource with
    inputs := orderedSource.inputs.map fun binder =>
      if binder.scheme.body = mapType then {binder with scheme := .mono principalType} else binder
    nodes := orderedSource.nodes.map fun
      | .expression node => .expression {node with type :=
          if node.type = mapType then principalType else if node.type = .word then .variable ⟨0⟩ else node.type}
      | .statement node => .statement (match node.form with
          | .assignValue target operator rhs => {node with
              form := .assignValue {target with target := {target.target with type := .variable ⟨0⟩}} operator rhs}
          | _ => node)}
  let original := (← single orderedPlan)
  let principal := {original with function := {original.function with typedBody := principalSource}}
  let principalPlan := {orderedPlan with specializations := [principal]}
  let contextualInventory ← match SourceCoreCompatibleDataPlaceFaultSites.prepare values principalPlan original.key
      [(original.key, orderedSource)] with
    | .ok receipt => pure receipt | .error error => throw (IO.userError s!"ground contextual route inventory failed: {reprStr error}")
  assertTrue ((contextualInventory.program.placeReason original.key (.occurrence assignmentNode.id.occurrence)
    assignment.target.root (some .word)) != Word.zero)
    "ground contextual source did not supply a principal body's missing route"
  let foreignKey := (← single (← planFor program "nested")).key
  match SourceCoreCompatibleDataPlaceFaultSites.prepare values missingPlan missingSpecialized.key
      [(foreignKey, missingSpecialized.function.typedBody)] with
  | .error (.sourceOwnerMismatch _ _) => pure ()
  | _ => throw (IO.userError "foreign contextual source owner accepted")
  let hugeChecked ← match SourceCoreCompatibleCatalog.prepare program.signatures 200
      [boxType, .mapping .word boxType] [] {maxEntries := Core.wordModulus} with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"large-budget catalog failed: {reprStr error}")
  match SourceCoreCompatibleDataPlaceFaultSites.prepare (SourceCoreCompatibleValues.Context.initial hugeChecked)
      missingPlan missingSpecialized.key with
  | .error .reasonSpaceExhausted => pure ()
  | _ => throw (IO.userError "diagnostic endpoint wrapped with an oversized registry budget")

  let reference := OptionalCell.referenceType (stagedBox.type)
  let markerBase := checked.catalog.definitions.length
  let hiddenLayout : SourceCoreHeapMarkers.Layout := ⟨⟨markerBase⟩, reference⟩
  let boundLayout : SourceCoreHeapMarkers.Layout := ⟨⟨markerBase + 1⟩, .product reference reference⟩
  let ambient := checked.catalog.definitions ++ [hiddenLayout.definition, boundLayout.definition]
  let allocation := SourceCoreSourceCells.marked fun request =>
    if request.scope.length = 1 then pure hiddenLayout
    else if request.scope.length = 2 then pure boundLayout
    else throw (.missingBinding request.binder.id)
  let choosePlan ← planFor program "choose"
  let chooseSpecialized ← single choosePlan
  let chooseSource := chooseSpecialized.function.typedBody
  let (matchNode, matchResolution) ← firstMatch chooseSource
  let arm ← match matchResolution.cases[0]? with
    | some arm => pure arm | none => throw (IO.userError "compatible constructor arm missing")
  let patternContext : SourceCoreCompatibleDataMatches.Context :=
    ⟨values, chooseSpecialized.function.solvedRequirements, none, some ambient⟩
  let hiddenScope := [(matchResolution.hiddenScrutinee, boxValue.type)] ++
    chooseSource.inputs.map (fun binder => (binder.id, boxValue.type))
  let compilePattern := fun pattern => SourceCoreCompatibleDataMatches.compilePattern patternContext 100 chooseSource
    hiddenScope matchNode.id arm.span boxType pattern
  match compilePattern {arm.pattern with type := .bool} with
  | .error _ => pure () | .ok _ => throw (IO.userError "forged compatible pattern type accepted")
  let .constructor expected instructions := arm.pattern.resolution
    | throw (IO.userError "compatible Box pattern form changed")
  match compilePattern {arm.pattern with resolution := .constructor {expected with parameterSubstitution := []} instructions} with
  | .error _ => pure () | .ok _ => throw (IO.userError "forged raw constructor metadata accepted by matcher")
  let (choose, _) ← lower values choosePlan [boxValue.value] (some allocation) (some ambient)
  let matchedStore ← done choose (.inRight .word (.word (w 7)))
  assertTrue (matchedStore.length == 5) "matched arm allocated wrong source cell count"
  assertTrue (SourceCoreHeapMarkers.completedPair hiddenLayout matchedStore 1 ==
    some (.cellRef (OptionalCell.cellType boxValue.type) 0, .inRight .unit boxValue.value))
    "hidden matcher source cell did not capture the lexical root"
  assertTrue (SourceCoreHeapMarkers.completedPair boundLayout matchedStore 3 ==
    some (.pair (.cellRef (OptionalCell.cellType boxValue.type) 2) (.cellRef (OptionalCell.cellType boxValue.type) 0),
      .inRight .unit (.word (w 7)))) "arm binder captured a temporary matcher bundle instead of lexical source refs"
  let (miss, _) ← lower values choosePlan [stagedBox.value] (some allocation) (some ambient)
  let missStore ← done miss (.inRight .word (.word (w 99)))
  assertTrue (missStore.length == 3) "raw metadata mismatch allocated the failed arm's binder"
  let (tuple, _) ← lower values (← planFor program "tuple")
    [.pair boxValue.value (.pair (.bool true) (.word (w 5)))]
  discard <| done tuple (.inRight .word (.word (w 12)))
  let (tupleMiss, _) ← lower values (← planFor program "tuple")
    [.pair stagedBox.value (.pair (.bool true) (.word (w 5)))]
  discard <| done tupleMiss (.inRight .word (.word (w 99)))

  let (scrutineeFailure, _) ← lower values (← planFor program "scrutineeFailure") [boxValue.value]
  assertTrue scrutineeFailure.check "compatible scrutinee failure failed native checking"
  match scrutineeFailure.runStateful 150000 with
  | .done (.inLeft .word (.word _)) store =>
      assertTrue (store.length == 2) "failed scrutinee allocated a hidden or arm source cell"
  | result => throw (IO.userError s!"compatible scrutinee failure result changed: {reprStr result}")

  for fuel in List.range 90 do
    match nested.runStateful fuel with
    | .outOfFuel state => match Core.runStateful 150000 state with
        | .done result _ => assertTrue (result == .inRight .word nestedUpdated.value) "compatible path checkpoint lost captured keys or metadata"
        | result => throw (IO.userError s!"compatible path resume failed: {reprStr result}")
    | .done result _ => assertTrue (result == .inRight .word nestedUpdated.value) "compatible completed path changed"
    | result => throw (IO.userError s!"typed compatible path faulted: {reprStr result}")
  IO.println "compatible structural places, raw patterns, marked captures and resume GREEN"

end Tests.SourceCoreCompatibleDataControl
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleDataExpressions
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMatchArmAllocations
/-! Consumers of the actual compatible marked arm allocator. Both evaluation
directions reach the same independent source allocations even when the
continuation returns a closure capturing the real inserted environment. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMatchArmAllocations
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof DataPatternValues
open CallableIndexedHistory CallableIndexedParameterMeaning

/-- Successful actual lowering is sufficient to derive the prefix. The body
execution and any exact closure equality under weakening are absent as premises. -/
theorem accepted_closure_body {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {compilation : SourceCoreCompatibleDataMatches.Context}
    {scope : SourceCoreSourceCells.Scope} {bindings : List (TypedBinder × Ty)} {code : Expr}
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator compilation source scope bindings
      (.function .unit .unit)
      ((LanguageResult.success (.lambda .unit .unit (.var 0))).weakenAt bindings.length) = .ok code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (sameDefinitions : layouts.definitions = definitions) (registered : layout.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {scrutinee : Value}
    {contextLocation : Location} {native : NativeFrame}
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual) :
    ∃ finalEnvironment finalHeap finalActual finalStore finalMap finalWorld,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      Evaluates actual store (code.rename ξ)
        (.inRight .word (.closure .unit .unit (.var 0) finalActual)) finalStore ∧
      (∀ result finished, Evaluates actual store (code.rename ξ) result finished →
        result = .inRight .word (.closure .unit .unit (.var 0) finalActual) ∧ finished = finalStore) := by
  obtain ⟨finalEnvironment, finalHeap, _, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, _, finalHeaps, _, _, frame, _, agreement⟩ :=
    CompatibleMatchArmPrefix.bindArm_prefix represented sameDefinitions registered allocator accepted
      (named := false) kinds reference read unmapped environments heaps actualLayout
  have child : Evaluates finalActual finalStore
      ((LanguageResult.success (.lambda .unit .unit (.var 0))).rename finalEmbedding)
      (.inRight .word (.closure .unit .unit (.var 0) finalActual)) finalStore := .inRight .lambda
  refine ⟨finalEnvironment, finalHeap, finalActual, finalStore, finalMap, finalWorld, allocated,
    finalHeaps, frame, agreement.wrap child, ?_⟩
  intro result finished completed
  exact evaluation_deterministic (agreement.unwrap completed) child

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function selected(flag: Word, a: Word, b: Word) returns (Word) { match ((flag, (a, b))) { case (0, (x, y)) { return x + y; } default { return 99; } } }",
    "function ordered(p: Word) returns (Word) { match ((p, (11, 13))) { case (0, (x, y)) { return x + y; } case (v, (_, y)) { return v + y; } } }",
    "function captured(marker: Word) returns (Word) { match ((lam(x: Word) -> Word { marker = marker + x; return marker; }, 2)) { case (f, x) { let ignored: Word = f(x); return marker; } } }"]}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "compatible marked arm program" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  let tupleType : TypeSystem.Ty := .product .word (.product .word .word)
  let selected ← SourceCompilerFeatureSupport.compileNamed program "selected"
  for (flag, expected) in [(0, 18), (1, 99)] do
    let inputs := [w flag, w 7, w 11]
    SourceCompilerFeatureSupport.require ((← selected.run inputs) == w expected) "selected arm changed source binding order"
    let cells := [(TypeSystem.Ty.word, some (w flag)), (.word, some (w 7)), (.word, some (w 11)),
      (tupleType, some (.product (w flag) (.product (w 7) (w 11))))]
    selected.checkCells inputs (cells ++ if flag == 0 then [(.word, some (w 7)), (.word, some (w 11))] else [])
    for budget in [0, 7, 43] do selected.checkResume inputs (w expected) budget
  let ordered ← SourceCompilerFeatureSupport.compileNamed program "ordered"
  for (value, expected, first) in [(0, 24, 11), (7, 20, 7)] do
    let inputs := [w value]
    SourceCompilerFeatureSupport.require ((← ordered.run inputs) == w expected) "failed arm allocated or changed later arm bindings"
    ordered.checkCells inputs [(.word, some (w value)),
      (tupleType, some (.product (w value) (.product (w 11) (w 13)))),
      (.word, some (w first)), (.word, some (w 13))]
    for budget in [0, 7, 43] do ordered.checkResume inputs (w expected) budget
  -- The lambda copies `marker = 10` when the scrutinee creates it, and `f(x)`
  -- assigns 12 only to its call's copy, so the arm still reads 10 from `marker`.
  let captured ← SourceCompilerFeatureSupport.compileNamed program "captured"
  SourceCompilerFeatureSupport.require ((← captured.run [w 10]) == w 10)
    "closure call reached the enclosing marker or the arm read an administrative temporary"
  for budget in [0, 7, 43] do captured.checkResume [w 10] (w 10) budget
  IO.println "compatible marked match arms: actual allocation receipts, skipped temporary captures, exact source cells and finite continuation agreement GREEN"
end Tests.SourceCoreCompatibleMatchArmAllocations
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMatchArmScopes
/-! Actual accepted arm scopes are paired with their independent source
contexts. Equal body lists do not erase distinct pattern binder identities.
The internal scrutinee does not become a source lexical declaration. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleMatchArmScopes
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchArmScopes
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"match_arm_scopes", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "match_arm_scopes.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 2⟩
private def binder (index : Nat) : TypedBinder :=
  ⟨⟨owner, index⟩, toString index, .mono .unit, [], false, none⟩
private def pattern (index : Nat) : TypedMatchPattern := {
  source := .group span (.binder span (toString index)), type := .unit, resolution := .binder (binder index) }
private def arm (index : Nat) : TypedMatchCase := ⟨span, pattern index, []⟩
private def resolution : MatchResolution := ⟨⟨⟨owner, 1⟩⟩, hidden, [arm 0, arm 1], none, []⟩
private def node : StatementNode := ⟨site, span, .unit, .matchWith resolution⟩
private def source : TypedSource := {owner, inputs := [], roots := [.statement site], nodes := [.statement node]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private theorem admitted : TypeAdmissible context .unit := .unit (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures])
private theorem patternTyped (index : Nat) : TypedMatchPatternHasType context (pattern index) .unit [binder index] 0 := {
  type_eq := rfl, source_represents := .group (.binder rfl)
  resolution_type := .binder {
    scheme_eq := rfl, runtime := rfl
    wellFormed := by intro declaration installed; cases installed }
  binders_distinct := ⟨by simp, by simp⟩ }
private def armContext (index : Nat) : SourceSemantics.Context :=
  context.withLocal (binder index).id (binder index).scheme []
private theorem extended (index : Nat) : BindersExtend source.owner context [binder index] (armContext index) := by
  apply BindersExtend.cons (middle := armContext index)
  · apply BinderExtends.intro
    · exact {
        owned := rfl, scheme := SchemeWellFormed.monoAdmissible admitted
        quantified_fresh := by intro metavariable member; cases member
        monomorphic_requirements_empty := by intro mono; rfl }
    · simp [LocalFresh, context, Context.ofSignatures]
  · exact .nil _
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.get catalogExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some checked.catalog.definitions⟩
private def hiddenScope : Scope := [(hidden, .unit)]
private def fallback : CertifiedPattern compilation.definitions := {
  pattern := ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
  typed := .lambda .unit (.sum .unit .unit) (.inRight .unit .unit) }
private def compiled (index : Nat) : CertifiedPattern compilation.definitions :=
  match compilePattern compilation 20 source hiddenScope site span .unit (pattern index) with
  | .ok result => result | .error _ => fallback
private theorem firstAccepted : compilePattern compilation 20 source hiddenScope site span .unit (pattern 0) = .ok (compiled 0) := by rfl
private theorem secondAccepted : compilePattern compilation 20 source hiddenScope site span .unit (pattern 1) = .ok (compiled 1) := by rfl
private theorem emptyScope : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index type selected authentic
  cases selected
private theorem hiddenAbsent : hidden ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id) := by
  simp [SourceCoreDataPlaces.declaredBinders, SourceCoreDataPlaces.patternBinders,
    source, node, resolution, arm, pattern, binder, hidden]

theorem first_arm_scope : CompatibleExpressionReads.ScopeDeclarations source
    (armScope hiddenScope (compiled 0).pattern) (armContext 0) :=
  Certificate.hidden_arm_scope (site := site) (node := node) (resolution := resolution) (arm := arm 0)
    (scope := []) (payload := .unit) (compiled := (compiled 0).pattern) (by rfl) rfl (List.mem_cons_self)
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 0) (compiled 0) firstAccepted) rfl (patternTyped 0) (extended 0) hiddenAbsent emptyScope

theorem second_arm_scope : CompatibleExpressionReads.ScopeDeclarations source
    (armScope hiddenScope (compiled 1).pattern) (armContext 1) :=
  Certificate.hidden_arm_scope (site := site) (node := node) (resolution := resolution) (arm := arm 1)
    (scope := []) (payload := .unit) (compiled := (compiled 1).pattern) (by rfl) rfl
    (List.mem_cons_of_mem _ (List.mem_cons_self))
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 1) (compiled 1) secondAccepted) rfl (patternTyped 1) (extended 1) hiddenAbsent emptyScope

theorem actual_binder_identity : (compiled 0).pattern.bindings.map Prod.fst = [binder 0] ∧
    (compiled 1).pattern.bindings.map Prod.fst = [binder 1] :=
  ⟨CompatiblePatternSourceBinders.Certificate.source_binders
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 0) (compiled 0) firstAccepted) rfl (patternTyped 0),
    CompatiblePatternSourceBinders.Certificate.source_binders
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 1) (compiled 1) secondAccepted) rfl (patternTyped 1)⟩

example : (arm 0).body = (arm 1).body := rfl
example : (armContext 0).locals ≠ (armContext 1).locals := by cbv; decide
theorem other_arm_context_is_invalid : ¬ CompatibleExpressionReads.ScopeDeclarations source
    (armScope hiddenScope (compiled 0).pattern) (armContext 1) := by
  intro declarations
  have selected := declarations (binder 0).id (binder 0) 0 .unit (by rfl) (by rfl)
  have selected := Resolved.LocalScope.lookup?_iff.mpr selected
  simp [armContext, context, Context.ofSignatures, Context.withLocal,
    Resolved.LocalScope.lookup?, binder] at selected
example : CompatibleExpressionReads.ScopeDeclarations source
    [((binder 0).id, .word), (hidden, .bool)] (armContext 0) :=
  scope_ids (by rfl) first_arm_scope
example : (armScope hiddenScope (compiled 0).pattern).map Prod.fst = [(binder 0).id, hidden] := by rfl
example : SourceCoreDataPlaces.rootBinder source hidden = .error (.missingBinding hidden) := by rfl
end Tests.SourceCoreCompatibleMatchArmScopes
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMatchPrefixes
/-! Whole actual compatible match receipt extraction and ordered source
selection, plus runtime regressions for hidden/arm allocations, no-branch
fallthrough, scrutinee fault and loop control through the common Core entry. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace Tests.SourceCoreCompatibleMatchPrefixes
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_match_prefixes", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "compatible_match_prefixes.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def scrutineeId : ExpressionId := ⟨⟨owner, 1⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 0⟩
private def bound : TypedBinder := ⟨⟨owner, 1⟩, "value", .mono .unit, [], false, none⟩
private def pattern : TypedMatchPattern := {source := .binder span "value", type := .unit, resolution := .binder bound}
private def resolution : MatchResolution := ⟨scrutineeId, hidden, [⟨span, pattern, []⟩], some [], []⟩
private def source : TypedSource := {owner, inputs := [], roots := [.statement site], nodes := [
  .statement ⟨site, span, .unit, .matchWith resolution⟩,
  .expression {id := scrutineeId, span, type := .unit, form := .tuple []}]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem checkedExists : (SourceCoreCompatibleCatalog.prepare signatures 50 [.unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 50 [.unit]).toOption.get checkedExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [⟨[.unit]⟩]
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some ambient.definitions⟩
private def expression : SourceCoreCompatibleDataMatches.ExpressionLowerer := fun _ _ _ _ _ =>
  .ok ⟨.unit, .inRight .word .unit⟩
private def body : SourceCoreCompatibleDataMatches.BodyLowerer := fun _ _ _ _ _ _ _ => .ok (LocalLoop.fallthrough .unit)
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def compiled : Expr := match SourceCoreCompatibleDataMatches.lowerWithReasons compilation expression body
    10 source [] site resolution .unit reasonAt Word.zero with | .ok code => code | .error _ => .unit
private theorem accepted : SourceCoreCompatibleDataMatches.lowerWithReasons compilation expression body
    10 source [] site resolution .unit reasonAt Word.zero = .ok compiled := by rfl
private theorem matchCertificate : CompatibleMatchCertificates.Certificate compilation source [] site resolution .unit Word.zero
    (fun _ _ value => value = ⟨.unit, .inRight .word .unit⟩)
    (fun _ _ code => code = LocalLoop.fallthrough .unit) compiled := by
  apply CompatibleMatchCertificates.certificate_of_lowerWithReasons (accepted := accepted)
  · intro _ _ _ _ accepted; exact Except.ok.inj accepted.symm
  · intro _ _ _ _ accepted; exact Except.ok.inj accepted.symm
private def context : SourceSemantics.Context := .ofSignatures signatures
private theorem contextValid : CompatiblePatternLeaves.ContextValid compilation context := {
  signatures := rfl, ledger := rfl, valid := ⟨by simp [RequirementIdsUnique, context, Context.ofSignatures],
    by intro requirement member; cases member⟩}
private theorem signatureValid : SignatureCatalogWellFormed signatures := by
  constructor <;> simp [signatures, signatureDeclarationIds]

/-- Actual compatible lowering records the complete fold, including the real
ambient checker and source binder identity; no child runtime premise is used. -/
example : CompatibleMatchSelectionPrefix.Ordinary matchCertificate :=
  CompatibleMatchSelectionPrefix.ordinary_of_source_ids matchCertificate rfl (by intro arm member binder found; rfl)

example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} (extended : SourceCoreRawMetadata.Extends values.registry registry) :
    ∃ selection, Dynamic.MatchCasesSelect context .unit resolution.cases resolution.defaultBody selection :=
  CompatibleMatchDecision.Certificate.source_selects matchCertificate contextValid signatureValid extended
    (show source.lookupExpression? resolution.scrutinee = some {id := scrutineeId, span, type := .unit, form := .tuple []} from rfl)
    (CompatiblePayload.ValueRep.unit (functions := functions) (mapping := mapping) (world := world))

example : SourceCoreCompatibleDataMatches.lowerWithReasons compilation expression body 10 source [(hidden, .unit)]
    site resolution .unit reasonAt Word.zero = .error (.duplicateBinding hidden) := by cbv

private def noBranchResolution : MatchResolution := ⟨scrutineeId, hidden, [], none, []⟩
private def noBranchSource : TypedSource := {source with nodes := [
  .statement ⟨site, span, .unit, .matchWith noBranchResolution⟩,
  .expression {id := scrutineeId, span, type := .unit, form := .tuple []}]}
private def noBranchCode : Expr := match SourceCoreCompatibleDataMatches.lowerWithReasons compilation expression body
    10 noBranchSource [] site noBranchResolution .unit reasonAt Word.zero with | .ok code => code | .error _ => .unit
private theorem noBranchCertificate : CompatibleMatchCertificates.Certificate compilation noBranchSource [] site noBranchResolution .unit Word.zero
    (fun _ _ value => value = ⟨.unit, .inRight .word .unit⟩)
    (fun _ _ code => code = LocalLoop.fallthrough .unit) noBranchCode := by
  apply CompatibleMatchCertificates.certificate_of_lowerWithReasons (accepted := show
    SourceCoreCompatibleDataMatches.lowerWithReasons compilation expression body
      10 noBranchSource [] site noBranchResolution .unit reasonAt Word.zero = .ok noBranchCode from rfl)
  · intro _ _ _ _ accepted; exact Except.ok.inj accepted.symm
  · intro _ _ _ _ accepted; exact Except.ok.inj accepted.symm

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function fallthrough(p: Word) returns (Word) { match (p) { case 0 { return 11; } default {} } return 17; }",
    "function fault(p: Word) returns (Word) { let hole: Word; match (hole) { case v { return v; } default { return 99; } } return p; }",
    "function nested(p: Word) returns (Word) { match ((p, (7, 11))) { case (0, (x, y)) { match ((x, y)) { case (a, b) { return a + b; } } } default { return 99; } } }",
    "function flow(stop: Word) returns (Word) { let tally: Word = 0; for (let i: Word = 0; i < stop; i = i + 1) { match (i) { case 0 { continue; } case 2 { break; } default { tally = tally + i; } } } return tally; }"]}] }

def run : IO Unit := do
  -- The checker requires exhaustive matches. Exercise the compiler's retained
  -- no-branch case using its actual accepted typed IR, then checked roots below.
  match Core.runStateful 1000 (.initial noBranchCode [] []) with
  | .done result store =>
    SourceCompilerFeatureSupport.require (result == .inRight .word (.inLeft LocalLoop.transferType (.inLeft .unit .unit)))
      "empty match changed the no-branch control value"
    SourceCompilerFeatureSupport.require (store == [.inRight .unit .unit]) "empty match changed the actual hidden allocation"
  | _ => throw (IO.userError "empty accepted typed match did not complete")
  let program ← SourceCompilerFeatureSupport.get "compatible whole match prefixes" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  let fallthrough ← SourceCompilerFeatureSupport.compileNamed program "fallthrough"
  for (p, result) in [(0, 11), (1, 17)] do
    SourceCompilerFeatureSupport.require ((← fallthrough.run [w p]) == w result) "default match changed fallthrough or first arm"
    fallthrough.checkCells [w p] [(.word, some (w p)), (.word, some (w p))]
    for budget in [0, 7, 43] do fallthrough.checkResume [w p] (w result) budget
  let fault ← SourceCompilerFeatureSupport.compileNamed program "fault"
  let failed ← fault.invoke [w 3]
  match failed.outcome with
  | .failed _ _ => pure ()
  | _ => throw (IO.userError "scrutinee fault reached the match allocation or branch")
  fault.checkCells [w 3] [(.word, some (w 3)), (.word, none)]
  let nested ← SourceCompilerFeatureSupport.compileNamed program "nested"
  SourceCompilerFeatureSupport.require ((← nested.run [w 0]) == w 18) "nested marked matches changed lexical binder order"
  for budget in [0, 7, 43] do nested.checkResume [w 0] (w 18) budget
  let flow ← SourceCompilerFeatureSupport.compileNamed program "flow"
  SourceCompilerFeatureSupport.require ((← flow.run [w 4]) == w 1) "match failed to restore for scope or transfer break/continue"
  flow.checkCells [w 4] [(.word, some (w 4)), (.word, some (w 1)), (.word, some (w 2)),
    (.word, some (w 0)), (.word, some (w 1)), (.word, some (w 2))]
  for budget in [0, 7, 43] do flow.checkResume [w 4] (w 1) budget
  IO.println "compatible whole match prefixes: actual fold receipts, ordered selection, raw hidden heap types, no-branch/fault/control and resume GREEN"
end Tests.SourceCoreCompatibleMatchPrefixes
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMatchRuntimeHead
/-! Concrete literal scrutinees and empty request bodies close the pointwise
interfaces of the runtime match head. The parent typing, actual compiler
certificate, allocation/frame authority and independent source semantics stay
explicit. Public runtime fixtures also exercise nonempty selected bodies. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleMatchRuntimeHead
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates GenericMatchChildren
open TypedLexicalWhile (ValuesContext)
open RecursiveNamedLoopContracts (PreservesAtFor ReflectsAtFor)

section EmptyBody
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} {frame : SourceCoreCallableIndexedFrames.Layout}
  {globals : Nat} {administrative : Core.Context} {scope : Scope} {expected : TypeSystem.Ty} {type : Ty}

/-- The empty body closes at every original source grade and every predicate. -/
theorem empty_preserves_at (validity : SourceSemantics.Context → Prop) (size : Nat) :
    PreservesAtFor functions program evidence validity (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      (administrative := administrative) (scope := scope) size false [] expected type (LocalLoop.fallthrough type) := by
  intro _ mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals _ _ _ _ _ _ trace
  cases trace with
  | control executed =>
    obtain ⟨rfl, rfl, rfl⟩ := ScalarStatementViews.nil_view false executed.sound
    exact ⟨_, store, mapping, world, LocalLoop.fallthrough_evaluates _ _ _, .fallthrough environment,
      heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩
  | fault failed => exact False.elim (ScalarStatementViews.nil_cannot_fault false failed.sound)

/-- Reflection keeps the native grade and constructs a separate source grade. -/
theorem empty_reflects_at (validity : SourceSemantics.Context → Prop) (size : Nat) :
    ReflectsAtFor functions program evidence validity (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      (administrative := administrative) (scope := scope) size false [] expected type (LocalLoop.fallthrough type) := by
  intro _ mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals _ _ _ _ _ _ evaluated
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.fallthrough_evaluates type actual store)
  have original := ProtectedLexicalStatements.nil_executes false program context evidence source environment before
  obtain ⟨sourceSize, trace⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size original
  exact ⟨sourceSize, context, _, before, mapping, world, trace, .fallthrough environment, heaps,
    .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩
end EmptyBody

section Concrete
variable {compilation : SourceCoreCompatibleDataMatches.Context}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends compilation.values.registry registry)
  {source : TypedSource} {context : SourceSemantics.Context} {control : ControlContext}
  {program : SourceSemantics.Program} {evidence : Dynamic.EvidenceEnvironment} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {solved : List SolvedRequirement} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
    (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved source id lowered) (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (signatures : context.signatures = compilation.signatures)
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
  (sameLedger : compilation.solvedRequirements = solved) {administrative : Core.Context} {faults : FunctionCalls.FaultRep}

  (emptyRequests : ∀ request ∈ requests, request.statements = [] ∧ request.code = LocalLoop.fallthrough type)

include allocator definitions registered extension ordinary signatures sameLedger catalogValid found casesTyped defaultTyped emptyRequests in
theorem concrete_preserves_at (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size ≤ budget) {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry) :
    RecursiveNamedMatchSourceBounds.Head.HeadPreservesAtFor (entry := entry) functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (values := compilation.values) (source := source)
      (context := context) (registry := registry) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) size (scope := scope) id expected type code := by
  apply CompatibleMatchRuntimeHead.head_preserves_bounded onError allocator functions definitions registered extension
    receipt ordinary signatures catalogValid found casesTyped defaultTyped sameLedger unique budget size bounded transport bindings
  · intro valid child smaller
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (TypedGenericExpressionMeaning.preserves_of_unrestricted
          (CompatibleExpressionLiteralRuntime.preserves functions program context evidence valid.ledger valid.runtime unique faults))) child
  · intro request member childContext related child smaller
    obtain ⟨statements, nativeCode⟩ := emptyRequests request member
    rw [statements, nativeCode]
    exact empty_preserves_at functions program evidence _ child

include allocator definitions registered extension ordinary signatures sameLedger catalogValid found casesTyped defaultTyped emptyRequests in
theorem concrete_reflects_at (budget size : Nat) (bounded : size ≤ budget) {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry) :
    RecursiveNamedMatchSourceBounds.Head.HeadReflectsAtFor (entry := entry) functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (values := compilation.values) (source := source)
      (context := context) (registry := registry) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) size (scope := scope) id expected type code := by
  apply CompatibleMatchRuntimeHead.head_reflects_bounded onError allocator functions definitions registered extension
    receipt ordinary signatures catalogValid found casesTyped defaultTyped sameLedger budget size bounded transport bindings
  · intro valid child smaller
    exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (TypedGenericExpressionMeaning.reflects_of_unrestricted
          (CompatibleExpressionLiteralRuntime.reflects functions program context evidence valid.ledger valid.runtime source faults))) child
  · intro request member childContext related child smaller
    obtain ⟨statements, nativeCode⟩ := emptyRequests request member
    rw [statements, nativeCode]
    exact empty_reflects_at functions program evidence _ child

end Concrete

section Frame
variable {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
  {types : List TypeSystem.Ty} {solved : List SolvedRequirement}

/-- The real frame supplies the same complete dictionary and ledger, with no
empty-template or ordinary-validity condition. -/
theorem frame_runtime_valid
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved) :
    CompatibleRuntimeContextValidity.Valid solved context function.evidence :=
  CompatibleRuntimeContextValidity.of_frame frame extended programTyped sameLedger

/-- Every retained row, including an unused template, is kept by the consumer. -/
theorem full_ledger_retained {row : SolvedRequirement}
    (valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence) (member : row ∈ solved) :
    row ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
end Frame

section Boundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def context : SourceSemantics.Context := (Context.ofSignatures signatures).withSolvedRequirements [row]

/-- Runtime validity cannot supply the old ordinary premise for an unused row. -/
theorem runtime_not_ordinary :
    CompatibleRuntimeContextValidity.Valid [row] context [] ∧
      ¬ CompatibleExpressionLiterals.ContextValid [row] context [] := by
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · change ([⟨0⟩] : List RequirementId).Nodup; decide
    · intro item evidence member implementation
      have same : item = row := by simpa [context, Context.withSolvedRequirements] using member
      subst item
      cases implementation
  · constructor
    · intro predicate evidence found; cases found
    · intro predicate member; cases member
  · intro ordinary
    have valid := ordinary.valid.entriesValid row (by simp [context, Context.withSolvedRequirements])
    cases valid with
    | intro retained =>
      cases retained with
      | intro represents valid =>
        cases represents
        cases valid with
        | assumption member => cases member
end Boundary

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)

/-- A real template-bearing source retains every row while the actual literal
scrutinee compiler and empty-body compiler lower this reached Match head.
The enclosing qualified lambda/function compilation is not claimed. -/
private def template_head : IO Unit := do
  let program ← get "runtime head template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " match (61) { case 61 {} default {} }",
      " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "head template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "head template function missing")
  let actual ← get "head template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger.map (·.id) == generic.solvedRequirements.map (·.id))
    "head template IDs or complete ordered ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !actual.assumptions.contains predicate)
          "head template assumption promoted"
      | _ => throw (IO.userError "head template implementation fabricated")
    | _ => throw (IO.userError "head template row missing/duplicated")
  let checked ← get "head template catalog" (SourceCoreCompatibleCatalog.prepare program.signatures 100 [.word, .bool])
  let compilation : SourceCoreCompatibleDataMatches.Context := ⟨.initial checked, ledger, none, none⟩
  let functions : SourceCoreFunctions.Context := {
    plan := ⟨[actual.key], [actual], [], []⟩,
    owner := actual.key, globals := [], administrativePrefix := 1, solvedRequirements := ledger, internalReason := Word.zero}
  let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .error (.traversalExhausted (.declaration actual.function.declaration))
  let expression : ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithReasons noBody fuel functions source scope id reasonAt
  let body : BodyLowerer := fun _ _ _ statements type _ _ =>
    if statements.isEmpty then .ok (LocalLoop.fallthrough type) else .error (.traversalExhausted (.declaration actual.function.declaration))
  let mut count := 0
  for node in source.nodes do
    match node with
    | .statement statement => match statement.form with
      | .matchWith resolution =>
        match accepted : lowerWithReasons compilation expression body 100 source [] statement.id resolution
            .unit (fun _ => Word.zero) Word.zero with
        | .error error => throw (IO.userError s!"head template lowering {reprStr error}")
        | .ok code =>
          have receipt := certificate_of_lowerWithReasons (expressionCertificate := fun _ _ _ => True)
            (bodyCertificate := fun _ _ _ => True) (fun _ _ _ _ _ => True.intro) (fun _ _ _ _ _ => True.intro) accepted
          have sites := CompatibleMatchRuntimeSelection.of_certificate receipt
          let _sites := sites
          require (Core.infer? [] code compilation.definitions == some (LocalLoop.resultType .unit)) "head actual type"
          let before : Core.Store := [.integer 977, .closure .unit .integer (.var 1) [.integer 983], .cellRef .integer 0]
          for fuel in [0, 1, 19, 10000] do
            let done := match Core.runStateful fuel (.initial code [] before) with
              | .outOfFuel state => Core.runStateful 10000 state | other => other
            match done with
            | .done value after =>
              require (value == LocalLoop.fallthroughValue .unit &&
                after == before ++ [.inRight .unit (.word (Word.ofNatModulo 61))]) "head template full native store/result"
            | other => throw (IO.userError s!"head template unfinished {reprStr other}")
          count := count + 1
      | _ => pure ()
    | _ => pure ()
  require (count == 1) "head template occurrence count"

private def content : String := String.intercalate "\n" [
  "function empty() returns (Word) { match (37) { case 37 {} default {} } return 41; }",
  "function bound() returns (Word) { match (9) { case binding {} } return 43; }",
  "function integerHead(value: integer) returns (Word) { match (value) { case 73 {} default {} } return 47; }",
  "function selected(a: Word, b: Word) returns (Word) { match ((a, b)) { case (37, chosen) { return chosen; } case (left, right) { return left + right; } } }",
  "function faultArm() returns (Word) { match (37) { case 37 { let prior: Word = 41; let missing: Word; return missing; } default { return 19; } } }",
  "function faultScrutinee() returns (Word) { let missing: Word; match (missing) { case 0 { return 23; } default { return 29; } } }"
]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "head public resume" (first.resume 300000)).observation

def run : IO Unit := do
  template_head
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "runtime whole match head" content
    ["empty", "bound", "integerHead", "selected", "faultArm", "faultScrutinee"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (word 991)⟩]}
  let cases : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("empty", [], word 41, [(.word, some (word 37))]),
    ("bound", [], word 43, [(.word, some (word 9)), (.word, some (word 9))]),
    ("integerHead", [.integer 73], word 47, [(.integer, some (.integer 73)), (.integer, some (.integer 73))]),
    ("integerHead", [.integer 74], word 47, [(.integer, some (.integer 74)), (.integer, some (.integer 74))]),
    ("selected", [word 37, word 8], word 8, [(.word, some (word 37)), (.word, some (word 8)), (.product .word .word, some (.product (word 37) (word 8))), (.word, some (word 8))]),
    ("selected", [word 38, word 8], word 46, [(.word, some (word 38)), (.word, some (word 8)), (.product .word .word, some (.product (word 38) (word 8))), (.word, some (word 38)), (.word, some (word 8))])]
  for (name, arguments, expected, cells) in cases do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 1, 19, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) "head success resume changed"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected &&
          reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"head public full source cells {name}"
      | other => throw (IO.userError s!"head success expected {reprStr other}")
  let failures : List (String × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("faultArm", [(.word, some (word 37)), (.word, some (word 41)), (.word, none)]),
    ("faultScrutinee", [(.word, none)])]
  for (name, cells) in failures do
    let named ← match compiled.indexed.base.functions.find? (fun named =>
        compiled.sourceProgram.signatures.functions.any (fun signature => signature.id == named.specialized.function.declaration && signature.name == name)) with
      | some named => pure named | none => throw (IO.userError "head source function missing")
    let missing ← match (SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
      | [binder] => pure binder.id | _ => throw (IO.userError "head missing binder identity")
    let baseline ← finish compiled name [] 300000 initial
    for fuel in [0, 1, 19, 300000] do
      let observed ← finish compiled name [] fuel initial
      require (reprStr observed == reprStr baseline) "head fault resume changed"
      match observed with
      | .fault (.uninitializedLocal found) final =>
        require (found == missing &&
          reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          "head first fault/full ordered cells"
      | other => throw (IO.userError s!"head fault expected {reprStr other}")
  IO.println "runtime whole match head: literal/empty concrete meaning / actual template full ledger / first and later arm/default / independent strict sizes / full cells and original fault / resume GREEN"

end Tests.SourceCoreCompatibleMatchRuntimeHead
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMatchRuntimeSelection
/-! Ordered accepted arm receipts supply runtime numeric support without a
whole ordinary ledger. Formal prefixes retain the original strict continuation;
callback-marker runtime tests exercise actual lowering and ordered selection.
They do not claim source meaning for arbitrary callbacks. Public execution tests
separately check full source cells and first-fault/resumption behavior. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleMatchRuntimeSelection
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates DataMatchBranchPrefix
open CallableIndexedHistory CompatibleMatchSelectionPrefix

theorem accepted_sites
    {compilation : SourceCoreCompatibleDataMatches.Context} {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer}
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId}
    {resolution : MatchResolution} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {internalReason : Core.Word} {code : Core.Expr}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate}
    (expressionExtract : ∀ childFuel scope id result,
      lowerExpression childFuel source scope id reasonAt = .ok result → expressionCertificate scope id result)
    (bodyExtract : ∀ childFuel scope statements code,
      lowerBody childFuel source scope statements resultType reasonAt internalReason = .ok code →
      bodyCertificate scope statements code)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      resultType reasonAt internalReason = .ok code) :
    CompatibleMatchDecision.Certificate.LiteralSites (CompatibleMatchRuntimeSelection.LiteralRows compilation)
      (certificate_of_lowerWithReasons expressionExtract bodyExtract accepted) :=
  CompatibleMatchRuntimeSelection.of_certificate _

theorem actual_remaining
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternRuntime.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry)
    (initial : entry scope mapping world heap store canonical)
    {wholeSize : Nat} {result : Value} {endStore : Store}
    (completed : EvaluationSize wholeSize actual before (code.rename ξ) result endStore) :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      entry finalScope finalMap finalWorld finalHeap finalStore finalCanonical ∧
      ∃ remainingSize, remainingSize < wholeSize ∧
        EvaluationSize remainingSize finalActual finalStore (body.rename finalEmbedding) result endStore := by
  obtain ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, spine, installedEntry, agreement⟩ :=
    CompatibleMatchRuntimeSelection.success_prefix certificate ordinary onError allocator valid catalogValid definitions registered extended found uniqueExpression
      represented environments heaps agrees actualTyped reference read unmapped evaluated transport bindings initial
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, spine, installedEntry,
    agreement.remaining completed⟩

section Boundaries

theorem repeated_arms {compilation : SourceCoreCompatibleDataMatches.Context}
    {source site scope expected} {arm : TypedMatchCase} {pattern : Pattern} {body : Core.Expr}
    {bodyCertificate : BodyCertificate}
    (certified : CompatiblePatternCertificates.Certificate compilation source scope site arm.span expected arm.pattern pattern)
    (typed : HasType [] pattern.matcher pattern.functionType compilation.definitions)
    (bodyAccepted : bodyCertificate (armScope scope pattern) arm.body body) :
    CompatibleMatchDecision.Arms.LiteralSites (CompatibleMatchRuntimeSelection.LiteralRows compilation)
      (Arms.cons certified typed bodyAccepted (Arms.cons certified typed bodyAccepted .nil)) :=
  CompatibleMatchRuntimeSelection.of_arms _

theorem empty_arms {compilation : SourceCoreCompatibleDataMatches.Context}
    {source site scope expected bodyCertificate} :
    CompatibleMatchDecision.Arms.LiteralSites (CompatibleMatchRuntimeSelection.LiteralRows compilation)
      (Arms.nil (compilation := compilation) (source := source) (site := site) (scope := scope)
        (expected := expected) (bodyCertificate := bodyCertificate)) :=
  CompatibleMatchRuntimeSelection.of_arms _

theorem actual_frame_runtime {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) {compilation : SourceCoreCompatibleDataMatches.Context}
    (signatures : context.signatures = compilation.signatures)
    (sameLedger : function.context.solvedRequirements = compilation.solvedRequirements) :
    CompatiblePatternRuntime.ContextValid compilation context :=
  ⟨signatures, (RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger,
    RecursiveNamedInitialContextValidity.runtime frame extended programTyped⟩

end Boundaries

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def content : String := String.intercalate "\n" [
  "function ordered(a: Word, b: Word) returns (Word) { match ((a, b)) { case (37, bound) { return bound; } case (37, later) { return later + 1; } case (left, right) { return left + right; } } }",
  "function choose(a: Word) returns (Word) { match (a) { case 0 { return 11; } case 1 { return 13; } default { return 17; } } }",
  "function failed(a: Word) returns (Word) { match (a) { case 0 { let prior: Word = 41; let missing: Word; return missing; } default { return 19; } } }",
  "function scrutineeFault() returns (Word) { let missing: Word; match (missing) { case 0 { return 23; } default { return 29; } } }"
]

/-- The actual whole match lowerer is supplied explicit constant scrutinee and
marker bodies. Full native cells expose exactly which ordered arm was reached. -/
private def auditLower (compilation : SourceCoreCompatibleDataMatches.Context) (source : TypedSource)
    (statement : StatementNode) (resolution : MatchResolution) (payload : Core.Ty)
    (input : Core.Value) (expected : Core.Value) (bindings : List Core.Value)
    (scrutineeFails : Bool := false) : IO Unit := do
  let lowerExpression : ExpressionLowerer := fun _ _ _ _ _ => .ok ⟨payload,
    if scrutineeFails then Core.LanguageResult.failure payload (.word (Word.ofNatModulo 811))
    else Core.LanguageResult.success (.var 0)⟩
  let lowerBody : BodyLowerer := fun _ _ _ statements _ _ _ =>
    let selected := resolution.cases.zipIdx.find? (fun (arm, _) => arm.body == statements)
    let marker := selected.map (fun (_, index) => 100 + index) |>.getD 900
    .ok (Core.LocalLoop.returned (.word (Word.ofNatModulo marker)))
  match accepted : lowerWithReasons compilation lowerExpression lowerBody 100 source [] statement.id resolution
      .word (fun _ => Word.ofNatModulo 813) (Word.ofNatModulo 817) with
  | .error error => throw (IO.userError s!"ordered match lowering rejected {reprStr error}")
  | .ok code =>
    have actual := certificate_of_lowerWithReasons (expressionCertificate := fun _ _ _ => True)
      (bodyCertificate := fun _ _ _ => True) (fun _ _ _ _ _ => True.intro) (fun _ _ _ _ _ => True.intro) accepted
    have support := CompatibleMatchRuntimeSelection.of_certificate actual
    let _support := support
    require (Core.infer? [payload] code compilation.definitions == some (Core.LocalLoop.resultType .word))
      "ordered matcher actual code type changed"
    let sentinel : Core.Store := [.integer 919, .closure .unit .integer (.var 1) [.integer 921], .cellRef .integer 0]
    let appended := if scrutineeFails then [] else (input :: bindings).map (Core.Value.inRight .unit)
    for fuel in [0, 3, 23, 10000] do
      let result := match Core.runStateful fuel (.initial code [input] sentinel) with
        | .outOfFuel pending => Core.runStateful 10000 pending | other => other
      match result with
      | .done value finalStore =>
        require (value == expected && finalStore == sentinel ++ appended)
          s!"ordered selection/full native store mismatch: {reprStr result}"
      | other => throw (IO.userError s!"ordered match prefix unfinished {reprStr other}")

private def replaceMatch (source : TypedSource) (statement : StatementNode) (resolution : MatchResolution) : TypedSource :=
  {source with nodes := source.nodes.map (fun node => match node with
    | .statement found => if found.id == statement.id then .statement {found with form := .matchWith resolution} else node
    | _ => node)}

private def inspect (artifact : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let w := Word.ofNatModulo
  let mut count := 0
  for named in artifact.indexed.base.functions do
    let actual ← get "ordered actual specialization" (SourceCompilationPlan.exactSpecialization artifact.indexed.base.plan named.signature.key)
    require (actual == named.specialized) "ordered full selected record changed"
    let source := actual.function.typedBody
    let signature ← match artifact.sourceProgram.signatures.functions.find? (·.id == actual.function.declaration) with
      | some value => pure value | none => throw (IO.userError "ordered signature missing")
    for node in source.nodes do
      match node with
      | .statement statement => match statement.form with
        | .matchWith resolution =>
          if signature.name == "ordered" || signature.name == "choose" then
            let ledger := actual.function.solvedRequirements
            let compilation : SourceCoreCompatibleDataMatches.Context := ⟨(.initial artifact.compatible.checked), ledger, none, none⟩
            let row ← match ledger.head? with
              | some value => pure value | none => throw (IO.userError "numeric row missing")
            let unused : SolvedRequirement := ⟨⟨(ledger.map (·.id.index)).foldl max 0 + 10000⟩, row.predicate, .assumption row.predicate⟩
            for changed in [compilation, {compilation with solvedRequirements := unused :: ledger},
                {compilation with solvedRequirements := ledger ++ [unused]}] do
              if signature.name == "ordered" then
                auditLower changed source statement resolution (.product .word .word)
                  (.pair (.word (w 37)) (.word (w 8))) (Core.LocalLoop.returnedValue (.word (w 100))) [.word (w 8)]
                auditLower changed source statement resolution (.product .word .word)
                  (.pair (.word (w 38)) (.word (w 8))) (Core.LocalLoop.returnedValue (.word (w 102))) [.word (w 38), .word (w 8)]
              else
                for (input, marker) in [(0, 100), (1, 101), (2, 900)] do
                  auditLower changed source statement resolution .word (.word (w input)) (Core.LocalLoop.returnedValue (.word (w marker))) []
            if signature.name == "ordered" then
              let first ← match resolution.cases.head? with
                | some value => pure value | none => throw (IO.userError "first ordered arm missing")
              let cases := resolution.cases.mapIdx (fun index arm => if index == 1 then {arm with pattern := first.pattern} else arm)
              let repeated := {resolution with cases := cases, requirements := cases.flatMap (·.pattern.requirements)}
              require (repeated.requirements.take 2 == first.pattern.requirements ++ first.pattern.requirements)
                "repeated requirement order lost"
              auditLower compilation (replaceMatch source statement repeated) statement repeated (.product .word .word)
                (.pair (.word (w 37)) (.word (w 8))) (Core.LocalLoop.returnedValue (.word (w 100))) [.word (w 8)]
            else
              let empty := {resolution with cases := [], defaultBody := none, requirements := []}
              auditLower compilation (replaceMatch source statement empty) statement empty .word (.word (w 3))
                (Core.LocalLoop.fallthroughValue .word) []
              let fallbackOnly := {resolution with cases := [], requirements := []}
              auditLower compilation (replaceMatch source statement fallbackOnly) statement fallbackOnly .word (.word (w 3))
                (Core.LocalLoop.returnedValue (.word (w 900))) []
              auditLower compilation source statement resolution .word (.word (w 0))
                (.inLeft (Core.LocalLoop.controlType .word) (.word (w 811))) [] true
            count := count + 1
        | _ => pure ()
      | _ => pure ()
  require (count == 2) "ordered match source count changed"

/-- Only the actual whole match is lowered; template-bearing lambda body
execution and whole callable acceptance are not claimed by this fixture. -/
private def template_root : IO Unit := do
  let program ← get "ordered template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word) {",
      " let f = lam(item) { return keep(item); }; let other: Bool = f(flag); let number: Word = 61;",
      " match ((number, number)) { case (61, 61) { return f(1); } default { return f(2); } } }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "ordered template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "ordered template function missing")
  let actual ← get "ordered actual template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger.map (·.id) == generic.solvedRequirements.map (·.id))
    "ordered template IDs or complete ordered ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !actual.assumptions.contains predicate)
          "ordered template assumption was promoted"
      | _ => throw (IO.userError "ordered template implementation fabricated")
    | _ => throw (IO.userError "ordered template row missing or duplicated")
  let checked ← get "ordered template catalog"
    (SourceCoreCompatibleCatalog.prepare program.signatures 100 [.word, .bool, .product .word .word])
  let compilation : SourceCoreCompatibleDataMatches.Context := ⟨.initial checked, ledger, none, none⟩
  let w := Word.ofNatModulo
  let mut count := 0
  for node in source.nodes do
    match node with
    | .statement statement => match statement.form with
      | .matchWith metadata =>
        auditLower compilation source statement metadata (.product .word .word)
          (.pair (.word (w 61)) (.word (w 61))) (Core.LocalLoop.returnedValue (.word (w 100))) []
        auditLower compilation source statement metadata (.product .word .word)
          (.pair (.word (w 62)) (.word (w 61))) (Core.LocalLoop.returnedValue (.word (w 900))) []
        count := count + 1
      | _ => pure ()
    | _ => pure ()
  require (count == 1) "ordered template occurrence count changed"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "ordered public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "runtime ordered match selection" content
    ["ordered", "choose", "failed", "scrutineeFault"]
  inspect compiled
  template_root
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (word 929)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("ordered", [word 37, word 8], word 8, [(.word, some (word 37)), (.word, some (word 8)), (.product .word .word, some (.product (word 37) (word 8))), (.word, some (word 8))]),
    ("ordered", [word 38, word 8], word 46, [(.word, some (word 38)), (.word, some (word 8)), (.product .word .word, some (.product (word 38) (word 8))), (.word, some (word 38)), (.word, some (word 8))]),
    ("choose", [word 0], word 11, [(.word, some (word 0)), (.word, some (word 0))]),
    ("choose", [word 1], word 13, [(.word, some (word 1)), (.word, some (word 1))]),
    ("choose", [word 2], word 17, [(.word, some (word 2)), (.word, some (word 2))]),
    ("failed", [word 1], word 19, [(.word, some (word 1)), (.word, some (word 1))])]
  for (name, arguments, expected, cells) in successes do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 7, 53, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) "ordered public resume changed"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected && reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"ordered public full cells changed {name}"
      | other => throw (IO.userError s!"ordered public success expected {reprStr other}")
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
      ("failed", [word 0], [(.word, some (word 0)), (.word, some (word 0)), (.word, some (word 41)), (.word, none)]),
      ("scrutineeFault", [], [(.word, none)])]
  for (name, arguments, cells) in failures do
    let actual ← match compiled.indexed.base.functions.find? (fun named =>
        compiled.sourceProgram.signatures.functions.any (fun signature => signature.id == named.specialized.function.declaration && signature.name == name)) with
      | some value => pure value | none => throw (IO.userError "fault source missing")
    let missing ← match (SourceCoreDataPlaces.declaredBinders actual.specialized.function.typedBody).findSome? (fun binder =>
        if binder.name == "missing" then some binder.id else none) with
      | some value => pure value | none => throw (IO.userError "fault binder missing")
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 7, 53, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) "ordered public fault resume changed"
      match observed with
      | .fault (.uninitializedLocal found) final =>
        require (found == missing && reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          "ordered public first fault/full cells changed"
      | other => throw (IO.userError s!"ordered public fault expected {reprStr other}")
  IO.println "runtime ordered match: actual root support / repeated arms and IDs / first selection and misses / empty default / full stores-heaps / original strict continuation / resume GREEN"

end Tests.SourceCoreCompatibleMatchRuntimeSelection
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMatchTypedPrefixes
/-! The independently selected compatible arm reaches an actual closure body
with exactly its real captured environment. Both finite directions preserve the
hidden/source binder allocations; no body evaluation is supplied by a caller. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMatchTypedPrefixes
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchSelectionPrefix CallableIndexedHistory

theorem selected_closure_body
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution (.function .unit .unit) internalReason
      expressionCertificate (fun _ _ code => code = LocalLoop.returnValue (.function .unit .unit) (LanguageResult.success (.lambda .unit .unit (.var 0)))) code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody (.arm statements bindings)) :
    ∃ hiddenHeap location selectedEnvironment selectedHeap selectedActual selectedStore selectedMap selectedWorld selectedContext,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.BindersAllocate environment hiddenHeap (bindings.map Prod.fst) (bindings.map Prod.snd) selectedEnvironment selectedHeap ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions selectedMap selectedWorld selectedHeap selectedStore ∧
      AdministrativePreserved mapping store selectedMap selectedStore ∧
      RuntimeEnvironmentHasTypes selectedWorld selectedActual selectedContext ambient.definitions ∧
      RuntimeValueHasType selectedWorld (.closure .unit .unit (.var 0) selectedActual) (.function .unit .unit) ambient.definitions ∧
      Evaluates actual before (code.rename ξ)
        (LocalLoop.returnedValue (.closure .unit .unit (.var 0) selectedActual)) selectedStore ∧
      (∀ result finished, Evaluates actual before (code.rename ξ) result finished →
        result = LocalLoop.returnedValue (.closure .unit .unit (.var 0) selectedActual) ∧ finished = selectedStore) := by
  obtain ⟨hiddenHeap, location, finalScope, selectedEnvironment, selectedHeap, selectedCanonical, selectedActual,
      selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
      allocated, selected, selectedBody, finalEnvironments, finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, _finalReference, _finalRead, _finalUnmapped, agreement⟩ :=
    CompatibleMatchTypedSelectionPrefix.Certificate.selected_prefix_typed certificate ordinary onError allocator valid catalogValid
      definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated selectedSource
  cases selectedBody with
  | arm identities bound certified =>
    subst body
    have child : Evaluates selectedActual selectedStore
        ((LocalLoop.returnValue (.function .unit .unit) (LanguageResult.success (.lambda .unit .unit (.var 0)))).rename selectedEmbedding)
        (LocalLoop.returnedValue (.closure .unit .unit (.var 0) selectedActual)) selectedStore := by
      simp only [LocalLoop.returnValue, LanguageResult.bind, LocalLoop.returned, LanguageResult.success, Expr.rename, Renaming.lift]
      exact .caseRight (.inRight .lambda) (.inRight (.inLeft (.inRight (.var rfl))))
    refine ⟨hiddenHeap, location, selectedEnvironment, selectedHeap, selectedActual, selectedStore, selectedMap, selectedWorld, selectedContext,
      allocated, bound, finalHeaps, preserved, finalTyped, .closure finalTyped (.var rfl), agreement.wrap child, ?_⟩
    intro result finished completed
    exact evaluation_deterministic completed (agreement.wrap child)


private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function captured(marker: Word) returns (integer) { match ((lam(x: Word) -> Word { marker = wordFromInteger(integerAdd(wordToInteger(marker), wordToInteger(x))); return marker; }, 2)) { case (f, x) { let changed = wordToInteger(f(x)); return changed; } } }",
    "function selected(p: Word) returns (integer) { match ((p, 7)) { case (0, x) { let next = wordFromInteger(integerAdd(wordToInteger(x), 4)); return wordToInteger(next); } case (v, x) { let next = wordFromInteger(integerAdd(wordToInteger(v), wordToInteger(x))); return wordToInteger(next); } } }",
    "function failed(p: Word) returns (integer) { let hole: Word; match ((p, 7)) { case (0, x) { return wordToInteger(x); } case (v, x) { let changed = wordFromInteger(integerAdd(wordToInteger(v), wordToInteger(hole))); return wordToInteger(changed); } } }"]}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "typed compatible match prefix" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  let captured ← SourceCompilerFeatureSupport.compileNamed program "captured"
  SourceCompilerFeatureSupport.require ((← captured.run [w 10]) == .integer 12) "selected closure lost actual typed mutable capture"
  for budget in [0, 7, 43] do captured.checkResume [w 10] (.integer 12) budget
  let selected ← SourceCompilerFeatureSupport.compileNamed program "selected"
  for (p, result) in [(0, 11), (3, 10)] do
    SourceCompilerFeatureSupport.require ((← selected.run [w p]) == .integer result) "selected builtin body changed matched binders or temporary values"
    let tuple : TypeSystem.Ty := .product .word .word
    let cells := if p == 0 then [(.word, some (w 7)), (.word, some (w 11))] else
      [(.word, some (w p)), (.word, some (w 7)), (.word, some (w 10))]
    selected.checkCells [w p] ([(.word, some (w p)), (tuple, some (.product (w p) (w 7)))] ++ cells)
    for budget in [0, 7, 43] do selected.checkResume [w p] (.integer result) budget
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let fault ← failed.invoke [w 3]
  match fault.outcome with
  | .failed _ _ => pure ()
  | _ => throw (IO.userError "selected builtin fault did not preserve the completed marked prefix")
  failed.checkCells [w 3] [(.word, some (w 3)), (.word, none),
    (.product .word .word, some (.product (w 3) (w 7))), (.word, some (w 3)), (.word, some (w 7))]
  IO.println "typed compatible match prefixes: all actual temporary slot typing, exact native closure captures, selected builtins and effectful faults GREEN"

end Tests.SourceCoreCompatibleMatchTypedPrefixes
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMixedPaths
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Checked source supplies roots and index occurrences. The retained ordinal
member path is assembled explicitly (source member syntax is not asserted).
Actual describe/prepare/checker/run preserve raw constructor IDs, raw mapping
headers, siblings, nested defaults, and ordered duplicate entries. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMixedPaths
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality CompatibleMapping CompatibleMapping.MixedPaths

private def w (n : Nat) : Word := Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Item(Word) }",
    "enum Holder<T> { Wrap(mapping(Word => T), Word), Other(mapping(Word => T), Word) }",
    "function mixed(root: mapping(Word => Holder<Word>), value: Holder<Word>, key: Word) returns (Word) { root[key] = value; return 0; }",
    "function missing(root: mapping(Word => Holder<Box>), value: Holder<Box>, key: Word) returns (Word) { root[key] = value; return 0; }",
    "function nested(root: mapping(Word => mapping(Word => @Word)), value: mapping(Word => @Word), key: Word) returns (Word) { root[key] = value; return 0; }"
  ]}] }
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def noIdentities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful noIdentities := ⟨False.elim, fun impossible _ => False.elim impossible⟩
private theorem noFunctionObservations (catalog : SourceCoreCompatibleCatalog.Catalog) :
    FunctionObservations catalog (noFunctions catalog) noIdentities := fun impossible => False.elim impossible

private def sourceFor (program : CheckedProgram) (name : String) : IO TypedSource := do
  let signature ← match program.signatures.functions.find? (·.name == name) with
    | some signature => pure signature | none => throw (IO.userError "mixed function missing")
  match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 100 with
  | .ok (.complete plan) => match plan.specializations with
    | [specialized] => pure specialized.function.typedBody
    | _ => throw (IO.userError "mixed specialization count changed")
  | other => throw (IO.userError s!"mixed specialization failed: {reprStr other}")
private def assignmentFor (source : TypedSource) : IO (StatementNode × AssignmentResolution × ExpressionId) := do
  let (node, assignment) ← match source.nodes.filterMap (fun
    | .statement node => match node.form with | .assignValue assignment _ _ => some (node, assignment) | _ => none
    | _ => none) with
    | [assignment] => pure assignment | _ => throw (IO.userError "mixed assignment missing")
  match assignment.target.projections with
  | [.index key] => pure (node, assignment, key)
  | _ => throw (IO.userError "mixed original assignment path changed")
private def encode (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty) (value : SourceCoreDataValues.Value) :
    IO (SourceCoreCompatibleValues.Encoded 500 context type value) :=
  match SourceCoreCompatibleValues.encode 500 context type value with
  | .ok encoded => pure encoded | .error error => throw (IO.userError s!"mixed encode failed: {reprStr error}")
private def decode (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty) (native : Value) (expected : SourceCoreDataValues.Value) : IO Unit :=
  match SourceCoreCompatibleValues.decode 500 context type native with
  | .ok actual => assertTrue (actual == expected) "mixed path lost raw metadata, sibling, or ordered duplicate"
  | .error error => throw (IO.userError s!"mixed decode failed: {reprStr error}")
private def completed (code : Expr) (environment : Environment) (before : Store) : IO (Value × Store) := do
  let result ← match runStateful 500000 (.initial code environment before) with
    | .done value after => pure (value, after)
    | other => throw (IO.userError s!"mixed helper failed: {reprStr other}")
  assertTrue (result.2.take before.length == before) "mixed helper changed source store prefix"
  match runStateful 7 (.initial code environment before) with
  | .outOfFuel checkpoint =>
    match runStateful 500000 checkpoint with
    | .done value after => assertTrue (value == result.1 && after == result.2) "mixed resume changed value/store"
    | _ => throw (IO.userError "mixed resume failed")
  | _ => throw (IO.userError "mixed fixture no longer checkpoints")
  pure result

/-- This consumer starts with actual memberStep and public encoding receipts.
Every projected child retains its full independent payload relation, including
nested mapping defaults and raw aliases; no helper execution is a premise. -/
private theorem member_receipt {context : SourceCoreCompatibleValues.Context}
    {root : TypeSystem.Ty} {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty}
    {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId}
    {step : SourceCoreCompatibleDataPlaces.Step} {field : TypeSystem.Ty}
    {metadata : DataConstructorInstantiation} {payload : List SourceCoreDataValues.Value}
    {sourcePayload : List Dynamic.Value}
    {encoded : SourceCoreCompatibleValues.Encoded 500 context root (.constructed metadata payload)}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments))
    (selected : context.checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
    (accepted : SourceCoreCompatibleDataPlaces.memberStep context.checked context.checked.signatures site binder root 0 = .ok (step, field))
    (encodedAccepted : SourceCoreCompatibleValues.encode 500 context root (.constructed metadata payload) = .ok encoded)
    (meaning : CompatibleEncoding.Meanings payload sourcePayload) :
    ∃ identity branches nativeField,
      step = .member identity 0 branches nativeField ∧
      ∃ sourceChild valueChild actual,
        Dynamic.ValueAt sourcePayload 0 sourceChild ∧
        SourceCoreRawMetadata.runtimeType actual = SourceCoreRawMetadata.runtimeType field ∧
        CompatiblePayload.ValueRep context.checked encoded.context.registry (noFunctions context.checked.catalog) [] [] actual sourceChild valueChild nativeField := by
  obtain ⟨identity, branches, nativeField, stepEq, certificate⟩ :=
    CompatibleMemberCertificates.certificate_of_memberStep nominal selected accepted
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions context.checked.catalog)
    encodedAccepted (.constructed meaning) [] []
  obtain ⟨tag, id, values, types, valueEq, typeEq, fields⟩ := constructor_fields represented rfl
  obtain ⟨_, branch, actual, sourceChild, valueChild, _, _, _, _, view, _, sourceAt, _, related⟩ :=
    certificate.select nominal selected fields
  exact ⟨identity, branches, nativeField, stepEq, sourceChild, valueChild, actual, sourceAt, view, related⟩

private def exercise (initial : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (rootType leafType : TypeSystem.Ty) (rootCarrier replacement : SourceCoreDataValues.Value)
    (member : Bool) (optionalAbsent : Bool) (expectedRead : Option SourceCoreDataValues.Value)
    (expectedUpdate : Option SourceCoreDataValues.Value) (missingHeader : Option Word := none) : IO Unit := do
  let (node, assignment, key) ← assignmentFor source
  let assignment := { assignment with target := { assignment.target with
    type := leafType
    projections := if member then [.index key, .member "entries" 0, .index key] else [.index key, .index key]}}
  let root ← encode initial rootType rootCarrier
  let replacement ← encode root.context leafType replacement
  let context := replacement.context
  let route ← match SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source (.occurrence node.id.occurrence) assignment with
    | .ok route => pure route | .error error => throw (IO.userError s!"mixed describe failed: {reprStr error}")
  let prepared ← match preparedAccepted : SourceCoreCompatibleDataPlaces.prepare context 200 route (w 900) (fun _ => w 1000) with
    | .ok prepared =>
      have _receipt := CompatibleMixedPreparation.of_prepare preparedAccepted
      pure prepared | .error error => throw (IO.userError s!"mixed prepare failed: {reprStr error}")
  assertTrue (prepared.keys.map Prod.fst == [key, key]) "mixed key occurrences/positions changed"
  let keys := Value.pair (.word (w 1)) (.word (w 1))
  let keyType := Ty.product .word .word
  let optional := if optionalAbsent then Value.inLeft route.rootType .unit else .inRight .unit root.value
  let before := [optional, Value.integer (-99)]
  let getter := SourceCoreCompatibleDataPlaces.getter prepared keyType
  let setter := SourceCoreCompatibleDataPlaces.setter prepared keyType
  assertTrue (infer? [] getter context.checked.catalog.definitions == some (.function (.product (OptionalCell.cellType route.rootType) keyType) (LanguageResult.resultType prepared.optionalLeaf))) "mixed getter checker failed"
  assertTrue (infer? [] setter context.checked.catalog.definitions == some (.function (.product (OptionalCell.cellType route.rootType) (.product keyType route.leafType)) (LanguageResult.resultType route.rootType))) "mixed setter checker failed"
  let (read, readStore) ← completed (.apply getter (.var 0)) [.pair optional keys] before
  assertTrue (readStore.length == before.length + 2 * (context.checked.catalog.entries.length + 1)) "mixed lookup allocation count changed"
  match expectedRead, read with
  | some expected, .inRight .word (.inRight .unit value) => decode context leafType value expected
  | none, .inLeft _ (.word token) => assertTrue (some token == missingHeader.map ((w 1000).add)) "mixed fault used outer raw header"
  | _, _ => throw (IO.userError s!"mixed getter outcome changed: {reprStr read}")
  let (updated, updateStore) ← completed (.apply setter (.var 0)) [.pair optional (.pair keys replacement.value)] before
  match expectedUpdate, updated with
  | some expected, .inRight .word value =>
    decode context rootType value expected
    assertTrue (updateStore.length == before.length + 4 * (context.checked.catalog.entries.length + 1)) "mixed setter skipped selection or outer insertion"
  | none, .inLeft _ (.word token) =>
    assertTrue (some token == missingHeader.map ((w 1000).add)) "mixed setter fault token changed"
    assertTrue (updateStore.length == readStore.length) "mixed setter inserted after inner failure"
  | _, _ => throw (IO.userError s!"mixed setter outcome changed: {reprStr updated}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"mixed source rejected: {reprStr error}")
  let holder ← match program.signatures.dataTypes.find? (·.name == "Holder") with
    | some holder => pure holder | none => throw (IO.userError "mixed Holder missing")
  let constructor ← match holder.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "mixed Wrap missing")
  let parameter ← match holder.parameters with
    | [parameter] => pure parameter | _ => throw (IO.userError "mixed Holder parameter changed")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "mixed Box missing")
  let boxCtor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "mixed Item missing")
  let holderWord := TypeSystem.Ty.nominal holder.id [.word]
  let rawHolder := TypeSystem.Ty.nominal holder.id [.comptime .word]
  let holderBox := TypeSystem.Ty.nominal holder.id [.nominal box.id []]
  let nested := TypeSystem.Ty.mapping .word (.mapping .word (.proxy .word))
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 500 [.mapping .word holderWord, .mapping .word holderBox, nested] with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"mixed catalog failed: {reprStr error}")
  let context := SourceCoreCompatibleValues.Context.initial checked
  let metadata : DataConstructorInstantiation := ⟨constructor.id, [(parameter, .comptime .word)], [.mapping .word (.comptime .word), .word], rawHolder⟩
  let inner : SourceCoreDataValues.Value := .mapping .word (.comptime .word) [(.word (w 1), .word (w 2)), (.word (w 1), .word (w 9))]
  let held := SourceCoreDataValues.Value.constructed metadata [inner, .word (w 55)]
  let root := SourceCoreDataValues.Value.mapping .word rawHolder [(.word (w 1), held), (.word (w 1), held)]
  let updatedInner := SourceCoreDataValues.Value.mapping .word (.comptime .word) [(.word (w 1), .word (w 7)), (.word (w 1), .word (w 9))]
  let updated := SourceCoreDataValues.Value.mapping .word rawHolder [(.word (w 1), .constructed metadata [updatedInner, .word (w 55)]), (.word (w 1), held)]
  exercise context (← sourceFor program "mixed") (.mapping .word holderWord) .word root (.word (w 7)) true false (some (.word (w 2))) (some updated)
  let boxType := TypeSystem.Ty.nominal box.id []
  let item : DataConstructorInstantiation := ⟨boxCtor.id, [], [.word], boxType⟩
  let boxHolder : DataConstructorInstantiation := ⟨constructor.id, [(parameter, boxType)], [.mapping .word boxType, .word], holderBox⟩
  let emptyInner := SourceCoreDataValues.Value.mapping .word boxType []
  let innerEncoded ← encode context (.mapping .word boxType) emptyInner
  let header ← match innerEncoded.value with
    | .pair (.word header) _ => pure header | _ => throw (IO.userError "mixed inner raw header absent")
  let missingRoot := SourceCoreDataValues.Value.mapping .word holderBox [(.word (w 1), .constructed boxHolder [emptyInner, .word (w 55)])]
  exercise innerEncoded.context (← sourceFor program "missing") (.mapping .word holderBox) boxType missingRoot (.constructed item [.word (w 7)]) true false none none (some header)
  let empty := SourceCoreDataValues.Value.mapping .word (.mapping .word (.proxy .word)) []
  let updated := SourceCoreDataValues.Value.mapping .word (.mapping .word (.proxy .word))
    [(.word (w 1), .mapping .word (.proxy .word) [(.word (w 1), .proxy .word)])]
  exercise context (← sourceFor program "nested") nested (.proxy .word) empty (.proxy .word) false true (some (.proxy .word)) (some updated)
  IO.println "compatible mixed member/mapping paths proofs GREEN"

end Tests.SourceCoreCompatibleMixedPaths
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatiblePathCertificates
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Actual route/preparation and codec receipts produce semantic trees for a
nested mapping. No hand-authored comparator tree or helper evaluation occurs. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Tests.SourceCoreCompatiblePathCertificates
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreCompatibleDataPlaces CompatiblePayload CompatibleEquality CompatibleMapping CompatibleMapping.MixedPaths CompatibleMixedRoute

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_path", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_path.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def innerType : TypeSystem.Ty := .mapping .bool .word
private def rootType : TypeSystem.Ty := .mapping .bool innerType
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def projections : List PlaceProjection := [.index key, .index key]
private def assignment : AssignmentResolution := ⟨⟨binder.id, projections, .word⟩, []⟩
private def innerLayout : OrderedMapping.Layout := ⟨.bool, .word, ⟨1⟩⟩
private def outerLayout : OrderedMapping.Layout := ⟨.bool, SourceCoreMappingWithDefault.type innerLayout, ⟨0⟩⟩
private def route : Route := ⟨rootType, SourceCoreMappingWithDefault.type outerLayout, .word,
  [.index outerLayout key innerType, .index innerLayout key .word], none⟩
private theorem preparedExists : (prepare context 100 route Word.zero (fun _ => Word.zero)).toOption.isSome = true := by cbv
private def prepared := (prepare context 100 route Word.zero (fun _ => Word.zero)).toOption.get preparedExists
private theorem preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) = .ok prepared := except_get _ preparedExists
private theorem routed : routeSteps checked checked.signatures source site binder.id rootType projections = .ok (route.steps, .word) := by cbv
private theorem path : PreparedPath checked source site rootType projections 0 prepared.steps prepared.keys .word :=
  (prepared_of_success routed preparedBy).2.2
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def keys : List Value := [.bool true, .bool true]
private def resolved : List Dynamic.EvaluatedProjection := [.index (.bool true), .index (.bool true)]

private theorem arguments {registry : SourceCoreRawMetadata.Registry} {steps : List PreparedStep} {sites : List (ExpressionId × Ty)}
    (actualPath : PreparedPath checked source site rootType projections 0 steps sites .word) :
    Arguments checked registry (noFunctions checked.catalog) [] [] source site keys actualPath resolved := by
  cases actualPath with
  | index first generated tail =>
    have shape := TypeSystem.Ty.mapping.inj first.view
    obtain ⟨rfl, rfl⟩ := shape
    have nativeKey := Except.ok.inj first.keyProjection
    cases tail with
    | index second other final =>
      have shape := TypeSystem.Ty.mapping.inj second.view
      obtain ⟨rfl, rfl⟩ := shape
      have secondKey := Except.ok.inj second.keyProjection
      cases final
      apply Arguments.index (certificate := first) (generated := generated) rfl
      · rw [← nativeKey]; exact .bool true
      · apply Arguments.index (certificate := second) (generated := other) rfl
        · rw [← secondKey]; exact .bool true
        · exact .nil

private def w (n : Nat) : Word := Word.ofNatModulo n
private def inner : SourceCoreDataValues.Value := .mapping .bool .word [(.bool true, .word (w 2)), (.bool true, .word (w 9))]
private def carrier : SourceCoreDataValues.Value := .mapping .bool innerType [(.bool true, inner)]
private def sourceInner : Dynamic.Value := .mapping .bool .word [(.bool true, .word (w 2)), (.bool true, .word (w 9))]
private def sourceRoot : Dynamic.Value := .mapping .bool innerType [(.bool true, sourceInner)]
private theorem meaning : CompatibleEncoding.Means carrier sourceRoot :=
  .mapping (.prepend (.bool _) (.mapping (.prepend (.bool _) (.word _) (.prepend (.bool _) (.word _) .empty))) .empty)
private theorem represented {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (encodedBy : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) :
    ValueRep checked encoded.context.registry (noFunctions checked.catalog) [] [] rootType sourceRoot encoded.value encoded.type :=
  CompatibleEncoding.encode_represents_at encodedBy meaning [] []
private theorem sourceRead : Dynamic.ProjectionsRead (some sourceRoot) resolved (some (.word (w 2))) :=
  .indexFound (.head ⟨rfl, .bool _⟩) (.indexFound (.head ⟨rfl, .bool _⟩) .nil)

example {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) : ReadTree checked encoded.context.registry (noFunctions checked.catalog) [] [] prepared keys
    .word .word rootType sourceRoot encoded.value prepared.steps resolved (.word (w 2)) (readCost checked prepared.steps) :=
  (arguments path).readTree (represented accepted) rfl sourceRead prepared

private def changedInner : Dynamic.Value := .mapping .bool .word [(.bool true, .word (w 7)), (.bool true, .word (w 9))]
private def changedRoot : Dynamic.Value := .mapping .bool innerType [(.bool true, changedInner)]
private theorem sourceUpdate : Dynamic.ProjectionsUpdate (fun _ value => value = .word (w 7)) (some sourceRoot) resolved changedRoot :=
  .indexFound (.head ⟨rfl, .bool _⟩)
    (.indexFound (.head ⟨rfl, .bool _⟩) (.leaf rfl) (.update (.head ⟨rfl, .bool _⟩))) (.update (.head ⟨rfl, .bool _⟩))
example {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) : UpdateTree checked encoded.context.registry (noFunctions checked.catalog) [] [] prepared keys
    (.word (w 7)) (.word (w 7)) rootType sourceRoot encoded.value encoded.type prepared.steps resolved changedRoot (updateCost checked prepared.steps) :=
  (arguments path).updateTree (represented accepted) (.word (w 7)) sourceUpdate prepared

private def noIdentities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful noIdentities := ⟨False.elim, fun impossible _ => False.elim impossible⟩
private theorem noFunctionObservations : FunctionObservations checked.catalog (noFunctions checked.catalog) noIdentities := fun impossible => False.elim impossible

private theorem completed_read {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) : ∃ value after administrative,
    Dynamic.RootInitialValue (⟨rootType, some sourceRoot, none⟩ : Dynamic.Cell) (some sourceRoot) ∧
    Dynamic.ProjectionsRead (some sourceRoot) resolved (some (.word (w 2))) ∧
    ValueRep checked encoded.context.registry (noFunctions checked.catalog) [] [] .word (.word (w 2)) value .word ∧
    FiniteRun [.pair (.inRight .unit encoded.value) (DataPatternValues.packValues keys)] []
      (.apply (getter prepared (.product .bool .bool)) (.var 0)) (.inRight .word (.inRight .unit value)) after ∧
    after = [] ++ administrative ∧ administrative.length = readCost checked prepared.steps := by
  exact getter_preserves_run (.initialized (sourceType := rootType))
    ((arguments path).readTree (represented accepted) rfl sourceRead prepared) rfl (by cbv; intro impossible; cases impossible)
    faithful noFunctionObservations (by cbv) _ [] (.product .bool .bool) (.var 0) (.var rfl)

private theorem completed_update {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) :
    ∃ value after administrative,
      Dynamic.RootInitialValue (⟨rootType, some sourceRoot, none⟩ : Dynamic.Cell) (some sourceRoot) ∧
      Dynamic.ProjectionsUpdate (fun _ value => value = .word (w 7)) (some sourceRoot) resolved changedRoot ∧
      ValueRep checked encoded.context.registry (noFunctions checked.catalog) [] [] rootType changedRoot value encoded.type ∧
      FiniteRun [.pair (.inRight .unit encoded.value) (.pair (DataPatternValues.packValues keys) (.word (w 7)))] []
        (.apply (setter prepared (.product .bool .bool)) (.var 0)) (.inRight .word value) after ∧
      after = [] ++ administrative ∧ administrative.length = updateCost checked prepared.steps := by
  exact setter_preserves_run (.initialized (sourceType := rootType))
    ((arguments path).updateTree (represented accepted) (.word (w 7)) sourceUpdate prepared)
    rfl (by cbv; intro impossible; cases impossible) faithful noFunctionObservations (by cbv) _ []
    (.product .bool .bool) (.var 0) (.var rfl)

private def runSuccess : IO Unit := do
  match accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier with
  | .error error => throw (IO.userError s!"path input encoding failed: {reprStr error}")
  | .ok encoded =>
    have _whole := completed_read accepted
    have _updated := completed_update accepted
    let code := Expr.apply (getter prepared (.product .bool .bool)) (.var 0)
    let environment := [Value.pair (.inRight .unit encoded.value) (DataPatternValues.packValues keys)]
    match runStateful 100000 (.initial code environment []) with
    | .done (.inRight .word (.inRight .unit (.word value))) _ =>
      unless value == w 2 do throw (IO.userError "automatic path read chose later duplicate")
    | other => throw (IO.userError s!"automatic path read failed: {reprStr other}")
    let write := Expr.apply (setter prepared (.product .bool .bool)) (.var 0)
    let writeEnvironment := [Value.pair (.inRight .unit encoded.value) (.pair (DataPatternValues.packValues keys) (.word (w 7)))]
    match runStateful 100000 (.initial write writeEnvironment []) with
    | .done (.inRight .word value) after =>
      let expected : SourceCoreDataValues.Value := .mapping .bool innerType [(.bool true, .mapping .bool .word [(.bool true, .word (w 7)), (.bool true, .word (w 9))])]
      match SourceCoreCompatibleValues.decode 100 encoded.context rootType value with
      | .ok actual => unless actual == expected do throw (IO.userError "automatic path update changed duplicate order")
      | .error error => throw (IO.userError s!"automatic path update decode failed: {reprStr error}")
      unless after.length == 4 * (checked.catalog.entries.length + 1) do throw (IO.userError "automatic path update allocation count changed")
    | other => throw (IO.userError s!"automatic path update failed: {reprStr other}")
  IO.println "compatible path certificate extraction GREEN"

namespace Fault
private def leaf : TypeSystem.Ty := .function .word .word
private def innerType : TypeSystem.Ty := .mapping .bool leaf
private def rootType : TypeSystem.Ty := .mapping .bool innerType
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def source : TypedSource := { owner, inputs := [⟨binder.id, "root", .mono rootType, [], false, none⟩], roots := [.expression key], nodes := [.expression node] }
private def innerLayout : OrderedMapping.Layout := ⟨.bool, CallableContract.functionType .word .word, ⟨1⟩⟩
private def outerLayout : OrderedMapping.Layout := ⟨.bool, SourceCoreMappingWithDefault.type innerLayout, ⟨0⟩⟩
private def route : Route := ⟨rootType, SourceCoreMappingWithDefault.type outerLayout, innerLayout.valueType,
  [.index outerLayout key innerType, .index innerLayout key leaf], none⟩
private theorem preparedExists : (prepare context 100 route Word.zero (fun _ => Word.zero)).toOption.isSome = true := by cbv
private def prepared := (prepare context 100 route Word.zero (fun _ => Word.zero)).toOption.get preparedExists
private theorem preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) = .ok prepared := except_get _ preparedExists
private theorem routed : routeSteps checked checked.signatures source site binder.id rootType projections = .ok (route.steps, leaf) := by cbv
private theorem path : PreparedPath checked source site rootType projections 0 prepared.steps prepared.keys leaf :=
  (prepared_of_success routed preparedBy).2.2
private theorem arguments {registry : SourceCoreRawMetadata.Registry} {steps : List PreparedStep} {sites : List (ExpressionId × Ty)}
    (actualPath : PreparedPath checked source site rootType projections 0 steps sites leaf) :
    Arguments checked registry (noFunctions checked.catalog) [] [] source site keys actualPath resolved := by
  cases actualPath with
  | index first generated tail =>
    have shape := TypeSystem.Ty.mapping.inj first.view
    obtain ⟨rfl, rfl⟩ := shape
    have nativeKey := Except.ok.inj first.keyProjection
    cases tail with
    | index second other final =>
      have shape := TypeSystem.Ty.mapping.inj second.view
      obtain ⟨rfl, rfl⟩ := shape
      have secondKey := Except.ok.inj second.keyProjection
      cases final
      apply Arguments.index (certificate := first) (generated := generated) rfl
      · rw [← nativeKey]; exact .bool true
      · apply Arguments.index (certificate := second) (generated := other) rfl
        · rw [← secondKey]; exact .bool true
        · exact .nil
private def carrier : SourceCoreDataValues.Value := .mapping .bool innerType [(.bool true, .mapping .bool leaf [])]
private def sourceRoot : Dynamic.Value := .mapping .bool innerType [(.bool true, .mapping .bool leaf [])]
private theorem meaning : CompatibleEncoding.Means carrier sourceRoot := .mapping (.prepend (.bool _) (.mapping .empty) .empty)
private theorem sourceFault : Dynamic.ProjectionsFaults (some sourceRoot) resolved (.missingMappingDefault leaf) :=
  .indexFound (.bool _) (.head ⟨rfl, .bool _⟩) (.indexDefaultUnavailable (.bool _) .nil (by intro defaulted; cases defaulted))
private theorem noFunctionObservations : FunctionObservations checked.catalog (noFunctions checked.catalog) noIdentities := fun impossible => False.elim impossible
private theorem completed_fault {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) :
    ∃ token count after administrative,
      FaultToken checked encoded.context.registry sourceRoot prepared.steps resolved (.missingMappingDefault leaf) token count ∧
      FiniteRun [.pair (.inRight .unit encoded.value) (DataPatternValues.packValues keys)] []
        (.apply (getter prepared (.product .bool .bool)) (.var 0)) (.inLeft prepared.optionalLeaf (.word token)) after ∧
      after = [] ++ administrative ∧ administrative.length = count := by
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted meaning [] []
  have typeEq : encoded.type = prepared.route.rootType := by
    have projected := encoded.projected
    have expected : checked.catalog.project rootType = .ok route.rootType := by cbv
    rw [(CompatibleMixedPreparation.of_prepare preparedBy).1]
    exact Except.ok.inj (projected.symm.trans expected)
  rw [typeEq] at represented
  obtain ⟨token, count, receipt, tree⟩ := (arguments path).faultTree represented sourceFault prepared
  obtain ⟨after, administrative, _, _, ran, appended, counted⟩ := getter_fault_run
    (.initialized (sourceType := rootType)) tree rfl (by cbv; intro impossible; cases impossible)
    faithful noFunctionObservations (by cbv) [.pair (.inRight .unit encoded.value) (DataPatternValues.packValues keys)] []
    (.product .bool .bool) (.var 0) (.var rfl)
  exact ⟨token, count, after, administrative, receipt, ran, appended, counted⟩
private def run : IO Unit := do
  match accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier with
  | .error error => throw (IO.userError s!"fault path input encoding failed: {reprStr error}")
  | .ok encoded =>
    have _whole := completed_fault accepted
    let code := Expr.apply (getter prepared (.product .bool .bool)) (.var 0)
    let environment := [Value.pair (.inRight .unit encoded.value) (DataPatternValues.packValues keys)]
    match runStateful 100000 (.initial code environment []) with
    | .done (.inLeft _ (.word token)) after =>
      unless encoded.context.registry.lookup token == some (.mapping .bool leaf) do throw (IO.userError "fault path token lost inner raw mapping metadata")
      unless after.length == 2 * (checked.catalog.entries.length + 1) do throw (IO.userError "fault path administrative count changed")
    | other => throw (IO.userError s!"automatic fault path failed: {reprStr other}")
end Fault

def run : IO Unit := do
  runSuccess
  Fault.run
  IO.println "compatible path fault certificate extraction GREEN"

end Tests.SourceCoreCompatiblePathCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatiblePatternLiteralRuntime
/-! Actual matcher acceptance supplies numeric implementation provenance. The
formal consumers keep the complete runtime ledger and need neither Covers nor
ordinary validity. Runtime checks also preserve unrelated assumption rows;
those ledger mutations are retained-IR tests, not checker-produced programs. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatiblePatternLiteralRuntime
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatiblePatternLeaves
open SourceCoreCompatibleDataMatches

section Accepted
variable {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
  {fuel : Nat} {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
  {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : CertifiedPattern compilation.definitions}
  (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
  (signatures : context.signatures = compilation.signatures)
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context) (leaf : LeafResolution pattern.resolution)
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
  {sourceValue : Dynamic.Value} {value : Core.Value} {world : StoreTyping}
  (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
include accepted signatures sameLedger runtime leaf represented

theorem accepted_preserves (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store :=
  CompatiblePatternLiteralRuntime.preserves
    (CompatiblePatternLiteralRuntime.of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)
    signatures sameLedger runtime leaf represented environment store

theorem accepted_reflects {environment : Environment} {store after : Store} {outcome : Core.Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome after) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧ after = store :=
  CompatiblePatternLiteralRuntime.reflects
    (CompatiblePatternLiteralRuntime.of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)
    signatures sameLedger runtime leaf represented completed
end Accepted

section ActualFrame
variable {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
  {types : List TypeSystem.Ty} (frame : NamedCalls.SourceFrame program instantiation body function)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (programTyped : ProgramWellFormed program)
  {compilation : SourceCoreCompatibleDataMatches.Context} {fuel : Nat} {scope : Scope}
  {site : StatementId} {span : Syntax.SourceSpan} {expected : TypeSystem.Ty}
  {pattern : TypedMatchPattern} {compiled : CertifiedPattern compilation.definitions}
  (accepted : compilePattern compilation fuel function.source scope site span expected pattern = .ok compiled)
  (signatures : context.signatures = compilation.signatures)
  (sameLedger : function.context.solvedRequirements = compilation.solvedRequirements)
  (leaf : LeafResolution pattern.resolution)
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
  {sourceValue : Dynamic.Value} {value : Core.Value} {world : StoreTyping}
  (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
include frame extended programTyped accepted signatures sameLedger leaf represented

theorem frame_preserves (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store :=
  accepted_preserves accepted signatures
    ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped) leaf represented environment store

theorem frame_reflects {environment : Environment} {store after : Store} {outcome : Core.Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome after) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧ after = store :=
  accepted_reflects accepted signatures
    ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped) leaf represented completed
end ActualFrame

section Boundaries
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def resolution : IntegerLiteralResolution := ⟨37, .word, ⟨0⟩⟩

/-- Runtime validity leaves assumption rows present. It does not authenticate
such a row as the validator-selected numeric implementation. -/
theorem runtime_not_selection :
    RuntimeRequirementLedgerValid ((Context.ofSignatures signatures).withSolvedRequirements [row]) ∧
    ¬ ∃ implementation, NumericLiteralEvidenceReceipts.Selected [row] resolution implementation := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · change ([⟨0⟩] : List RequirementId).Nodup
      decide
    · intro item evidence member implementation
      have eq : item = row := by simpa [Context.withSolvedRequirements] using member
      subst item
      cases implementation
  · rintro ⟨implementation, item, singleton, _, selected⟩
    have eq : item = row := by simpa [row, resolution] using singleton.symm
    subst item
    cases selected

theorem wildcard_needs_no_numeric (compilation : SourceCoreCompatibleDataMatches.Context) :
    CompatiblePatternLiteralRuntime.NumericSelected compilation .wildcard := by
  intro literal numeric impossible
  cases impossible

theorem binder_needs_no_numeric (compilation : SourceCoreCompatibleDataMatches.Context) (binder : TypedBinder) :
    CompatiblePatternLiteralRuntime.NumericSelected compilation (.binder binder) := by
  intro literal numeric impossible
  cases impossible
end Boundaries

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def huge : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639937
private def content : String := String.intercalate "\n" [
  "function wordMatch(x: Word) returns (Word) { match (x) { case 37 { return 11; } case bound { return bound; } } }",
  s!"function wordWrap(x: Word) returns (Word) \{ match (x) \{ case {huge} \{ return 13; } default \{ return 17; } } }",
  s!"function integerMatch(x: integer) returns (Word) \{ match (x) \{ case {huge} \{ return 19; } default \{ return 23; } } }",
  "function faultMatch(x: Word) returns (Word) { match (x) { case 37 { x = 41; let missing: Word; return missing; } default { return 29; } } }"
]

private def inspectPattern (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (site : StatementId) (span : Syntax.SourceSpan) (pattern : TypedMatchPattern)
    (rows : List SolvedRequirement) : IO Unit := do
  let compilation : SourceCoreCompatibleDataMatches.Context :=
    ⟨.initial checked, rows, none, none⟩
  match accepted : compilePattern compilation 100 source [] site span pattern.type pattern with
  | .error error => throw (IO.userError s!"actual numeric matcher rejected: {reprStr error}")
  | .ok compiled =>
    have receipt := CompatiblePatternLiteralRuntime.of_compilePattern compilation 100 source [] site span pattern.type pattern compiled accepted
    let _receipt := receipt
    match pattern.resolution with
    | .integerLiteral _ numeric =>
      let selected ← match rows.filter (·.id == numeric.requirement) with
        | [row] => pure row
        | _ => throw (IO.userError "numeric matcher row lost singleton identity")
      let implementation : ProgramImplId := .builtin (if pattern.type == .integer then .intInteger else .intWord)
      require (selected.predicate == numeric.predicate &&
        selected.evidence == .implementation (.byImpl numeric.predicate implementation []))
        "numeric matcher full implementation/premises changed"
      let expected := if pattern.type == .integer then Core.Value.integer (Int.ofNat numeric.rawValue)
        else .word (Word.ofNatModulo numeric.rawValue)
      let different := if pattern.type == .integer then Core.Value.integer (Int.ofNat numeric.rawValue + 1)
        else .word (Word.ofNatModulo (numeric.rawValue + 1))
      for (input, wanted) in [(expected, Core.Value.inRight .unit .unit), (different, .inLeft .unit .unit)] do
        let quoted ← match SourceCoreCompatibleDataExpressions.quote input with
          | some code => pure code | none => throw (IO.userError "numeric input quote missing")
        let code := Core.Expr.apply compiled.pattern.matcher quoted
        require (Core.Program.mk compiled.pattern.resultType code compilation.definitions).check
          "numeric matcher actual native typing failed"
        let sentinel : Core.Store := [.integer 901, .closure .unit .integer (.var 1) [.integer 777], .cellRef .integer 0]
        for fuel in [0, 2, 11, 1000] do
          let outcome := match Core.runStateful fuel (.initial code [] sentinel) with
            | .outOfFuel pending => Core.runStateful 1000 pending
            | other => other
          match outcome with
          | .done actual store =>
            require (actual == wanted && store == sentinel)
              "numeric match/miss or full saved store/captures changed on resume"
          | other => throw (IO.userError s!"numeric matcher did not finish: {reprStr other}")
    | _ => throw (IO.userError "numeric matcher audit reached a nonnumeric pattern")

private def inspect (artifact : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut count := 0
  for named in artifact.indexed.base.functions do
    let selected ← get "actual selected numeric matcher owner"
      (SourceCompilationPlan.exactSpecialization artifact.indexed.base.plan named.signature.key)
    require (selected == named.specialized) "numeric matcher full selected function changed"
    let source := selected.function.typedBody
    let rows := selected.function.solvedRequirements
    for retained in source.nodes do
      match retained with
      | .statement statement => match statement.form with
        | .matchWith metadata =>
          for arm in metadata.cases do
            match arm.pattern.resolution with
            | .integerLiteral _ numeric =>
              count := count + 1
              inspectPattern artifact.compatible.checked source statement.id arm.span arm.pattern rows
              let fresh : RequirementId := ⟨(rows.map (·.id.index)).foldl max 0 + 1⟩
              let unused : SolvedRequirement := ⟨fresh, numeric.predicate, .assumption numeric.predicate⟩
              for fullRows in [unused :: rows, rows ++ [unused]] do
                inspectPattern artifact.compatible.checked source statement.id arm.span arm.pattern fullRows
              let malformed := rows.map fun row => if row.id == numeric.requirement then
                {row with evidence := .assumption row.predicate} else row
              let compilation : SourceCoreCompatibleDataMatches.Context :=
                ⟨.initial artifact.compatible.checked, malformed, none, none⟩
              require (compilePattern compilation 100 source [] statement.id arm.span arm.pattern.type arm.pattern).toOption.isNone
                "numeric matcher accepted metadata without actual implementation"
              let duplicated := rows ++ rows.filter (·.id == numeric.requirement)
              require (compilePattern {compilation with solvedRequirements := duplicated} 100 source [] statement.id arm.span arm.pattern.type arm.pattern).toOption.isNone
                "numeric matcher accepted a duplicate selected requirement ID"
            | _ => pure ()
        | _ => pure ()
      | _ => pure ()
  require (count == 4) "actual matcher audit count changed"

/-- The matcher is compiled from a real specialized body that still contains
qualified-local template rows. This certifies only the reached pattern, not
the lambda or the complete callable body. -/
private def template_root : IO Unit := do
  let program ← get "pattern checked template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " let f = lam(item) { return keep(item); }; let number: Word = 61;",
      " match (number) { case 61 { return (f(1), f(flag)); } default { return (f(2), f(flag)); } } }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "template pattern signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "template pattern function missing")
  let actual ← get "pattern actual template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger.map (·.id) == generic.solvedRequirements.map (·.id))
    "pattern template IDs or complete ordered ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !actual.assumptions.contains predicate)
          "pattern template assumption was promoted"
      | _ => throw (IO.userError "pattern template implementation fabricated")
    | _ => throw (IO.userError "pattern template row missing or duplicated")
  let checked ← get "pattern template catalog" (SourceCoreCompatibleCatalog.prepare program.signatures 100 [.word, .bool])
  let mut count := 0
  for node in source.nodes do
    match node with
    | .statement statement => match statement.form with
      | .matchWith metadata =>
        for arm in metadata.cases do
          match arm.pattern.resolution with
          | .integerLiteral _ _ =>
            inspectPattern checked source statement.id arm.span arm.pattern ledger
            count := count + 1
          | _ => pure ()
      | _ => pure ()
    | _ => pure ()
  require (count == 1) "template pattern occurrence count changed"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"numeric pattern full source heap changed: {reprStr state.heap}"

def run : IO Unit := do
  let artifact ← SourceCoreUnifiedCorpusSupport.prepare "runtime numeric pattern receipts" content
    ["wordMatch", "wordWrap", "integerMatch", "faultMatch"]
  inspect artifact
  template_root
  let w := Word.ofNatModulo
  let successes : List (String × SourceTypedRuntime.Value × Nat × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("wordMatch", .word (w 37), 11, [(.word, some (.word (w 37))), (.word, some (.word (w 37)))]),
    ("wordMatch", .word (w 7), 7, [(.word, some (.word (w 7))), (.word, some (.word (w 7))), (.word, some (.word (w 7)))]),
    ("wordWrap", .word (w 1), 13, [(.word, some (.word (w 1))), (.word, some (.word (w 1)))]),
    ("wordWrap", .word (w 2), 17, [(.word, some (.word (w 2))), (.word, some (.word (w 2)))]),
    ("integerMatch", .integer (Int.ofNat huge), 19, [(.integer, some (.integer (Int.ofNat huge))), (.integer, some (.integer (Int.ofNat huge)))]),
    ("integerMatch", .integer 1, 23, [(.integer, some (.integer 1)), (.integer, some (.integer 1))]),
    ("faultMatch", .word (w 3), 29, [(.word, some (.word (w 3))), (.word, some (.word (w 3)))])]
  let missing ← match (artifact.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
    | [binder] => pure binder.id | _ => throw (IO.userError "numeric pattern missing binder identity lost")
  for fuel in [0, 37, 151, 300000] do
    for (name, input, result, heap) in successes do
      let first ← SourceCoreUnifiedCorpusSupport.execute artifact name [input] fuel
      let finished ← get "numeric match public resume" (first.resume 300000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr (SourceTypedRuntime.Value.word (w result))) "numeric match public result changed"
        cells state heap
      | other => throw (IO.userError s!"numeric match success expected: {reprStr other}")
    let first ← SourceCoreUnifiedCorpusSupport.execute artifact "faultMatch" [.word (w 37)] fuel
    let finished ← get "numeric match fault resume" (first.resume 300000)
    match finished.observation with
    | .fault (.uninitializedLocal actual) state =>
      require (actual == missing) "numeric pattern first fault identity changed"
      cells state [(.word, some (.word (w 41))), (.word, some (.word (w 37))), (.word, none)]
    | other => throw (IO.userError s!"numeric selected arm fault expected: {reprStr other}")
  IO.println "pattern actual numeric rows / complete runtime ledger / Word Integer match and miss / full store and heap / resume GREEN"
end Tests.SourceCoreCompatiblePatternLiteralRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatiblePatternProofs
/-! Actual compatible compiler consumers use general payloads and ambient
nominal definitions. The formal leaf results require only input representation,
not a matcher trace. Composite runtime fixtures retain raw constructor guards;
full composite matching and marked arm allocation are separate proof layers. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace Tests.SourceCoreCompatiblePatternProofs
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatiblePatternLeaves

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_pattern_proofs", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "compatible_pattern_proofs.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def source : TypedSource := {owner, inputs := [], roots := [], nodes := []}
private def functionType : TypeSystem.Ty := .function .word .word
private def mapType : TypeSystem.Ty := .mapping .word .word
private def types : List TypeSystem.Ty := [.word, .integer, functionType, .proxy .word, mapType]
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 30 types).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 30 types).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [⟨[.unit]⟩]
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some ambient.definitions⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private theorem valid : ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, Context.ofSignatures],
    by intro requirement member; cases member⟩ }
private def binder (type : TypeSystem.Ty) : TypedBinder := ⟨⟨owner, 0⟩, "bound", .mono type, [], false, none⟩
private def pattern (type : TypeSystem.Ty) : TypedMatchPattern := {
  source := .group span (.binder span "bound"), type, resolution := .binder (binder type) }
private def fallback : SourceCoreCompatibleDataMatches.CertifiedPattern compilation.definitions := {
  pattern := ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
  typed := .lambda .unit (.sum .unit .unit) (.inRight .unit .unit) }
private def compiled (type : TypeSystem.Ty) : SourceCoreCompatibleDataMatches.CertifiedPattern compilation.definitions :=
  match SourceCoreCompatibleDataMatches.compilePattern compilation 10 source [] site span type (pattern type) with
  | .ok result => result | .error _ => fallback
private theorem functionAccepted : SourceCoreCompatibleDataMatches.compilePattern compilation 10 source [] site span
    functionType (pattern functionType) = .ok (compiled functionType) := by cbv
private theorem mappingAccepted : SourceCoreCompatibleDataMatches.compilePattern compilation 10 source [] site span
    mapType (pattern mapType) = .ok (compiled mapType) := by cbv
private theorem proxyAccepted : SourceCoreCompatibleDataMatches.compilePattern compilation 10 source [] site span
    (.proxy .word) (pattern (.proxy .word)) = .ok (compiled (.proxy .word)) := by cbv
private theorem wordAccepted : SourceCoreCompatibleDataMatches.compilePattern compilation 10 source [] site span
    .word (pattern .word) = .ok (compiled .word) := by cbv
private theorem sourceMatches (type : TypeSystem.Ty) (value : Dynamic.Value) :
    Dynamic.PatternMatches context (pattern type) value [(binder type, value)] :=
  .intro (.group (.binder rfl)) .binder

/-- The actual compiler receipt certifies its matcher in the extended ambient
world, rather than substituting the base catalog's typing judgment. -/
example : CompatiblePatternCertificates.Certificate compilation source [] site span functionType
    (pattern functionType) (compiled functionType).pattern :=
  CompatiblePatternCertificates.certificate_of_compilePattern compilation 10 source [] site span functionType
    (pattern functionType) (compiled functionType) functionAccepted

/-- Binding a function retains its complete native identity, descriptor and
capture payload. The function model is unchanged by the pure matcher. -/
example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Value} {native : Core.Value}
    (represented : ValueRep checked registry functions mapping world functionType function native
      (compiled functionType).pattern.type) (environment : Environment) (store : Store) :
    ∃ bound, BindingsRep checked registry functions mapping world (compiled functionType).pattern.bindings
      [(binder functionType, function)] bound ∧
      Evaluates (native :: environment) store (.apply (compiled functionType).pattern.matcher (.var 0))
        (.inRight .unit (DataPatternValues.packValues bound)) store :=
  compilePattern_leaf_success_preserves compilation 10 source [] site span functionType (pattern functionType)
    (compiled functionType) functionAccepted context valid (.binder _) represented (sourceMatches _ _) environment store

/-- Ordered mappings, including their exact raw header, duplicates and
transported default, are bound without decoding or re-encoding. -/
example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {sourceValue : Dynamic.Value} {native : Core.Value}
    (represented : ValueRep checked registry functions mapping world mapType sourceValue native
      (compiled mapType).pattern.type) (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep checked registry functions mapping world context (pattern mapType)
      (compiled mapType).pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (.apply (compiled mapType).pattern.matcher (.var 0)) (native :: environment) store) = .done outcome store) ∧
      (∀ fuel actual after, runStateful fuel
        (.initial (.apply (compiled mapType).pattern.matcher (.var 0)) (native :: environment) store) = .done actual after →
        actual = outcome ∧ after = store) :=
  compilePattern_leaf_run_preserves compilation 10 source [] site span mapType (pattern mapType)
    (compiled mapType) mappingAccepted context valid (.binder _) represented environment store

/-- Reflection starts with completed Core execution and reconstructs source
meaning for an opaque proxy carrier. Native typing is not raw authenticity. -/
example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {sourceValue : Dynamic.Value} {native outcome : Core.Value}
    (represented : ValueRep checked registry functions mapping world (.proxy .word) sourceValue native
      (compiled (.proxy .word)).pattern.type) {environment : Environment} {store after : Store}
    (completed : Evaluates (native :: environment) store
      (.apply (compiled (.proxy .word)).pattern.matcher (.var 0)) outcome after) :
    OutcomeRep checked registry functions mapping world context (pattern (.proxy .word))
      (compiled (.proxy .word)).pattern sourceValue outcome ∧ after = store :=
  compilePattern_leaf_reflects compilation 10 source [] site span (.proxy .word) (pattern (.proxy .word))
    (compiled (.proxy .word)) proxyAccepted context valid (.binder _) represented completed

private def noFunctions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem wordRep (word : Word) : ValueRep checked values.registry noFunctions [] []
    .word (.word word) (.word word) (compiled .word).pattern.type := by
  change ValueRep checked values.registry noFunctions [] [] .word (.word word) (.word word) .word
  exact .word word
example (word : Word) (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep checked values.registry noFunctions [] [] context (pattern .word)
      (compiled .word).pattern (.word word) outcome ∧
      Evaluates (.word word :: environment) store (.apply (compiled .word).pattern.matcher (.var 0)) outcome store :=
  compilePattern_leaf_preserves compilation 10 source [] site span .word (pattern .word) (compiled .word)
    wordAccepted context valid (.binder _) (wordRep word) environment store

/-- Exact retained metadata, including substitution order, follows from
independent runtime agreement only under authentic well-formed declarations. -/
example {left right : DataConstructorInstantiation} (catalogValid : SignatureCatalogWellFormed checked.signatures)
    (leftAuthentic : SourceCoreRawMetadata.constructorAuthentic checked.signatures left = true)
    (rightAuthentic : SourceCoreRawMetadata.constructorAuthentic checked.signatures right = true)
    (agrees : Dynamic.ConstructorInstantiationsAgree left right) : left = right :=
  CompatiblePatternMetadata.metadata_eq catalogValid leftAuthentic rightAuthentic agrees

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Tree { Leaf(Word), Pair(Tree, Tree) }",
    "enum Box<T> { Box(T) }",
    "function closure(marker: Word) returns (Word) { match (lam(x: Word) -> Word { marker = marker + x; return marker; }) { case f { let first: Word = f(2); return f(3); } } }",
    "function mapping(m: mapping(Word => Word)) returns (Word) { match (m) { case bound { return bound[7] + bound[9]; } } }",
    "function wildcard(m: mapping(Word => Word)) returns (Word) { match (m) { case _ { return 41; } } }",
    "function nested(tree: Tree) returns (Word) { match (tree) { case .Pair(.Leaf(left), .Leaf(0)) { return left; } case .Pair(.Leaf(left), .Leaf(right)) { return left + right; } default { return 99; } } }",
    "function numeric(value: Word) returns (Word) { match (value) { case 115792089237316195423570985008687907853269984665640564039457584007913129639936 { return 1; } case bound { return bound; } } }",
    "function failed(marker: Word) returns (Word) { match (marker) { case bound { marker = bound + 1; let absent: Word; return absent; } } }"]}] }

private def checkRawGuard (program : CheckedProgram) : IO Unit := do
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "Box signature missing")
  let boxType := TypeSystem.Ty.nominal box.id [.word]
  let stagedType := TypeSystem.Ty.nominal box.id [.comptime .word]
  let ordinary : DataConstructorInstantiation := ⟨⟨box.id, 0⟩, box.parameters.zip [.word], [.word], boxType⟩
  let staged : DataConstructorInstantiation := ⟨⟨box.id, 0⟩, box.parameters.zip [.comptime .word], [.comptime .word], stagedType⟩
  let checked ← SourceCompilerFeatureSupport.get "raw pattern catalog"
    (SourceCoreCompatibleCatalog.prepare program.signatures 100 [boxType, stagedType])
  let first ← SourceCompilerFeatureSupport.get "ordinary constructor input"
    (SourceCoreCompatibleValues.encode 100 (.initial checked) boxType (.constructed ordinary [.word (Word.ofNatModulo 7)]))
  let second ← SourceCompilerFeatureSupport.get "staged constructor input"
    (SourceCoreCompatibleValues.encode 100 first.context boxType (.constructed staged [.word (Word.ofNatModulo 7)]))
  let definitions := checked.catalog.definitions ++ [⟨[.unit]⟩]
  let compilation : SourceCoreCompatibleDataMatches.Context := ⟨second.context, [], none, some definitions⟩
  let sourcePattern : TypedMatchPattern := {
    source := .group span (.constructor span (some span) [] "Box" 1), type := boxType
    resolution := .constructor ordinary [.wildcard] }
  let compiled ← SourceCompilerFeatureSupport.get "actual compatible raw matcher"
    (SourceCoreCompatibleDataMatches.compilePattern compilation 20 source [] site span boxType sourcePattern)
  for (input, expected) in [(first.value, Core.Value.inRight .unit .unit),
      (second.value, .inLeft .unit .unit)] do
    let expression ← match SourceCoreCompatibleDataExpressions.quote input with
      | some expression => pure expression | none => throw (IO.userError "constructor was not quotable")
    let code := Core.Expr.apply compiled.pattern.matcher expression
    SourceCompilerFeatureSupport.require ((Core.Program.mk compiled.pattern.resultType code definitions).check)
      "actual ambient matcher failed native checking"
    let sentinel : Core.Store := [.integer 901, .cellRef .integer 0]
    match Core.runStateful 1000 (.initial code [] sentinel) with
    | .done actual after =>
      SourceCompilerFeatureSupport.require (actual == expected && after == sentinel)
        "raw constructor guard erased the staged instantiation or changed surrounding state"
    | _ => throw (IO.userError "raw constructor matcher failed to finish")
    for budget in [0, 2, 11] do
      match Core.runStateful budget (.initial code [] sentinel) with
      | .outOfFuel pending =>
        match Core.runStateful 1000 pending with
        | .done actual after =>
          SourceCompilerFeatureSupport.require (actual == expected && after == sentinel)
            "resumed raw constructor matcher changed outcome or state"
        | _ => throw (IO.userError "raw matcher checkpoint did not finish")
      | .done actual after =>
        SourceCompilerFeatureSupport.require (actual == expected && after == sentinel)
          "completed small-budget raw matcher changed outcome"
      | .fault _ _ => throw (IO.userError "raw matcher faulted")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "compatible pattern checker" (checkProgram workspace)
  checkRawGuard program
  let w := Word.ofNatModulo
  let mapping : SourceCoreExecution.Value := .mapping .word .word
    [(.word (w 7), .word (w 13)), (.word (w 7), .word (w 90)), (.word (w 9), .word (w 29))]
  -- The bound closure captures `marker = 10` by value; each call starts again
  -- from it, so `f(3)` returns 13.
  for (name, inputs, expected) in [
      ("closure", [.word (w 10)], (.word (w 13) : SourceCoreExecution.Value)),
      ("mapping", [mapping], .word (w 42)), ("wildcard", [mapping], .word (w 41)),
      ("numeric", [.word (w 0)], .word (w 1)), ("numeric", [.word (w 9)], .word (w 9))] do
    let entry ← SourceCompilerFeatureSupport.compileNamed program name
    SourceCompilerFeatureSupport.require ((← entry.run inputs) == expected) "compatible leaf matcher changed result"
    for budget in [0, 7, 47] do entry.checkResume inputs expected budget
  let tree ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some tree => pure tree | none => throw (IO.userError "Tree signature missing")
  let leafMetadata : DataConstructorInstantiation := ⟨⟨tree.id, 0⟩, [], [.word], .nominal tree.id []⟩
  let pairMetadata : DataConstructorInstantiation := ⟨⟨tree.id, 1⟩, [], [.nominal tree.id [], .nominal tree.id []], .nominal tree.id []⟩
  let leaf (value : Nat) : SourceCoreExecution.Value := .constructed leafMetadata [.word (w value)]
  let nested ← SourceCompilerFeatureSupport.compileNamed program "nested"
  for (argument, expected) in [(.constructed pairMetadata [leaf 11, leaf 0], (.word (w 11) : SourceCoreExecution.Value)),
      (.constructed pairMetadata [leaf 11, leaf 3], .word (w 14)), (leaf 8, .word (w 99))] do
    SourceCompilerFeatureSupport.require ((← nested.run [argument]) == expected) "nested compatible pattern changed ordered bindings"
    nested.checkResume [argument] expected
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  match (← failed.invoke [.word (w 7)]).outcome with
  | .failed _ _ => pure ()
  | _ => throw (IO.userError "selected pattern arm lost its source fault")
  IO.println "compatible patterns: general leaf preservation/reflection, ordered bindings and ambient raw guards GREEN"
end Tests.SourceCoreCompatiblePatternProofs
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleCompositePatterns
/-! Actual accepted nested tuple patterns bind whole function and mapping
carriers. Formal consumers preserve independent source binding order and
reflect completed Core alone, in an extended ambient nominal world. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace Tests.SourceCoreCompatibleCompositePatterns
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap DataPatternValues CompatiblePayload CompatiblePatternLeaves
open SourceCoreCompatibleDataMatches CompatiblePatternDecision
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_composite_patterns", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "compatible_composite_patterns.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def source : TypedSource := {owner, inputs := [], roots := [], nodes := []}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private theorem signatureValid : SignatureCatalogWellFormed signatures := by
  constructor <;> simp [signatures, signatureDeclarationIds]
private def functionType : TypeSystem.Ty := .function .word .word
private def mapType : TypeSystem.Ty := .mapping .word .word
private def tupleType : TypeSystem.Ty := .product (.comptime functionType) (.product (.proxy .word) mapType)
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 50 [tupleType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 50 [tupleType]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [⟨[.unit]⟩]
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some ambient.definitions⟩
private theorem valid : ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, Context.ofSignatures],
    by intro requirement member; cases member⟩ }
private def functionBinder : TypedBinder := ⟨⟨owner, 0⟩, "f", .mono (.comptime functionType), [], false, none⟩
private def mappingBinder : TypedBinder := ⟨⟨owner, 1⟩, "m", .mono mapType, [], false, none⟩
private def pattern : TypedMatchPattern := {
  source := .group span (.group span (.tuple span 2)), type := tupleType
  resolution := .tuple [.binder functionBinder, .tuple 2, .wildcard, .binder mappingBinder] }
private def fallback : CertifiedPattern compilation.definitions := {
  pattern := ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
  typed := .lambda .unit (.sum .unit .unit) (.inRight .unit .unit) }
private def compiled : CertifiedPattern compilation.definitions :=
  match compilePattern compilation 20 source [] site span tupleType pattern with
  | .ok result => result | .error _ => fallback
private theorem accepted : compilePattern compilation 20 source [] site span tupleType pattern = .ok compiled := by cbv
private theorem sourceMatches (function mappingValue : Dynamic.Value) :
    Dynamic.PatternMatches context pattern
      (.product function (.product (.proxy (.comptime .word)) mappingValue))
      [(functionBinder, function), (mappingBinder, mappingValue)] :=
  .intro (.group (.group .tuple))
    (.tuple (.cons (.singleton _)) rfl
      (.cons .binder (.cons (.tuple (.cons (.singleton _)) rfl (.cons .wildcard (.cons .binder .nil))) .nil)))

/-- Typed compiler receipts include both nested child trees, actual ambient
checking and the exact ordered binder pair. -/
example : CompatiblePatternCertificates.Certificate compilation source [] site span tupleType pattern compiled.pattern :=
  CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source [] site span tupleType pattern compiled accepted
example : compiled.pattern.bindings.map (·.1) = [functionBinder, mappingBinder] := by cbv

/-- Independent matching binds whole source functions and ordered mappings;
no child or matcher evaluation premise is present. -/
example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {function mappingValue : Dynamic.Value} {native : Core.Value}
    (extended : SourceCoreRawMetadata.Extends values.registry registry)
    (represented : ValueRep checked registry functions mapping world tupleType
      (.product function (.product (.proxy (.comptime .word)) mappingValue)) native compiled.pattern.type)
    (environment : Environment) (store : Store) :
    ∃ bound, BindingsRep checked registry functions mapping world compiled.pattern.bindings
      [(functionBinder, function), (mappingBinder, mappingValue)] bound ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (.apply compiled.pattern.matcher (.var 0)) (native :: environment) store) =
          .done (.inRight .unit (packValues bound)) store) ∧
      (∀ fuel actual after, runStateful fuel
        (.initial (.apply compiled.pattern.matcher (.var 0)) (native :: environment) store) = .done actual after →
        actual = .inRight .unit (packValues bound) ∧ after = store) :=
  CompatiblePatternSuccess.compilePattern_success_run compilation 20 source [] site span tupleType pattern compiled accepted
    context rfl signatureValid extended represented (sourceMatches _ _) environment store

/-- Core completion alone reconstructs independent matching or non-matching,
including all nested bindings, with exactly the surrounding state. -/
example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {sourceValue : Dynamic.Value} {native actual : Core.Value}
    (extended : SourceCoreRawMetadata.Extends values.registry registry)
    (represented : ValueRep checked registry functions mapping world tupleType sourceValue native compiled.pattern.type)
    {environment : Environment} {store after : Store}
    (completed : Evaluates (native :: environment) store (.apply compiled.pattern.matcher (.var 0)) actual after) :
    OutcomeRep checked registry functions mapping world context pattern compiled.pattern sourceValue actual ∧ after = store :=
  compilePattern_reflects compilation 20 source [] site span tupleType pattern compiled accepted context valid signatureValid
    extended represented completed

/-- Source runtime views decide tuple shape despite native function products.
A singleton unpack keeps the full native function carrier. -/
example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Value} {native : Core.Value} {type : Core.Ty}
    (represented : ValueRep checked registry functions mapping world functionType function native type) :
    ∃ sources natives types, ValuesRep checked registry functions mapping world [functionType] sources natives types ∧
      Dynamic.ValuesPack sources function ∧ native = packValues natives ∧ type = SourceCoreCompatibleCatalog.packTypes types :=
  CompatiblePatternValues.unpack (count := 1) rfl represented

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function nested(marker: Word, m: mapping(Word => Word)) returns (Word) { match ((lam(x: Word) -> Word { marker = marker + x; return marker; }, (0, m))) { case (f, (0, bound)) { let ignored: Word = f(bound[7]); return f(bound[9]); } default { return 99; } } }",
    "function miss(marker: Word, m: mapping(Word => Word)) returns (Word) { match ((lam(x: Word) -> Word { marker = marker + x; return marker; }, (1, m))) { case (f, (0, bound)) { return f(bound[7]); } default { return marker; } } }",
    "function constructed(marker: Word, m: mapping(Word => Word)) returns (Word) { match (Box((lam(x: Word) -> Word { marker = marker + x; return marker; }, m))) { case .Box((f, bound)) { let ignored: Word = f(bound[7]); return f(bound[9]); } } }"]}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "general composite pattern source"
    (checkProgram workspace)
  let w := Word.ofNatModulo
  let mapping : SourceCoreExecution.Value := .mapping .word .word
    [(.word (w 7), .word (w 13)), (.word (w 7), .word (w 900)), (.word (w 9), .word (w 29))]
  -- The bound closure captures `marker = 10` by value and each call starts
  -- again from it, so `f(bound[9])` returns 10 + 29.
  for (name, expected) in [("nested", 39), ("constructed", 39), ("miss", 10)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed program name
    let inputs : List SourceCoreExecution.Value := [.word (w 10), mapping]
    SourceCompilerFeatureSupport.require ((← entry.run inputs) == .word (w expected))
      "nested function/mapping matcher changed ordered bindings or by-value captures"
    for budget in [0, 7, 43] do entry.checkResume inputs (.word (w expected)) budget
  IO.println "compatible composite patterns: recursive typed receipts, general payloads, raw guards and finite source/Core correspondence GREEN"
end Tests.SourceCoreCompatibleCompositePatterns
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatiblePatternRuntime
/-! Actual composite matcher acceptance supplies every numeric leaf receipt.
The formal consumers preserve the full ledger and do not require ordinary
validity, Covers, source execution or preservation as a reflection input.
Retained-IR tests for repeated leaves and unused rows are labelled separately.
Whole ordered Match and Header/Profile integration are not claimed here. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatiblePatternRuntime
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatiblePatternLeaves
open SourceCoreCompatibleDataMatches
section Accepted
variable {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
  {fuel : Nat} {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
  {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : CertifiedPattern compilation.definitions}
  (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
  (signatures : context.signatures = compilation.signatures)
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context)
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  (extension : SourceCoreRawMetadata.Extends compilation.values.registry registry)
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
  {sourceValue : Dynamic.Value} {value : Core.Value} {world : StoreTyping}
  (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
include accepted signatures sameLedger runtime catalogValid extension represented

theorem accepted_preserves (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store :=
  CompatiblePatternRuntime.preserves
    (CompatiblePatternRuntime.of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)
    ⟨signatures, sameLedger, runtime⟩ catalogValid extension represented environment store

theorem accepted_reflects {environment : Environment} {store after : Store} {outcome : Core.Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome after) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧ after = store :=
  CompatiblePatternRuntime.reflects
    (CompatiblePatternRuntime.of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)
    ⟨signatures, sameLedger, runtime⟩ catalogValid extension represented completed
end Accepted

section ActualFrame
variable {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
  {types : List TypeSystem.Ty} (frame : NamedCalls.SourceFrame program instantiation body function)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (programTyped : ProgramWellFormed program)
  {compilation : SourceCoreCompatibleDataMatches.Context} {fuel : Nat} {scope : Scope}
  {site : StatementId} {span : Syntax.SourceSpan} {expected : TypeSystem.Ty}
  {pattern : TypedMatchPattern} {compiled : CertifiedPattern compilation.definitions}
  (accepted : compilePattern compilation fuel function.source scope site span expected pattern = .ok compiled)
  (signatures : context.signatures = compilation.signatures)
  (sameLedger : function.context.solvedRequirements = compilation.solvedRequirements)

  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  (extension : SourceCoreRawMetadata.Extends compilation.values.registry registry)
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
  {sourceValue : Dynamic.Value} {value : Core.Value} {world : StoreTyping}
  (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
include frame extended programTyped accepted signatures sameLedger catalogValid extension represented

theorem frame_preserves (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store :=
  accepted_preserves accepted signatures
    ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped) catalogValid extension represented environment store

theorem frame_reflects {environment : Environment} {store after : Store} {outcome : Core.Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome after) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧ after = store :=
  accepted_reflects accepted signatures
    ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped) catalogValid extension represented completed
end ActualFrame


section Boundaries
open CompatiblePatternCertificates CompatiblePatternDecision

/-- Both occurrences retain the same child proof when an instruction stream
repeats a numeric resolution; no set-like normalization is performed. -/
theorem repeated_sites {compilation : Compilation} {source : TypedSource} {site : StatementId}
    {span : Syntax.SourceSpan} {scope : Scope} {type : TypeSystem.Ty} {native : Core.Ty}
    {literal : Syntax.CoreLiteralValue} {numeric : IntegerLiteralResolution} {matcher : Core.Expr}
    (projection : projected compilation source type = .ok native)
    (validated : literalMatcher compilation site span type literal numeric = .ok matcher)
    :
    Forest.LiteralSites (fun numeric => ∃ implementation, NumericLiteralEvidenceReceipts.Selected compilation.solvedRequirements numeric implementation) (Forest.cons
      (Tree.literal (scope := scope) (rest := [.integerLiteral literal numeric]) projection validated)
      (Forest.cons (Tree.literal (scope := scope) (rest := []) projection validated) .nil)) := by
  intro resolution occurrence
  cases occurrence with
  | head first =>
    exact Tree.literalSites _ _
      (fun expected literal resolution matcher accepted =>
        CompatiblePatternLiteralRuntime.literalMatcher_selected compilation site span expected literal resolution matcher accepted) _ first
  | tail remaining =>
    cases remaining with
    | head first =>
      exact Tree.literalSites _ _
        (fun expected literal resolution matcher accepted =>
          CompatiblePatternLiteralRuntime.literalMatcher_selected compilation site span expected literal resolution matcher accepted) _ first
    | tail impossible => cases impossible

theorem empty_forest_sites {compilation : Compilation} {source : TypedSource} {site : StatementId}
    {span : Syntax.SourceSpan} {scope : Scope} (literals : IntegerLiteralResolution → Prop)
    (instructions : List MatchPatternInstruction) :
    Forest.LiteralSites literals (Forest.nil (compilation := compilation) (source := source)
      (site := site) (span := span) (scope := scope) (instructions := instructions)) := by
  intro resolution impossible
  cases impossible

/-- The factory retains the whole ledger and actual covering dictionary across
an independently typed match arm's binder context. -/
theorem scoped_runtime_fields {source : TypedSource} {parent child : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)}
    {request : GenericMatchChildren.Request} {solved : List SolvedRequirement}
    {evidence : Dynamic.EvidenceEnvironment}
    (related : GenericMatchChildren.ScopedContextFor source parent hiddenIds scrutineeType cases fallback request child)
    (valid : CompatibleRuntimeContextValidity.Valid solved parent evidence) :
    child.solvedRequirements = solved ∧ RuntimeRequirementLedgerValid child ∧ evidence.Covers child := by
  have result := CompatibleMatchContextFactory.scoped_runtime related valid
  exact ⟨result.ledger, result.runtime, result.covers⟩

end Boundaries

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def content : String := String.intercalate "\n" [
  "enum Tree { Leaf(Word), Pair(Tree, Tree) }",
  "enum Box<T> { Box(T) }",
  "function nested(tree: Tree) returns (Word) { match (tree) { case .Pair(.Leaf(37), .Leaf(bound)) { return bound; } case .Pair(.Leaf(left), .Leaf(right)) { return left + right; } default { return 99; } } }",
  "function tuple(a: Word, b: Word) returns (Word) { match ((a, b)) { case (37, 37) { return 11; } case (left, right) { return left + right; } } }",
  "function integerTuple(a: integer, b: Word) returns (Word) { match ((a, b)) { case (73, bound) { return bound; } default { return 17; } } }",
  "function faultTuple(a: Word, b: Word) returns (Word) { match ((a, b)) { case (37, bound) { a = bound; let missing: Word; return missing; } default { return 29; } } }"
]

private def auditPattern (compilation : SourceCoreCompatibleDataMatches.Context) (source : TypedSource)
    (site : StatementId) (span : Syntax.SourceSpan) (pattern : TypedMatchPattern)
    (inputs : List (Core.Value × Core.Value)) (names : List String) : IO Unit := do
  match accepted : compilePattern compilation 100 source [] site span pattern.type pattern with
  | .error error => throw (IO.userError s!"composite matcher rejected: {reprStr error}")
  | .ok compiled =>
    have receipt := CompatiblePatternRuntime.of_compilePattern compilation 100 source [] site span pattern.type pattern compiled accepted
    let _receipt := receipt
    require (compiled.pattern.requirements == pattern.requirements && compiled.pattern.bindings.map (·.1.name) == names)
      "composite matcher changed ordered requirements or binders"
    let code := Core.Expr.apply compiled.pattern.matcher (.var 0)
    require (Core.infer? [compiled.pattern.type] code compilation.definitions == some compiled.pattern.resultType)
      "composite matcher native typing failed"
    let sentinel : Core.Store := [.integer 901, .closure .unit .integer (.var 1) [.integer 777], .cellRef .integer 0]
    for (input, wanted) in inputs do
      for fuel in [0, 3, 19, 10000] do
        let result := match Core.runStateful fuel (.initial code [input] sentinel) with
          | .outOfFuel pending => Core.runStateful 10000 pending
          | other => other
        match result with
        | .done actual after =>
          require (actual == wanted && after == sentinel)
            "composite match/miss, ordered bindings, captured sentinel or full store changed"
        | other => throw (IO.userError s!"composite matcher did not finish: {reprStr other}")

/-- Retained metadata fixtures isolate raw constructor identity and the empty
ordered forest. They are accepted by the actual pattern compiler. -/
private def raw_and_empty (program : CheckedProgram) (source : TypedSource)
    (site : StatementId) (span : Syntax.SourceSpan) : IO Unit := do
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "Box signature missing")
  let boxType := TypeSystem.Ty.nominal box.id [.word]
  let stagedType := TypeSystem.Ty.nominal box.id [.comptime .word]
  let ordinary : DataConstructorInstantiation := ⟨⟨box.id, 0⟩, box.parameters.zip [.word], [.word], boxType⟩
  let staged : DataConstructorInstantiation := ⟨⟨box.id, 0⟩, box.parameters.zip [.comptime .word], [.comptime .word], stagedType⟩
  let checked ← get "composite raw guard catalog" (SourceCoreCompatibleCatalog.prepare program.signatures 100 [boxType, stagedType, .unit])
  let first ← get "composite ordinary raw constructor"
    (SourceCoreCompatibleValues.encode 100 (.initial checked) boxType (.constructed ordinary [.word (Word.ofNatModulo 7)]))
  let second ← get "composite staged raw constructor"
    (SourceCoreCompatibleValues.encode 100 first.context boxType (.constructed staged [.word (Word.ofNatModulo 7)]))
  let compilation : SourceCoreCompatibleDataMatches.Context := ⟨second.context, [], none, some (checked.catalog.definitions ++ [⟨[.unit]⟩])⟩
  let pattern : TypedMatchPattern := {
    source := .group span (.constructor span (some span) [] "Box" 1), type := boxType
    resolution := .constructor ordinary [.wildcard] }
  auditPattern compilation source site span pattern
    [(first.value, .inRight .unit .unit), (second.value, .inLeft .unit .unit)] []
  let empty : TypedMatchPattern := {source := .tuple span 0, type := .unit, resolution := .tuple []}
  auditPattern compilation source site span empty [(.unit, .inRight .unit .unit)] []

/-- A real checked specialization retains qualified local template rows. Only
the reached composite pattern is compiled; the complete lambda body is outside
this consumer's scope. -/
private def template_root : IO Unit := do
  let program ← get "composite template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " let f = lam(item) { return keep(item); }; let number: Word = 61;",
      " match ((number, number)) { case (61, 61) { return (f(1), f(flag)); } default { return (f(2), f(flag)); } } }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "composite template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "composite template function missing")
  let actual ← get "composite actual template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger.map (·.id) == generic.solvedRequirements.map (·.id))
    "composite template IDs or complete ordered ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !actual.assumptions.contains predicate)
          "composite template assumption was promoted"
      | _ => throw (IO.userError "composite template implementation fabricated")
    | _ => throw (IO.userError "composite template row missing or duplicated")
  let checked ← get "composite template catalog"
    (SourceCoreCompatibleCatalog.prepare program.signatures 100 [.word, .bool, .product .word .word])
  let compilation : SourceCoreCompatibleDataMatches.Context := ⟨.initial checked, ledger, none, none⟩
  let w := Word.ofNatModulo
  let mut count := 0
  for node in source.nodes do
    match node with
    | .statement statement => match statement.form with
      | .matchWith metadata =>
        for arm in metadata.cases do
          auditPattern compilation source statement.id arm.span arm.pattern
            [(.pair (.word (w 61)) (.word (w 61)), .inRight .unit .unit),
             (.pair (.word (w 62)) (.word (w 61)), .inLeft .unit .unit),
             (.pair (.word (w 61)) (.word (w 62)), .inLeft .unit .unit)] []
          count := count + 1
      | _ => pure ()
    | _ => pure ()
  require (count == 1) "composite template occurrence count changed"

private def inspect (artifact : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let w := Word.ofNatModulo
  let tree ← match artifact.sourceProgram.signatures.dataTypes.find? (·.name == "Tree") with
    | some tree => pure tree | none => throw (IO.userError "Tree signature missing")
  let treeType := TypeSystem.Ty.nominal tree.id []
  let leaf : DataConstructorInstantiation := ⟨⟨tree.id, 0⟩, [], [.word], treeType⟩
  let pair : DataConstructorInstantiation := ⟨⟨tree.id, 1⟩, [], [treeType, treeType], treeType⟩
  let leafValue (n : Nat) : SourceCoreCompatibleValues.Value := .constructed leaf [.word (w n)]
  let mut values := SourceCoreCompatibleValues.Context.initial artifact.compatible.checked
  let mut nativeTrees : List Core.Value := []
  for input in [(SourceCoreDataValues.Value.constructed pair [leafValue 37, leafValue 8]),
      .constructed pair [leafValue 2, leafValue 8], leafValue 7] do
    let encoded ← get "composite constructor input" (SourceCoreCompatibleValues.encode 100 values treeType input)
    values := encoded.context
    nativeTrees := nativeTrees ++ [encoded.value]
  let mut count := 0
  for named in artifact.indexed.base.functions do
    let actual ← get "composite full selected record"
      (SourceCompilationPlan.exactSpecialization artifact.indexed.base.plan named.signature.key)
    require (actual == named.specialized) "composite owner specialization changed"
    let signature ← match artifact.sourceProgram.signatures.functions.find? (·.id == actual.function.declaration) with
      | some signature => pure signature | none => throw (IO.userError "actual signature missing")
    let source := actual.function.typedBody
    let rows := actual.function.solvedRequirements
    for node in source.nodes do
      match node with
      | .statement statement => match statement.form with
        | .matchWith metadata =>
          for (arm, index) in metadata.cases.zipIdx do
            let compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, rows, none, none⟩
            let failure := Core.Value.inLeft (bundleType (← get "binding native types"
              ((match compilePattern compilation 100 source [] statement.id arm.span arm.pattern.type arm.pattern with
                | .ok compiled => .ok compiled.pattern.bindingTypes | .error error => .error error)))) .unit
            let (inputs, names) : List (Core.Value × Core.Value) × List String :=
              if signature.name == "nested" then
                if index == 0 then (nativeTrees.zip [.inRight .unit (.word (w 8)), failure, failure], ["bound"])
                else (nativeTrees.zip [.inRight .unit (.pair (.word (w 37)) (.word (w 8))),
                  .inRight .unit (.pair (.word (w 2)) (.word (w 8))), failure], ["left", "right"])
              else if signature.name == "tuple" then
                if index == 0 then ([(.pair (.word (w 37)) (.word (w 37)), .inRight .unit .unit),
                  (.pair (.word (w 1)) (.word (w 37)), failure), (.pair (.word (w 37)) (.word (w 2)), failure)], [])
                else ([(.pair (.word (w 4)) (.word (w 9)), .inRight .unit (.pair (.word (w 4)) (.word (w 9))))], ["left", "right"])
              else if signature.name == "integerTuple" then
                ([(.pair (.integer 73) (.word (w 8)), .inRight .unit (.word (w 8))),
                  (.pair (.integer 74) (.word (w 8)), failure)], ["bound"])
              else ([(.pair (.word (w 37)) (.word (w 8)), .inRight .unit (.word (w 8))),
                (.pair (.word (w 1)) (.word (w 8)), failure)], ["bound"])
            auditPattern compilation source statement.id arm.span arm.pattern inputs names
            let unusedId : RequirementId := ⟨(rows.map (·.id.index)).foldl max 0 + 1⟩
            let unusedGoal := ProgramSignatures.builtinIntPredicate .word
            let unused : SolvedRequirement := ⟨unusedId, unusedGoal, .assumption unusedGoal⟩
            for fullRows in [unused :: rows, rows ++ [unused]] do
              auditPattern {compilation with solvedRequirements := fullRows} source statement.id arm.span arm.pattern inputs names
            if signature.name == "tuple" && index == 0 then
              match arm.pattern.resolution with
              | .tuple [first@(.integerLiteral _ numeric), .integerLiteral _ _] =>
                let repeated := {arm.pattern with resolution := .tuple [first, first], requirements := [numeric.requirement, numeric.requirement]}
                auditPattern compilation source statement.id arm.span repeated inputs names
                let malformed := rows.map fun row => if row.id == numeric.requirement then
                  {row with evidence := .assumption row.predicate} else row
                require (compilePattern {compilation with solvedRequirements := malformed} 100 source [] statement.id arm.span repeated.type repeated).toOption.isNone
                  "composite matcher accepted a numeric assumption row"
              | _ => throw (IO.userError "tuple numeric instruction order changed")
            if count == 0 then raw_and_empty artifact.sourceProgram source statement.id arm.span
            count := count + 1
        | _ => pure ()
      | _ => pure ()
  require (count == 6) "composite matcher occurrence count changed"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"composite full ordered source heap changed: {reprStr state.heap}"

def run : IO Unit := do
  let artifact ← SourceCoreUnifiedCorpusSupport.prepare "composite runtime pattern receipts" content
    ["nested", "tuple", "integerTuple", "faultTuple"]
  inspect artifact
  template_root
  let w := Word.ofNatModulo
  let successes : List (String × List SourceTypedRuntime.Value × Nat × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("tuple", [.word (w 37), .word (w 37)], 11, [(.word, some (.word (w 37))), (.word, some (.word (w 37))),
      (.product .word .word, some (.product (.word (w 37)) (.word (w 37))))]),
    ("tuple", [.word (w 4), .word (w 9)], 13, [(.word, some (.word (w 4))), (.word, some (.word (w 9))),
      (.product .word .word, some (.product (.word (w 4)) (.word (w 9)))), (.word, some (.word (w 4))), (.word, some (.word (w 9)))]),
    ("integerTuple", [.integer 73, .word (w 8)], 8, [(.integer, some (.integer 73)), (.word, some (.word (w 8))),
      (.product .integer .word, some (.product (.integer 73) (.word (w 8)))), (.word, some (.word (w 8)))]),
    ("integerTuple", [.integer 74, .word (w 8)], 17, [(.integer, some (.integer 74)), (.word, some (.word (w 8))),
      (.product .integer .word, some (.product (.integer 74) (.word (w 8))))]),
    ("faultTuple", [.word (w 1), .word (w 8)], 29, [(.word, some (.word (w 1))), (.word, some (.word (w 8))),
      (.product .word .word, some (.product (.word (w 1)) (.word (w 8))))])]
  let missing ← match (artifact.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
    | [binder] => pure binder.id | _ => throw (IO.userError "composite missing binder identity lost")
  for fuel in [0, 37, 151, 300000] do
    for (name, inputs, result, heap) in successes do
      let first ← SourceCoreUnifiedCorpusSupport.execute artifact name inputs fuel
      let finished ← get "composite public resume" (first.resume 300000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr (SourceTypedRuntime.Value.word (w result))) "composite result changed"
        cells state heap
      | other => throw (IO.userError s!"composite success expected: {reprStr other}")
    let first ← SourceCoreUnifiedCorpusSupport.execute artifact "faultTuple" [.word (w 37), .word (w 8)] fuel
    let finished ← get "composite fault resume" (first.resume 300000)
    match finished.observation with
    | .fault (.uninitializedLocal actual) state =>
      require (actual == missing) "composite first fault identity changed"
      cells state [(.word, some (.word (w 8))), (.word, some (.word (w 8))),
        (.product .word .word, some (.product (.word (w 37)) (.word (w 8)))), (.word, some (.word (w 8))), (.word, none)]
    | other => throw (IO.userError s!"composite arm fault expected: {reprStr other}")
  IO.println "composite pattern actual numeric sites / nested and repeated order / early and late miss / full ledger and store / heap fault resume GREEN"

end Tests.SourceCoreCompatiblePatternRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleSelectedMatchPrefixes
/-! The independently selected compatible arm reaches an actual closure body
with exactly its real captured environment. Both finite directions preserve the
hidden/source binder allocations; no body evaluation is supplied by a caller. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleSelectedMatchPrefixes
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchSelectionPrefix CallableIndexedHistory

theorem selected_closure_body
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution (.function .unit .unit) internalReason
      expressionCertificate (fun _ _ code => code = LocalLoop.returnValue (.function .unit .unit) (LanguageResult.success (.lambda .unit .unit (.var 0)))) code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody (.arm statements bindings)) :
    ∃ hiddenHeap location selectedEnvironment selectedHeap selectedActual selectedStore selectedMap selectedWorld,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.BindersAllocate environment hiddenHeap (bindings.map Prod.fst) (bindings.map Prod.snd) selectedEnvironment selectedHeap ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions selectedMap selectedWorld selectedHeap selectedStore ∧
      AdministrativePreserved mapping store selectedMap selectedStore ∧
      Evaluates actual before (code.rename ξ)
        (LocalLoop.returnedValue (.closure .unit .unit (.var 0) selectedActual)) selectedStore ∧
      (∀ result finished, Evaluates actual before (code.rename ξ) result finished →
        result = LocalLoop.returnedValue (.closure .unit .unit (.var 0) selectedActual) ∧ finished = selectedStore) := by
  obtain ⟨hiddenHeap, location, finalScope, selectedEnvironment, selectedHeap, selectedCanonical, selectedActual,
      selectedStore, selectedMap, selectedWorld, selectedEmbedding, body,
      allocated, selected, selectedBody, finalEnvironments, finalHeaps, maps, worlds, preserved, finalLayout, agreement⟩ :=
    CompatibleMatchSelectedPrefix.Certificate.selected_prefix certificate ordinary onError allocator valid catalogValid
      definitions registered extended found uniqueExpression represented environments heaps agrees reference read unmapped evaluated selectedSource
  cases selectedBody with
  | arm identities bound certified =>
    subst body
    have child : Evaluates selectedActual selectedStore
        ((LocalLoop.returnValue (.function .unit .unit) (LanguageResult.success (.lambda .unit .unit (.var 0)))).rename selectedEmbedding)
        (LocalLoop.returnedValue (.closure .unit .unit (.var 0) selectedActual)) selectedStore := by
      simp only [LocalLoop.returnValue, LanguageResult.bind, LocalLoop.returned, LanguageResult.success, Expr.rename, Renaming.lift]
      exact .caseRight (.inRight .lambda) (.inRight (.inLeft (.inRight (.var rfl))))
    refine ⟨hiddenHeap, location, selectedEnvironment, selectedHeap, selectedActual, selectedStore, selectedMap, selectedWorld,
      allocated, bound, finalHeaps, preserved, agreement.wrap child, ?_⟩
    intro result finished completed
    exact evaluation_deterministic completed (agreement.wrap child)

end Tests.SourceCoreCompatibleSelectedMatchPrefixes
end
