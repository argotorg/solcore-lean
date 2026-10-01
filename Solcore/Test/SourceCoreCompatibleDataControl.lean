import Solcore.Frontend.SourceCoreCompatibleDataMatches
import Solcore.Frontend.ProgramChecking

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
