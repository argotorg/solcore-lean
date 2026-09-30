import Solcore.SourceSemantics.CoreLowering.DataPlacePathHelpers

/-! A mixed mapping/member/mapping path. The actual preparation and checker
are used; source constructor metadata is authenticated independently. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreDataPlacePaths
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceMappingIndex DataEquality DataEqualityValues DataPatternValues
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"place_paths", by decide⟩], by decide⟩⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def keyId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "place_paths.solc"⟩, 0, 1⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def innerType : TypeSystem.Ty := .mapping .integer .integer
private def innerLayout : Core.OrderedMapping.Layout := ⟨.integer, .integer, ⟨0⟩⟩
private def outerLayout : Core.OrderedMapping.Layout := ⟨.integer, .namedData ⟨1⟩, ⟨2⟩⟩
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [innerType, .integer], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := innerType, definition := some innerLayout.definition },
  { sourceType := boxType, definition := some ⟨[.product innerLayout.type .integer]⟩, constructors := [⟨dataId, 0⟩] },
  { sourceType := .mapping .integer boxType, definition := some outerLayout.definition }]
}
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def metadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [innerType, .integer], boxType⟩
private def branch : MemberBranch := ⟨⟨⟨1⟩, 0⟩, [innerLayout.type, .integer]⟩
private def route : Route := ⟨.mapping .integer boxType, outerLayout.type, .integer,
  [.index outerLayout (keyId 0) boxType, .member ⟨1⟩ 0 [branch] innerLayout.type, .index innerLayout (keyId 1) .integer], some outerLayout⟩

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok value => rfl
private theorem comparisonExists : (SourceCoreDataEquality.prepare 20 checked .integer).toOption.isSome = true := by cbv
private def comparison := (SourceCoreDataEquality.prepare 20 checked .integer).toOption.get comparisonExists
private theorem comparisonGenerated : SourceCoreDataEquality.prepare 20 checked .integer = .ok comparison := except_get _ comparisonExists
private theorem scalarDefaultExists : (SourceCoreDefaultValue.prepare (TypeSystem.Ty.integer.size + 1) checked .integer).toOption.isSome = true := by decide
private def scalarDefault := (SourceCoreDefaultValue.prepare (TypeSystem.Ty.integer.size + 1) checked .integer).toOption.get scalarDefaultExists
private theorem scalarDefaultGenerated : SourceCoreDefaultValue.prepare (TypeSystem.Ty.integer.size + 1) checked .integer = .ok scalarDefault := except_get _ scalarDefaultExists
private theorem boxDefaultExists : (SourceCoreDefaultValue.prepare (boxType.size + 1) checked boxType).toOption.isSome = true := by decide
private def boxDefault := (SourceCoreDefaultValue.prepare (boxType.size + 1) checked boxType).toOption.get boxDefaultExists
private theorem boxDefaultGenerated : SourceCoreDefaultValue.prepare (boxType.size + 1) checked boxType = .ok boxDefault := except_get _ boxDefaultExists
private def innerIndex : PreparedIndex := ⟨innerLayout, keyId 1, 1, comparison.expression, scalarDefault.expression, Word.zero⟩
private def outerIndex : PreparedIndex := ⟨outerLayout, keyId 0, 0, comparison.expression, boxDefault.expression, Word.zero⟩
private def prepared : Prepared := ⟨route, [.index outerIndex, .member ⟨1⟩ 0 [branch] innerLayout.type, .index innerIndex],
  [(keyId 0, .integer), (keyId 1, .integer)], Word.zero⟩
private def innerCertificate : Index checked .integer innerIndex :=
  Index.of_generated comparisonGenerated scalarDefaultGenerated rfl rfl
private def outerCertificate : Index checked boxType outerIndex :=
  Index.of_generated comparisonGenerated boxDefaultGenerated rfl (by rfl)
private theorem accepted : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared := by
  have inner : checked.catalog.entries[0]? = some ⟨innerType, some innerLayout.definition, []⟩ := rfl
  have outer : checked.catalog.entries[2]? = some ⟨.mapping .integer boxType, some outerLayout.definition, []⟩ := rfl
  simp [prepare, route, innerLayout, outerLayout, inner, outer, innerType,
    comparisonGenerated, scalarDefaultGenerated, boxDefaultGenerated,
    prepared, innerIndex, outerIndex, bind, Except.bind, pure, Except.pure, Except.mapError]

private theorem noIdentities : IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem comparisonType : comparison.type = .integer := by
  have projection := comparison.projection
  rw [DataPlaceMappingPreparation.comparison_sourceType comparisonGenerated] at projection
  exact Except.ok.inj projection.symm
private abbrev IntegerRep := DataPatternTypedValues.TypedValueRep catalog signatures .integer
private abbrev Key := Observation catalog signatures (fun _ _ => False) .integer
private def innerSources (n : Int) : List (Dynamic.Value × Dynamic.Value) := [(.integer 7, .integer n), (.integer 7, .integer 22)]
private def innerEntries (n : Int) : Core.OrderedMapping.Entries := [(.integer 7, .integer n), (.integer 7, .integer 22)]
private def innerValue (n : Int) : Value := Core.OrderedMapping.encode innerLayout (innerEntries n)
private def boxSource (n : Int) : Dynamic.Value := .constructed metadata [.mapping .integer .integer (innerSources n), .integer 999]
private def boxValue (n : Int) : Value := .constructed ⟨⟨1⟩, 0⟩ (.pair (innerValue n) (.integer 999))
private inductive BoxRep : Dynamic.Value → Value → Prop where
  | intro (n : Int) : BoxRep (boxSource n) (boxValue n)
private def outerSources (n : Int) : List (Dynamic.Value × Dynamic.Value) := [(.integer 9, boxSource n)]
private def outerEntries (n : Int) : Core.OrderedMapping.Entries := [(.integer 9, boxValue n)]
private def outerSource (n : Int) : Dynamic.Value := .mapping .integer boxType (outerSources n)
private def outerValue (n : Int) : Value := Core.OrderedMapping.encode outerLayout (outerEntries n)
private def keys : List Value := [.integer 9, .integer 7]
private def projections : List Dynamic.EvaluatedProjection := [.index (.integer 9), .member "entries" 0, .index (.integer 7)]
private def innerStep : List PreparedStep := [.index innerIndex]
private def mixedSteps : List PreparedStep := [.index outerIndex, .member ⟨1⟩ 0 [branch] innerLayout.type, .index innerIndex]
private theorem innerKey (n : Int) : KeyRep innerCertificate signatures (fun _ _ => False) (.integer n) (.integer n) := by
  change Observation _ _ _ comparison.type _ _
  rw [comparisonType]; exact .integer n
private theorem outerKey (n : Int) : KeyRep outerCertificate signatures (fun _ _ => False) (.integer n) (.integer n) := by
  change Observation _ _ _ comparison.type _ _
  rw [comparisonType]; exact .integer n
private theorem innerRelated (n : Int) :
    OrderedMapping.EntriesRel (KeyRep innerCertificate signatures (fun _ _ => False)) IntegerRep (innerSources n) (innerEntries n) :=
  .cons (innerKey 7) (.integer n) (.cons (innerKey 7) (.integer 22) .nil)
private theorem outerRelated (n : Int) :
    OrderedMapping.EntriesRel (KeyRep outerCertificate signatures (fun _ _ => False)) BoxRep (outerSources n) (outerEntries n) :=
  .cons (outerKey 9) (.intro n) .nil
private theorem boxAuthenticated : checked.catalog.resolveConstructor signatures metadata = .ok ⟨⟨1⟩, 0⟩ := by cbv

private theorem readInner : DataPlaceReadTree.Tree checked signatures (fun _ _ => False) prepared keys IntegerRep
    (.mapping .integer .integer (innerSources 11)) (innerValue 11) innerStep [.index (.integer 7)] (.integer 11) 4 := by
  apply DataPlaceReadTree.Tree.mapping (count := 0) innerCertificate (innerKey 7) rfl (innerRelated 11) (.found (.head ⟨rfl, .integer 7⟩))
  intro value represented
  rcases represented with represented | ⟨_, tree⟩
  · exact .leaf represented
  · cases tree
private theorem readBox : DataPlaceReadTree.Tree checked signatures (fun _ _ => False) prepared keys IntegerRep
    (boxSource 11) (boxValue 11) (.member ⟨1⟩ 0 [branch] innerLayout.type :: innerStep)
    [.member "entries" 0, .index (.integer 7)] (.integer 11) 4 :=
  .member (branch := branch) (values := [innerValue 11, .integer 999])
    (sources := [.mapping .integer .integer (innerSources 11), .integer 999])
    boxAuthenticated rfl rfl rfl rfl rfl .head rfl readInner
private theorem readOuter : DataPlaceReadTree.Tree checked signatures (fun _ _ => False) prepared keys IntegerRep
    (outerSource 11) (outerValue 11) mixedSteps projections (.integer 11) 8 := by
  apply DataPlaceReadTree.Tree.mapping (count := 4) outerCertificate (outerKey 9) rfl (outerRelated 11) (.found (.head ⟨rfl, .integer 9⟩))
  intro value represented
  rcases represented with represented | ⟨_, tree⟩
  · cases represented; exact readBox
  · have impossible := tree.meaning.defaultable
    cases impossible

example : ∃ finalStore administrative,
    Dynamic.ProjectionsRead (some (outerSource 11)) projections (some (.integer 11)) ∧
    Evaluates [outerValue 11, packValues keys] [.integer 900]
      (select prepared mixedSteps (.var 0) (.var 1)) (.inRight .word (.inRight .unit (.integer 11))) finalStore ∧
    finalStore = [.integer 900] ++ administrative ∧ administrative.length = 8 := by
  obtain ⟨leaf, finalStore, administrative, sourceRead, represented, evaluated, extended, counted⟩ :=
    readOuter.preserves noIdentities rfl [outerValue 11, packValues keys] [.integer 900] (.var 0) (.var 1) (.var rfl) (.var rfl)
  cases represented
  exact ⟨finalStore, administrative, sourceRead, evaluated, extended, counted⟩

private theorem integerKey_cases {source : Dynamic.Value} {value : Value}
    (represented : KeyRep innerCertificate signatures (fun _ _ => False) source value) : Key source value := by
  change Observation _ _ _ comparison.type _ _ at represented
  rwa [comparisonType] at represented
private theorem innerUnique (n : Int) {value : Value}
    (represented : OrderedMapping.ValueRel innerLayout (KeyRep innerCertificate signatures (fun _ _ => False)) IntegerRep (innerSources n) value) :
    value = innerValue n := by
  obtain ⟨entries, related, rfl⟩ := represented
  cases related with
  | cons key first rest =>
    have key := integerKey_cases key
    cases key
    cases first
    cases rest with
    | cons key second tail =>
      have key := integerKey_cases key
      cases key
      cases second
      cases tail
      rfl
private abbrev InnerRep : OrderedMapping.Relation := fun source value =>
  ∃ n, source = .mapping .integer .integer (innerSources n) ∧ value = innerValue n

private theorem updateInner : DataPlaceUpdateTree.Tree checked signatures (fun _ _ => False) prepared keys
    (.integer 55) (.integer 55) InnerRep (.mapping .integer .integer (innerSources 11)) (innerValue 11)
    innerStep [.index (.integer 7)] (.mapping .integer .integer (innerSources 55)) 8 := by
  apply DataPlaceUpdateTree.Tree.mapping (count := 0) innerCertificate (innerKey 7) rfl (innerRelated 11) (.found (.head ⟨rfl, .integer 7⟩))
    (updatedChild := .integer 55)
  · intro value _; exact .leaf (.integer 55)
  · exact .update (.head ⟨rfl, .integer 7⟩)
  · intro value represented; exact ⟨55, rfl, innerUnique 55 represented⟩
private theorem updateBox : DataPlaceUpdateTree.Tree checked signatures (fun _ _ => False) prepared keys
    (.integer 55) (.integer 55) BoxRep (boxSource 11) (boxValue 11)
    (.member ⟨1⟩ 0 [branch] innerLayout.type :: innerStep) [.member "entries" 0, .index (.integer 7)] (boxSource 55) 8 := by
  apply DataPlaceUpdateTree.Tree.member (branch := branch) (values := [innerValue 11, .integer 999])
    (sources := [.mapping .integer .integer (innerSources 11), .integer 999]) boxAuthenticated rfl rfl rfl rfl rfl .head rfl updateInner
  intro child represented
  obtain ⟨n, same, rfl⟩ := represented
  have sameN : n = 55 := by cases same; rfl
  subst n
  exact .intro 55
private abbrev OuterRep : OrderedMapping.Relation := fun source value =>
  ∃ n, source = outerSource n ∧ value = outerValue n
private theorem updateOuter : DataPlaceUpdateTree.Tree checked signatures (fun _ _ => False) prepared keys
    (.integer 55) (.integer 55) OuterRep (outerSource 11) (outerValue 11) mixedSteps projections (outerSource 55) 16 := by
  apply DataPlaceUpdateTree.Tree.mapping (count := 8) outerCertificate (outerKey 9) rfl (outerRelated 11) (.found (.head ⟨rfl, .integer 9⟩))
    (updatedChild := boxSource 55)
  · intro value represented
    rcases represented with represented | ⟨_, tree⟩
    · cases represented; exact updateBox
    · have impossible := tree.meaning.defaultable; cases impossible
  · exact .update (.head ⟨rfl, .integer 9⟩)
  · intro value represented
    obtain ⟨entries, related, rfl⟩ := represented
    cases related with
    | cons key boxed tail =>
      change Observation _ _ _ comparison.type _ _ at key
      rw [comparisonType] at key
      cases key
      cases boxed
      cases tail
      exact ⟨55, rfl, rfl⟩

example : ∃ finalStore administrative,
    Dynamic.ProjectionsUpdate (fun _ value => value = .integer 55) (some (outerSource 11)) projections (outerSource 55) ∧
    Evaluates [outerValue 11, packValues keys, .integer 55] [.integer 900]
      (update prepared mixedSteps outerLayout.type (.var 0) (.var 1) (.var 2)) (.inRight .word (outerValue 55)) finalStore ∧
    finalStore = [.integer 900] ++ administrative ∧ administrative.length = 16 := by
  obtain ⟨value, finalStore, administrative, sourceUpdate, represented, evaluated, extended, counted⟩ :=
    updateOuter.preserves noIdentities rfl [outerValue 11, packValues keys, .integer 55] [.integer 900]
      outerLayout.type (.var 0) (.var 1) (.var 2) (.var rfl) (.var rfl) (.var rfl)
  obtain ⟨n, same, rfl⟩ := represented
  have sameN : n = 55 := by cases same; rfl
  subst n
  exact ⟨finalStore, administrative, sourceUpdate, evaluated, extended, counted⟩

example : ∃ finalStore administrative, administrative.length = 16 ∧ finalStore = [.integer 900] ++ administrative ∧
    ∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
      (.initial (.apply (setter prepared (.product .integer .integer)) (.var 0))
        [.pair (.inRight .unit (outerValue 11)) (.pair (packValues keys) (.integer 55))] [.integer 900]) =
      .done (.inRight .word (outerValue 55)) finalStore := by
  obtain ⟨value, finalStore, administrative, _, _, represented, evaluated, extended, counted⟩ :=
    DataPlacePathHelpers.setter_preserves (.initialized (.mapping .integer boxType) _ _) updateOuter rfl noIdentities rfl
      [.pair (.inRight .unit (outerValue 11)) (.pair (packValues keys) (.integer 55))] [.integer 900]
      (.product .integer .integer) (.var 0) (.var rfl)
  obtain ⟨n, same, rfl⟩ := represented
  have sameN : n = 55 := by cases same; rfl
  subst n
  exact ⟨finalStore, administrative, counted, extended, evaluation_runStateful_complete_with_sufficient_fuel evaluated⟩

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def checkRun (expression : Expr) (environment : Environment) (context : Core.Context) (initial : Store)
    (resultType : Core.Ty) (expected : Value) (expectedPrefix : Store) (allocated : Nat) : IO Unit := do
  assertTrue (infer? context expression catalog.definitions == some resultType) "mixed path code failed Core checker"
  let check := fun result => do
    match result with
    | .done value store =>
      assertTrue (value == expected) "mixed path returned wrong value or sibling contents"
      assertTrue (store.length == initial.length + allocated) "mixed path helper cell count differs"
      assertTrue (store.take expectedPrefix.length == expectedPrefix) "mixed path changed wrong store prefix"
    | other => throw (IO.userError s!"mixed path did not complete: {reprStr other}")
  let state := Core.State.initial expression environment initial
  check (runStateful 20000 state)
  match runStateful 19 state with
  | .outOfFuel checkpoint => check (runStateful 20000 checkpoint)
  | other => throw (IO.userError s!"mixed path expected checkpoint: {reprStr other}")
private def boxExpression (n sibling : Int) : Expr :=
  .construct ⟨⟨1⟩, 0⟩ (.pair
    (Core.OrderedMapping.cons innerLayout (.integer 7) (.integer n)
      (Core.OrderedMapping.cons innerLayout (.integer 7) (.integer 22) (Core.OrderedMapping.empty innerLayout)))
    (.integer sibling))
private def outerExpression (n sibling : Int) : Expr :=
  Core.OrderedMapping.cons outerLayout (.integer 9) (boxExpression n sibling) (Core.OrderedMapping.empty outerLayout)
private def latestValue (n sibling : Int) : Value :=
  Core.OrderedMapping.encode outerLayout [(.integer 9, .constructed ⟨⟨1⟩, 0⟩ (.pair (innerValue n) (.integer sibling)))]
private def event (digit value : Int) : Expr :=
  .letE (.storeCell (.var 1) (.binary .integerAdd (.binary .integerMul (.loadCell (.var 1)) (.integer 10)) (.integer digit)))
    (LanguageResult.success (.integer value))

def run : IO Unit := do
  let prepared ← match prepare checked 20 route Word.zero (fun _ => Word.zero) with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"mixed route preparation failed: {reprStr error}")
  let keyType : Core.Ty := .product .integer .integer
  let readArgument : Value := .pair (.inRight .unit (outerValue 11)) (packValues keys)
  checkRun (.apply (getter prepared keyType) (.var 0)) [readArgument]
    [.product (.sum .unit outerLayout.type) keyType] [.integer 900]
    (.sum .word (.sum .unit .integer)) (.inRight .word (.inRight .unit (.integer 11))) [.integer 900] 8
  let writeArgument : Value := .pair (.inRight .unit (outerValue 11)) (.pair (packValues keys) (.integer 55))
  checkRun (.apply (setter prepared keyType) (.var 0)) [writeArgument]
    [.product (.sum .unit outerLayout.type) (.product keyType .integer)] [.integer 900]
    (.sum .word outerLayout.type) (.inRight .word (outerValue 55)) [.integer 900] 16
  -- Events 1 and 2 are the two index evaluations. Event 3 is the RHS.
  -- The RHS changes both the selected value and a sibling in the latest root.
  let keyCode := SourceCoreCalls.packArguments [⟨.integer, event 1 9⟩, ⟨.integer, event 2 7⟩]
  let rhs := .letE (.storeCell (.var 0) (.inRight .unit (outerExpression 22 777))) ((event 3 5).weakenAt 0)
  let next := LanguageResult.success (.pair (.loadCell (.var 0)) (.loadCell (.var 1)))
  let outputType := .product (.sum .unit outerLayout.type) .integer
  let expression := execute prepared (.var 0) keyCode rhs next outputType (some .integerAdd) false Word.zero
  let initial : Store := [.inRight .unit (outerValue 11), .integer 0]
  let finalPrefix : Store := [.inRight .unit (latestValue 16 777), .integer 123]
  checkRun expression [.cellRef (.sum .unit outerLayout.type) 0, .cellRef .integer 1]
    [.cell (.sum .unit outerLayout.type), .cell .integer] initial (.sum .word outputType)
    (.inRight .word (.pair (.inRight .unit (latestValue 16 777)) (.integer 123))) finalPrefix 24
  IO.println "source Core mixed path certificates GREEN"

end Tests.SourceCoreDataPlacePaths
