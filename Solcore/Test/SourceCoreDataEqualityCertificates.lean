import Solcore.SourceSemantics.CoreLowering.DataEqualityCertificates

/-! Consumers of automatic comparison-tree extraction, including recursive
nominal payloads, exact proxy identities and opaque mapping/function contents. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataEqualityCertificates
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataEquality DataEquality DataEqualityValues DataEqualityCertificates DataPatternTypedValues

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"equality_certificates", by decide⟩], by decide⟩⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def functionBoxId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "equality_certificates.solc"⟩, 0, 1⟩
private def treeType : TypeSystem.Ty := .nominal dataId []
private def functionBoxType : TypeSystem.Ty := .nominal functionBoxId []
private def constructorSource (name : String) : Syntax.EnumConstructor :=
  ⟨span, ⟨[], ⟨span, name⟩, none⟩⟩
private def signature : ProgramDataSignature := {
  id := dataId, name := "Tree", parameters := []
  constructors := [
    ⟨⟨dataId, 0⟩, "Leaf", [.integer], constructorSource "Leaf"⟩,
    ⟨⟨dataId, 1⟩, "Node", [treeType, treeType], constructorSource "Node"⟩]
  source := ⟨span, ⟨none, ⟨span, "Tree"⟩, none, span, []⟩⟩
}
private def functionBoxSignature : ProgramDataSignature := {
  id := functionBoxId, name := "FunctionBox", parameters := []
  constructors := [⟨⟨functionBoxId, 0⟩, "Box", [.function .unit .unit], constructorSource "Box"⟩]
  source := ⟨span, ⟨none, ⟨span, "FunctionBox"⟩, none, span, []⟩⟩
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature, functionBoxSignature], []⟩
private def layout : OrderedMapping.Layout := ⟨.word, .word, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := treeType, definition := some ⟨[.integer, .product (.namedData ⟨0⟩) (.namedData ⟨0⟩)]⟩
    constructors := [⟨dataId, 0⟩, ⟨dataId, 1⟩] },
  { sourceType := .mapping .word .word, definition := some layout.definition },
  { sourceType := .proxy (.comptime .integer), definition := some ⟨[.unit]⟩ },
  { sourceType := functionBoxType, definition := some ⟨[TaggedFunction.functionType .unit .unit]⟩
    constructors := [⟨functionBoxId, 0⟩] }]
}
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def leafMetadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [.integer], treeType⟩
private def nodeMetadata : DataConstructorInstantiation := ⟨⟨dataId, 1⟩, [], [treeType, treeType], treeType⟩
private def leafSource (n : Int) : Dynamic.Value := .constructed leafMetadata [.integer n]
private def leafValue (n : Int) : Value := .constructed ⟨⟨0⟩, 0⟩ (.integer n)
private def nodeSource (right : Int) : Dynamic.Value := .constructed nodeMetadata [leafSource 7, leafSource right]
private def nodeValue (right : Int) : Value := .constructed ⟨⟨0⟩, 1⟩ (.pair (leafValue 7) (leafValue right))
private theorem leafRepresented (n : Int) : TypedValueRep catalog signatures treeType (leafSource n) (leafValue n) :=
  .constructed (values := [.integer n]) (by rfl) rfl (by cbv) (.cons (.integer _) .nil)
private theorem nodeRepresented (n : Int) : TypedValueRep catalog signatures treeType (nodeSource n) (nodeValue n) :=
  .constructed (values := [leafValue 7, leafValue n]) (by rfl) rfl (by cbv)
    (.cons (leafRepresented _) (.cons (leafRepresented _) .nil))
private theorem leafComparable (n : Int) : Dynamic.ValueComparable (leafSource n) := by
  apply Dynamic.ValueComparable.constructed
  intro value member
  simp only [List.mem_singleton] at member
  subst value
  exact .integer n
private theorem nodeComparable (n : Int) : Dynamic.ValueComparable (nodeSource n) := by
  apply Dynamic.ValueComparable.constructed
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact leafComparable _
private theorem noIdentities : IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction

private def observation (prepared : Prepared checked) (left right : Value) : Core.State :=
  .initial (.letE prepared.expression (.apply (.var 0) (.pair (.var 1) (.var 2)))) [left, right] [.integer 900]
private def finalStore (prepared : Prepared checked) (left right : Value) : Store :=
  [.integer 900] ++ DataEqualityInstalled.cells
    (DataEqualityInstalled.allocatedEnvironment catalog 1 [left, right]) prepared.bodies

/-- The input relation authenticates every finite recursive payload. The
theorem derives actual initialization and all recursive calls itself. -/
example (prepared : Prepared checked) (sourceType : prepared.sourceType = treeType) (n : Int) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (observation prepared (nodeValue n) (nodeValue n)) =
        .done (.bool true) (finalStore prepared (nodeValue n) (nodeValue n)) := by
  have represented : TypedValueRep catalog signatures prepared.sourceType (nodeSource n) (nodeValue n) :=
    sourceType ▸ nodeRepresented n
  obtain ⟨result, meaning, evaluated⟩ := typed_compare_preserves prepared noIdentities represented represented
    [nodeValue n, nodeValue n] [.integer 900] (.var 0) (.var 1) (.var rfl) (.var rfl)
  have same : result = true := meaning.mpr ⟨rfl, nodeComparable n⟩
  subst result
  simpa [observation, finalStore, checked, Expr.weakenAt] using evaluation_runStateful_complete_with_sufficient_fuel evaluated

/-- Distinct constructors are rejected before their payloads are compared. -/
example (prepared : Prepared checked) (sourceType : prepared.sourceType = treeType) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (observation prepared (leafValue 7) (nodeValue 7)) =
        .done (.bool false) (finalStore prepared (leafValue 7) (nodeValue 7)) := by
  have left : TypedValueRep catalog signatures prepared.sourceType (leafSource 7) (leafValue 7) := sourceType ▸ leafRepresented 7
  have right : TypedValueRep catalog signatures prepared.sourceType (nodeSource 7) (nodeValue 7) := sourceType ▸ nodeRepresented 7
  obtain ⟨result, meaning, evaluated⟩ := typed_compare_preserves prepared noIdentities left right
    [leafValue 7, nodeValue 7] [.integer 900] (.var 0) (.var 1) (.var rfl) (.var rfl)
  have different : result = false := by
    cases result with
    | false => rfl
    | true => have impossible := (meaning.mp rfl).1; cases impossible
  subst result
  simpa [observation, finalStore, checked, Expr.weakenAt] using evaluation_runStateful_complete_with_sufficient_fuel evaluated

private def proxyValue : Value := .constructed ⟨⟨2⟩, 0⟩ .unit
private def mappingValue : Value := Core.OrderedMapping.encode layout [(Word.zero |> Value.word, .word Word.zero)]

/-- A mapping remains unequal to itself even though its carrier is a normal
Core list. A proxy retains the raw comptime wrapper in its source identity. -/
example (prepared : Prepared checked) (type : prepared.type = .product (.namedData ⟨2⟩) (.namedData ⟨1⟩)) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (observation prepared (.pair proxyValue mappingValue) (.pair proxyValue mappingValue)) =
        .done (.bool false) (finalStore prepared (.pair proxyValue mappingValue) (.pair proxyValue mappingValue)) := by
  have observed : Observation catalog signatures (fun _ _ => False) prepared.type
      (.product (.proxy (.comptime .integer)) (.mapping .word .word [(.word Word.zero, .word Word.zero)]))
      (.pair proxyValue mappingValue) := type ▸ .product (.proxy _ rfl rfl) (.mapping rfl rfl _ _ _ _)
  obtain ⟨result, meaning, evaluated⟩ := prepared_compare_preserves prepared noIdentities observed observed
    [.pair proxyValue mappingValue, .pair proxyValue mappingValue] [.integer 900]
    (.var 0) (.var 1) (.var rfl) (.var rfl)
  have different : result = false := by
    cases result with
    | false => rfl
    | true =>
      have impossible := (meaning.mp rfl).2
      cases impossible with
      | product _ mapping => cases mapping
  subst result
  simpa [observation, finalStore, checked, Expr.weakenAt] using evaluation_runStateful_complete_with_sufficient_fuel evaluated

private def oneIdentity (function : Dynamic.GlobalFunction) (source : Dynamic.Value) (identity : Word) : Prop :=
  source = .global function ∧ identity = Word.zero
private theorem oneFaithful (function : Dynamic.GlobalFunction) : IdentityFaithful (oneIdentity function) := by
  constructor
  · intro source identity represented
    rw [represented.1]; exact .global _
  · intro left right leftId rightId leftRep rightRep
    simp [leftRep.1, rightRep.1, leftRep.2, rightRep.2]

/-- Named-function identity does not execute either body, even when they have
different code or captures. The source identity includes its full evidence. -/
example (prepared : Prepared checked) (type : prepared.type = TaggedFunction.functionType .unit .unit)
    (function : Dynamic.GlobalFunction) (leftCode rightCode : Value) (store : Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (.letE prepared.expression (.apply (.var 0) (.pair (.var 1) (.var 2))))
        [.pair (.inRight .unit (.word Word.zero)) leftCode, .pair (.inRight .unit (.word Word.zero)) rightCode] store) =
      .done (.bool true) (store ++ DataEqualityInstalled.cells
        (DataEqualityInstalled.allocatedEnvironment catalog store.length
          [.pair (.inRight .unit (.word Word.zero)) leftCode, .pair (.inRight .unit (.word Word.zero)) rightCode]) prepared.bodies) := by
  have left : Observation catalog signatures (oneIdentity function) prepared.type (.global function)
      (.pair (.inRight .unit (.word Word.zero)) leftCode) := type ▸ .identified _ _ _ ⟨rfl, rfl⟩ rfl
  have right : Observation catalog signatures (oneIdentity function) prepared.type (.global function)
      (.pair (.inRight .unit (.word Word.zero)) rightCode) := type ▸ .identified _ _ _ ⟨rfl, rfl⟩ rfl
  obtain ⟨result, meaning, evaluated⟩ := prepared_compare_preserves prepared (oneFaithful function) left right
    [.pair (.inRight .unit (.word Word.zero)) leftCode, .pair (.inRight .unit (.word Word.zero)) rightCode]
    store (.var 0) (.var 1) (.var rfl) (.var rfl)
  have same : result = true := meaning.mpr ⟨rfl, .global _⟩
  subst result
  simpa [checked, Expr.weakenAt] using evaluation_runStateful_complete_with_sufficient_fuel evaluated

private def functionBoxMetadata : DataConstructorInstantiation :=
  ⟨⟨functionBoxId, 0⟩, [], [.function .unit .unit], functionBoxType⟩
private def anonymousBox (code : Value) : Value :=
  .constructed ⟨⟨3⟩, 0⟩ (.pair (.inLeft .word .unit) code)

/-- A nominal payload containing an anonymous closure is unequal to itself.
The nominal helper calls the generated function comparator without executing
the closure body or touching its captured cells. -/
example (prepared : Prepared checked) (type : prepared.type = .namedData ⟨3⟩)
    (function : Dynamic.Closure) (code : Value) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (observation prepared (anonymousBox code) (anonymousBox code)) =
        .done (.bool false) (finalStore prepared (anonymousBox code) (anonymousBox code)) := by
  have observed : Observation catalog signatures (fun _ _ => False) prepared.type
      (.constructed functionBoxMetadata [.closure function]) (anonymousBox code) := by
    rw [type]
    apply Observation.constructed (sources := [.closure function])
      (payloadType := TaggedFunction.functionType .unit .unit) (packed := .closure function)
    · rfl
    · rfl
    · rfl
    · cbv
    · rfl
    · rfl
    · exact .singleton _
    · exact .anonymous _ _ _ _ rfl
  obtain ⟨result, meaning, evaluated⟩ := prepared_compare_preserves prepared noIdentities observed observed
    [anonymousBox code, anonymousBox code] [.integer 900] (.var 0) (.var 1) (.var rfl) (.var rfl)
  have different : result = false := by
    cases result with
    | false => rfl
    | true =>
      have impossible := (meaning.mp rfl).2
      cases impossible with
      | constructed _ _ children => cases children (.closure function) (by simp)
  subst result
  simpa [observation, finalStore, checked, Expr.weakenAt] using evaluation_runStateful_complete_with_sufficient_fuel evaluated

end Tests.SourceCoreDataEqualityCertificates
