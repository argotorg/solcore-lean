import Solcore.SourceSemantics.CoreLowering.DataEqualityCertificates
import Solcore.SourceSemantics.CoreLowering.DataEqualityInitialization
import Solcore.SourceSemantics.CoreLowering.DataEquality
import Solcore.SourceSemantics.CoreLowering.DataDefaults
import Solcore.SourceSemantics.CoreLowering.DataEqualityScalarCertificates
import Solcore.SourceSemantics.CoreLowering.DataEqualityInstalled
import Solcore.Frontend.SourceCoreDefaultValue
import Solcore.SourceSemantics.CoreLowering.DataExpressionSequence
import Solcore.SourceSemantics.CoreLowering.Literals
import Solcore.Frontend.SourceCoreDataExpressions
import Solcore.Frontend.SourceCoreGeneralEntry
import Solcore.SourceSemantics.CoreLowering.DataMatchCertificates
import Solcore.SourceSemantics.CoreLowering.DataMatchSourceScopes
import Solcore.SourceSemantics.CoreLowering.DataPatternEncoding
import Solcore.SourceSemantics.CoreLowering.DataPatternParametricLeaves
import Solcore.SourceSemantics.CoreLowering.DataPatternDecision
import Solcore.Frontend.SourceCoreDataMatches
import Solcore.Frontend.SourceCoreLoops
import Solcore.SourceSemantics.CoreLowering.DataPayloadCatalog
import Solcore.SourceSemantics.CoreLowering.DataPayloadEncoding
import Solcore.SourceSemantics.CoreLowering.DataPayloadEquality
import Solcore.SourceSemantics.CoreLowering.GenericHeap
import Solcore.SourceSemantics.CoreLowering.DataPayloadFaultPaths
import Solcore.SourceSemantics.CoreLowering.DataPayloadMapping
import Solcore.SourceSemantics.CoreLowering.DataPayloadUpdatePaths
import Solcore.SourceSemantics.CoreLowering.DataPayloadWriteBack
import Solcore.SourceSemantics.CoreLowering.DataPlaceExecution

/-!
# Data value tests

Data equality, payloads, patterns and matches.

Native typing stays out of this file, in `Compatible/Expressions`: its import reaches the private `BEq`
of `SourceCoreCallablePrincipals`, which would win over the one the match tests use.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreDataEqualityCertificates
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataEqualityInitialization
/-! Equality initialization terminates independently of recursive comparison
bodies. The concrete comparison exercises those installed closures afterwards. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreDataEqualityInitialization
open Solcore Solcore.Frontend Solcore.SourceSemantics.CoreLowering
open SourceCoreDataEquality DataEqualityInitialization

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"equality_initialization", by decide⟩], by decide⟩⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def treeType : TypeSystem.Ty := .nominal dataId []
private def layout : Core.OrderedMapping.Layout := ⟨.word, .word, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := treeType
    definition := some ⟨[.unit, .integer, .product (.namedData ⟨0⟩) (.namedData ⟨0⟩)]⟩
    constructors := [⟨dataId, 0⟩, ⟨dataId, 1⟩, ⟨dataId, 2⟩] },
  { sourceType := .mapping .word .word, definition := some layout.definition, constructors := [] }]
}
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
example (prepared : Prepared checked) : Initializer prepared.expression := prepared_initializes prepared
example (prepared : Prepared checked) : allocations prepared.expression = 2 := prepared_allocation_count prepared

/-- Neither closure bodies nor assumptions of their termination are needed to
initialize real mutually referring cells under an existing typed store. -/
example (prepared : Prepared checked) : ∃ body captured finalStore finalWorld,
    Core.Evaluates [.integer 7] [.integer 900] prepared.expression
      (.closure (.product prepared.type prepared.type) .bool body captured) finalStore ∧
    Core.WorldExtends [.integer] finalWorld ∧
    Core.RuntimeStoreHasTypes finalWorld finalStore catalog.definitions ∧
    Core.RuntimeValueHasType finalWorld (.closure (.product prepared.type prepared.type) .bool body captured)
      (comparatorType prepared.type) catalog.definitions ∧ finalStore.length = 3 := by
  have environment : Core.RuntimeEnvironmentHasTypes [.integer] [.integer 7] [.integer] catalog.definitions :=
    .cons .integer .nil
  have store : Core.RuntimeStoreHasTypes [.integer] [.integer 900] catalog.definitions := {
    length_eq := rfl
    lookup := by
      intro location type found
      cases location with
      | zero => cases found; exact ⟨_, rfl, .integer⟩
      | succ location => simp at found
  }
  obtain ⟨body, captured, finalStore, finalWorld, evaluated, extension, storeTyped, valueTyped⟩ :=
    prepared_evaluates prepared environment store
  exact ⟨body, captured, finalStore, finalWorld, evaluated, extension, storeTyped, valueTyped,
    by simpa [checked, catalog] using prepared_evaluation_length prepared evaluated⟩

private def leaf (value : Int) : Core.Expr := .construct ⟨⟨0⟩, 1⟩ (.integer value)
private def tree (right : Int) : Core.Expr := .construct ⟨⟨0⟩, 2⟩ (.pair (leaf 7) (leaf right))
private def comparison (prepared : Prepared checked) (right : Int) : Core.Expr :=
  .apply prepared.expression (.pair (tree (-3)) (tree right))

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def checkResult (result : Core.StatefulRunResult) (expected : Bool) : IO Unit := do
  match result with
  | .done value store =>
    assertTrue (value == .bool expected) "recursive initialized comparison returned the wrong value"
    assertTrue (store.length == 3) "comparison reallocated or lost helper cells"
    assertTrue (store[0]? == some (.integer 900)) "helper initialization overwrote the preexisting store"
  | other => throw (IO.userError s!"initialized comparison did not finish: {reprStr other}")

/-- Recursive comparison uses installed helper references in real captured
environments; initialization has a typed proof above rather than a finite-fuel
assumption. Runtime checks also observe prefix preservation and resumption. -/
def run : IO Unit := do
  let prepared ← match prepare 20 checked treeType with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"recursive initializer rejected: {reprStr error}")
  for (right, expected) in [((-3 : Int), true), (8, false)] do
    let initial := Core.State.initial (comparison prepared right) [.integer 7] [.integer 900]
    checkResult (Core.runStateful 3000 initial) expected
    match Core.runStateful 10 initial with
    | .outOfFuel checkpoint => checkResult (Core.runStateful 3000 checkpoint) expected
    | other => throw (IO.userError s!"initialization did not expose the expected checkpoint: {reprStr other}")
  IO.println "source Core equality initialization GREEN"

end Tests.SourceCoreDataEqualityInitialization
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataEqualityProofs
/-! A recursive nominal comparison proof for every finite pair of unary
constructor trees, using the actual generated helper body and a shared cell.
The source constructors are explicit canonical metadata parameters. -/

set_option autoImplicit false

namespace Tests.SourceCoreDataEqualityProofs

open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics
open Solcore.SourceSemantics.CoreLowering.DataEquality

private def sourceType (declaration : Resolved.DeclarationId) : TypeSystem.Ty :=
  .constructor (.declaration declaration)
private def catalog (declaration : Resolved.DeclarationId) : SourceCoreDataCatalog.Catalog :=
  { entries := [{ sourceType := sourceType declaration, definition := some ⟨[.unit, .namedData ⟨0⟩]⟩ }] }
private def type : Core.Ty := .namedData ⟨0⟩
private def parameter : Core.Ty := .product type type
private def helper : Expr := .matchData ⟨0⟩ .bool (.first (.var 0)) [
  .matchData ⟨0⟩ .bool (.second (.var 1)) [.bool true, .bool false],
  .matchData ⟨0⟩ .bool (.second (.var 1)) [.bool false,
    SourceCoreDataEquality.invoke (.var 3) (.var 1) (.var 0)]]

example (declaration : Resolved.DeclarationId) :
    SourceCoreDataEquality.helperBody 8 (catalog declaration) ⟨0⟩ = .ok helper := by
  simp [SourceCoreDataEquality.helperBody, SourceCoreDataEquality.nominalBody,
    SourceCoreDataEquality.compareType, SourceCoreDataEquality.referenceIndex,
    catalog, sourceType, helper, List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure]

private def encode : Nat → Value
  | 0 => .constructed ⟨⟨0⟩, 0⟩ .unit
  | n + 1 => .constructed ⟨⟨0⟩, 1⟩ (encode n)
private def source (nil cons : DataConstructorInstantiation) : Nat → Dynamic.Value
  | 0 => .constructed nil []
  | n + 1 => .constructed cons [source nil cons n]
private def reference (location : Nat) : Value :=
  .cellRef (OptionalCell.cellType (SourceCoreDataEquality.comparatorType type)) location
private def closure (location : Nat) (captured : Environment) : Value :=
  .closure parameter .bool helper (reference location :: captured)
private def identities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : IdentityFaithful identities := {
  comparable := by intro _ _ impossible; cases impossible
  equal := by intro _ _ _ _ impossible; cases impossible
}

/-- Structural induction over the compared values traverses the shared
recursive helper. It neither unfolds an evaluator nor assumes its result. -/
private theorem comparison (nil cons : DataConstructorInstantiation) (distinct : nil ≠ cons)
    (store : Store) (location : Nat) (captured : Environment)
    (installed : store[location]? = some (.inRight .unit (closure location captured)))
    (left right : Nat) :
    Tree identities store (.pair (encode left) (encode right) :: reference location :: captured)
      helper (source nil cons left) (source nil cons right) (decide (left = right)) := by
  induction left generalizing right with
  | zero =>
    cases right with
    | zero =>
      simp only [source, encode, helper]
      exact Tree.nominalSame (right := .second (.var 0)) (rightBranches := [.bool true, .bool false]) nil
        (.first (.var rfl)) (.second (.var rfl)) (by simp [Expr.weakenAt]) rfl
        .nil .nil rfl .unit
    | succ right =>
      simp only [source, encode, helper]
      exact Tree.nominalDifferent (right := .second (.var 0)) (rightBranches := [.bool true, .bool false]) nil cons [] [source nil cons right] distinct
        (.first (.var rfl)) (.second (.var rfl)) (by simp [Expr.weakenAt]) rfl
  | succ left ih =>
    cases right with
    | zero =>
      simp only [source, encode, helper]
      exact Tree.nominalDifferent (right := .second (.var 0))
        (rightBranches := [.bool false, SourceCoreDataEquality.invoke (.var 3) (.var 1) (.var 0)]) cons nil [source nil cons left] [] (Ne.symm distinct)
        (.first (.var rfl)) (.second (.var rfl)) (by simp [Expr.weakenAt]) rfl
    | succ right =>
      simp only [source, encode, helper, Nat.succ.injEq]
      refine Tree.nominalSame (right := .second (.var 0))
        (rightBranches := [.bool false, SourceCoreDataEquality.invoke (.var 3) (.var 1) (.var 0)]) cons
        (.first (.var rfl)) (.second (.var rfl)) (by simp [Expr.weakenAt]) rfl
        (.singleton (source nil cons left)) (.singleton (source nil cons right)) rfl ?_
      exact Tree.invoke (.var rfl) (.var rfl) (.var rfl) installed (ih right)

/-- Arbitrary existing store contents and captured values are retained. The
helper remains pure after any append that preserves its installed location. -/
example (nil cons : DataConstructorInstantiation) (distinct : nil ≠ cons)
    (store : Store) (location : Nat) (captured : Environment)
    (installed : store[location]? = some (.inRight .unit (closure location captured)))
    (left right : Nat) :
    OrderedMapping.Compares ⟨type, .word, ⟨1⟩⟩ (closure location captured)
      (encode left) (encode right) (decide (left = right)) store ∧
    (decide (left = right) = true ↔
      Dynamic.ValueEquivalent (source nil cons left) (source nil cons right)) := by
  have tree := comparison nil cons distinct store location captured installed left right
  exact ⟨tree.compares _, tree.meaning faithful⟩

/-- Authentic generator output and the recursive value certificate yield a
finite run for every finite pair, with the exact unchanged store. -/
example (declaration : Resolved.DeclarationId)
    (nil cons : DataConstructorInstantiation) (distinct : nil ≠ cons)
    (store : Store) (location : Nat) (captured : Environment)
    (installed : store[location]? = some (.inRight .unit (closure location captured)))
    (left right : Nat) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (State.initial
        (SourceCoreDataEquality.invoke (.var 1) (.first (.var 0)) (.second (.var 0)))
        (.pair (encode left) (encode right) :: reference location :: captured) store) =
      .done (.bool (decide (left = right))) store := by
  have compiled : SourceCoreDataEquality.compareType 8 (catalog declaration) 1 type
      (.first (.var 0)) (.second (.var 0)) =
      .ok (SourceCoreDataEquality.invoke (.var 1) (.first (.var 0)) (.second (.var 0))) := by
    simp [SourceCoreDataEquality.compareType, SourceCoreDataEquality.referenceIndex, catalog, sourceType, type]
  exact (compareType_run_preserves faithful compiled
    (Tree.invoke (.var rfl) (.first (.var rfl)) (.second (.var rfl)) installed
      (comparison nil cons distinct store location captured installed left right))).2

example (environment : Environment) (store : Store) :
    ∃ source value required,
      CoreLowering.DataDefaults.Tree {} (.product .integer .bool) source value
        (.pair (.integer 0) (.bool false)) ∧
      Dynamic.DefaultValue (.product .integer .bool) source ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial (.pair (.integer 0) (.bool false)) environment store) =
          .done value store :=
  CoreLowering.DataDefaults.defaultExpression_run_preserves 3 {} (.product .integer .bool)
    _ rfl environment store

end Tests.SourceCoreDataEqualityProofs
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataEqualityScalarProofs
/-! Proof consumers join real initialization and actual scalar/product
comparison compilation to independent source equality. The catalog may contain
unrelated recursive helpers; comparison performs no extra allocations. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataEqualityScalarProofs
open Solcore Solcore.Core Solcore.Frontend Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataEquality DataEquality DataEqualityScalarCertificates DataPatternValues

private theorem noIdentities : IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction

private def leftSource : Dynamic.Value := .product (.bool true) (.integer (-9))
private def leftValue : Core.Value := .pair (.bool true) (.integer (-9))
private def rightSource : Dynamic.Value := .product (.bool false) (.integer (-9))
private def rightValue : Core.Value := .pair (.bool false) (.integer (-9))

example (checked : SourceCoreDataCatalog.Checked) (prepared : Prepared checked)
    (type : prepared.type = .product .bool .integer) (store : Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial
        (.letE prepared.expression (.apply (.var 0) (.pair (.var 1) (.var 2))))
        [leftValue, rightValue] store) =
        .done (.bool false) (store ++ DataEqualityInstalled.cells
          (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length [leftValue, rightValue]) prepared.bodies) := by
  have profile : ScalarType prepared.type := type ▸ (.product .bool .integer)
  have leftTyped : ValueHasType leftValue prepared.type checked.catalog.definitions := type ▸ (.pair .bool .integer)
  have rightTyped : ValueHasType rightValue prepared.type checked.catalog.definitions := type ▸ (.pair .bool .integer)
  obtain ⟨result, meaning, evaluates⟩ := prepared_compare_preserves prepared profile noIdentities
    (sourceLeft := leftSource) (sourceRight := rightSource)
    (.product (.bool _) (.integer _)) (.product (.bool _) (.integer _)) leftTyped rightTyped
    [leftValue, rightValue] store (.var 0) (.var 1) (.var rfl) (.var rfl)
  have falseResult : result = false := by
    cases result with
    | false => rfl
    | true => have impossible := (meaning.mp rfl).1; cases impossible
  subst result
  simpa [Expr.weakenAt] using evaluation_runStateful_complete_with_sufficient_fuel evaluates

example (checked : SourceCoreDataCatalog.Checked) (prepared : Prepared checked)
    (type : prepared.type = .product .bool .integer) (store : Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial
        (.letE prepared.expression (.apply (.var 0) (.pair (.var 1) (.var 1))))
        [leftValue] store) =
        .done (.bool true) (store ++ DataEqualityInstalled.cells
          (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length [leftValue]) prepared.bodies) := by
  have profile : ScalarType prepared.type := type ▸ (.product .bool .integer)
  have typed : ValueHasType leftValue prepared.type checked.catalog.definitions := type ▸ (.pair .bool .integer)
  obtain ⟨result, meaning, evaluates⟩ := prepared_compare_preserves prepared profile noIdentities
    (sourceLeft := leftSource) (sourceRight := leftSource)
    (.product (.bool _) (.integer _)) (.product (.bool _) (.integer _)) typed typed
    [leftValue] store (.var 0) (.var 0) (.var rfl) (.var rfl)
  have trueResult : result = true := meaning.mpr ⟨rfl, .product (.bool _) (.integer _)⟩
  subst result
  simpa [Expr.weakenAt] using evaluation_runStateful_complete_with_sufficient_fuel evaluates

end Tests.SourceCoreDataEqualityScalarProofs
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataEqualityStoreProofs
/-! The caller deliberately supplies a reference to an old heap cell. The
closed initializer still appends helper cells without modifying that old cell. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataEqualityStoreProofs
open Solcore Solcore.Core Solcore.Frontend Solcore.SourceSemantics.CoreLowering
open SourceCoreDataEquality DataEqualityInitializationStore

example (checked : SourceCoreDataCatalog.Checked) (prepared : Prepared checked) :
    ∃ body captured administrative required,
      administrative.length = checked.catalog.entries.length ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (.initial prepared.expression [.cellRef .integer 0] [.integer 900]) =
          .done (.closure (.product prepared.type prepared.type) .bool body captured) (.integer 900 :: administrative) := by
  have environment : RuntimeEnvironmentHasTypes [.integer] [.cellRef .integer 0] [.cell .integer] checked.catalog.definitions :=
    .cons (.cellRef rfl) .nil
  have store : RuntimeStoreHasTypes [.integer] [.integer 900] checked.catalog.definitions := {
    length_eq := rfl
    lookup := by
      intro location type found
      cases location with
      | zero => cases found; exact ⟨_, rfl, .integer⟩
      | succ location => simp at found
  }
  obtain ⟨body, captured, administrative, _, length, _, _, _, ⟨required, runs⟩, _⟩ :=
    prepared_run_extends prepared environment store
  exact ⟨body, captured, administrative, required, length, runs⟩

/-- A completed preparation authenticates exact code/capture contents, not
just function tags. The first helper captures no installation Unit binder. -/
example (checked : SourceCoreDataCatalog.Checked) (prepared : Prepared checked)
    (firstBody : Expr) (first : prepared.bodies[0]? = some firstBody)
    (fuel : Nat) (value : Value) (finalStore : Store)
    (ran : runStateful fuel (.initial prepared.expression [.cellRef .integer 0] [.integer 900]) = .done value finalStore) :
    finalStore.read? 1 = some (.inRight .unit
      (DataEqualityInstalled.helper (DataEqualityInstalled.allocatedEnvironment checked.catalog 1 [.cellRef .integer 0]) firstBody 0)) := by
  obtain ⟨_, _, installed⟩ := DataEqualityInstalled.prepared_completed_installed prepared ran
  exact installed 0 firstBody first

/-- Later closures retain both their shifted bodies and previous write-result
binders; exact initialization does not collapse these captures to one template. -/
example (checked : SourceCoreDataCatalog.Checked) (prepared : Prepared checked)
    (secondBody : Expr) (second : prepared.bodies[1]? = some secondBody)
    (fuel : Nat) (value : Value) (finalStore : Store)
    (ran : runStateful fuel (.initial prepared.expression [] []) = .done value finalStore) :
    finalStore.read? 1 = some (.inRight .unit
      (.closure (.product (.namedData ⟨1⟩) (.namedData ⟨1⟩)) .bool
        (secondBody.rename (DataEqualityInstalled.offset 1).lift)
        (.unit :: DataEqualityInstalled.allocatedEnvironment checked.catalog 0 []))) := by
  obtain ⟨_, _, installed⟩ := DataEqualityInstalled.prepared_completed_installed prepared ran
  simpa [DataEqualityInstalled.helper, DataEqualityInstalled.captured] using installed 1 secondBody second

end Tests.SourceCoreDataEqualityStoreProofs
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataEquality
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCoreDataEquality

open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
    "function identity(value: Word) returns (Word) { return value; }"
  ] }]
}

private def prepared (checked : SourceCoreDataCatalog.Checked) (type : TypeSystem.Ty) :
    IO (SourceCoreDataEquality.Prepared checked) :=
  match SourceCoreDataEquality.prepare 128 checked type with
  | .ok comparator => pure comparator
  | .error error => throw (IO.userError s!"comparison compilation rejected {reprStr error}")

private def runProgram (definitions : DataEnvironment) (type : Core.Ty) (expression : Expr)
    (expected : Value) (cells : Nat) : IO Unit := do
  let program : Program := ⟨type, expression, definitions⟩
  assertTrue program.check "generated comparison/default failed Core.check"
  match program.runStateful 100000 with
  | .done value store =>
    assertTrue (value == expected) s!"comparison/default mismatch: {reprStr value}"
    assertTrue (store.length == cells) "comparison allocated cells during invocation"
  | result => throw (IO.userError s!"comparison/default did not complete: {reprStr result}")

private def assertComparison (checked : SourceCoreDataCatalog.Checked) (type : TypeSystem.Ty)
    (left right : Expr) (expected : Bool) : IO Unit := do
  let comparator ← prepared checked type
  runProgram checked.catalog.definitions .bool
    (.apply comparator.expression (.pair left right)) (.bool expected) checked.catalog.entries.length
  -- The same prepared comparator is invoked twice; installation is not repeated.
  runProgram checked.catalog.definitions (.product .bool .bool)
    (.letE comparator.expression (.pair
      (.apply (.var 0) (.pair left right)) (.apply (.var 0) (.pair right left))))
    (.pair (.bool expected) (.bool expected)) checked.catalog.entries.length

private def leaf (id : DataTypeId) (value : Int) : Expr := .construct ⟨id, 0⟩ (.integer value)
private def pair (id : DataTypeId) (left right : Expr) : Expr := .construct ⟨id, 1⟩ (.pair left right)
private def tree (id : DataTypeId) : Nat → Expr
  | 0 => leaf id (-10)
  | n + 1 => pair id (leaf id (Int.ofNat n)) (tree id n)

private def rawFunction : Expr :=
  .lambda .word (LanguageResult.resultType .word) (LanguageResult.success (.var 0))

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"data equality fixture rejected {reprStr errors}")
  let signature ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some signature => pure signature
    | none => throw (IO.userError "missing Tree")
  let treeType := TypeSystem.Ty.nominal signature.id [.integer]
  let mapType := TypeSystem.Ty.mapping treeType .word
  let functionType := TypeSystem.Ty.function .word .word
  let functionTree := TypeSystem.Ty.nominal signature.id [functionType]
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 128
      [treeType, functionTree, mapType, .proxy .word, .proxy (.comptime .word), .mapping .word .word] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"data catalog rejected {reprStr error}")
  let id ← match checked.catalog.identity? treeType with
    | some id => pure id
    | none => throw (IO.userError "tree identity missing")
  assertComparison checked .unit .unit .unit true
  assertComparison checked .bool (.bool false) (.bool true) false
  assertComparison checked .bool (.bool true) (.bool true) true
  assertComparison checked .integer (.integer (-(2 ^ 300))) (.integer (-(2 ^ 300))) true
  assertComparison checked (.product .word .integer)
    (.pair (.word Word.zero) (.integer 8)) (.pair (.word Word.zero) (.integer 9)) false
  assertComparison checked treeType (tree id 12) (tree id 12) true
  assertComparison checked treeType (tree id 12) (tree id 11) false
  assertComparison checked treeType (leaf id 1) (pair id (leaf id 1) (leaf id 1)) false
  assertComparison checked treeType (leaf id 1) (leaf id 2) false
  assertComparison checked functionType (TaggedFunction.anonymous rawFunction) (TaggedFunction.anonymous rawFunction) false
  assertComparison checked functionType (TaggedFunction.identified Word.zero rawFunction)
    (TaggedFunction.identified Word.zero rawFunction) true
  assertComparison checked functionType (TaggedFunction.identified Word.zero rawFunction)
    (TaggedFunction.identified (Word.ofNatModulo 1) rawFunction) false
  assertComparison checked functionType (TaggedFunction.anonymous rawFunction)
    (TaggedFunction.identified Word.zero rawFunction) false
  assertComparison checked functionType (TaggedFunction.identified Word.zero rawFunction)
    (TaggedFunction.anonymous rawFunction) false
  -- Even a body that allocates when invoked is never invoked by equality.
  let effectfulCode := Expr.lambda .word (LanguageResult.resultType .word)
    (.letE (.newCell .word (.var 0)) (LanguageResult.success (.loadCell (.var 0))))
  assertComparison checked functionType (TaggedFunction.identified Word.zero effectfulCode)
    (TaggedFunction.identified Word.zero rawFunction) true
  let functionTreeId := (checked.catalog.identity? functionTree).getD ⟨0⟩
  assertComparison checked functionTree
    (.construct ⟨functionTreeId, 0⟩ (TaggedFunction.anonymous rawFunction))
    (.construct ⟨functionTreeId, 0⟩ (TaggedFunction.anonymous rawFunction)) false
  assertComparison checked functionTree
    (.construct ⟨functionTreeId, 0⟩ (TaggedFunction.identified Word.zero rawFunction))
    (.construct ⟨functionTreeId, 0⟩ (TaggedFunction.identified Word.zero effectfulCode)) true
  let proxyId := (checked.catalog.identity? (.proxy .word)).getD ⟨0⟩
  assertTrue (checked.catalog.identity? (.proxy .word) != checked.catalog.identity? (.proxy (.comptime .word)))
    "exact proxy staging identity collapsed"
  assertComparison checked (.proxy .word) (.construct ⟨proxyId, 0⟩ .unit) (.construct ⟨proxyId, 0⟩ .unit) true
  let mapId := (checked.catalog.identity? mapType).getD ⟨0⟩
  let mapping : Expr := .construct ⟨mapId, 0⟩ .unit
  assertComparison checked mapType mapping mapping false
  assertComparison checked (.product .unit mapType) (.pair .unit mapping) (.pair .unit mapping) false

  let comparator ← prepared checked treeType
  let layout : OrderedMapping.Layout := ⟨.namedData id, .word, mapId⟩
  let entries := OrderedMapping.cons layout (tree id 3) (.word Word.zero)
    (OrderedMapping.cons layout (tree id 2) (.word (Word.ofNatModulo 4)) (OrderedMapping.empty layout))
  let insert := OrderedMapping.insert layout (.var 0) entries (tree id 3) (.word (Word.ofNatModulo 6))
  let expected : Expr := OrderedMapping.cons layout (tree id 3) (.word (Word.ofNatModulo 6))
    (OrderedMapping.cons layout (tree id 2) (.word (Word.ofNatModulo 4)) (OrderedMapping.empty layout))
  let expectedValue ← match (Program.mk layout.type expected checked.catalog.definitions).runStateful 100000 with
    | .done value _ => pure value
    | _ => throw (IO.userError "expected mapping construction failed")
  runProgram checked.catalog.definitions (LanguageResult.resultType layout.type)
    (.letE comparator.expression insert) (.inRight .word expectedValue) (checked.catalog.entries.length + 1)

  for (type, present) in [(TypeSystem.Ty.unit, true), (.integer, true),
      (.product .bool (.proxy .word), true), (mapType, true), (functionType, false), (treeType, false)] do
    let default ← match SourceCoreDefaultValue.prepare 128 checked type with
      | .ok default => pure default
      | .error error => throw (IO.userError s!"default rejected {reprStr error}")
    let result := (Program.mk (.sum .unit default.type) default.expression checked.catalog.definitions).runStateful 1000
    match result with
    | .done (.inRight .unit _) [] => assertTrue present "unexpected present default"
    | .done (.inLeft _ .unit) [] => assertTrue (!present) "unexpected absent default"
    | _ => throw (IO.userError s!"default execution shape changed: {reprStr result}")
  IO.println "source Core data equality/default GREEN"

end Tests.SourceCoreDataEquality
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataExpressionSequence
/-! The universal vector reflection theorem is instantiated by an actual
Boolean leaf compiler certificate. Separate machine checks exercise mutation
order, first-fault short circuit and a closure captured under temporary slots. -/

set_option autoImplicit false
set_option maxRecDepth 4096
namespace Tests.SourceCoreDataExpressionSequence
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GenericExpressionMeaning DataExpressionSequence GeneralHeap

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"expression_sequence", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "expression_sequence.solc" }
  startByte := 0
  endByte := 1 }
private def node (index : Nat) (value : Bool) : ExpressionNode := {
  id := id index, span, type := .bool, form := .reference "boolean" (.builtinBoolean value) }
private def source : TypedSource := {
  owner
  inputs := []
  roots := [.expression (id 0), .expression (id 1), .expression (id 2)]
  nodes := [.expression (node 0 true), .expression (node 1 false), .expression (node 2 true)] }
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def model := GenericHeap.finitePayload catalog signatures
private def context : SourceSemantics.Context := .ofSignatures signatures
private def code (value : Bool) : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool value)⟩

private inductive Child : Certificate where
  | boolean {scope expression node name value}
      (found : source.lookupExpression? expression = some node)
      (form : node.form = .reference name (.builtinBoolean value))
      (type : node.type = .bool) (requirements : node.requirements = []) (coercions : node.coercions = []) :
      Child scope expression (code value)

private theorem unique : NodeOccurrencesUnique source := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source, node, Node.occurrenceId, Node.id, NodeId.occurrenceId, id]

private theorem same_node {expression : ExpressionId} {left right : ExpressionNode}
    (found : source.lookupExpression? expression = some left) (contained : ContainsExpression source expression right) :
    right = left := Option.some.inj ((lookupExpression?_complete unique contained).symm.trans found)

private theorem boolean_no_fault {program : SourceSemantics.Program} {expression : ExpressionId}
    {selected : ExpressionNode} {name : String} {boolean : Bool} {sourceEnv : Dynamic.Environment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (known : source.lookupExpression? expression = some selected)
    (form : selected.form = .reference name (.builtinBoolean boolean)) (coercions : selected.coercions = [])
    (failed : Dynamic.ExpressionFaults program context [] source sourceEnv before expression reason after) : False := by
  cases failed with
  | missing absent => exact Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound known)
  | form contained failed =>
    have same := same_node known contained
    subst_vars
    rw [form] at failed
    cases failed
  | coercion contained _ failed =>
    have same := same_node known contained
    subst_vars
    rw [coercions] at failed
    cases failed
  | generalizedLocalRequirement contained other _ _ _ _ _ _ _ =>
    have same := same_node known contained
    subst_vars
    rw [form] at other
    cases other
  | generalizedLocalCoercion contained other _ _ _ _ _ _ _ =>
    have same := same_node known contained
    subst_vars
    rw [form] at other
    cases other

private theorem leaf_preserves (program : SourceSemantics.Program) :
    Preserves model program context [] source Child (fun _ _ => False) := by
  intro scope expression lowered certified foundNode found mapping world admin sourceEnv canonical actual
    before store ξ outcome after environments heaps locals layout execution
  cases certified with
  | @boolean scope expression selected name boolean known form type requirements coercions =>
    have same : foundNode = selected := Option.some.inj (found.symm.trans known)
    subst foundNode
    cases execution with
    | value evaluated =>
      have literal : Literals.Tree source expression (.bool boolean) 1 :=
        .bool (lookupExpression?_sound known) form type requirements coercions
      obtain ⟨rfl, rfl⟩ := literal.source_sound unique evaluated
      refine ⟨.inRight .word (.bool boolean), store, mapping, world, .inRight .bool, ?_, heaps,
        .refl _, .refl _, .refl _ _, .refl _⟩
      rw [type]
      exact .value ⟨rfl, .bool boolean⟩
    | fault failed => exact (boolean_no_fault known form coercions failed).elim

private theorem leaf_reflects (program : SourceSemantics.Program) :
    Reflects model program context [] source Child (fun _ _ => False) := by
  intro scope expression lowered certified foundNode found mapping world admin sourceEnv canonical actual
    before store ξ value finalStore environments heaps locals layout evaluated
  cases certified with
  | @boolean scope expression selected name boolean known form type requirements coercions =>
    have same : foundNode = selected := Option.some.inj (found.symm.trans known)
    subst foundNode
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (show Evaluates actual store
      ((code boolean).expression.rename ξ) (.inRight .word (.bool boolean)) store from .inRight .bool)
    refine ⟨.value (.bool boolean), before, mapping, world, .value ?_, ?_, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
    · apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound known)
      · rw [form, requirements, coercions]; exact .builtinBoolean rfl
      · rw [coercions]; exact .nil
    · rw [type]
      exact .value ⟨rfl, .bool boolean⟩

private theorem tree : Tree source Child [] [id 0, id 1, id 2] [.bool, .bool, .bool]
    [code true, code false, code true] :=
  .cons (node := node 0 true) (by cbv) (Child.boolean (by cbv) rfl rfl rfl rfl)
    (.cons (node := node 1 false) (by cbv) (Child.boolean (by cbv) rfl rfl rfl rfl)
      (.single (node := node 2 true) (by cbv) (Child.boolean (by cbv) rfl rfl rfl rfl)))

private def packed := SourceCoreCalls.packArguments [code true, code false, code true]
private def output : Value := .inRight .word (.pair (.bool true) (.pair (.bool false) (.bool true)))
example : SourceCoreBasic.lowerExpression 4 source [] (id 1) Word.zero = .ok (code false) := by cbv
example : SourceCoreBasic.lowerExpression 4 source [] (id 2) Word.zero = .ok (code true) := by cbv

example : ∃ types, Tree source Child [] [id 0, id 1] types [code true, code false] := by
  let identify := fun (value : Bool) => id (if value then 0 else 1)
  let compile := fun value => SourceCoreBasic.lowerExpression 4 source [] (identify value) Word.zero
  have trueCompiled : compile true = .ok (code true) := by
    change SourceCoreBasic.lowerExpression 4 source [] (id 0) Word.zero = .ok (code true)
    cbv
  have falseCompiled : compile false = .ok (code false) := by
    change SourceCoreBasic.lowerExpression 4 source [] (id 1) Word.zero = .ok (code false)
    cbv
  have compiled : [true, false].mapM compile = .ok [code true, code false] := by
    simp only [List.mapM_cons, List.mapM_nil, trueCompiled, falseCompiled, bind, Except.bind, pure, Except.pure]
  apply Tree.of_mapM identify compile compiled
  intro value lowered accepted
  cases value with
  | false =>
    rw [falseCompiled] at accepted
    cases accepted
    exact ⟨node 1 false, by cbv, Child.boolean (by cbv) rfl rfl rfl rfl⟩
  | true =>
    rw [trueCompiled] at accepted
    cases accepted
    exact ⟨node 0 true, by cbv, Child.boolean (by cbv) rfl rfl rfl rfl⟩

private theorem run : runStateful 100 (.initial packed.expression [.integer 900] []) = .done output [] := by cbv

private theorem source_trace (program : SourceSemantics.Program) :
    Trace program context [] source [] ⟨[]⟩ [id 0, id 1, id 2]
      (.ok [.bool true, .bool false, .bool true]) ⟨[]⟩ := by
  have first : Literals.Tree source (id 0) (.bool true) 1 :=
    .bool (lookupExpression?_sound (show source.lookupExpression? (id 0) = some (node 0 true) by cbv)) rfl rfl rfl rfl
  have second : Literals.Tree source (id 1) (.bool false) 1 :=
    .bool (lookupExpression?_sound (show source.lookupExpression? (id 1) = some (node 1 false) by cbv)) rfl rfl rfl rfl
  have third : Literals.Tree source (id 2) (.bool true) 1 :=
    .bool (lookupExpression?_sound (show source.lookupExpression? (id 2) = some (node 2 true) by cbv)) rfl rfl rfl rfl
  exact .values (.cons (first.source_evaluates program context [] [] ⟨[]⟩)
    (.cons (second.source_evaluates program context [] [] ⟨[]⟩)
      (.cons (third.source_evaluates program context [] [] ⟨[]⟩) .nil)))

example (program : SourceSemantics.Program) : ∃ value finalStore finalMap finalWorld required,
    (∀ fuel, required ≤ fuel → runStateful fuel
      (.initial (packed.expression.rename (Renaming.insertion 0)) [.integer 900] []) = .done value finalStore) ∧
    Result model finalMap finalWorld [.bool, .bool, .bool] [code true, code false, code true]
      (fun _ _ => False) (.ok [.bool true, .bool false, .bool true]) value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld ⟨[]⟩ finalStore ∧
    LocationMap.Extends [] finalMap ∧ WorldExtends [] finalWorld ∧
    AdministrativePreserved [] [] finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ ⟨[]⟩ :=
  tree.preserves_sufficient_fuel (leaf_preserves program) (.nil .nil) .empty .nil
    (by intro index value impossible; simp at impossible) (source_trace program)

/-- The Core execution constructs the source vector trace even with an extra
raw administrative environment slot. No source trace is supplied here. -/
example (program : SourceSemantics.Program) : ∃ outcome after finalMap finalWorld,
    Trace program context [] source [] ⟨[]⟩ [id 0, id 1, id 2] outcome after ∧
    Result model finalMap finalWorld [.bool, .bool, .bool] [code true, code false, code true]
      (fun _ _ => False) outcome output ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after [] ∧
    LocationMap.Extends [] finalMap ∧ WorldExtends [] finalWorld ∧
    AdministrativePreserved [] [] finalMap [] ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after := by
  apply tree.reflects (leaf_reflects program) (canonical := []) (ξ := Renaming.insertion 0)
    (.nil .nil) .empty .nil (by intro index value impossible; simp at impossible)
  simpa [packed, code, SourceCoreCalls.packArguments, LocalSequence.pair, LanguageResult.bind,
    LanguageResult.success, Expr.rename, Expr.weakenAt, Renaming.insertion, Renaming.lift] using
    runStateful_evaluation_sound run

/-- Updating the same captured cell twice observes source order in both the
returned pair and the final store. -/
private def writeThenRead (value : Int) : SourceCoreBasic.LoweredExpr :=
  ⟨.integer, .letE (.storeCell (.var 0) (.integer value)) (LanguageResult.success (.loadCell (.var 1)))⟩
private def mutations := SourceCoreCalls.packArguments [writeThenRead 11, writeThenRead 22]
example : runStateful 100 (.initial mutations.expression [.cellRef .integer 0] [.integer 0]) =
    .done (.inRight .word (.pair (.integer 11) (.integer 22))) [.integer 22] := by cbv

private def failed : SourceCoreBasic.LoweredExpr := ⟨.integer, LanguageResult.failure .integer (.word Word.zero)⟩
private def stops := SourceCoreCalls.packArguments [writeThenRead 11, failed, writeThenRead 22]
example : runStateful 100 (.initial stops.expression [.cellRef .integer 0] [.integer 0]) =
    .done (.inLeft (.product .integer (.product .integer .integer)) (.word Word.zero)) [.integer 11] := by cbv

/-- The second child's closure captures the inserted first payload, so later
application must retain the compiler's shifted reference in its real body. -/
private def captured : SourceCoreBasic.LoweredExpr :=
  ⟨.function .unit .integer, LanguageResult.success (.lambda .unit .integer (.loadCell (.var 1)))⟩
private def makeCapture := SourceCoreCalls.packArguments [writeThenRead 33, captured]
private def invokeCapture : Expr := LanguageResult.bind .integer makeCapture.expression
  (LanguageResult.success (.apply (.second (.var 0)) .unit))
example : infer? [.cell .integer] invokeCapture = some (.sum .word .integer) := by
  simp [invokeCapture, makeCapture, captured, writeThenRead, SourceCoreCalls.packArguments,
    LocalSequence.pair, LanguageResult.bind, LanguageResult.success, Expr.weakenAt]
  decide
example : runStateful 200 (.initial invokeCapture [.cellRef .integer 0] [.integer 0]) =
    .done (.inRight .word (.integer 33)) [.integer 33] := by cbv

end Tests.SourceCoreDataExpressionSequence
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataExpressions
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCoreDataExpressions

open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceCoreGeneralEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def w (value : Nat) : Word := Word.ofNatModulo value
private def present (value : Value) : Value := .inRight .unit value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
    "enum Row { First(Word, Bool), Other(Word, Bool) }",
    "function leaf(value: integer) returns (Tree<integer>) { return .Leaf(value); }",
    "function branch(left: Tree<integer>, right: Tree<integer>, marker: Word) returns (Tree<integer>) { return .Pair(left, right); }",
    "function proxyValue() returns (@Word) { return @Word; }",
    "function find(marker: Word, table: mapping(Word => Word), key: Word) returns (Word) { return table[key]; }",
    "function missing(table: mapping(Word => Tree<integer>), key: Word) returns (Tree<integer>) { return table[key]; }"
  ] }]
}

private def rootExpression (source : TypedSource) : Except SourceCoreBasic.Error ExpressionId := do
  let [.statement root] := source.roots | throw (.missingReturn .unit)
  let statement ← match source.lookupStatement? root with
    | some statement => pure statement
    | none => throw (.missingStatement root)
  match statement.form with
  | .returnStmt (some value) => pure value
  | _ => throw (.unsupportedStatement root statement.form)

/-- Test child policy: operands in these fixtures are ordinary local reads.
Injected effects below test the leaf's sequencing independently of any claim
about the supplied child policy's source semantics. -/
private def localChild (checked : Checked) : SourceCoreDataExpressions.ExpressionLowerer :=
  fun _ source scope id reasonAt => do
    let (node, type) ← SourceCoreDataExpressions.readExpression checked source id
    match node.form with
    | .reference _ (.local binder) =>
      let (index, slot) ← match SourceCoreLocalCell.lookup? scope binder with
        | some found => pure found
        | none => throw (.missingBinding binder)
      SourceCoreBasic.ensureType (.occurrence id.occurrence) type slot
      pure ⟨type, OptionalCell.read type (.var index) (reasonAt id)⟩
    | _ => throw (.unsupportedExpression id node.form)

private def lowerer (checked : Checked) (signatures : ProgramSignatures)
    (child : SourceCoreDataExpressions.ExpressionLowerer) : BodyLowerer checked SourceCoreBasic.Error :=
  fun fuel request => do
    let source := request.specialized.function.typedBody
    let root ← rootExpression source
    let table ← (SourceCoreFaultSites.prepare source request.sourceResultType).mapError
      (fun _ => SourceCoreBasic.Error.missingReturn request.result.type)
    let node ← match source.lookupExpression? root with
      | some node => pure node
      | none => throw (.missingExpression root)
    let missingReason := w 17
    let table := {table with additional := table.additional ++ [(missingReason, {
      error := .typeMismatch request.sourceResultType none,
      site := .occurrence root.occurrence, span := some node.span
    })]}
    let reasonAt := fun id => if id = root then missingReason else table.reasonAt id
    let lowered ← SourceCoreDataExpressions.lowerWithReasons fuel checked signatures child
      source (inputScope request.inputs) root reasonAt
    pure ⟨lowered.expression, table⟩

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"data expression function missing: {name}")

private def prepareEntry (program : CheckedProgram) (checked : Checked) (name : String)
    (child : SourceCoreDataExpressions.ExpressionLowerer) : IO (Entry checked) := do
  let selected ← request program name
  let plan ← match SourceSpecializationWorklist.run program [selected] 100 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"data expression worklist failed: {reprStr result}")
  match prepare program plan checked 100 (lowerer checked program.signatures child) with
  | .ok prepared => match prepared.entries with
      | [entry] => pure entry
      | _ => throw (IO.userError "data expression seed mismatch")
  | .error error => throw (IO.userError s!"data expression compile failed: {reprStr error}")

private def sourceFor (program : CheckedProgram) (name : String) : IO TypedSource := do
  let selected ← request program name
  match SourceSpecializationWorklist.run program [selected] 100 with
  | .ok (.complete plan) => match plan.specializations with
      | specialized :: _ => pure specialized.function.typedBody
      | _ => throw (IO.userError "source specialization missing")
  | _ => throw (IO.userError "source specialization failed")

private def modifyExpression (source : TypedSource) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode) : TypedSource :=
  { source with nodes := source.nodes.map fun
    | .expression node => .expression (if node.id = id then modify node else node)
    | node => node }

private def rejected {α : Type} : Except SourceCoreBasic.Error α → Bool
  | .error _ => true
  | .ok _ => false

private def execute {checked : Checked} (entry : Entry checked) (arguments : List Value) :
    IO LanguageResult.Observation :=
  match entry.run arguments 100000 with
  | .ok result => pure result.observation
  | .error error => throw (IO.userError s!"data expression input rejected: {reprStr error}")

private def effectChild (checked : Checked) : SourceCoreDataExpressions.ExpressionLowerer :=
  fun fuel source scope id reasonAt => do
    let lowered ← localChild checked fuel source scope id reasonAt
    let node ← match source.lookupExpression? id with
      | some node => pure node
      | none => throw (.missingExpression id)
    let digit := match node.form with
      | .reference "table" _ => 1
      | .reference "key" _ => 2
      | _ => 0
    -- `find` has marker/table/key, so marker is the third lexical reference.
    pure ⟨lowered.type, .letE
      (.storeCell (.var 2) (.inRight .unit (.binary .wordAdd
        (.binary .wordMul
          (.caseE (.loadCell (.var 2)) (.word Word.zero) (.var 0)) (.word (w 10))) (.word (w digit)))))
      (lowered.expression.weakenAt 0)⟩

private def keyFailureChild (checked : Checked) : SourceCoreDataExpressions.ExpressionLowerer :=
  fun fuel source scope id reasonAt => do
    let node ← match source.lookupExpression? id with
      | some node => pure node
      | none => throw (.missingExpression id)
    match node.form with
    | .reference "key" _ => pure ⟨.word, LanguageResult.failure .word (.word (w 21))⟩
    | _ => effectChild checked fuel source scope id reasonAt

private def firstFailureChild (checked : Checked) : SourceCoreDataExpressions.ExpressionLowerer :=
  fun fuel source scope id reasonAt => do
    let lowered ← localChild checked fuel source scope id reasonAt
    let node ← match source.lookupExpression? id with
      | some node => pure node
      | none => throw (.missingExpression id)
    match node.form with
    | .reference "left" _ => pure ⟨lowered.type, LanguageResult.failure lowered.type (.word (w 23))⟩
    | .reference "right" _ => pure ⟨lowered.type,
      .letE (.storeCell (.var 0) (.inRight .unit (.word (w 99)))) (lowered.expression.weakenAt 0)⟩
    | _ => pure lowered

example {checked : Checked} {context : Core.Context}
    (compiled : SourceCoreDataExpressions.Certified checked context) :
    HasType context compiled.lowered.expression (LanguageResult.resultType compiled.lowered.type)
      checked.catalog.definitions := compiled.typed

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"data expression source rejected: {reprStr errors}")
  let treeSignature ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some signature => pure signature
    | none => throw (IO.userError "Tree missing")
  let rowSignature ← match program.signatures.dataTypes.find? (·.name == "Row") with
    | some signature => pure signature
    | none => throw (IO.userError "Row missing")
  let treeType := TypeSystem.Ty.nominal treeSignature.id [.integer]
  let rowType := TypeSystem.Ty.nominal rowSignature.id []
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 100
      [treeType, rowType, .proxy .word, .mapping .word .word, .mapping .word treeType] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"data expression catalog rejected: {reprStr error}")
  let treeId := (checked.catalog.identity? treeType).getD ⟨999⟩
  let proxyId := (checked.catalog.identity? (.proxy .word)).getD ⟨999⟩
  let mapId := (checked.catalog.identity? (.mapping .word .word)).getD ⟨999⟩
  let treeMapId := (checked.catalog.identity? (.mapping .word treeType)).getD ⟨999⟩
  let leaf := fun value => Value.constructed ⟨treeId, 0⟩ (.integer value)
  let leafEntry ← prepareEntry program checked "leaf" (localChild checked)
  assertTrue ((← execute leafEntry [.integer (-7)]) == .succeeded (leaf (-7)) [present (.integer (-7))])
    "actual nominal constructor lowering failed"
  let branch ← prepareEntry program checked "branch" (localChild checked)
  let args := [leaf 1, leaf 2, .word Word.zero]
  assertTrue ((← execute branch args) == .succeeded (.constructed ⟨treeId, 1⟩ (.pair (leaf 1) (leaf 2))) (args.map present))
    "constructor payload packing changed"
  let failedBranch ← prepareEntry program checked "branch" (firstFailureChild checked)
  assertTrue ((← execute failedBranch args) == .failed (w 23) (args.map present))
    "failed first constructor argument did not skip later effects"
  let proxy ← prepareEntry program checked "proxyValue" (localChild checked)
  assertTrue ((← execute proxy []) == .succeeded (.constructed ⟨proxyId, 0⟩ .unit) []) "proxy lowering failed"

  let mapping := Value.constructed ⟨mapId, 1⟩
    (.pair (.pair (.word (w 5)) (.word (w 44))) (.constructed ⟨mapId, 0⟩ .unit))
  let find ← prepareEntry program checked "find" (effectChild checked)
  match ← execute find [.word Word.zero, mapping, .word (w 5)] with
  | .succeeded (.word value) store =>
    assertTrue (value == w 44 && store[0]? == some (present (.word (w 12)))) "mapping base/key evaluation order changed"
    assertTrue (store.length == 3 + checked.catalog.entries.length + 1) "mapping helper preparation count changed"
  | other => throw (IO.userError s!"mapping lookup failed: {reprStr other}")
  let failedFind ← prepareEntry program checked "find" (keyFailureChild checked)
  assertTrue ((← execute failedFind [.word Word.zero, mapping, .word (w 5)]) ==
      .failed (w 21) [present (.word (w 1)), present mapping, present (.word (w 5))])
    "key failure must preserve base effects and skip comparator/helper allocation"
  let layout : OrderedMapping.Layout := ⟨.word, .word, mapId⟩
  let lazyBody := Expr.letE (OptionalCell.allocate layout.type)
    (LocalSequence.pair layout.type layout.type
      (SourceCoreDataExpressions.readMapping layout (.var 0))
      (SourceCoreDataExpressions.readMapping layout (.var 0)))
  let lazyProgram : Program := ⟨LanguageResult.resultType (.product layout.type layout.type), lazyBody, checked.catalog.definitions⟩
  assertTrue lazyProgram.check "lazy mapping read failed typing"
  let empty := OrderedMapping.encode layout []
  assertTrue (lazyProgram.runStateful 1000 == .done (.inRight .word (.pair empty empty)) [present empty])
    "lazy mapping read must initialize once at the original location"
  let simpleFind ← prepareEntry program checked "find" (localChild checked)
  match ← execute simpleFind [.word Word.zero, mapping, .word (w 9)] with
  | .succeeded (.word value) _ => assertTrue (value == Word.zero) "absent Word mapping default changed"
  | _ => throw (IO.userError "absent Word mapping did not default")
  let missing ← prepareEntry program checked "missing" (localChild checked)
  match ← execute missing [.constructed ⟨treeMapId, 0⟩ .unit, .word (w 1)] with
  | .failed reason store =>
    assertTrue (reason == w 17 && store.length == 2 + checked.catalog.entries.length + 1)
      "absent nominal mapping did not preserve failure/helper state"
    assertTrue (missing.failureDiagnostic? reason |>.isSome) "caller missing-default diagnostic token was lost"
  | _ => throw (IO.userError "absent nominal mapping unexpectedly invented a value")
  let source ← sourceFor program "branch"
  let root ← match rootExpression source with
    | .ok root => pure root
    | .error error => throw (IO.userError s!"constructor root missing: {reprStr error}")
  let rootNode ← match source.lookupExpression? root with
    | some node => pure node
    | none => throw (IO.userError "constructor node missing")
  let .constructor instantiation arguments := rootNode.form | throw (IO.userError "constructor fixture form changed")
  let scope := inputScope branch.inputs
  let reasonAt := fun _ => Word.zero
  for malformed in [
      {instantiation with parameterSubstitution := []},
      {instantiation with payloadTypes := [.bool, .bool]},
      {instantiation with constructor := {instantiation.constructor with constructorIndex := 99}}] do
    let forged := modifyExpression source root fun node => {node with form := .constructor malformed arguments}
    assertTrue (rejected (SourceCoreDataExpressions.lowerWithReasons 100 checked program.signatures
      (localChild checked) forged scope root reasonAt)) "forged constructor metadata accepted"
  let short := modifyExpression source root fun node => {node with form := .constructor instantiation []}
  assertTrue (rejected (SourceCoreDataExpressions.lowerWithReasons 100 checked program.signatures
    (localChild checked) short scope root reasonAt)) "constructor arity mismatch accepted"
  assertTrue (rejected (SourceCoreDataExpressions.lowerWithReasons 0 checked program.signatures
    (localChild checked) source scope root reasonAt)) "data leaf compile budget ignored"

  -- Member is exercised as retained typed IR: the static source relation uses
  -- uniform positional fields across every registered constructor.
  let base ← match arguments with
    | base :: _ => pure base
    | _ => throw (IO.userError "member base occurrence missing")
  let baseNode ← match source.lookupExpression? base with
    | some node => pure node
    | none => throw (IO.userError "member base node missing")
  let .reference _ (.local binder) := baseNode.form | throw (IO.userError "member base local missing")
  let rowId := (checked.catalog.identity? rowType).getD ⟨999⟩
  let memberSource := modifyExpression (modifyExpression source base fun node => {node with type := rowType})
    root fun node => {node with type := .word, form := .member base "0" 0}
  let memberScope := [(binder, Core.Ty.namedData rowId)]
  let context := [OptionalCell.referenceType (.namedData rowId)]
  let certified ← match SourceCoreDataExpressions.lowerChecked 100 checked program.signatures
      (localChild checked) memberSource memberScope context root reasonAt with
    | .ok certified => pure certified
    | .error error => throw (IO.userError s!"uniform member rejected: {reprStr error}")
  for tag in [0, 1] do
    let value := Value.constructed ⟨rowId, tag⟩ (.pair (.word (w 76)) (.bool true))
    let store := [present value]
    let initial := State.initial certified.lowered.expression
      [.cellRef (OptionalCell.cellType (.namedData rowId)) 0] store
    assertTrue (runStateful 1000 initial == .done (.inRight .word (.word (w 76))) store)
      "member selection used the wrong constructor payload layout"
  for malformed in [
      modifyExpression memberSource root fun node => {node with form := .member base "2" 2},
      modifyExpression memberSource root fun node => {node with type := .bool},
      modifyExpression memberSource root fun node => {node with requirements := [⟨0⟩]}] do
    assertTrue (rejected (SourceCoreDataExpressions.lowerWithReasons 100 checked program.signatures
      (localChild checked) malformed memberScope root reasonAt)) "invalid member metadata accepted"
  IO.println "source Core data expression leaves GREEN"

end Tests.SourceCoreDataExpressions
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataMatchCertificates
/-! Kernel-checked extraction and representation regressions. The match fixture
uses actual metadata checks and exact callback syntax. The heap fixture keeps
a Core-only closure before a nominal source cell and allocates a hidden local
without introducing a source lexical binding. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataMatchCertificates
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"data_match_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "data_match_certificates.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def scrutineeId : ExpressionId := ⟨⟨owner, 1⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 0⟩
private def bound : TypedBinder := ⟨⟨owner, 1⟩, "value", .mono .unit, [], false, none⟩
private def pattern : TypedMatchPattern := {
  source := .binder span "value", type := .unit, resolution := .binder bound
}
private def resolution : MatchResolution := ⟨scrutineeId, hidden, [⟨span, pattern, []⟩], some [], []⟩
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement site]
  nodes := [
    .statement ⟨site, span, .unit, .matchWith resolution⟩,
    .expression { id := scrutineeId, span, type := .unit, form := .tuple [] }]
}
private def checked : SourceCoreDataCatalog.Checked := ⟨{}, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def compilation : SourceCoreDataMatches.Context := ⟨checked, ⟨[], [], [], [], [], []⟩, []⟩
private def expression : SourceCoreDataMatches.ExpressionLowerer := fun _ _ _ _ _ =>
  .ok ⟨.unit, .inRight .word .unit⟩
private def body : SourceCoreDataMatches.BodyLowerer := fun _ _ _ _ _ _ _ =>
  .ok (Core.LocalLoop.fallthrough .unit)
private def reasonAt : ExpressionId → Core.Word := fun _ => Core.Word.zero
private def compiled : Core.Expr :=
  match SourceCoreDataMatches.lowerWithReasons compilation expression body 10 source [] site resolution .unit reasonAt Core.Word.zero with
  | .ok code => code
  | .error _ => .unit
private theorem accepted : SourceCoreDataMatches.lowerWithReasons compilation expression body 10 source [] site
    resolution .unit reasonAt Core.Word.zero = .ok compiled := by rfl

/-- Callback syntax, binder order and hidden/default scopes are extracted from
the executable compiler; no source or Core child evaluation is assumed. -/
private theorem matchCertificate : DataMatchCertificates.Certificate compilation source [] site resolution .unit Core.Word.zero
    (fun _ _ value => value = ⟨.unit, .inRight .word .unit⟩)
    (fun _ _ code => code = Core.LocalLoop.fallthrough .unit) compiled := by
  apply DataMatchCertificates.certificate_of_lowerWithReasons (accepted := accepted)
  · intro _ _ _ _ accepted
    exact Except.ok.inj accepted.symm
  · intro _ _ _ _ accepted
    exact Except.ok.inj accepted.symm

example : SourceCoreDataMatches.lowerWithReasons compilation expression body 10 source [(hidden, .unit)] site
    resolution .unit reasonAt Core.Word.zero = .error (.duplicateBinding hidden) := by cbv

private def context : SourceSemantics.Context := .ofSignatures compilation.signatures
private theorem contextValid : DataPatternLeaves.ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures],
    by intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member⟩
}

/-- Whole compiler acceptance supplies ordered source selection without an
input source matching derivation or a child evaluator premise. -/
example : ∃ selection, Dynamic.MatchCasesSelect context .unit resolution.cases resolution.defaultBody selection :=
  DataMatchDecision.Certificate.source_selects matchCertificate contextValid
    (show source.lookupExpression? resolution.scrutinee = some
      { id := scrutineeId, span, type := .unit, form := .tuple [] } from rfl)
    (DataPatternTypedValues.TypedValueRep.unit)

private def nominal : TypeSystem.Ty := .nominal dataId []
private def constructorSource : Syntax.EnumConstructor := ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [.integer], constructorSource⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [{
  sourceType := nominal, definition := some ⟨[.integer]⟩, constructors := [⟨dataId, 0⟩]
}] }
private def metadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [.integer], nominal⟩
private def sourceBox (n : Int) : Dynamic.Value := .constructed metadata [.integer n]
private def coreBox (n : Int) : Core.Value := .constructed ⟨⟨0⟩, 0⟩ (.integer n)
private theorem represented (n : Int) :
    DataPatternTypedValues.TypedValueRep catalog signatures nominal (sourceBox n) (coreBox n) :=
  .constructed (catalog := catalog) (signatures := signatures) (metadata := metadata)
    (tag := ⟨⟨0⟩, 0⟩) rfl rfl (by cbv) (.cons (.integer n) .nil)
example : ∃ type, catalog.project nominal = .ok type ∧
    ∀ world, Core.RuntimeValueHasType world (coreBox (-7)) type catalog.definitions :=
  DataValueTyping.TypedValueRep.project_typed (represented (-7))

private def admin : Core.Value := .closure .unit .unit .unit []
private def adminType : Core.Ty := .function .unit .unit
private def initialWorld : Core.StoreTyping := [adminType]
private def initialStore : Core.Store := [admin]
private theorem initialHeap : DataHeap.HeapRepresents catalog signatures [] initialWorld ⟨[]⟩ initialStore :=
  DataHeap.HeapRepresents.empty.allocate_administrative (.closure .nil .unit)
private theorem initialEnv : DataHeap.EnvRepresents catalog [] initialWorld [] [] [] [] := .nil .nil
private def finalWorld : Core.StoreTyping := [adminType, Core.OptionalCell.cellType (.namedData ⟨0⟩)]
private def finalStore : Core.Store := [admin, .inRight .unit (coreBox 7)]
private def finalHeap : Dynamic.Heap := ⟨[⟨nominal, some (sourceBox 7), none⟩]⟩

/-- Source location zero maps to Core location one. The hidden Core slot does
not add an entry to the source environment. -/
private theorem hiddenAllocation :
    DataHeap.EnvRepresents catalog [1] finalWorld [] [(hidden, .namedData ⟨0⟩)] []
      [.cellRef (Core.OptionalCell.cellType (.namedData ⟨0⟩)) 1] ∧
    DataHeap.HeapRepresents catalog signatures [1] finalWorld finalHeap finalStore :=
  initialEnv.bind_internal initialHeap rfl (.initialized rfl (represented 7)) .append
example : ¬ Dynamic.Environment.LooksUp ([] : Dynamic.Environment) hidden ⟨0⟩ := by intro impossible; cases impossible
example : Core.RuntimeStoreHasTypes finalWorld finalStore catalog.definitions := hiddenAllocation.2.runtime_hasTypes
example : GeneralHeap.AdministrativePreserved [] initialStore [1] finalStore :=
  GeneralHeap.AdministrativePreserved.allocate [] initialStore (.inRight .unit (coreBox 7))

private def updatedHeap : Dynamic.Heap := ⟨[⟨nominal, some (sourceBox 9), none⟩]⟩
example : ∃ updated, finalStore.write? 1 (.inRight .unit (coreBox 9)) = some updated ∧
    DataHeap.HeapRepresents catalog signatures [1] finalWorld updatedHeap updated ∧
    GeneralHeap.AdministrativePreserved [1] finalStore [1] updated :=
  hiddenAllocation.2.write_initialized ⟨rfl, rfl⟩ (.intro .head) (represented 9)
    (.intro (.intro .head) .head)
private def boxBinder : TypedBinder := ⟨⟨owner, 2⟩, "box", .mono nominal, [], false, none⟩
private def integerBinder : TypedBinder := ⟨⟨owner, 3⟩, "integer", .mono .integer, [], false, none⟩
private def twoBinders : List (TypedBinder × Core.Ty) := [(boxBinder, .namedData ⟨0⟩), (integerBinder, .integer)]
private def boundSources : List (TypedBinder × Dynamic.Value) := [(boxBinder, sourceBox 7), (integerBinder, .integer 9)]
private def boundValues : List Core.Value := [coreBox 7, .integer 9]
private theorem bindingsRepresented : DataPatternBindings.BindingsRep catalog signatures twoBinders boundSources boundValues :=
  .cons rfl (represented 7) (.cons rfl (.integer 9) .nil)

/-- Every successful binder is allocated once, in source order. -/
example : ∃ finalEnvironment finalSourceHeap finalCanonical finalCoreStore finalMap finalCoreWorld,
    Dynamic.BindersAllocate [] finalHeap (boundSources.map Prod.fst) (boundSources.map Prod.snd)
      finalEnvironment finalSourceHeap ∧
    DataHeap.EnvRepresents catalog finalMap finalCoreWorld []
      (twoBinders.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) [(hidden, .namedData ⟨0⟩)])
      finalEnvironment finalCanonical ∧
    DataHeap.HeapRepresents catalog signatures finalMap finalCoreWorld finalSourceHeap finalCoreStore ∧
    GeneralHeap.LocationMap.Extends [1] finalMap ∧ Core.WorldExtends finalWorld finalCoreWorld ∧
    GeneralHeap.AdministrativePreserved [1] finalStore finalMap finalCoreStore :=
  DataMatchAllocation.BindingsRep.allocate bindingsRepresented hiddenAllocation.1 hiddenAllocation.2

private def selectedBody : Core.Expr := Core.OptionalCell.read .integer (.var 0) Core.Word.zero
private def selectedCode : Core.Expr :=
  SourceCoreDataMatches.bindArm twoBinders .integer (selectedBody.weakenAt twoBinders.length)
private def selectedEnvironment : Core.Environment :=
  [DataPatternValues.packValues boundValues, coreBox 7, .cellRef (Core.OptionalCell.cellType (.namedData ⟨0⟩)) 1]

/-- Two temporary slots and two source bindings must not interchange the
bundle, loaded scrutinee or last-bound Integer cell. This is actual Core code. -/
example : Core.runStateful 200 (.initial selectedCode selectedEnvironment finalStore) =
    .done (.inRight .word (.integer 9))
      [admin, .inRight .unit (coreBox 7), .inRight .unit (coreBox 7), .inRight .unit (.integer 9)] := by cbv

end Tests.SourceCoreDataMatchCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPatternEncoding
/-! Concrete consumers of accepted pattern compilation and independent source
matching. Synthetic retained metadata makes the compiler certificate reducible;
source matching is proved separately from the Core machine execution. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataPatternEncoding
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataMatches DataPatternValues DataPatternLeaves DataPatternExecution DataPatternSuccess
open DataPatternTypedValues DataPatternDecision

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"data_pattern_proofs", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "data_pattern_proofs.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def treeType : TypeSystem.Ty := .nominal dataId []
private def constructorSource (name : String) : Syntax.EnumConstructor :=
  ⟨span, ⟨[], ⟨span, name⟩, none⟩⟩
private def signature : ProgramDataSignature := {
  id := dataId, name := "Tree", parameters := []
  constructors := [
    ⟨⟨dataId, 0⟩, "Empty", [], constructorSource "Empty"⟩,
    ⟨⟨dataId, 1⟩, "Leaf", [.integer], constructorSource "Leaf"⟩,
    ⟨⟨dataId, 2⟩, "Pair", [treeType, treeType], constructorSource "Pair"⟩]
  source := ⟨span, ⟨none, ⟨span, "Tree"⟩, none, span, []⟩⟩
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [{
  sourceType := treeType
  definition := some ⟨[.unit, .integer, .product (.namedData ⟨0⟩) (.namedData ⟨0⟩)]⟩
  constructors := [⟨dataId, 0⟩, ⟨dataId, 1⟩, ⟨dataId, 2⟩]
}] }
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def compilation : SourceCoreDataMatches.Context := ⟨checked, signatures, []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def source : TypedSource := { owner, inputs := [], roots := [], nodes := [] }
private def left : TypedBinder := ⟨⟨owner, 0⟩, "left", .mono .integer, [], false, none⟩
private def right : TypedBinder := ⟨⟨owner, 1⟩, "right", .mono .integer, [], false, none⟩
private def emptyMetadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [], treeType⟩
private def leafMetadata : DataConstructorInstantiation := ⟨⟨dataId, 1⟩, [], [.integer], treeType⟩
private def pairMetadata : DataConstructorInstantiation := ⟨⟨dataId, 2⟩, [], [treeType, treeType], treeType⟩
private def pattern : TypedMatchPattern := {
  source := .group span (.constructor span (some span) [] "Pair" 2)
  type := treeType
  resolution := .constructor pairMetadata
    [.constructor leafMetadata 1, .binder left, .constructor leafMetadata 1, .binder right]
}
private def fallback : CertifiedPattern catalog.definitions := {
  pattern := ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
  typed := .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)
}
private def compiled : CertifiedPattern catalog.definitions :=
  match compilePattern compilation 20 source [] site span treeType pattern with
  | .ok result => result
  | .error _ => fallback

private theorem accepted : compilePattern compilation 20 source [] site span treeType pattern = .ok compiled := by cbv
private theorem bindings_order : compiled.pattern.bindings = [(left, .integer), (right, .integer)] := by cbv

private def sourceLeaf (value : Int) : Dynamic.Value := .constructed leafMetadata [.integer value]
private def coreLeaf (value : Int) : Core.Value := .constructed ⟨⟨0⟩, 1⟩ (.integer value)
private def sourceValue : Dynamic.Value := .constructed pairMetadata [sourceLeaf 7, sourceLeaf (-3)]
private def coreValue : Core.Value := .constructed ⟨⟨0⟩, 2⟩ (.pair (coreLeaf 7) (coreLeaf (-3)))
private def sourceBindings : List (TypedBinder × Dynamic.Value) := [(left, .integer 7), (right, .integer (-3))]


open DataPatternEncoding
private def publicLeaf (value : Int) : PublicValue := .constructed leafMetadata [.integer value]
private def publicTree : PublicValue := .constructed pairMetadata [publicLeaf 7, publicLeaf (-3)]
private theorem publicProfile : CarrierProfile publicTree :=
  .constructed (by intro type member; simp [pairMetadata] at member; subst type; exact .nominal (by rfl))
    (.cons (.constructed (by intro type member; simp [leafMetadata] at member; subst type; exact .integer) (.cons (.integer _) .nil))
      (.cons (.constructed (by intro type member; simp [leafMetadata] at member; subst type; exact .integer) (.cons (.integer _) .nil)) .nil))
private theorem publicMeaning : Means publicTree sourceValue :=
  .constructed (.cons (.constructed (.cons (.integer _) .nil)) (.cons (.constructed (.cons (.integer _) .nil)) .nil))
private theorem encoded : SourceCoreDataValues.encode 30 ⟨checked, signatures⟩ treeType publicTree = .ok coreValue := by cbv
private theorem decoded : SourceCoreDataValues.decode 30 ⟨checked, signatures⟩ treeType coreValue = .ok publicTree := by cbv
private theorem contextValid : ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures],
    by intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member⟩
}

/-- The exact independent value is extracted from the real public encoder. -/
example : TypedValueRep catalog signatures treeType sourceValue coreValue := by
  obtain ⟨dynamic, meaning, represented⟩ := encode_represents (.nominal (by rfl)) publicProfile encoded
  have same := Means.functional meaning publicMeaning
  exact same ▸ represented

example : TypedValueRep catalog signatures treeType sourceValue coreValue := by
  obtain ⟨dynamic, meaning, represented⟩ := decode_represents (.nominal (by rfl)) publicProfile decoded
  have same := Means.functional meaning publicMeaning
  exact same ▸ represented

/-- No manual constructor or matcher correspondence certificate is supplied. -/
example (environment : Core.Environment) (store : Core.Store) :
    ∃ sourceValue outcome, Means publicTree sourceValue ∧
      OutcomeRep catalog context pattern compiled.pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (.initial (.apply compiled.pattern.matcher (.var 0)) (coreValue :: environment) store) = .done outcome store) ∧
      (∀ fuel actual finalStore,
        Core.runStateful fuel (.initial (.apply compiled.pattern.matcher (.var 0)) (coreValue :: environment) store) = .done actual finalStore →
        actual = outcome ∧ finalStore = store) :=
  encode_matcher_run_preserves compilation 20 30 source [] site span treeType pattern compiled accepted context contextValid
    (.nominal (by rfl)) publicProfile encoded environment store

private def functionType : TypeSystem.Ty := .function .integer .integer
private def functionBinder : TypedBinder := ⟨⟨owner, 2⟩, "callback", .mono functionType, [], false, none⟩
private def functionPattern : TypedMatchPattern := ⟨.binder span "callback", functionType, .binder functionBinder, []⟩
private def functionCompiled : CertifiedPattern catalog.definitions :=
  match compilePattern compilation 20 source [] site span functionType functionPattern with
  | .ok result => result
  | .error _ => fallback
private theorem functionAccepted : compilePattern compilation 20 source [] site span functionType functionPattern = .ok functionCompiled := by cbv

/-- Function binding transports any already established value/capture relation;
the matcher itself makes no assumptions about the closure representation. -/
example (relation : Dynamic.Value → Core.Value → Prop) {sourceValue : Dynamic.Value} {value : Core.Value}
    (represented : relation sourceValue value) :
    ∃ bindings values, Dynamic.PatternMatches context functionPattern sourceValue bindings ∧
      DataPatternParametricLeaves.BindingsRelated relation functionCompiled.pattern.bindings bindings values ∧
      MatcherRuns functionCompiled.pattern value values :=
  DataPatternParametricLeaves.compilePattern_preserves compilation 20 source [] site span functionType functionPattern
    functionCompiled functionAccepted context rfl (.binder functionBinder) relation represented

end Tests.SourceCoreDataPatternEncoding
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPatternProofs
/-! Concrete consumers of accepted pattern compilation and independent source
matching. Synthetic retained metadata makes the compiler certificate reducible;
source matching is proved separately from the Core machine execution. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataPatternProofs
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataMatches DataPatternValues DataPatternLeaves DataPatternExecution DataPatternSuccess
open DataPatternTypedValues DataPatternDecision

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"data_pattern_proofs", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "data_pattern_proofs.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def treeType : TypeSystem.Ty := .nominal dataId []
private def constructorSource (name : String) : Syntax.EnumConstructor :=
  ⟨span, ⟨[], ⟨span, name⟩, none⟩⟩
private def signature : ProgramDataSignature := {
  id := dataId, name := "Tree", parameters := []
  constructors := [
    ⟨⟨dataId, 0⟩, "Empty", [], constructorSource "Empty"⟩,
    ⟨⟨dataId, 1⟩, "Leaf", [.integer], constructorSource "Leaf"⟩,
    ⟨⟨dataId, 2⟩, "Pair", [treeType, treeType], constructorSource "Pair"⟩]
  source := ⟨span, ⟨none, ⟨span, "Tree"⟩, none, span, []⟩⟩
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [{
  sourceType := treeType
  definition := some ⟨[.unit, .integer, .product (.namedData ⟨0⟩) (.namedData ⟨0⟩)]⟩
  constructors := [⟨dataId, 0⟩, ⟨dataId, 1⟩, ⟨dataId, 2⟩]
}] }
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def compilation : SourceCoreDataMatches.Context := ⟨checked, signatures, []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def source : TypedSource := { owner, inputs := [], roots := [], nodes := [] }
private def left : TypedBinder := ⟨⟨owner, 0⟩, "left", .mono .integer, [], false, none⟩
private def right : TypedBinder := ⟨⟨owner, 1⟩, "right", .mono .integer, [], false, none⟩
private def emptyMetadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [], treeType⟩
private def leafMetadata : DataConstructorInstantiation := ⟨⟨dataId, 1⟩, [], [.integer], treeType⟩
private def pairMetadata : DataConstructorInstantiation := ⟨⟨dataId, 2⟩, [], [treeType, treeType], treeType⟩
private def pattern : TypedMatchPattern := {
  source := .group span (.constructor span (some span) [] "Pair" 2)
  type := treeType
  resolution := .constructor pairMetadata
    [.constructor leafMetadata 1, .binder left, .constructor leafMetadata 1, .binder right]
}
private def fallback : CertifiedPattern catalog.definitions := {
  pattern := ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
  typed := .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)
}
private def compiled : CertifiedPattern catalog.definitions :=
  match compilePattern compilation 20 source [] site span treeType pattern with
  | .ok result => result
  | .error _ => fallback

private theorem accepted : compilePattern compilation 20 source [] site span treeType pattern = .ok compiled := by cbv
private theorem bindings_order : compiled.pattern.bindings = [(left, .integer), (right, .integer)] := by cbv

private def sourceLeaf (value : Int) : Dynamic.Value := .constructed leafMetadata [.integer value]
private def coreLeaf (value : Int) : Core.Value := .constructed ⟨⟨0⟩, 1⟩ (.integer value)
private def sourceValue : Dynamic.Value := .constructed pairMetadata [sourceLeaf 7, sourceLeaf (-3)]
private def coreValue : Core.Value := .constructed ⟨⟨0⟩, 2⟩ (.pair (coreLeaf 7) (coreLeaf (-3)))
private def sourceBindings : List (TypedBinder × Dynamic.Value) := [(left, .integer 7), (right, .integer (-3))]

private theorem source_matches : Dynamic.PatternMatches context pattern sourceValue sourceBindings := by
  apply Dynamic.PatternMatches.intro
    (rootArity := 2) (.group (.constructor ⟨signature, by simp [context, SourceSemantics.Context.ofSignatures, signatures],
      ⟨⟨dataId, 2⟩, "Pair", [treeType, treeType], constructorSource "Pair"⟩, by simp [signature], rfl, rfl⟩))
  exact .constructor (.refl _) rfl (.cons (.constructor (.refl _) rfl (.cons .binder .nil))
    (.cons (.constructor (.refl _) rfl (.cons .binder .nil)) .nil))

private theorem represented : ValueRep catalog sourceValue coreValue :=
  .constructed (by rfl) (.cons (.constructed (by rfl) (.cons (.integer _) .nil))
    (.cons (.constructed (by rfl) (.cons (.integer _) .nil)) .nil))

/-- Compiler acceptance, independent source matching, and finite machine
execution are joined without assuming that the generated matcher evaluates. -/
example (environment : Core.Environment) (store : Core.Store) :
    ∃ values, BindingsRep catalog compiled.pattern.bindings sourceBindings values ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (.initial (.apply compiled.pattern.matcher (.var 0)) (coreValue :: environment) store) =
          .done (.inRight .unit (packValues values)) store) ∧
      (∀ fuel outcome finalStore,
        Core.runStateful fuel (.initial (.apply compiled.pattern.matcher (.var 0)) (coreValue :: environment) store) =
          .done outcome finalStore → outcome = .inRight .unit (packValues values) ∧ finalStore = store) :=
  compilePattern_success_run compilation 20 source [] site span treeType pattern compiled accepted
    context rfl represented source_matches environment store

private def sentinel : Core.Store := [.integer 900, .cellRef .integer 0]
example : Core.runStateful 1000 (.initial (.apply compiled.pattern.matcher (.var 0)) [coreValue] sentinel) =
    .done (.inRight .unit (.pair (.integer 7) (.integer (-3)))) sentinel := by cbv

private def failedSource : Dynamic.Value := .constructed pairMetadata [sourceLeaf 7, .constructed emptyMetadata []]
private def failedCore : Core.Value := .constructed ⟨⟨0⟩, 2⟩ (.pair (coreLeaf 7) (.constructed ⟨⟨0⟩, 0⟩ .unit))

private theorem failed_representation : ValueRep catalog failedSource failedCore :=
  .constructed (by rfl) (.cons (.constructed (by rfl) (.cons (.integer _) .nil))
    (.cons (.constructed (by rfl) .nil) .nil))

/-- A successful first child does not leak bindings when the second constructor
mismatches. The independent source relation also rejects that exact value. -/
private theorem source_fails : Dynamic.PatternDoesNotMatch context pattern failedSource := by
  apply Dynamic.PatternDoesNotMatch.intro (rootArity := 2)
    (.group (.constructor ⟨signature, by simp [context, SourceSemantics.Context.ofSignatures, signatures],
      ⟨⟨dataId, 2⟩, "Pair", [treeType, treeType], constructorSource "Pair"⟩, by simp [signature], rfl, rfl⟩))
  refine ⟨.constructor (.succ (.constructor (.succ .binder .zero)) (.succ (.constructor (.succ .binder .zero)) .zero)), ?_⟩
  intro bindings matched
  cases matched with
  | constructor agree arity children =>
    cases children with
    | cons first rest =>
      cases first with
      | constructor firstAgree firstArity firstChildren =>
        cases firstChildren with
        | cons head tail =>
          cases head
          cases tail
          cases rest with
          | cons second last =>
            cases second with
            | constructor wrong => cases wrong.constructor_eq

example : Core.runStateful 1000 (.initial (.apply compiled.pattern.matcher (.var 0)) [failedCore] sentinel) =
    .done (.inLeft (.product .integer .integer) .unit) sentinel := by cbv


private theorem contextValid : ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures],
    by intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member⟩
}
private theorem leafTyped (value : Int) : TypedValueRep catalog signatures treeType (sourceLeaf value) (coreLeaf value) :=
  .constructed (metadata := leafMetadata) (values := [.integer value]) (by rfl) rfl (by cbv) (.cons (.integer _) .nil)
private theorem typedRepresentation : TypedValueRep catalog signatures treeType sourceValue coreValue :=
  .constructed (metadata := pairMetadata) (values := [coreLeaf 7, coreLeaf (-3)]) (by rfl) rfl (by cbv)
    (.cons (leafTyped 7) (.cons (leafTyped (-3)) .nil))
private theorem failedTypedRepresentation : TypedValueRep catalog signatures treeType failedSource failedCore :=
  .constructed (metadata := pairMetadata) (values := [coreLeaf 7, .constructed ⟨⟨0⟩, 0⟩ .unit]) (by rfl) rfl (by cbv)
    (.cons (leafTyped 7) (.cons (.constructed (metadata := emptyMetadata) (values := []) (by rfl) rfl (by cbv) .nil) .nil))

example (environment : Core.Environment) (store : Core.Store) :
    ∃ outcome, OutcomeRep catalog context pattern compiled.pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (.initial (.apply compiled.pattern.matcher (.var 0)) (coreValue :: environment) store) = .done outcome store) ∧
      (∀ fuel actual finalStore,
        Core.runStateful fuel (.initial (.apply compiled.pattern.matcher (.var 0)) (coreValue :: environment) store) = .done actual finalStore →
        actual = outcome ∧ finalStore = store) :=
  compilePattern_run_preserves compilation 20 source [] site span treeType pattern compiled accepted context contextValid
    typedRepresentation environment store

example (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates (failedCore :: environment) store (.apply compiled.pattern.matcher (.var 0))
      (.inLeft (.product .integer .integer) .unit) store := by
  have evaluated := compilePattern_failure_preserves compilation 20 source [] site span treeType pattern compiled accepted
    context contextValid failedTypedRepresentation source_fails environment store
  simpa only [Pattern.bindingTypes, bindings_order, List.map_cons, List.map_nil, bundleType] using evaluated

private def tupleType : TypeSystem.Ty := .product treeType (.product .bool .integer)
private def tuplePattern : TypedMatchPattern := {
  source := .tuple span 2
  type := tupleType
  resolution := .tuple [.constructor leafMetadata 1, .binder left, .tuple 2, .wildcard, .binder right]
}
private def tupleCompiled : CertifiedPattern catalog.definitions :=
  match compilePattern compilation 20 source [] site span tupleType tuplePattern with
  | .ok result => result
  | .error _ => fallback
private theorem tupleAccepted : compilePattern compilation 20 source [] site span tupleType tuplePattern = .ok tupleCompiled := by cbv
private def tupleSource : Dynamic.Value := .product (sourceLeaf 7) (.product (.bool true) (.integer (-3)))
private def tupleCore : Core.Value := .pair (coreLeaf 7) (.pair (.bool true) (.integer (-3)))
private theorem tupleSourceMatches : Dynamic.PatternMatches context tuplePattern tupleSource sourceBindings :=
  .intro .tuple (.tuple (.cons (.singleton _)) rfl
    (.cons (.constructor (.refl _) rfl (.cons .binder .nil))
      (.cons (.tuple (.cons (.singleton _)) rfl (.cons .wildcard (.cons .binder .nil))) .nil)))
private theorem tupleRepresents : ValueRep catalog tupleSource tupleCore :=
  .product (.constructed (by rfl) (.cons (.integer _) .nil)) (.product (.bool _) (.integer _))

example : ∃ values, BindingsRep catalog tupleCompiled.pattern.bindings sourceBindings values ∧
    MatcherRuns tupleCompiled.pattern tupleCore values :=
  compilePattern_success_preserves compilation 20 source [] site span tupleType tuplePattern tupleCompiled
    tupleAccepted context rfl tupleRepresents tupleSourceMatches

example : Core.runStateful 1000 (.initial (.apply tupleCompiled.pattern.matcher (.var 0)) [tupleCore] sentinel) =
    .done (.inRight .unit (.pair (.integer 7) (.integer (-3)))) sentinel := by cbv

/-- Repeated root groups preserve the arity of the nested tuple pattern. -/
private def groupedTuplePattern : TypedMatchPattern :=
  { tuplePattern with source := .group span (.group span tuplePattern.source) }
private def groupedTupleCompiled : CertifiedPattern catalog.definitions :=
  match compilePattern compilation 20 source [] site span tupleType groupedTuplePattern with
  | .ok result => result
  | .error _ => fallback
private theorem groupedTupleAccepted :
    compilePattern compilation 20 source [] site span tupleType groupedTuplePattern = .ok groupedTupleCompiled := by cbv

/-- The static certificate comes from the actual compiler, including the root
instruction arity and both nested child certificates. -/
example : DataPatternCertificates.Certificate compilation source [] site span tupleType groupedTuplePattern
    groupedTupleCompiled.pattern :=
  DataPatternCertificates.certificate_of_compilePattern compilation 20 source [] site span tupleType
    groupedTuplePattern groupedTupleCompiled groupedTupleAccepted

private theorem groupedTupleSourceMatches :
    Dynamic.PatternMatches context groupedTuplePattern tupleSource sourceBindings := by
  cases tupleSourceMatches with
  | intro spelling matched => exact .intro (.group (.group spelling)) matched

private theorem tupleTypedRepresents : TypedValueRep catalog signatures tupleType tupleSource tupleCore :=
  .product (leafTyped 7) (.product (.bool _) (.integer _))

/-- Independent source matching determines the finite Core result with the
same binder order and the original store, for arbitrary surrounding state. -/
example (environment : Core.Environment) (store : Core.Store) :
    ∃ values, BindingsRep catalog groupedTupleCompiled.pattern.bindings sourceBindings values ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (.initial (.apply groupedTupleCompiled.pattern.matcher (.var 0))
          (tupleCore :: environment) store) = .done (.inRight .unit (packValues values)) store) ∧
      (∀ fuel outcome finalStore,
        Core.runStateful fuel (.initial (.apply groupedTupleCompiled.pattern.matcher (.var 0))
          (tupleCore :: environment) store) = .done outcome finalStore →
        outcome = .inRight .unit (packValues values) ∧ finalStore = store) :=
  compilePattern_success_run compilation 20 source [] site span tupleType groupedTuplePattern groupedTupleCompiled
    groupedTupleAccepted context rfl tupleRepresents groupedTupleSourceMatches environment store

example (environment : Core.Environment) (store : Core.Store) :
    ∃ outcome, OutcomeRep catalog context groupedTuplePattern groupedTupleCompiled.pattern tupleSource outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (.initial (.apply groupedTupleCompiled.pattern.matcher (.var 0))
          (tupleCore :: environment) store) = .done outcome store) ∧
      (∀ fuel actual finalStore,
        Core.runStateful fuel (.initial (.apply groupedTupleCompiled.pattern.matcher (.var 0))
          (tupleCore :: environment) store) = .done actual finalStore → actual = outcome ∧ finalStore = store) :=
  compilePattern_run_preserves compilation 20 source [] site span tupleType groupedTuplePattern groupedTupleCompiled
    groupedTupleAccepted context contextValid tupleTypedRepresents environment store

example : Core.runStateful 1000 (.initial (.apply groupedTupleCompiled.pattern.matcher (.var 0))
    [tupleCore] sentinel) = .done (.inRight .unit (.pair (.integer 7) (.integer (-3)))) sentinel := by cbv

end Tests.SourceCoreDataPatternProofs
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataMatches
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false
namespace Tests.SourceCoreDataMatches
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceCoreGeneralEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def w (value : Nat) : Word := Word.ofNatModulo value
private def present (value : Value) : Value := .inRight .unit value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree { Leaf(Word), Pair(Tree, Tree) }",
    "function choose(tree: Tree) returns (Word) {",
    "  match (tree) {",
    "    case .Pair(.Leaf(left), .Leaf(0)) { return left; }",
    "    case .Pair(.Leaf(left), .Leaf(right)) { left = left + right; return left; }",
    "    case .Leaf(value) { return value; }",
    "    default { return 99; }",
    "  }",
    "}",
    "function tuple(value: (Tree, (Bool, Word))) returns (Word) {",
    "  match (value) {",
    "    case (.Leaf(left), (flag, right)) { return flag ? left + right : right; }",
    "    default { return 99; }",
    "  }",
    "}",
    "function integerCase(value: integer) returns (integer) {",
    "  match (value) { case 0 { return 5; } case (1) { return 6; } case other { return other; } }",
    "}",
    "function wildcard(value: Word) returns (Word) {",
    "  match (value) { case _ { return 3; } default { let absent: Word; return absent; } }",
    "}",
    "function unitCase(value: Unit) returns (Word) { match (value) { case () { return 7; } } }",
    "function nestedFailure(value: Tree) returns (Word) {",
    "  match (value) { case .Leaf(bound) { let absent: Word; return absent; } default { return 8; } }",
    "}",
    "function none(value: Word) returns (Unit) { match (value) { case 0 { return; } default {} } }",
    "function once(value: Tree, marker: Word) returns (Word) {",
    "  match ((lam() -> Tree { marker = marker + 1; return value; })()) {",
    "    case .Leaf(bound) { return marker + bound; } default { return marker; }",
    "  }",
    "}",
    "function scrutineeFailure(value: Tree) returns (Word) {",
    "  match ((lam() -> Tree { let missing: Tree; return missing; })()) {",
    "    case .Leaf(bound) { return bound; } default { return 9; }",
    "  }",
    "}",
    "function functionBinder(marker: Word) returns (Word) {",
    "  match (lam(x: Word) -> Word { marker = marker + x; return marker; }) {",
    "    case f { let first: Word = f(2); return f(3); }",
    "  }",
    "}",
    "function moduloPattern(value: Word) returns (Word) {",
    "  match (value) { case 115792089237316195423570985008687907853269984665640564039457584007913129639936 { return 1; } default { return 2; } }",
    "}"
  ] }]
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"match function missing: {name}")

private def planFor (program : CheckedProgram) (name : String) : IO Plan := do
  let selected ← request program name
  match SourceSpecializationWorklist.run program [selected] 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"match worklist failed: {reprStr result}")

private def rootMatch (source : TypedSource) : Except SourceCoreBasic.Error (StatementId × StatementNode × MatchResolution) := do
  let [.statement root] := source.roots | throw (.missingReturn .unit)
  let node ← match source.lookupStatement? root with
    | some node => pure node
    | none => throw (.missingStatement root)
  match node.form with
  | .matchWith resolution => pure (root, node, resolution)
  | _ => throw (.unsupportedStatement root node.form)

private def flowPolicy (checked : Checked) (expression : SourceCoreFunctions.ExpressionLowerer) : SourceCoreLoops.Policy := {
  lowerExpression := expression
  readStatement := SourceCoreGeneralTypes.readStatement checked
  lowerBinder := SourceCoreGeneralTypes.lowerBinder checked
  lowerAssignment := SourceCoreGeneralTypes.lowerAssignment checked
}

private def lambdaBody (checked : Checked) : SourceCoreFunctions.BodyLowerer :=
  fun expression fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy (flowPolicy checked expression)
      fuel source scope statements result reasonAt fellThrough escaped

private def lowering (program : CheckedProgram) (checked : Checked) : BodyLowerer checked SourceCoreBasic.Error :=
  fun fuel request => do
    let source := request.specialized.function.typedBody
    let (id, _, resolution) ← rootMatch source
    let table ← (SourceCoreFaultSites.prepare source request.sourceResultType).mapError
      (fun _ => SourceCoreBasic.Error.missingReturn request.result.type)
    let context : SourceCoreCalls.Context := {
      plan := request.plan, owner := request.specialized.key, globals := [], administrativePrefix := 0,
      solvedRequirements := request.specialized.function.solvedRequirements, internalReason := w 250
    }
    let expression : SourceCoreFunctions.ExpressionLowerer := fun budget source scope id reasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy (SourceCoreGeneralTypes.policy checked program.signatures)
        (lambdaBody checked) budget context source scope id reasonAt
    let nested : SourceCoreDataMatches.BodyLowerer := fun fuel source scope statements result reasonAt escaped =>
      SourceCoreLoops.lowerFlowStatementsWithPolicy (flowPolicy checked expression)
        fuel source scope statements result reasonAt false escaped
    let compiled ← SourceCoreDataMatches.lowerChecked
      ⟨checked, program.signatures, request.specialized.function.solvedRequirements⟩ expression nested fuel source
      (inputScope request.inputs) (inputContext request.inputs) id resolution request.result.type table.reasonAt (w 250)
    let fallback := if request.result.type = .unit then LanguageResult.success .unit
      else LanguageResult.failure request.result.type (.word Word.zero)
    pure ⟨LocalControl.finish request.result.type (LocalLoop.toControl request.result.type compiled.expression (w 251)) fallback, table⟩

private def entryFor (program : CheckedProgram) (checked : Checked) (name : String) : IO (Entry checked) := do
  let plan ← planFor program name
  match prepare program plan checked 100 (lowering program checked) with
  | .ok prepared => match prepared.entries with
      | [entry] => pure entry
      | _ => throw (IO.userError "match seed mismatch")
  | .error error => throw (IO.userError s!"match compile {name} failed: {reprStr error}")

private def execute {checked : Checked} (entry : Entry checked) (arguments : List Value) : IO LanguageResult.Observation :=
  match entry.run arguments 100000 with
  | .ok result => pure result.observation
  | .error error => throw (IO.userError s!"match inputs failed: {reprStr error}")

private def rejected {α : Type} : Except SourceCoreBasic.Error α → Bool
  | .error _ => true
  | .ok _ => false

private def metadataTests (program : CheckedProgram) (checked : Checked) : IO Unit := do
  let plan ← planFor program "choose"
  let specialized ← match plan.specializations with
    | [specialized] => pure specialized
    | _ => throw (IO.userError "choose specialization mismatch")
  let source := specialized.function.typedBody
  let (id, node, resolution) ← match rootMatch source with
    | .ok root => pure root
    | .error error => throw (IO.userError s!"match root failed: {reprStr error}")
  let first ← match resolution.cases[0]? with
    | some arm => pure arm
    | none => throw (IO.userError "literal constructor arm missing")
  let second ← match resolution.cases[1]? with
    | some arm => pure arm
    | none => throw (IO.userError "binder constructor arm missing")
  let context : SourceCoreDataMatches.Context := ⟨checked, program.signatures, specialized.function.solvedRequirements⟩
  let scope ← source.inputs.foldlM (fun scope binder => do
    match SourceCoreGeneralTypes.lowerBinder checked source scope binder with
    | .ok type => pure ((binder.id, type) :: scope)
    | .error error => throw (IO.userError s!"match input scope: {reprStr error}")) []
  let scope := (resolution.hiddenScrutinee, (checked.catalog.project first.pattern.type).toOption.getD .unit) :: scope
  let compile := fun (pattern : TypedMatchPattern) => SourceCoreDataMatches.compilePattern context 100 source scope
    id node.span first.pattern.type pattern
  assertTrue (!rejected (compile first.pattern)) "valid pattern metadata rejected"
  assertTrue (rejected (SourceCoreDataMatches.compilePattern context 0 source scope id node.span
    first.pattern.type first.pattern)) "zero pattern compile fuel accepted"
  let .constructor constructor instructions := first.pattern.resolution
    | throw (IO.userError "constructor resolution missing")
  assertTrue (rejected (compile {first.pattern with requirements := []})) "detached pattern requirements accepted"
  assertTrue (rejected (compile {first.pattern with type := .word})) "wrong pattern result type accepted"
  let wrongPayload := {constructor with payloadTypes := []}
  let wrongIdentity := {constructor with constructor := {constructor.constructor with constructorIndex := 999}}
  assertTrue (rejected (compile {first.pattern with resolution := .constructor wrongPayload instructions}))
    "forged constructor payload metadata accepted"
  assertTrue (rejected (compile {first.pattern with resolution := .constructor wrongIdentity instructions}))
    "forged constructor identity accepted"
  assertTrue (rejected (compile {first.pattern with resolution := .constructor constructor (instructions ++ [.wildcard])}))
    "unconsumed pattern instruction accepted"
  let .constructor span dot qualifiers name count := first.pattern.source
    | throw (IO.userError "constructor source root missing")
  assertTrue (rejected (compile {first.pattern with source := .constructor span dot qualifiers name (count + 1)}))
    "wrong retained root arity accepted"
  assertTrue (rejected (compile {first.pattern with source := .constructor span dot qualifiers "Forged" count}))
    "wrong constructor source spelling accepted"
  let changedLiteral := instructions.map fun
    | .integerLiteral raw literal => .integerLiteral raw {literal with rawValue := literal.rawValue + 1}
    | instruction => instruction
  assertTrue (rejected (compile {first.pattern with resolution := .constructor constructor changedLiteral}))
    "literal raw value mismatch accepted"
  let noEvidence := {context with solvedRequirements := []}
  assertTrue (rejected (SourceCoreDataMatches.compilePattern noEvidence 100 source scope id node.span
    first.pattern.type first.pattern)) "unproved literal pattern accepted"
  let .constructor secondConstructor secondInstructions := second.pattern.resolution
    | throw (IO.userError "second constructor pattern missing")
  let binders := secondInstructions.filterMap fun | .binder binder => some binder | _ => none
  let [left, right] := binders | throw (IO.userError "nested binders missing")
  let changeRight := fun (replacement : TypedBinder) =>
    let instructions := secondInstructions.map fun
      | .binder binder => .binder (if binder.id = right.id then replacement else binder)
      | instruction => instruction
    {second.pattern with resolution := .constructor secondConstructor instructions}
  assertTrue (rejected (compile (changeRight {right with id := left.id}))) "duplicate binder identity accepted"
  assertTrue (rejected (compile (changeRight {right with name := left.name}))) "duplicate binder name accepted"
  assertTrue (rejected (compile (changeRight {right with id := resolution.hiddenScrutinee}))) "hidden-cell alias accepted"
  assertTrue (rejected (compile (changeRight {right with comptime := true}))) "comptime pattern binding accepted"
  assertTrue (rejected (compile (changeRight {right with scheme := .mono .bool}))) "wrong binder source type accepted"
  let tuplePlan ← planFor program "tuple"
  let tupleFunction ← match tuplePlan.specializations with
    | [specialized] => pure specialized.function
    | _ => throw (IO.userError "tuple specialization mismatch")
  let (tupleId, tupleNode, tupleResolution) ← match rootMatch tupleFunction.typedBody with
    | .ok root => pure root
    | .error error => throw (IO.userError s!"tuple root failed: {reprStr error}")
  let [tupleArm] := tupleResolution.cases | throw (IO.userError "tuple arm missing")
  let tupleContext : SourceCoreDataMatches.Context := ⟨checked, program.signatures, tupleFunction.solvedRequirements⟩
  let plain ← match SourceCoreDataMatches.compilePattern tupleContext 100 tupleFunction.typedBody []
      tupleId tupleNode.span tupleArm.pattern.type tupleArm.pattern with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError s!"plain tuple pattern failed: {reprStr error}")
  let grouped ← match SourceCoreDataMatches.compilePattern tupleContext 100 tupleFunction.typedBody []
      tupleId tupleNode.span tupleArm.pattern.type
      {tupleArm.pattern with source := .group tupleNode.span (.group tupleNode.span tupleArm.pattern.source)} with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError s!"grouped tuple pattern failed: {reprStr error}")
  assertTrue (grouped.pattern.matcher == plain.pattern.matcher && grouped.pattern.bindings == plain.pattern.bindings)
    "tuple grouping changed its generated matcher or binder order"

example {context : SourceCoreDataMatches.Context} {environment : Core.Context} {type : Ty}
    (compiled : SourceCoreDataMatches.Certified context environment type) :
    HasType environment compiled.expression (LocalLoop.resultType type) context.checked.catalog.definitions := compiled.typed

example {definitions : DataEnvironment} (pattern : SourceCoreDataMatches.CertifiedPattern definitions) :
    HasType [] pattern.pattern.matcher pattern.pattern.functionType definitions := pattern.typed

/-- A binder matcher is pure even when its value contains shared cells. -/
example (environment : Environment) (store : Store) (type : Ty) (location : Location) :
    Evaluates (.cellRef type location :: environment) store
      (.apply (.lambda (.cell type) (.sum .unit (.cell type)) (.inRight .unit (.var 0))) (.var 0))
      (.inRight .unit (.cellRef type location)) store :=
  SourceCoreDataMatches.binder_evaluates environment store (.cell type) (.cellRef type location)

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"match source rejected: {reprStr errors}")
  let tree ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some signature => pure signature
    | none => throw (IO.userError "Tree missing")
  let treeType := TypeSystem.Ty.nominal tree.id []
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 100 [treeType] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"match catalog rejected: {reprStr error}")
  let treeId := (checked.catalog.identity? treeType).getD ⟨999⟩
  let leaf := fun value => Value.constructed ⟨treeId, 0⟩ (.word (w value))
  let pair := fun left right => Value.constructed ⟨treeId, 1⟩ (.pair left right)
  let choose ← entryFor program checked "choose"
  let nested := pair (leaf 7) (leaf 8)
  assertTrue ((← execute choose [nested]) == .succeeded (.word (w 15))
    [present nested, present nested, present (.word (w 15)), present (.word (w 8))])
    "failed partial pattern allocated a binder or successful bindings were not source ordered"
  let first := pair (leaf 7) (leaf 0)
  assertTrue ((← execute choose [first]) == .succeeded (.word (w 7)) [present first, present first, present (.word (w 7))])
    "first matching arm or literal selection changed"
  let single := leaf 4
  assertTrue ((← execute choose [single]) == .succeeded (.word (w 4)) [present single, present single, present (.word (w 4))])
    "constructor mismatch did not skip to later arm"
  let unmatched := pair nested nested
  assertTrue ((← execute choose [unmatched]) == .succeeded (.word (w 99)) [present unmatched, present unmatched])
    "default arm should allocate no pattern bindings"
  let tuple ← entryFor program checked "tuple"
  let input := Value.pair (leaf 10) (.pair (.bool true) (.word (w 20)))
  assertTrue ((← execute tuple [input]) == .succeeded (.word (w 30))
    [present input, present input, present (.word (w 10)), present (.bool true), present (.word (w 20))])
    "nested tuple and constructor binding order changed"
  let integerCase ← entryFor program checked "integerCase"
  assertTrue ((← execute integerCase [.integer 0]) == .succeeded (.integer 5) [present (.integer 0), present (.integer 0)])
    "Integer literal pattern rejected zero"
  assertTrue ((← execute integerCase [.integer 1]) == .succeeded (.integer 6) [present (.integer 1), present (.integer 1)])
    "grouped Integer literal changed meaning"
  assertTrue ((← execute integerCase [.integer (-3)]) == .succeeded (.integer (-3))
    [present (.integer (-3)), present (.integer (-3)), present (.integer (-3))]) "Integer binder changed signed value"
  let wildcard ← entryFor program checked "wildcard"
  assertTrue ((← execute wildcard [.word (w 8)]) == .succeeded (.word (w 3))
    [present (.word (w 8)), present (.word (w 8))]) "wildcard did not skip faulting default"
  let unitCase ← entryFor program checked "unitCase"
  assertTrue ((← execute unitCase [.unit]) == .succeeded (.word (w 7)) [present .unit, present .unit]) "unit pattern failed"
  let noMatchEntry ← entryFor program checked "none"
  assertTrue ((← execute noMatchEntry [.word (w 8)]) == .succeeded .unit
    [present (.word (w 8)), present (.word (w 8))]) "nonmatching Unit match did not fall through"
  let failure ← entryFor program checked "nestedFailure"
  match ← execute failure [single] with
  | .failed reason store =>
      assertTrue (failure.failureDiagnostic? reason |>.isSome) "arm fault lost source diagnostic"
      assertTrue (store == [present single, present single, present (.word (w 4)), .inLeft .word .unit])
        "arm failure lost initialized binders or executed fallback"
  | other => throw (IO.userError s!"arm failure changed: {reprStr other}")
  match choose.run [nested] 20 with
  | .ok suspended => match suspended.checkpoint? with
    | some checkpoint =>
      let resumed := checkpoint.resume 100000
      assertTrue (resumed.observation == (← execute choose [nested])) "typed match checkpoint changed result/store"
    | none => throw (IO.userError "match checkpoint completed unexpectedly")
  | .error error => throw (IO.userError s!"match checkpoint rejected: {reprStr error}")
  -- Closures capture by value. The scrutinee lambda copies `marker` and `value`
  -- when it is created and again for its one call, which assigns 11 to its own
  -- copy of `marker`; the arm reads the enclosing `marker`, still 10.
  let once ← entryFor program checked "once"
  assertTrue ((← execute once [single, .word (w 10)]) == .succeeded (.word (w 14))
    [present single, present (.word (w 10)), present (.word (w 10)), present single,
      present (.word (w 11)), present single, present single, present (.word (w 4))])
    "scrutinee closure ran more than once or its call reached the enclosing marker"
  let scrutineeFailure ← entryFor program checked "scrutineeFailure"
  match ← execute scrutineeFailure [single] with
  | .failed reason store =>
    assertTrue (scrutineeFailure.failureDiagnostic? reason |>.isSome) "scrutinee failure lost exact diagnostic"
    -- `value`, the lambda's snapshot of it, its call's copy, then the absent local.
    assertTrue (store == [present single, present single, present single, .inLeft (.namedData treeId) .unit])
      "failed scrutinee allocated hidden or arm cells"
  | other => throw (IO.userError s!"scrutinee failure changed: {reprStr other}")
  let functionBinder ← entryFor program checked "functionBinder"
  match ← execute functionBinder [.word (w 10)] with
  | .succeeded (.word value) store =>
    -- Both calls start again from the lambda's snapshot of `marker = 10`.
    assertTrue (value == w 13 && store[0]? == some (present (.word (w 10))))
      "function pattern call reached the enclosing marker or did not restart from its snapshot"
    -- The six parameter, hidden, binder and let cells, the lambda's snapshot and two call copies.
    assertTrue (store.length == 9) "function pattern binder parameter/let/copy allocation count changed"
  | other => throw (IO.userError s!"function pattern binder changed: {reprStr other}")
  let modulo ← entryFor program checked "moduloPattern"
  assertTrue ((← execute modulo [.word Word.zero]) == .succeeded (.word (w 1))
    [present (.word Word.zero), present (.word Word.zero)]) "Word pattern modulo semantics changed"
  metadataTests program checked
  IO.println "source Core data matches GREEN"

end Tests.SourceCoreDataMatches
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPayload
/-! Actual public encoding supplies a complete nominal/mapping/proxy payload,
then the same certificate supplies equality observations and mapped heap cells.
Duplicate mapping keys and raw comptime proxy identities are retained. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreDataPayload
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open DataPayload DataPayloadEncoding
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"payload", by decide⟩], by decide⟩⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "payload.solc"⟩, 0, 1⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def proxyInner : TypeSystem.Ty := .comptime .integer
private def proxyType : TypeSystem.Ty := .proxy proxyInner
private def mappingType : TypeSystem.Ty := .mapping (.comptime .word) proxyType
private def layout : Core.OrderedMapping.Layout := ⟨.word, .namedData ⟨2⟩, ⟨1⟩⟩
private def payloadTypes : List TypeSystem.Ty := [mappingType, .product .bool .integer]
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", payloadTypes, ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := boxType, definition := some ⟨[.product layout.type (.product .bool .integer)]⟩, constructors := [⟨dataId, 0⟩] },
  { sourceType := .mapping .word proxyType, definition := some layout.definition },
  { sourceType := proxyType, definition := some ⟨[.unit]⟩ }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def context : SourceCoreDataValues.Context := ⟨checked, signatures⟩
private def metadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], payloadTypes, boxType⟩
private def emptyFunctions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private def model := payloadModel catalog signatures emptyFunctions
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero => cases selected; trivial
  | succ index => cases index with
    | zero =>
      cases selected
      exact ⟨.word, .namedData ⟨2⟩, rfl, rfl, ⟨.word, .namedData (by rfl), rfl⟩⟩
    | succ index => cases index with
      | zero => cases selected; rfl
      | succ index => simp [catalog] at selected
private theorem observedFunctions : FunctionObservations catalog signatures emptyFunctions (fun _ _ => False) :=
  fun impossible => False.elim impossible
private def publicValue : SourceCoreDataValues.Value := .constructed metadata [
  .mapping (.comptime .word) proxyType [(.word Word.zero, .proxy proxyInner), (.word Word.zero, .proxy proxyInner)],
  .product (.bool true) (.integer (-7))]
private def sourceValue : Dynamic.Value := .constructed metadata [
  .mapping (.comptime .word) proxyType [(.word Word.zero, .proxy proxyInner), (.word Word.zero, .proxy proxyInner)],
  .product (.bool true) (.integer (-7))]
private def proxyCore : Value := .constructed ⟨⟨2⟩, 0⟩ .unit
private def coreValue : Value := .constructed ⟨⟨0⟩, 0⟩
  (.pair (Core.OrderedMapping.encode layout [(.word Word.zero, proxyCore), (.word Word.zero, proxyCore)])
    (.pair (.bool true) (.integer (-7))))
private theorem meaning : Means publicValue sourceValue :=
  .constructed (.cons (.mapping (.prepend (.word _) (.proxy _) (.prepend (.word _) (.proxy _) .empty)))
    (.cons (.product (.bool _) (.integer _)) .nil))
private theorem encoded : SourceCoreDataValues.encode 40 context boxType publicValue = .ok coreValue := by cbv
private theorem receipt : SourceCoreDataValues.Encodes 40 context boxType publicValue coreValue :=
  SourceCoreDataValues.encodes_of_encode encoded
private theorem represented : ValueRep catalog signatures emptyFunctions [] [] boxType sourceValue coreValue (.namedData ⟨0⟩) :=
  encodes_represents_at layouts meaning (by rfl) receipt

example : SourceCoreDataCatalog.prepare signatures 100 [boxType] = .ok checked := by cbv
example : SourceCoreDataValues.decode 40 context boxType coreValue = .ok publicValue := by cbv
example : RuntimeValueHasType [] coreValue (.namedData ⟨0⟩) catalog.definitions := represented.runtime_hasType
example : DataEqualityValues.Observation catalog signatures (fun _ _ => False) (.namedData ⟨0⟩) sourceValue coreValue :=
  represented.observation observedFunctions
example : ValueRep catalog signatures emptyFunctions [4, 8] [.word, .integer]
    boxType sourceValue coreValue (.namedData ⟨0⟩) :=
  represented.extend ⟨[4, 8], rfl⟩ ⟨[.word, .integer], rfl⟩

/-- The full payload model uses the same source/Core location map API. -/
example : GenericHeap.HeapRepresents model [0] [OptionalCell.cellType (.namedData ⟨0⟩)]
    ⟨[⟨boxType, some sourceValue, none⟩]⟩ [.inRight .unit coreValue] := by
  exact (GenericHeap.HeapRepresents.empty.allocate (.initialized represented) .append).1

/-- A missing mapping default is still authenticated through the actual raw
proxy identity and actual catalog layout. -/
example : ValueRep catalog signatures emptyFunctions [] [] (.comptime mappingType)
    (.mapping (.comptime .word) proxyType []) (Core.OrderedMapping.encode layout []) layout.type := by
  apply default_represents_at layouts (by rfl)
  exact .comptime (.mapping _ _ _ (by rfl))

/-- Changing the raw identity inside a proxy is rejected even if its runtime
projection would erase the same outer staging wrapper. -/
example : (SourceCoreDataValues.encode 40 context proxyType (.proxy .integer)).toOption.isNone = true := by cbv

/-- Registered Core typing alone cannot authenticate source constructor
payload metadata; the public encoder rejects this tampering. -/
example : (SourceCoreDataValues.encode 40 context boxType
    (.constructed { metadata with payloadTypes := [.integer] } [.integer 0])).toOption.isNone = true := by cbv

end Tests.SourceCoreDataPayload
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPayloadFaults
/-! A default-created inner mapping whose function value has no default.
Both nested lookup helpers run, but neither insertion nor the replacement
expression runs after the inner failure. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreDataPayloadFaults
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceMappingIndex DataEquality DataEqualityValues DataPatternValues
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"place_path_faults", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def keyId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functionType : TypeSystem.Ty := .function .unit .unit
private def innerType : TypeSystem.Ty := .mapping .integer functionType
private def innerLayout : Core.OrderedMapping.Layout := ⟨.integer, TaggedFunction.functionType .unit .unit, ⟨0⟩⟩
private def outerLayout : Core.OrderedMapping.Layout := ⟨.integer, innerLayout.type, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := innerType, definition := some innerLayout.definition },
  { sourceType := .mapping .integer innerType, definition := some outerLayout.definition }]
}
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def route : Route := ⟨.mapping .integer innerType, outerLayout.type, innerLayout.valueType,
  [.index outerLayout (keyId 0) innerType, .index innerLayout (keyId 1) functionType], some outerLayout⟩
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok value => rfl
private theorem comparisonExists : (SourceCoreDataEquality.prepare 20 checked .integer).toOption.isSome = true := by cbv
private def comparison := (SourceCoreDataEquality.prepare 20 checked .integer).toOption.get comparisonExists
private theorem comparisonGenerated : SourceCoreDataEquality.prepare 20 checked .integer = .ok comparison := except_get _ comparisonExists
private theorem innerDefaultExists : (SourceCoreDefaultValue.prepare (functionType.size + 1) checked functionType).toOption.isSome = true := by cbv
private def innerDefault := (SourceCoreDefaultValue.prepare (functionType.size + 1) checked functionType).toOption.get innerDefaultExists
private theorem innerDefaultGenerated : SourceCoreDefaultValue.prepare (functionType.size + 1) checked functionType = .ok innerDefault := except_get _ innerDefaultExists
private theorem outerDefaultExists : (SourceCoreDefaultValue.prepare (innerType.size + 1) checked innerType).toOption.isSome = true := by cbv
private def outerDefault := (SourceCoreDefaultValue.prepare (innerType.size + 1) checked innerType).toOption.get outerDefaultExists
private theorem outerDefaultGenerated : SourceCoreDefaultValue.prepare (innerType.size + 1) checked innerType = .ok outerDefault := except_get _ outerDefaultExists
private def innerIndex : PreparedIndex := ⟨innerLayout, keyId 1, 1, comparison.expression, innerDefault.expression, Word.zero⟩
private def outerIndex : PreparedIndex := ⟨outerLayout, keyId 0, 0, comparison.expression, outerDefault.expression, Word.zero⟩
private def prepared : Prepared := ⟨route, [.index outerIndex, .index innerIndex], [(keyId 0, .integer), (keyId 1, .integer)], Word.zero⟩
private def innerCertificate : Index checked functionType innerIndex := Index.of_generated comparisonGenerated innerDefaultGenerated rfl rfl
private def outerCertificate : Index checked innerType outerIndex := Index.of_generated comparisonGenerated outerDefaultGenerated rfl rfl
private theorem accepted : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared := by
  have inner : checked.catalog.entries[0]? = some ⟨innerType, some innerLayout.definition, []⟩ := rfl
  have outer : checked.catalog.entries[1]? = some ⟨.mapping .integer innerType, some outerLayout.definition, []⟩ := rfl
  have innerDefaultCompiled := innerDefaultGenerated
  have outerDefaultCompiled := outerDefaultGenerated
  simp only [innerType, functionType] at innerDefaultCompiled outerDefaultCompiled
  simp [prepare, route, innerLayout, outerLayout, inner, outer, innerType,
    comparisonGenerated, innerDefaultCompiled, outerDefaultCompiled, functionType,
    prepared, innerIndex, outerIndex, bind, Except.bind, pure, Except.pure, Except.mapError]
open DataPayload DataPayloadReadPaths
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) :=
  fun impossible => False.elim impossible
private theorem faithful : IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero =>
    cases selected
    exact ⟨_, _, rfl, rfl, ⟨.integer, Core.Ty.isWellFormed_sound (by decide), rfl⟩⟩
  | succ index => cases index with
    | zero => cases selected; exact ⟨_, _, rfl, rfl, ⟨.integer, .namedData (by rfl), rfl⟩⟩
    | succ index => simp [catalog] at selected
private def keys : List Value := [.integer 9, .integer 7]
private def outerEmpty : Value := Core.OrderedMapping.encode outerLayout []
private def source : Dynamic.Value := .mapping .integer innerType []
private def projections : List Dynamic.EvaluatedProjection := [.index (.integer 9), .index (.integer 7)]
private theorem represented : DataPayload.ValueRep catalog signatures functions [] [] (.mapping .integer innerType)
    source outerEmpty outerLayout.type :=
  .mapping rfl rfl rfl ⟨.integer, .namedData (by rfl), rfl⟩ (.empty _ _ _ _)
private theorem path : Path checked signatures functions [] [] keys (.mapping .integer innerType) outerLayout.type
    prepared.steps projections functionType innerLayout.valueType 6 := by
  apply Path.index (count := 3) outerCertificate rfl rfl (.integer 9) rfl
  apply Path.index (count := 0) innerCertificate rfl rfl (.integer 7) rfl
  exact .nil rfl
private theorem sourceFault : Dynamic.ProjectionsFaults (some source) projections (.missingMappingDefault functionType) :=
  .indexDefault (.integer 9) .nil (.mapping _ _) (.indexDefaultUnavailable (.integer 7) .nil (by intro impossible; cases impossible))

/-- Automatic fault correspondence consumes the independent source fault and
full payload, including the generated default-created inner mapping. -/
example : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared ∧
    ∃ token finalStore admin,
      Evaluates [outerEmpty, packValues keys] [.integer 900]
        (select prepared prepared.steps (.var 0) (.var 1)) (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      Evaluates [outerEmpty, packValues keys] [.integer 900]
        (update prepared prepared.steps outerLayout.type (.var 0) (.var 1) (.apply .unit .unit))
        (.inLeft outerLayout.type (.word token)) finalStore ∧
      finalStore = [.integer 900] ++ admin ∧ admin.length ≤ 6 :=
  ⟨accepted, path.fault_preserves observations faithful layouts prepared rfl represented sourceFault
    [outerEmpty, packValues keys] [.integer 900] (.var 0) (.var 1) (.apply .unit .unit) (.var rfl) (.var rfl)⟩

example : (match runStateful 2000 (.initial
    (update prepared prepared.steps outerLayout.type (.var 0) (.var 1) (.apply .unit .unit))
    [outerEmpty, packValues keys] [.integer 900]) with
    | .done value store => value == .inLeft outerLayout.type (.word Word.zero) && store.length == 7 && store[0]? == some (.integer 900)
    | _ => false) = true := by cbv

end Tests.SourceCoreDataPayloadFaults
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPayloadMapping
/-! Non-reflexive mapping keys append even when structurally identical. The
actual helper retains the complete contents of both old and appended keys. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreDataPayloadMapping
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering DataPayload DataPatternValues
private def innerType : TypeSystem.Ty := .mapping .integer .integer
private def innerLayout : Core.OrderedMapping.Layout := ⟨.integer, .integer, ⟨0⟩⟩
private def outerLayout : Core.OrderedMapping.Layout := ⟨innerLayout.type, .integer, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := innerType, definition := some innerLayout.definition },
  { sourceType := .mapping innerType .integer, definition := some outerLayout.definition }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) :=
  fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem comparisonExists : (SourceCoreDataEquality.prepare 20 checked innerType).toOption.isSome = true := by cbv
private def comparison := (SourceCoreDataEquality.prepare 20 checked innerType).toOption.get comparisonExists
private theorem comparisonGenerated : SourceCoreDataEquality.prepare 20 checked innerType = .ok comparison := by
  generalize result : SourceCoreDataEquality.prepare 20 checked innerType = outcome
  have positive := comparisonExists
  rw [result] at positive
  cases outcome with
  | error => simp [Except.toOption] at positive
  | ok prepared => simp [comparison, result]; rfl
private theorem comparisonType : outerLayout.keyType = comparison.type := by
  have projected := comparison.projection
  rw [DataPlaceMappingPreparation.comparison_sourceType comparisonGenerated] at projected
  exact Except.ok.inj projected
private def sourceKey : Dynamic.Value := .mapping .integer .integer [(.integer 2, .integer 3)]
private def key : Value := Core.OrderedMapping.encode innerLayout [(.integer 2, .integer 3)]
private def original : Core.OrderedMapping.Entries := [(key, .integer 11)]
private def sources : List (Dynamic.Value × Dynamic.Value) := [(sourceKey, .integer 11)]
private def updated : List (Dynamic.Value × Dynamic.Value) := [(sourceKey, .integer 11), (sourceKey, .integer 22)]
private theorem keyRep : ValueRep catalog signatures functions [] [] innerType sourceKey key innerLayout.type :=
  .mapping rfl rfl rfl ⟨.integer, .integer, rfl⟩ (.prepend (.integer 2) (.integer 3) (.empty _ _ _ _))
private theorem entriesRep : EntriesRep catalog signatures functions [] [] innerType .integer outerLayout.keyType .integer sources original :=
  .prepend keyRep (.integer 11) (.empty _ _ _ _)
private theorem inserted : Dynamic.MappingInsert sourceKey (.integer 22) sources updated := by
  apply Dynamic.MappingInsert.append
  apply Dynamic.MappingAbsent.cons
  · intro equivalent
    have impossible := equivalent.2
    cases impossible
  · exact .nil
private def expression : Expr := Core.OrderedMapping.insert outerLayout comparison.expression (.var 0) (.var 1) (.var 2)
private def environment : Environment := [Core.OrderedMapping.encode outerLayout original, key, .integer 22]
private def initialStore : Store := [.integer 900]

/-- Full payload preservation comes from the actual compiled comparator and
insert code; it is not inferred from weak equality observations of keys. -/
example : ∃ output required,
    ValueRep catalog signatures functions [] [] (.mapping innerType .integer)
      (.mapping innerType .integer updated) output outerLayout.type ∧
    ∀ fuel, required ≤ fuel → runStateful fuel (.initial expression environment initialStore) =
      .done (.inRight .word output)
        (DataMappingComparison.insertStore comparison outerLayout environment initialStore original key (.integer 22)) := by
  obtain ⟨output, represented, evaluated⟩ := DataPayload.insert_preserves observations faithful comparison outerLayout comparisonType
    rfl rfl rfl ⟨.namedData (by rfl), .integer, rfl⟩ keyRep (.integer 22) entriesRep inserted
    environment initialStore (.var 0) (.var 1) (.var 2) (.var rfl) (.var rfl) (.var rfl)
  obtain ⟨required, complete⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨output, required, represented, complete⟩

/-- The finite run appends a second identical mapping key; it preserves the
old value and both keys' nested data, and the administrative prefix. -/
example : ∃ store, runStateful 1000 (.initial expression environment initialStore) =
    .done (.inRight .word (Core.OrderedMapping.encode outerLayout [(key, .integer 11), (key, .integer 22)])) store ∧
    store.read? 0 = some (.integer 900) := by
  refine ⟨DataMappingComparison.insertStore comparison outerLayout environment initialStore original key (.integer 22), ?_, ?_⟩
  · cbv
  · rfl

end Tests.SourceCoreDataPayloadMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPayloadPaths
/-! Public encoding and actual route preparation supply a nested read tree.
All equality/default evaluations are generated by the semantic proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreDataPayloadPaths
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open DataPayload DataPayloadEncoding DataPayloadReadPaths SourceCoreDataPlaces DataPlaceMappingIndex
private def innerType : TypeSystem.Ty := .mapping .integer .integer
private def outerType : TypeSystem.Ty := .mapping .integer innerType
private def innerLayout : Core.OrderedMapping.Layout := ⟨.integer, .integer, ⟨0⟩⟩
private def outerLayout : Core.OrderedMapping.Layout := ⟨.integer, innerLayout.type, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := innerType, definition := some innerLayout.definition },
  { sourceType := outerType, definition := some outerLayout.definition }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceCoreDataValues.Context := ⟨checked, signatures⟩
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) :=
  fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero => cases selected; exact ⟨.integer, .integer, rfl, rfl, ⟨.integer, .integer, rfl⟩⟩
  | succ index => cases index with
    | zero => cases selected; exact ⟨.integer, .namedData ⟨0⟩, rfl, rfl, ⟨.integer, .namedData (by rfl), rfl⟩⟩
    | succ index => simp [catalog] at selected
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok => rfl
private theorem comparisonExists : (SourceCoreDataEquality.prepare 20 checked .integer).toOption.isSome = true := by cbv
private def comparison := (SourceCoreDataEquality.prepare 20 checked .integer).toOption.get comparisonExists
private theorem comparisonGenerated : SourceCoreDataEquality.prepare 20 checked .integer = .ok comparison := except_get _ comparisonExists
private theorem innerDefaultExists : (SourceCoreDefaultValue.prepare (innerType.size + 1) checked innerType).toOption.isSome = true := by cbv
private def innerDefault := (SourceCoreDefaultValue.prepare (innerType.size + 1) checked innerType).toOption.get innerDefaultExists
private theorem innerDefaultGenerated : SourceCoreDefaultValue.prepare (innerType.size + 1) checked innerType = .ok innerDefault := except_get _ innerDefaultExists
private theorem integerDefaultExists : (SourceCoreDefaultValue.prepare (TypeSystem.Ty.integer.size + 1) checked .integer).toOption.isSome = true := by cbv
private def integerDefault := (SourceCoreDefaultValue.prepare (TypeSystem.Ty.integer.size + 1) checked .integer).toOption.get integerDefaultExists
private theorem integerDefaultGenerated : SourceCoreDefaultValue.prepare (TypeSystem.Ty.integer.size + 1) checked .integer = .ok integerDefault := except_get _ integerDefaultExists
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"payload_path", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def keyId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def innerIndex : PreparedIndex := ⟨innerLayout, keyId 1, 1, comparison.expression, integerDefault.expression, Word.zero⟩
private def outerIndex : PreparedIndex := ⟨outerLayout, keyId 0, 0, comparison.expression, innerDefault.expression, Word.zero⟩
private def route : Route := ⟨outerType, outerLayout.type, .integer,
  [.index outerLayout (keyId 0) innerType, .index innerLayout (keyId 1) .integer], some outerLayout⟩
private def prepared : Prepared := ⟨route, [.index outerIndex, .index innerIndex], [(keyId 0, .integer), (keyId 1, .integer)], Word.zero⟩
private theorem accepted : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared := by
  have outer : checked.catalog.entries[1]? = some ⟨outerType, some outerLayout.definition, []⟩ := rfl
  have inner : checked.catalog.entries[0]? = some ⟨innerType, some innerLayout.definition, []⟩ := rfl
  have innerGenerated := innerDefaultGenerated
  simp only [innerType] at innerGenerated
  simp [prepare, route, innerLayout, outerLayout, outer, inner, outerType, innerType,
    comparisonGenerated, innerGenerated, integerDefaultGenerated,
    prepared, innerIndex, outerIndex, bind, Except.bind, pure, Except.pure, Except.mapError]
private def publicValue : SourceCoreDataValues.Value := .mapping .integer innerType [
  (.integer 9, .mapping .integer .integer [(.integer 7, .integer 11), (.integer 7, .integer 22)])]
private def sourceValue : Dynamic.Value := .mapping .integer innerType [
  (.integer 9, .mapping .integer .integer [(.integer 7, .integer 11), (.integer 7, .integer 22)])]
private def coreValue : Value := Core.OrderedMapping.encode outerLayout [
  (.integer 9, Core.OrderedMapping.encode innerLayout [(.integer 7, .integer 11), (.integer 7, .integer 22)])]
private theorem meaning : Means publicValue sourceValue :=
  .mapping (.prepend (.integer 9) (.mapping (.prepend (.integer 7) (.integer 11) (.prepend (.integer 7) (.integer 22) .empty))) .empty)
private theorem encoded : SourceCoreDataValues.encode 40 context outerType publicValue = .ok coreValue := by cbv
private theorem represented : ValueRep catalog signatures functions [] [] outerType sourceValue coreValue outerLayout.type :=
  encodes_represents_at layouts meaning rfl (SourceCoreDataValues.encodes_of_encode encoded)
private def keys : List Value := [.integer 9, .integer 7]
private def projections : List Dynamic.EvaluatedProjection := [.index (.integer 9), .index (.integer 7)]
private theorem path : Path checked signatures functions [] [] keys outerType outerLayout.type prepared.steps projections .integer .integer 6 := by
  apply Path.index (count := 3) (Index.of_generated comparisonGenerated innerDefaultGenerated rfl rfl) rfl rfl (.integer 9) rfl
  apply Path.index (count := 0) (Index.of_generated comparisonGenerated integerDefaultGenerated rfl rfl) rfl rfl (.integer 7) rfl
  exact .nil rfl
private theorem sourceRead : Dynamic.ProjectionsRead (some sourceValue) projections (some (.integer 11)) :=
  .indexFound (.head ⟨rfl, .integer 9⟩) (.indexFound (.head ⟨rfl, .integer 7⟩) .nil)

/-- The source read, full public payload, and actual helper preparations imply
finite Core completion. No recursive read-tree nodes are supplied by hand. -/
example : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared ∧
    ∃ finalStore required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (select prepared prepared.steps (.var 0) (.var 1))
        [coreValue, DataPatternValues.packValues keys] [.integer 900]) =
        .done (.inRight .word (.inRight .unit (.integer 11))) finalStore := by
  have tree := path.read_tree observations layouts prepared represented sourceRead
  obtain ⟨leaf, finalStore, admin, read, represented, evaluated, extended, counted⟩ :=
    tree.preserves faithful rfl [coreValue, DataPatternValues.packValues keys] [.integer 900] (.var 0) (.var 1) (.var rfl) (.var rfl)
  cases represented with
  | integer =>
    obtain ⟨required, complete⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
    exact ⟨accepted, finalStore, required, complete⟩

private def updatedSource : Dynamic.Value := .mapping .integer innerType [
  (.integer 9, .mapping .integer .integer [(.integer 7, .integer 55), (.integer 7, .integer 22)])]
private def updatedCore : Value := Core.OrderedMapping.encode outerLayout [
  (.integer 9, Core.OrderedMapping.encode innerLayout [(.integer 7, .integer 55), (.integer 7, .integer 22)])]
private theorem sourceUpdate : Dynamic.ProjectionsUpdate (fun _ new => new = Dynamic.Value.integer 55)
    (some sourceValue) projections updatedSource :=
  .indexFound (.head ⟨rfl, .integer 9⟩)
    (.indexFound (.head ⟨rfl, .integer 7⟩) (.leaf rfl) (.update (.head ⟨rfl, .integer 7⟩)))
    (.update (.head ⟨rfl, .integer 9⟩))

/-- Complete keys and untouched duplicate entries survive reconstruction.
The actual recursive helper evaluations are consequences of the theorem. -/
example : ∃ output finalStore admin required,
    ValueRep catalog signatures functions [] [] outerType updatedSource output outerLayout.type ∧
    finalStore = [.integer 900] ++ admin ∧ admin.length = 12 ∧
    ∀ fuel, required ≤ fuel → runStateful fuel
      (.initial (update prepared prepared.steps outerLayout.type (.var 0) (.var 1) (.var 2))
        [coreValue, DataPatternValues.packValues keys, .integer 55] [.integer 900]) = .done (.inRight .word output) finalStore := by
  obtain ⟨output, finalStore, admin, represented, evaluated, extended, counted⟩ :=
    path.update_preserves observations faithful layouts prepared rfl represented (.integer 55) sourceUpdate
      [coreValue, DataPatternValues.packValues keys, .integer 55] [.integer 900] (.var 0) (.var 1) (.var 2)
      (.var rfl) (.var rfl) (.var rfl)
  obtain ⟨required, complete⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨output, finalStore, admin, required, represented, extended, counted, complete⟩

example : (match runStateful 2000
    (.initial (update prepared prepared.steps outerLayout.type (.var 0) (.var 1) (.var 2))
      [coreValue, DataPatternValues.packValues keys, .integer 55] [.integer 900]) with
    | .done value _ => some value
    | _ => none) = some (.inRight .word updatedCore) := by cbv

end Tests.SourceCoreDataPayloadPaths
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPayloadWriteBack
/-! A commit consumer preserves an unmapped administrative cell and two
references to the same mapped source location. The source snapshot may precede
the latest cell, which is the one reconstructed and written. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataPayloadWriteBack
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces GeneralHeap GenericHeap DataEquality DataPayload DataPayloadReadPaths
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functions : PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private def model := payloadModel catalog signatures functions
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) :=
  fun impossible => False.elim impossible
private theorem layouts : CatalogLayouts catalog := by
  constructor <;> intros <;> contradiction
private def prepared : Prepared := ⟨⟨.integer, .integer, .integer, [], none⟩, [], [], Word.zero⟩
private def cell : Dynamic.Cell := ⟨.integer, some (.integer 7), none⟩
private def heap : Dynamic.Heap := ⟨[cell]⟩
private def world : StoreTyping := [.sum .unit .integer, .integer]
private def store : Store := [.inRight .unit (.integer 7), .integer 900]
private def argument : Value := .pair (.inRight .unit (.integer 7)) (.pair .unit (.integer 55))
private def environment : Environment := [.cellRef (.sum .unit .integer) 0, .cellRef (.sum .unit .integer) 0, argument]
private def context : Core.Context := [.cell (.sum .unit .integer), .cell (.sum .unit .integer),
  .product (.sum .unit .integer) (.product .unit .integer)]
private theorem related : HeapRepresents model [0] world heap store := by
  have empty : HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  have represented : model.Represents [] [] .integer (.integer 7) (.integer 7) .integer := .integer 7
  exact (empty.allocate (.initialized represented) .append).1.allocate_administrative .integer
private theorem environmentTyped : RuntimeEnvironmentHasTypes world environment context catalog.definitions :=
  .cons (.cellRef rfl) (.cons (.cellRef rfl) (.cons (.pair (.inRight .integer) (.pair .unit .integer)) .nil))
private theorem faithful : IdentityFaithful (fun _ _ => False) := by constructor <;> intros <;> contradiction
private def liveArgument : Expr := .pair (.loadCell (.var 1)) (.pair .unit (.integer 55))
private def expression : Expr := DataPlaceWriteBack.commit prepared .unit (.var 0) liveArgument

example : ∃ updatedValue finalHeap finalStore futureWorld,
    Dynamic.ResolvedPlaceWrites (fun _ value => value = .integer 55) heap
      ⟨⟨0⟩, .integer, .integer, [], some (.integer 3)⟩ (.integer 55) finalHeap ∧
    Evaluates environment store expression (.inRight .word .unit) finalStore ∧
    WorldExtends world futureWorld ∧ HeapRepresents model [0] futureWorld finalHeap finalStore ∧
    model.Represents [0] futureWorld .integer (.integer 55) updatedValue .integer ∧
    finalStore.read? 0 = some (.inRight .unit updatedValue) ∧ AdministrativePreserved [0] store [0] finalStore := by
  have path : Path checked signatures functions [0] world [] cell.type .integer [] [] .integer .integer 0 := .nil rfl
  exact DataPayloadWriteBack.commit_preserves observations faithful layouts prepared rfl path related ⟨rfl, rfl⟩ (.intro .head) rfl
    (.initialized .integer (.integer 7) (.integer 7)) (.integer 7) (.integer 55) (.leaf rfl) environmentTyped
    (infer_sound (by decide)) (.var rfl) (.pair (.loadCell (.var rfl) rfl) (.pair .unit .integer)) (some (.integer 3))

private def observeAliases : Expr := .letE expression
  (LanguageResult.success (.pair (.loadCell (.var 1)) (.loadCell (.var 2))))
example : infer? context observeAliases = some (.sum .word (.product (.sum .unit .integer) (.sum .unit .integer))) := by
  simp [observeAliases, expression, liveArgument, DataPlaceWriteBack.commit, prepared, setter, LanguageResult.bind,
    LanguageResult.success, OptionalCell.cellType, LanguageResult.resultType, Expr.weakenAt]
  decide
example : runStateful 100 (.initial observeAliases environment store) =
    .done (.inRight .word (.pair (.inRight .unit (.integer 55)) (.inRight .unit (.integer 55))))
      [.inRight .unit (.integer 55), .integer 900] := by cbv

end Tests.SourceCoreDataPayloadWriteBack
end
