import Solcore.SourceSemantics.CoreLowering.CompatiblePayload
import Solcore.Frontend.SourceRuntimeValues

/-! The pure runtime default constructor agrees with the independent source
semantics. Its original source types are retained: runtime type erasure is
never used to choose a default. The carrier relation below is structural and
has no evaluator, codec, or generated-expression premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend GeneralHeap

/-- The data shapes that the pure default constructor can produce. Raw proxy
and empty-mapping metadata is equal on both sides. -/
inductive DefaultData : SourceTypedRuntime.Value → Dynamic.Value → Prop where
  | unit : DefaultData .unit .unit
  | bool (value : Bool) : DefaultData (.bool value) (.bool value)
  | word (value : Word) : DefaultData (.word value) (.word value)
  | integer (value : Int) : DefaultData (.integer value) (.integer value)
  | product {a b : SourceTypedRuntime.Value} {left right : Dynamic.Value}
      (first : DefaultData a left) (second : DefaultData b right) :
      DefaultData (.product a b) (.product left right)
  | proxy (inner : TypeSystem.Ty) : DefaultData (.proxy inner) (.proxy inner)
  | mapping (key value : TypeSystem.Ty) :
      DefaultData (.mapping key value []) (.mapping key value [])

theorem DefaultData.functional {raw : SourceTypedRuntime.Value} {a b : Dynamic.Value}
    (first : DefaultData raw a) (second : DefaultData raw b) : a = b := by
  induction first generalizing b with
  | product _ _ first second =>
    cases ‹DefaultData _ b› with
    | product a b => rw [first a, second b]
  | unit | bool | word | integer | proxy | mapping => cases second; rfl

/-- Every successful pure constructor has an independent default meaning,
including the exact un-erased metadata of proxy and mapping leaves. -/
theorem defaultValue?_sound {fuel : Nat} {type : TypeSystem.Ty} {raw : SourceTypedRuntime.Value}
    (found : SourceTypedRuntime.defaultValue? fuel type = some raw) :
    ∃ source, Dynamic.DefaultValue type source ∧ DefaultData raw source := by
  induction fuel generalizing type raw with
  | zero => simp [SourceTypedRuntime.defaultValue?] at found
  | succ fuel ih =>
    cases type with
    | constructor id =>
      cases id with
      | builtin builtin =>
        cases builtin <;> simp [SourceTypedRuntime.defaultValue?] at found <;> subst raw
        · exact ⟨_, .unit, .unit⟩
        · exact ⟨_, .bool, .bool _⟩
        · exact ⟨_, .word, .word _⟩
        · exact ⟨_, .integer, .integer _⟩
      | declaration => simp [SourceTypedRuntime.defaultValue?] at found
    | product left right =>
      cases first : SourceTypedRuntime.defaultValue? fuel left with
      | none => simp [SourceTypedRuntime.defaultValue?, first] at found
      | some a =>
        cases second : SourceTypedRuntime.defaultValue? fuel right with
        | none => simp [SourceTypedRuntime.defaultValue?, first, second] at found
        | some b =>
          simp [SourceTypedRuntime.defaultValue?, first, second] at found
          subst raw
          obtain ⟨aSource, aMeaning, aRep⟩ := ih first
          obtain ⟨bSource, bMeaning, bRep⟩ := ih second
          exact ⟨_, .product aMeaning bMeaning, .product aRep bRep⟩
    | proxy inner =>
      simp [SourceTypedRuntime.defaultValue?] at found
      subst raw
      exact ⟨_, .proxy _, .proxy _⟩
    | mapping key value =>
      simp [SourceTypedRuntime.defaultValue?] at found
      subst raw
      exact ⟨_, .mapping _ _, .mapping _ _⟩
    | comptime inner =>
      obtain ⟨source, meaning, represented⟩ := ih found
      exact ⟨source, .comptime meaning, represented⟩
    | «variable» | parameter | application | function | error => simp [SourceTypedRuntime.defaultValue?] at found

/-- A structural source-size bound suffices; this is compile-time constructor
fuel and has no relationship to Core execution fuel. -/
theorem defaultValue?_complete {type : TypeSystem.Ty} {source : Dynamic.Value}
    (meaning : Dynamic.DefaultValue type source) :
    ∀ fuel, type.size < fuel → ∃ raw,
      SourceTypedRuntime.defaultValue? fuel type = some raw ∧ DefaultData raw source := by
  induction meaning with
  | unit | bool | word | integer | proxy | mapping =>
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => exact ⟨_, rfl, by constructor⟩
  | @product leftType rightType left right _ _ first second =>
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [TypeSystem.Ty.size] at bound
      obtain ⟨a, aFound, aRep⟩ := first fuel (by omega)
      obtain ⟨b, bFound, bRep⟩ := second fuel (by omega)
      exact ⟨_, by simp [SourceTypedRuntime.defaultValue?, aFound, bFound], .product aRep bRep⟩
  | @comptime inner source _ ih =>
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [TypeSystem.Ty.size] at bound
      exact ih fuel (by omega)

theorem defaultValue?_absent_iff {fuel : Nat} {type : TypeSystem.Ty} (enough : type.size < fuel) :
    SourceTypedRuntime.defaultValue? fuel type = none ↔ ¬ Dynamic.Defaultable type := by
  constructor
  · intro absent existsDefault
    obtain ⟨source, meaning⟩ := existsDefault.exists_default
    obtain ⟨raw, found, _⟩ := defaultValue?_complete meaning fuel enough
    rw [absent] at found
    contradiction
  · intro missing
    cases found : SourceTypedRuntime.defaultValue? fuel type with
    | none => rfl
    | some raw =>
      obtain ⟨source, meaning, _⟩ := defaultValue?_sound found
      exact False.elim (missing meaning.defaultable)

theorem defaultValue?_canonical {type : TypeSystem.Ty} {source : Dynamic.Value}
    (meaning : Dynamic.DefaultValue type source) :
    ∃ raw, SourceTypedRuntime.defaultValue? (type.size + 1) type = some raw ∧ DefaultData raw source :=
  defaultValue?_complete meaning _ (by omega)

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}

/-- A transported default is present exactly when the original raw source
type has a default. Its native carrier may recursively contain mappings and
raw proxy metadata. -/
theorem DefaultRep.isSome_iff {type : TypeSystem.Ty} {fallback : Option Value} {coreType : Ty}
    (represented : DefaultRep checked registry functions mapping world type fallback coreType) :
    fallback.isSome = true ↔ Dynamic.Defaultable type := by
  cases represented with
  | absent missing => simp [missing]
  | present meaning => simp [meaning.defaultable]

theorem DefaultRep.absent_iff {type : TypeSystem.Ty} {fallback : Option Value} {coreType : Ty}
    (represented : DefaultRep checked registry functions mapping world type fallback coreType) :
    fallback = none ↔ ¬ Dynamic.Defaultable type := by
  cases represented with
  | absent missing => simp [missing]
  | present meaning => simp [meaning.defaultable]

/-- This bridge connects the actual pure default computation to an already
authenticated native payload. It does not assume a codec is semantics. -/
theorem DefaultRep.of_computed {fuel : Nat} {type : TypeSystem.Ty} {raw : SourceTypedRuntime.Value}
    {source : Dynamic.Value} {value : Value} {coreType : Ty}
    (found : SourceTypedRuntime.defaultValue? fuel type = some raw)
    (data : DefaultData raw source)
    (represented : ValueRep checked registry functions mapping world type source value coreType) :
    DefaultRep checked registry functions mapping world type (some value) coreType := by
  obtain ⟨actual, meaning, related⟩ := defaultValue?_sound found
  have same := related.functional data
  subst actual
  exact .present meaning represented

theorem DefaultRep.of_absent {fuel : Nat} {type : TypeSystem.Ty} {coreType : Ty}
    (enough : type.size < fuel) (missing : SourceTypedRuntime.defaultValue? fuel type = none)
    (projected : checked.catalog.project type = .ok coreType)
    (wf : coreType.WellFormed checked.catalog.definitions) :
    DefaultRep checked registry functions mapping world type none coreType :=
  .absent ((defaultValue?_absent_iff enough).mp missing) projected wf

/-- Conversely, an independent transported default determines the observable
pure-constructor result. Absence cannot be attributed to exhausted fuel. -/
theorem DefaultRep.computed {fuel : Nat} {type : TypeSystem.Ty} {fallback : Option Value} {coreType : Ty}
    (represented : DefaultRep checked registry functions mapping world type fallback coreType)
    (enough : type.size < fuel) :
    match fallback with
    | none => SourceTypedRuntime.defaultValue? fuel type = none
    | some value => ∃ raw source,
        SourceTypedRuntime.defaultValue? fuel type = some raw ∧ DefaultData raw source ∧
        Dynamic.DefaultValue type source ∧ ValueRep checked registry functions mapping world type source value coreType := by
  cases represented with
  | absent missing => exact (defaultValue?_absent_iff enough).mpr missing
  | present meaning related =>
    obtain ⟨raw, found, data⟩ := defaultValue?_complete meaning fuel enough
    exact ⟨raw, _, found, data, meaning, related⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePayload
