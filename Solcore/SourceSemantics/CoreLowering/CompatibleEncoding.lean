import Solcore.SourceSemantics.CoreLowering.CompatibleEncodingMapping

/-! Successful execution of the actual compatible encoder produces the
independent source/native representation. The induction follows its real
fuel and registry extensions. Public encoding supplies the final native
shape validation; native typing alone never authenticates source metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
open Core Frontend Frontend.SourceInference GeneralHeap CompatiblePayload
open SourceCoreCompatibleValues (encodeRaw)
variable {checked : Checked} {functions : FunctionModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}

private theorem unit_sound {fuel : Nat} {registry : Registry} {expected : TypeSystem.Ty}
     {encoded : Extended registry Value} {type : Ty}
    (accepted : encodeRaw (fuel + 1) checked registry expected .unit = .ok encoded)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means .unit source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type := by
  cases erased : SourceCoreRawMetadata.runtimeType expected <;>
    (unfold encodeRaw at accepted; rw [erased] at accepted)
  all_goals try (solve | cases accepted)
  case constructor id =>
    cases id with
    | declaration => cases accepted
    | builtin builtin =>
      cases builtin <;> try (solve | cases accepted)
      case unit =>
        cases accepted
        cases typed
        exact ⟨_, .unit, .compatible (actual := .unit) erased (.unit)⟩

private theorem bool_sound {fuel : Nat} {registry : Registry} {expected : TypeSystem.Ty}
    (value : Bool) {encoded : Extended registry Value} {type : Ty}
    (accepted : encodeRaw (fuel + 1) checked registry expected (.bool value) = .ok encoded)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means (.bool value) source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type := by
  cases erased : SourceCoreRawMetadata.runtimeType expected <;>
    (unfold encodeRaw at accepted; rw [erased] at accepted)
  all_goals try (solve | cases accepted)
  case constructor id =>
    cases id with
    | declaration => cases accepted
    | builtin builtin =>
      cases builtin <;> try (solve | cases accepted)
      case bool =>
        cases accepted
        cases typed
        exact ⟨_, .bool value, .compatible (actual := .bool) erased (.bool value)⟩

private theorem word_sound {fuel : Nat} {registry : Registry} {expected : TypeSystem.Ty}
    (value : Word) {encoded : Extended registry Value} {type : Ty}
    (accepted : encodeRaw (fuel + 1) checked registry expected (.word value) = .ok encoded)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means (.word value) source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type := by
  cases erased : SourceCoreRawMetadata.runtimeType expected <;>
    (unfold encodeRaw at accepted; rw [erased] at accepted)
  all_goals try (solve | cases accepted)
  case constructor id =>
    cases id with
    | declaration => cases accepted
    | builtin builtin =>
      cases builtin <;> try (solve | cases accepted)
      case word =>
        cases accepted
        cases typed
        exact ⟨_, .word value, .compatible (actual := .word) erased (.word value)⟩

private theorem integer_sound {fuel : Nat} {registry : Registry} {expected : TypeSystem.Ty}
    (value : Int) {encoded : Extended registry Value} {type : Ty}
    (accepted : encodeRaw (fuel + 1) checked registry expected (.integer value) = .ok encoded)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means (.integer value) source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type := by
  cases erased : SourceCoreRawMetadata.runtimeType expected <;>
    (unfold encodeRaw at accepted; rw [erased] at accepted)
  all_goals try (solve | cases accepted)
  case constructor id =>
    cases id with
    | declaration => cases accepted
    | builtin builtin =>
      cases builtin <;> try (solve | cases accepted)
      case integer =>
        cases accepted
        cases typed
        exact ⟨_, .integer value, .compatible (actual := .integer) erased (.integer value)⟩

private theorem raw_succ {fuel : Nat} (raw : RawSound checked functions mapping world fuel)
    (payload : PayloadSound checked functions mapping world fuel) (entries : EntriesSound checked functions mapping world fuel) :
    RawSound checked functions mapping world (fuel + 1) := by
  intro registry owner expected carrier encoded type accepted projected typed
  cases carrier with
  | unit => exact unit_sound accepted typed
  | bool value => exact bool_sound value accepted typed
  | word value => exact word_sound value accepted typed
  | integer value => exact integer_sound value accepted typed
  | constructed metadata carriers => exact constructed_sound payload owner accepted projected typed
  | product left right =>
    cases erased : SourceCoreRawMetadata.runtimeType expected
    case product leftType rightType => exact product_sound raw owner erased accepted projected typed
    all_goals
      unfold encodeRaw at accepted
      rw [erased] at accepted
    all_goals try (solve | cases accepted)
    case constructor id =>
      cases id with
      | declaration => cases accepted
      | builtin builtin => cases builtin <;> cases accepted
  | proxy actual =>
    cases erased : SourceCoreRawMetadata.runtimeType expected
    case proxy inner => exact proxy_sound erased accepted typed
    all_goals
      unfold encodeRaw at accepted
      rw [erased] at accepted
    all_goals try (solve | cases accepted)
    case constructor id =>
      cases id with
      | declaration => cases accepted
      | builtin builtin => cases builtin <;> cases accepted
  | mapping actualKey actualValue carriers =>
    cases erased : SourceCoreRawMetadata.runtimeType expected
    case mapping keyType valueType => exact mapping_sound raw entries owner erased accepted projected typed
    all_goals
      unfold encodeRaw at accepted
      rw [erased] at accepted
    all_goals try (solve | cases accepted)
    case constructor id =>
      cases id with
      | declaration => cases accepted
      | builtin builtin => cases builtin <;> cases accepted

/-- All mutually recursive encoder components are closed by one ordinary
natural-number induction. Children and default execution are derived from the
accepted real encoder computation, never retained as external hypotheses. -/
theorem raw_sound (fuel : Nat) : RawSound checked functions mapping world fuel ∧
    PayloadSound checked functions mapping world fuel ∧ EntriesSound checked functions mapping world fuel := by
  induction fuel with
  | zero =>
    refine ⟨?_, payload_zero, entries_zero⟩
    intro registry owner expected carrier encoded type accepted projected typed
    unfold encodeRaw at accepted
    cases accepted
  | succ fuel ih => exact ⟨raw_succ ih.1 ih.2.1 ih.2.2, payload_succ ih.1 ih.2.1, entries_succ ih.1 ih.2.2⟩

theorem encodeRaw_represents {fuel : Nat} {registry : Registry} (owner : registry.signatures = checked.signatures)
    {expected : TypeSystem.Ty} {carrier : PublicValue} {encoded : Extended registry Value} {type : Ty}
    (accepted : encodeRaw fuel checked registry expected carrier = .ok encoded)
    (projected : checked.catalog.project expected = .ok type)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means carrier source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type :=
  (raw_sound fuel).1 registry owner expected carrier encoded type accepted projected typed

/-- Public successful encoding supplies the actual native typing receipt and
its original encoder equation. No catalog layout premise is required beyond
the checks actually performed by this public call. -/
theorem encode_represents {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {functions : FunctionModel context.checked.catalog} {expected : TypeSystem.Ty} {carrier : PublicValue}
    {encoded : SourceCoreCompatibleValues.Encoded fuel context expected carrier}
    (accepted : SourceCoreCompatibleValues.encode fuel context expected carrier = .ok encoded)
    (mapping : LocationMap) (world : StoreTyping) :
    ∃ source, Means carrier source ∧
      ValueRep context.checked encoded.context.registry functions mapping world expected source encoded.value encoded.type := by
  unfold SourceCoreCompatibleValues.encode at accepted
  obtain ⟨generated, generatedEq, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · rename_i decoded decodedEq
    split at accepted
    · cases accepted
      exact encodeRaw_represents context.registryOwner generatedEq decoded.projected (decoded.typed world)
    · cases accepted

theorem encode_represents_at {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {functions : FunctionModel context.checked.catalog} {expected : TypeSystem.Ty} {carrier : PublicValue}
    {encoded : SourceCoreCompatibleValues.Encoded fuel context expected carrier} {source : Dynamic.Value}
    (accepted : SourceCoreCompatibleValues.encode fuel context expected carrier = .ok encoded)
    (meaning : Means carrier source) (mapping : LocationMap) (world : StoreTyping) :
    ValueRep context.checked encoded.context.registry functions mapping world expected source encoded.value encoded.type := by
  obtain ⟨actual, actualMeaning, represented⟩ := encode_represents (functions := functions) accepted mapping world
  have same := actualMeaning.functional meaning
  subst actual
  exact represented

/-- A standalone decoded receipt exposes an authenticated re-encoding under
an extension of its registry. This statement retains that extension explicitly
and does not identify it with the original registry. -/
theorem decoded_represents_extended {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {functions : FunctionModel context.checked.catalog} {expected : TypeSystem.Ty} {value : Value}
    (decoded : SourceCoreCompatibleValues.Decoded fuel context expected value)
    (mapping : LocationMap) (world : StoreTyping) :
    ∃ registry source, SourceCoreRawMetadata.Extends context.registry registry ∧ Means decoded.source source ∧
      ValueRep context.checked registry functions mapping world expected source value decoded.type := by
  obtain ⟨generated, generatedEq, same⟩ := decoded.reencodes
  obtain ⟨source, meaning, represented⟩ := encodeRaw_represents (functions := functions) (mapping := mapping)
    context.registryOwner generatedEq decoded.projected (by rw [same]; exact decoded.typed world)
  exact ⟨generated.registry, source, generated.preserves, meaning, same ▸ represented⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
