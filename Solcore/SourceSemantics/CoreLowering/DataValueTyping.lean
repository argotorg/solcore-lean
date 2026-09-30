import Solcore.SourceSemantics.CoreLowering.DataPatternAuthenticity

/-! Catalog projection and Core runtime typing for the authenticated finite
scalar/product/nominal value relation used by pattern and member proofs. The
proof checks nominal payload types through the actual constructor resolver;
Core typing alone is not used to authenticate source metadata. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataValueTyping
open Core Frontend Frontend.SourceInference DataPatternValues DataPatternTypedValues

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]

/-- Constructor authentication includes the exact packed payload type stored
in the Core data environment. -/
theorem resolveConstructor_payload {catalog : SourceCoreDataCatalog.Catalog}
    {signatures : ProgramSignatures} {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (accepted : catalog.resolveConstructor signatures metadata = .ok tag) :
    ∃ types, metadata.payloadTypes.mapM catalog.project = .ok types ∧
      catalog.definitions.lookupConstructorPayloadType? tag = some (SourceCoreDataMatches.bundleType types) := by
  unfold SourceCoreDataCatalog.Catalog.resolveConstructor at accepted
  obtain ⟨signature, _, accepted⟩ := bind_ok accepted
  simp only [pure, Except.pure, bind, Except.bind, throw] at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · split at accepted
        · split at accepted
          · split at accepted
            · rename_i tag' selected
              cases projected : metadata.payloadTypes.mapM catalog.project with
              | error error => simp [projected] at accepted
              | ok types =>
                simp only [projected] at accepted
                split at accepted
                · rename_i payload
                  cases accepted
                  refine ⟨types, rfl, payload.trans ?_⟩
                  apply congrArg some
                  clear projected payload
                  induction types with
                  | nil => rfl
                  | cons type rest ih =>
                    cases rest with
                    | nil => rfl
                    | cons => exact congrArg (Ty.product type) ih
                · cases accepted
            · cases accepted
          · cases accepted
        · cases accepted
      · cases accepted
    · cases accepted
  · cases accepted

private theorem project_nominal {catalog : SourceCoreDataCatalog.Catalog}
    {type : TypeSystem.Ty} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    {identity : DataTypeId}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (selected : catalog.identity? type = some identity) : catalog.project type = .ok (.namedData identity) := by
  cases type with
  | constructor constructor =>
    cases constructor with
    | declaration declaration => simp [SourceCoreDataCatalog.Catalog.project, selected]
    | builtin builtin => cases builtin <;> simp [SourceCoreDataCatalog.nominalParts] at nominal
  | application function argument => simp [SourceCoreDataCatalog.Catalog.project, selected]
  | _ =>
    simp [SourceCoreDataCatalog.nominalParts] at nominal

/-- A packed list is unit, a singleton, or a right-associated product, exactly
as the data constructor catalog and the pattern compiler require. -/
private theorem pack_typed {world : StoreTyping} {definitions : DataEnvironment}
    {types : List Ty} {values : List Value}
    (typed : ListRel (fun value type => RuntimeValueHasType world value type definitions) values types) :
    RuntimeValueHasType world (packValues values) (SourceCoreDataMatches.bundleType types) definitions := by
  induction typed with
  | nil => exact .unit
  | @cons value type values types head tail ih =>
    cases tail with
    | nil => exact head
    | cons second rest => exact .pair head ih

/-- The finite relation does not contain raw references or closure code. Its
runtime typing therefore holds in every Core world, including worlds with
administrative function cells. -/
theorem TypedValueRep.project_typed {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (represented : DataPatternTypedValues.TypedValueRep catalog signatures sourceType source value) :
    ∃ type, catalog.project sourceType = .ok type ∧
      ∀ world, RuntimeValueHasType world value type catalog.definitions := by
  induction represented using DataPatternTypedValues.TypedValueRep.rec
    (motive_2 := fun types _ values _ => ∃ coreTypes, types.mapM catalog.project = .ok coreTypes ∧
      ∀ world, ListRel (fun value type => RuntimeValueHasType world value type catalog.definitions) values coreTypes) with
  | unit => exact ⟨.unit, rfl, fun _ => .unit⟩
  | bool value => exact ⟨.bool, rfl, fun _ => .bool⟩
  | word value => exact ⟨.word, rfl, fun _ => .word⟩
  | integer value => exact ⟨.integer, rfl, fun _ => .integer⟩
  | product left right leftIH rightIH =>
    obtain ⟨a, projectA, typedA⟩ := leftIH
    obtain ⟨b, projectB, typedB⟩ := rightIH
    exact ⟨.product a b, by simp [SourceCoreDataCatalog.Catalog.project, projectA, projectB, bind, Except.bind, pure, Except.pure],
      fun world => .pair (typedA world) (typedB world)⟩
  | constructed nominal result authenticated payloads ih =>
    obtain ⟨types, projected, typed⟩ := ih
    obtain ⟨registered, projectedRegistered, payloadType⟩ := resolveConstructor_payload authenticated
    have same := Except.ok.inj (projected.symm.trans projectedRegistered)
    subst registered
    have identity := DataPatternAuthenticity.constructor_identity
      (SourceCoreDataValues.resolveConstructor_lookup authenticated)
    rw [result] at identity
    exact ⟨_, project_nominal nominal identity, fun world => .constructed payloadType (pack_typed (typed world))⟩
  | nil => exact ⟨[], rfl, fun _ => .nil⟩
  | cons head tail headIH tailIH =>
    obtain ⟨type, projection, typed⟩ := headIH
    obtain ⟨types, projections, restTyped⟩ := tailIH
    exact ⟨type :: types, by simp [List.mapM_cons, projection, projections, bind, Except.bind, pure, Except.pure],
      fun world => .cons (typed world) (restTyped world)⟩

end Solcore.SourceSemantics.CoreLowering.DataValueTyping
