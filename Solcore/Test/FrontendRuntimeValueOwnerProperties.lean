import Solcore.Frontend.RuntimeValueOwnerProperties

/- Handwritten nested values exercise literal Core code, tags, locations and
duplicate rows. Direct structural calculations precede the representation laws. -/
set_option autoImplicit false
namespace Tests.RuntimeValueOwnerMixed
open Solcore Solcore.Frontend

private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId := ⟨owner,index⟩
private def plainCore (tag : Core.ConstructorId) (word : Core.Word) : Core.Value :=
  .closure .unit .word (.var 99)
    [.constructed tag (.inLeft .word (.pair (.word word) (.cellRef .word 701))),.hostFunction .storageWrite]
private def deep (source : Syntax.Expr) (caller foreign : Resolved.DeclarationId) : RuntimeValue :=
  .sourceClosure source foreign [("deep",localId caller 9),("deep",localId foreign 2)]
    [(localId foreign 2,.unit),(localId foreign 2,.cellRef .word 702)]
private def mixed (source : Syntax.Expr) (caller saved foreign : Resolved.DeclarationId)
    (tag : Core.ConstructorId) (word : Core.Word) : RuntimeValue :=
  .pair
    (.sourceClosure source saved [("p",localId saved 7),("p",localId saved 1),("x",localId foreign 8)]
      [(localId saved 7,.coreClosure .unit .word (.var 17)
        [deep source caller foreign,.ofCore (plainCore tag word)]),
       (localId saved 7,.bool false),(localId saved 9,.hostFunction .storageRead)])
    (.coreClosure .bool .unit (.var 3)
      [.constructed tag (.inRight .word
        (.sourceClosure source caller [("p",localId saved 9)]
          [(localId caller 0,.pair (.cellRef .word 703) (.word word))]))])

private theorem direct_mapping (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (source : Syntax.Expr) (caller saved foreign : Resolved.DeclarationId)
    (tag : Core.ConstructorId) (word : Core.Word) :
    (mixed source caller saved foreign tag word).mapOwners mapping =
      mixed source (mapping caller) (mapping saved) (mapping foreign) tag word := by
  simp only [mixed,deep,plainCore,RuntimeValue.ofCore,List.attach_map_val,
    RuntimeValue.mapOwners_coreClosure,RuntimeValue.mapOwners_sourceClosure,RuntimeValue.mapOwners,
    mapRuntimeCapturedOwners,LocalNameTable.mapIds,ownerLocalIdMap,localId,List.map_cons,List.map_nil]

private theorem direct_projection (source : Syntax.Expr) (caller saved foreign : Resolved.DeclarationId)
    (tag : Core.ConstructorId) (word : Core.Word) :
    (mixed source caller saved foreign tag word).toCore? = none := by
  simp only [mixed,RuntimeValue.toCore?,bind,Option.bind_none]

private theorem direct_core_projection (tag : Core.ConstructorId) (word : Core.Word) :
    (RuntimeValue.ofCore (plainCore tag word)).toCore? = some (plainCore tag word) := by
  simp [plainCore,RuntimeValue.ofCore,RuntimeValue.toCore?]

/-- Deep closures and duplicate captures retain every field through all seven representation laws. -/
theorem complete_mixed_representation
    (mapping second : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (source : Syntax.Expr)
    (caller saved foreign : Resolved.DeclarationId) (tag : Core.ConstructorId) (word : Core.Word) :
    let value := mixed source caller saved foreign tag word
    let captures := [(localId saved 7,value),(localId saved 7,RuntimeValue.unit)]
    let store := [RuntimeValue.cellRef .word 704,value,RuntimeValue.ofCore (plainCore tag word)]
    value.mapOwners mapping = mixed source (mapping caller) (mapping saved) (mapping foreign) tag word ∧
    store.map (RuntimeValue.mapOwners mapping) = [.cellRef .word 704,
      mixed source (mapping caller) (mapping saved) (mapping foreign) tag word,RuntimeValue.ofCore (plainCore tag word)] ∧
    value.mapOwners id = value ∧
    (value.mapOwners mapping).mapOwners second = value.mapOwners (second ∘ mapping) ∧
    (RuntimeValue.ofCore (plainCore tag word)).mapOwners mapping = RuntimeValue.ofCore (plainCore tag word) ∧
    ((RuntimeValue.ofCore (plainCore tag word)).mapOwners mapping).toCore? = some (plainCore tag word) ∧
    (value.mapOwners mapping).toCore? = none ∧
    (∀ left right : RuntimeValue, left.mapOwners mapping = right.mapOwners mapping ↔ left = right) ∧
    mapRuntimeCapturedOwners id captures = captures ∧
    mapRuntimeCapturedOwners second (mapRuntimeCapturedOwners mapping captures) =
      mapRuntimeCapturedOwners (second ∘ mapping) captures := by
  have exactFields := direct_mapping mapping source caller saved foreign tag word
  have projection := direct_projection source caller saved foreign tag word
  have coreProjection := direct_core_projection tag word
  have exactStore : [RuntimeValue.cellRef .word 704,mixed source caller saved foreign tag word,
      RuntimeValue.ofCore (plainCore tag word)].map (RuntimeValue.mapOwners mapping) =
      [.cellRef .word 704,mixed source (mapping caller) (mapping saved) (mapping foreign) tag word,
        RuntimeValue.ofCore (plainCore tag word)] := by
    simp only [List.map_cons,List.map_nil,exactFields]
    simp only [plainCore,RuntimeValue.ofCore,List.attach_map_val,RuntimeValue.mapOwners_coreClosure,
      RuntimeValue.mapOwners,List.map_cons,List.map_nil]
  refine ⟨exactFields,exactStore,RuntimeValue.mapOwners_id _,RuntimeValue.mapOwners_comp _ mapping second,
    RuntimeValue.mapOwners_ofCore mapping _,?_,?_,?_,mapRuntimeCapturedOwners_id _,mapRuntimeCapturedOwners_comp _ mapping second⟩
  · exact (RuntimeValue.toCore?_mapOwners mapping _).trans coreProjection
  · exact (RuntimeValue.toCore?_mapOwners mapping _).trans projection
  · intro left right
    exact ⟨fun same => RuntimeValue.mapOwners_injective mapping injective same,
      congrArg (RuntimeValue.mapOwners mapping)⟩

/-- Noninjective relabeling can collapse distinct saved owners even though projection stays absent. -/
theorem constant_mapping_loses_owner (source : Syntax.Expr)
    (left right replacement : Resolved.DeclarationId) (distinct : left ≠ right) :
    let a := RuntimeValue.sourceClosure source left [] []
    let b := RuntimeValue.sourceClosure source right [] []
    a ≠ b ∧ a.mapOwners (fun _ => replacement) = b.mapOwners (fun _ => replacement) ∧
    a.toCore? = none ∧ b.toCore? = none := by
  refine ⟨?_,?_,?_,?_⟩
  · intro same
    exact distinct (RuntimeValue.sourceClosure.inj same).2.1
  · simp only [RuntimeValue.mapOwners_sourceClosure,LocalNameTable.mapIds,
      mapRuntimeCapturedOwners,List.map_nil]
  · simp only [RuntimeValue.toCore?]
  · simp only [RuntimeValue.toCore?]

private def span : Syntax.SourceSpan := ⟨⟨.main,"owner-representation.sol"⟩,0,1⟩
private def source : Syntax.Expr := ⟨span,.tuple ⟨span,[]⟩⟩
private def caller : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Caller",by decide⟩],by decide⟩⟩,1⟩
private def saved : Resolved.DeclarationId := {caller with declarationIndex:=2}
private def foreign : Resolved.DeclarationId := {caller with declarationIndex:=3}
private def shift (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  {owner with declarationIndex:=owner.declarationIndex+5}
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  cases left with
  | mk lm li =>
    cases right with
    | mk rm ri =>
      change lm = rm at modules
      change li+5 = ri+5 at indices
      have equal : li = ri := by omega
      cases modules
      cases equal
      rfl

/-- A concrete non-surjective injection preserves this nested, owner-separated fixture. -/
theorem shifted_fixture (tag : Core.ConstructorId) (word : Core.Word) :
    caller ≠ saved ∧ saved ≠ foreign ∧ ¬ Function.Surjective shift ∧
    (mixed source caller saved foreign tag word).mapOwners shift =
      mixed source (shift caller) (shift saved) (shift foreign) tag word ∧
    (mixed source caller saved foreign tag word).mapOwners (fun _ => caller) =
      mixed source caller caller caller tag word := by
  have collision := direct_mapping (fun _ => caller) source caller saved foreign tag word
  have consumed := complete_mixed_representation shift shift shift_injective source caller saved foreign tag word
  refine ⟨by decide,by decide,?_,consumed.1,collision⟩
  intro onto
  obtain ⟨preimage,same⟩ := onto {caller with declarationIndex:=0}
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  change preimage.declarationIndex+5 = 0 at impossible
  omega

end Tests.RuntimeValueOwnerMixed
