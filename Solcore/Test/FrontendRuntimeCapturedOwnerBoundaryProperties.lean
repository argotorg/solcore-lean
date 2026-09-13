import Solcore.Frontend.RuntimeCapturedOwnerProperties

/- Independent collision calculations precede the covariance APIs. Duplicate rows
remain ordered, and opaque closure syntax, cells and full payloads are literal.
Word selection needs no owner injectivity and does not inspect skipped suffixes. -/
set_option autoImplicit false
namespace Tests.RuntimeCapturedOwnerBoundaries
open Solcore Solcore.Frontend
private abbrev L := Resolved.LocalScope.Lookup (α := RuntimeValue)
private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"OwnerBoundary",by decide⟩],by decide⟩⟩,n⟩
private def id (o n : Nat) : Resolved.LocalId := ⟨owner o,n⟩
private def collapse (_ : Resolved.DeclarationId) := owner 0
private def collisionRows : Resolved.LocalScope RuntimeValue :=
  [(id 2 7,.bool false),(id 9 7,.bool true),(id 9 7,.unit)]
private def foreignNames : LocalNameTable := [("dup",id 9 7),("dup",id 9 7)]

/-- Collapsing distinct owners changes the first payload and the allocated index. -/
theorem noninjective_owner_collision_breaks_lookup_and_fresh :
    ¬ Function.Injective collapse ∧
    L collisionRows (id 9 7) (.bool true) ∧
    Resolved.LocalScope.lookup? collisionRows (id 9 7) = some (.bool true) ∧
    Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners collapse collisionRows)
      (ownerLocalIdMap collapse (id 9 7)) = some (.bool false) ∧
    Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners collapse collisionRows)
      (ownerLocalIdMap collapse (id 9 7)) ≠
        (Resolved.LocalScope.lookup? collisionRows (id 9 7)).map (RuntimeValue.mapOwners collapse) ∧
    Resolved.freshLocalId (owner 2) (foreignNames.map Prod.snd) = id 2 0 ∧
    Resolved.freshLocalId (collapse (owner 2))
      ((LocalNameTable.mapIds (ownerLocalIdMap collapse) foreignNames).map Prod.snd) = id 0 8 ∧
    Resolved.freshLocalId (collapse (owner 2))
      ((LocalNameTable.mapIds (ownerLocalIdMap collapse) foreignNames).map Prod.snd) ≠
        ownerLocalIdMap collapse (Resolved.freshLocalId (owner 2) (foreignNames.map Prod.snd)) := by
  have found : L collisionRows (id 9 7) (.bool true) := .tail (by decide) .head
  have original : Resolved.LocalScope.lookup? collisionRows (id 9 7) = some (.bool true) := rfl
  have mapped : Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners collapse collisionRows)
      (ownerLocalIdMap collapse (id 9 7)) = some (.bool false) := by
    simp [collisionRows,mapRuntimeCapturedOwners,RuntimeValue.mapOwners,ownerLocalIdMap,collapse,id,
      Resolved.LocalScope.lookup?]
  have oldFresh : Resolved.freshLocalId (owner 2) (foreignNames.map Prod.snd) = id 2 0 := rfl
  have newFresh : Resolved.freshLocalId (collapse (owner 2))
      ((LocalNameTable.mapIds (ownerLocalIdMap collapse) foreignNames).map Prod.snd) = id 0 8 := rfl
  have notInjective : ¬ Function.Injective collapse := by
    intro injective
    have same := injective (show collapse (owner 2) = collapse (owner 9) from rfl)
    have impossible := congrArg Resolved.DeclarationId.declarationIndex same
    contradiction
  refine ⟨notInjective,found,original,mapped,?_,oldFresh,newFresh,?_⟩
  · rw [mapped,original]
    simp [RuntimeValue.mapOwners]
  · rw [newFresh,oldFresh]
    decide

private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId :=
  ⟨o.moduleId,o.declarationIndex+1⟩
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  cases left; cases right
  simp only [shift] at modules indices
  cases modules
  have equal := Nat.add_right_cancel indices
  cases equal
  rfl
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨before,equal⟩ := onto (owner 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex equal
  change before.declarationIndex+1=0 at impossible
  omega
private def span (n : Nat) : Syntax.SourceSpan := ⟨⟨.main,"owner-boundary.sol"⟩,n,n+1⟩
private def source : Syntax.Expr := ⟨span 10,.identifier ⟨span 11,"opaque"⟩⟩
private def core : RuntimeValue :=
  .coreClosure .unit .word (.var 99) [.cellRef .word 700,.hostFunction .storageWrite]
private def payload : RuntimeValue := .sourceClosure source (owner 2)
  [("q",id 2 7),("q",id 9 7)] [(id 2 7,core),(id 2 7,.unit)]
private def shiftedPayload : RuntimeValue := .sourceClosure source (owner 3)
  [("q",id 3 7),("q",id 10 7)] [(id 3 7,core),(id 3 7,.unit)]
private def rows : Resolved.LocalScope RuntimeValue :=
  [(id 9 7,.unit),(id 2 7,payload),(id 2 7,.bool false),(id 2 8,.cellRef .word 900)]
private def names : LocalNameTable :=
  [("x",id 2 7),("x",id 9 7),("y",id 2 8),("y",id 2 8),("z",id 9 90)]
private theorem payload_calculation : payload.mapOwners shift = shiftedPayload := by
  simp [payload,shiftedPayload,core,RuntimeValue.mapOwners,LocalNameTable.mapIds,ownerLocalIdMap,shift,id,owner]

/-- Surjectivity and unique rows are unnecessary: first matches and fresh index stay exact. -/
theorem injective_nonsurjective_transport_keeps_duplicate_first_match :
    Function.Injective shift ∧ ¬ Function.Surjective shift ∧
    LocalNameTable.Lookup names "x" (id 2 7) ∧
    LocalNameTable.Lookup (LocalNameTable.mapIds (ownerLocalIdMap shift) names) "x" (id 3 7) ∧
    LocalNameTable.lookup? names "missing" = none ∧
    LocalNameTable.lookup? (LocalNameTable.mapIds (ownerLocalIdMap shift) names) "missing" = none ∧
    L rows (id 2 7) payload ∧
    Resolved.LocalScope.lookup? rows (id 2 7) = some payload ∧
    Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners shift rows) (id 3 7) = some shiftedPayload ∧
    L (mapRuntimeCapturedOwners shift rows) (id 3 7) shiftedPayload ∧
    Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners shift rows) (id 3 99) = none ∧
    Resolved.freshLocalId (owner 2) (names.map Prod.snd) = id 2 9 ∧
    Resolved.freshLocalId (owner 3)
      ((LocalNameTable.mapIds (ownerLocalIdMap shift) names).map Prod.snd) = id 3 9 ∧
    Resolved.freshLocalId (owner 3)
      ((LocalNameTable.mapIds (ownerLocalIdMap shift) names).map Prod.snd) =
        ownerLocalIdMap shift (Resolved.freshLocalId (owner 2) (names.map Prod.snd)) := by
  have named : LocalNameTable.Lookup names "x" (id 2 7) := .head
  have mappedNamed : LocalNameTable.Lookup (LocalNameTable.mapIds (ownerLocalIdMap shift) names) "x" (id 3 7) := .head
  have missingName : LocalNameTable.lookup? names "missing" = none := rfl
  have mappedMissingName : LocalNameTable.lookup? (LocalNameTable.mapIds (ownerLocalIdMap shift) names) "missing" = none := rfl
  have found : L rows (id 2 7) payload := .tail (by decide) .head
  have original : Resolved.LocalScope.lookup? rows (id 2 7) = some payload := rfl
  have absent : Resolved.LocalScope.lookup? rows (id 2 99) = none := rfl
  have mapped : Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners shift rows) (id 3 7) = some shiftedPayload := by
    simp [rows,mapRuntimeCapturedOwners,Resolved.LocalScope.lookup?,ownerLocalIdMap,shift,id,owner,
      payload_calculation,RuntimeValue.mapOwners]
  have fresh : Resolved.freshLocalId (owner 2) (names.map Prod.snd) = id 2 9 := rfl
  have mappedFresh : Resolved.freshLocalId (owner 3)
      ((LocalNameTable.mapIds (ownerLocalIdMap shift) names).map Prod.snd) = id 3 9 := rfl
  have transported := mapRuntimeCapturedOwners_lookup shift shift_injective found
  have absentTransport := lookup?_mapRuntimeCapturedOwners shift shift_injective rows (id 2 99)
  have freshTransport := freshLocalId_mapRuntimeNamesOwners shift shift_injective (owner 2) names
  have mappedFound : L (mapRuntimeCapturedOwners shift rows) (id 3 7) shiftedPayload := by
    simpa only [payload_calculation,ownerLocalIdMap,shift,id,owner,L] using transported
  have mappedAbsent : Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners shift rows) (id 3 99) = none := by
    rw [absent] at absentTransport
    simpa only [Option.map_none,ownerLocalIdMap,shift,id,owner] using absentTransport
  exact ⟨shift_injective,shift_not_surjective,named,mappedNamed,missingName,mappedMissingName,
    found,original,mapped,mappedFound,mappedAbsent,fresh,
    mappedFresh,freshTransport⟩

private def body (n : Nat) : Syntax.Block := ⟨span n,[]⟩
private def literalCase (text : String) (n : Nat) : Syntax.MatchCase :=
  ⟨span (n+1),⟨⟨span (n+2),.literal ⟨span (n+3),.decimal text⟩⟩,body n⟩⟩
private def wildcardCase : Syntax.MatchCase := ⟨span 31,⟨⟨span 32,.wildcard (span 33)⟩,body 30⟩⟩
private def badCase : Syntax.MatchCase :=
  ⟨span 51,⟨⟨span 52,.literal ⟨span 53,.string "unvisited"⟩⟩,body 50⟩⟩
private def literalCases := [literalCase "0" 10,literalCase "1" 20,literalCase "1" 21,badCase]
private def one : Core.Word := ⟨1,by decide⟩
private theorem zeroMeaning : WordMatchPatternClassifies (literalCase "0" 10).value.pattern (some Core.Word.zero) := by
  refine .literal ⟨_,rfl,?_⟩
  exact .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) (by decide)) .nil)
private theorem oneMeaning : WordMatchPatternClassifies (literalCase "1" 20).value.pattern (some one) := by
  refine .literal ⟨_,rfl,?_⟩
  exact .decimal (by decide) (.cons (.decimal (digit:=1) (by decide) (by decide)) .nil)

/-- Literal position/count, mixed wildcard/default, and first non-Word rejection survive any map. -/
theorem owner_changes_preserve_ordered_word_selection
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) :
    literalCases[1]? = some (literalCase "1" 20) ∧
    RuntimeWordMatchChooses ((RuntimeValue.word one).mapOwners mapping) literalCases (some (body 40)) (body 20) 2 ∧
    chooseRuntimeWordMatch? ((RuntimeValue.word one).mapOwners mapping) literalCases (some (body 40)) = some (body 20,2) ∧
    RuntimeWordMatchChooses (payload.mapOwners mapping) [wildcardCase,badCase] (some (body 40)) (body 30) 0 ∧
    chooseRuntimeWordMatch? (payload.mapOwners mapping) [wildcardCase,badCase] (some (body 40)) = some (body 30,0) ∧
    RuntimeWordMatchChooses (payload.mapOwners mapping) [] (some (body 40)) (body 40) 0 ∧
    chooseRuntimeWordMatch? (payload.mapOwners mapping) [] (some (body 40)) = some (body 40,0) ∧
    chooseRuntimeWordMatch? (payload.mapOwners mapping) literalCases (some (body 40)) = none := by
  have literalOriginal : RuntimeWordMatchChooses (.word one) literalCases (some (body 40)) (body 20) 2 :=
    .miss zeroMeaning (by decide) (.hit oneMeaning)
  have wildcardOriginal : RuntimeWordMatchChooses payload [wildcardCase,badCase] (some (body 40)) (body 30) 0 :=
    .wildcard (.wildcard rfl)
  have defaultOriginal : RuntimeWordMatchChooses payload [] (some (body 40)) (body 40) 0 := .fallback
  have literalRun : chooseRuntimeWordMatch? (.word one) literalCases (some (body 40)) = some (body 20,2) :=
    chooseRuntimeWordMatch?_iff.mpr literalOriginal
  have wildcardRun : chooseRuntimeWordMatch? payload [wildcardCase,badCase] (some (body 40)) = some (body 30,0) :=
    chooseRuntimeWordMatch?_iff.mpr wildcardOriginal
  have defaultRun : chooseRuntimeWordMatch? payload [] (some (body 40)) = some (body 40,0) :=
    chooseRuntimeWordMatch?_iff.mpr defaultOriginal
  have rejected : chooseRuntimeWordMatch? payload literalCases (some (body 40)) = none := by
    simp only [literalCases,chooseRuntimeWordMatch?,interpretWordMatchPattern?_iff.mpr zeroMeaning,payload]
  exact ⟨rfl,(runtimeWordMatchChooses_mapOwners_iff mapping).mpr literalOriginal,
    (chooseRuntimeWordMatch?_mapOwners mapping _ _ _).trans literalRun,
    (runtimeWordMatchChooses_mapOwners_iff mapping).mpr wildcardOriginal,
    (chooseRuntimeWordMatch?_mapOwners mapping _ _ _).trans wildcardRun,
    (runtimeWordMatchChooses_mapOwners_iff mapping).mpr defaultOriginal,
    (chooseRuntimeWordMatch?_mapOwners mapping _ _ _).trans defaultRun,
    (chooseRuntimeWordMatch?_mapOwners mapping _ _ _).trans rejected⟩

end Tests.RuntimeCapturedOwnerBoundaries
