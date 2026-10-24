import Solcore.Frontend.RustHull.ProgramSelectionCorrespondence

/-! Name and code lookup for calls within one accepted compiled program.
Source selections determine actual signatures and installed closure indices;
the assembler's uniqueness check makes each such code choice unambiguous. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

theorem CompiledSignatures.source_selected {fuel : Nat} {functions : List Function}
    {signatures : List Signature} (compiled : CompiledSignatures fuel functions signatures)
    {name : String} {function : Function}
    (selected : functions.find? (·.name == name) = some function) :
    ∃ own, signatures.find? (·.name == name) = some own ∧ signature fuel function = .ok own := by
  induction compiled with
  | nil => simp at selected
  | @cons head own functions signatures headCompiled tail ih =>
      by_cases matched : head.name == name
      · simp only [List.find?_cons, matched, Option.some.injEq] at selected
        subst function
        exact ⟨own, by simp only [List.find?_cons, signature_name headCompiled, matched], headCompiled⟩
      · simp only [List.find?_cons, matched] at selected
        obtain ⟨result, found, accepted⟩ := ih selected
        exact ⟨result, by simpa only [List.find?_cons, signature_name headCompiled, matched] using found, accepted⟩

theorem compiledFunction_resolve {fuel : Nat} {functions : List Function} {signatures : List Signature}
    {scope : Scope} {codes : List GlobalCode}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (codesCompiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes)
    {name : String} {function : Function}
    (selected : functions.find? (·.name == name) = some function) :
    ∃ (index : Nat) (code : GlobalCode), signatures.find? (·.name == name) = some code.own ∧
      codes[index]? = some code ∧ signature fuel function = .ok code.own ∧
      lowerFunction fuel signatures scope function code.own = .ok code.expression := by
  obtain ⟨own, signatureFound, _⟩ := (compiledSignatures signaturesCompiled).source_selected selected
  obtain ⟨signatureCompiled, index, code, codeFound, ownEqual, functionCompiled⟩ :=
    compiledFunction_selected signaturesCompiled codesCompiled selected signatureFound
  cases ownEqual
  exact ⟨index, code, signatureFound, codeFound, signatureCompiled, functionCompiled⟩

theorem GlobalCode.lookup_unique {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse)
    (unique : (signatures.map Signature.name).Nodup)
    {leftIndex rightIndex : Nat} {left right : GlobalCode}
    (leftFound : codes[leftIndex]? = some left) (rightFound : codes[rightIndex]? = some right)
    (sameName : left.own.name = right.own.name) : leftIndex = rightIndex ∧ left = right := by
  have names : codes.map (fun code => code.own.name) = (signatures.map Signature.name).reverse := by
    change codes.map (Signature.name ∘ GlobalCode.own) = _
    rw [← List.map_map, aligned, List.map_reverse]
  have codeNamesUnique : (codes.map (fun code => code.own.name)).Nodup := by
    rw [names]
    exact (List.reverse_perm _).nodup_iff.mpr unique
  have leftName : (codes.map (fun code => code.own.name))[leftIndex]? = some left.own.name := by
    simp only [List.getElem?_map, leftFound, Option.map_some]
  have rightName : (codes.map (fun code => code.own.name))[rightIndex]? = some left.own.name := by
    simp only [List.getElem?_map, rightFound, Option.map_some, sameName]
  have sameIndex : leftIndex = rightIndex := (List.getElem?_inj
    ((List.getElem?_eq_some_iff.mp leftName).1) codeNamesUnique).mp (leftName.trans rightName.symm)
  subst rightIndex
  exact ⟨rfl, Option.some.inj (leftFound.symm.trans rightFound)⟩

theorem compiledFunction_at {fuel : Nat} {functions : List Function} {signatures : List Signature}
    {scope : Scope} {codes : List GlobalCode}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (codesCompiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes)
    (unique : (signatures.map Signature.name).Nodup)
    {name : String} {function : Function} {code : GlobalCode} {index : Nat}
    (selected : functions.find? (·.name == name) = some function)
    (signatureFound : signatures.find? (·.name == name) = some code.own)
    (codeFound : codes[index]? = some code) :
    signature fuel function = .ok code.own ∧
      lowerFunction fuel signatures scope function code.own = .ok code.expression := by
  obtain ⟨signatureCompiled, otherIndex, other, otherFound, ownEqual, functionCompiled⟩ :=
    compiledFunction_selected signaturesCompiled codesCompiled selected signatureFound
  have ⟨_, equal⟩ := GlobalCode.lookup_unique (codesCompiled.aligned signaturesCompiled)
    unique otherFound codeFound (congrArg Signature.name ownEqual)
  subst other
  exact ⟨signatureCompiled, functionCompiled⟩

end Solcore.Frontend.RustHull.Correspondence
