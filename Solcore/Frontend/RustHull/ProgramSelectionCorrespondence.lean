import Solcore.Frontend.RustHull.GlobalFunctionCorrespondence

/-! Function names, signatures and installed-code indices are selected by the
actual assembler. These facts connect that selection to independent source
function lookup, including the compiler's reverse global-scope order. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

inductive CompiledSignatures (fuel : Nat) : List Function → List Signature → Prop where
  | nil : CompiledSignatures fuel [] []
  | cons {function : Function} {own : Signature} {functions : List Function} {signatures : List Signature}
      (head : signature fuel function = .ok own)
      (tail : CompiledSignatures fuel functions signatures) :
      CompiledSignatures fuel (function :: functions) (own :: signatures)

theorem compiledSignatures {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : functions.mapM (signature fuel) = .ok signatures) :
    CompiledSignatures fuel functions signatures := by
  induction functions generalizing signatures with
  | nil => cases compiled; exact .nil
  | cons function functions ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨own, head, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨rest, tail, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      exact .cons head (ih tail)

theorem CompiledSignatures.names {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : CompiledSignatures fuel functions signatures) :
    signatures.map (·.name) = functions.map (·.name) := by
  induction compiled with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, signature_name head, ih]

theorem CompiledSignatures.length {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : CompiledSignatures fuel functions signatures) : signatures.length = functions.length := by
  simpa only [List.length_map] using congrArg List.length compiled.names

theorem CompiledSignatures.selected {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : CompiledSignatures fuel functions signatures) {entry : String} {own : Signature}
    (selected : signatures.find? (·.name == entry) = some own) :
    ∃ function, functions.find? (·.name == entry) = some function ∧ signature fuel function = .ok own := by
  induction compiled with
  | nil => simp at selected
  | @cons function own' functions signatures head tail ih =>
      by_cases matched : own'.name == entry
      · simp only [List.find?_cons, matched, Option.some.injEq] at selected
        subst own
        exact ⟨function, by simp only [List.find?_cons, ← signature_name head, matched], head⟩
      · simp only [List.find?_cons, matched] at selected
        obtain ⟨selectedFunction, found, accepted⟩ := ih selected
        exact ⟨selectedFunction, by simpa only [List.find?_cons, ← signature_name head, matched] using found, accepted⟩

private theorem eraseDups_length_le (names : List String) : names.eraseDups.length ≤ names.length := by
  cases names with
  | nil => simp
  | cons name rest =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      exact Nat.succ_le_succ (Nat.le_trans (eraseDups_length_le (rest.filter fun other => !other == name))
        (List.length_filter_le _ _))
termination_by names.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem names_unique_of_checked {names : List String} (checked : names.eraseDups.length = names.length) :
    names.Nodup := by
  induction names with
  | nil => exact .nil
  | cons name rest ih =>
      rw [List.eraseDups_cons] at checked
      have deduplicated := eraseDups_length_le (rest.filter fun other => !other == name)
      have filtered := List.length_filter_le (fun other => !other == name) rest
      have sameLength : (rest.filter fun other => !other == name).length = rest.length := by
        simp only [List.length_cons] at checked
        omega
      have allDifferent := List.length_filter_eq_length_iff.mp sameLength
      have same : rest.filter (fun other => !other == name) = rest := List.filter_eq_self.mpr allDifferent
      rw [same] at checked
      apply List.nodup_cons.mpr
      constructor
      · intro member
        simpa using allDifferent name member
      · exact ih (Nat.succ.inj checked)

theorem assemble_names_unique {functions : List Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (compiled : assemble functions entry runtime fuel = .ok (own, allocated)) :
    (functions.map (·.name)).Nodup := by
  by_cases unique : (functions.map (·.name)).eraseDups.length = functions.length
  · exact names_unique_of_checked (by simpa only [List.length_map] using unique)
  · simp [assemble, unique, fail, Bind.bind, Except.bind] at compiled

def globalBinding (own : Signature) : Binding :=
  ⟨some (Effects.slotName ("function$" ++ own.name)), own.functionType, true⟩

theorem functionSlot_injective : Function.Injective (fun name => Effects.slotName ("function$" ++ name)) := by
  intro left right same
  simpa [Effects.slotName] using same

private theorem namedScope_lookup {signatures : List Signature} {own : Signature} {index : Nat}
    (unique : (signatures.map (·.name)).Nodup) (found : signatures[index]? = some own) (runtime : Scope) :
    Scope.lookup ((signatures.map globalBinding) ++ runtime) (Effects.slotName ("function$" ++ own.name)) =
      .ok (globalBinding own, index) := by
  induction signatures generalizing index with
  | nil => simp at found
  | cons head rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst head
          simp [globalBinding, scope_lookup_cons]
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          have different : head.name ≠ own.name := by
            intro same
            apply absent
            change head.name ∈ rest.map (·.name)
            rw [same]
            exact List.mem_map.mpr ⟨own, List.mem_of_getElem? found, rfl⟩
          have slotDifferent : Effects.slotName ("function$" ++ head.name) ≠
              Effects.slotName ("function$" ++ own.name) := fun same => different (functionSlot_injective same)
          simp only [List.map_cons, List.cons_append, scope_lookup_cons, globalBinding,
            Option.some_beq_some, beq_eq_false_iff_ne.mpr slotDifferent, Bool.false_eq_true, ↓reduceIte]
          rw [ih tailUnique found]
          rfl

/-- The actual reverse global scope finds every unique function at precisely
its installed-code index, even when a separate runtime scope follows it. -/
theorem globalScope_lookup {signatures : List Signature} {own : Signature} {index : Nat}
    (unique : (signatures.map (·.name)).Nodup)
    (found : signatures.reverse[index]? = some own) (runtime : Scope) :
    (globalScope signatures runtime).lookup (Effects.slotName ("function$" ++ own.name)) =
      .ok (globalBinding own, index) := by
  apply namedScope_lookup (runtime := runtime) _ found
  simpa only [List.map_reverse] using (List.reverse_perm (signatures.map (·.name))).nodup_iff.mpr unique

theorem CompiledSignatures.selected_pair {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : CompiledSignatures fuel functions signatures) {entry : String} {own : Signature}
    (selected : signatures.find? (·.name == entry) = some own) :
    ∃ function, functions.find? (·.name == entry) = some function ∧
      signature fuel function = .ok own ∧ (function, own) ∈ functions.zip signatures := by
  induction compiled with
  | nil => simp at selected
  | @cons function own' functions signatures head tail ih =>
      by_cases matched : own'.name == entry
      · simp only [List.find?_cons, matched, Option.some.injEq] at selected
        subst own
        exact ⟨function, by simp only [List.find?_cons, ← signature_name head, matched],
          head, List.mem_cons_self ..⟩
      · simp only [List.find?_cons, matched] at selected
        obtain ⟨selectedFunction, found, accepted, member⟩ := ih selected
        exact ⟨selectedFunction, by simpa only [List.find?_cons, ← signature_name head, matched] using found,
          accepted, List.mem_cons_of_mem _ member⟩

theorem CompiledGlobals.get {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {items : List (Function × Signature)} {codes : List GlobalCode}
    (compiled : CompiledGlobals fuel signatures scope items codes)
    {index : Nat} {item : Function × Signature} (found : items[index]? = some item) :
    ∃ code, codes[index]? = some code ∧ CompiledGlobal fuel signatures scope item code := by
  induction compiled generalizing index with
  | nil => simp at found
  | @cons headItem code items codes head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst item
          exact ⟨code, rfl, head⟩
      | succ index => exact ih found

/-- A source-level named call and signature lookup select the same actual
compiled closure. This applies to any function, not only the public entry. -/
theorem compiledFunction_selected {fuel : Nat} {functions : List Function}
    {signatures : List Signature} {scope : Scope} {codes : List GlobalCode}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (codesCompiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes)
    {name : String} {function : Function} {own : Signature}
    (sourceSelected : functions.find? (·.name == name) = some function)
    (signatureSelected : signatures.find? (·.name == name) = some own) :
    signature fuel function = .ok own ∧ ∃ (index : Nat) (code : GlobalCode),
      codes[index]? = some code ∧ code.own = own ∧
      lowerFunction fuel signatures scope function own = .ok code.expression := by
  obtain ⟨selectedFunction, selected, signatureCompiled, member⟩ :=
    (compiledSignatures signaturesCompiled).selected_pair signatureSelected
  have same := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨index, itemFound⟩ := List.getElem?_of_mem (List.mem_reverse.mpr member)
  obtain ⟨code, found, ownEqual, functionCompiled⟩ := codesCompiled.get itemFound
  exact ⟨signatureCompiled, index, code, found, ownEqual, functionCompiled⟩

/-- The selected source function and installed closure are extracted from the
same accepted assembler run, with the real reverse installation index. -/
theorem assemble_selection {functions : List Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated)) :
    ∃ signatures codes function code index,
      functions.mapM (signature fuel) = .ok signatures ∧
      functions.find? (·.name == entry) = some function ∧
      signature fuel function = .ok own ∧
      CompiledGlobals fuel signatures (globalScope signatures runtime)
        (functions.zip signatures).reverse codes ∧
      codes[index]? = some code ∧ code.own = own ∧
      lowerFunction fuel signatures (globalScope signatures runtime) function own = .ok code.expression ∧
      allocated = globalAllocation signatures
        (globalInstallation codes 0 (globalInvocation own index signatures.length runtime.length)) := by
  obtain ⟨signatures, codes, binding, selectedIndex, signaturesCompiled, selected,
    codesCompiled, looked, allocatedEqual⟩ := assemble_components accepted
  have signaturesRelated := compiledSignatures signaturesCompiled
  obtain ⟨function, functionSelected, signatureCompiled, member⟩ := signaturesRelated.selected_pair selected
  obtain ⟨index, itemFound⟩ := List.getElem?_of_mem (List.mem_reverse.mpr member)
  obtain ⟨code, codeFound, ownEqual, functionCompiled⟩ := codesCompiled.get itemFound
  have aligned := codesCompiled.aligned signaturesCompiled
  have signatureFound : signatures.reverse[index]? = some own := by
    rw [← aligned, List.getElem?_map, codeFound]
    exact congrArg some ownEqual
  have unique : (signatures.map (·.name)).Nodup := by
    rw [signaturesRelated.names]
    exact assemble_names_unique accepted
  have actualLookup := globalScope_lookup unique signatureFound runtime
  have ownName : own.name = entry := by simpa only [beq_iff_eq] using List.find?_some selected
  rw [ownName] at actualLookup
  obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj (looked.symm.trans actualLookup))
  exact ⟨signatures, codes, function, code, selectedIndex, signaturesCompiled, functionSelected,
    signatureCompiled, codesCompiled, codeFound, ownEqual, functionCompiled, allocatedEqual⟩

end Solcore.Frontend.RustHull.Correspondence
