import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySyntaxTable

/-! Actual cache eligibility requires the original signature catalog. Unselected
ordinary and method bodies do not enter this executable table scan. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinarySyntaxTable
open Frontend SourceInference
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Eligible)
open CallableIndexedOwnedPreparedOrdinarySyntaxTable (range? Table)

def eligible? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (fuel : Nat) {index : Nat} (named : SourceCoreGeneralFunctions.Function)
    (selected : compiled.indexed.base.functions[index]? = some named) :
    Option (PLift (Eligible compiled named.specialized)) := do
  match found : compiled.sourceProgram.signatures.functions.find?
      (fun signature => decide (named.specialized.declaration = signature.id)) with
  | none => none
  | some signature =>
      let ⟨range⟩ ← range? compiled.sourceProgram.signatures fuel named.specialized.parameterSubstitution
      if ordinaryReturn : named.specialized.function.returnComptime = false then
        if ordinaryParameters : named.specialized.function.typedBody.inputs.all
            (fun binder => !binder.comptime) = true then
          pure ⟨{
            origin := SelectedCompilationCatalog.ordinary_origin compiled signatures
              (RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected rfl)
              (List.mem_of_find?_eq_some found)
              (by simpa only [decide_eq_true_eq] using (List.find?_some found))
            range := range
            ordinaryReturn := ordinaryReturn
            ordinaryParameters := by
              intro binder member
              have checked := List.all_eq_true.mp ordinaryParameters binder member
              cases same : binder.comptime <;> simp_all }⟩
        else none
      else none

def collect (compiled : SourceCoreUnifiedCompilation.Compiled)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (fuel : Nat) : Table compiled :=
  let rec go (remaining : List (Fin compiled.indexed.base.functions.length)) : Table compiled :=
    match remaining with
    | [] => ⟨[], by intro row member; cases member⟩
    | index :: rest =>
        let named := compiled.indexed.base.functions[index.val]
        have selected : compiled.indexed.base.functions[index.val]? = some named :=
          List.getElem?_eq_getElem index.isLt
        let tail := go rest
        match eligible? compiled signatures fuel named selected with
        | none => tail
        | some ⟨accepted⟩ =>
            { rows := named.specialized :: tail.rows
              admitted := by
                intro row member
                rcases List.mem_cons.mp member with same | member
                · subst row; exact ⟨index.val, named, selected, rfl, accepted⟩
                · exact tail.admitted row member }
  go (List.finRange compiled.indexed.base.functions.length)

/-- Existing accepted programs retain the identical eligible rows. -/
theorem eligible_eq (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (fuel : Nat) {index : Nat} (named : SourceCoreGeneralFunctions.Function)
    (selected : compiled.indexed.base.functions[index]? = some named) :
    eligible? compiled wellFormed.signatures fuel named selected =
      CallableIndexedOwnedPreparedOrdinarySyntaxTable.eligible? compiled wellFormed fuel named selected := by
  rfl

/-- Signature-only scanning preserves the original table and physical order. -/
theorem collect_eq (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) (fuel : Nat) :
    collect compiled wellFormed.signatures fuel =
      CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel := by
  unfold collect CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect
  generalize List.finRange compiled.indexed.base.functions.length = remaining
  induction remaining with
  | nil => rfl
  | cons first rest ih =>
      simp only [collect.go, CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect.go,
        ih]
      rfl

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinarySyntaxTable
