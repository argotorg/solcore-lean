import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog

/-! An executable direct-site table scans the actual cached data. Successful
checks retain original ordinary provenance, complete replacement formation and
stage flags. A separate theorem transfers its rows into a proof-issued catalog;
the scanner never evaluates a catalog chosen by classical existence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySyntaxTable
open Frontend SourceInference TypeSystem
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input)

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by
        intro item member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail item member⟩

private theorem types_scoped {context : Context} {types : List Ty}
    (each : ∀ type ∈ types, TypeWellScoped context [] type) : TypesWellScoped context [] types := by
  induction types with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (each head List.mem_cons_self)
        (ih (fun type member => each type (List.mem_cons_of_mem _ member)))

/-- Fuel bounds the type traversal. Nominal replacements retain actual catalog
membership and full arity, rather than merely a closed runtime representation. -/
def type? (signatures : ProgramSignatures) :
    (fuel : Nat) → (type : Ty) → Option (PLift (TypeWellScoped (Context.ofSignatures signatures) [] type))
  | 0, _ => none
  | fuel + 1, type =>
      match type with
      | .constructor (.builtin builtin) => some ⟨.builtin builtin⟩
      | .function parameter result => do
          let ⟨first⟩ ← type? signatures fuel parameter
          let ⟨second⟩ ← type? signatures fuel result
          pure ⟨.function first second⟩
      | .product left right => do
          let ⟨first⟩ ← type? signatures fuel left
          let ⟨second⟩ ← type? signatures fuel right
          pure ⟨.product first second⟩
      | .mapping key value => do
          let ⟨first⟩ ← type? signatures fuel key
          let ⟨second⟩ ← type? signatures fuel value
          pure ⟨.mapping first second⟩
      | .proxy inner => do
          let ⟨formed⟩ ← type? signatures fuel inner
          pure ⟨.proxy formed⟩
      | .comptime inner => do
          let ⟨formed⟩ ← type? signatures fuel inner
          pure ⟨.comptime formed⟩
      | type => do
          let (id, arguments) ← SourceCoreDataCatalog.nominalParts type
          if same : type = Ty.nominal id arguments then
            let ⟨formed⟩ ← allProof?
              (fun argument => TypeWellScoped (Context.ofSignatures signatures) [] argument)
              (type? signatures fuel) arguments
            match found : signatures.dataTypes.find? (fun signature => decide (signature.id = id)) with
            | some signature =>
                if arity : arguments.length = signature.parameters.length then
                  have key : signature.id = id := by
                    simpa only [decide_eq_true_eq] using (List.find?_some found)
                  pure ⟨by
                    rw [same, ← key]
                    exact .nominal signature arguments (List.mem_of_find?_eq_some found) arity
                      (types_scoped formed)⟩
                else none
            | none =>
                match found : signatures.contracts.find? (fun signature => decide (signature.id = id)) with
                | some signature =>
                    if arity : arguments.length = signature.parameters.length then
                      have key : signature.id = id := by
                        simpa only [decide_eq_true_eq] using (List.find?_some found)
                      pure ⟨by
                        rw [same, ← key]
                        exact .contractNominal signature arguments (List.mem_of_find?_eq_some found) arity
                          (types_scoped formed)⟩
                    else none
                | none => none
          else none

def range? (signatures : ProgramSignatures) (fuel : Nat)
    (substitution : TypeSystem.ParameterSubstitution) :
    Option (PLift (SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures signatures) substitution)) := do
  let ⟨formed⟩ ← allProof? (fun item : TypeParameterId × Ty =>
    TypeWellScoped (Context.ofSignatures signatures) [] item.2)
    (fun item => type? signatures fuel item.2) substitution
  pure ⟨by
    intro parameter replacement member
    exact ⟨TypeParameterBindersWellFormed.ofSignatures signatures, formed _ member⟩⟩

/-- Only an actual ordinary declaration can pass; implementation-method rows
cannot acquire ordinary provenance through a matching native type. -/
def eligible? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
            origin := CallableIndexedOwnedPreparedOrdinaryCachedInputs.ordinary_origin compiled wellFormed
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

structure Table (compiled : SourceCoreUnifiedCompilation.Compiled) where
  rows : List SourceSpecialization.SpecializedFunction
  admitted : ∀ row ∈ rows, ∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function),
    compiled.indexed.base.functions[index]? = some named ∧
    named.specialized = row ∧ Eligible compiled row

/-- The executable result contains data from the actual cache in physical
order. Rows outside the checked fragment are omitted; no completeness is claimed. -/
def collect (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (fuel : Nat) : Table compiled :=
  let rec go (remaining : List (Fin compiled.indexed.base.functions.length)) : Table compiled :=
    match remaining with
    | [] => ⟨[], by intro row member; cases member⟩
    | index :: rest =>
        let named := compiled.indexed.base.functions[index.val]
        have selected : compiled.indexed.base.functions[index.val]? = some named :=
          List.getElem?_eq_getElem index.isLt
        let tail := go rest
        match eligible? compiled wellFormed fuel named selected with
        | none => tail
        | some ⟨accepted⟩ =>
            { rows := named.specialized :: tail.rows
              admitted := by
                intro row member
                rcases List.mem_cons.mp member with same | member
                · subst row; exact ⟨index.val, named, selected, rfl, accepted⟩
                · exact tail.admitted row member }
  go (List.finRange compiled.indexed.base.functions.length)

/-- Pure proof transfer connects data-only scanning to any authentic ordinary
catalog. No catalog Input needs to be inspected by an executable checker. -/
theorem Table.aligned {compiled : SourceCoreUnifiedCompilation.Compiled}
    (table : Table compiled) (catalog : Catalog compiled) :
    ∀ row ∈ table.rows, ∃ input : Input compiled, input ∈ catalog.inputs ∧ input.row = row := by
  intro row member
  obtain ⟨index, named, selected, same, eligible⟩ := table.admitted row member
  obtain ⟨input, retained, _slot, actual⟩ := catalog.covered index named selected (same.symm ▸ eligible)
  exact ⟨input, retained, (input.prepared.same.symm.trans (congrArg (·.specialized) actual)).trans same⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySyntaxTable
