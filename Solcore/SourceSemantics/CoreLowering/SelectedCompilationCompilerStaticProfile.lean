import Solcore.SourceSemantics.ProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinarySyntaxTable
import Solcore.SourceSemantics.CoreLowering.CompilerProgramStaticProfile

/-! The finite profile scans the complete actual cache using signature facts.
Its original row receipts and acceptance checks are preserved. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile
open Core Frontend SourceInference
open CompilerProgramStaticProfile

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

def row? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {index : Nat} (named : SourceCoreGeneralFunctions.Function)
    (selected : compiled.indexed.base.functions[index]? = some named)
    (rows : List SourceSpecialization.SpecializedFunction) : Option (Row compiled named rows) := do
  if absent : compiled.sourceProgram.signatures.functions.all (fun signature =>
      decide (named.specialized.declaration ≠ signature.id)) = true then
    let ⟨range⟩ ← CallableIndexedOwnedPreparedOrdinarySyntaxTable.range?
      compiled.sourceProgram.signatures (max 1 compiled.indexed.fuel) named.specialized.parameterSubstitution
    let ⟨forms⟩ ← CallableIndexedOwnedPreparedScopedMethodAdmission.directSource? named.specialized.function.typedBody
    let profile ← scoped? compiled named rows true
    pure (.method (fun signature member => of_decide_eq_true (List.all_eq_true.mp absent signature member))
      range forms profile)
  else
    let ⟨eligible⟩ ← SelectedCompilationOrdinarySyntaxTable.eligible? compiled signatures
      (max 1 compiled.indexed.fuel) named selected
    if excluded : (Program.ofChecked compiled.sourceProgram).methods.all (fun definition =>
        decide (named.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
      let profile ← ordinary? compiled named rows
      pure (.ordinary eligible (fun definition member =>
        of_decide_eq_true (List.all_eq_true.mp excluded definition member)) profile)
    else none

def validateProfile (compiled : SourceCoreUnifiedCompilation.Compiled)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures) :
    Option (StaticProfile compiled) := do
  if callable : compiled.compatible.checked.catalog.callableContracts = true then
    match present : compiled.indexed.base.diagnostics with
    | none => none
    | some diagnostics =>
      let table := SelectedCompilationOrdinarySyntaxTable.collect compiled signatures
        (max 1 compiled.indexed.fuel)
      let ⟨catalog⟩ ← CallableIndexedOwnedPreparedOriginsMethodAdmission.certify compiled
      let ⟨rows⟩ ← allProof?
        (fun index : Fin compiled.indexed.base.functions.length =>
          Nonempty (Row compiled compiled.indexed.base.functions[index.val] table.rows))
        (fun index => do
          let profile ← row? compiled signatures compiled.indexed.base.functions[index.val]
            (List.getElem?_eq_getElem index.isLt) table.rows
          pure ⟨⟨profile⟩⟩) (List.finRange compiled.indexed.base.functions.length)
      pure ⟨table, catalog, fun index => rows index (List.mem_finRange index), callable, diagnostics, present⟩
  else none

/-- Genuine checker success supplies the signature catalog internally. -/
def validateCheckedProfile (compiled : SourceCoreUnifiedCompilation.Compiled)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    Option (StaticProfile compiled) :=
  validateProfile compiled (SignatureCatalogWellFormed.ofCheckProgram checked)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile
