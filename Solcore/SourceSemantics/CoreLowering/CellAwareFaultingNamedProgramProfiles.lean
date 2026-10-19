import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNamedBodyReceipt

/-! The complete ordered named cache receives finite compiler profiles.
Root extraction accepts only the actual statement-root action, and a selected
slot recovers its original profile without dropping any other cached row. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNamedProgramProfiles
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source)

def statements (named : SourceCoreGeneralFunctions.Function) :
    Except SourceCoreGeneralFunctions.Error (List StatementId) :=
  (source named).roots.mapM (fun
    | .statement id => pure id
    | .expression id => throw (.expectedStatementRoot id))

structure Entry {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) where
  roots : List StatementId
  extracted : statements named = .ok roots
  profile : CellAwareFaultingNamedBodyProducer.Profile prepared named roots
    named.specialized.function.inferredBodyType

def entry? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) : Option (Entry prepared named) :=
  match extracted : statements named with
  | .error _ => none
  | .ok roots => do
    let profile ← CellAwareFaultingNamedBodyProducer.profile? prepared named roots
      named.specialized.function.inferredBodyType
    pure ⟨roots, extracted, profile⟩

inductive Rows {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    List SourceCoreGeneralFunctions.Function → Type where
  | nil : Rows prepared []
  | cons {named rest} (entry : Entry prepared named) (tail : Rows prepared rest) :
      Rows prepared (named :: rest)

def rows? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    (named : List SourceCoreGeneralFunctions.Function) → Option (Rows prepared named)
  | [] => some .nil
  | named :: rest => do
    let entry ← entry? prepared named
    let tail ← rows? prepared rest
    pure (.cons entry tail)

abbrev Profile {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :=
  Rows prepared prepared.base.functions

def profile? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    Option (Profile prepared) := rows? prepared prepared.base.functions

theorem Rows.at_slot {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : List SourceCoreGeneralFunctions.Function} (rows : Rows prepared named)
    {index : Nat} {function : SourceCoreGeneralFunctions.Function}
    (selected : named[index]? = some function) : Nonempty (Entry prepared function) := by
  induction rows generalizing index with
  | nil => simp only [List.getElem?_nil] at selected; cases selected
  | cons entry tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero] at selected
      cases selected
      exact ⟨entry⟩
    | succ index => exact ih selected

def Entry.for_compilation {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} (entry : Entry prepared named)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) :
    CellAwareFaultingNamedBodyProducer.Profile prepared named compiled.statements
      named.specialized.function.inferredBodyType := by
  have same : entry.roots = compiled.statements := Except.ok.inj (entry.extracted.symm.trans compiled.roots)
  exact same ▸ entry.profile

end Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNamedProgramProfiles
