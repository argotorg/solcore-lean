import Solcore.Frontend.SourceCoreRecursiveEntry
import Solcore.Frontend.SourceCoreLambdaTemplates
import Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning
import Solcore.Core.Correspondence

/-! Actual global reservations and cached lambda installation are finite Core
prefixes. Their exact physical references, closure code and captured Unit
binders are derived from emitted syntax, independently of source body meaning.
The continuation law is explicit in general composition. Source attribution,
initial frame history, represented heaps and catalog Authority remain separate.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationMeaning
open Core Frontend
abbrev Signature := SourceCoreCalls.Signature

/-- Pure layout of the emitted reservations, in actual allocation order. -/
def reserve (signatures : List Signature) (store : Store) (environment : Environment) : Store × Environment :=
  match signatures with
  | [] => (store, environment)
  | signature :: rest => reserve rest (store ++ [.inLeft signature.functionType .unit])
      (.cellRef (OptionalCell.cellType signature.functionType) store.length :: environment)

theorem reserved_store (signatures : List Signature) (store : Store) (environment : Environment) :
    (reserve signatures store environment).1 = store ++ signatures.map (fun signature => .inLeft signature.functionType .unit) := by
  induction signatures generalizing store environment with
  | nil => simp [reserve]
  | cons signature rest ih =>
    simp only [reserve, ih, List.map_cons, List.append_assoc, List.singleton_append]

/-- The actual reversed environment retains each reservation's allocation
location and full optional function-cell type. -/
theorem reserved_environment (signatures : List Signature) (store : Store) (environment : Environment) :
    (reserve signatures store environment).2 =
      ((signatures.zipIdx store.length).map (fun (signature, location) =>
        Value.cellRef (OptionalCell.cellType signature.functionType) location)).reverse ++ environment := by
  induction signatures generalizing store environment with
  | nil => simp [reserve]
  | cons signature rest ih =>
    simp only [reserve, ih, List.length_append, List.length_singleton,
      List.zipIdx_cons, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem reserved_prefix (signatures : List Signature) (store : Store) (environment : Environment)
    {location : Nat} (earlier : location < store.length) :
    (reserve signatures store environment).1.read? location = store.read? location := by
  rw [reserved_store]
  exact List.getElem?_append_left earlier

/-- A row in the actual newest-first global inventory determines its physical
reference; no environment lookup or allocation bound is an assumed law. -/
theorem reserved_reference (signatures : List Signature) (store : Store) (environment : Environment)
    {index : Nat} {signature : Signature} (found : signatures.reverse[index]? = some signature) :
    (reserve signatures store environment).2[index]? = some
      (.cellRef (OptionalCell.cellType signature.functionType) (store.length + (signatures.length - 1 - index))) := by
  have within : index < signatures.length := by
    obtain ⟨valid, _⟩ := List.getElem?_eq_some_iff.mp found
    simpa using valid
  rw [reserved_environment, List.getElem?_append_left (by simpa using within)]
  rw [List.getElem?_reverse (by simpa using within)]
  simp only [List.length_map, List.length_zipIdx, List.getElem?_map, List.getElem?_zipIdx]
  rw [List.getElem?_reverse (by simpa using within)] at found
  rw [found]
  rfl

theorem reserved_location_bound (signatures : List Signature) (store : Store) (environment : Environment)
    {index : Nat} (within : index < signatures.length) :
    store.length + (signatures.length - 1 - index) < (reserve signatures store environment).1.length := by
  rw [reserved_store]
  simp only [List.length_append, List.length_map]
  omega

/-- The original allocation prefix has exactly the same child evaluation,
with no execution of a source expression or a function body. -/
theorem allocated_iff (signatures : List Signature) (body : Expr)
    (environment : Environment) (store finalStore : Store) (value : Value) :
    Evaluates environment store (SourceCoreRecursiveEntry.allocateGlobals signatures body) value finalStore ↔
    Evaluates (reserve signatures store environment).2 (reserve signatures store environment).1 body value finalStore := by
  induction signatures generalizing environment store with
  | nil => rfl
  | cons signature rest ih =>
    change Evaluates environment store (.letE (OptionalCell.allocate signature.functionType)
      (SourceCoreRecursiveEntry.allocateGlobals rest body)) value finalStore ↔ _
    constructor
    · intro completed
      cases completed with
      | letE allocated tail =>
        cases allocated with
        | newCell initialized =>
          cases initialized with
          | inLeft payload =>
            cases payload
            exact (ih _ _).mp tail
    · intro completed
      exact .letE (.newCell (.inLeft .unit)) ((ih _ _).mpr completed)

/-- A syntactic cached lambda row; it contains no execution law. -/
structure LambdaRow where
  parameter : Ty
  result : Ty
  body : Expr

def LambdaRow.expression (row : LambdaRow) : Expr := .lambda row.parameter row.result row.body

def shift (count : Nat) : Renaming := fun index => index + count

def shifted (count : Nat) (expression : Expr) : Expr := expression.rename (shift count)

private theorem shifted_weaken (count : Nat) (expression : Expr) :
    (expression.weakenAt 0).rename (shift count).lift = shifted (count + 1) expression := by
  rw [← Expr.rename_insertion, Expr.rename_comp]
  apply congrArg (Expr.rename expression)
  funext index
  simp [Renaming.comp, Renaming.insertion, Renaming.lift, shift, Nat.add_assoc]

private theorem shifted_front (count : Nat) (expression : Expr) :
    (shifted count expression).weakenAt 0 = shifted (count + 1) expression := by
  unfold shifted
  rw [← Expr.rename_insertion, Expr.rename_comp]
  apply congrArg (Expr.rename expression)
  funext index
  simp [Renaming.comp, Renaming.insertion, shift, Nat.add_assoc]

theorem installed_template (count : Nat) (expression : Expr) :
    SourceCoreLambdaTemplates.installedTemplate count expression = shifted count expression := by
  induction count with
  | zero =>
    have same : shift 0 = Renaming.id := by funext index; simp [shift, Renaming.id]
    simp [SourceCoreLambdaTemplates.installedTemplate, shifted, same]
  | succ count ih =>
    rw [SourceCoreLambdaTemplates.installedTemplate, List.range_succ, List.foldl_append]
    change (SourceCoreLambdaTemplates.installedTemplate count expression).weakenAt 0 = _
    rw [ih, shifted_front]

/-- Exact captured code includes every prior installer Unit binder. -/
def installedValue (environment : Environment) (index : Nat) (row : LambdaRow) : Value :=
  .closure row.parameter row.result (row.body.rename (shift index).lift)
    (List.replicate index .unit ++ environment)

private def installItems (rows : List LambdaRow) (index : Nat) (body : Expr) : Expr :=
  (rows.zipIdx index).foldr (fun (row, slot) continuation =>
    .letE (.storeCell (.var slot) (.inRight .unit row.expression)) (continuation.weakenAt 0)) body

private theorem installItems_actual (rows : List LambdaRow) (body : Expr) :
    installItems rows 0 body = SourceCoreRecursiveEntry.installFunctions (rows.map LambdaRow.expression) body := by
  simp only [installItems, SourceCoreRecursiveEntry.installFunctions, List.zipIdx_map, List.foldr_map, Prod.map, id]

def installStore (rows : List LambdaRow) (locations : Nat → Location) (environment : Environment)
    (store : Store) (index : Nat) : Store :=
  match rows with
  | [] => store
  | row :: rest => installStore rest locations environment
      (store.set (locations index) (.inRight .unit (installedValue environment index row))) (index + 1)

theorem installed_length (rows : List LambdaRow) (locations : Nat → Location)
    (environment : Environment) (store : Store) (index : Nat) :
    (installStore rows locations environment store index).length = store.length := by
  induction rows generalizing store index with
  | nil => rfl
  | cons row rest ih => simp only [installStore, ih, List.length_set]

private theorem shifted_install_iff (rows : List LambdaRow) (body : Expr)
    (environment : Environment) (store finalStore : Store) (locations : Nat → Location) (index : Nat) (value : Value)
    (references : ∀ i row, rows[i]? = some row → environment[index + i]? =
      some (.cellRef (OptionalCell.cellType (.function row.parameter row.result)) (locations (index + i))))
    (bounds : ∀ i, i < rows.length → locations (index + i) < store.length) :
    Evaluates (List.replicate index .unit ++ environment) store (shifted index (installItems rows index body)) value finalStore ↔
    Evaluates (List.replicate (index + rows.length) .unit ++ environment)
      (installStore rows locations environment store index) (shifted (index + rows.length) body) value finalStore := by
  induction rows generalizing store index with
  | nil => simp only [installItems, List.zipIdx_nil, List.foldr_nil, List.length_nil, Nat.add_zero, installStore]
  | cons row rest ih =>
    have reference : (List.replicate index .unit ++ environment)[index + index]? =
        some (.cellRef (OptionalCell.cellType (.function row.parameter row.result)) (locations index)) := by
      rw [List.getElem?_append_right (by simp)]
      simpa using references 0 row rfl
    have bound : locations index < store.length := by simpa using bounds 0 (by simp)
    obtain ⟨old, read⟩ : ∃ old, store.read? (locations index) = some old := by
      exact ⟨store[locations index], List.getElem?_eq_getElem bound⟩
    let nextStore := store.set (locations index) (.inRight .unit (installedValue environment index row))
    have written : store.write? (locations index) (.inRight .unit (installedValue environment index row)) = some nextStore :=
      Store.write?_eq_some_iff.mpr ⟨bound, rfl⟩
    have write : Evaluates (List.replicate index .unit ++ environment) store
        (shifted index (.storeCell (.var index) (.inRight .unit row.expression))) .unit nextStore := by
      exact .storeCell (.var reference) read (.inRight .lambda) written
    have tailReferences : ∀ i selected, rest[i]? = some selected → environment[index + 1 + i]? =
        some (.cellRef (OptionalCell.cellType (.function selected.parameter selected.result)) (locations (index + 1 + i))) := by
      intro i selected found
      have selected := references (i + 1) selected found
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using selected
    have tailBounds : ∀ i, i < rest.length → locations (index + 1 + i) < nextStore.length := by
      intro i within
      have valid := bounds (i + 1) (by simpa using Nat.succ_lt_succ within)
      simpa only [nextStore, List.length_set, Nat.add_assoc, Nat.add_comm 1 i] using valid
    have tail := ih nextStore (index + 1) tailReferences tailBounds
    have length : index + (row :: rest).length = index + 1 + rest.length := by simp; omega
    rw [length]
    change Evaluates _ _ (.letE _ (((installItems rest (index + 1) body).weakenAt 0).rename (shift index).lift)) _ _ ↔ _
    rw [shifted_weaken]
    constructor
    · intro completed
      cases completed with
      | letE actual tailCompleted =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic actual write
        exact tail.mp (by simpa only [List.replicate_succ, List.cons_append] using tailCompleted)
    · intro completed
      exact .letE write (by simpa only [List.replicate_succ, List.cons_append] using tail.mpr completed)

/-- Actual installation introduces only its real Unit binders and store
writes. The continuation is the same emitted body under those binders. -/
theorem installed_iff (rows : List LambdaRow) (body : Expr)
    (environment : Environment) (store finalStore : Store) (locations : Nat → Location) (value : Value)
    (references : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → environment[i]? =
      some (.cellRef (OptionalCell.cellType (.function row.parameter row.result)) (locations i)))
    (bounds : ∀ i, i < rows.length → locations i < store.length) :
    Evaluates environment store (SourceCoreRecursiveEntry.installFunctions (rows.map LambdaRow.expression) body) value finalStore ↔
    Evaluates (List.replicate rows.length .unit ++ environment)
      (installStore rows locations environment store 0) (shifted rows.length body) value finalStore := by
  have meaning := shifted_install_iff rows body environment store finalStore locations 0 value (by simpa using references) (by simpa using bounds)
  have same : shift 0 = Renaming.id := by funext index; simp [shift, Renaming.id]
  simpa [shifted, same, installItems_actual] using meaning

/-- No write targets a protected location. This is derived from the real
ordered installer state, without treating closure typing as read authority. -/
theorem installed_preserves_other (rows : List LambdaRow) (locations : Nat → Location)
    (environment : Environment) (store : Store) (index location : Nat)
    (different : ∀ i, i < rows.length → locations (index + i) ≠ location) :
    (installStore rows locations environment store index).read? location = store.read? location := by
  induction rows generalizing store index with
  | nil => rfl
  | cons row rest ih =>
    rw [installStore, ih]
    · exact List.getElem?_set_ne (by simpa using different 0 (by simp))
    · intro i within
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using different (i + 1) (by simpa using Nat.succ_lt_succ within)

/-- Each final read retains this row's full installed code and actual captured
environment. Distinctness is required only for real occupied slots. -/
theorem installed_read (rows : List LambdaRow) (locations : Nat → Location)
    (environment : Environment) (store : Store) (index : Nat)
    (bounds : ∀ i, i < rows.length → locations (index + i) < store.length)
    (distinct : ∀ i j, i < rows.length → j < rows.length → i ≠ j → locations (index + i) ≠ locations (index + j))
    {i : Nat} {row : LambdaRow} (found : rows[i]? = some row) :
    (installStore rows locations environment store index).read? (locations (index + i)) =
      some (.inRight .unit (installedValue environment (index + i) row)) := by
  induction rows generalizing store index i with
  | nil => simp at found
  | cons first rest ih =>
    cases i with
    | zero =>
      cases found
      rw [installStore, installed_preserves_other]
      · exact List.getElem?_set_self (by simpa using bounds 0 (by simp))
      · intro j within
        have diff := distinct (j + 1) 0 (by simpa using Nat.succ_lt_succ within) (by simp) (by omega)
        simpa only [Nat.add_assoc, Nat.add_zero, Nat.add_comm 1 j] using diff
    | succ i =>
      have nextBounds : ∀ j, j < rest.length → locations (index + 1 + j) <
          (store.set (locations index) (.inRight .unit (installedValue environment index first))).length := by
        intro j within
        simpa only [List.length_set, Nat.add_assoc, Nat.add_comm 1 j] using bounds (j + 1) (by simpa using Nat.succ_lt_succ within)
      have nextDistinct : ∀ j k, j < rest.length → k < rest.length → j ≠ k →
          locations (index + 1 + j) ≠ locations (index + 1 + k) := by
        intro j k hj hk ne
        have diff := distinct (j + 1) (k + 1) (by simpa using Nat.succ_lt_succ hj) (by simpa using Nat.succ_lt_succ hk) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 j, Nat.add_comm 1 k] using diff
      simpa only [installStore, Nat.add_assoc, Nat.add_comm 1 i] using
        ih (store.set (locations index) (.inRight .unit (installedValue environment index first))) (index + 1) nextBounds nextDistinct found

/-- Reservations append cells and every installation write is beyond the
old store. The complete old prefix survives, including any protocol frame. -/
theorem initialized_prefix (signatures : List Signature) (rows : List LambdaRow)
    (environment : Environment) (store : Store) (locations : Nat → Location)
    (later : ∀ i, i < rows.length → store.length ≤ locations i)
    {location : Nat} (earlier : location < store.length) :
    (installStore rows locations (reserve signatures store environment).2
      (reserve signatures store environment).1 0).read? location = store.read? location := by
  have unchanged := installed_preserves_other rows locations (reserve signatures store environment).2
    (reserve signatures store environment).1 0 location (by
      intro i within
      have beyond := later i within
      simpa only [Nat.zero_add] using (Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le earlier beyond))))
  exact unchanged.trans (reserved_prefix signatures store environment earlier)

/-- The actual bootstrap continuation is closed here. It does not call any
cached function body. Its successful result leaves every installed slot intact. -/
theorem bootstrap_evaluates (signatures : List Signature) (rows : List LambdaRow)
    (environment : Environment) (store : Store) (locations : Nat → Location)
    (references : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row →
      (reserve signatures store environment).2[i]? =
        some (.cellRef (OptionalCell.cellType (.function row.parameter row.result)) (locations i)))
    (bounds : ∀ i, i < rows.length → locations i < (reserve signatures store environment).1.length) :
    Evaluates environment store (SourceCoreRecursiveEntry.allocateGlobals signatures
      (SourceCoreRecursiveEntry.installFunctions (rows.map LambdaRow.expression) (LanguageResult.success .unit)))
      (.inRight .word .unit)
      (installStore rows locations (reserve signatures store environment).2 (reserve signatures store environment).1 0) := by
  apply (allocated_iff signatures _ environment store _ _).mpr
  apply (installed_iff rows _ _ _ _ locations _ references bounds).mpr
  exact .inRight .unit

/-- A static, ordered cache-to-signature receipt supplies the only remaining
installation premise. Every physical reference and allocation bound follows
from the actual reservation prefix. This receipt carries no body meaning. -/
theorem ordered_bootstrap_evaluates (signatures : List Signature) (rows : List LambdaRow)
    (environment : Environment) (store : Store)
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      signatures.reverse[i]? = some signature ∧ signature.functionType = .function row.parameter row.result) :
    Evaluates environment store (SourceCoreRecursiveEntry.allocateGlobals signatures
      (SourceCoreRecursiveEntry.installFunctions (rows.map LambdaRow.expression) (LanguageResult.success .unit)))
      (.inRight .word .unit)
      (installStore rows (fun index => store.length + (signatures.length - 1 - index))
        (reserve signatures store environment).2 (reserve signatures store environment).1 0) := by
  apply bootstrap_evaluates
  · intro i row found
    obtain ⟨signature, selected, same⟩ := ordered i row found
    simpa only [same] using reserved_reference signatures store environment selected
  · intro i within
    have found : rows[i]? = some rows[i] := List.getElem?_eq_getElem within
    obtain ⟨signature, selected, _⟩ := ordered i rows[i] found
    obtain ⟨valid, _⟩ := List.getElem?_eq_some_iff.mp selected
    exact reserved_location_bound signatures store environment (by simpa using valid)

end Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationMeaning
