import Solcore.SourceSemantics.CoreLowering.DataPlaceWriteBack
import Solcore.SourceSemantics.CoreLowering.DataPlaceExecution

/-! A commit consumer preserves an unmapped administrative cell and two
references to the same mapped source location. The source snapshot may precede
the latest cell, which is the one reconstructed and written. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataPlaceWriteBack
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces GeneralHeap GenericHeap DataEquality
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def model := finitePayload catalog signatures
private def prepared : Prepared := ⟨⟨.integer, .integer, .integer, [], none⟩, [], [], Word.zero⟩
private def cell : Dynamic.Cell := ⟨.integer, some (.integer 7), none⟩
private def heap : Dynamic.Heap := ⟨[cell]⟩
private def world : StoreTyping := [.sum .unit .integer, .integer]
private def store : Store := [.inRight .unit (.integer 7), .integer 900]
private def argument : Value := .pair (.inRight .unit (.integer 7)) (.pair .unit (.integer 55))
private def environment : Environment := [.cellRef (.sum .unit .integer) 0, .cellRef (.sum .unit .integer) 0, argument]
private def context : Core.Context := [.cell (.sum .unit .integer), .cell (.sum .unit .integer),
  .product (.sum .unit .integer) (.product .unit .integer)]
private theorem related : HeapRepresents model [0] world heap store := by
  have empty : HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  have represented : model.Represents [] [] .integer (.integer 7) (.integer 7) .integer := ⟨rfl, .integer 7⟩
  exact (empty.allocate (.initialized represented) .append).1.allocate_administrative .integer
private theorem environmentTyped : RuntimeEnvironmentHasTypes world environment context catalog.definitions :=
  .cons (.cellRef rfl) (.cons (.cellRef rfl) (.cons (.pair (.inRight .integer) (.pair .unit .integer)) .nil))
private theorem faithful : IdentityFaithful (fun _ _ => False) := by constructor <;> intros <;> contradiction
private def expression : Expr := DataPlaceWriteBack.commit prepared .unit (.var 0) (.var 2)

example : ∃ updatedValue finalHeap finalStore futureWorld,
    Dynamic.ResolvedPlaceWrites (fun _ value => value = .integer 55) heap
      ⟨⟨0⟩, .integer, .integer, [], some (.integer 3)⟩ (.integer 55) finalHeap ∧
    Evaluates environment store expression (.inRight .word .unit) finalStore ∧
    WorldExtends world futureWorld ∧ HeapRepresents model [0] futureWorld finalHeap finalStore ∧
    model.Represents [0] futureWorld .integer (.integer 55) updatedValue .integer ∧
    finalStore.read? 0 = some (.inRight .unit updatedValue) ∧ AdministrativePreserved [0] store [0] finalStore := by
  have tree : DataPlaceUpdateTree.Tree checked signatures (fun _ _ => False) prepared []
      (.integer 55) (.integer 55) (fun source value => model.Represents [0] world cell.type source value .integer)
      (.integer 7) (.integer 7) [] [] (.integer 55) 0 := .leaf ⟨rfl, .integer 55⟩
  exact DataPlaceWriteBack.commit_preserves related ⟨rfl, rfl⟩ (.intro .head) rfl
    (.initialized .integer (.integer 7) (.integer 7)) tree rfl faithful rfl environmentTyped
    (infer_sound (by decide)) (.var rfl) (.var rfl) .integer (some (.integer 3))

private def observeAliases : Expr := .letE expression
  (LanguageResult.success (.pair (.loadCell (.var 1)) (.loadCell (.var 2))))
example : infer? context observeAliases = some (.sum .word (.product (.sum .unit .integer) (.sum .unit .integer))) := by
  simp [observeAliases, expression, DataPlaceWriteBack.commit, prepared, setter, LanguageResult.bind,
    LanguageResult.success, OptionalCell.cellType, LanguageResult.resultType, Expr.weakenAt]
  decide
example : runStateful 100 (.initial observeAliases environment store) =
    .done (.inRight .word (.pair (.inRight .unit (.integer 55)) (.inRight .unit (.integer 55))))
      [.inRight .unit (.integer 55), .integer 900] := by cbv

end Tests.SourceCoreDataPlaceWriteBack
