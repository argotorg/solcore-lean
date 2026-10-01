import Solcore.SourceSemantics.CoreLowering.DataPlaceModifierReflection

/-! Modifier reflection distinguishes an absent compound-assignment snapshot
from ordinary initialization, and constructs the source primitive result for
any completed typed Word operation without assuming its source application. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataPlaceModifierReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload DataPlaceModifierReflection

private def catalog : SourceCoreDataCatalog.Catalog := {}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible

example (operator : Syntax.ValueAssignOp) (left right : Word) (before after : Store) (result : Value)
    (completed : Evaluates [.inRight .unit (.word left), .word right] before
      (modified .word (binaryOperator false operator) false (.var 0) (.var 1) Word.zero) result after) :
    after = before ∧ ∃ source value,
      Dynamic.AssignmentValueApplies operator (some (.word left)) (.word right) source ∧
      ValueRep catalog signatures functions [] [] .word source value .word ∧ result = .inRight .word value := by
  obtain ⟨sameStore, related⟩ := reflects (catalog := catalog) (signatures := signatures) (functions := functions)
    (.inr (.inl rfl)) (.present (.word left)) (.word right) (.var rfl) (.var (index := 1) rfl) completed
  refine ⟨sameStore, ?_⟩
  cases related with
  | applied applied value => exact ⟨_, _, applied, value, rfl⟩
  | uninitialized absent => cases absent

private def token : Word := ⟨17, by decide⟩
private def absentAdd : Expr := modified .integer (binaryOperator true .add) false (.var 0) (.var 1) token
private theorem absentRan : runStateful 30 (.initial absentAdd [.inLeft .integer .unit, .integer 5] [.integer 900]) =
    .done (.inLeft .integer (.word token)) [.integer 900] := by cbv

example : Dynamic.AssignmentOperandsInvalid .add none (.integer 5) := by
  have result := reflects (catalog := catalog) (signatures := signatures) (functions := functions)
    (mapping := []) (world := []) (.inr (.inr rfl)) .absent (.integer 5)
    (.var rfl) (.var (index := 1) rfl) (runStateful_evaluation_sound absentRan)
  exact result.2.invalid.2.2

private def initializeCode : Expr := modified .bool (binaryOperator false .equal) false (.var 0) (.var 1) token
private theorem initializeRan : runStateful 30 (.initial initializeCode [.inLeft .bool .unit, .bool true] [.integer 900]) =
    .done (.inRight .word (.bool true)) [.integer 900] := by cbv

example : ∃ source, Dynamic.AssignmentValueApplies .equal none (.bool true) source ∧
    ValueRep catalog signatures functions [] [] .bool source (.bool true) .bool := by
  have result := reflects (catalog := catalog) (signatures := signatures) (functions := functions)
    (mapping := []) (world := []) (.inl rfl) .absent (.bool true)
    (.var rfl) (.var (index := 1) rfl) (runStateful_evaluation_sound initializeRan)
  cases result.2 with
  | applied applied related => exact ⟨_, applied, related⟩

end Tests.SourceCoreDataPlaceModifierReflection
