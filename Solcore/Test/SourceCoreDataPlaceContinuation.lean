import Solcore.SourceSemantics.CoreLowering.DataPlaceContinuation

/-! The continuation law retains the actual seven-slot capture environment.
Returning and invoking a closure observes the completed assignment; a failing
continuation also retains the already committed store.
-/
set_option autoImplicit false
namespace Tests.SourceCoreDataPlaceContinuation
open Solcore Solcore.Core Solcore.Frontend Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceContinuation

private def prepared : Prepared := ⟨⟨.integer, .integer, .integer, [], none⟩, [], [], Word.zero⟩
private def environment : Environment := [.cellRef (.sum .unit .integer) 0]
private def before : Store := [.inRight .unit (.integer 3), .integer 900]
private def after : Store := [.inRight .unit (.integer 17), .integer 900]
private def rhs : Expr := LanguageResult.success (.integer 17)
private def terminal : Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) rhs
  (LanguageResult.success .unit) .unit none false Word.zero
private theorem completed : Evaluates environment before terminal (.inRight .word .unit) after :=
  runStateful_evaluation_sound (show runStateful 100 (.initial terminal environment before) =
    .done (.inRight .word .unit) after by cbv)

private def closureType : Ty := .function .unit (.sum .unit .integer)
private def next : Expr := LanguageResult.success (.lambda .unit (.sum .unit .integer) (.loadCell (.var 1)))
private def captures : Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) rhs
  next closureType none false Word.zero

/-- The law does not equate closures that capture different environments.
It explicitly retains the seven values actually introduced by execute. -/
example : ∃ slots : Environment, slots.length = 7 ∧
    Evaluates environment before captures
      (.inRight .word (.closure .unit (.sum .unit .integer) (.loadCell (.var 8)) (slots ++ environment))) after := by
  obtain ⟨slots, length, finish⟩ := plug completed
  refine ⟨slots, length, finish ?_⟩
  simp [next, shift, List.range, List.range.loop, List.foldl, LanguageResult.success, Expr.weakenAt]
  exact .inRight .lambda

private def invoke : Expr := LanguageResult.bind (.sum .unit .integer) captures
  (LanguageResult.success (.apply (.var 0) .unit))
example : infer? [.cell (.sum .unit .integer)] invoke = some (.sum .word (.sum .unit .integer)) := by cbv
example : runStateful 140 (.initial invoke environment before) =
    .done (.inRight .word (.inRight .unit (.integer 17))) after := by cbv

private def failing : Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) rhs
  (LanguageResult.failure .bool (.word Word.zero)) .bool none false Word.zero
example : Evaluates environment before failing (.inLeft .bool (.word Word.zero)) after := by
  obtain ⟨slots, _, finish⟩ := plug completed
  apply finish
  simp only [shift, List.range, List.range.loop, List.foldl, LanguageResult.failure, Expr.weakenAt]
  exact .inLeft .word
example : runStateful 100 (.initial failing environment before) = .done (.inLeft .bool (.word Word.zero)) after := by cbv

/-- Source finite evaluation can be fed through the universal continuation
theorem in the production compiler proof; no additional fuel contract is
needed for this algebraic phase. -/
example : ∃ required, ∀ fuel, required ≤ fuel →
    runStateful fuel (.initial terminal environment before) = .done (.inRight .word .unit) after :=
  evaluation_runStateful_complete_with_sufficient_fuel completed

end Tests.SourceCoreDataPlaceContinuation
