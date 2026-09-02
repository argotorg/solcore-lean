import Solcore.Syntax.DeclarativeTopItemOutcomeGrammar
import Solcore.Syntax.DeclarativeTopItemRecoveryOutcomeGrammar

/-!
Parser-independent broad outcomes for the source-file item loop. The relation
retains source-order items, rewinds a rejected item to its original cursor,
and recovers only away from a recognized top-item boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A rejected top item retains its exact failed endpoint while preserving
the token carrier and active-window end needed for the file-loop rewind. -/
def TopItemRejectsWithPreservedWindow (input : Remainder) : Prop :=
  ∃ failed, TopItemRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Forward-order exact successful outcomes of the recovery-aware file-item
loop, independent of its executable reverse accumulator. -/
inductive FileItemsOrdinaryParses :
    Remainder → List Syntax.TopItem → Remainder → Prop where
  | done {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      FileItemsOrdinaryParses input [] input
  | direct {input afterItem output : Remainder}
      {item : Syntax.TopItem} {items : List Syntax.TopItem}
      (inside : input.cursor < input.endIndex)
      (itemParsed : TopItemOrdinaryParses input item afterItem)
      (progress : input.cursor < afterItem.cursor)
      (tail : FileItemsOrdinaryParses afterItem items output) :
      FileItemsOrdinaryParses input (item :: items) output
  | boundaryStop {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (itemRejected : TopItemRejectsWithPreservedWindow input)
      (boundaryPresent : ImportTerminatorTopItemStartsAt input) :
      FileItemsOrdinaryParses input [] input
  | recovered {input afterRecovery output : Remainder}
      {item : Syntax.TopItem} {items : List Syntax.TopItem}
      (inside : input.cursor < input.endIndex)
      (itemRejected : TopItemRejectsWithPreservedWindow input)
      (boundaryAbsent : ¬ ImportTerminatorTopItemStartsAt input)
      (recoveryParsed : TopItemRecoveryParses input item afterRecovery)
      (tail : FileItemsOrdinaryParses afterRecovery items output) :
      FileItemsOrdinaryParses input (item :: items) output

/-- Exact first rejection of the prioritized recovery-aware file-item loop.
Ordinary top-item rejection itself is rewound; only recovery or a later loop
step can reject. -/
inductive FileItemsRejects : Remainder → Remainder → Prop where
  | recoveryRejected {input rejected : Remainder}
      (inside : input.cursor < input.endIndex)
      (itemRejected : TopItemRejectsWithPreservedWindow input)
      (boundaryAbsent : ¬ ImportTerminatorTopItemStartsAt input)
      (rejectedRecovery : TopItemRecoveryRejects input rejected) :
      FileItemsRejects input rejected
  | laterDirect {input afterItem rejected : Remainder}
      {item : Syntax.TopItem}
      (inside : input.cursor < input.endIndex)
      (itemParsed : TopItemOrdinaryParses input item afterItem)
      (progress : input.cursor < afterItem.cursor)
      (tailRejected : FileItemsRejects afterItem rejected) :
      FileItemsRejects input rejected
  | laterRecovered {input afterRecovery rejected : Remainder}
      {item : Syntax.TopItem}
      (inside : input.cursor < input.endIndex)
      (itemRejected : TopItemRejectsWithPreservedWindow input)
      (boundaryAbsent : ¬ ImportTerminatorTopItemStartsAt input)
      (recoveryParsed : TopItemRecoveryParses input item afterRecovery)
      (tailRejected : FileItemsRejects afterRecovery rejected) :
      FileItemsRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
