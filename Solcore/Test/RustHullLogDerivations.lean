import Solcore.Frontend.RustHull.LogsSemantics

/-! Concrete independent event derivations: an unaligned 33-byte snapshot,
followed by a changed memory byte and a second one-byte event. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
namespace Tests.RustHullLogDerivations
open Solcore Solcore.Frontend.RustHull

abbrev word := Core.Word.ofNatModulo

def firstMemory : MemorySemantics.State :=
  (MemorySemantics.mstore8 {} (word 1) (word 171)).2

def firstWords (address : Core.Word) : LogsSemantics.Words :=
  [(word 0, address), (word 1, word 1), (word 2, word 33), (word 3, word 7),
    (word 4, LogsSemantics.paddedWord firstMemory.words (word 1) (word 33)),
    (word 5, LogsSemantics.paddedWord firstMemory.words (word 33) (word 1))]

def beforeFirst (address : Core.Word) : LogsSemantics.State :=
  {memory := firstMemory, address := address}

def afterFirst (address : Core.Word) : LogsSemantics.State :=
  {beforeFirst address with memory := {firstMemory with size := word 64}, words := firstWords address, cursor := word 6}

theorem first_append (address : Core.Word) :
    LogsSemantics.Append (word 1) (word 33) [word 7] (beforeFirst address) (.value .unit) (afterFirst address) := by
  apply LogsSemantics.Append.done (size := word 64) (words := firstWords address)
  · decide
  · change ¬word 0 > LogsSemantics.nextCursor (word 0) (word 33) [word 7]
    decide
  · change MemorySemantics.touchSize? firstMemory.size (word 1) (word 33) = some (word 64)
    decide
  · apply LogsSemantics.Copy.step (by decide)
    apply LogsSemantics.Copy.step (by decide)
    exact LogsSemantics.Copy.empty _ _ _

theorem first_execute (address : Core.Word) :
    LogsSemantics.Execute (word 1) (word 33) [word 7] (beforeFirst address) (.value .unit) (afterFirst address) :=
  .writable rfl (first_append address)

def overwrittenMemory : MemorySemantics.State :=
  (MemorySemantics.mstore8 {firstMemory with size := word 64} (word 1) (word 205)).2

def beforeSecond (address : Core.Word) : LogsSemantics.State :=
  {afterFirst address with memory := overwrittenMemory}

def secondWords (address : Core.Word) : LogsSemantics.Words :=
  firstWords address ++ [(word 6, address), (word 7, word 0), (word 8, word 1), (word 9, LogsSemantics.paddedWord overwrittenMemory.words (word 1) (word 1))]

def afterSecond (address : Core.Word) : LogsSemantics.State :=
  {beforeSecond address with words := secondWords address, cursor := word 10}

theorem second_append (address : Core.Word) :
    LogsSemantics.Append (word 1) (word 1) [] (beforeSecond address) (.value .unit) (afterSecond address) := by
  apply LogsSemantics.Append.done (size := word 64) (words := secondWords address)
  · decide
  · change ¬word 6 > LogsSemantics.nextCursor (word 6) (word 1) []
    decide
  · change MemorySemantics.touchSize? overwrittenMemory.size (word 1) (word 1) = some (word 64)
    decide
  · apply LogsSemantics.Copy.step (by decide)
    exact LogsSemantics.Copy.empty _ _ _

theorem second_execute (address : Core.Word) :
    LogsSemantics.Execute (word 1) (word 1) [] (beforeSecond address) (.value .unit) (afterSecond address) :=
  .writable rfl (second_append address)

theorem first_payload_retained (address : Core.Word) :
    MemorySemantics.lookup (word 4) (secondWords address) = LogsSemantics.paddedWord firstMemory.words (word 1) (word 33) := by
  rfl

theorem second_payload_changed (address : Core.Word) :
    MemorySemantics.lookup (word 9) (secondWords address) = LogsSemantics.paddedWord overwrittenMemory.words (word 1) (word 1) := by
  rfl


theorem first_payload_value :
    LogsSemantics.paddedWord firstMemory.words (word 1) (word 33) = word (171 * 256 ^ 31) := by
  decide +kernel

theorem first_tail_zero :
    LogsSemantics.paddedWord firstMemory.words (word 33) (word 1) = word 0 := by
  decide +kernel

theorem second_payload_value :
    LogsSemantics.paddedWord overwrittenMemory.words (word 1) (word 1) = word (205 * 256 ^ 31) := by
  decide +kernel

end Tests.RustHullLogDerivations
