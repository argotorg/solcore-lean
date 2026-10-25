import Solcore.Frontend.RustHull.MemoryCopySemantics

/-! A 33-byte copy uses one full word and one byte. Its final byte comes from
an immutable source even when the first destination write overlaps that byte. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullMemoryCopyDerivations
open Solcore Solcore.Frontend.RustHull
abbrev word := Core.Word.ofNatModulo

def calldata : List UInt8 := (List.range 32).map (fun index => UInt8.ofNat (index + 1))
def calldataWord : Core.Word := word 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
def calldataWords : MemorySemantics.Entries :=
  [(word 0, calldataWord)]

def copied33 (sourceWords destinationWords : MemorySemantics.Entries) (destination source : Core.Word) :
    MemorySemantics.Entries :=
  MemoryCopySemantics.written
    (MemoryCopySemantics.written destinationWords destination (word 33)
      (MemoryCopySemantics.copiedWord sourceWords source (word 33)))
    (destination.add (word 32)) (word 1)
    (MemoryCopySemantics.copiedWord (MemoryCopySemantics.remainingSource sourceWords source (word 33))
      (source.add (word 32)) (word 1))

theorem copy33 (sourceWords destinationWords : MemorySemantics.Entries) (destination source : Core.Word) :
    MemoryCopySemantics.Copy sourceWords destination source (word 33) destinationWords
      (copied33 sourceWords destinationWords destination source) := by
  apply MemoryCopySemantics.Copy.step (by decide)
  apply MemoryCopySemantics.Copy.step (by decide)
  exact .empty _ _ _ _

def first : MemorySemantics.State := ⟨copied33 calldataWords [] (word 1) (word 0), word 64⟩
def right : MemorySemantics.State := ⟨copied33 first.words first.words (word 2) (word 1), word 64⟩
def left : MemorySemantics.State := ⟨copied33 right.words right.words (word 0) (word 2), word 64⟩

theorem from_calldata :
    MemoryCopySemantics.From calldataWords (word 1) (word 0) (word 33) {} (.value .unit) first :=
  .done (by decide) (copy33 _ _ _ _)

theorem overlap_right :
    MemoryCopySemantics.Move (word 2) (word 1) (word 33) first (.value .unit) right :=
  .done (destinationSize := word 64) (by decide) (by decide) (by decide) (by decide) (copy33 _ _ _ _)

theorem overlap_left :
    MemoryCopySemantics.Move (word 0) (word 2) (word 33) right (.value .unit) left :=
  .done (destinationSize := word 64) (by decide) (by decide) (by decide) (by decide) (copy33 _ _ _ _)

theorem destination_overflow :
    MemoryCopySemantics.Move Core.Word.maximum (word 0) (word 1) left MemorySemantics.overflow left :=
  .destinationOverflow _ (by decide)

theorem source_overflow :
    MemoryCopySemantics.Move (word 96) Core.Word.maximum (word 1) left MemorySemantics.overflow left :=
  .sourceOverflow _ (by decide) (by decide)

theorem empty_maximum :
    MemoryCopySemantics.Move Core.Word.maximum Core.Word.maximum Core.Word.zero left (.value .unit) left :=
  .done (by decide) (by decide) (by rfl) (by rfl) (.empty _ _ _ _)

theorem zero_fill : MemoryCopySemantics.readByte first.words (word 33) = Core.Word.zero := by decide +kernel
theorem right_snapshot_tail : MemoryCopySemantics.readByte right.words (word 34) = Core.Word.zero := by decide +kernel
theorem right_previous_byte : MemoryCopySemantics.readByte right.words (word 33) = word 32 := by decide +kernel
theorem left_word : MemorySemantics.readWord left.words (word 0) = calldataWord := by decide +kernel
theorem left_tail : MemoryCopySemantics.readByte left.words (word 32) = Core.Word.zero := by decide +kernel

end Tests.RustHullMemoryCopyDerivations
