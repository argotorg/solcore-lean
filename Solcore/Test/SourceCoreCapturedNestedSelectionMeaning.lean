import Solcore.Test.SourceCoreCapturedNestedCommon
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputSelections

/-! The selected mapping rows retain their original order, duplicate keys and
repeated function occurrence. Each entry comes from the actual output codec. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedNested
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicNestedOutputSelections

def sourceArgument (first second : Dynamic.Value) : Dynamic.Value :=
  .mapping .word (.function .unit .word)
    [(.word (Core.Word.ofNatModulo 1), first),
     (.word (Core.Word.ofNatModulo 1), second),
     (.word (Core.Word.ofNatModulo 2), first)]

def outputSelection (first second third : SourceCorePublicValues.Handle) :
    Selection containerType (mappingArgument first second third) :=
  .mapping (.entry .skip .function (.entry .skip .function (.entry .skip .function .empty)))

structure Collected (first second : Dynamic.Value) (a b c : SourceCorePublicValues.Handle)
    (entries : List Entry) where
  firstEntry : Entry
  secondEntry : Entry
  repeatedEntry : Entry
  ordered : entries = [firstEntry, secondEntry, repeatedEntry]
  firstType : firstEntry.sourceType = .function .unit .word
  secondType : secondEntry.sourceType = .function .unit .word
  repeatedType : repeatedEntry.sourceType = .function .unit .word
  firstHandle : firstEntry.handle = a
  secondHandle : secondEntry.handle = b
  repeatedHandle : repeatedEntry.handle = c
  firstSource : firstEntry.source = first
  secondSource : secondEntry.source = second
  repeatedSource : repeatedEntry.source = first

theorem selected_uncast {checked : SourceCoreCompatibleCatalog.Checked}
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {type : TypeSystem.Ty} {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : Selection type first} {source : Dynamic.Value} {native : Core.Value}
    {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected checked session (same ▸ selection : Selection type second)
      source native nativeType fuel entries) :
    Selected checked session selection source native nativeType fuel entries := by
  cases same
  exact selected

theorem selected_entries {checked : SourceCoreCompatibleCatalog.Checked}
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {first second : Dynamic.Value} {a b c : SourceCorePublicValues.Handle}
    {native : Core.Value} {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected checked session (outputSelection a b c)
      (sourceArgument first second) native type fuel entries) :
    Nonempty (Collected first second a b c entries) := by
  cases selected with
  | mapping registered children =>
    cases children with
    | entry firstKey firstValue tail =>
      cases firstKey
      cases firstValue
      cases tail with
      | entry secondKey secondValue tail =>
        cases secondKey
        cases secondValue
        cases tail with
        | entry thirdKey thirdValue tail =>
          cases thirdKey
          cases thirdValue
          cases tail
          exact ⟨⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end Tests.SourceCoreCapturedNested
