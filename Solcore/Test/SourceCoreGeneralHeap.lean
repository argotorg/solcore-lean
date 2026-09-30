import Solcore.SourceSemantics.CoreLowering.GeneralHeap

/-! Source cells need not occupy the same Core indices, or even share one
constant offset. Administrative closures can capture mapped source cells and
form cycles through an optional function cell without recursively typing the
store. These are representation tests, not source-closure execution proofs. -/

set_option autoImplicit false

namespace Tests.SourceCoreGeneralHeap

open Solcore Solcore.Frontend Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def functionType : Core.Ty := .function .unit (Core.LanguageResult.resultType .word)
private def optionalFunction : Core.Ty := Core.OptionalCell.cellType functionType
private def optionalWord : Core.Ty := Core.OptionalCell.cellType .word
private def world : Core.StoreTyping := [optionalFunction, optionalWord]
private def sourceCell (value : Nat) : Dynamic.Cell := { type := .word, value := some (.word (word value)) }
private def sourceHeap (value : Nat) : Dynamic.Heap := ⟨[sourceCell value]⟩
private def presentWord (value : Nat) : Core.Value := .inRight .unit (.word (word value))
private def before : Core.Store := [.inLeft functionType .unit, presentWord 7]
private theorem beforeRelated : GeneralHeap.HeapRepresents [1] world (sourceHeap 7) before := by
  have admin : GeneralHeap.HeapRepresents [] [optionalFunction] ⟨[]⟩ [.inLeft functionType .unit] :=
    GeneralHeap.HeapRepresents.empty.allocate_administrative (.inLeft .unit)
  exact (admin.allocate (.initialized (.word (word 7))) .append).1

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"general_heap", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : Resolved.LocalId := ⟨owner, 0⟩
private def capture : Core.Environment := [.cellRef optionalWord 1, .cellRef optionalFunction 0]
private def sourceCapture : Dynamic.Environment := [(binder, ⟨0⟩)]
private def scope : SourceCoreLocalCell.Scope := [(binder, .word)]
private theorem captures : GeneralHeap.EnvRepresents [1] world [.cell optionalFunction]
    scope sourceCapture capture :=
  .cons ⟨rfl, rfl⟩ (.nil (.cons (.cellRef rfl) .nil))

/-- The function may call its own optional cell. The capture includes both
that cell and the mutable source cell, so the resulting store is cyclic. -/
private def body : Core.Expr :=
  .caseE (.loadCell (.var 2)) (.inLeft .word (.word (word 90))) (.apply (.var 0) (.var 1))
private def function : Core.Value := .closure .unit (Core.LanguageResult.resultType .word) body capture
private theorem functionTyped : Core.RuntimeValueHasType world function functionType := by
  apply Core.RuntimeValueHasType.closure captures.runtime_hasTypes
  exact .caseE (.loadCell (.var rfl)) (.inLeft .word .word) (.apply (.var rfl) (.var rfl))
private def installed : Core.Store := [.inRight .unit function, presentWord 7]
private theorem installedRelated : GeneralHeap.HeapRepresents [1] world (sourceHeap 7) installed := by
  apply beforeRelated.write_administrative (location := 0) (type := optionalFunction)
  · intro index impossible
    cases index <;> simp at impossible
  · rfl
  · exact .inRight functionTyped
  · rfl

/-- The complete store typing is finite even though cell zero contains a
closure whose captured environment refers back to cell zero. -/
example : Core.RuntimeStoreHasTypes world installed := installedRelated.runtime_hasTypes

private theorem sourceWritten : Dynamic.Heap.Writes (sourceHeap 7) ⟨0⟩
    (some (.word (word 9))) (sourceHeap 9) :=
  .intro (.intro .head) .head
private def updated : Core.Store := [.inRight .unit function, presentWord 9]
private theorem updatedRelated : GeneralHeap.HeapRepresents [1] world (sourceHeap 9) updated := by
  obtain ⟨actual, written, related⟩ := installedRelated.write_initialized
    (reference := ⟨rfl, rfl⟩) (.word (word 9)) rfl sourceWritten
  have expected : installed.write? 1 (presentWord 9) = some updated := rfl
  have same : actual = updated := Option.some.inj (written.symm.trans expected)
  exact same ▸ related

/-- Captures keep the original reference and see the new source cell value.
The administrative recursive closure stays installed at index zero. -/
example : Core.Evaluates capture updated
    (Core.OptionalCell.read .word (.var 0) (word 91))
    (.inRight .word (.word (word 9))) updated :=
  Core.OptionalCell.read_success _ (.var rfl) rfl
example : updated.read? 0 = some (.inRight .unit function) := rfl
example : ∃ source target cell value,
    Dynamic.Environment.LooksUp sourceCapture binder source ∧
    capture[0]? = some (.cellRef optionalWord target) ∧
    GeneralHeap.ReferenceRepresents [1] world source target .word ∧
    Dynamic.Heap.Reads (sourceHeap 9) source cell ∧ updated.read? target = some value ∧
    LocalCell.CellRepresents cell value .word :=
  captures.lookup_heap updatedRelated rfl

private def administrativeWorld : Core.StoreTyping := world ++ [functionType]
private def administrativeStore : Core.Store := updated ++ [function]
private theorem administrativeRelated : GeneralHeap.HeapRepresents [1]
    administrativeWorld (sourceHeap 9) administrativeStore :=
  updatedRelated.allocate_administrative functionTyped

/-- Adding a second administrative function cell does not allocate any source
location. The next source cell consequently maps to Core index three. -/
private def finalHeap : Dynamic.Heap := ⟨(sourceHeap 9).cells ++ [{ type := .bool, value := none }]⟩
private def finalWorld : Core.StoreTyping := administrativeWorld ++ [Core.OptionalCell.cellType .bool]
private def finalStore : Core.Store := administrativeStore ++ [.inLeft .bool .unit]
private theorem finalRelated : GeneralHeap.HeapRepresents [1, 3] finalWorld finalHeap finalStore :=
  (administrativeRelated.allocate (.uninitialized .bool) .append).1
example : GeneralHeap.ReferenceRepresents [1, 3] finalWorld ⟨1⟩ 3 .bool :=
  (administrativeRelated.allocate (.uninitialized .bool) .append).2
example : GeneralHeap.EnvRepresents [1, 3] finalWorld [.cell optionalFunction] scope sourceCapture capture :=
  captures.extend ⟨[3], rfl⟩ ⟨[functionType, Core.OptionalCell.cellType .bool], rfl⟩
example : Core.RuntimeStoreHasTypes finalWorld finalStore := finalRelated.runtime_hasTypes
example : finalStore.read? 1 = some (presentWord 9) := rfl
example : finalStore.read? 3 = some (.inLeft .bool .unit) := rfl

/-- The identity-map embedding reuses every existing exact-index heap proof. -/
example : GeneralHeap.HeapRepresents [0] [optionalWord] (sourceHeap 9) [presentWord 9] :=
  GeneralHeap.HeapRepresents.of_exact (.cons (.initialized (.word (word 9))) .nil)

/-- Distinct source cells cannot map to one Core location. -/
example : ¬ GeneralHeap.LocationMap.Injective [1, 1] := by
  intro injective
  have impossible : 0 = 1 := injective rfl rfl
  cases impossible

private def readId : SourceInference.ExpressionId := ⟨⟨owner, 0⟩⟩
private def readNode : SourceInference.ExpressionNode := {
  id := readId
  span := { source := { origin := .main, path := "general_heap.solc" }, startByte := 0, endByte := 1 }
  type := .word
  form := .reference "shared" (.local binder)
}
private def readSource : SourceInference.TypedSource := {
  owner, inputs := [], roots := [.expression readId], nodes := [.expression readNode]
}
private def readSite : LocalCell.ReadSite readSource scope readId .word := {
  node := readNode, binder, name := "shared", index := 0
  contains := lookupExpression?_sound rfl
  form := rfl, owner := rfl, requirements := rfl, coercions := rfl, slot := rfl, types := .word
}
private theorem readUnique : NodeOccurrencesUnique readSource := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide
example : SourceCoreLocalCell.lowerRead readSource scope readId (word 91) =
    .ok (Core.OptionalCell.read .word (.var 0) (word 91)) := readSite.lower readUnique _

/-- The independent source read of source location zero corresponds to a
Core read of location one in the cyclic administrative heap. -/
example (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    ∃ location target sourceOutcome coreValue,
      GeneralHeap.ReferenceRepresents [1] world location target .word ∧
      Dynamic.ExpressionEvaluatesOutcome program context evidence readSource sourceCapture
        (sourceHeap 9) readId sourceOutcome (sourceHeap 9) ∧
      LocalCell.OutcomeRepresents location (word 91) sourceOutcome coreValue ∧
      Core.Evaluates capture updated (Core.OptionalCell.read .word (.var 0) (word 91)) coreValue updated :=
  GeneralHeap.read_preserves readSite program context evidence captures updatedRelated _

end Tests.SourceCoreGeneralHeap
