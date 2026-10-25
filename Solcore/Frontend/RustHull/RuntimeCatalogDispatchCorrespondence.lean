import Solcore.Frontend.RustHull.AccountCallRunCorrespondence
import Solcore.Frontend.RustHull.ContractCatalogCorrespondence

/-! The installed dispatcher selects a compiled frame by its actual runtime
identity. The selected branch retains the original frame allocator and child
completion wrapper. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCatalogDispatchCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

def invokeFrame (slots : List (String × Core.Ty)) (count index : Nat)
    (functions : Code) (shared : AccountRuntime.References) (dispatcher creator record frame : Code) : Code :=
  AccountRuntime.allocateFrame slots shared frame dispatcher creator (present (part 5 8 frame))
    (part 4 9 record) (part 5 9 record) (part 6 9 record) fun cells =>
      bind (apply (part index count functions) (packet cells)) AccountRuntime.childResult

def selectFrame (indices : List Nat) (record : Code) (invoke : Nat → Code) : Code :=
  indices.foldr (fun index fallback =>
    choose (binary .wordEq (part 3 9 record) (number (index + 1))) (invoke index) fallback)
    (failure Calls.responseType (number 16))

def runFrame (slots : List (String × Core.Ty)) (count : Nat)
    (functions : Code) (shared : AccountRuntime.References) (dispatcher creator record frame : Code) : Code :=
  selectFrame (List.range count) record
    (fun index => invokeFrame slots count index functions shared dispatcher creator record frame)

theorem objectHandlers_dispatch (slots : List (String × Core.Ty)) (count : Nat)
    (images : List (Nat × List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (functions : Code) (shared : AccountRuntime.References) (dispatcher creator : Code) :
    (AccountRuntime.objectHandlers slots count images catalog functions shared dispatcher creator).1 =
      lambda AccountRuntime.dispatchType (LanguageResult.resultType Calls.responseType)
        (AccountRuntime.dispatch shared (runFrame slots count functions shared dispatcher creator)) := rfl

theorem selectFrame_evaluates {indices : List Nat} {index : Nat} {identity : Word}
    {depth : Nat} {environment : Environment} {initial final : Store}
    {record : Code} {invoke : Nat → Code} {result : Value}
    (selected : indices.find? (fun candidate => identity == Word.ofNatModulo (candidate + 1)) = some index)
    (represented : CodeValue depth environment (part 3 9 record) (.word identity))
    (executed : Core.Evaluates environment initial (invoke index depth) result final) :
    Core.Evaluates environment initial (selectFrame indices record invoke depth) result final := by
  induction indices with
  | nil => simp at selected
  | cons candidate rest ih =>
      by_cases matched : identity == Word.ofNatModulo (candidate + 1)
      · have same : candidate = index := by simpa [List.find?, matched] using selected
        subst candidate
        apply Core.Evaluates.ifTrue
        · exact .binary (represented.evaluates initial) .word (by
            change some (Core.Value.bool (identity == Word.ofNatModulo (index + 1))) = some (Core.Value.bool true)
            rw [matched])
        · exact executed
      · have rejected : (identity == Word.ofNatModulo (candidate + 1)) = false := Bool.eq_false_iff.mpr matched
        apply Core.Evaluates.ifFalse
        · exact .binary (represented.evaluates initial) .word (by
            change some (Core.Value.bool (identity == Word.ofNatModulo (candidate + 1))) = some (Core.Value.bool false)
            rw [rejected])
        · exact ih (by simpa [List.find?, rejected] using selected)

theorem runFrame_evaluates {slots : List (String × Core.Ty)} {count index : Nat}
    {functions : Code} {shared : AccountRuntime.References} {dispatcher creator record frame : Code}
    {depth : Nat} {environment : Environment} {initial final : Store}
    {account : AccountState.Account} {identity : Nat} {result : Value}
    (selected : (List.range count).find? (fun candidate => Word.ofNatModulo identity == Word.ofNatModulo (candidate + 1)) = some index)
    (represented : CodeValue depth environment record (StorageCorrespondence.record account identity))
    (executed : Core.Evaluates environment initial
      (invokeFrame slots count index functions shared dispatcher creator record frame depth) result final) :
    Core.Evaluates environment initial
      (runFrame slots count functions shared dispatcher creator record frame depth) result final :=
  selectFrame_evaluates selected (represented.part (index := 3) rfl) executed

end Solcore.Frontend.RustHull.RuntimeCatalogDispatchCorrespondence
