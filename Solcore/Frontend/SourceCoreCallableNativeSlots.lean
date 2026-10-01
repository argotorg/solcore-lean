import Solcore.Core.OptionalCell
import Solcore.Core.LanguageResult
import Solcore.Core.Safety

/-! Pure native environment checks shared by callable profiles. Receipts here
prove equality to the supplied installed code, heap and reference types. They
do not authenticate a source owner, a descriptor word, or execution history.
The enclosing artifact must supply its exact compilation receipt separately.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableNativeSlots
open Core

/-- Public native data paths stop at closures. Saved environments are never
treated as values returned by a source computation. -/
inductive Subvalue (value : Value) : Value → Prop where
  | root : Subvalue value value
  | pairLeft {left right : Value} (inside : Subvalue value left) : Subvalue value (.pair left right)
  | pairRight {left right : Value} (inside : Subvalue value right) : Subvalue value (.pair left right)
  | inLeft {type : Ty} {payload : Value} (inside : Subvalue value payload) : Subvalue value (.inLeft type payload)
  | inRight {type : Ty} {payload : Value} (inside : Subvalue value payload) : Subvalue value (.inRight type payload)
  | constructed {constructor : ConstructorId} {payload : Value} (inside : Subvalue value payload) :
      Subvalue value (.constructed constructor payload)

inductive Error where
  | missingGlobal (index : Nat)
  | globalTemplateMismatch (index : Nat)
  | globalsMismatch (location : Nat)
  | missingReference (index : Nat)
  | referenceMismatch (index : Nat)
  | referenceWorldMismatch (location : Nat)
  deriving Repr

/-- Input code has already undergone the caller's actual installation
renaming. Global positions are physical indices, independent of source heap
locations. Every installed closure saves the same globals and protocol tail. -/
def expectedGlobals (signatures : List (Ty × Ty)) (installed : List Expr)
    (environment : Environment) (base : Nat) : Except Error (List (Nat × Value)) := do
  if installed.length != signatures.length then throw (.missingGlobal 0)
  signatures.zipIdx.mapM fun ((parameter, result), index) => do
    let closure ← match installed[index]? with
      | some closure => pure closure | none => throw (.missingGlobal index)
    let .lambda actualParameter actualResult body := closure
      | throw (.globalTemplateMismatch index)
    if actualParameter != parameter || actualResult != LanguageResult.resultType result then
      throw (.globalTemplateMismatch index)
    pure (base + signatures.length - 1 - index,
      .inRight .unit (.closure parameter (LanguageResult.resultType result) body
        (List.replicate index .unit ++ environment)))

structure Globals (signatures : List (Ty × Ty)) (installed : List Expr)
    (environment : Environment) (base : Nat) (store : Store) where private mk ::
  slots : List (Nat × Value)
  generated : expectedGlobals signatures installed environment base = .ok slots
  exact : slots.all (fun (location, value) => decide (store[location]? = some value)) = true

/-- Runtime checking consumes precomputed code slots. No installation
renaming, signature traversal or source traversal is needed here. -/
def checkPreparedGlobals {signatures : List (Ty × Ty)} {installed : List Expr}
    {environment : Environment} {base : Nat} (slots : List (Nat × Value))
    (generated : expectedGlobals signatures installed environment base = .ok slots) (store : Store) :
    Except Error (Globals signatures installed environment base store) := do
  if exact : slots.all (fun (location, value) => decide (store[location]? = some value)) = true then
    pure ⟨slots, generated, exact⟩
  else
    match slots.find? (fun (location, value) => decide (store[location]? != some value)) with
    | some (location, _) => throw (.globalsMismatch location)
    | none => throw (.globalsMismatch base)

def checkGlobals (signatures : List (Ty × Ty)) (installed : List Expr)
    (environment : Environment) (base : Nat) (store : Store) :
    Except Error (Globals signatures installed environment base store) := do
  match generated : expectedGlobals signatures installed environment base with
  | .error error => throw error
  | .ok slots => checkPreparedGlobals slots generated store

theorem Globals.slot_exact {signatures : List (Ty × Ty)} {installed : List Expr}
    {environment : Environment} {base : Nat} {store : Store}
    (checked : Globals signatures installed environment base store)
    {location : Nat} {value : Value} (member : (location, value) ∈ checked.slots) :
    store[location]? = some value :=
  of_decide_eq_true (List.all_eq_true.mp checked.exact _ member)

structure Reference (environment : Environment) (world : StoreTyping) (index : Nat) (payloadType : Ty) where private mk ::
  location : Nat
  exact : environment[index]? = some (.cellRef (OptionalCell.cellType payloadType) location)
  worldExact : world[location]? = some (OptionalCell.cellType payloadType)

def reference (environment : Environment) (world : StoreTyping) (index : Nat) (payloadType : Ty) :
    Except Error (Reference environment world index payloadType) := do
  let value ← match environment[index]? with
    | some value => pure value | none => throw (.missingReference index)
  let .cellRef actual location := value | throw (.referenceMismatch index)
  if actual != OptionalCell.cellType payloadType then throw (.referenceMismatch index)
  if exact : environment[index]? = some (.cellRef (OptionalCell.cellType payloadType) location) then
    if worldExact : world[location]? = some (OptionalCell.cellType payloadType) then
      pure ⟨location, exact, worldExact⟩
    else throw (.referenceWorldMismatch location)
  else throw (.referenceMismatch index)

private theorem environment_slot_typed {definitions : DataEnvironment} {world : StoreTyping}
    {environment : Environment} {context : Context} {index : Nat} {value : Value}
    (typed : RuntimeEnvironmentHasTypes world environment context definitions)
    (found : environment[index]? = some value) : RuntimeValueHasType world value value.type definitions := by
  induction typed using RuntimeEnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True) generalizing index with
  | unit | bool | word | integer | pair | inLeft | inRight | closure | cellRef | constructed => trivial
  | nil => simp at found
  | cons valueTyped _ _ tailIH =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst value
      rw [valueTyped.type_eq]
      exact valueTyped
    | succ index => exact tailIH (by simpa using found)

/-- Inverting the saved environment preserves actual runtime typing. The
requested slot is checked again by the owning profile for its expected type. -/
theorem saved_slot_typed {definitions : DataEnvironment} {world : StoreTyping}
    {environment : Environment} {body : Expr} {parameter result : Ty} {index : Nat} {value : Value}
    (typed : RuntimeValueHasType world (.closure parameter result body environment) (.function parameter result) definitions)
    (found : environment[index]? = some value) : RuntimeValueHasType world value value.type definitions := by
  cases typed with
  | closure environmentTyped _ => exact environment_slot_typed environmentTyped found

end Solcore.Frontend.SourceCoreCallableNativeSlots
