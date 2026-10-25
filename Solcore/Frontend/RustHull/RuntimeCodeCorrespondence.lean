import Solcore.Frontend.RustHull.CodeBuilder
import Solcore.Frontend.RustHull.FunctionInstallationCorrespondence

/-! Values of runtime builder inputs are retained under the actual lexical
binders introduced while allocating frames and collecting their results. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

def CodeValue (depth : Nat) (environment : Core.Environment) (code : Code) (value : Core.Value) : Prop :=
  ∀ extra store, Core.Evaluates (extra ++ environment) store (code (depth + extra.length)) value store

theorem CodeValue.evaluates {depth : Nat} {environment : Core.Environment} {code : Code} {value : Core.Value}
    (related : CodeValue depth environment code value) (store : Core.Store) :
    Core.Evaluates environment store (code depth) value store := by
  simpa only [List.nil_append, List.length_nil, Nat.add_zero] using related [] store

theorem CodeValue.prepend {depth : Nat} {environment : Core.Environment} {code : Code} {value : Core.Value}
    (related : CodeValue depth environment code value) (earlier : Core.Environment) :
    CodeValue (depth + earlier.length) (earlier ++ environment) code value := by
  intro extra store
  simpa only [List.append_assoc, List.length_append, Nat.add_assoc, Nat.add_comm earlier.length extra.length]
    using related (extra ++ earlier) store

theorem CodeValue.bound (depth : Nat) (environment : Core.Environment) (value : Core.Value) :
    CodeValue (depth + 1) (value :: environment) (fun here => .var (here - depth - 1)) value := by
  intro extra store
  apply Core.Evaluates.var
  have index : depth + 1 + extra.length - depth - 1 = extra.length := by omega
  rw [index]
  simp

theorem CodeValue.number (value depth : Nat) (environment : Core.Environment) :
    CodeValue depth environment (CodeBuilder.number value) (.word (Core.Word.ofNatModulo value)) :=
  fun _ _ => .word

theorem CodeValue.boolean (value : Bool) (depth : Nat) (environment : Core.Environment) :
    CodeValue depth environment (CodeBuilder.boolean value) (.bool value) := fun _ _ => .bool

theorem CodeValue.unit (depth : Nat) (environment : Core.Environment) :
    CodeValue depth environment CodeBuilder.unit .unit := fun _ _ => .unit

theorem CodeValue.empty (depth : Nat) (environment : Core.Environment) :
    CodeValue depth environment CodeBuilder.empty (Core.WordMapping.encode []) := fun _ _ => .construct .unit

theorem CodeValue.mapping (entries : Core.WordMapping.Entries) (depth : Nat) (environment : Core.Environment) :
    CodeValue depth environment (constant (Core.WordMapping.literal entries)) (Core.WordMapping.encode entries) :=
  fun _ _ => Core.WordMapping.literal_evaluates _ _ _

theorem CodeValue.part {depth : Nat} {environment : Core.Environment} {code : Code} {values : List Core.Value}
    (related : CodeValue depth environment code (bundleValues values)) {index : Nat} {value : Core.Value}
    (found : values[index]? = some value) :
    CodeValue depth environment (part index values.length code) value :=
  fun extra store => projectArgument_evaluates (related extra store) found

inductive CodeValues (depth : Nat) (environment : Core.Environment) : List Code → List Core.Value → Prop where
  | nil : CodeValues depth environment [] []
  | cons {code value codes values} (head : CodeValue depth environment code value)
      (tail : CodeValues depth environment codes values) : CodeValues depth environment (code :: codes) (value :: values)

theorem CodeValues.prepend {depth : Nat} {environment : Core.Environment} {codes : List Code} {values : List Core.Value}
    (related : CodeValues depth environment codes values) (earlier : Core.Environment) :
    CodeValues (depth + earlier.length) (earlier ++ environment) codes values := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.prepend earlier) ih

theorem CodeValues.append {depth : Nat} {environment : Core.Environment}
    {first second : List Code} {left right : List Core.Value}
    (heads : CodeValues depth environment first left) (tails : CodeValues depth environment second right) :
    CodeValues depth environment (first ++ second) (left ++ right) := by
  induction heads with
  | nil => exact tails
  | cons head tail ih => exact .cons head ih

theorem CodeValues.reverse {depth : Nat} {environment : Core.Environment} {codes : List Code} {values : List Core.Value}
    (related : CodeValues depth environment codes values) : CodeValues depth environment codes.reverse values.reverse := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => simpa only [List.reverse_cons] using ih.append (.cons head .nil)

theorem CodeValues.length {depth : Nat} {environment : Core.Environment} {codes : List Code} {values : List Core.Value}
    (related : CodeValues depth environment codes values) : codes.length = values.length := by
  induction related with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

theorem CodeValues.of_getElem? {depth : Nat} {environment : Core.Environment}
    {codes : List Code} {values : List Core.Value}
    (length : codes.length = values.length)
    (related : ∀ (index : Nat) code value, codes[index]? = some code → values[index]? = some value →
      CodeValue depth environment code value) : CodeValues depth environment codes values := by
  induction codes generalizing values with
  | nil => cases values <;> simp_all only [List.length_nil, List.length_cons, Nat.zero_ne_add_one]; exact .nil
  | cons code codes ih =>
      cases values with
      | nil => simp at length
      | cons value values =>
          refine .cons (related 0 code value rfl rfl) (ih (Nat.succ.inj length) ?_)
          intro index tailCode tailValue codeFound valueFound
          exact related (index + 1) tailCode tailValue codeFound valueFound

theorem CodeValue.packet {depth : Nat} {environment : Core.Environment} {codes : List Code} {values : List Core.Value}
    (related : CodeValues depth environment codes values) :
    CodeValue depth environment (packet codes) (bundleValues values) := by
  intro extra store
  induction related with
  | nil => exact .unit
  | @cons code value codes values head tail ih =>
      cases tail with
      | nil => exact head extra store
      | cons next rest => exact .pair (head extra store) ih

end Solcore.Frontend.RustHull.Correspondence
