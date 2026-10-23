import Solcore.Frontend.RustHull.ScalarExecutionSafety
import Solcore.Frontend.RustHull.LiteralCorrespondence

/-! Actual public scalar arguments denote independent Hull values. The parser
constructs closed Core literals, whose evaluation preserves every input heap.
Arguments retain their source order and the compiler's unit/scalar/product
bundle convention. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.ScalarExecution
open Correspondence

inductive InputRel : Core.Ty → String → Semantics.Value → Prop where
  | word {input : String} {value : Core.Word} (parsed : Semantics.parseWord? input = some value) :
      InputRel .word input (.word value)
  | boolTrue : InputRel .bool "true" (.bool true)
  | boolFalse : InputRel .bool "false" (.bool false)
  | sumTrue : InputRel (.sum .unit .unit) "true" (.inr .unit)
  | sumFalse : InputRel (.sum .unit .unit) "false" (.inl .unit)
  | unit : InputRel .unit "unit" .unit

inductive InputsRel : List Core.Ty → List String → List Semantics.Value → Prop where
  | nil : InputsRel [] [] []
  | cons {type : Core.Ty} {types : List Core.Ty} {input : String} {inputs : List String}
      {value : Semantics.Value} {values : List Semantics.Value}
      (head : InputRel type input value) (tail : InputsRel types inputs values) :
      InputsRel (type :: types) (input :: inputs) (value :: values)

inductive ValuesRel : List Core.Ty → List Semantics.Value → List Core.Value → Prop where
  | nil : ValuesRel [] [] []
  | cons {type : Core.Ty} {types : List Core.Ty} {source : Semantics.Value}
      {sources : List Semantics.Value} {target : Core.Value} {targets : List Core.Value}
      (head : ValueRel type source target) (tail : ValuesRel types sources targets) :
      ValuesRel (type :: types) (source :: sources) (target :: targets)

def bundleValues : List Core.Value → Core.Value
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (bundleValues rest)

theorem ValuesRel.length {types : List Core.Ty} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ValuesRel types sources targets) :
    sources.length = types.length ∧ targets.length = types.length := by
  induction related with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => simpa only [List.length_cons, Nat.succ.injEq] using ih

theorem parseInput_correspondence {type : Core.Ty} {input : String} {expression : Core.Expr}
    (parsed : parseInput type input = .ok expression) :
    ∃ source target, InputRel type input source ∧ ValueRel type source target ∧
      ∀ environment store, Core.Evaluates environment store expression target store := by
  cases type <;> try simp [parseInput, fail] at parsed
  case word =>
    obtain ⟨value, wordParsed, returned⟩ := lower_bind_eq_ok.mp parsed
    cases returned
    exact ⟨.word value, .word value, .word (parseWord_some_of_ok wordParsed), .word value,
      fun _ _ => .word⟩
  case unit =>
    split at parsed
    · rename_i same
      subst input
      cases parsed
      exact ⟨.unit, .unit, .unit, .unit, fun _ _ => .unit⟩
    · contradiction
  case bool =>
    split at parsed
    · rename_i same
      subst input
      cases parsed
      exact ⟨.bool true, .bool true, .boolTrue, .bool true, fun _ _ => .bool⟩
    · split at parsed
      · rename_i same
        subst input
        cases parsed
        exact ⟨.bool false, .bool false, .boolFalse, .bool false, fun _ _ => .bool⟩
      · contradiction
  case sum left right =>
    cases left <;> cases right <;> simp only at parsed <;> try contradiction
    split at parsed
    · rename_i same
      subst input
      cases parsed
      exact ⟨.inr .unit, .inRight .unit .unit, .sumTrue, .inr .unit, fun _ _ => .inRight .unit⟩
    · split at parsed
      · rename_i same
        subst input
        cases parsed
        exact ⟨.inl .unit, .inLeft .unit .unit, .sumFalse, .inl .unit, fun _ _ => .inLeft .unit⟩
      · contradiction

/-- Actual arity checking and parsing provide all argument value and heap
premises needed by a function-preservation theorem. -/
theorem parseArguments_correspondence {parameters : List Core.Ty} {inputs : List String}
    {expression : Core.Expr} (parsed : parseArguments parameters inputs = .ok expression) :
    ∃ sources targets, InputsRel parameters inputs sources ∧ ValuesRel parameters sources targets ∧
      ∀ environment store, Core.Evaluates environment store expression (bundleValues targets) store := by
  induction parameters generalizing inputs expression with
  | nil =>
      cases inputs with
      | nil =>
          simp [parseArguments] at parsed
          cases parsed
          exact ⟨[], [], .nil, .nil, fun _ _ => .unit⟩
      | cons input inputs => simp [parseArguments, fail, Bind.bind, Except.bind] at parsed
  | cons type types ih =>
      cases inputs with
      | nil => simp [parseArguments, fail, Bind.bind, Except.bind] at parsed
      | cons input inputs =>
          by_cases length : inputs.length = types.length
          · cases types with
            | nil =>
                have empty : inputs = [] := List.eq_nil_of_length_eq_zero length
                subst inputs
                simp only [parseArguments, List.length_cons, List.length_nil, ↓reduceIte] at parsed
                obtain ⟨source, target, inputRelated, valueRelated, evaluated⟩ := parseInput_correspondence parsed
                exact ⟨[source], [target], .cons inputRelated .nil, .cons valueRelated .nil, evaluated⟩
            | cons next rest =>
                have lengths : (input :: inputs).length = (type :: next :: rest).length := congrArg Nat.succ length
                simp only [parseArguments, lengths, ↓reduceIte] at parsed
                obtain ⟨head, headParsed, tail⟩ := lower_bind_eq_ok.mp parsed
                obtain ⟨tail, tailParsed, returned⟩ := lower_bind_eq_ok.mp tail
                cases returned
                obtain ⟨source, target, inputRelated, valueRelated, headEvaluates⟩ := parseInput_correspondence headParsed
                obtain ⟨sources, targets, inputsRelated, valuesRelated, tailEvaluates⟩ := ih tailParsed
                refine ⟨source :: sources, target :: targets, .cons inputRelated inputsRelated,
                  .cons valueRelated valuesRelated, ?_⟩
                cases targets with
                | nil => have impossible := valuesRelated.length; simp at impossible
                | cons targetHead targets =>
                    intro environment store
                    exact .pair (headEvaluates environment store) (tailEvaluates environment store)
          · rw [parseArguments.eq_def] at parsed
            simp [length, fail, Bind.bind, Except.bind] at parsed

end Solcore.Frontend.RustHull.ScalarExecution
