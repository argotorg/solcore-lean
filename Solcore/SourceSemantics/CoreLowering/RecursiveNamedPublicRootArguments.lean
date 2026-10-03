import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.SourceSemantics.CoreLowering.DataExpressionSequence
import Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning

/-! Public root arguments are pure reads of the reversed native input prefix.
The proof copies arbitrary payloads, including closures, without changing their
captures or the store. Source attribution and input encoding remain separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootArguments
open Core Frontend ReadOnly

/-- A static ordered list of the exact native input slots. -/
inductive Slots (canonical : Environment) : List SourceCoreBasic.LoweredExpr → List Value → Prop where
  | nil : Slots canonical [] []
  | cons {type index value codes values}
      (found : canonical[index]? = some value) (rest : Slots canonical codes values) :
      Slots canonical (⟨type, LanguageResult.success (.var index)⟩ :: codes) (value :: values)

theorem Slots.evaluates {canonical : Environment} {codes : List SourceCoreBasic.LoweredExpr}
    {values : List Value} (slots : Slots canonical codes values)
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    (store : Store) :
    Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
      (.inRight .word (DataPatternValues.packValues values)) store := by
  induction slots generalizing actual ξ with
  | nil => exact .inRight .unit
  | @cons type index value codes values found rest ih =>
    have first : Evaluates actual store ((LanguageResult.success (.var index)).rename ξ)
        (.inRight .word value) store := .inRight (.var (agrees found))
    cases rest with
    | nil => exact first
    | @cons nextType nextIndex nextValue nextCodes nextValues nextFound remaining =>
      have second := ih (GenericExpressionMeaning.agree_prefix agrees value)
      rw [GenericExpressionMeaning.rename_prefix] at second
      simpa [SourceCoreCalls.packArguments, DataPatternValues.packValues, DataExpressionSequence.pair_rename]
        using LocalSequence.pair_success type (SourceCoreCalls.packArguments
          (⟨nextType, LanguageResult.success (.var nextIndex)⟩ :: nextCodes)).type first second

private theorem ordered_slots (types : List Ty) (values : List Value) (canonical : Environment)
    (total start : Nat) (lengths : types.length = values.length)
    (selected : ∀ {index value}, values[index]? = some value →
      canonical[total - 1 - (start + index)]? = some value) :
    Slots canonical (types.zipIdx.map fun (type, index) =>
      ⟨type, LanguageResult.success (.var (total - 1 - (start + index)))⟩) values := by
  induction types generalizing values start with
  | nil => cases values with
    | nil => exact .nil
    | cons => simp at lengths
  | cons type types ih =>
    cases values with
    | nil => simp at lengths
    | cons value values =>
      have tailLengths : types.length = values.length := Nat.succ.inj lengths
      have first : canonical[total - 1 - start]? = some value := by simpa using selected (index := 0) rfl
      have tailSelected : ∀ {index value}, values[index]? = some value →
          canonical[total - 1 - (start + 1 + index)]? = some value := by
        intro index value found
        simpa [Nat.add_assoc, Nat.add_comm 1] using selected (index := index + 1) found
      have remaining := ih values (start + 1) tailLengths tailSelected
      simpa only [List.zipIdx_cons', List.map_cons, List.map_map, Prod.map, Function.comp_def, id_eq, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using Slots.cons (type := type) first remaining

/-- The actual reversed prefix selects each original payload in source order.
The length condition concerns native slots and never identifies a source type. -/
theorem input_slots (types : List Ty) (values globals : Environment)
    (lengths : types.length = values.length) :
    Slots (values.reverse ++ globals) (types.zipIdx.map fun (type, index) =>
      ⟨type, LanguageResult.success (.var (types.length - 1 - index))⟩) values := by
  have selected : ∀ {index value}, values[index]? = some value →
      (values.reverse ++ globals)[types.length - 1 - (0 + index)]? = some value := by
    intro index value found
    have bound : index < values.length := (List.getElem?_eq_some_iff.mp found).1
    have backwards : values.reverse[types.length - 1 - index]? = some value := by
      rw [List.getElem?_reverse' (j := index) (by omega)]
      exact found
    have within : types.length - 1 - index < values.reverse.length := by
      simp only [List.length_reverse]; omega
    simpa only [Nat.zero_add, List.getElem?_append_left within] using backwards
  simpa only [Nat.zero_add] using ordered_slots types values (values.reverse ++ globals) types.length 0 lengths selected

/-- Every public argument bundle succeeds without changing any store cell. -/
theorem arguments_evaluate (types : List Ty) (values globals : Environment) (store : Store)
    (lengths : types.length = values.length) :
    Evaluates (values.reverse ++ globals) store
      (SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (types.length - 1 - index))⟩)).expression
      (.inRight .word (DataPatternValues.packValues values)) store := by
  have evaluated := (input_slots types values globals lengths).evaluates
    (ξ := Renaming.id) (actual := values.reverse ++ globals) (by intro index value found; exact found) store
  simpa only [Expr.rename_id] using evaluated


/-- Enough fuel evaluates only the argument reads and preserves the store. -/
theorem arguments_have_sufficient_fuel (types : List Ty) (values globals : Environment) (store : Store)
    (lengths : types.length = values.length) :
    ∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
      (.initial (SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (types.length - 1 - index))⟩)).expression
        (values.reverse ++ globals) store) = .done (.inRight .word (DataPatternValues.packValues values)) store :=
  evaluation_runStateful_complete_with_sufficient_fuel (arguments_evaluate types values globals store lengths)

/-- Original native completion has the same ordered payload and full store. -/
theorem completed_arguments (types : List Ty) (values globals : Environment) (store : Store)
    (lengths : types.length = values.length) {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial (SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (types.length - 1 - index))⟩)).expression
        (values.reverse ++ globals) store) = .done value finalStore) :
    value = .inRight .word (DataPatternValues.packValues values) ∧ finalStore = store :=
  evaluation_deterministic (runStateful_evaluation_sound completed) (arguments_evaluate types values globals store lengths)

/-- The encoder's native environment typing supplies the exact native arity.
It is used only for slot lengths, with no source identity inferred from it. -/
theorem typed_arguments_evaluate {definitions : DataEnvironment} {world : StoreTyping}
    {types : List Ty} {values : Environment} (globals : Environment) (store : Store)
    (typed : RuntimeEnvironmentHasTypes world values types definitions) :
    Evaluates (values.reverse ++ globals) store
      (SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (types.length - 1 - index))⟩)).expression
      (.inRight .word (DataPatternValues.packValues values)) store := by
  have lengths : types.length = values.length := by
    have same := congrArg List.length typed.type_tags
    simpa only [List.length_map] using same.symm
  exact arguments_evaluate types values globals store lengths

/-- Factory provenance supplies the actual call; the typed native prefix
closes its pure argument evaluation, retaining every payload and store cell. -/
theorem factory_call_arguments {compiled : SourceCoreUnifiedCompilation.Compiled}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    {root : SourceCoreIndexedSession.Root compiled}
    (issued : root.FactoryShape compiled entry) {world : StoreTyping} {values : Environment}
    (store : Store) (typed : RuntimeEnvironmentHasTypes world values root.types compiled.indexed.layouts.definitions) :
    ∃ (function : SourceCoreGeneralFunctions.Function) (index : Nat),
      function.signature.key = root.key ∧
      root.body = SourceCoreCalls.call function.signature (index + root.types.length)
        (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
          ⟨type, LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression Word.zero ∧
      Evaluates (values.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store
        (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
          ⟨type, LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression
        (.inRight .word (DataPatternValues.packValues values)) store := by
  obtain ⟨function, index, _, key, rootKey, _, _, _, _, _, body, _⟩ := issued
  exact ⟨function, index, key.trans rootKey.symm, body,
    typed_arguments_evaluate (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store typed⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootArguments
