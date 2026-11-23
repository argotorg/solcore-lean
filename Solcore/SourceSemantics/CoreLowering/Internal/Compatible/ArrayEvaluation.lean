import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionArrays
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.Core.Internal.DerivedForms

/-!
# Compatible expressions: how memory arrays' Core code runs

The Core code of the memory array forms, run on Core values: each form's children in order, a child's
failure, the bounds checks and their panics, and the cells a form allocates, reads and writes. Main
declarations: `newArray_evaluates`, `arrayIndex_evaluates`, `viewRead_evaluates`, `arraySlice_evaluates`,
`elementRef_evaluates`, `memrefLoad_evaluates` and `memrefStore_evaluates`.
-/

section
/-! The code's comparisons are of words, its cells are the arrays' cells of
`CompatibleExpressionArrays.arrayType`, and its reads and writes of entries run the ordered mapping
helpers with the word comparison. Children are any expressions; a child's run is a premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleArrayEvaluation
open Core Frontend CompatibleExpressionArrays

/-- `wordLt` of a pure operand and an operand pure after the first is bound. -/
theorem wordLt_evaluates {environment : Environment} {store : Store} {left right weakened : Expr} {a b : Word}
    (weakening : right.weakenAt 0 = weakened)
    (leftEvaluated : Evaluates environment store left (.word a) store)
    (rightEvaluated : Evaluates (.word a :: environment) store weakened (.word b) store) :
    Evaluates environment store (left.wordLt right) (.bool (decide (a < b))) store := by
  rw [Expr.wordLt_expansion, weakening]
  exact .letE leftEvaluated (.letE rightEvaluated (.binary (.var rfl) (.var rfl) rfl))

/-- `wordLe` of two pure operands. -/
theorem wordLe_evaluates {environment : Environment} {store : Store} {left right : Expr} {a b : Word}
    (leftEvaluated : Evaluates environment store left (.word a) store)
    (rightEvaluated : Evaluates environment store right (.word b) store) :
    Evaluates environment store (left.wordLe right) (.bool (!decide (a > b))) store := by
  rw [Expr.wordLe_expansion]
  exact .unary (.binary leftEvaluated rightEvaluated rfl) rfl

/-! ### Lengths -/

theorem arrayLength_failure {environment : Environment} {before after : Store} {base : Expr}
    {type : Ty} {reason : Word}
    (failed : Evaluates environment before base (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.arrayLength base) (.inLeft .word (.word reason)) after :=
  LanguageResult.bind_failure _ failed

/-- An array's length is the first component of its cell. -/
theorem arrayLength_evaluates {environment : Environment} {before after : Store} {base : Expr}
    {type : Ty} {location : Location} {length : Word} {rest : Value}
    (evaluated : Evaluates environment before base (.inRight .word (.cellRef type location)) after)
    (read : after.read? location = some (.pair (.word length) rest)) :
    Evaluates environment before (SourceCoreDataExpressions.arrayLength base) (.inRight .word (.word length)) after :=
  LanguageResult.bind_success _ evaluated (.inRight (.first (.loadCell (.var rfl) read)))

theorem sliceLength_failure {environment : Environment} {before after : Store} {base : Expr}
    {type : Ty} {reason : Word}
    (failed : Evaluates environment before base (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.sliceLength base) (.inLeft .word (.word reason)) after :=
  LanguageResult.bind_failure _ failed

/-- A slice's length is its last component. -/
theorem sliceLength_evaluates {environment : Environment} {before after : Store} {base : Expr}
    {view start : Value} {length : Word}
    (evaluated : Evaluates environment before base (.inRight .word (.pair view (.pair start (.word length)))) after) :
    Evaluates environment before (SourceCoreDataExpressions.sliceLength base) (.inRight .word (.word length)) after :=
  LanguageResult.bind_success _ evaluated (.inRight (.second (.second (.var rfl))))

/-! ### `lidx` -/

section ElementRef
variable {layout : OrderedMapping.Layout} {environment : Environment} {base index : Expr}

theorem elementRef_base_failure {before after : Store} {type : Ty} {reason : Word}
    (failed : Evaluates environment before base (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.elementRef layout base index)
      (.inLeft (.product (.cell (.product .word (.product layout.valueType layout.type))) .word) (.word reason)) after :=
  LanguageResult.bind_failure _ failed

theorem elementRef_index_failure {before middle after : Store} {array : Value} {type : Ty} {reason : Word}
    (evaluated : Evaluates environment before base (.inRight .word array) middle)
    (failed : Evaluates (array :: environment) middle (index.weakenAt 0) (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.elementRef layout base index)
      (.inLeft (.product (.cell (.product .word (.product layout.valueType layout.type))) .word) (.word reason)) after :=
  LanguageResult.bind_success _ evaluated (LanguageResult.bind_failure _ failed)

/-- `lidx(a, i)` below the length is the pair of the array and the index. -/
theorem elementRef_evaluates {before middle after : Store} {type : Ty} {location : Location}
    {length position : Word} {rest : Value}
    (evaluated : Evaluates environment before base (.inRight .word (.cellRef type location)) middle)
    (indexed : Evaluates (.cellRef type location :: environment) middle (index.weakenAt 0)
      (.inRight .word (.word position)) after)
    (read : after.read? location = some (.pair (.word length) rest)) (below : position < length) :
    Evaluates environment before (SourceCoreDataExpressions.elementRef layout base index)
      (.inRight .word (.pair (.cellRef type location) (.word position))) after := by
  apply LanguageResult.bind_success _ evaluated (LanguageResult.bind_success _ indexed _)
  apply Evaluates.ifTrue
  · simpa only [below, decide_true] using
      wordLt_evaluates (environment := .word position :: .cellRef type location :: environment) (store := after)
        (left := .var 0) (right := .first (.loadCell (.var 1)))
        (weakened := .first (.loadCell (.var 2))) (by simp [Expr.weakenAt]) (.var rfl) (.first (.loadCell (.var rfl) read))
  · exact .inRight (.pair (.var rfl) (.var rfl))

/-- `lidx(a, i)` from the length on panics with `0x32`. -/
theorem elementRef_outOfBounds {before middle after : Store} {type : Ty} {location : Location}
    {length position : Word} {rest : Value}
    (evaluated : Evaluates environment before base (.inRight .word (.cellRef type location)) middle)
    (indexed : Evaluates (.cellRef type location :: environment) middle (index.weakenAt 0)
      (.inRight .word (.word position)) after)
    (read : after.read? location = some (.pair (.word length) rest)) (beyond : ¬ position < length) :
    Evaluates environment before (SourceCoreDataExpressions.elementRef layout base index)
      (.inLeft (.product (.cell (.product .word (.product layout.valueType layout.type))) .word)
        (.word (SourceCorePanics.reason SourceCorePanics.outOfBounds))) after := by
  apply LanguageResult.bind_success _ evaluated (LanguageResult.bind_success _ indexed _)
  apply Evaluates.ifFalse
  · simpa only [beyond, decide_false] using
      wordLt_evaluates (environment := .word position :: .cellRef type location :: environment) (store := after)
        (left := .var 0) (right := .first (.loadCell (.var 1)))
        (weakened := .first (.loadCell (.var 2))) (by simp [Expr.weakenAt]) (.var rfl) (.first (.loadCell (.var rfl) read))
  · exact .inLeft .word

end ElementRef

/-! ### `new` -/

/-- A default element's code runs without failing and without reading the store: zero, or one fresh empty
array per level of nesting, each cell after the cells of its own default. -/
theorem arrayDefault_evaluates {catalog : SourceCoreCompatibleCatalog.Catalog} {element : TypeSystem.Ty}
    {default : Expr} (defined : SourceCoreCompatibleDataExpressions.arrayDefault catalog element = some default)
    (environment : Environment) (store : Store) :
    ∃ value cells, Evaluates environment store default value (store ++ cells) := by
  induction element using SourceCoreCompatibleDataExpressions.arrayDefault.induct generalizing default with
  | case1 =>
    simp only [SourceCoreCompatibleDataExpressions.arrayDefault, Option.some.injEq] at defined
    subst default
    exact ⟨_, [], by simpa using (Evaluates.word : Evaluates environment store (.word Word.zero) _ store)⟩
  | case2 type =>
    simp only [SourceCoreCompatibleDataExpressions.arrayDefault, Option.some.injEq] at defined
    subst default
    exact ⟨_, [], by simpa using (Evaluates.word : Evaluates environment store (.word Word.zero) _ store)⟩
  | case3 inner ih =>
    unfold SourceCoreCompatibleDataExpressions.arrayDefault at defined
    cases projected : (catalog.project inner).toOption <;>
      cases identified : catalog.identity? (.mapping (.constructor (.builtin .word)) inner) <;>
      cases innerDefined : SourceCoreCompatibleDataExpressions.arrayDefault catalog inner <;>
      simp only [projected, identified, innerDefined, bind, Option.bind, reduceCtorEq, Option.some.injEq] at defined
    rename_i innerType identity innerDefault
    subst default
    obtain ⟨value, cells, evaluated⟩ := ih innerDefined
    refine ⟨.cellRef (.product .word (.product innerType (.namedData identity))) (store ++ cells).length,
      cells ++ [.pair (.word Word.zero) (.pair value (.constructed ⟨identity, 0⟩ .unit))], ?_⟩
    rw [← List.append_assoc]
    exact Evaluates.newCell (.pair .word (.pair evaluated (.construct .unit)))
  | case4 other notWord notFixed notArray =>
    rw [SourceCoreCompatibleDataExpressions.arrayDefault.eq_def] at defined
    split at defined
    · exact absurd rfl notWord
    · exact absurd rfl (notFixed _)
    · exact absurd rfl (notArray _)
    · cases defined

section NewArray
variable {layout : OrderedMapping.Layout} {default length : Expr} {environment : Environment}

theorem newArray_length_failure {before after : Store} {type : Ty} {reason : Word}
    (failed : Evaluates environment before length (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.newArray layout default length)
      (.inLeft (.cell (.product .word (.product layout.valueType layout.type))) (.word reason)) after :=
  LanguageResult.bind_failure _ failed

/-- Below the limit, `new T[](n)` allocates one cell of `n`, the default element and no entry, after the
default's own cells. -/
theorem newArray_evaluates {before middle defaulted : Store} {count : Word} {defaultValue : Value}
    (lengthEvaluated : Evaluates environment before length (.inRight .word (.word count)) middle)
    (below : count < Word.ofNatModulo SourceCoreDataExpressions.arrayLengthLimit)
    (defaultEvaluated : Evaluates (.word count :: environment) middle (default.weakenAt 0) defaultValue defaulted) :
    Evaluates environment before (SourceCoreDataExpressions.newArray layout default length)
      (.inRight .word (.cellRef (.product .word (.product layout.valueType layout.type)) defaulted.length))
      (defaulted ++ [.pair (.word count) (.pair defaultValue (OrderedMapping.encode layout []))]) := by
  apply LanguageResult.bind_success _ lengthEvaluated
  apply Evaluates.ifTrue
  · simpa only [below, decide_true] using wordLt_evaluates (environment := .word count :: environment) (store := middle)
      (left := .var 0) (right := .word (Word.ofNatModulo SourceCoreDataExpressions.arrayLengthLimit))
      (weakened := .word (Word.ofNatModulo SourceCoreDataExpressions.arrayLengthLimit)) (by simp [Expr.weakenAt]) (.var rfl) .word
  · exact .inRight (.newCell (.pair (.var rfl) (.pair defaultEvaluated (.construct .unit))))

/-- From the limit on, `new T[](n)` panics with `0x41` and allocates nothing. -/
theorem newArray_tooLong {before middle : Store} {count : Word}
    (lengthEvaluated : Evaluates environment before length (.inRight .word (.word count)) middle)
    (beyond : ¬ count < Word.ofNatModulo SourceCoreDataExpressions.arrayLengthLimit) :
    Evaluates environment before (SourceCoreDataExpressions.newArray layout default length)
      (.inLeft (.cell (.product .word (.product layout.valueType layout.type)))
        (.word (SourceCorePanics.reason SourceCorePanics.allocation))) middle := by
  apply LanguageResult.bind_success _ lengthEvaluated
  apply Evaluates.ifFalse
  · simpa only [beyond, decide_false] using wordLt_evaluates (environment := .word count :: environment) (store := middle)
      (left := .var 0) (right := .word (Word.ofNatModulo SourceCoreDataExpressions.arrayLengthLimit))
      (weakened := .word (Word.ofNatModulo SourceCoreDataExpressions.arrayLengthLimit)) (by simp [Expr.weakenAt]) (.var rfl) .word
  · exact .inLeft .word

end NewArray


/-! ### The word comparison -/

section Comparison
variable {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
  {comparison : SourceCoreCompatibleDataEquality.Prepared checked}

/-- The word comparison's carrier is `word`, and its body compares two words. -/
theorem word_comparison
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison) :
    comparison.type = .word ∧ comparison.body = .binary .wordEq (.first (.var 0)) (.second (.var 0)) := by
  have projected := comparison.projection
  rw [CompatibleMapping.comparison_sourceType prepared] at projected
  simp only [SourceCoreCompatibleCatalog.Catalog.project, pure, Except.pure, Except.ok.injEq] at projected
  have generated := comparison.bodyGenerated
  rw [← projected] at generated
  cases fuelEq : comparison.compilationFuel with
  | zero => simp [fuelEq, SourceCoreCompatibleDataEquality.compareType, throw, throwThe] at generated
  | succ rest =>
    simp [fuelEq, SourceCoreCompatibleDataEquality.compareType,
      SourceCoreCompatibleDataEquality.isMappingCarrier, pure, Except.pure] at generated
    exact ⟨projected.symm, generated.symm⟩

/-- The word comparison's closure compares two words, wherever it was prepared and whatever the store. -/
theorem word_compares
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
    {layout : OrderedMapping.Layout} (keyType : layout.keyType = .word) (environment : Environment) (base : Store)
    (left right : Word) (store : Store) :
    OrderedMapping.Compares layout (CompatibleMappingComparison.comparator comparison environment base)
      (.word left) (.word right) (left == right) store := by
  obtain ⟨typeEq, bodyEq⟩ := word_comparison prepared
  refine ⟨comparison.body.rename (DataEqualityInstalled.offset comparison.bodies.length).lift,
    DataEqualityInstalled.captured comparison.bodies.length
      (DataEqualityInstalled.allocatedEnvironment (CompatibleEquality.storageCatalog checked.catalog) base.length
        environment), ?_, ?_⟩
  · unfold CompatibleMappingComparison.comparator
    rw [typeEq, keyType]
  · rw [bodyEq]
    simp only [Expr.rename, Renaming.lift]
    exact .binary (.first (.var rfl)) (.second (.var rfl)) rfl

/-- With word keys, the word comparison's comparisons are the arrays' key equality. -/
theorem word_comparisons
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
    {layout : OrderedMapping.Layout} (keyType : layout.keyType = .word) (environment : Environment) (base : Store)
    {entries : OrderedMapping.Entries} (wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word)
    (position : Word) (store : Store) :
    OrderedMapping.Comparisons layout (CompatibleMappingComparison.comparator comparison environment base)
      GenericHeap.arrayKeyEqual (.word position) entries store := by
  intro stored value member
  obtain ⟨word, rfl⟩ := wordKeys stored value member
  have same : (position == word) = GenericHeap.arrayKeyEqual (.word position) (.word word) := by
    by_cases equal : position = word
    · subst equal; simp [GenericHeap.arrayKeyEqual]
    · simp [GenericHeap.arrayKeyEqual, equal]
  rw [← same]
  exact word_compares prepared keyType environment base position word store

/-- The store after a lookup keeps every earlier cell. -/
theorem lookupStore_read {layout : OrderedMapping.Layout} {environment : Environment} {store : Store}
    {entries : OrderedMapping.Entries} {key : Value} {location : Location} {value : Value}
    (read : store.read? location = some value) :
    (CompatibleMappingComparison.lookupStore comparison layout environment store entries key).read? location =
      some value := by
  have bound : location < store.length := (List.getElem?_eq_some_iff.mp read).1
  simp only [CompatibleMappingComparison.lookupStore, OrderedMapping.installedStore, WordMapping.installedStore,
    CompatibleMappingComparison.comparisonStore, Store.read?, List.append_assoc] at read ⊢
  rw [List.getElem?_append_left bound]
  exact read

end Comparison

/-! ### Reads -/

/-- The positions a read through slices computes: a selected word, or a slice's start plus a position. -/
inductive PureWord (environment : Environment) : Expr → Word → Prop where
  | select {expression : Expr} {value : Word}
      (selected : DataEquality.Selects environment expression (.word value)) : PureWord environment expression value
  | add {start position : Expr} {first second : Word}
      (startSelected : DataEquality.Selects environment start (.word first))
      (positionPure : PureWord environment position second) :
      PureWord environment (.binary .wordAdd start position) (first.add second)

theorem PureWord.evaluates {environment : Environment} {expression : Expr} {value : Word}
    (pure : PureWord environment expression value) (store : Store) :
    Evaluates environment store expression (.word value) store := by
  induction pure with
  | select selected => exact selected.evaluates store
  | add startSelected _ ih => exact .binary (startSelected.evaluates store) ih rfl

theorem PureWord.weaken {environment : Environment} {expression : Expr} {value : Word}
    (pure : PureWord environment expression value) (inserted : Value) :
    PureWord (inserted :: environment) (expression.weakenAt 0) value := by
  induction pure with
  | select selected => exact .select (selected.weaken inserted)
  | add startSelected _ ih => simpa [Expr.weakenAt] using PureWord.add (startSelected.weaken inserted) ih

section Reads
variable {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
  {comparison : SourceCoreCompatibleDataEquality.Prepared checked} {layout : OrderedMapping.Layout}

/-- The panic of a read, a slice or `lidx` out of bounds. -/
abbrev outOfBounds : Word := SourceCorePanics.reason SourceCorePanics.outOfBounds

/-- A read through `depth` slices on Core values: each slice checks the position against its length and
reads its base at its start plus the position, and an array's cell is read as `arrayIndex` reads it, the
entry at the position or the default, with the store after the word comparison's and the lookup's cells. -/
inductive ViewReads (comparison : SourceCoreCompatibleDataEquality.Prepared checked) (layout : OrderedMapping.Layout)
    (environment : Environment) (store : Store) : Nat → Value → Word → Value → Store → Prop where
  | array {type : Ty} {location : Location} {length position : Word} {default : Value}
      {entries : OrderedMapping.Entries}
      (read : store.read? location = some (.pair (.word length) (.pair default (OrderedMapping.encode layout entries))))
      (below : position < length) (wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word) :
      ViewReads comparison layout environment store 0 (.cellRef type location) position
        (.inRight .word ((OrderedMapping.lookupEntries GenericHeap.arrayKeyEqual (.word position) entries).getD default))
        (CompatibleMappingComparison.lookupStore comparison layout
          (.word position :: .cellRef type location :: environment) store entries (.word position))
  | arrayOutside {type : Ty} {location : Location} {length position : Word} {rest : Value}
      (read : store.read? location = some (.pair (.word length) rest)) (beyond : ¬ position < length) :
      ViewReads comparison layout environment store 0 (.cellRef type location) position
        (.inLeft layout.valueType (.word outOfBounds)) store
  | slice {depth : Nat} {inner : Value} {start length position : Word} {result : Value} {final : Store}
      (below : position < length)
      (innerRead : ViewReads comparison layout environment store depth inner (start.add position) result final) :
      ViewReads comparison layout environment store (depth + 1) (.pair inner (.pair (.word start) (.word length)))
        position result final
  | sliceOutside {depth : Nat} {inner : Value} {start length position : Word} (beyond : ¬ position < length) :
      ViewReads comparison layout environment store (depth + 1) (.pair inner (.pair (.word start) (.word length)))
        position (.inLeft layout.valueType (.word outOfBounds)) store

variable (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
  (keyType : layout.keyType = .word)

theorem arrayIndex_base_failure {environment : Environment} {before after : Store} {base index : Expr}
    {type : Ty} {reason : Word}
    (failed : Evaluates environment before base (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.arrayIndex layout comparison.expression base index)
      (.inLeft layout.valueType (.word reason)) after :=
  LanguageResult.bind_failure _ failed

theorem arrayIndex_index_failure {environment : Environment} {before middle after : Store} {base index : Expr}
    {array : Value} {type : Ty} {reason : Word}
    (evaluated : Evaluates environment before base (.inRight .word array) middle)
    (failed : Evaluates (array :: environment) middle (index.weakenAt 0) (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.arrayIndex layout comparison.expression base index)
      (.inLeft layout.valueType (.word reason)) after :=
  LanguageResult.bind_success _ evaluated (LanguageResult.bind_failure _ failed)

include prepared keyType in
/-- `a[i]` on an array below its length: the entry at the position, or the default element. -/
theorem arrayIndex_evaluates {environment : Environment} {before middle after : Store} {base index : Expr}
    {type : Ty} {location : Location} {length position : Word} {default : Value} {entries : OrderedMapping.Entries}
    (evaluated : Evaluates environment before base (.inRight .word (.cellRef type location)) middle)
    (indexed : Evaluates (.cellRef type location :: environment) middle (index.weakenAt 0)
      (.inRight .word (.word position)) after)
    (read : after.read? location = some (.pair (.word length) (.pair default (OrderedMapping.encode layout entries))))
    (below : position < length) (wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word) :
    Evaluates environment before (SourceCoreDataExpressions.arrayIndex layout comparison.expression base index)
      (.inRight .word ((OrderedMapping.lookupEntries GenericHeap.arrayKeyEqual (.word position) entries).getD default))
      (CompatibleMappingComparison.lookupStore comparison layout
        (.word position :: .cellRef type location :: environment) after entries (.word position)) := by
  apply LanguageResult.bind_success _ evaluated (LanguageResult.bind_success _ indexed _)
  apply Evaluates.ifTrue
  · simpa only [below, decide_true] using
      wordLt_evaluates (environment := .word position :: .cellRef type location :: environment) (store := after)
        (left := .var 0) (right := .first (.loadCell (.var 1)))
        (weakened := .first (.loadCell (.var 2))) (by simp [Expr.weakenAt]) (.var rfl) (.first (.loadCell (.var rfl) read))
  · rw [CompatibleMapping.Transport.expression_weaken, CompatibleMapping.Transport.expression_weaken]
    apply LanguageResult.bind_success _
      (OrderedMapping.lookup_evaluates entries (.word position)
        (CompatibleMappingComparison.comparator comparison (.word position :: .cellRef type location :: environment) after)
        GenericHeap.arrayKeyEqual (.second (.second (.loadCell (.var rfl) read))) (.var rfl)
        (CompatibleEquality.prepared_evaluates_exact comparison _ after)
        (word_comparisons prepared keyType _ after wordKeys position _))
    have kept := lookupStore_read (comparison := comparison) (layout := layout)
      (environment := .word position :: .cellRef type location :: environment) (entries := entries)
      (key := .word position) read
    cases found : OrderedMapping.lookupEntries GenericHeap.arrayKeyEqual (.word position) entries with
    | none =>
      simp only [OrderedMapping.optionValue, Option.getD_none]
      exact .caseLeft (.var rfl) (.inRight (.first (.second (.loadCell (.var rfl) kept))))
    | some value =>
      simp only [OrderedMapping.optionValue, Option.getD_some]
      exact .caseRight (.var rfl) (.inRight (.var rfl))

/-- `a[i]` on an array from its length on panics with `0x32`. -/
theorem arrayIndex_outOfBounds {environment : Environment} {before middle after : Store} {base index : Expr}
    {type : Ty} {location : Location} {length position : Word} {rest : Value}
    (evaluated : Evaluates environment before base (.inRight .word (.cellRef type location)) middle)
    (indexed : Evaluates (.cellRef type location :: environment) middle (index.weakenAt 0)
      (.inRight .word (.word position)) after)
    (read : after.read? location = some (.pair (.word length) rest)) (beyond : ¬ position < length) :
    Evaluates environment before (SourceCoreDataExpressions.arrayIndex layout comparison.expression base index)
      (.inLeft layout.valueType (.word outOfBounds)) after := by
  apply LanguageResult.bind_success _ evaluated (LanguageResult.bind_success _ indexed _)
  apply Evaluates.ifFalse
  · simpa only [beyond, decide_false] using
      wordLt_evaluates (environment := .word position :: .cellRef type location :: environment) (store := after)
        (left := .var 0) (right := .first (.loadCell (.var 1)))
        (weakened := .first (.loadCell (.var 2))) (by simp [Expr.weakenAt]) (.var rfl) (.first (.loadCell (.var rfl) read))
  · exact .inLeft .word

include prepared keyType in
/-- A read through `depth` slices runs as `ViewReads` gives it, from a selected view and a pure position. -/
theorem viewRead_evaluates {environment : Environment} {store : Store} {depth : Nat} {viewValue : Value}
    {position : Word} {result : Value} {final : Store}
    (reads : ViewReads comparison layout environment store depth viewValue position result final)
    {view positionCode : Expr} (viewSelected : DataEquality.Selects environment view viewValue)
    (positionPure : PureWord environment positionCode position) :
    Evaluates environment store (SourceCoreDataExpressions.viewRead layout comparison.expression depth view positionCode)
      result final := by
  induction reads generalizing view positionCode with
  | @array type location length position default entries read below wordKeys =>
    have indexed : Evaluates (.cellRef type location :: environment) store
        ((LanguageResult.success positionCode).weakenAt 0) (.inRight .word (.word position)) store := by
      simpa only [LanguageResult.success, Expr.weakenAt] using
        LanguageResult.success_evaluates ((positionPure.weaken _).evaluates store)
    exact arrayIndex_evaluates prepared keyType (LanguageResult.success_evaluates (viewSelected.evaluates store))
      indexed read below wordKeys
  | @arrayOutside type location length position rest read beyond =>
    have indexed : Evaluates (.cellRef type location :: environment) store
        ((LanguageResult.success positionCode).weakenAt 0) (.inRight .word (.word position)) store := by
      simpa only [LanguageResult.success, Expr.weakenAt] using
        LanguageResult.success_evaluates ((positionPure.weaken _).evaluates store)
    exact arrayIndex_outOfBounds (LanguageResult.success_evaluates (viewSelected.evaluates store)) indexed read beyond
  | @slice depth inner start length position result final below innerRead ih =>
    simp only [SourceCoreDataExpressions.viewRead]
    apply Evaluates.ifTrue
    · simpa only [below, decide_true] using
        wordLt_evaluates (right := .second (.second view)) (weakened := (Expr.second (.second view)).weakenAt 0) rfl
          (positionPure.evaluates store) (((viewSelected.second.second).weaken _).evaluates store)
    · exact ih viewSelected.first (.add viewSelected.second.first positionPure)
  | sliceOutside beyond =>
    simp only [SourceCoreDataExpressions.viewRead]
    apply Evaluates.ifFalse
    · simpa only [beyond, decide_false] using
        wordLt_evaluates (right := .second (.second view)) (weakened := (Expr.second (.second view)).weakenAt 0) rfl
          (positionPure.evaluates store) (((viewSelected.second.second).weaken _).evaluates store)
    · exact .inLeft .word

include prepared keyType in
/-- `a[i]` on a view inside `depth + 1` slices: the view's and the index's runs, then the read. -/
theorem viewIndex_evaluates {environment : Environment} {before middle after : Store} {depth : Nat}
    {base index : Expr} {viewValue : Value} {position : Word} {result : Value} {final : Store}
    (evaluated : Evaluates environment before base (.inRight .word viewValue) middle)
    (indexed : Evaluates (viewValue :: environment) middle (index.weakenAt 0) (.inRight .word (.word position)) after)
    (reads : ViewReads comparison layout (.word position :: viewValue :: environment) after (depth + 1) viewValue
      position result final) :
    Evaluates environment before
      (SourceCoreDataExpressions.viewIndex layout comparison.expression (depth + 1) base index) result final := by
  simp only [SourceCoreDataExpressions.viewIndex]
  apply LanguageResult.bind_success _ evaluated (LanguageResult.bind_success _ indexed _)
  rw [CompatibleMapping.Transport.expression_weaken, CompatibleMapping.Transport.expression_weaken]
  exact viewRead_evaluates prepared keyType reads (.var rfl) (.select (.var rfl))

theorem viewIndex_base_failure {environment : Environment} {before after : Store} {depth : Nat}
    {base index : Expr} {type : Ty} {reason : Word}
    (failed : Evaluates environment before base (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.viewIndex layout comparison.expression depth base index)
      (.inLeft layout.valueType (.word reason)) after := by
  cases depth with
  | zero => exact arrayIndex_base_failure failed
  | succ depth => exact LanguageResult.bind_failure _ failed

theorem viewIndex_index_failure {environment : Environment} {before middle after : Store} {depth : Nat}
    {base index : Expr} {view : Value} {type : Ty} {reason : Word}
    (evaluated : Evaluates environment before base (.inRight .word view) middle)
    (failed : Evaluates (view :: environment) middle (index.weakenAt 0) (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.viewIndex layout comparison.expression depth base index)
      (.inLeft layout.valueType (.word reason)) after := by
  cases depth with
  | zero => exact arrayIndex_index_failure evaluated failed
  | succ depth => exact LanguageResult.bind_success _ evaluated (LanguageResult.bind_failure _ failed)

end Reads


/-! ### Slices -/

/-- A view's length on Core values: an array cell's first component, or a slice's last. -/
inductive ViewLength (store : Store) : Nat → Value → Word → Prop where
  | array {type : Ty} {location : Location} {length : Word} {rest : Value}
      (read : store.read? location = some (.pair (.word length) rest)) :
      ViewLength store 0 (.cellRef type location) length
  | slice {depth : Nat} {inner : Value} {start length : Word} :
      ViewLength store (depth + 1) (.pair inner (.pair (.word start) (.word length))) length

theorem ViewLength.evaluates {store : Store} {depth : Nat} {viewValue : Value} {length : Word}
    (measured : ViewLength store depth viewValue length) {environment : Environment} {view : Expr}
    (selected : DataEquality.Selects environment view viewValue) :
    Evaluates environment store (SourceCoreDataExpressions.viewLength depth view) (.word length) store := by
  cases measured with
  | array read => exact .first (.loadCell (selected.evaluates store) read)
  | slice => exact selected.second.second.evaluates store

/-- A slice's bounds check on Core values: the base, the start and the length `stop - start` when
`start ≤ stop ≤ length`, else `Panic(0x32)`. -/
def sliced (sliceType : Ty) (view : Value) (first last length : Word) : Value :=
  if ¬ first > last ∧ ¬ last > length then .inRight .word (.pair view (.pair (.word first) (.word (last.sub first))))
  else .inLeft sliceType (.word outOfBounds)

section Slices
variable {baseType : Ty} {depth : Nat} {environment : Environment}

private theorem made_evaluates {store : Store} {view firstCode lastCode : Expr} {viewValue : Value}
    {first last length : Word} (viewSelected : DataEquality.Selects environment view viewValue)
    (firstEvaluated : Evaluates environment store firstCode (.word first) store)
    (lastEvaluated : Evaluates environment store lastCode (.word last) store)
    (measured : ViewLength store depth viewValue length) :
    Evaluates environment store
      (.ifE (firstCode.wordLe lastCode)
        (.ifE (lastCode.wordLe (SourceCoreDataExpressions.viewLength depth view))
          (LanguageResult.success (.pair view (.pair firstCode (.binary .wordSub lastCode firstCode))))
          (LanguageResult.failure (.product baseType (.product .word .word)) (.word outOfBounds)))
        (LanguageResult.failure (.product baseType (.product .word .word)) (.word outOfBounds)))
      (sliced (.product baseType (.product .word .word)) viewValue first last length) store := by
  have lengthEvaluated := measured.evaluates viewSelected
  by_cases ordered : first > last
  · have result : sliced (.product baseType (.product .word .word)) viewValue first last length =
        .inLeft (.product baseType (.product .word .word)) (.word outOfBounds) := by
      simp [sliced, ordered]
    rw [result]
    apply Evaluates.ifFalse
    · simpa only [ordered, decide_true, Bool.not_true] using wordLe_evaluates firstEvaluated lastEvaluated
    · exact .inLeft .word
  · by_cases within : last > length
    · have result : sliced (.product baseType (.product .word .word)) viewValue first last length =
          .inLeft (.product baseType (.product .word .word)) (.word outOfBounds) := by
        simp [sliced, within]
      rw [result]
      apply Evaluates.ifTrue
      · simpa only [ordered, decide_false, Bool.not_false] using wordLe_evaluates firstEvaluated lastEvaluated
      · apply Evaluates.ifFalse
        · simpa only [within, decide_true, Bool.not_true] using wordLe_evaluates lastEvaluated lengthEvaluated
        · exact .inLeft .word
    · have result : sliced (.product baseType (.product .word .word)) viewValue first last length =
          .inRight .word (.pair viewValue (.pair (.word first) (.word (last.sub first)))) := by
        simp [sliced, ordered, within]
      rw [result]
      apply Evaluates.ifTrue
      · simpa only [ordered, decide_false, Bool.not_false] using wordLe_evaluates firstEvaluated lastEvaluated
      · apply Evaluates.ifTrue
        · simpa only [within, decide_false, Bool.not_false] using wordLe_evaluates lastEvaluated lengthEvaluated
        · exact .inRight (.pair (viewSelected.evaluates store)
            (.pair firstEvaluated (.binary lastEvaluated firstEvaluated rfl)))

theorem arraySlice_base_failure {before after : Store} {base : Expr} {start stop : Option Expr}
    {type : Ty} {reason : Word}
    (failed : Evaluates environment before base (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.arraySlice baseType depth base start stop)
      (.inLeft (.product baseType (.product .word .word)) (.word reason)) after := by
  unfold SourceCoreDataExpressions.arraySlice
  exact LanguageResult.bind_failure _ failed

/-- `a[s:e]`: the base's, the start's and the stop's runs, then the bounds check. -/
theorem arraySlice_both {before middle started after : Store} {base start stop : Expr} {viewValue : Value}
    {first last length : Word}
    (evaluated : Evaluates environment before base (.inRight .word viewValue) middle)
    (startEvaluated : Evaluates (viewValue :: environment) middle (start.weakenAt 0) (.inRight .word (.word first))
      started)
    (stopEvaluated : Evaluates (.word first :: viewValue :: environment) started ((stop.weakenAt 0).weakenAt 0)
      (.inRight .word (.word last)) after)
    (measured : ViewLength after depth viewValue length) :
    Evaluates environment before (SourceCoreDataExpressions.arraySlice baseType depth base (some start) (some stop))
      (sliced (.product baseType (.product .word .word)) viewValue first last length) after := by
  unfold SourceCoreDataExpressions.arraySlice
  exact LanguageResult.bind_success _ evaluated (LanguageResult.bind_success _ startEvaluated
    (LanguageResult.bind_success _ stopEvaluated (made_evaluates (.var rfl) (.var rfl) (.var rfl) measured)))

theorem arraySlice_both_start_failure {before middle after : Store} {base start stop : Expr} {viewValue : Value}
    {type : Ty} {reason : Word}
    (evaluated : Evaluates environment before base (.inRight .word viewValue) middle)
    (failed : Evaluates (viewValue :: environment) middle (start.weakenAt 0) (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.arraySlice baseType depth base (some start) (some stop))
      (.inLeft (.product baseType (.product .word .word)) (.word reason)) after := by
  unfold SourceCoreDataExpressions.arraySlice
  exact LanguageResult.bind_success _ evaluated (LanguageResult.bind_failure _ failed)

theorem arraySlice_both_stop_failure {before middle started after : Store} {base start stop : Expr}
    {viewValue : Value} {first : Word} {type : Ty} {reason : Word}
    (evaluated : Evaluates environment before base (.inRight .word viewValue) middle)
    (startEvaluated : Evaluates (viewValue :: environment) middle (start.weakenAt 0) (.inRight .word (.word first))
      started)
    (failed : Evaluates (.word first :: viewValue :: environment) started ((stop.weakenAt 0).weakenAt 0)
      (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.arraySlice baseType depth base (some start) (some stop))
      (.inLeft (.product baseType (.product .word .word)) (.word reason)) after := by
  unfold SourceCoreDataExpressions.arraySlice
  exact LanguageResult.bind_success _ evaluated (LanguageResult.bind_success _ startEvaluated
    (LanguageResult.bind_failure _ failed))

/-- `a[s:]`: the stop is the view's length. -/
theorem arraySlice_from {before middle after : Store} {base start : Expr} {viewValue : Value} {first length : Word}
    (evaluated : Evaluates environment before base (.inRight .word viewValue) middle)
    (startEvaluated : Evaluates (viewValue :: environment) middle (start.weakenAt 0) (.inRight .word (.word first))
      after)
    (measured : ViewLength after depth viewValue length) :
    Evaluates environment before (SourceCoreDataExpressions.arraySlice baseType depth base (some start) none)
      (sliced (.product baseType (.product .word .word)) viewValue first length length) after := by
  unfold SourceCoreDataExpressions.arraySlice
  exact LanguageResult.bind_success _ evaluated (LanguageResult.bind_success _ startEvaluated
    (made_evaluates (.var rfl) (.var rfl) (measured.evaluates (.var rfl)) measured))

theorem arraySlice_from_start_failure {before middle after : Store} {base start : Expr} {viewValue : Value}
    {type : Ty} {reason : Word}
    (evaluated : Evaluates environment before base (.inRight .word viewValue) middle)
    (failed : Evaluates (viewValue :: environment) middle (start.weakenAt 0) (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.arraySlice baseType depth base (some start) none)
      (.inLeft (.product baseType (.product .word .word)) (.word reason)) after := by
  unfold SourceCoreDataExpressions.arraySlice
  exact LanguageResult.bind_success _ evaluated (LanguageResult.bind_failure _ failed)

/-- `a[:e]`: the start is zero. -/
theorem arraySlice_to {before middle after : Store} {base stop : Expr} {viewValue : Value} {last length : Word}
    (evaluated : Evaluates environment before base (.inRight .word viewValue) middle)
    (stopEvaluated : Evaluates (viewValue :: environment) middle (stop.weakenAt 0) (.inRight .word (.word last)) after)
    (measured : ViewLength after depth viewValue length) :
    Evaluates environment before (SourceCoreDataExpressions.arraySlice baseType depth base none (some stop))
      (sliced (.product baseType (.product .word .word)) viewValue Word.zero last length) after := by
  unfold SourceCoreDataExpressions.arraySlice
  exact LanguageResult.bind_success _ evaluated (LanguageResult.bind_success _ stopEvaluated
    (made_evaluates (.var rfl) .word (.var rfl) measured))

theorem arraySlice_to_stop_failure {before middle after : Store} {base stop : Expr} {viewValue : Value}
    {type : Ty} {reason : Word}
    (evaluated : Evaluates environment before base (.inRight .word viewValue) middle)
    (failed : Evaluates (viewValue :: environment) middle (stop.weakenAt 0) (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.arraySlice baseType depth base none (some stop))
      (.inLeft (.product baseType (.product .word .word)) (.word reason)) after := by
  unfold SourceCoreDataExpressions.arraySlice
  exact LanguageResult.bind_success _ evaluated (LanguageResult.bind_failure _ failed)

/-- `a[:]`: the whole view. -/
theorem arraySlice_all {before after : Store} {base : Expr} {viewValue : Value} {length : Word}
    (evaluated : Evaluates environment before base (.inRight .word viewValue) after)
    (measured : ViewLength after depth viewValue length) :
    Evaluates environment before (SourceCoreDataExpressions.arraySlice baseType depth base none none)
      (sliced (.product baseType (.product .word .word)) viewValue Word.zero length length) after := by
  unfold SourceCoreDataExpressions.arraySlice
  exact LanguageResult.bind_success _ evaluated
    (made_evaluates (.var rfl) .word (measured.evaluates (.var rfl)) measured)

end Slices

/-! ### Memrefs -/

private theorem write_at {store : Store} {location : Location} (bound : location < store.length) (value : Value) :
    store.write? location value = some (store.set location value) := by
  simp [Store.write?, bound]


section Memrefs
variable {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
  {comparison : SourceCoreCompatibleDataEquality.Prepared checked} {layout : OrderedMapping.Layout}
  {environment : Environment}

theorem memrefLoad_failure {before after : Store} {reference : Expr} {type : Ty} {reason : Word}
    (failed : Evaluates environment before reference (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.memrefLoad layout comparison.expression reference)
      (.inLeft layout.valueType (.word reason)) after :=
  LanguageResult.bind_failure _ failed

/-- `CanStore.load(r)`: the memref's run, then the read of its array at its position. -/
theorem memrefLoad_evaluates
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
    (keyType : layout.keyType = .word) {before after : Store} {reference : Expr} {type : Ty} {location : Location}
    {position : Word} {result : Value} {final : Store}
    (evaluated : Evaluates environment before reference
      (.inRight .word (.pair (.cellRef type location) (.word position))) after)
    (reads : ViewReads comparison layout (.pair (.cellRef type location) (.word position) :: environment) after 0
      (.cellRef type location) position result final) :
    Evaluates environment before (SourceCoreDataExpressions.memrefLoad layout comparison.expression reference)
      result final := by
  apply LanguageResult.bind_success _ evaluated
  rw [CompatibleMapping.Transport.expression_weaken]
  exact viewRead_evaluates prepared keyType reads (.first (.var rfl)) (.select (.second (.var rfl)))

theorem memrefStore_reference_failure {before after : Store} {reference value : Expr} {type : Ty} {reason : Word}
    (failed : Evaluates environment before reference (.inLeft type (.word reason)) after) :
    Evaluates environment before
      (SourceCoreDataExpressions.memrefStore layout comparison.expression reference value)
      (.inLeft .unit (.word reason)) after :=
  LanguageResult.bind_failure _ failed

theorem memrefStore_value_failure {before middle after : Store} {reference value : Expr} {memref : Value}
    {type : Ty} {reason : Word}
    (evaluated : Evaluates environment before reference (.inRight .word memref) middle)
    (failed : Evaluates (memref :: environment) middle (value.weakenAt 0) (.inLeft type (.word reason)) after) :
    Evaluates environment before
      (SourceCoreDataExpressions.memrefStore layout comparison.expression reference value)
      (.inLeft .unit (.word reason)) after :=
  LanguageResult.bind_success _ evaluated (LanguageResult.bind_failure _ failed)

/-- `CanStore.store(r, v)`: the memref's and the value's runs, then its array's cell takes the value at
its position, keeping its length and default element, and the store gives `()`. -/
theorem memrefStore_evaluates
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
    (keyType : layout.keyType = .word) {before middle after : Store} {reference value : Expr} {type : Ty}
    {location : Location} {position length : Word} {default stored : Value} {entries : OrderedMapping.Entries}
    (evaluated : Evaluates environment before reference
      (.inRight .word (.pair (.cellRef type location) (.word position))) middle)
    (valueEvaluated : Evaluates (.pair (.cellRef type location) (.word position) :: environment) middle
      (value.weakenAt 0) (.inRight .word stored) after)
    (read : after.read? location = some (.pair (.word length) (.pair default (OrderedMapping.encode layout entries))))
    (wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word) :
    Evaluates environment before
      (SourceCoreDataExpressions.memrefStore layout comparison.expression reference value)
      (.inRight .word .unit)
      ((CompatibleMappingComparison.insertStore comparison layout
          (stored :: .pair (.cellRef type location) (.word position) :: environment) after entries
          (.word position) stored).set location
        (.pair (.word length) (.pair default (OrderedMapping.encode layout
          (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) stored entries))))) := by
  apply LanguageResult.bind_success _ evaluated (LanguageResult.bind_success _ valueEvaluated _)
  rw [CompatibleMapping.Transport.expression_weaken, CompatibleMapping.Transport.expression_weaken]
  let stack := stored :: .pair (.cellRef type location) (.word position) :: environment
  have inserted := OrderedMapping.insert_evaluates (environment := stack)
    (mapping := .second (.second (.loadCell (.first (.var 1))))) (keyExpr := .second (.var 1)) (valueExpr := .var 0)
    (keyEqual := comparison.expression) entries (.word position) stored
    (CompatibleMappingComparison.comparator comparison stack after) GenericHeap.arrayKeyEqual
    (.second (.second (.loadCell (.first (.var rfl)) read))) (.second (.var rfl)) (.var rfl)
    (CompatibleEquality.prepared_evaluates_exact comparison stack after)
    (word_comparisons prepared keyType stack after wordKeys position _)
  apply LanguageResult.bind_success _ inserted
  have bound : location < after.length := (List.getElem?_eq_some_iff.mp read).1
  have kept : (CompatibleMappingComparison.insertStore comparison layout stack after entries (.word position)
      stored).read? location = some (.pair (.word length) (.pair default (OrderedMapping.encode layout entries))) := by
    simp only [CompatibleMappingComparison.insertStore, OrderedMapping.installedStore, WordMapping.installedStore,
      CompatibleMappingComparison.comparisonStore, Store.read?, List.append_assoc] at read ⊢
    rw [List.getElem?_append_left bound]
    exact read
  have keptBound : location <
      (CompatibleMappingComparison.insertStore comparison layout stack after entries (.word position) stored).length :=
    (List.getElem?_eq_some_iff.mp kept).1
  apply Evaluates.letE (.storeCell (.first (.var rfl)) kept
    (.pair (.first (.loadCell (.first (.var rfl)) kept)) (.pair (.first (.second (.loadCell (.first (.var rfl)) kept)))
      (.var rfl))) (write_at keptBound _))
  exact .inRight .unit

end Memrefs

/-! ### Literals and defaults -/

/-- A literal's entries: each element at its own position, from `index` on. -/
def literalEntries : Nat → List Value → OrderedMapping.Entries
  | _, [] => []
  | index, value :: values => (.word (Word.ofNatModulo index), value) :: literalEntries (index + 1) values

/-- A literal's entries' code, on the packed elements. -/
theorem arrayLiteralEntries_evaluates {layout : OrderedMapping.Layout} {environment : Environment} {store : Store} :
    ∀ (values : List Value) (index : Nat) {packed : Expr},
      DataEquality.Selects environment packed (DataPatternValues.packValues values) →
      Evaluates environment store (SourceCoreDataExpressions.arrayLiteralEntries layout index values.length packed)
        (OrderedMapping.encode layout (literalEntries index values)) store
  | [], _, _, _ => .construct .unit
  | [_], _, _, selected => .construct (.pair (.pair .word (selected.evaluates store)) (.construct .unit))
  | _ :: second :: rest, index, _, selected =>
    .construct (.pair (.pair .word (selected.first.evaluates store))
      (arrayLiteralEntries_evaluates (second :: rest) (index + 1) selected.second))

theorem arrayLiteral_failure {layout : OrderedMapping.Layout} {environment : Environment} {before after : Store}
    {default elements : Expr} {count : Nat} {type : Ty} {reason : Word}
    (failed : Evaluates environment before elements (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreDataExpressions.arrayLiteral layout default elements count)
      (.inLeft (.cell (.product .word (.product layout.valueType layout.type))) (.word reason)) after :=
  LanguageResult.bind_failure _ failed

/-- `[e₀, …, eₙ₋₁]`: the elements' run, then one cell of `n`, the default element and each element at its
own position, after the default's own cells. -/
theorem arrayLiteral_evaluates {layout : OrderedMapping.Layout} {environment : Environment}
    {before middle defaulted : Store} {default elements : Expr} {values : List Value} {defaultValue : Value}
    (evaluated : Evaluates environment before elements (.inRight .word (DataPatternValues.packValues values)) middle)
    (defaultEvaluated : Evaluates (DataPatternValues.packValues values :: environment) middle (default.weakenAt 0)
      defaultValue defaulted) :
    Evaluates environment before (SourceCoreDataExpressions.arrayLiteral layout default elements values.length)
      (.inRight .word (.cellRef (.product .word (.product layout.valueType layout.type)) defaulted.length))
      (defaulted ++ [.pair (.word (Word.ofNatModulo values.length))
        (.pair defaultValue (OrderedMapping.encode layout (literalEntries 0 values)))]) :=
  LanguageResult.bind_success _ evaluated (.inRight (.newCell (.pair .word (.pair defaultEvaluated
    (arrayLiteralEntries_evaluates values 0 (.var rfl))))))

/-- A default element's code is closed. -/
theorem arrayDefault_rename {catalog : SourceCoreCompatibleCatalog.Catalog} {element : TypeSystem.Ty}
    {default : Expr} (defined : SourceCoreCompatibleDataExpressions.arrayDefault catalog element = some default)
    (ξ : Renaming) : default.rename ξ = default := by
  induction element using SourceCoreCompatibleDataExpressions.arrayDefault.induct generalizing default with
  | case1 =>
    simp only [SourceCoreCompatibleDataExpressions.arrayDefault, Option.some.injEq] at defined
    subst default; rfl
  | case2 type =>
    simp only [SourceCoreCompatibleDataExpressions.arrayDefault, Option.some.injEq] at defined
    subst default; rfl
  | case3 inner ih =>
    unfold SourceCoreCompatibleDataExpressions.arrayDefault at defined
    cases projected : (catalog.project inner).toOption <;>
      cases identified : catalog.identity? (.mapping (.constructor (.builtin .word)) inner) <;>
      cases innerDefined : SourceCoreCompatibleDataExpressions.arrayDefault catalog inner <;>
      simp only [projected, identified, innerDefined, bind, Option.bind, reduceCtorEq, Option.some.injEq] at defined
    rename_i innerType identity innerDefault
    subst default
    simp only [Expr.rename, OrderedMapping.empty, ih innerDefined]
  | case4 other notWord notFixed notArray =>
    rw [SourceCoreCompatibleDataExpressions.arrayDefault.eq_def] at defined
    split at defined
    · exact absurd rfl notWord
    · exact absurd rfl (notFixed _)
    · exact absurd rfl (notArray _)
    · cases defined

theorem arrayDefault_weaken {catalog : SourceCoreCompatibleCatalog.Catalog} {element : TypeSystem.Ty}
    {default : Expr} (defined : SourceCoreCompatibleDataExpressions.arrayDefault catalog element = some default)
    (cutoff : Nat) : default.weakenAt cutoff = default := by
  rw [← Expr.rename_insertion]
  exact arrayDefault_rename defined _

end Solcore.SourceSemantics.CoreLowering.CompatibleArrayEvaluation
end
