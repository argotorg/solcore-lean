import Solcore.Core.Mappings
import Solcore.Core.Internal.ConventionLaws
import Solcore.Core.Internal.Renaming
import Solcore.Core.Correspondence

/-!
# Laws of the mappings

Typing and evaluation laws of `WordMapping` and `OrderedMapping`.
-/

section
-- leanmerge: from Solcore.Core.WordMapping
/-! A fixed-catalog prototype for ordered `mapping(Word => Word)`. Its carrier,
recursion, and language outcomes use existing Core syntax. The source compiler
must allocate a catalog identity before generalizing this standalone helper. -/

set_option autoImplicit false

namespace Solcore.Core.WordMapping

theorem definitions_wellFormed : actualDefinitions.isWellFormed = true := rfl

theorem type_wellFormed : Ty.WellFormed actualDefinitions type := .namedData rfl

theorem literal_hasType (entries : Entries) (context : Context) :
    HasType context (literal entries) type actualDefinitions := by
  induction entries with
  | nil => exact .construct rfl .unit
  | cons entry rest ih => exact .construct rfl (.pair (.pair .word .word) ih)

theorem encode_hasType (entries : Entries) (world : StoreTyping) :
    RuntimeValueHasType world (encode entries) type actualDefinitions := by
  induction entries with
  | nil => exact .constructed rfl .unit
  | cons entry rest ih => exact .constructed rfl (.pair (.pair .word .word) ih)

theorem literal_evaluates (entries : Entries) (environment : Environment) (store : Store) :
    Evaluates environment store (literal entries) (encode entries) store := by
  induction entries with
  | nil => exact .construct .unit
  | cons entry rest ih => exact .construct (.pair (.pair .word .word) ih)

theorem lookupBody_hasType (context : Context) :
    HasType (lookupParameter :: OptionalCell.referenceType (helperType lookupParameter .word) :: context)
      lookupBody (LanguageResult.resultType .word) actualDefinitions := by
  apply infer_sound
  simp only [lookupBody, invoke, Expr.weakenAt]
  rfl

theorem insertBody_hasType (context : Context) :
    HasType (insertParameter :: OptionalCell.referenceType (helperType insertParameter type) :: context)
      insertBody (LanguageResult.resultType type) actualDefinitions := by
  apply infer_sound
  simp only [insertBody, invoke, Expr.weakenAt]
  rfl

theorem invoke_evaluates
    {environment captured : Environment} {store : Store} {parameter result : Ty}
    {body reference argument : Expr} {location : Location} {input output : Value}
    (referenceEvaluated : Evaluates environment store reference
      (.cellRef (OptionalCell.cellType (helperType parameter result)) location) store)
    (installed : Installed store parameter result body location captured)
    (argumentEvaluated : Evaluates
      (closure parameter result body location captured :: environment)
      store (argument.weakenAt 0) input store)
    (bodyEvaluated : Evaluates
      (input :: .cellRef (OptionalCell.cellType (helperType parameter result)) location :: captured)
      store body output store) :
    Evaluates environment store (invoke parameter result reference argument) output store := by
  exact Evaluates.caseRight
    (OptionalCell.read_success Word.zero referenceEvaluated installed)
    (.apply (.var rfl) argumentEvaluated bodyEvaluated)

theorem lookupBody_evaluates (entries : Entries) (key : Word)
    (store : Store) (location : Location) (captured : Environment)
    (installed : Installed store lookupParameter .word lookupBody location captured) :
    Evaluates
      (.pair (encode entries) (.word key) ::
        .cellRef (OptionalCell.cellType (helperType lookupParameter .word)) location :: captured)
      store lookupBody (.inRight .word (.word (lookupEntries key entries))) store := by
  induction entries with
  | nil => exact .matchData (.first (.var rfl)) rfl rfl (.inRight .word)
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, value⟩
      unfold lookupBody
      apply Evaluates.matchData (constructor := consConstructor) (.first (.var rfl)) rfl rfl
      by_cases same : (key == storedKey) = true
      · simp only [lookupEntries, same, ↓reduceIte]
        exact .ifTrue (.binary (.second (.var rfl)) (.first (.first (.var rfl)))
          (by simp [BinaryOp.apply, same])) (.inRight (.second (.first (.var rfl))))
      · have different : (key == storedKey) = false := Bool.eq_false_iff.mpr same
        simp only [lookupEntries, different, Bool.false_eq_true, ↓reduceIte]
        apply Evaluates.ifFalse
          (.binary (.second (.var rfl)) (.first (.first (.var rfl)))
            (by simp [BinaryOp.apply, different]))
        apply invoke_evaluates (.var rfl) installed
        · simpa [Expr.weakenAt] using
            (Evaluates.pair (Evaluates.second (Evaluates.var (by rfl)))
              (Evaluates.second (Evaluates.var (by rfl))))
        · exact ih

theorem insertBody_evaluates (entries : Entries) (key value : Word)
    (store : Store) (location : Location) (captured : Environment)
    (installed : Installed store insertParameter type insertBody location captured) :
    Evaluates
      (.pair (encode entries) (.pair (.word key) (.word value)) ::
        .cellRef (OptionalCell.cellType (helperType insertParameter type)) location :: captured)
      store insertBody (.inRight .word (encode (insertEntries key value entries))) store := by
  induction entries with
  | nil =>
      exact .matchData (.first (.var rfl)) rfl rfl
        (.inRight (.construct (.pair
          (.pair (.first (.second (.var rfl))) (.second (.second (.var rfl))))
          (.construct .unit))))
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, storedValue⟩
      unfold insertBody
      apply Evaluates.matchData (constructor := consConstructor) (.first (.var rfl)) rfl rfl
      by_cases same : (key == storedKey) = true
      · simp only [insertEntries, same, ↓reduceIte]
        exact .ifTrue
          (.binary (.first (.second (.var rfl))) (.first (.first (.var rfl)))
            (by simp [BinaryOp.apply, same]))
          (.inRight (.construct (.pair
            (.pair (.first (.second (.var rfl))) (.second (.second (.var rfl))))
            (.second (.var rfl)))))
      · have different : (key == storedKey) = false := Bool.eq_false_iff.mpr same
        simp only [insertEntries, different, Bool.false_eq_true, ↓reduceIte]
        apply Evaluates.ifFalse
          (.binary (.first (.second (.var rfl))) (.first (.first (.var rfl)))
            (by simp [BinaryOp.apply, different]))
        apply LanguageResult.bind_success type
        · apply invoke_evaluates (.var rfl) installed
          · simpa [Expr.weakenAt] using
              (Evaluates.pair (Evaluates.second (Evaluates.var (by rfl)))
                (Evaluates.second (Evaluates.var (by rfl))))
          · exact ih
        · exact .inRight (.construct (.pair
            (.pair (.first (.first (.var rfl))) (.second (.first (.var rfl)))) (.var rfl)))

theorem invoke_hasType {context : Context} {parameter result : Ty}
    {reference argument : Expr}
    (parameterWF : Ty.WellFormed actualDefinitions parameter)
    (resultWF : Ty.WellFormed actualDefinitions result)
    (referenceTyped : HasType context reference
      (OptionalCell.referenceType (helperType parameter result)) actualDefinitions)
    (argumentTyped : HasType context argument parameter actualDefinitions) :
    HasType context (invoke parameter result reference argument)
      (LanguageResult.resultType result) actualDefinitions := by
  apply LanguageResult.bind_hasType resultWF
    (OptionalCell.read_hasType Word.zero (.function parameterWF (.sum .word resultWF)) referenceTyped)
  apply HasType.apply (.var rfl)
  simpa [Context.insertAt, helperType, LanguageResult.resultType] using argumentTyped.weakenAt
    (inserted := helperType parameter result) 0

theorem runHelper_hasType {context : Context} {parameter result : Ty} {body argument : Expr}
    (parameterWF : Ty.WellFormed actualDefinitions parameter)
    (resultWF : Ty.WellFormed actualDefinitions result)
    (argumentTyped : HasType context argument parameter actualDefinitions)
    (bodyTyped : HasType
      (parameter :: OptionalCell.referenceType (helperType parameter result) :: parameter :: context)
      body (LanguageResult.resultType result) actualDefinitions) :
    HasType context (runHelper parameter result body argument)
      (LanguageResult.resultType result) actualDefinitions :=
  .letE argumentTyped
    (.letE (OptionalCell.allocate_hasType (.function parameterWF (.sum .word resultWF)))
      (.letE (.storeCell (.var rfl)
        (.inRight .unit (.lambda parameterWF (.sum .word resultWF) bodyTyped)))
        (invoke_hasType parameterWF resultWF (.var rfl) (.var rfl))))

theorem lookup_hasType {context : Context} {mapping key : Expr}
    (mappingTyped : HasType context mapping type actualDefinitions)
    (keyTyped : HasType context key .word actualDefinitions) :
    HasType context (lookup mapping key) (LanguageResult.resultType .word) actualDefinitions :=
  runHelper_hasType (.product type_wellFormed .word) .word
    (.pair mappingTyped keyTyped) (lookupBody_hasType _)

theorem insert_hasType {context : Context} {mapping key value : Expr}
    (mappingTyped : HasType context mapping type actualDefinitions)
    (keyTyped : HasType context key .word actualDefinitions)
    (valueTyped : HasType context value .word actualDefinitions) :
    HasType context (insert mapping key value) (LanguageResult.resultType type) actualDefinitions :=
  runHelper_hasType (.product type_wellFormed (.product .word .word)) type_wellFormed
    (.pair mappingTyped (.pair keyTyped valueTyped)) (insertBody_hasType _)

theorem runHelper_evaluates {environment : Environment} {initialStore argumentStore : Store}
    {parameter result : Ty} {body argument : Expr} {input output : Value}
    (argumentEvaluated : Evaluates environment initialStore argument input argumentStore)
    (bodyEvaluated : Evaluates
      (input :: .cellRef (OptionalCell.cellType (helperType parameter result)) argumentStore.length ::
        input :: environment)
      (installedStore argumentStore parameter result body input environment) body output
      (installedStore argumentStore parameter result body input environment)) :
    Evaluates environment initialStore (runHelper parameter result body argument) output
      (installedStore argumentStore parameter result body input environment) := by
  apply Evaluates.letE argumentEvaluated
  apply Evaluates.letE (OptionalCell.allocate_evaluates _ _ _)
  apply Evaluates.letE (bodyStore := installedStore argumentStore parameter result body input environment)
  · apply Evaluates.storeCell (oldValue := .inLeft (helperType parameter result) .unit) (.var rfl)
    · simp [Store.read?]
    · exact .inRight .lambda
    · simp [Store.write?, installedStore, closure]
  · apply invoke_evaluates (body := body) (captured := input :: environment) (.var rfl)
    · simp [Installed, installedStore, Store.read?]
    · simpa [Expr.weakenAt] using (Evaluates.var (by rfl))
    · exact bodyEvaluated

theorem lookup_evaluates {environment : Environment} {initialStore mappingStore keyStore : Store}
    {mapping keyExpr : Expr} (entries : Entries) (key : Word)
    (mappingEvaluated : Evaluates environment initialStore mapping (encode entries) mappingStore)
    (keyEvaluated : Evaluates environment mappingStore keyExpr (.word key) keyStore) :
    Evaluates environment initialStore (lookup mapping keyExpr)
      (.inRight .word (.word (lookupEntries key entries)))
      (installedStore keyStore lookupParameter .word lookupBody
        (.pair (encode entries) (.word key)) environment) := by
  apply runHelper_evaluates (.pair mappingEvaluated keyEvaluated)
  apply lookupBody_evaluates
  simp [Installed, installedStore, Store.read?]

theorem insert_evaluates {environment : Environment}
    {initialStore mappingStore keyStore valueStore : Store}
    {mapping keyExpr valueExpr : Expr} (entries : Entries) (key value : Word)
    (mappingEvaluated : Evaluates environment initialStore mapping (encode entries) mappingStore)
    (keyEvaluated : Evaluates environment mappingStore keyExpr (.word key) keyStore)
    (valueEvaluated : Evaluates environment keyStore valueExpr (.word value) valueStore) :
    Evaluates environment initialStore (insert mapping keyExpr valueExpr)
      (.inRight .word (encode (insertEntries key value entries)))
      (installedStore valueStore insertParameter type insertBody
        (.pair (encode entries) (.pair (.word key) (.word value))) environment) := by
  apply runHelper_evaluates (.pair mappingEvaluated (.pair keyEvaluated valueEvaluated))
  apply insertBody_evaluates
  simp [Installed, installedStore, Store.read?]

/-- A finite list gives a concrete finite run; fuel exhaustion remains a
separate machine observation below the sufficient bound. -/
theorem lookup_run_complete (entries : Entries) (key : Word) (environment : Environment) (store : Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (State.initial (lookup (literal entries) (.word key)) environment store) =
        .done (.inRight .word (.word (lookupEntries key entries)))
          (installedStore store lookupParameter .word lookupBody
            (.pair (encode entries) (.word key)) environment) :=
  evaluation_runStateful_complete_with_sufficient_fuel
    (lookup_evaluates entries key (literal_evaluates entries environment store) .word)

theorem insert_run_complete (entries : Entries) (key value : Word)
    (environment : Environment) (store : Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (State.initial (insert (literal entries) (.word key) (.word value)) environment store) =
        .done (.inRight .word (encode (insertEntries key value entries)))
          (installedStore store insertParameter type insertBody
            (.pair (encode entries) (.pair (.word key) (.word value))) environment) :=
  evaluation_runStateful_complete_with_sufficient_fuel
    (insert_evaluates entries key value (literal_evaluates entries environment store) .word .word)

theorem assign_hasType {context : Context} {reference key rhs : Expr}
    (referenceTyped : HasType context reference (OptionalCell.referenceType type) actualDefinitions)
    (keyTyped : HasType context key (LanguageResult.resultType .word) actualDefinitions)
    (rhsTyped : HasType context rhs (LanguageResult.resultType .word) actualDefinitions) :
    HasType context (assign reference key rhs) (LanguageResult.resultType .unit) actualDefinitions := by
  apply HasType.letE referenceTyped
  apply LanguageResult.bind_hasType .unit
  · simpa [Context.insertAt] using keyTyped.weakenAt
      (inserted := OptionalCell.referenceType type) 0
  · apply LanguageResult.bind_hasType .unit
    · have once := rhsTyped.weakenAt (inserted := OptionalCell.referenceType type) 0
      simpa [Context.insertAt] using once.weakenAt (inserted := Ty.word) 0
    · apply LanguageResult.bind_hasType .unit (OptionalCell.read_hasType Word.zero type_wellFormed (.var rfl))
      apply LanguageResult.bind_hasType .unit (insert_hasType (.var rfl) (.var rfl) (.var rfl))
      exact OptionalCell.write_hasType (.var rfl) (.var rfl)

/-- `latest` refers to the store produced by the RHS, with no constraint on
what this root contained before reference/key/RHS evaluation. -/
theorem assign_latest_evaluates {environment : Environment}
    {initialStore referenceStore keyStore rhsStore : Store}
    {reference keyExpr rhs : Expr} {location : Location} (entries : Entries) (key value : Word)
    (referenceEvaluated : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType type) location) referenceStore)
    (keyEvaluated : Evaluates
      (.cellRef (OptionalCell.cellType type) location :: environment)
      referenceStore (keyExpr.weakenAt 0) (.inRight .word (.word key)) keyStore)
    (rhsEvaluated : Evaluates
      (.word key :: .cellRef (OptionalCell.cellType type) location :: environment)
      keyStore ((rhs.weakenAt 0).weakenAt 0) (.inRight .word (.word value)) rhsStore)
    (latest : rhsStore.read? location = some (.inRight .unit (encode entries))) :
    Evaluates environment initialStore (assign reference keyExpr rhs)
      (.inRight .word .unit)
      ((assignInsertStore rhsStore entries key value location environment).set location
        (.inRight .unit (encode (insertEntries key value entries)))) := by
  apply Evaluates.letE referenceEvaluated
  apply LanguageResult.bind_success _ keyEvaluated
  apply LanguageResult.bind_success _ rhsEvaluated
  apply LanguageResult.bind_success _ (OptionalCell.read_success Word.zero (.var rfl) latest)
  apply LanguageResult.bind_success _ (insert_evaluates entries key value (.var rfl) (.var rfl) (.var rfl))
  have inBounds : location < rhsStore.length := (List.getElem?_eq_some_iff.mp latest).choose
  apply OptionalCell.write_evaluates (.var rfl) (oldValue := .inRight .unit (encode entries))
  · change (rhsStore ++ _)[location]? = _
    rw [List.getElem?_append_left inBounds]
    exact latest
  · exact .var rfl
  · apply Store.write?_eq_some_iff.mpr
    exact ⟨by simpa [assignInsertStore, installedStore] using Nat.lt_succ_of_lt inBounds, rfl⟩

/-- A failed key computation skips the RHS, root read, helper allocation and
write. The place's and key's preceding effects remain observable. -/
theorem assign_key_failure {environment : Environment}
    {initialStore referenceStore failureStore : Store} {reference key rhs : Expr}
    {location : Location} {reason : Word}
    (referenceEvaluated : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType type) location) referenceStore)
    (failed : Evaluates (.cellRef (OptionalCell.cellType type) location :: environment)
      referenceStore (key.weakenAt 0) (.inLeft .word (.word reason)) failureStore) :
    Evaluates environment initialStore (assign reference key rhs)
      (.inLeft .unit (.word reason)) failureStore :=
  .letE referenceEvaluated (LanguageResult.bind_failure .unit failed)

theorem assign_rhs_failure {environment : Environment}
    {initialStore referenceStore keyStore failureStore : Store} {reference keyExpr rhs : Expr}
    {location : Location} {key reason : Word}
    (referenceEvaluated : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType type) location) referenceStore)
    (keyEvaluated : Evaluates (.cellRef (OptionalCell.cellType type) location :: environment)
      referenceStore (keyExpr.weakenAt 0) (.inRight .word (.word key)) keyStore)
    (failed : Evaluates (.word key :: .cellRef (OptionalCell.cellType type) location :: environment)
      keyStore ((rhs.weakenAt 0).weakenAt 0) (.inLeft .word (.word reason)) failureStore) :
    Evaluates environment initialStore (assign reference keyExpr rhs)
      (.inLeft .unit (.word reason)) failureStore :=
  .letE referenceEvaluated (LanguageResult.bind_success .unit keyEvaluated
    (LanguageResult.bind_failure .unit failed))

end Solcore.Core.WordMapping
end

section
-- leanmerge: from Solcore.Core.OrderedMapping
/-! Ordered mappings with an explicit registered catalog layout. Comparison is
an ordinary Core closure passed in the argument bundle. Lookup distinguishes
absence from a value; source default selection belongs to the caller. -/

set_option autoImplicit false

namespace Solcore.Core.OrderedMapping

namespace Layout

theorem Registered.typeWellFormed {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) : Ty.WellFormed definitions layout.type :=
  .namedData registered.lookup

theorem Registered.comparisonWellFormed {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) : Ty.WellFormed definitions layout.comparisonType :=
  .function (.product registered.keyWellFormed registered.keyWellFormed) .bool

theorem Registered.lookupWellFormed {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) : Ty.WellFormed definitions layout.lookupResult :=
  .sum .unit registered.valueWellFormed

theorem Registered.nilLookup {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) :
    definitions.lookupConstructorPayloadType? layout.nilConstructor = some .unit := by
  simp [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?,
    nilConstructor, registered.lookup, definition]

theorem Registered.consLookup {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) :
    definitions.lookupConstructorPayloadType? layout.consConstructor =
      some (.product (.product layout.keyType layout.valueType) layout.type) := by
  simp [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?,
    consConstructor, registered.lookup, definition]

end Layout

theorem Compares.apply {layout : Layout} {comparator left right : Value} {result : Bool} {store : Store}
    (comparison : Compares layout comparator left right result store)
    {environment : Environment} {function argument : Expr}
    (functionEvaluated : Evaluates environment store function comparator store)
    (argumentEvaluated : Evaluates environment store argument (.pair left right) store) :
    Evaluates environment store (.apply function argument) (.bool result) store := by
  obtain ⟨body, captured, rfl, bodyEvaluated⟩ := comparison
  exact .apply functionEvaluated argumentEvaluated bodyEvaluated

theorem lookupBody_evaluates (layout : Layout) (entries : Entries) (key comparator : Value)
    (equal : Predicate) (store : Store) (location : Location) (captured : Environment)
    (installed : Installed store layout.lookupParameter layout.lookupResult (lookupBody layout) location captured)
    (comparisons : Comparisons layout comparator equal key entries store) :
    Evaluates
      (.pair (encode layout entries) (.pair key comparator) ::
        .cellRef (OptionalCell.cellType (helperType layout.lookupParameter layout.lookupResult)) location :: captured)
      store (lookupBody layout)
      (.inRight .word (optionValue layout.valueType (lookupEntries equal key entries))) store := by
  induction entries with
  | nil => exact .matchData (.first (.var rfl)) rfl rfl (.inRight (.inLeft .unit))
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, value⟩
      unfold lookupBody
      apply Evaluates.matchData (constructor := layout.consConstructor) (.first (.var rfl)) rfl rfl
      have compared := comparisons storedKey value (by simp)
      have tailCompared : Comparisons layout comparator equal key rest store :=
        fun k v member => comparisons k v (by simp [member])
      by_cases same : equal key storedKey = true
      · simp only [lookupEntries, same, ↓reduceIte, optionValue]
        apply Evaluates.ifTrue
        · simpa only [same] using compared.apply (.second (.second (.var rfl)))
            (.pair (.first (.second (.var rfl))) (.first (.first (.var rfl))))
        · exact .inRight (.inRight (.second (.first (.var rfl))))
      · have different : equal key storedKey = false := Bool.eq_false_iff.mpr same
        simp only [lookupEntries, different, Bool.false_eq_true, ↓reduceIte]
        apply Evaluates.ifFalse
        · simpa only [different] using compared.apply (.second (.second (.var rfl)))
            (.pair (.first (.second (.var rfl))) (.first (.first (.var rfl))))
        · apply WordMapping.invoke_evaluates (.var rfl) installed
          · simpa [Expr.weakenAt] using
              (Evaluates.pair (Evaluates.second (Evaluates.var (by rfl)))
                (Evaluates.second (Evaluates.var (by rfl))))
          · exact ih tailCompared

theorem insertBody_evaluates (layout : Layout) (entries : Entries) (key value comparator : Value)
    (equal : Predicate) (store : Store) (location : Location) (captured : Environment)
    (installed : Installed store layout.insertParameter layout.type (insertBody layout) location captured)
    (comparisons : Comparisons layout comparator equal key entries store) :
    Evaluates
      (.pair (encode layout entries) (.pair (.pair key value) comparator) ::
        .cellRef (OptionalCell.cellType (helperType layout.insertParameter layout.type)) location :: captured)
      store (insertBody layout) (.inRight .word (encode layout (insertEntries equal key value entries))) store := by
  induction entries with
  | nil =>
      exact .matchData (.first (.var rfl)) rfl rfl (.inRight (.construct (.pair
        (.pair (.first (.first (.second (.var rfl)))) (.second (.first (.second (.var rfl)))))
        (.construct .unit))))
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, storedValue⟩
      unfold insertBody
      apply Evaluates.matchData (constructor := layout.consConstructor) (.first (.var rfl)) rfl rfl
      have compared := comparisons storedKey storedValue (by simp)
      have tailCompared : Comparisons layout comparator equal key rest store :=
        fun k v member => comparisons k v (by simp [member])
      by_cases same : equal key storedKey = true
      · simp only [insertEntries, same, ↓reduceIte]
        apply Evaluates.ifTrue
        · simpa only [same] using compared.apply (.second (.second (.var rfl)))
            (.pair (.first (.first (.second (.var rfl)))) (.first (.first (.var rfl))))
        · exact .inRight (.construct (.pair
            (.pair (.first (.first (.second (.var rfl)))) (.second (.first (.second (.var rfl)))))
            (.second (.var rfl))))
      · have different : equal key storedKey = false := Bool.eq_false_iff.mpr same
        simp only [insertEntries, different, Bool.false_eq_true, ↓reduceIte]
        apply Evaluates.ifFalse
        · simpa only [different] using compared.apply (.second (.second (.var rfl)))
            (.pair (.first (.first (.second (.var rfl)))) (.first (.first (.var rfl))))
        · apply LanguageResult.bind_success layout.type
          · apply WordMapping.invoke_evaluates (.var rfl) installed
            · simpa [Expr.weakenAt] using
                (Evaluates.pair (Evaluates.second (Evaluates.var (by rfl)))
                  (Evaluates.second (Evaluates.var (by rfl))))
            · exact ih tailCompared
          · exact .inRight (.construct (.pair
              (.pair (.first (.first (.var rfl))) (.second (.first (.var rfl)))) (.var rfl)))

theorem Layout.Registered.lookupParameterWellFormed {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) : Ty.WellFormed definitions layout.lookupParameter :=
  .product registered.typeWellFormed (.product registered.keyWellFormed registered.comparisonWellFormed)

theorem Layout.Registered.insertParameterWellFormed {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) : Ty.WellFormed definitions layout.insertParameter :=
  .product registered.typeWellFormed
    (.product (.product registered.keyWellFormed registered.valueWellFormed) registered.comparisonWellFormed)

theorem empty_hasType {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) (context : Context) :
    HasType context (empty layout) layout.type definitions := .construct registered.nilLookup .unit

theorem cons_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    {key value tail : Expr} (registered : layout.Registered definitions)
    (keyTyped : HasType context key layout.keyType definitions)
    (valueTyped : HasType context value layout.valueType definitions)
    (tailTyped : HasType context tail layout.type definitions) :
    HasType context (cons layout key value tail) layout.type definitions :=
  .construct registered.consLookup (.pair (.pair keyTyped valueTyped) tailTyped)

theorem encode_hasType {definitions : DataEnvironment} {layout : Layout} {world : StoreTyping}
    (registered : layout.Registered definitions) (entries : Entries)
    (typed : ∀ key value, (key, value) ∈ entries →
      RuntimeValueHasType world key layout.keyType definitions ∧
      RuntimeValueHasType world value layout.valueType definitions) :
    RuntimeValueHasType world (encode layout entries) layout.type definitions := by
  induction entries with
  | nil => exact .constructed registered.nilLookup .unit
  | cons entry rest ih =>
      have head := typed entry.1 entry.2 (by simp)
      exact .constructed registered.consLookup (.pair (.pair head.1 head.2)
        (ih (fun key value member => typed key value (by simp [member]))))

theorem invoke_hasType {definitions : DataEnvironment} {context : Context} {parameter result : Ty}
    {reference argument : Expr} (parameterWF : Ty.WellFormed definitions parameter)
    (resultWF : Ty.WellFormed definitions result)
    (referenceTyped : HasType context reference (OptionalCell.referenceType (helperType parameter result)) definitions)
    (argumentTyped : HasType context argument parameter definitions) :
    HasType context (invoke parameter result reference argument) (LanguageResult.resultType result) definitions := by
  apply LanguageResult.bind_hasType resultWF
    (OptionalCell.read_hasType Word.zero (.function parameterWF (.sum .word resultWF)) referenceTyped)
  apply HasType.apply (.var rfl)
  simpa [Context.insertAt, helperType, WordMapping.helperType, LanguageResult.resultType] using
    argumentTyped.weakenAt (inserted := helperType parameter result) 0

theorem lookupBody_hasType {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) (context : Context) :
    HasType (layout.lookupParameter :: OptionalCell.referenceType (helperType layout.lookupParameter layout.lookupResult) :: context)
      (lookupBody layout) (LanguageResult.resultType layout.lookupResult) definitions := by
  apply HasType.matchData registered.lookup (.sum .word registered.lookupWellFormed) (.first (.var rfl))
  apply BranchesHaveType.cons
  · exact .inRight .word (.inLeft registered.valueWellFormed .unit)
  · apply BranchesHaveType.cons
    · apply HasType.ifE
      · exact .apply (.second (.second (.var rfl)))
          (.pair (.first (.second (.var rfl))) (.first (.first (.var rfl))))
      · exact .inRight .word (.inRight .unit (.second (.first (.var rfl))))
      · exact invoke_hasType registered.lookupParameterWellFormed registered.lookupWellFormed
          (.var rfl) (.pair (.second (.var rfl)) (.second (.var rfl)))
    · exact .nil

theorem insertBody_hasType {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) (context : Context) :
    HasType (layout.insertParameter :: OptionalCell.referenceType (helperType layout.insertParameter layout.type) :: context)
      (insertBody layout) (LanguageResult.resultType layout.type) definitions := by
  apply HasType.matchData registered.lookup (.sum .word registered.typeWellFormed) (.first (.var rfl))
  apply BranchesHaveType.cons
  · exact .inRight .word (cons_hasType registered
      (.first (.first (.second (.var rfl)))) (.second (.first (.second (.var rfl))))
      (empty_hasType registered _))
  · apply BranchesHaveType.cons
    · apply HasType.ifE
      · exact .apply (.second (.second (.var rfl)))
          (.pair (.first (.first (.second (.var rfl)))) (.first (.first (.var rfl))))
      · exact .inRight .word (cons_hasType registered
          (.first (.first (.second (.var rfl)))) (.second (.first (.second (.var rfl)))) (.second (.var rfl)))
      · apply LanguageResult.bind_hasType registered.typeWellFormed
          (invoke_hasType registered.insertParameterWellFormed registered.typeWellFormed
            (.var rfl) (.pair (.second (.var rfl)) (.second (.var rfl))))
        exact .inRight .word (cons_hasType registered
          (.first (.first (.var rfl))) (.second (.first (.var rfl))) (.var rfl))
    · exact .nil

theorem runHelper_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} {body argument : Expr}
    (parameterWF : Ty.WellFormed definitions parameter) (resultWF : Ty.WellFormed definitions result)
    (argumentTyped : HasType context argument parameter definitions)
    (bodyTyped : HasType
      (parameter :: OptionalCell.referenceType (helperType parameter result) :: parameter :: context)
      body (LanguageResult.resultType result) definitions) :
    HasType context (runHelper parameter result body argument) (LanguageResult.resultType result) definitions :=
  .letE argumentTyped
    (.letE (OptionalCell.allocate_hasType (.function parameterWF (.sum .word resultWF)))
      (.letE (.storeCell (.var rfl)
        (.inRight .unit (.lambda parameterWF (.sum .word resultWF) bodyTyped)))
        (invoke_hasType parameterWF resultWF (.var rfl) (.var rfl))))

theorem lookup_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    {keyEqual mapping key : Expr} (registered : layout.Registered definitions)
    (comparisonTyped : HasType context keyEqual layout.comparisonType definitions)
    (mappingTyped : HasType context mapping layout.type definitions)
    (keyTyped : HasType context key layout.keyType definitions) :
    HasType context (lookup layout keyEqual mapping key) (LanguageResult.resultType layout.lookupResult) definitions :=
  runHelper_hasType registered.lookupParameterWellFormed registered.lookupWellFormed
    (.pair mappingTyped (.pair keyTyped comparisonTyped)) (lookupBody_hasType registered _)

theorem insert_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    {keyEqual mapping key value : Expr} (registered : layout.Registered definitions)
    (comparisonTyped : HasType context keyEqual layout.comparisonType definitions)
    (mappingTyped : HasType context mapping layout.type definitions)
    (keyTyped : HasType context key layout.keyType definitions)
    (valueTyped : HasType context value layout.valueType definitions) :
    HasType context (insert layout keyEqual mapping key value) (LanguageResult.resultType layout.type) definitions :=
  runHelper_hasType registered.insertParameterWellFormed registered.typeWellFormed
    (.pair mappingTyped (.pair (.pair keyTyped valueTyped) comparisonTyped)) (insertBody_hasType registered _)

theorem lookup_evaluates {environment : Environment}
    {initialStore mappingStore keyStore comparisonStore : Store} {layout : Layout}
    {mapping keyExpr keyEqual : Expr} (entries : Entries) (key comparator : Value) (equal : Predicate)
    (mappingEvaluated : Evaluates environment initialStore mapping (encode layout entries) mappingStore)
    (keyEvaluated : Evaluates environment mappingStore keyExpr key keyStore)
    (comparatorEvaluated : Evaluates environment keyStore keyEqual comparator comparisonStore)
    (comparisons : Comparisons layout comparator equal key entries
      (installedStore comparisonStore layout.lookupParameter layout.lookupResult (lookupBody layout)
        (.pair (encode layout entries) (.pair key comparator)) environment)) :
    Evaluates environment initialStore (lookup layout keyEqual mapping keyExpr)
      (.inRight .word (optionValue layout.valueType (lookupEntries equal key entries)))
      (installedStore comparisonStore layout.lookupParameter layout.lookupResult (lookupBody layout)
        (.pair (encode layout entries) (.pair key comparator)) environment) := by
  apply WordMapping.runHelper_evaluates (.pair mappingEvaluated (.pair keyEvaluated comparatorEvaluated))
  apply lookupBody_evaluates _ _ _ _ _ _ _ _ _ comparisons
  simp [Installed, WordMapping.Installed, installedStore, WordMapping.installedStore, Store.read?]

theorem insert_evaluates {environment : Environment}
    {initialStore mappingStore keyStore valueStore comparisonStore : Store} {layout : Layout}
    {mapping keyExpr valueExpr keyEqual : Expr} (entries : Entries) (key value comparator : Value) (equal : Predicate)
    (mappingEvaluated : Evaluates environment initialStore mapping (encode layout entries) mappingStore)
    (keyEvaluated : Evaluates environment mappingStore keyExpr key keyStore)
    (valueEvaluated : Evaluates environment keyStore valueExpr value valueStore)
    (comparatorEvaluated : Evaluates environment valueStore keyEqual comparator comparisonStore)
    (comparisons : Comparisons layout comparator equal key entries
      (installedStore comparisonStore layout.insertParameter layout.type (insertBody layout)
        (.pair (encode layout entries) (.pair (.pair key value) comparator)) environment)) :
    Evaluates environment initialStore (insert layout keyEqual mapping keyExpr valueExpr)
      (.inRight .word (encode layout (insertEntries equal key value entries)))
      (installedStore comparisonStore layout.insertParameter layout.type (insertBody layout)
        (.pair (encode layout entries) (.pair (.pair key value) comparator)) environment) := by
  apply WordMapping.runHelper_evaluates
    (.pair mappingEvaluated (.pair (.pair keyEvaluated valueEvaluated) comparatorEvaluated))
  apply insertBody_evaluates _ _ _ _ _ _ _ _ _ _ comparisons
  simp [Installed, WordMapping.Installed, installedStore, WordMapping.installedStore, Store.read?]

theorem assign_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    {keyEqual reference key rhs : Expr} (registered : layout.Registered definitions)
    (comparisonTyped : HasType context keyEqual layout.comparisonType definitions)
    (referenceTyped : HasType context reference (OptionalCell.referenceType layout.type) definitions)
    (keyTyped : HasType context key (LanguageResult.resultType layout.keyType) definitions)
    (rhsTyped : HasType context rhs (LanguageResult.resultType layout.valueType) definitions) :
    HasType context (assign layout keyEqual reference key rhs) (LanguageResult.resultType .unit) definitions := by
  apply HasType.letE referenceTyped
  apply LanguageResult.bind_hasType .unit
  · simpa [Context.insertAt] using keyTyped.weakenAt
      (inserted := OptionalCell.referenceType layout.type) 0
  · apply LanguageResult.bind_hasType .unit
    · have once := rhsTyped.weakenAt (inserted := OptionalCell.referenceType layout.type) 0
      simpa [Context.insertAt] using once.weakenAt (inserted := layout.keyType) 0
    · apply HasType.letE
      · have once := comparisonTyped.weakenAt (inserted := OptionalCell.referenceType layout.type) 0
        have twice := once.weakenAt (inserted := layout.keyType) 0
        simpa [Context.insertAt] using twice.weakenAt (inserted := layout.valueType) 0
      · apply LanguageResult.bind_hasType .unit
          (OptionalCell.read_hasType Word.zero registered.typeWellFormed (.var rfl))
        apply LanguageResult.bind_hasType .unit
          (insert_hasType registered (.var rfl) (.var rfl) (.var rfl) (.var rfl))
        exact OptionalCell.write_hasType (.var rfl) (.var rfl)

theorem assign_latest_evaluates {environment : Environment} {layout : Layout}
    {initialStore referenceStore keyStore rhsStore comparisonStore : Store}
    {keyEqual reference keyExpr rhs : Expr} {location : Location}
    (entries : Entries) (key value comparator : Value) (equal : Predicate)
    (referenceEvaluated : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType layout.type) location) referenceStore)
    (keyEvaluated : Evaluates (.cellRef (OptionalCell.cellType layout.type) location :: environment)
      referenceStore (keyExpr.weakenAt 0) (.inRight .word key) keyStore)
    (rhsEvaluated : Evaluates (key :: .cellRef (OptionalCell.cellType layout.type) location :: environment)
      keyStore ((rhs.weakenAt 0).weakenAt 0) (.inRight .word value) rhsStore)
    (comparisonEvaluated : Evaluates
      (value :: key :: .cellRef (OptionalCell.cellType layout.type) location :: environment)
      rhsStore (((keyEqual.weakenAt 0).weakenAt 0).weakenAt 0) comparator comparisonStore)
    (latest : comparisonStore.read? location = some (.inRight .unit (encode layout entries)))
    (comparisons : Comparisons layout comparator equal key entries
      (assignInsertStore layout comparisonStore entries key value comparator location environment)) :
    Evaluates environment initialStore (assign layout keyEqual reference keyExpr rhs) (.inRight .word .unit)
      ((assignInsertStore layout comparisonStore entries key value comparator location environment).set location
        (.inRight .unit (encode layout (insertEntries equal key value entries)))) := by
  apply Evaluates.letE referenceEvaluated
  apply LanguageResult.bind_success _ keyEvaluated
  apply LanguageResult.bind_success _ rhsEvaluated
  apply Evaluates.letE comparisonEvaluated
  apply LanguageResult.bind_success _ (OptionalCell.read_success Word.zero (.var rfl) latest)
  apply LanguageResult.bind_success _ (insert_evaluates entries key value comparator equal
    (.var rfl) (.var rfl) (.var rfl) (.var rfl) comparisons)
  have inBounds : location < comparisonStore.length := (List.getElem?_eq_some_iff.mp latest).choose
  apply OptionalCell.write_evaluates (.var rfl) (oldValue := .inRight .unit (encode layout entries))
  · change (comparisonStore ++ _)[location]? = _
    rw [List.getElem?_append_left inBounds]
    exact latest
  · exact .var rfl
  · apply Store.write?_eq_some_iff.mpr
    exact ⟨by simpa [assignInsertStore, installedStore, WordMapping.installedStore] using
      Nat.lt_succ_of_lt inBounds, rfl⟩

theorem assign_key_failure {layout : Layout} {environment : Environment}
    {initialStore referenceStore failureStore : Store} {keyEqual reference key rhs : Expr}
    {location : Location} {reason : Word}
    (referenceEvaluated : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType layout.type) location) referenceStore)
    (failed : Evaluates (.cellRef (OptionalCell.cellType layout.type) location :: environment)
      referenceStore (key.weakenAt 0) (.inLeft layout.keyType (.word reason)) failureStore) :
    Evaluates environment initialStore (assign layout keyEqual reference key rhs)
      (.inLeft .unit (.word reason)) failureStore :=
  .letE referenceEvaluated (LanguageResult.bind_failure .unit failed)

theorem assign_rhs_failure {layout : Layout} {environment : Environment}
    {initialStore referenceStore keyStore failureStore : Store} {keyEqual reference keyExpr rhs : Expr}
    {location : Location} {key : Value} {reason : Word}
    (referenceEvaluated : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType layout.type) location) referenceStore)
    (keyEvaluated : Evaluates (.cellRef (OptionalCell.cellType layout.type) location :: environment)
      referenceStore (keyExpr.weakenAt 0) (.inRight .word key) keyStore)
    (failed : Evaluates (key :: .cellRef (OptionalCell.cellType layout.type) location :: environment)
      keyStore ((rhs.weakenAt 0).weakenAt 0) (.inLeft layout.valueType (.word reason)) failureStore) :
    Evaluates environment initialStore (assign layout keyEqual reference keyExpr rhs)
      (.inLeft .unit (.word reason)) failureStore :=
  .letE referenceEvaluated (LanguageResult.bind_success .unit keyEvaluated
    (LanguageResult.bind_failure .unit failed))

end Solcore.Core.OrderedMapping
end
