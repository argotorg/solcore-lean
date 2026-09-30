import Solcore.Core.WordMapping

/-! Ordered mappings with an explicit registered catalog layout. Comparison is
an ordinary Core closure passed in the argument bundle. Lookup distinguishes
absence from a value; source default selection belongs to the caller. -/

set_option autoImplicit false

namespace Solcore.Core.OrderedMapping

structure Layout where
  keyType : Ty
  valueType : Ty
  dataType : DataTypeId
  deriving Repr, BEq, DecidableEq

namespace Layout

def type (layout : Layout) : Ty := .namedData layout.dataType
def definition (layout : Layout) : DataDefinition :=
  { constructorPayloadTypes := [.unit, .product (.product layout.keyType layout.valueType) layout.type] }
def nilConstructor (layout : Layout) : ConstructorId := ⟨layout.dataType, 0⟩
def consConstructor (layout : Layout) : ConstructorId := ⟨layout.dataType, 1⟩
def comparisonType (layout : Layout) : Ty := .function (.product layout.keyType layout.keyType) .bool
def lookupResult (layout : Layout) : Ty := .sum .unit layout.valueType
def lookupParameter (layout : Layout) : Ty := .product layout.type (.product layout.keyType layout.comparisonType)
def insertParameter (layout : Layout) : Ty :=
  .product layout.type (.product (.product layout.keyType layout.valueType) layout.comparisonType)

structure Registered (definitions : DataEnvironment) (layout : Layout) : Prop where
  keyWellFormed : Ty.WellFormed definitions layout.keyType
  valueWellFormed : Ty.WellFormed definitions layout.valueType
  lookup : definitions[layout.dataType.index]? = some layout.definition

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

abbrev Entries := List (Value × Value)
abbrev Predicate := Value → Value → Bool

def encode (layout : Layout) : Entries → Value
  | [] => .constructed layout.nilConstructor .unit
  | (key, value) :: rest => .constructed layout.consConstructor (.pair (.pair key value) (encode layout rest))
def empty (layout : Layout) : Expr := .construct layout.nilConstructor .unit
def cons (layout : Layout) (key value tail : Expr) : Expr :=
  .construct layout.consConstructor (.pair (.pair key value) tail)
def optionValue (type : Ty) : Option Value → Value
  | none => .inLeft type .unit
  | some value => .inRight .unit value

def lookupEntries (equal : Predicate) (key : Value) : Entries → Option Value
  | [] => none
  | (storedKey, value) :: rest => if equal key storedKey then some value else lookupEntries equal key rest

def insertEntries (equal : Predicate) (key value : Value) : Entries → Entries
  | [] => [(key, value)]
  | (storedKey, storedValue) :: rest =>
      if equal key storedKey then (key, value) :: rest
      else (storedKey, storedValue) :: insertEntries equal key value rest

abbrev helperType := WordMapping.helperType
abbrev invoke := WordMapping.invoke
abbrev runHelper := WordMapping.runHelper
abbrev closure := WordMapping.closure
abbrev Installed := WordMapping.Installed
abbrev installedStore := WordMapping.installedStore

/-- Entry: argument, self reference, captured values. A match branch adds its
constructor payload. The comparator remains in the ordinary argument bundle. -/
def lookupBody (layout : Layout) : Expr :=
  .matchData layout.dataType (LanguageResult.resultType layout.lookupResult) (.first (.var 0))
    [LanguageResult.success (.inLeft layout.valueType .unit),
      .ifE (.apply (.second (.second (.var 1)))
        (.pair (.first (.second (.var 1))) (.first (.first (.var 0)))))
        (LanguageResult.success (.inRight .unit (.second (.first (.var 0)))))
        (invoke layout.lookupParameter layout.lookupResult (.var 2)
          (.pair (.second (.var 0)) (.second (.var 1))))]

def insertBody (layout : Layout) : Expr :=
  .matchData layout.dataType (LanguageResult.resultType layout.type) (.first (.var 0))
    [LanguageResult.success (cons layout (.first (.first (.second (.var 1))))
        (.second (.first (.second (.var 1)))) (empty layout)),
      .ifE (.apply (.second (.second (.var 1)))
        (.pair (.first (.first (.second (.var 1)))) (.first (.first (.var 0)))))
        (LanguageResult.success (cons layout (.first (.first (.second (.var 1))))
          (.second (.first (.second (.var 1)))) (.second (.var 0))))
        (LanguageResult.bind layout.type
          (invoke layout.insertParameter layout.type (.var 2)
            (.pair (.second (.var 0)) (.second (.var 1))))
          (LanguageResult.success
            (cons layout (.first (.first (.var 1))) (.second (.first (.var 1))) (.var 0))))]

/-- Arguments evaluate mapping, key, then the comparator expression. -/
def lookup (layout : Layout) (keyEqual mapping key : Expr) : Expr :=
  runHelper layout.lookupParameter layout.lookupResult (lookupBody layout)
    (.pair mapping (.pair key keyEqual))

/-- Arguments evaluate mapping, key, value, then the comparator expression. -/
def insert (layout : Layout) (keyEqual mapping key value : Expr) : Expr :=
  runHelper layout.insertParameter layout.type (insertBody layout)
    (.pair mapping (.pair (.pair key value) keyEqual))

/-- A concrete comparison execution, with the exact input pair and unchanged
store. No claim follows merely from the comparison function's type. -/
def Compares (layout : Layout) (comparator left right : Value) (result : Bool) (store : Store) : Prop :=
  ∃ body captured, comparator = .closure (.product layout.keyType layout.keyType) .bool body captured ∧
    Evaluates (.pair left right :: captured) store body (.bool result) store

/-- Only comparisons actually needed for this finite key/entry set are assumed.
The caller supplies these facts in the store containing the installed helper. -/
def Comparisons (layout : Layout) (comparator : Value) (equal : Predicate)
    (key : Value) (entries : Entries) (store : Store) : Prop :=
  ∀ storedKey storedValue, (storedKey, storedValue) ∈ entries →
    Compares layout comparator key storedKey (equal key storedKey) store

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

/-- Capture the place and key before the RHS, prepare the comparison closure,
then read the latest root. No previous snapshot is used for insertion. -/
def assign (layout : Layout) (keyEqual reference key rhs : Expr) : Expr :=
  .letE reference
    (LanguageResult.bind .unit (key.weakenAt 0)
      (LanguageResult.bind .unit ((rhs.weakenAt 0).weakenAt 0)
        (.letE (((keyEqual.weakenAt 0).weakenAt 0).weakenAt 0)
          (LanguageResult.bind .unit (OptionalCell.read layout.type (.var 3) Word.zero)
            (LanguageResult.bind .unit (insert layout (.var 1) (.var 0) (.var 3) (.var 2))
              (OptionalCell.write (.var 5) (.var 0)))))))

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

def assignInsertStore (layout : Layout) (store : Store) (entries : Entries)
    (key value comparator : Value) (location : Location) (environment : Environment) : Store :=
  installedStore store layout.insertParameter layout.type (insertBody layout)
    (.pair (encode layout entries) (.pair (.pair key value) comparator))
    (encode layout entries :: comparator :: value :: key ::
      .cellRef (OptionalCell.cellType layout.type) location :: environment)

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
