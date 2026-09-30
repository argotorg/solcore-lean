import Solcore.Core.OptionalCell
import Solcore.Core.Renaming
import Solcore.Core.Correspondence

/-! A fixed-catalog prototype for ordered `mapping(Word => Word)`. Its carrier,
recursion, and language outcomes use existing Core syntax. The source compiler
must allocate a catalog identity before generalizing this standalone helper. -/

set_option autoImplicit false

namespace Solcore.Core.WordMapping

abbrev Entries := List (Word × Word)
def dataType : DataTypeId := ⟨0⟩
def nilConstructor : ConstructorId := ⟨dataType, 0⟩
def consConstructor : ConstructorId := ⟨dataType, 1⟩
def type : Ty := .namedData dataType
def actualDefinitions : DataEnvironment :=
  [{ constructorPayloadTypes := [.unit, .product (.product .word .word) type] }]

def empty : Expr := .construct nilConstructor .unit
def cons (key value tail : Expr) : Expr :=
  .construct consConstructor (.pair (.pair key value) tail)

def encode : Entries → Value
  | [] => .constructed nilConstructor .unit
  | (key, value) :: rest =>
      .constructed consConstructor (.pair (.pair (.word key) (.word value)) (encode rest))

def literal : Entries → Expr
  | [] => empty
  | (key, value) :: rest => cons (.word key) (.word value) (literal rest)

def lookupEntries (key : Word) : Entries → Word
  | [] => Word.zero
  | (storedKey, value) :: rest => if key == storedKey then value else lookupEntries key rest

def insertEntries (key value : Word) : Entries → Entries
  | [] => [(key, value)]
  | (storedKey, storedValue) :: rest =>
      if key == storedKey then (key, value) :: rest
      else (storedKey, storedValue) :: insertEntries key value rest

def lookupParameter : Ty := .product type .word
def insertParameter : Ty := .product type (.product .word .word)
def helperType (parameter result : Ty) : Ty :=
  .function parameter (LanguageResult.resultType result)

/-- Read the installed self closure, then apply it. The argument is in the
caller's lexical context; the language-result binder shifts it once. -/
def invoke (parameter result : Ty) (reference argument : Expr) : Expr :=
  LanguageResult.bind result
    (OptionalCell.read (helperType parameter result) reference Word.zero)
    (.apply (.var 0) (argument.weakenAt 0))

/-- At entry: argument, self-reference, captured outer values. -/
def lookupBody : Expr :=
  .matchData dataType (LanguageResult.resultType .word) (.first (.var 0))
    [LanguageResult.success (.word Word.zero),
      .ifE (.binary .wordEq (.second (.var 1)) (.first (.first (.var 0))))
        (LanguageResult.success (.second (.first (.var 0))))
        (invoke lookupParameter .word (.var 2)
          (.pair (.second (.var 0)) (.second (.var 1))))]

def insertBody : Expr :=
  .matchData dataType (LanguageResult.resultType type) (.first (.var 0))
    [LanguageResult.success (cons (.first (.second (.var 1)))
        (.second (.second (.var 1))) empty),
      .ifE (.binary .wordEq (.first (.second (.var 1))) (.first (.first (.var 0))))
        (LanguageResult.success (cons (.first (.second (.var 1)))
          (.second (.second (.var 1))) (.second (.var 0))))
        (LanguageResult.bind type
          (invoke insertParameter type (.var 2)
            (.pair (.second (.var 0)) (.second (.var 1))))
          (LanguageResult.success
            (cons (.first (.first (.var 1))) (.second (.first (.var 1))) (.var 0))))]

/-- Evaluate the input before installing a fresh self cell. The installed
closure captures a reference, never a snapshot of the store. -/
def runHelper (parameter result : Ty) (body argument : Expr) : Expr :=
  .letE argument
    (.letE (OptionalCell.allocate (helperType parameter result))
      (.letE (.storeCell (.var 0)
        (.inRight .unit (.lambda parameter (LanguageResult.resultType result) body)))
        (invoke parameter result (.var 1) (.var 2))))

def lookup (mapping key : Expr) : Expr :=
  runHelper lookupParameter .word lookupBody (.pair mapping key)

def insert (mapping key value : Expr) : Expr :=
  runHelper insertParameter type insertBody (.pair mapping (.pair key value))

def closure (parameter result : Ty) (body : Expr) (location : Location)
    (captured : Environment) : Value :=
  .closure parameter (LanguageResult.resultType result) body
    (.cellRef (OptionalCell.cellType (helperType parameter result)) location :: captured)

def Installed (store : Store) (parameter result : Ty) (body : Expr)
    (location : Location) (captured : Environment) : Prop :=
  store.read? location = some (.inRight .unit (closure parameter result body location captured))

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

/-- Exactly one administrative cell is added after argument effects. -/
def installedStore (store : Store) (parameter result : Ty) (body : Expr)
    (input : Value) (environment : Environment) : Store :=
  store ++ [.inRight .unit (closure parameter result body store.length (input :: environment))]

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

/-- The place reference and key are captured before the RHS. The root is read
only after the RHS succeeds, so RHS writes to this same root are retained.
This initialized-root helper leaves source-specific empty-map initialization to
the caller; key and RHS already use the language-result carrier. -/
def assign (reference key rhs : Expr) : Expr :=
  .letE reference
    (LanguageResult.bind .unit (key.weakenAt 0)
      (LanguageResult.bind .unit ((rhs.weakenAt 0).weakenAt 0)
        (LanguageResult.bind .unit (OptionalCell.read type (.var 2) Word.zero)
          (LanguageResult.bind .unit (insert (.var 0) (.var 2) (.var 1))
            (OptionalCell.write (.var 4) (.var 0))))))

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

def assignInsertStore (store : Store) (entries : Entries) (key value : Word)
    (location : Location) (environment : Environment) : Store :=
  installedStore store insertParameter type insertBody
    (.pair (encode entries) (.pair (.word key) (.word value)))
    (encode entries :: .word value :: .word key ::
      .cellRef (OptionalCell.cellType type) location :: environment)

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
