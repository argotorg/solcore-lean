import Solcore.Core.Conventions

/-!
# Mappings

Mappings encoded in ordinary Core. `WordMapping` is the fixed-catalog `mapping(Word => Word)` and
`OrderedMapping` the ordered mapping with a registered catalog layout. These are the definitions;
their laws are in `Internal/MappingLaws`.
-/

section
-- leanmerge: from Solcore.Core.Internal.WordMappingDefs
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

/-- Exactly one administrative cell is added after argument effects. -/
def installedStore (store : Store) (parameter result : Ty) (body : Expr)
    (input : Value) (environment : Environment) : Store :=
  store ++ [.inRight .unit (closure parameter result body store.length (input :: environment))]

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

def assignInsertStore (store : Store) (entries : Entries) (key value : Word)
    (location : Location) (environment : Environment) : Store :=
  installedStore store insertParameter type insertBody
    (.pair (encode entries) (.pair (.word key) (.word value)))
    (encode entries :: .word value :: .word key ::
      .cellRef (OptionalCell.cellType type) location :: environment)

end Solcore.Core.WordMapping
end

section
-- leanmerge: from Solcore.Core.Internal.OrderedMappingDefs
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

def assignInsertStore (layout : Layout) (store : Store) (entries : Entries)
    (key value comparator : Value) (location : Location) (environment : Environment) : Store :=
  installedStore store layout.insertParameter layout.type (insertBody layout)
    (.pair (encode layout entries) (.pair (.pair key value) comparator))
    (encode layout entries :: comparator :: value :: key ::
      .cellRef (OptionalCell.cellType layout.type) location :: environment)

end Solcore.Core.OrderedMapping
end
