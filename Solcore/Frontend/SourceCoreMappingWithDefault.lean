import Solcore.Core.OrderedMapping

/-! Ordinary Core transport for source mapping metadata and its raw-type
default. This compatibility carrier retains metadata separately from entries.
The host authenticates metadata IDs and supplies the default before execution;
Core selects that value without interpreting source types at runtime.

This library does not yet change the public compiler or its strict data codec.
The missing-default token base and metadata registry are owned by its caller. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreMappingWithDefault
open Core

def type (layout : OrderedMapping.Layout) : Ty :=
  .product .word (.product layout.lookupResult layout.type)

def pack (metadata defaultValue entries : Expr) : Expr :=
  .pair metadata (.pair defaultValue entries)

def value (metadata : Word) (defaultValue : Option Value) (layout : OrderedMapping.Layout)
    (entries : OrderedMapping.Entries) : Value :=
  .pair (.word metadata) (.pair (OrderedMapping.optionValue layout.valueType defaultValue)
    (OrderedMapping.encode layout entries))

def metadata (mapping : Expr) : Expr := .first mapping
def defaultValue (mapping : Expr) : Expr := .first (.second mapping)
def entries (mapping : Expr) : Expr := .second (.second mapping)

theorem type_wellFormed {definitions : DataEnvironment} {layout : OrderedMapping.Layout}
    (registered : layout.Registered definitions) : Ty.WellFormed definitions (type layout) :=
  .product .word (.product registered.lookupWellFormed registered.typeWellFormed)

theorem pack_hasType {definitions : DataEnvironment} {layout : OrderedMapping.Layout}
    {context : Core.Context} {header fallback stored : Expr}
    (headerTyped : HasType context header .word definitions)
    (fallbackTyped : HasType context fallback layout.lookupResult definitions)
    (storedTyped : HasType context stored layout.type definitions) :
    HasType context (pack header fallback stored) (type layout) definitions :=
  .pair headerTyped (.pair fallbackTyped storedTyped)

/-- The key's stored value takes precedence. The transported fallback is
observed only for absence; a missing fallback observes the supplied reason. -/
def select (result : Ty) (missingReason fallback found : Expr) : Expr :=
  .caseE found
    (.caseE (fallback.weakenAt 0)
      (LanguageResult.failure result ((missingReason.weakenAt 0).weakenAt 0))
      (LanguageResult.success (.var 0)))
    (LanguageResult.success (.var 0))

theorem select_hasType {definitions : DataEnvironment} {context : Core.Context}
    {result : Ty} {missingReason fallback found : Expr}
    (resultWF : Ty.WellFormed definitions result)
    (reasonTyped : HasType context missingReason .word definitions)
    (fallbackTyped : HasType context fallback (.sum .unit result) definitions)
    (foundTyped : HasType context found (.sum .unit result) definitions) :
    HasType context (select result missingReason fallback found) (LanguageResult.resultType result) definitions := by
  apply HasType.caseE foundTyped
  · apply HasType.caseE
      (by simpa [Context.insertAt] using fallbackTyped.weakenAt (inserted := .unit) 0)
    · apply LanguageResult.failure_hasType resultWF
      simpa [Context.insertAt] using
        (reasonTyped.weakenAt (inserted := .unit) 0).weakenAt (inserted := .unit) 0
    · exact .inRight .word (.var rfl)
  · exact .inRight .word (.var rfl)

theorem select_found {environment : Environment} {before after : Store}
    {result : Ty} {reason fallback found : Expr} {payload : Value}
    (evaluated : Evaluates environment before found (.inRight .unit payload) after) :
    Evaluates environment before (select result reason fallback found)
      (.inRight .word payload) after :=
  .caseRight evaluated (.inRight (.var rfl))

theorem select_default {environment : Environment} {before middle after : Store}
    {result : Ty} {reason fallback found : Expr} {payload : Value}
    (absent : Evaluates environment before found (.inLeft result .unit) middle)
    (transported : Evaluates (.unit :: environment) middle (fallback.weakenAt 0)
      (.inRight .unit payload) after) :
    Evaluates environment before (select result reason fallback found)
      (.inRight .word payload) after :=
  .caseLeft absent (.caseRight transported (.inRight (.var rfl)))

theorem select_missing {environment : Environment} {before middle selected after : Store}
    {result : Ty} {reason fallback found : Expr} {token : Word}
    (absent : Evaluates environment before found (.inLeft result .unit) middle)
    (missing : Evaluates (.unit :: environment) middle (fallback.weakenAt 0)
      (.inLeft result .unit) selected)
    (reported : Evaluates (.unit :: .unit :: environment) selected
      ((reason.weakenAt 0).weakenAt 0) (.word token) after) :
    Evaluates environment before (select result reason fallback found)
      (.inLeft result (.word token)) after :=
  .caseLeft absent (.caseLeft missing (.inLeft reported))

/-- Evaluate the mapping once, then key and comparison. Ordinary lookup
returns absence; this wrapper selects the authenticated transported default. -/
def lookup (layout : OrderedMapping.Layout) (missingBase : Word)
    (keyEqual mapping key : Expr) : Expr :=
  .letE mapping
    (LanguageResult.bind layout.valueType
      (OrderedMapping.lookup layout (keyEqual.weakenAt 0) (entries (.var 0)) (key.weakenAt 0))
      (select layout.valueType (.binary .wordAdd (.word missingBase) (metadata (.var 1)))
        (defaultValue (.var 1)) (.var 0)))

/-- Replacement and insertion preserve both raw metadata and the fallback,
including the fallback's nested source metadata and function captures. -/
def insert (layout : OrderedMapping.Layout) (keyEqual mapping key replacement : Expr) : Expr :=
  .letE mapping
    (LanguageResult.bind (type layout)
      (OrderedMapping.insert layout (keyEqual.weakenAt 0) (entries (.var 0))
        (key.weakenAt 0) (replacement.weakenAt 0))
      (LanguageResult.success (pack (metadata (.var 1)) (defaultValue (.var 1)) (.var 0))))

def selectedValue (result : Ty) (missingBase header : Word)
    (fallback found : Option Value) : Value :=
  match found.or fallback with
  | some payload => .inRight .word payload
  | none => .inLeft result (.word (missingBase.add header))

private theorem select_transported (layout : OrderedMapping.Layout) (missingBase header : Word)
    (fallback found : Option Value) (stored : Value) (environment : Environment) (store : Store) :
    Evaluates (OrderedMapping.optionValue layout.valueType found ::
      .pair (.word header) (.pair (OrderedMapping.optionValue layout.valueType fallback) stored) :: environment)
      store (select layout.valueType (.binary .wordAdd (.word missingBase) (metadata (.var 1)))
        (defaultValue (.var 1)) (.var 0))
      (selectedValue layout.valueType missingBase header fallback found) store := by
  cases found with
  | some payload => exact select_found (.var rfl)
  | none =>
    cases fallback with
    | some payload =>
      apply select_default (.var rfl)
      simpa [defaultValue, Expr.weakenAt] using
        (Evaluates.first (Evaluates.second (Evaluates.var (index := 2) (by rfl))))
    | none =>
      apply select_missing (.var rfl)
      · simpa [defaultValue, Expr.weakenAt] using
          (Evaluates.first (Evaluates.second (Evaluates.var (index := 2) (by rfl))))
      · simpa [metadata, Expr.weakenAt] using
          (Evaluates.binary (op := .wordAdd) Evaluates.word
            (Evaluates.first (Evaluates.var (index := 3) (by rfl))) (by rfl))

/-- A completed real helper lookup is decoded using this mapping's own
fallback, while retaining every store change made by the helper and children. -/
theorem lookup_completed {layout : OrderedMapping.Layout} {missingBase header : Word}
    {fallback found : Option Value} {stored : Value} {environment : Environment}
    {before middle after : Store} {keyEqual mapping key : Expr}
    (mappingEvaluation : Evaluates environment before mapping
      (.pair (.word header) (.pair (OrderedMapping.optionValue layout.valueType fallback) stored)) middle)
    (lookupEvaluation : Evaluates
      (.pair (.word header) (.pair (OrderedMapping.optionValue layout.valueType fallback) stored) :: environment)
      middle (OrderedMapping.lookup layout (keyEqual.weakenAt 0) (entries (.var 0)) (key.weakenAt 0))
      (.inRight .word (OrderedMapping.optionValue layout.valueType found)) after) :
    Evaluates environment before (lookup layout missingBase keyEqual mapping key)
      (selectedValue layout.valueType missingBase header fallback found) after :=
  .letE mappingEvaluation (LanguageResult.bind_success layout.valueType lookupEvaluation
    (select_transported layout missingBase header fallback found stored environment after))

/-- A completed real insertion changes only the entry sequence in the
carrier. Header/default values and any captured references remain identical. -/
theorem insert_completed {layout : OrderedMapping.Layout} {header : Word}
    {fallback : Option Value} {stored updated : Value} {environment : Environment}
    {before middle after : Store} {keyEqual mapping key replacement : Expr}
    (mappingEvaluation : Evaluates environment before mapping
      (.pair (.word header) (.pair (OrderedMapping.optionValue layout.valueType fallback) stored)) middle)
    (insertEvaluation : Evaluates
      (.pair (.word header) (.pair (OrderedMapping.optionValue layout.valueType fallback) stored) :: environment)
      middle (OrderedMapping.insert layout (keyEqual.weakenAt 0) (entries (.var 0))
        (key.weakenAt 0) (replacement.weakenAt 0)) (.inRight .word updated) after) :
    Evaluates environment before (insert layout keyEqual mapping key replacement)
      (.inRight .word (.pair (.word header)
        (.pair (OrderedMapping.optionValue layout.valueType fallback) updated))) after :=
  .letE mappingEvaluation (LanguageResult.bind_success (type layout) insertEvaluation
    (.inRight (.pair (.first (.var rfl)) (.pair (.first (.second (.var rfl))) (.var rfl)))))

theorem lookup_hasType {definitions : DataEnvironment} {layout : OrderedMapping.Layout}
    {context : Core.Context} {keyEqual mapping key : Expr} (missingBase : Word)
    (registered : layout.Registered definitions)
    (comparisonTyped : HasType context keyEqual layout.comparisonType definitions)
    (mappingTyped : HasType context mapping (type layout) definitions)
    (keyTyped : HasType context key layout.keyType definitions) :
    HasType context (lookup layout missingBase keyEqual mapping key)
      (LanguageResult.resultType layout.valueType) definitions := by
  apply HasType.letE mappingTyped
  apply LanguageResult.bind_hasType registered.valueWellFormed
  · apply OrderedMapping.lookup_hasType registered
    · simpa [Context.insertAt] using comparisonTyped.weakenAt (inserted := type layout) 0
    · exact .second (.second (.var rfl))
    · simpa [Context.insertAt] using keyTyped.weakenAt (inserted := type layout) 0
  · exact select_hasType registered.valueWellFormed
      (.binary .word (.first (.var rfl))) (.first (.second (.var rfl))) (.var rfl)

theorem insert_hasType {definitions : DataEnvironment} {layout : OrderedMapping.Layout}
    {context : Core.Context} {keyEqual mapping key replacement : Expr}
    (registered : layout.Registered definitions)
    (comparisonTyped : HasType context keyEqual layout.comparisonType definitions)
    (mappingTyped : HasType context mapping (type layout) definitions)
    (keyTyped : HasType context key layout.keyType definitions)
    (replacementTyped : HasType context replacement layout.valueType definitions) :
    HasType context (insert layout keyEqual mapping key replacement)
      (LanguageResult.resultType (type layout)) definitions := by
  apply HasType.letE mappingTyped
  apply LanguageResult.bind_hasType (type_wellFormed registered)
  · apply OrderedMapping.insert_hasType registered
    · simpa [Context.insertAt] using comparisonTyped.weakenAt (inserted := type layout) 0
    · exact .second (.second (.var rfl))
    · simpa [Context.insertAt] using keyTyped.weakenAt (inserted := type layout) 0
    · simpa [Context.insertAt] using replacementTyped.weakenAt (inserted := type layout) 0
  · exact .inRight .word (pack_hasType (.first (.var rfl)) (.first (.second (.var rfl))) (.var rfl))

end Solcore.Frontend.SourceCoreMappingWithDefault
