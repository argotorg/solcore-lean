import Solcore.Frontend.RustHull.AccountState
import Solcore.Frontend.RustHull.Ambient

/-! Typing of the host values used by the public account runtime initializer.
The data environment contains both byte/word mappings and account records.
These results accept arbitrary supplied values; normalization and catalog
selection do not require extra typing premises from the caller. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.ContextTyping

theorem wordMappingLiteral_hasType (entries : Core.WordMapping.Entries) (context : Core.Context) :
    Core.HasType context (Core.WordMapping.literal entries) Core.WordMapping.type
      AccountState.definitions := by
  induction entries with
  | nil => exact .construct rfl .unit
  | cons entry rest ih => exact .construct rfl (.pair (.pair .word .word) ih)

theorem optionalWordLiteral_hasType (value : Option Core.Word) (context : Core.Context) :
    Core.HasType context
      (match value with
        | none => .inLeft .word .unit
        | some value => .inRight .unit (.word value))
      Ambient.optionalWord AccountState.definitions := by
  cases value with
  | none => exact .inLeft .word .unit
  | some value => exact .inRight .unit .word

theorem optionalMappingLiteral_hasType (value : Option Core.WordMapping.Entries)
    (context : Core.Context) :
    Core.HasType context
      (match value with
        | none => .inLeft Core.WordMapping.type .unit
        | some entries => .inRight .unit (Core.WordMapping.literal entries))
      Ambient.optionalHashes AccountState.definitions := by
  cases value with
  | none => exact .inLeft (.namedData rfl) .unit
  | some entries => exact .inRight .unit (wordMappingLiteral_hasType entries context)

theorem accountRecordLiteral_hasType (account : AccountState.Account) (identity : Nat)
    (context : Core.Context) :
    Core.HasType context (AccountState.recordLiteral account identity) AccountState.recordType
      AccountState.definitions := by
  simp only [AccountState.recordLiteral, AccountState.recordType, AccountState.fieldTypes,
    bundle, bundleType]
  repeat first
    | exact wordMappingLiteral_hasType _ _
    | exact Core.HasType.word
    | exact Core.HasType.bool
    | apply Core.HasType.pair

theorem accountStateLiteral_hasType (accounts : List (AccountState.Account × Nat))
    (context : Core.Context) :
    Core.HasType context (AccountState.literal accounts) AccountState.type
      AccountState.definitions := by
  induction accounts with
  | nil => exact .construct rfl .unit
  | cons entry rest ih =>
      exact .construct rfl (.pair (.pair .word (accountRecordLiteral_hasType entry.1 entry.2 context)) ih)

theorem ambientContextExpression_hasType (value : Ambient.Context) (context : Core.Context) :
    Core.HasType context (Ambient.contextExpression value) Ambient.contextType
      AccountState.definitions := by
  simp only [Ambient.contextExpression, Ambient.contextType, Ambient.slots,
    List.map, bundle, bundleType]
  repeat first
    | exact optionalWordLiteral_hasType _ _
    | exact optionalMappingLiteral_hasType _ _
    | apply Core.HasType.pair

end Solcore.Frontend.RustHull.ContextTyping
