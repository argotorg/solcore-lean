import Solcore.Frontend.RustHull.LoweringSupport
import Solcore.Frontend.RustHull.Memory
import Solcore.Core.Internal.MappingLaws
import Solcore.Frontend.RustHull.Precompiles

/-!
# EVM effects on Core

Account records, ambient observations, calls, creation and the builtin effect compiler. Main
declarations: `AccountState.Account`, `Effects`, `Calls`, `Creation`, `Ambient`, `CreationRuntime`,
`AccountInspection`, `AccountLifecycle`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountState
/-! Account records stored in an ordinary Core ordered mapping. The world cell
is copied at a message boundary so rollback restores all account observations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountState
open Core CodeBuilder

def fieldTypes : List Core.Ty :=
  [WordMapping.type, WordMapping.type, .word, .word, WordMapping.type, .word, .bool, .bool, .bool]
def recordType : Core.Ty := bundleType fieldTypes
def layout : OrderedMapping.Layout := ⟨.word, recordType, ⟨1⟩⟩
def type : Core.Ty := layout.type
def definitions : DataEnvironment := Memory.definitions ++ [layout.definition]
def empty : Core.Expr := OrderedMapping.empty layout
def field (index : Nat) (record : Core.Expr) : Core.Expr := projectArgument index 9 record
def defaultRecord : Core.Expr := bundle [WordMapping.empty, WordMapping.empty,
  .word Word.zero, .word Word.zero, WordMapping.empty, .word Word.zero,
  .bool true, .bool false, .bool false]
def equal : Core.Expr := .lambda (.product .word .word) .bool
  (.binary .wordEq (.first (.var 0)) (.second (.var 0)))

structure Account where
  address : Word
  storage : WordMapping.Entries := []
  transient : WordMapping.Entries := []
  nonce : Word := Word.zero
  code : Option (List UInt8) := some []
  created : Bool := false
  destroyed : Bool := false
  deriving Repr

/-- The compiler assigns executable code identities from exact supplied images. -/
def recordLiteral (account : Account) (codeIdentity : Nat := 0) : Core.Expr :=
  bundle [WordMapping.literal account.storage, WordMapping.literal account.transient,
    .word account.nonce, .word (Word.ofNatModulo codeIdentity),
    WordMapping.literal (Memory.packBytes (account.code.getD [])),
    .word (Word.ofNatModulo (account.code.getD []).length),
    .bool account.code.isSome, .bool account.created, .bool account.destroyed]

def literal (accounts : List (Account × Nat)) : Core.Expr :=
  accounts.foldr (fun (account, identity) tail => OrderedMapping.cons layout
    (.word (Word.ofNatModulo (account.address.val % 2 ^ 160))) (recordLiteral account identity) tail) empty

def lookup (world address : Core.Expr) : Core.Expr :=
  OrderedMapping.lookup layout equal world address

def put (world address account : Core.Expr) : Core.Expr :=
  OrderedMapping.insert layout equal world address account

/-- An omitted account is known empty only in an explicitly complete world. -/
def get (world address complete : Core.Expr) : Core.Expr :=
  .letE (bundle [world, address, complete])
    (LanguageResult.bind recordType
      (lookup (projectArgument 0 3 (.var 0)) (projectArgument 1 3 (.var 0)))
      (.caseE (.var 0)
        (.ifE (projectArgument 2 3 (.var 2))
          (LanguageResult.success defaultRecord)
          (LanguageResult.failure recordType (.word (Word.ofNatModulo 7))))
        (LanguageResult.success (.var 0))))

def replace (record : Core.Expr) (index : Nat) (value : Core.Expr) : Core.Expr :=
  bundle ((List.range 9).map fun item => if item == index then value else field item record)

/-- Read-modify-write one account field without retaining a stale world value. -/
def writeField (worldReference address complete : Core.Expr) (index : Nat) (value : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [worldReference, address, complete, value])) fun args =>
    let world := part 0 4 args
    let address := part 1 4 args
    bindResult .unit (fun d => get (load world d) (address d) (part 2 4 args d)) fun record =>
    bindResult .unit (fun d => put (load world d) (address d)
      (replace (record d) index (part 3 4 args d))) fun next =>
    success (store world next)) 0

def readStorage (worldReference address complete key : Core.Expr) (transient : Bool := false) : Core.Expr :=
  (bind (constant (bundle [worldReference, address, complete, key])) fun args =>
    bindResult .word (fun d => get (load (part 0 4 args) d) (part 1 4 args d) (part 2 4 args d)) fun record =>
    CodeBuilder.lookup (part (if transient then 1 else 0) 9 record) (part 3 4 args)) 0

def writeStorage (worldReference address complete key value : Core.Expr) (transient : Bool := false) : Core.Expr :=
  (bind (constant (bundle [worldReference, address, complete, key, value])) fun args =>
    let world := part 0 5 args
    let address := part 1 5 args
    let index := if transient then 1 else 0
    bindResult .unit (fun d => get (load world d) (address d) (part 2 5 args d)) fun record =>
    bindResult .unit (insert (part index 9 record) (part 3 5 args) (part 4 5 args)) fun updated =>
    bindResult .unit (fun d => put (load world d) (address d) (replace (record d) index (updated d))) fun next =>
    success (store world next)) 0

/-- Finalization preserves persistent fields while resetting transaction-local
state. Account removal is decided separately by both lifecycle flags. -/
def clearTransaction (record : Core.Expr) : Core.Expr :=
  bundle ((List.range 9).map fun index =>
    if index == 1 then WordMapping.empty
    else if index == 7 || index == 8 then .bool false
    else field index record)

def finalizeParameter : Core.Ty := .product type (.cell WordMapping.type)

def finalizeBody : Core.Expr :=
  .matchData layout.dataType (LanguageResult.resultType type) (.first (.var 0))
    [LanguageResult.success empty,
      (bind (constant (bundle [.var 0, .var 1, .var 2])) fun args =>
        let entry := part 0 3 args
        let key := part 0 2 (part 0 2 entry)
        let record := part 1 2 (part 0 2 entry)
        let tail := part 1 2 entry
        let balances := part 1 2 (part 1 3 args)
        let recurse : Code := fun depth =>
          OrderedMapping.invoke finalizeParameter type (part 2 3 args depth)
            (.pair (tail depth) (balances depth))
        let remove := bindResult type (insert (load balances) key (number 0)) fun updated =>
          bind (store balances updated) fun _ => recurse
        let retain := bindResult type recurse fun next =>
          success (fun depth => OrderedMapping.cons layout (key depth)
            (clearTransaction (record depth)) (next depth))
        choose (part 7 9 record) (choose (part 8 9 record) remove retain) retain) 0]

/-- Finish a successful top-level transaction, entirely on Core. Accounts
created and destroyed in this transaction disappear and any subsequent credit
to them is burned. Existing accounts retain their persistent state and balance.
This must not run at a nested message boundary. Both references evaluate once. -/
def finalize (worldReference balancesReference : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [worldReference, balancesReference])) fun args =>
    let world := part 0 2 args
    bindResult .unit (fun depth => OrderedMapping.runHelper finalizeParameter type finalizeBody
      (.pair (load world depth) (part 1 2 args depth))) fun next =>
    success (store world next)) 0

private def mappingEntries : Core.Value → Except String WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor = WordMapping.nilConstructor then pure []
      else .error "invalid account word mapping nil constructor"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor = WordMapping.consConstructor do
        throw "invalid account word mapping cons constructor"
      pure ((key, value) :: (← mappingEntries tail))
  | _ => .error "invalid account word mapping value"

/-- Index packed code once. As in Core mapping lookup, the first occurrence
of a repeated key wins, absent words are zero, and bytes past size are ignored. -/
private def codeBytes (entries : WordMapping.Entries) (size : Nat) : List UInt8 := Id.run do
  let mut words : Array (Option Word) := Array.replicate ((size + 31) / 32) none
  for (key, value) in entries do
    if key.val < words.size && words[key.val]!.isNone then
      words := words.set! key.val (some value)
  return (List.range size).map fun offset => UInt8.ofNat
    (Word.byteAt (Word.ofNatModulo (offset % 32)) (words[offset / 32]!.getD Word.zero)).val

private def decodeRecord (address : Word) (value : Core.Value) (maxCodeBytes : Nat) :
    Except String Account := do
  let .pair storage (.pair transient (.pair (.word nonce) (.pair (.word _codeIdentity)
    (.pair code (.pair (.word size) (.pair (.bool known) (.pair (.bool created) (.bool destroyed)))))))) := value
    | throw "invalid account record"
  unless size.val ≤ maxCodeBytes do throw "account code exceeds the configured export limit"
  let storage ← mappingEntries storage
  let transient ← mappingEntries transient
  let code ← mappingEntries code
  pure {
    address := address
    storage := storage
    transient := transient
    nonce := nonce
    code := if known then some (codeBytes code size.val) else none
    created := created
    destroyed := destroyed
  }

/-- Decode the ordered world snapshot without trusting executable identities.
The host resolves code from the exact exported bytes when the next transaction
is compiled. `maxCodeBytes` bounds each account image, including unknown images.
Entry order and first-match semantics of the Core mapping are preserved. -/
def decode (value : Core.Value) (maxCodeBytes : Nat := 1048576) : Except String (List Account) :=
  let rec accounts : Core.Value → Except String (List Account)
    | .constructed constructor .unit =>
        if constructor = layout.nilConstructor then pure []
        else .error "invalid account mapping nil constructor"
    | .constructed constructor (.pair (.pair (.word address) record) tail) => do
        unless constructor = layout.consConstructor do throw "invalid account mapping cons constructor"
        pure ((← decodeRecord address record maxCodeBytes) :: (← accounts tail))
    | _ => .error "invalid account mapping value"
  accounts value

end Solcore.Frontend.RustHull.AccountState
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountInspection
/-! External code observations run on the Core account catalog. Pending
SELFDESTRUCT does not hide code: deletion belongs to transaction finalization.
An incomplete world or an account without supplied code fails explicitly. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountInspection
open Core CodeBuilder

def definitions : DataEnvironment := AccountState.definitions
def unknownCodeReason : Word := Word.ofNatModulo 15

def known (resultType : Core.Ty) (record : Code) (body : Code) : Code :=
  choose (part 6 9 record) body (failure resultType (constant (.word unknownCodeReason)))

/-- EXTCODESIZE evaluates its input expressions once and normalizes the target. -/
def size (worldReference complete target : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [worldReference, complete, target])) fun args =>
    bindResult .word (fun depth => AccountState.get (load (part 0 3 args) depth)
      (address (part 2 3 args) depth) (part 1 3 args depth)) fun record =>
    known .word record (success (part 5 9 record))) 0

/-- EXTCODECOPY uses a fixed packed code image. Only destination memory expands;
missing source bytes are zero and an oversized source offset cannot wrap. -/
def copy (worldReference complete memoryReference sizeReference target destination source length : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [worldReference, complete, memoryReference, sizeReference,
      target, destination, source, length])) fun args =>
    bindResult .unit (fun depth => AccountState.get (load (part 0 8 args) depth)
      (address (part 4 8 args) depth) (part 1 8 args depth)) fun record =>
    known .unit record (fun depth => Memory.copyPackedFrom
      (part 2 8 args depth) (part 3 8 args depth) (part 5 8 args depth)
      (part 4 9 record depth) (part 6 8 args depth) (part 7 8 args depth))) 0

/-- EXTCODEHASH returns zero exactly for an EIP-161 empty account. Accounts with
positive nonce or balance and no code return Keccak(empty). Code hashing itself
is ordinary Core execution and does not expand the caller's memory. -/
def hash (worldReference complete balancesReference target : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [worldReference, complete, balancesReference, target])) fun args =>
    bind (address (part 3 4 args)) fun target =>
    bindResult .word (fun depth => AccountState.get (load (part 0 4 args) depth)
      (target depth) (part 1 4 args depth)) fun record =>
    known .word record <|
      bindResult .word (lookup (load (part 2 4 args)) target) fun balance =>
      let emptyAccount := choose (binary .wordEq (part 2 9 record) (number 0))
        (choose (binary .wordEq (part 5 9 record) (number 0))
          (binary .wordEq balance (number 0)) (boolean false)) (boolean false)
      choose emptyAccount (success (number 0)) <|
        bind (allocate WordMapping.type (part 4 9 record)) fun memory =>
        bind (allocate .word (number 0)) fun memorySize =>
        fun depth => Keccak.hash (memory depth) (memorySize depth)
          (number 0 depth) (part 5 9 record depth)) 0

def supports (name : String) : Bool := name ∈ ["extcodesize", "extcodecopy", "extcodehash"]

def reference (scope : Scope) (name : String) (type : Core.Ty) : LowerM Core.Expr := do
  let (binding, index) ← scope.lookup ("$lean$evm$" ++ name)
  expectType type binding.type
  pure (.var index)

/-- Slot adapter independent of Effects, so the effect dispatcher can import
this module without a dependency cycle. Arguments are already evaluated words. -/
def lowerBuiltin (scope : Scope) (name : String) (arguments : List Core.Expr) : LowerM Lowered := do
  let world ← reference scope "world" AccountState.type
  let complete := Core.Expr.loadCell (← reference scope "worldComplete" .bool)
  match name, arguments with
  | "extcodesize", [target] => pure ⟨.word, size world complete target⟩
  | "extcodecopy", [target, destination, source, length] => pure ⟨.unit, copy world complete
      (← reference scope "memory" WordMapping.type) (← reference scope "memorySize" .word)
      target destination source length⟩
  | "extcodehash", [target] => pure ⟨.word, hash world complete
      (← reference scope "balances" WordMapping.type) target⟩
  | _, _ => fail s!"unsupported account inspection or incorrect arity: {name}"

end Solcore.Frontend.RustHull.AccountInspection
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountLifecycle
/-! SELFDESTRUCT account updates for the Osaka/EIP-6780 model. Account removal
belongs to transaction finalization. Code, nonce and storage remain observable
after a child frame schedules an account for removal. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountLifecycle
open Core CodeBuilder

def definitions : DataEnvironment := AccountState.definitions
def balanceOverflowReason : Word := Word.ofNatModulo 12

private def publish (world balances current record nextBalances : Code) : Code :=
  choose (part 7 9 record)
    (bindResult .unit (fun depth => AccountState.put (load world depth) (current depth)
      (AccountState.replace (record depth) 8 (.bool true))) fun nextWorld =>
      bind (store balances nextBalances) fun _ => success (store world nextWorld))
    (success (store balances nextBalances))

/-- Transfer the complete balance, or burn it for a newly created account
whose beneficiary is itself. Existing accounts retain their balance for that
self-beneficiary case. Only accounts created in this transaction acquire the
pending-removal flag. The complete-world flag is used only for the current
record; beneficiary balances come from the explicit ledger with zero on miss.
All checked updates precede the two externally visible cell stores. -/
def destroy (worldReference balancesReference currentAddress beneficiary complete : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [worldReference, balancesReference, currentAddress, beneficiary, complete])) fun args =>
    let world := part 0 5 args
    let balances := part 1 5 args
    bind (address (part 2 5 args)) fun current =>
    bind (address (part 3 5 args)) fun recipient =>
    bindResult .unit (fun depth => AccountState.get (load world depth) (current depth)
      (part 4 5 args depth)) fun record =>
    let finish := publish world balances current record
    bindResult .unit (lookup (load balances) current) fun amount =>
    choose (binary .wordEq current recipient)
      (choose (part 7 9 record)
        (choose (binary .wordEq amount (number 0)) (finish (load balances))
          (bindResult .unit (insert (load balances) current (number 0)) finish))
        (success unit))
      (choose (binary .wordEq amount (number 0)) (finish (load balances))
        (bindResult .unit (lookup (load balances) recipient) fun recipientBalance =>
          choose (binary .wordGt recipientBalance (binary .wordSub (number (wordModulus - 1)) amount))
            (failure .unit (constant (.word balanceOverflowReason)))
            (bindResult .unit (insert (load balances) current (number 0)) fun debited =>
              bindResult .unit (insert debited recipient (binary .wordAdd recipientBalance amount)) finish)))) 0

end Solcore.Frontend.RustHull.AccountLifecycle
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Ambient
/-! Explicit transaction and block observations for imported Hull. All reads
execute on Core cells. An omitted observation remains distinguishable from a
supplied zero value or an empty hash model. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Ambient
open Core

structure Context where
  origin : Option Word := none
  gasprice : Option Word := none
  coinbase : Option Word := none
  timestamp : Option Word := none
  number : Option Word := none
  prevrandao : Option Word := none
  gaslimit : Option Word := none
  chainid : Option Word := none
  basefee : Option Word := none
  blobbasefee : Option Word := none
  /-- Block number to hash; missing entries in a supplied model have hash zero. -/
  blockHashes : Option WordMapping.Entries := none
  /-- Versioned transaction blob hashes in their original index order. -/
  blobHashes : Option (List Word) := none
  deriving Repr

def unavailableReason : Word := Word.ofNatModulo 14
def optionalWord : Core.Ty := .sum .unit .word
def optionalHashes : Core.Ty := .sum .unit WordMapping.type

def slots : List (String × Core.Ty) :=
  [("origin", optionalWord), ("gasprice", optionalWord),
   ("coinbase", optionalWord), ("timestamp", optionalWord),
   ("number", optionalWord), ("prevrandao", optionalWord),
   ("gaslimit", optionalWord), ("chainid", optionalWord),
   ("basefee", optionalWord), ("blobbasefee", optionalWord),
   ("blockHashes", optionalHashes), ("blobHashes", optionalHashes)]

def contextType : Core.Ty := bundleType (slots.map Prod.snd)

def wordLiteral : Option Word → Core.Expr
  | none => .inLeft .word .unit
  | some value => .inRight .unit (.word value)

def hashesLiteral : Option WordMapping.Entries → Core.Expr
  | none => .inLeft WordMapping.type .unit
  | some entries => .inRight .unit (WordMapping.literal entries)

/-- Indices outside the Word address space are omitted, never wrapped back
onto earlier blobs. Every representable index still denotes its original blob. -/
def blobEntries (hashes : List Word) : WordMapping.Entries :=
  hashes.zipIdx.filterMap fun (hash, index) =>
    if index < wordModulus then some (Word.ofNatModulo index, hash) else none

def contextExpression (context : Context) : Core.Expr :=
  bundle [wordLiteral context.origin, wordLiteral context.gasprice,
    wordLiteral context.coinbase, wordLiteral context.timestamp,
    wordLiteral context.number, wordLiteral context.prevrandao,
    wordLiteral context.gaslimit, wordLiteral context.chainid,
    wordLiteral context.basefee, wordLiteral context.blobbasefee,
    hashesLiteral context.blockHashes, hashesLiteral (context.blobHashes.map blobEntries)]

/-- The caller allocates each slot as a direct Core cell containing this value. -/
def initialValue (index : Nat) (context : Core.Expr) : Core.Expr :=
  projectArgument index slots.length context

def supports (name : String) : Bool := name ∈
  ["origin", "gasprice", "coinbase", "timestamp", "number", "prevrandao",
   "gaslimit", "chainid", "basefee", "blobbasefee", "blockhash", "blobhash"]

def read (scope : Scope) (name : String) (type : Core.Ty) : LowerM Core.Expr := do
  let (binding, index) ← scope.lookup ("$lean$evm$" ++ name)
  expectType type binding.type
  pure (.loadCell (.var index))

abbrev Code := Nat → Core.Expr
def raw (value : Core.Expr) : Code := fun depth => value.rename (· + depth)
def number (value : Nat) : Code := fun _ => .word (Word.ofNatModulo value)
def success (value : Code) : Code := fun depth => LanguageResult.success (value depth)
def binary (operation : BinaryOp) (left right : Code) : Code :=
  fun depth => .binary operation (left depth) (right depth)
def choose (condition yes no : Code) : Code :=
  fun depth => .ifE (condition depth) (yes depth) (no depth)
def bind (value : Code) (body : Code → Code) : Code := fun depth =>
  .letE (value depth) (body (fun here => .var (here - depth - 1)) (depth + 1))
def requireValue (option : Code) (body : Code → Code) : Code := fun depth =>
  .caseE (option depth) (LanguageResult.failure .word (.word unavailableReason))
    (body (fun here => .var (here - depth - 1)) (depth + 1))
def lookup (mapping key : Code) : Code :=
  fun depth => WordMapping.lookup (mapping depth) (key depth)

/-- Arguments have been evaluated by Hull/Yul lowering. The hash operations
also bind their index once, so guarded comparisons cannot repeat its effects.
Both number and hash history must be supplied for a blockhash observation. -/
def lowerBuiltin (scope : Scope) (name : String) (arguments : List Core.Expr) : LowerM Lowered := do
  let expression ← match name, arguments with
    | "blockhash", [index] => do
        let current ← read scope "number" optionalWord
        let hashes ← read scope "blockHashes" optionalHashes
        pure <| (bind (raw index) fun index =>
          requireValue (raw current) fun current =>
          requireValue (raw hashes) fun hashes =>
          choose (binary .wordGt current index)
            (choose (binary .wordGt (binary .wordSub current index) (number 256))
              (success (number 0)) (lookup hashes index))
            (success (number 0))) 0
    | "blobhash", [index] => do
        let hashes ← read scope "blobHashes" optionalHashes
        pure <| (bind (raw index) fun index =>
          requireValue (raw hashes) fun hashes => lookup hashes index) 0
    | "origin", [] | "coinbase", [] => do
        let value ← read scope name optionalWord
        pure <| (requireValue (raw value) fun value =>
          success (binary .wordAnd value (number (2 ^ 160 - 1)))) 0
    | "gasprice", [] | "timestamp", [] | "number", [] | "prevrandao", []
    | "gaslimit", [] | "chainid", [] | "basefee", [] | "blobbasefee", [] => do
        let value ← read scope name optionalWord
        pure <| (requireValue (raw value) success) 0
    | _, _ => fail s!"unsupported ambient operation or wrong arity: {name}"
  pure ⟨.word, expression⟩

end Solcore.Frontend.RustHull.Ambient
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Calls
/-! CALL/STATICCALL frame transport through an ordinary Core closure. Account
dispatch, transfer, shared state checkpoints and static-write restrictions are
the callback's responsibility. Caller memory and return data stay frame-local.
Depth follows the execution specification's zero-based message depth:
https://ethereum.github.io/execution-specs/src/ethereum/forks/cancun/vm/instructions/system.py.html
-/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Calls
open Core

/-- target, caller, value, static flag, child depth, forwarded gas, packed
calldata, calldata size. Addresses are reduced to their low 160 bits. -/
def requestType : Core.Ty := bundleType
  [.word, .word, .word, .bool, .word, .word, WordMapping.type, .word]

/-- Success flag, complete packed return data, return-data size. A reverted
child returns false with its revert bytes. An exceptional child returns false
with empty bytes. Unsupported execution uses the outer language failure. -/
def responseType : Core.Ty := bundleType [.bool, WordMapping.type, .word]
def callbackType : Core.Ty := .function requestType (LanguageResult.resultType responseType)
def callbackReferenceType : Core.Ty := OptionalCell.referenceType callbackType
def unavailableReason : Word := Word.ofNatModulo 7
def depthLimit : Nat := 1024
def requestField (index : Nat) (value : Core.Expr) : Core.Expr := projectArgument index 8 value
def responseField (index : Nat) (value : Core.Expr) : Core.Expr := projectArgument index 3 value
def response (success mapping length : Core.Expr) : Core.Expr := bundle [success, mapping, length]

abbrev Code := Nat → Core.Expr
def number (value : Nat) : Code := fun _ => .word (Word.ofNatModulo value)
def arg : Code := fun depth => .var depth
def part (index : Nat) : Code := fun depth => projectArgument index 15 (arg depth)
def bind (value : Code) (body : Code → Code) : Code := fun depth =>
  .letE (value depth) (body (fun here => .var (here - depth - 1)) (depth + 1))
def bindResult (value : Code) (body : Code → Code) : Code := fun depth =>
  LanguageResult.bind .word (value depth)
    (body (fun here => .var (here - depth - 1)) (depth + 1))
def success (value : Code) : Code := fun depth => LanguageResult.success (value depth)
def binary (op : BinaryOp) (left right : Code) : Code := fun depth =>
  .binary op (left depth) (right depth)
def choose (test yes no : Code) : Code := fun depth => .ifE (test depth) (yes depth) (no depth)
def load (reference : Code) : Code := fun depth => .loadCell (reference depth)
def store (reference value : Code) : Code := fun depth => .storeCell (reference depth) (value depth)
def allocate (type : Core.Ty) (value : Code) : Code := fun depth => .newCell type (value depth)
def empty : Code := fun _ => WordMapping.empty
def copy (memory size destination mapping source length : Code) : Code := fun depth =>
  Memory.copyPackedFrom (memory depth) (size depth) (destination depth)
    (mapping depth) (source depth) (length depth)
def touch (size offset length : Code) : Code := fun depth =>
  Memory.touch (size depth) (offset depth) (length depth)
def memory : Code := part 0
def memorySize : Code := part 1
def returnData : Code := part 2
def returnSize : Code := part 3
def callback : Code := part 4
def caller : Code := part 5
def depth : Code := part 6
def childStatic : Code := part 7
def gas : Code := part 8
def target : Code := part 9
def value : Code := part 10
def inputOffset : Code := part 11
def inputLength : Code := part 12
def outputOffset : Code := part 13
def outputLength : Code := part 14

def finish (result : Code) : Code :=
  let returned : Code := fun depth => responseField 1 (result depth)
  let length : Code := fun depth => responseField 2 (result depth)
  bind (store returnData returned) fun _ =>
  bind (store returnSize length) fun _ =>
  bindResult (copy memory memorySize outputOffset returned (number 0)
    (choose (binary .wordGt length outputLength) outputLength length)) fun _ =>
  success (choose (fun depth => responseField 0 (result depth)) (number 1) (number 0))

def dispatch : Code :=
  bind (load memory) fun snapshot =>
  bind (allocate WordMapping.type empty) fun input =>
  bind (allocate .word (number 0)) fun inputSize =>
  bindResult (copy input inputSize (number 0) snapshot inputOffset inputLength) fun _ =>
  bindResult (fun depth => OptionalCell.read callbackType (callback depth) unavailableReason) fun function =>
  bindResult (fun depth => .apply (function depth) (bundle [
    binary .wordAnd target (number (2 ^ 160 - 1)) depth,
    binary .wordAnd caller (number (2 ^ 160 - 1)) depth,
    value depth, childStatic depth, binary .wordAdd Calls.depth (number 1) depth,
    gas depth, load input depth, inputLength depth])) finish

def callCode : Code :=
  bindResult (touch memorySize inputOffset inputLength) fun _ =>
  bindResult (touch memorySize outputOffset outputLength) fun _ =>
  bind (store returnData empty) fun _ =>
  bind (store returnSize (number 0)) fun _ =>
  choose (binary .wordGt depth (number (depthLimit - 1))) (success (number 0)) dispatch

/-- Evaluate every argument once. Both memory ranges are checked before a call
starts; return data is then cleared even when depth prevents dispatch. Depth
zero is the outer frame: child depth 1024 is permitted and depth 1025 is refused.
The four mutable frame cells must be distinct. The callback receives copied
calldata starting at byte zero, independently of later caller memory writes. -/
def invoke (memoryReference sizeReference returnDataReference returnSizeReference callbackReference
    callerAddress currentDepth staticFlag suppliedGas address transferredValue
    sourceOffset sourceLength destinationOffset destinationLength : Core.Expr) : Core.Expr :=
  .letE (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
    callbackReference, callerAddress, currentDepth, staticFlag, suppliedGas, address,
    transferredValue, sourceOffset, sourceLength, destinationOffset, destinationLength]) (callCode 0)

end Solcore.Frontend.RustHull.Calls
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Creation
/-! Contract address derivation and CREATE frame transport on ordinary Core.
The callback controls account nonce, collision checks, constructor selection,
deployment and rollback. This module preserves init bytes and return data. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Creation
open Core

/-- Creator, value, salt, CREATE2 flag, child depth, forwarded gas, packed init
bytes and init byte length. The creator uses its low 160 bits. -/
def requestType : Core.Ty := bundleType
  [.word, .word, .word, .bool, .word, .word, WordMapping.type, .word]

/-- Created address or zero, complete revert data, and its byte length. The
callback returns empty data on successful creation or exceptional failure. -/
def responseType : Core.Ty := bundleType [.word, WordMapping.type, .word]
def callbackType : Core.Ty := .function requestType (LanguageResult.resultType responseType)
def callbackReferenceType : Core.Ty := OptionalCell.referenceType callbackType
def unavailableReason : Word := Word.ofNatModulo 7
def depthLimit : Nat := 1024
def requestField (index : Nat) (value : Core.Expr) : Core.Expr := projectArgument index 8 value
def responseField (index : Nat) (value : Core.Expr) : Core.Expr := projectArgument index 3 value
def response (address mapping length : Core.Expr) : Core.Expr := bundle [address, mapping, length]

private abbrev Code := Nat → Core.Expr
private def number (value : Nat) : Code := fun _ => .word (Word.ofNatModulo value)
private def part (index count : Nat) : Code := fun depth => projectArgument index count (.var depth)
private def bind (value : Code) (body : Code → Code) : Code := fun depth =>
  .letE (value depth) (body (fun here => .var (here - depth - 1)) (depth + 1))
private def bindResult (value : Code) (body : Code → Code) : Code := fun depth =>
  LanguageResult.bind .word (value depth)
    (body (fun here => .var (here - depth - 1)) (depth + 1))
private def success (value : Code) : Code := fun depth => LanguageResult.success (value depth)
private def binary (operation : BinaryOp) (left right : Code) : Code := fun depth =>
  .binary operation (left depth) (right depth)
private def choose (condition yes no : Code) : Code :=
  fun depth => .ifE (condition depth) (yes depth) (no depth)
private def load (reference : Code) : Code := fun depth => .loadCell (reference depth)
private def store (reference value : Code) : Code :=
  fun depth => .storeCell (reference depth) (value depth)
private def allocate (type : Core.Ty) (value : Code) : Code :=
  fun depth => .newCell type (value depth)
private def empty : Code := fun _ => WordMapping.empty
private def maskedAddress (value : Code) : Code := binary .wordAnd value (number (2 ^ 160 - 1))
private def writeWord (memory size offset value : Code) : Code := fun depth =>
  Memory.mstore (memory depth) (size depth) (offset depth) (value depth)
private def writeByte (memory size offset value : Code) : Code := fun depth =>
  Memory.mstore8 (memory depth) (size depth) (offset depth) (value depth)
private def hash (memory size offset length : Code) : Code := fun depth =>
  Keccak.hash (memory depth) (size depth) (offset depth) (length depth)
private def scratch (body : Code → Code → Code) : Code :=
  bind (allocate WordMapping.type empty) fun memory =>
  bind (allocate .word (number 0)) fun size => body memory size

private def createAddressCode : Code :=
  let creator := part 0 2
  let nonce := part 1 2
  bind (binary .wordSub (number 32)
    (binary .wordDiv (fun depth => .unary .wordClz (nonce depth)) (number 8))) fun byteCount =>
  bind (choose (binary .wordGt nonce (number 127))
    (binary .wordAdd byteCount (number 1)) (number 1)) fun encodedLength =>
  scratch fun memory size =>
  bindResult (writeByte memory size (number 0) (binary .wordAdd (number 213) encodedLength)) fun _ =>
  bindResult (writeByte memory size (number 1) (number 148)) fun _ =>
  bindResult (writeWord memory size (number 2)
    (binary .wordShl (maskedAddress creator) (number 96))) fun _ =>
  let finish := bindResult (hash memory size (number 0)
    (binary .wordAdd (number 22) encodedLength)) fun digest => success (maskedAddress digest)
  choose (binary .wordEq nonce (number 0))
    (bindResult (writeByte memory size (number 22) (number 128)) fun _ => finish)
    (choose (binary .wordGt nonce (number 127))
      (bindResult (writeByte memory size (number 22) (binary .wordAdd (number 128) byteCount)) fun _ =>
        bindResult (writeWord memory size (number 23)
          (binary .wordShl nonce (binary .wordMul
            (binary .wordSub (number 32) byteCount) (number 8)))) fun _ => finish)
      (bindResult (writeByte memory size (number 22) nonce) fun _ => finish))

/-- Exact RLP of the 20-byte address and minimally encoded nonnegative nonce.
The runtime checks its account nonce limit separately before incrementing it. -/
def createAddress (creator nonce : Core.Expr) : Core.Expr :=
  .letE (.pair creator nonce) (createAddressCode 0)

private def create2AddressCode : Code :=
  bindResult (hash (part 0 6) (part 1 6) (part 4 6) (part 5 6)) fun initHash =>
  scratch fun memory size =>
  bindResult (writeByte memory size (number 0) (number 255)) fun _ =>
  bindResult (writeWord memory size (number 1)
    (binary .wordShl (maskedAddress (part 2 6)) (number 96))) fun _ =>
  bindResult (writeWord memory size (number 21) (part 3 6)) fun _ =>
  bindResult (writeWord memory size (number 53) initHash) fun _ =>
  bindResult (hash memory size (number 0) (number 85)) fun digest => success (maskedAddress digest)

/-- Hash the exact init byte range and the 85-byte CREATE2 preimage. Scratch
memory is separate from the caller; only its input range expands caller memory. -/
def create2Address (memoryReference sizeReference creator salt offset length : Core.Expr) : Core.Expr :=
  .letE (bundle [memoryReference, sizeReference, creator, salt, offset, length]) (create2AddressCode 0)

private def memory : Code := part 0 13
private def memorySize : Code := part 1 13
private def returnData : Code := part 2 13
private def returnSize : Code := part 3 13
private def callback : Code := part 4 13
private def creator : Code := part 5 13
private def currentDepth : Code := part 6 13
private def value : Code := part 7 13
private def salt : Code := part 8 13
private def create2 : Code := part 9 13
private def gas : Code := part 10 13
private def inputOffset : Code := part 11 13
private def inputLength : Code := part 12 13

private def finish (result : Code) : Code :=
  bind (store returnData (fun depth => responseField 1 (result depth))) fun _ =>
  bind (store returnSize (fun depth => responseField 2 (result depth))) fun _ =>
  success (fun depth => responseField 0 (result depth))

private def dispatch : Code :=
  bind (load memory) fun snapshot =>
  bind (allocate WordMapping.type empty) fun input =>
  bind (allocate .word (number 0)) fun size =>
  bindResult (fun depth => Memory.copyPackedFrom (input depth) (size depth) (number 0 depth)
    (snapshot depth) (inputOffset depth) (inputLength depth)) fun _ =>
  bindResult (fun depth => OptionalCell.read callbackType (callback depth) unavailableReason) fun function =>
  bindResult (fun depth => .apply (function depth) (bundle [maskedAddress creator depth,
    value depth, salt depth, create2 depth, binary .wordAdd currentDepth (number 1) depth,
    gas depth, load input depth, inputLength depth])) finish

private def invokeCode : Code :=
  bindResult (fun depth => Memory.touch (memorySize depth) (inputOffset depth) (inputLength depth)) fun _ =>
  bind (store returnData empty) fun _ =>
  bind (store returnSize (number 0)) fun _ =>
  choose (binary .wordGt currentDepth (number (depthLimit - 1))) (success (number 0)) dispatch

/-- Evaluate inputs once, touch the input range, clear prior return data and
copy init bytes to a private map starting at zero. A depth refusal returns zero.
The callback's full revert bytes become return data; caller memory is not used
as an output buffer. The four mutable frame cells must be distinct. -/
def invoke (memoryReference sizeReference returnDataReference returnSizeReference callbackReference
    creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length : Core.Expr) : Core.Expr :=
  .letE (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
    callbackReference, creatorAddress, depth, transferredValue, saltValue, isCreate2,
    suppliedGas, offset, length]) (invokeCode 0)

end Solcore.Frontend.RustHull.Creation
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Effects
/-! EVM effects expressed with ordinary Core cells. Message calls use an
explicit callback installed by the contract runner.
Termination records a byte range and propagates through the language-result
envelope, so no later Hull or Yul instruction executes. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Effects

def reservedPrefix : String := "$lean$evm$"
def slotName (name : String) : String := reservedPrefix ++ name

def slots : List (String × Core.Ty) :=
  [("memory", Core.WordMapping.type), ("memorySize", .word),
   ("calldata", Core.WordMapping.type), ("calldataSize", .word),
   ("world", AccountState.type), ("worldComplete", .bool),
   ("callvalue", .word), ("caller", .word), ("address", .word),
   ("returnData", Core.WordMapping.type), ("returnDataSize", .word),
   ("logs", Core.WordMapping.type), ("logSize", .word),
   ("balances", Core.WordMapping.type), ("isStatic", .bool), ("callDepth", .word),
   ("callHandler", Core.OptionalCell.cellType Calls.callbackType),
   ("callCodeHandler", Core.OptionalCell.cellType Calls.callbackType),
   ("delegateCallHandler", Core.OptionalCell.cellType Calls.callbackType),
   ("createHandler", Core.OptionalCell.cellType Creation.callbackType),
   ("availableGas", .sum .unit .word),
   ("exit", .word), ("returnOffset", .word), ("returnSize", .word)] ++ Ambient.slots

/-- Installed only when the caller supplies a concrete linked code image. -/
def codeSlots : List (String × Core.Ty) :=
  [("code", Core.WordMapping.type), ("codeSize", .word), ("codeKnown", .bool)]

def reference (scope : Scope) (name : String) (type : Core.Ty) : LowerM Core.Expr := do
  let (binding, index) ← scope.lookup (slotName name)
  expectType type binding.type
  pure (.var index)

def supports (name : String) : Bool := Ambient.supports name || AccountInspection.supports name || name ∈
  ["mload", "mstore", "mstore8", "msize", "calldataload", "calldatasize",
   "callvalue", "caller", "address", "sload", "sstore", "tload", "tstore",
   "memoryguard", "mcopy", "calldatacopy", "keccak256", "codesize", "codecopy", "datacopy",
   "gas", "returndatasize", "returndatacopy", "staticcall", "call", "callcode", "delegatecall",
   "create", "create2", "selfdestruct", "selfbalance", "balance",
   "log0", "log1", "log2", "log3", "log4",
   "return", "revert", "stop", "invalid"]

def terminate (scope : Scope) (kind : Nat) (offset size : Core.Expr) : LowerM Core.Expr := do
  let memorySize ← reference scope "memorySize" .word
  let exit ← reference scope "exit" .word
  let returnOffset ← reference scope "returnOffset" .word
  let returnSize ← reference scope "returnSize" .word
  let stores : List Core.Expr :=
    [.storeCell returnOffset offset, .storeCell returnSize size,
     .storeCell exit (.word (Core.Word.ofNatModulo kind))]
  let finish : Core.Expr := stores.foldr (fun store next =>
    .letE store (next.weakenAt 0))
      (Core.LanguageResult.failure .unit (.word Core.Word.maximum))
  pure (Core.LocalSequence.discard .unit (Memory.touch memorySize offset size) finish)

private def log (scope : Scope) (count : Nat) (arguments : List Core.Expr) : LowerM Lowered := do
  let offset :: length :: topics := arguments | fail "log requires memory offset and size"
  unless topics.length = count do fail "wrong number of log topics"
  let append := Logs.append
    (← reference scope "memory" Core.WordMapping.type) (← reference scope "memorySize" .word)
    (← reference scope "logs" Core.WordMapping.type) (← reference scope "logSize" .word)
    (.loadCell (← reference scope "address" .word)) topics offset length
  pure ⟨.unit, .ifE (.loadCell (← reference scope "isStatic" .bool))
    (← terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero)) append⟩

inductive CallMode where
  | ordinary | staticCall | callCode | delegateCall
  deriving BEq

def call (scope : Scope) (mode : CallMode)
    (gas target value inputOffset inputLength outputOffset outputLength : Core.Expr) : LowerM Lowered := do
  let isStatic := Core.Expr.loadCell (← reference scope "isStatic" .bool)
  let zeroValue := Core.Expr.binary .wordEq value (.word Core.Word.zero)
  let stipend := mode == .ordinary || mode == .callCode
  let suppliedGas := if !stipend then gas else Core.Expr.ifE zeroValue gas
    (.binary .wordAdd gas (.word (Core.Word.ofNatModulo 2300)))
  let invoke := Calls.invoke
    (← reference scope "memory" Core.WordMapping.type) (← reference scope "memorySize" .word)
    (← reference scope "returnData" Core.WordMapping.type) (← reference scope "returnDataSize" .word)
    (← reference scope (if mode == .callCode then "callCodeHandler"
      else if mode == .delegateCall then "delegateCallHandler" else "callHandler")
      (Core.OptionalCell.cellType Calls.callbackType))
    (.loadCell (← reference scope (if mode == .delegateCall then "caller" else "address") .word))
    (.loadCell (← reference scope "callDepth" .word))
    (if mode == .staticCall then .bool true else isStatic)
    suppliedGas target value inputOffset inputLength outputOffset outputLength
  if !stipend then pure ⟨.word, invoke⟩
  else
    let invalid ← terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero)
    let invalidWord := Core.LanguageResult.bind .word invalid
      (Core.LanguageResult.success (.word Core.Word.zero))
    let withStipend := Core.Expr.ifE zeroValue invoke
      (.ifE (.binary .wordGt gas (.word (Core.Word.ofNatModulo (Core.wordModulus - 2301))))
        (Core.LanguageResult.failure .word (.word (Core.Word.ofNatModulo 13))) invoke)
    pure ⟨.word, if mode == .callCode then withStipend
      else .ifE isStatic (.ifE zeroValue invoke invalidWord) withStipend⟩

private def create (scope : Scope) (create2 : Bool)
    (value offset length salt : Core.Expr) : LowerM Lowered := do
  let isStatic := Core.Expr.loadCell (← reference scope "isStatic" .bool)
  let invalid ← terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero)
  let invalidWord := Core.LanguageResult.bind .word invalid
    (Core.LanguageResult.success (.word Core.Word.zero))
  let gas := Core.Expr.loadCell (← reference scope "availableGas" (.sum .unit .word))
  let inner := scope.temporary .word
  let invoke := Creation.invoke
    (← reference inner "memory" Core.WordMapping.type) (← reference inner "memorySize" .word)
    (← reference inner "returnData" Core.WordMapping.type) (← reference inner "returnDataSize" .word)
    (← reference inner "createHandler" (Core.OptionalCell.cellType Creation.callbackType))
    (.loadCell (← reference inner "address" .word))
    (.loadCell (← reference inner "callDepth" .word))
    (value.weakenAt 0) (salt.weakenAt 0) (.bool create2) (.var 0)
    (offset.weakenAt 0) (length.weakenAt 0)
  let withGas := Core.Expr.caseE gas
    (Core.LanguageResult.failure .word (.word (Core.Word.ofNatModulo 9))) invoke
  pure ⟨.word, .ifE isStatic invalidWord
    (.ifE (.binary .wordGt length (.word (Core.Word.ofNatModulo 49152))) invalidWord withGas)⟩

def requireCode (scope : Scope) (type : Core.Ty) (body : Core.Expr) : LowerM Core.Expr := do
  pure (.ifE (.loadCell (← reference scope "codeKnown" .bool)) body
    (Core.LanguageResult.failure type (.word AccountInspection.unknownCodeReason)))

/-- Arguments are already evaluated word values in `scope`; the caller owns
the Hull or Yul argument order and failure propagation. -/
def lowerBuiltin (scope : Scope) (name : String) (arguments : List Core.Expr) : LowerM Lowered := do
  if Ambient.supports name then return ← Ambient.lowerBuiltin scope name arguments
  if AccountInspection.supports name then return ← AccountInspection.lowerBuiltin scope name arguments
  let result ← match name, arguments with
    | "memoryguard", [value] => pure ⟨.word, Core.LanguageResult.success value⟩
    | "mload", [offset] => pure ⟨.word, Memory.mload
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) offset⟩
    | "mstore", [offset, value] => pure ⟨.unit, Memory.mstore
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) offset value⟩
    | "mstore8", [offset, value] => pure ⟨.unit, Memory.mstore8
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) offset value⟩
    | "mcopy", [destination, source, length] => pure ⟨.unit, Memory.mcopy
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) destination source length⟩
    | "keccak256", [offset, length] => pure ⟨.word, Keccak.hash
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) offset length⟩
    | "calldatacopy", [destination, source, length] => pure ⟨.unit, Memory.copyPackedFrom
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) destination
        (.loadCell (← reference scope "calldata" Core.WordMapping.type)) source length⟩
    | "codecopy", [destination, source, length]
    | "datacopy", [destination, source, length] => pure ⟨.unit, ← requireCode scope .unit (Memory.copyPackedFrom
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) destination
        (.loadCell (← reference scope "code" Core.WordMapping.type)) source length)⟩
    | "codesize", [] => pure ⟨.word, ← requireCode scope .word (Core.LanguageResult.success
        (.loadCell (← reference scope "codeSize" .word)))⟩
    | "gas", [] => pure ⟨.word, .caseE
        (.loadCell (← reference scope "availableGas" (.sum .unit .word)))
        (Core.LanguageResult.failure .word (.word (Core.Word.ofNatModulo 9)))
        (Core.LanguageResult.success (.var 0))⟩
    | "staticcall", [gas, target, inputOffset, inputLength, outputOffset, outputLength] =>
        call scope .staticCall gas target (.word Core.Word.zero) inputOffset inputLength outputOffset outputLength
    | "call", [gas, target, value, inputOffset, inputLength, outputOffset, outputLength] =>
        call scope .ordinary gas target value inputOffset inputLength outputOffset outputLength
    | "callcode", [gas, target, value, inputOffset, inputLength, outputOffset, outputLength] =>
        call scope .callCode gas target value inputOffset inputLength outputOffset outputLength
    | "delegatecall", [gas, target, inputOffset, inputLength, outputOffset, outputLength] =>
        call scope .delegateCall gas target (.loadCell (← reference scope "callvalue" .word))
          inputOffset inputLength outputOffset outputLength
    | "create", [value, offset, length] => create scope false value offset length (.word Core.Word.zero)
    | "create2", [value, offset, length, salt] => create scope true value offset length salt
    | "selfbalance", [] => pure ⟨.word, Core.WordMapping.lookup
        (.loadCell (← reference scope "balances" Core.WordMapping.type))
        (.loadCell (← reference scope "address" .word))⟩
    | "balance", [address] => pure ⟨.word, Core.WordMapping.lookup
        (.loadCell (← reference scope "balances" Core.WordMapping.type))
        (.binary .wordAnd address (.word (Core.Word.ofNatModulo (2 ^ 160 - 1))))⟩
    | "log0", arguments => log scope 0 arguments
    | "log1", arguments => log scope 1 arguments
    | "log2", arguments => log scope 2 arguments
    | "log3", arguments => log scope 3 arguments
    | "log4", arguments => log scope 4 arguments
    | "returndatasize", [] => pure ⟨.word, Core.LanguageResult.success
        (.loadCell (← reference scope "returnDataSize" .word))⟩
    | "returndatacopy", [destination, source, length] => do
        let size := Core.Expr.loadCell (← reference scope "returnDataSize" .word)
        let invalid ← terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero)
        let copy := Memory.copyPackedFrom
          (← reference scope "memory" Core.WordMapping.type)
          (← reference scope "memorySize" .word) destination
          (.loadCell (← reference scope "returnData" Core.WordMapping.type)) source length
        pure ⟨.unit, .ifE (.binary .wordGt source size) invalid
          (.ifE (.binary .wordGt length (.binary .wordSub size source)) invalid copy)⟩
    | "msize", [] => pure ⟨.word, Core.LanguageResult.success
        (.loadCell (← reference scope "memorySize" .word))⟩
    | "calldataload", [offset] => pure ⟨.word, Memory.readMemoryWord
        (.loadCell (← reference scope "calldata" Core.WordMapping.type)) offset⟩
    | "calldatasize", [] => pure ⟨.word, Core.LanguageResult.success
        (.loadCell (← reference scope "calldataSize" .word))⟩
    | "callvalue", [] | "caller", [] | "address", [] => pure ⟨.word,
        Core.LanguageResult.success (.loadCell (← reference scope name .word))⟩
    | "sload", [key] | "tload", [key] => pure ⟨.word, AccountState.readStorage
        (← reference scope "world" AccountState.type) (.loadCell (← reference scope "address" .word))
        (.loadCell (← reference scope "worldComplete" .bool)) key (name == "tload")⟩
    | "sstore", [key, value] | "tstore", [key, value] => pure ⟨.unit,
        .ifE (.loadCell (← reference scope "isStatic" .bool))
          (← terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero))
          (AccountState.writeStorage (← reference scope "world" AccountState.type)
            (.loadCell (← reference scope "address" .word))
            (.loadCell (← reference scope "worldComplete" .bool)) key value (name == "tstore"))⟩
    | "selfdestruct", [beneficiary] => do
        let destroy := AccountLifecycle.destroy (← reference scope "world" AccountState.type)
          (← reference scope "balances" Core.WordMapping.type) (.loadCell (← reference scope "address" .word))
          beneficiary (.loadCell (← reference scope "worldComplete" .bool))
        pure ⟨.unit, .ifE (.loadCell (← reference scope "isStatic" .bool))
          (← terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero))
          (Core.LocalSequence.discard .unit destroy
            (← terminate scope 1 (.word Core.Word.zero) (.word Core.Word.zero)))⟩
    | "return", [offset, size] => pure ⟨.unit, ← terminate scope 1 offset size⟩
    | "revert", [offset, size] => pure ⟨.unit, ← terminate scope 2 offset size⟩
    | "stop", [] => pure ⟨.unit, ← terminate scope 1 (.word Core.Word.zero) (.word Core.Word.zero)⟩
    | "invalid", [] => pure ⟨.unit, ← terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero)⟩
    | _, _ => fail s!"unsupported EVM operation or wrong arity: {name}"
  pure result

/-- Hull's explicit revert writes one short UTF-8 message at byte zero, as in
the pinned Yul backend. Oversized messages are diagnosed rather than truncated. -/
def revertMessage (scope : Scope) (message : String) : LowerM Core.Expr := do
  let bytes := message.toUTF8
  if bytes.size > 32 then fail "Hull revert message exceeds one EVM word"
  else
    let leading := bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0
    let value := Core.Word.ofNatModulo (leading * 256 ^ (32 - bytes.size))
    let write ← lowerBuiltin scope "mstore" [.word Core.Word.zero, .word value]
    let exit ← lowerBuiltin scope "revert" [.word Core.Word.zero, .word (Core.Word.ofNatModulo bytes.size)]
    pure (Core.LocalSequence.discard .unit write.expression exit.expression)

end Solcore.Frontend.RustHull.Effects
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CreationRuntime
/-! CREATE/CREATE2 account lifecycle on ordinary Core. The enclosing runtime
provides checked constructor execution and exact deployed-image installation.
The creator nonce survives child failure; child world, balance and log changes
are restored together. Transaction-end deletion remains a separate operation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationRuntime
open Core CodeBuilder

private def response (address data size : Code) : Code := success (packet [address, data, size])
private def refused : Code := response (number 0) empty (number 0)

private def checkpoint (references : List Code) (continuation : Code → Code) : Code :=
  let rec capture : List Code → List (Code × Code) → Code
    | [], saved =>
        continuation (saved.foldr (fun (cell, value) next =>
          bind (store cell value) (fun _ => next)) unit)
    | reference :: rest, saved => bind (load reference) fun value =>
        capture rest ((reference, value) :: saved)
  capture references []

private def protect (restore attempt : Code) : Code := fun depth =>
  .caseE (attempt depth)
    ((bind restore fun _ => failure Creation.responseType
      (fun here => .var (here - depth - 1))) (depth + 1))
    (LanguageResult.success (.var 0))

private def deriveAddress (creator nonce request : Code) : Code :=
  choose (part 3 8 request)
    (bind (allocate WordMapping.type (part 6 8 request)) fun memory =>
      bind (allocate .word (number 0)) fun size =>
      fun depth => Creation.create2Address (memory depth) (size depth) (creator depth)
        (part 2 8 request depth) (number 0 depth) (part 7 8 request depth))
    (fun depth => Creation.createAddress (creator depth) (nonce depth))

private def transfer (balances creator target value creatorBalance : Code) : Code :=
  choose (binary .wordEq value (number 0)) (success unit) <|
  bindResult .unit (lookup (load balances) target) fun targetBalance =>
  choose (binary .wordGt targetBalance (binary .wordSub (number (wordModulus - 1)) value))
    (failure .unit (number 12)) <|
  bindResult .unit (insert (load balances) creator (binary .wordSub creatorBalance value)) fun debited =>
  bindResult .unit (insert debited target (binary .wordAdd targetBalance value)) fun credited =>
  success (store balances credited)

/-- Execute a creation request. `runInit target request` returns the usual
message-call response, while `installRuntime target childResponse` validates
and installs the exact returned runtime image. Both callbacks may mutate the
shared cells; every language failure is rolled back to the post-nonce snapshot.
Frame depth, static restrictions, gas and init-size limits are checked before
this dispatcher. All supplied references, completeness and request evaluate once. -/
def dispatch (worldReference balancesReference logsReference logSizeReference complete request : Code)
    (runInit : Code → Code → Code) (installRuntime : Code → Code → Code) : Code :=
  bind (packet [worldReference, balancesReference, logsReference, logSizeReference, complete, request]) fun args =>
  let world := part 0 6 args
  let balances := part 1 6 args
  let logs := part 2 6 args
  let logSize := part 3 6 args
  let complete := part 4 6 args
  let request := part 5 6 args
  let creator := address (part 0 8 request)
  let value := part 1 8 request
  bindResult Creation.responseType (lookup (load balances) creator) fun creatorBalance =>
  choose (binary .wordGt value creatorBalance) refused <|
  bindResult Creation.responseType (fun depth =>
    AccountState.get (load world depth) (creator depth) (complete depth)) fun creatorRecord =>
  let nonce := part 2 9 creatorRecord
  choose (binary .wordGt nonce (number (2 ^ 64 - 2))) refused <|
  bindResult Creation.responseType (deriveAddress creator nonce request) fun target =>
  bindResult Creation.responseType (fun depth => AccountState.writeField (world depth) (creator depth)
    (complete depth) 2 (binary .wordAdd nonce (number 1) depth)) fun _ =>
  checkpoint [world, balances, logs, logSize] fun restore =>
  let rollback (result : Code) := bind restore fun _ => result
  protect restore <|
  bindResult Creation.responseType (fun depth => AccountState.get (load world depth) (target depth)
    (complete depth)) fun existing =>
  choose (binary .wordGt (part 2 9 existing) (number 0)) refused <|
  choose (binary .wordGt (part 5 9 existing) (number 0)) refused <|
  choose (part 6 9 existing)
    (bindResult Creation.responseType (fun depth => AccountState.put (load world depth) (target depth)
      (AccountState.replace (AccountState.replace AccountState.defaultRecord 2 (number 1 depth)) 7 (.bool true))) fun inserted =>
      bind (store world inserted) fun _ =>
      bindResult Creation.responseType (transfer balances creator target value creatorBalance) fun _ =>
      bindResult Creation.responseType
        (choose (binary .wordEq (part 7 8 request) (number 0))
          (success (packet [boolean true, empty, number 0])) (runInit target request)) fun child =>
      choose (part 0 3 child)
        (choose (binary .wordGt (part 2 3 child) (number 24576)) (rollback refused) <|
          bindResult Creation.responseType (fun depth =>
            Memory.readMemoryByte (part 1 3 child depth) (number 0 depth)) fun first =>
          let invalidPrefix := choose (binary .wordGt (part 2 3 child) (number 0))
            (binary .wordEq first (number 0xef)) (boolean false)
          choose invalidPrefix (rollback refused) <|
          bindResult Creation.responseType (installRuntime target child) fun _ =>
          response target empty (number 0))
        (rollback (response (number 0) (part 1 3 child) (part 2 3 child))))
    (failure Creation.responseType (number 7))

end Solcore.Frontend.RustHull.CreationRuntime
end
