import Solcore.Frontend.RustHull.CodeBuilder
import Solcore.Frontend.RustHull.Memory
import Solcore.Core.OrderedMapping

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
private def clearTransaction (record : Core.Expr) : Core.Expr :=
  bundle ((List.range 9).map fun index =>
    if index == 1 then WordMapping.empty
    else if index == 7 || index == 8 then .bool false
    else field index record)

private def finalizeParameter : Core.Ty := .product type (.cell WordMapping.type)

private def finalizeBody : Core.Expr :=
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
