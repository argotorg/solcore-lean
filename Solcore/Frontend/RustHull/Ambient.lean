import Solcore.Frontend.RustHull.LoweringSupport
import Solcore.Frontend.RustHull.Memory

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

private def wordLiteral : Option Word → Core.Expr
  | none => .inLeft .word .unit
  | some value => .inRight .unit (.word value)

private def hashesLiteral : Option WordMapping.Entries → Core.Expr
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

private def read (scope : Scope) (name : String) (type : Core.Ty) : LowerM Core.Expr := do
  let (binding, index) ← scope.lookup ("$lean$evm$" ++ name)
  expectType type binding.type
  pure (.loadCell (.var index))

private abbrev Code := Nat → Core.Expr
private def raw (value : Core.Expr) : Code := fun depth => value.rename (· + depth)
private def number (value : Nat) : Code := fun _ => .word (Word.ofNatModulo value)
private def success (value : Code) : Code := fun depth => LanguageResult.success (value depth)
private def binary (operation : BinaryOp) (left right : Code) : Code :=
  fun depth => .binary operation (left depth) (right depth)
private def choose (condition yes no : Code) : Code :=
  fun depth => .ifE (condition depth) (yes depth) (no depth)
private def bind (value : Code) (body : Code → Code) : Code := fun depth =>
  .letE (value depth) (body (fun here => .var (here - depth - 1)) (depth + 1))
private def requireValue (option : Code) (body : Code → Code) : Code := fun depth =>
  .caseE (option depth) (LanguageResult.failure .word (.word unavailableReason))
    (body (fun here => .var (here - depth - 1)) (depth + 1))
private def lookup (mapping key : Code) : Code :=
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
