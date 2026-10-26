import Solcore.Frontend.RustHull.KeccakSemantics

/-! Contract addresses of CREATE and CREATE2, independent of Core. Byte strings
are lists of naturals below 256. RLP follows appendix B of the Yellow Paper,
and Keccak-256 of a byte string is the connected `KeccakSemantics` absorption
of those bytes stored from address zero. An address is the low 20 bytes of a
digest. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationAddressSemantics
open Core

abbrev Bytes := List Nat

/-- RLP's BE: the big-endian bytes of a natural number, without leading zeros. -/
def bigEndian (value : Nat) : Bytes :=
  if value = 0 then [] else bigEndian (value / 256) ++ [value % 256]
termination_by value
decreasing_by omega

/-- RLP of a byte string. -/
def encodeBytes (bytes : Bytes) : Bytes :=
  if bytes.length = 1 ∧ bytes.headD 0 < 128 then bytes
  else if bytes.length < 56 then (128 + bytes.length) :: bytes
  else (183 + (bigEndian bytes.length).length) :: (bigEndian bytes.length ++ bytes)

/-- RLP of a list whose items are already encoded. -/
def encodeList (items : List Bytes) : Bytes :=
  let payload := items.flatten
  if payload.length < 56 then (192 + payload.length) :: payload
  else (247 + (bigEndian payload.length).length) :: (bigEndian payload.length ++ payload)

/-- The 32 big-endian bytes of a word. -/
def wordBytes (value : Word) : Bytes :=
  (List.range 32).map fun index => value.val / 256 ^ (31 - index) % 256

/-- An address occupies the low 20 bytes of a word. -/
def addressBytes (value : Word) : Bytes := (wordBytes value).drop 12

/-- CREATE hashes the RLP list of the creator address and its nonce. -/
def createPreimage (creator nonce : Word) : Bytes :=
  encodeList [encodeBytes (addressBytes creator), encodeBytes (bigEndian nonce.val)]

/-- CREATE2 hashes 0xff, the creator address, the salt and the init-code hash. -/
def create2Preimage (creator salt initHash : Word) : Bytes :=
  255 :: (addressBytes creator ++ wordBytes salt ++ wordBytes initHash)

/-- Bytes written one at a time from `index`. -/
def storeBytes : MemorySemantics.Entries → Nat → Bytes → MemorySemantics.Entries
  | words, _, [] => words
  | words, index, byte :: rest =>
      storeBytes (MemorySemantics.writeByte words (Word.ofNatModulo index) (Word.ofNatModulo byte)) (index + 1) rest

def stored (bytes : Bytes) : MemorySemantics.Entries := storeBytes [] 0 bytes

/-- Keccak-256 of a byte string. -/
def Keccak (bytes : Bytes) (digest : Word) : Prop :=
  KeccakSemantics.Absorb (stored bytes) Word.zero (Word.ofNatModulo bytes.length)
    (List.replicate 25 Word.zero) digest

def address (digest : Word) : Word := digest.bitAnd (Word.ofNatModulo (2 ^ 160 - 1))

inductive Scheme where
  | create
  | create2 (salt : Word)

/-- The address of a new account. CREATE2's init-code hash is taken over the
init bytes copied from address zero. -/
inductive Derived (creator nonce : Word) (initCode : MemorySemantics.Entries) (initLength : Word) :
    Scheme → Word → Prop where
  | create {digest : Word} (hashed : Keccak (createPreimage creator nonce) digest) :
      Derived creator nonce initCode initLength .create (address digest)
  | create2 {salt initHash digest : Word}
      (initHashed : KeccakSemantics.Absorb initCode Word.zero initLength (List.replicate 25 Word.zero) initHash)
      (hashed : Keccak (create2Preimage creator salt initHash) digest) :
      Derived creator nonce initCode initLength (.create2 salt) (address digest)

end Solcore.Frontend.RustHull.CreationAddressSemantics
