import Solcore.Abi.Keccak256
import Solcore.ContractRuntime.RuntimeScalars.WordBytesProperties
import Solcore.ContractRuntime.CheckedHostCoreProgram
import Solcore.Core.Renaming
import Solcore.ContractRuntime.CheckedCoreContract
import Solcore.ContractRuntime.BalancedTopLevelExecution

/-!
Executable ABI support for statically described word methods, from metadata
and codecs through method-table dispatch and contract execution.
-/

/-!
## Consolidated module: `Solcore.Abi.StaticWordMetadata`
-/

/-! Validated metadata and selectors for the Static Word ABI profile. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.ContractRuntime

/-- The only external value type admitted by the first ABI profile. -/
inductive SupportedType where
  | uint256
  deriving Repr, BEq, DecidableEq

def SupportedType.canonicalText : SupportedType → String
  | .uint256 => "uint256"

private def isAsciiLetter (character : Char) : Bool :=
  let code := character.toNat
  (65 ≤ code && code ≤ 90) || (97 ≤ code && code ≤ 122)

private def isAsciiDigit (character : Char) : Bool :=
  let code := character.toNat
  48 ≤ code && code ≤ 57

private def isMethodNameStart (character : Char) : Bool :=
  isAsciiLetter character || character == '_'

private def isMethodNameContinue (character : Char) : Bool :=
  isMethodNameStart character || isAsciiDigit character

/-- Decide the exact ASCII grammar `[A-Za-z_][A-Za-z0-9_]*`. -/
def isValidMethodName (text : String) : Bool :=
  match text.toList with
  | [] => false
  | first :: rest =>
      isMethodNameStart first && rest.all isMethodNameContinue

/-- A method name carrying evidence that it satisfies the Static Word grammar. -/
structure MethodName where
  text : String
  valid : isValidMethodName text = true

/-- Validate an arbitrary string without normalization or partial failure. -/
def validateMethodName? (text : String) : Option MethodName :=
  if valid : isValidMethodName text = true then
    some ⟨text, valid⟩
  else
    none

/-- Syntax-independent metadata for one `uint256 -> uint256` method. -/
structure MethodMetadata where
  name : MethodName
  inputType : SupportedType
  outputType : SupportedType

def MethodMetadata.staticWord (name : MethodName) : MethodMetadata where
  name := name
  inputType := .uint256
  outputType := .uint256

/-- Canonical Ethereum signature spelling; return types are not included. -/
def MethodMetadata.canonicalSignatureText
    (metadata : MethodMetadata) : String :=
  metadata.name.text ++ "(" ++ metadata.inputType.canonicalText ++ ")"

def MethodMetadata.canonicalSignatureBytes
    (metadata : MethodMetadata) : Bytes :=
  metadata.canonicalSignatureText.toUTF8

/-- An ABI selector whose four-octet width is part of its type. -/
structure Selector where
  bytes : Vector UInt8 4
  deriving Repr, BEq, DecidableEq

def Selector.encode (selector : Selector) : Bytes :=
  ⟨selector.bytes.toArray⟩

/-- Decode only an exact four-byte sequence. -/
def Selector.decode? (bytes : Bytes) : Option Selector :=
  if width : bytes.size = 4 then
    some ⟨⟨bytes.data, width⟩⟩
  else
    none

@[simp] theorem Selector.encode_size (selector : Selector) :
    selector.encode.size = 4 := by
  change selector.bytes.toArray.size = 4
  exact selector.bytes.size_toArray

@[simp] theorem Selector.decode_encode (selector : Selector) :
    Selector.decode? selector.encode = some selector := by
  unfold Selector.decode?
  rw [dif_pos selector.encode_size]
  congr

def Selector.toUInt32 (selector : Selector) : UInt32 :=
  selector.bytes.toArray.foldl
    (fun value byte => (value <<< 8) ||| byte.toUInt32) 0

/-- Big-endian numeric view of the selector in the exact `2^32` range. -/
def Selector.toFin (selector : Selector) : Fin (2 ^ 32) :=
  Fin.cast (by decide) selector.toUInt32.toFin

/-- Derive the first four Keccak digest bytes from arbitrary signature bytes. -/
def selectorFromSignatureBytes (signature : Bytes) : Selector :=
  let digest := Keccak256.hash signature
  ⟨Vector.ofFn (fun index => digest.get! index.val)⟩

def MethodMetadata.selector (metadata : MethodMetadata) : Selector :=
  selectorFromSignatureBytes metadata.canonicalSignatureBytes

end Solcore.Abi.V1

/-!
## Consolidated module: `Solcore.Abi.StaticWordMetadataProperties`
-/

/-! Proof contracts for Static Word ABI metadata and selectors. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.ContractRuntime

theorem validateMethodName?_isSome_iff (text : String) :
    (validateMethodName? text).isSome ↔ isValidMethodName text = true := by
  unfold validateMethodName?
  split <;> simp_all

theorem validateMethodName?_eq_some_iff
    (text : String) (name : MethodName) :
    validateMethodName? text = some name ↔ name.text = text := by
  constructor
  · intro success
    unfold validateMethodName? at success
    split at success
    · cases success
      rfl
    · contradiction
  · intro textEq
    rcases name with ⟨nameText, valid⟩
    simp only at textEq
    subst nameText
    unfold validateMethodName?
    rw [dif_pos valid]

theorem validateMethodName?_success_text
    {text : String} {name : MethodName}
    (success : validateMethodName? text = some name) :
    name.text = text :=
  (validateMethodName?_eq_some_iff text name).mp success

theorem Selector.encode_of_decode?_eq_some
    {bytes : Bytes} {selector : Selector}
    (success : Selector.decode? bytes = some selector) :
    selector.encode = bytes := by
  unfold Selector.decode? at success
  split at success
  · cases success
    rfl
  · contradiction

theorem Selector.decode?_eq_some_iff
    (bytes : Bytes) (selector : Selector) :
    Selector.decode? bytes = some selector ↔ bytes = selector.encode := by
  constructor
  · intro success
    exact (Selector.encode_of_decode?_eq_some success).symm
  · intro encoded
    subst bytes
    exact selector.decode_encode

/-- The numeric selector view consumes its four bytes from most to least
significant, with one eight-bit shift per byte. -/
theorem Selector.toUInt32_eq_bigEndianBytes (selector : Selector) :
    selector.toUInt32 =
      ((selector.bytes[0].toUInt32 <<< 8 |||
          selector.bytes[1].toUInt32) <<< 8 |||
        selector.bytes[2].toUInt32) <<< 8 |||
      selector.bytes[3].toUInt32 := by
  rcases selector with ⟨⟨⟨items⟩, sizeEq⟩⟩
  cases items with
  | nil => simp at sizeEq
  | cons first rest =>
      cases rest with
      | nil => simp at sizeEq
      | cons second rest =>
          cases rest with
          | nil => simp at sizeEq
          | cons third rest =>
              cases rest with
              | nil => simp at sizeEq
              | cons fourth rest =>
                  cases rest with
                  | nil => simp [Selector.toUInt32]
                  | cons fifth rest => simp at sizeEq

/-- The bounded numeric view carries the same big-endian value. -/
theorem Selector.toFin_val_eq_bigEndianBytes (selector : Selector) :
    selector.toFin.val =
      (((selector.bytes[0].toUInt32 <<< 8 |||
          selector.bytes[1].toUInt32) <<< 8 |||
        selector.bytes[2].toUInt32) <<< 8 |||
      selector.bytes[3].toUInt32).toNat := by
  change selector.toUInt32.toNat = _
  rw [selector.toUInt32_eq_bigEndianBytes]

private theorem selectorOfFirstFourBytes_encode
    (bytes : Bytes) (width : 4 ≤ bytes.size) :
    (⟨Vector.ofFn (fun index => bytes.get! index.val)⟩ : Selector).encode =
      bytes.extract 0 4 := by
  apply ByteArray.ext
  apply Array.ext
  · simp [Selector.encode, Nat.min_eq_left width]
  · intro index leftLt rightLt
    have indexLtFour : index < 4 := by
      simpa [Selector.encode] using leftLt
    have indexLtBytes : index < bytes.data.size := by
      exact Nat.lt_of_lt_of_le indexLtFour width
    simp [Selector.encode, ByteArray.data_extract]
    change bytes.data[index]! = bytes.data[index]
    exact getElem!_pos bytes.data index indexLtBytes

theorem selectorFromSignatureBytes_encode (signature : Bytes) :
    (selectorFromSignatureBytes signature).encode =
      (Keccak256.hash signature).extract 0 4 := by
  unfold selectorFromSignatureBytes
  apply selectorOfFirstFourBytes_encode
  rw [Keccak256.hash_size]
  omega

end Solcore.Abi.V1

/-!
## Consolidated module: `Solcore.Abi.StaticWordCodec`
-/

/-! Exact calldata and returndata codecs for the Static Word ABI profile. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.Util
open Solcore.ContractRuntime

/-- A decoded `uint256 -> uint256` call, before selector admission. -/
structure StaticWordCall where
  selector : Selector
  argument : Core.Word
  deriving Repr, BEq, DecidableEq

/-- The sole low-level call decoding failure: the fixed prefix is incomplete. -/
inductive CallDecodeFailure where
  | shortCalldata (actualSize : Nat)
  deriving Repr, BEq, DecidableEq

/-- Strict returndata rejects every width other than one ABI word. -/
inductive ResultDecodeFailure where
  | invalidLength (actualSize : Nat)
  deriving Repr, BEq, DecidableEq

def callSize : Nat := 36

def resultSize : Nat := 32

/-- Canonical calldata is the exact selector followed by one big-endian word. -/
def encodeCall (selector : Selector) (argument : Core.Word) : Bytes :=
  selector.encode.append (encodeWordBytesBE argument)

/-- Canonical returndata is one exact big-endian word. -/
def encodeResult (result : Core.Word) : Bytes :=
  encodeWordBytesBE result

private def selectorOfExactBytes
    (bytes : Bytes) (width : bytes.size = 4) : Selector :=
  ⟨⟨bytes.data, by simpa using width⟩⟩

private def wordOfExactBytes
    (bytes : Bytes) (width : bytes.size = 32) : Core.Word :=
  RuntimeScalar.Internal.wordOfByteValue
    (FixedRadix.decode
      ⟨bytes.data.map UInt8.toFin, by simpa using width⟩)

private theorem selectorOfExactBytes_encode (selector : Selector) :
    selectorOfExactBytes selector.encode selector.encode_size = selector := by
  cases selector
  rfl

private theorem selectorOfExactBytes_eq_of_eq
    (bytes : Bytes) (width : bytes.size = 4) (selector : Selector)
    (selected : bytes = selector.encode) :
    selectorOfExactBytes bytes width = selector := by
  subst bytes
  exact selectorOfExactBytes_encode selector

private theorem decodeWordBytesBE?_wordOfExactBytes
    (bytes : Bytes) (width : bytes.size = 32) :
    decodeWordBytesBE? bytes = some (wordOfExactBytes bytes width) := by
  unfold decodeWordBytesBE? RuntimeScalar.Internal.wordDigitsOfBytes?
  rw [dif_pos width]
  rfl

private theorem wordOfExactBytes_encode (word : Core.Word) :
    wordOfExactBytes (encodeWordBytesBE word) (encodeWordBytesBE_size word) =
      word := by
  have decoded := decodeWordBytesBE?_wordOfExactBytes
    (encodeWordBytesBE word) (encodeWordBytesBE_size word)
  rw [decodeWordBytesBE?_encodeWordBytesBE] at decoded
  exact Option.some.inj decoded |>.symm

private theorem wordOfExactBytes_eq_of_eq
    (bytes : Bytes) (width : bytes.size = 32) (word : Core.Word)
    (selected : bytes = encodeWordBytesBE word) :
    wordOfExactBytes bytes width = word := by
  subst bytes
  exact wordOfExactBytes_encode word

/-- Decode the fixed 36-byte prefix and deliberately ignore any suffix. -/
def decodeCall (calldata : Bytes) :
    Except CallDecodeFailure StaticWordCall :=
  if short : calldata.size < callSize then
    .error (.shortCalldata calldata.size)
  else
    let selectorBytes := calldata.extract 0 4
    let argumentBytes := calldata.extract 4 36
    have selectorWidth : selectorBytes.size = 4 := by
      simp only [selectorBytes, ByteArray.size_extract, callSize] at short ⊢
      omega
    have argumentWidth : argumentBytes.size = 32 := by
      simp only [argumentBytes, ByteArray.size_extract, callSize] at short ⊢
      omega
    .ok {
      selector := selectorOfExactBytes selectorBytes selectorWidth
      argument := wordOfExactBytes argumentBytes argumentWidth
    }

/-- Decode returndata only at the exact one-word width. -/
def decodeResult (returndata : Bytes) :
    Except ResultDecodeFailure Core.Word :=
  if width : returndata.size = resultSize then
    .ok (wordOfExactBytes returndata width)
  else
    .error (.invalidLength returndata.size)

@[simp] theorem encodeCall_size (selector : Selector) (argument : Core.Word) :
    (encodeCall selector argument).size = callSize := by
  simp [encodeCall, callSize]

@[simp] theorem encodeResult_size (result : Core.Word) :
    (encodeResult result).size = resultSize := by
  simp [encodeResult, resultSize]

@[simp] theorem decodeCall_encode
    (selector : Selector) (argument : Core.Word) :
    decodeCall (encodeCall selector argument) =
      .ok ⟨selector, argument⟩ := by
  simp [decodeCall, encodeCall, callSize,
    ByteArray.extract_append_eq_left,
    ByteArray.extract_append_eq_right,
    selectorOfExactBytes_encode, wordOfExactBytes_encode]

/-- Additional calldata does not change the decoded fixed call prefix. -/
@[simp] theorem decodeCall_encode_append
    (selector : Selector) (argument : Core.Word) (suffix : Bytes) :
    decodeCall ((encodeCall selector argument).append suffix) =
      .ok ⟨selector, argument⟩ := by
  have selectorExtract :
      ((encodeCall selector argument).append suffix).extract 0 4 =
        selector.encode := by
    unfold encodeCall
    rw [show
      (selector.encode.append (encodeWordBytesBE argument)).append suffix =
        selector.encode.append ((encodeWordBytesBE argument).append suffix) from
      ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_left selector.encode_size.symm
  have argumentExtract :
      ((encodeCall selector argument).append suffix).extract 4 36 =
        encodeWordBytesBE argument := by
    unfold encodeCall
    rw [show
      (selector.encode.append (encodeWordBytesBE argument)).append suffix =
        selector.encode.append ((encodeWordBytesBE argument).append suffix) from
      ByteArray.append_assoc]
    calc
      _ = ((encodeWordBytesBE argument).append suffix).extract 0 32 := by
        simpa using
          (ByteArray.extract_append_size_add
            (a := selector.encode)
            (b := (encodeWordBytesBE argument).append suffix)
            (i := 0) (j := 32))
      _ = encodeWordBytesBE argument :=
        ByteArray.extract_append_eq_left
          (encodeWordBytesBE_size argument).symm
  unfold decodeCall
  rw [dif_neg (by simp [encodeCall, callSize])]
  dsimp only
  rw [selectorOfExactBytes_eq_of_eq _ _ _ selectorExtract,
    wordOfExactBytes_eq_of_eq _ _ _ argumentExtract]

@[simp] theorem decodeResult_encode (result : Core.Word) :
    decodeResult (encodeResult result) = .ok result := by
  simp [decodeResult, encodeResult, resultSize, wordOfExactBytes_encode]

theorem decodeCall_eq_shortCalldata_iff (calldata : Bytes) :
    decodeCall calldata = .error (.shortCalldata calldata.size) ↔
      calldata.size < callSize := by
  unfold decodeCall
  split <;> simp_all

theorem decodeResult_eq_invalidLength_iff (returndata : Bytes) :
    decodeResult returndata = .error (.invalidLength returndata.size) ↔
      returndata.size ≠ resultSize := by
  unfold decodeResult
  split <;> simp_all

theorem decodeCall_failure_ne_success
    (calldata : Bytes) (failure : CallDecodeFailure) (call : StaticWordCall)
    (failed : decodeCall calldata = .error failure) :
    decodeCall calldata ≠ .ok call := by
  rw [failed]
  simp

theorem decodeResult_failure_ne_success
    (returndata : Bytes) (failure : ResultDecodeFailure) (result : Core.Word)
    (failed : decodeResult returndata = .error failure) :
    decodeResult returndata ≠ .ok result := by
  rw [failed]
  simp

end Solcore.Abi.V1

/-!
## Consolidated module: `Solcore.Abi.StaticWordImplementation`
-/

/-! Proof-carrying checked implementations for the Static Word ABI profile. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.Core
open Solcore.ContractRuntime

/-- Checker-accepted method code with the exact `uint256 -> uint256` Core shape.
The first ABI profile deliberately excludes named-data definitions. -/
structure WordImplementation where
  code : CheckedHostCoreProgram
  resultType_eq :
    code.program.resultType = .function .word .word
  dataDefinitions_eq : code.program.dataDefinitions = []

namespace WordImplementation

/-- Refine already checked host-aware code exactly when it has the supported
method type and no named-data definitions. -/
def ofCode? (code : CheckedHostCoreProgram) : Option WordImplementation :=
  if resultTypeEq :
      code.program.resultType = .function .word .word then
    if dataDefinitionsEq : code.program.dataDefinitions = [] then
      some ⟨code, resultTypeEq, dataDefinitionsEq⟩
    else
      none
  else
    none

/-- Check host admission before applying the Static Word refinement. -/
def ofProgram? (program : Program) : Option WordImplementation := do
  let code ← CheckedHostCoreProgram.ofProgram? program
  ofCode? code

@[simp] theorem ofCode?_of_profile
    (code : CheckedHostCoreProgram)
    (resultTypeEq :
      code.program.resultType = .function .word .word)
    (dataDefinitionsEq : code.program.dataDefinitions = []) :
    ofCode? code = some ⟨code, resultTypeEq, dataDefinitionsEq⟩ := by
  simp [ofCode?, resultTypeEq, dataDefinitionsEq]

/-- Admission succeeds exactly for the supported checked-code shape. -/
theorem ofCode?_exists_iff (code : CheckedHostCoreProgram) :
    (∃ implementation, ofCode? code = some implementation) ↔
      code.program.resultType = .function .word .word ∧
        code.program.dataDefinitions = [] := by
  constructor
  · intro admitted
    rcases admitted with ⟨implementation, admitted⟩
    simp only [ofCode?] at admitted
    split at admitted
    · split at admitted
      · exact ⟨by assumption, by assumption⟩
      · contradiction
    · contradiction
  · rintro ⟨resultTypeEq, dataDefinitionsEq⟩
    exact ⟨⟨code, resultTypeEq, dataDefinitionsEq⟩,
      ofCode?_of_profile code resultTypeEq dataDefinitionsEq⟩

/-- Rejection is exactly a result-type or definition-table mismatch. -/
@[simp] theorem ofCode?_eq_none_iff (code : CheckedHostCoreProgram) :
    ofCode? code = none ↔
      code.program.resultType ≠ .function .word .word ∨
        code.program.dataDefinitions ≠ [] := by
  constructor
  · intro rejected
    by_cases resultTypeEq :
        code.program.resultType = .function .word .word
    · right
      intro dataDefinitionsEq
      simp [ofCode?, resultTypeEq, dataDefinitionsEq] at rejected
    · exact Or.inl resultTypeEq
  · intro mismatch
    rcases mismatch with resultTypeNe | dataDefinitionsNe
    · simp [ofCode?, resultTypeNe]
    · by_cases resultTypeEq :
          code.program.resultType = .function .word .word
      · simp [ofCode?, resultTypeEq, dataDefinitionsNe]
      · simp [ofCode?, resultTypeEq]

@[simp] theorem ofProgram?_of_rejected
    (program : Program)
    (rejected : program.checkHost = false) :
    ofProgram? program = none := by
  simp [ofProgram?,
    CheckedHostCoreProgram.ofProgram?_of_rejected program rejected]

end WordImplementation

end Solcore.Abi.V1

/-!
## Consolidated module: `Solcore.Abi.StaticWordMethodTable`
-/

/-! Deterministic validation for Static Word ABI method tables. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

/-- Metadata paired with the checked Core implementation it describes. -/
structure Method where
  metadata : MethodMetadata
  implementation : WordImplementation

/-- One method with its canonical signature and selector computed once.
The equality fields prevent the cached dispatch keys from drifting from the
metadata. -/
structure IndexedMethod where
  method : Method
  signature : String
  signature_eq : signature = method.metadata.canonicalSignatureText
  selector : Selector
  selector_eq : selector = method.metadata.selector

namespace Method

def index (method : Method) : IndexedMethod where
  method := method
  signature := method.metadata.canonicalSignatureText
  signature_eq := rfl
  selector := method.metadata.selector
  selector_eq := rfl

end Method

namespace IndexedMethod

/-- Unicode-scalar ordering of canonical ASCII signatures. -/
def signatureLE (left right : IndexedMethod) : Bool :=
  (compare left.signature right.signature).isLE

end IndexedMethod

/-- Index and canonically order methods before selecting any conflict. -/
def canonicalMethodEntries (methods : List Method) : List IndexedMethod :=
  (methods.map Method.index).mergeSort IndexedMethod.signatureLE

/-- The lexicographically first pair sharing a canonical signature. -/
def firstDuplicateSignature? :
    List IndexedMethod → Option (IndexedMethod × IndexedMethod)
  | [] => none
  | first :: rest =>
      match rest.find? (fun later => decide (later.signature = first.signature)) with
      | some later => some (first, later)
      | none => firstDuplicateSignature? rest

/-- The lexicographically first pair sharing a selector. -/
def firstSelectorCollision? :
    List IndexedMethod → Option (IndexedMethod × IndexedMethod)
  | [] => none
  | first :: rest =>
      match rest.find? (fun later => decide (later.selector = first.selector)) with
      | some later => some (first, later)
      | none => firstSelectorCollision? rest

/-- A complete and machine-readable method-table validation failure. -/
inductive MethodTableError where
  | empty
  | duplicateSignature
      (first second : MethodMetadata)
      (signature : String)
  | selectorCollision
      (first second : MethodMetadata)
      (firstSignature secondSignature : String)
      (selector : Selector)

/-- A nonempty canonical table whose constructor is available only to this
validator. The retained equations certify both conflict scans. -/
structure MethodTable where
  private mk ::
  entries : List IndexedMethod
  nonempty : entries ≠ []
  noDuplicateSignature : firstDuplicateSignature? entries = none
  noSelectorCollision : firstSelectorCollision? entries = none

namespace MethodTable

/-- Validate every finite input, reporting one canonically selected error. -/
def validate (methods : List Method) : Except MethodTableError MethodTable :=
  match entriesEq : canonicalMethodEntries methods with
  | [] => .error .empty
  | first :: rest =>
      let entries := first :: rest
      match duplicateEq : firstDuplicateSignature? entries with
      | some conflict =>
          .error (.duplicateSignature
            conflict.1.method.metadata
            conflict.2.method.metadata
            conflict.1.signature)
      | none =>
          match collisionEq : firstSelectorCollision? entries with
          | some conflict =>
              .error (.selectorCollision
                conflict.1.method.metadata
                conflict.2.method.metadata
                conflict.1.signature
                conflict.2.signature
                conflict.1.selector)
          | none =>
              .ok {
                entries := entries
                nonempty := by simp [entries]
                noDuplicateSignature := duplicateEq
                noSelectorCollision := collisionEq
              }

end MethodTable

end Solcore.Abi.V1

/-!
## Consolidated module: `Solcore.Abi.StaticWordMethodTableProperties`
-/

/-! External proof contract for deterministic Static Word method tables. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

/-- A duplicate-signature scan succeeds exactly when every pair differs. -/
theorem firstDuplicateSignature?_eq_none_iff (entries : List IndexedMethod) :
    firstDuplicateSignature? entries = none ↔
      entries.Pairwise fun left right => left.signature ≠ right.signature := by
  induction entries with
  | nil => simp [firstDuplicateSignature?]
  | cons first rest inductionHypothesis =>
      cases found : rest.find? (fun later =>
          decide (later.signature = first.signature)) with
      | none =>
          have headDistinct : ∀ later ∈ rest,
              first.signature ≠ later.signature := by
            intro later member equal
            have rejected := (List.find?_eq_none.mp found) later member
            exact rejected (by simp [equal])
          rw [firstDuplicateSignature?, found, inductionHypothesis,
            List.pairwise_cons]
          exact ⟨fun tail => ⟨headDistinct, tail⟩, fun all => all.2⟩
      | some later =>
          have laterMember : later ∈ rest :=
            List.mem_of_find?_eq_some found
          have equal : later.signature = first.signature := by
            simpa using List.find?_some found
          simp only [firstDuplicateSignature?, found, reduceCtorEq,
            false_iff, List.pairwise_cons]
          intro pairwise
          exact pairwise.1 later laterMember equal.symm

/-- A selector-collision scan succeeds exactly when every pair differs. -/
theorem firstSelectorCollision?_eq_none_iff (entries : List IndexedMethod) :
    firstSelectorCollision? entries = none ↔
      entries.Pairwise fun left right => left.selector ≠ right.selector := by
  induction entries with
  | nil => simp [firstSelectorCollision?]
  | cons first rest inductionHypothesis =>
      cases found : rest.find? (fun later =>
          decide (later.selector = first.selector)) with
      | none =>
          have headDistinct : ∀ later ∈ rest,
              first.selector ≠ later.selector := by
            intro later member equal
            have rejected := (List.find?_eq_none.mp found) later member
            exact rejected (by simp [equal])
          rw [firstSelectorCollision?, found, inductionHypothesis,
            List.pairwise_cons]
          exact ⟨fun tail => ⟨headDistinct, tail⟩, fun all => all.2⟩
      | some later =>
          have laterMember : later ∈ rest :=
            List.mem_of_find?_eq_some found
          have equal : later.selector = first.selector := by
            simpa using List.find?_some found
          simp only [firstSelectorCollision?, found, reduceCtorEq,
            false_iff, List.pairwise_cons]
          intro pairwise
          exact pairwise.1 later laterMember equal.symm

theorem IndexedMethod.signatureLE_trans
    {first second third : IndexedMethod}
    (firstSecond : IndexedMethod.signatureLE first second = true)
    (secondThird : IndexedMethod.signatureLE second third = true) :
    IndexedMethod.signatureLE first third = true := by
  exact Std.TransCmp.isLE_trans (cmp := compare) firstSecond secondThird

theorem IndexedMethod.signatureLE_total (left right : IndexedMethod) :
    IndexedMethod.signatureLE left right = true ∨
      IndexedMethod.signatureLE right left = true := by
  cases order : compare left.signature right.signature with
  | lt => exact Or.inl (by simp [IndexedMethod.signatureLE, order])
  | eq => exact Or.inl (by simp [IndexedMethod.signatureLE, order])
  | gt =>
      have swapped : compare right.signature left.signature = .lt :=
        Std.OrientedCmp.lt_of_gt (cmp := compare) order
      exact Or.inr (by simp [IndexedMethod.signatureLE, swapped])

/-- Canonicalization retains exactly the indexed input entries. -/
theorem canonicalMethodEntries_perm (methods : List Method) :
    (canonicalMethodEntries methods).Perm (methods.map Method.index) := by
  exact List.mergeSort_perm _ _

/-- Permuting metadata input only permutes its canonical indexed entries. -/
theorem canonicalMethodEntries_perm_of_input_perm
    {firstMethods secondMethods : List Method}
    (inputPermutation : firstMethods.Perm secondMethods) :
    (canonicalMethodEntries firstMethods).Perm
      (canonicalMethodEntries secondMethods) :=
  (canonicalMethodEntries_perm firstMethods).trans <|
    (inputPermutation.map Method.index).trans <|
      (canonicalMethodEntries_perm secondMethods).symm

/-- Pointwise provenance for every canonical entry. -/
theorem mem_canonicalMethodEntries_iff
    {methods : List Method} {entry : IndexedMethod} :
    entry ∈ canonicalMethodEntries methods ↔
      ∃ method, method ∈ methods ∧ Method.index method = entry := by
  simp [canonicalMethodEntries]

private theorem pairwise_signatures_iff_of_perm
    {first second : List IndexedMethod} (permutation : first.Perm second) :
    (first.Pairwise fun left right => left.signature ≠ right.signature) ↔
      second.Pairwise fun left right => left.signature ≠ right.signature := by
  constructor
  · intro pairwise
    exact permutation.pairwise pairwise fun different equal =>
      different equal.symm
  · intro pairwise
    exact permutation.symm.pairwise pairwise fun different equal =>
      different equal.symm

private theorem pairwise_selectors_iff_of_perm
    {first second : List IndexedMethod} (permutation : first.Perm second) :
    (first.Pairwise fun left right => left.selector ≠ right.selector) ↔
      second.Pairwise fun left right => left.selector ≠ right.selector := by
  constructor
  · intro pairwise
    exact permutation.pairwise pairwise fun different equal =>
      different equal.symm
  · intro pairwise
    exact permutation.symm.pairwise pairwise fun different equal =>
      different equal.symm

/-- Duplicate-scan success is invariant under input permutation. -/
theorem duplicateScanNone_iff_of_input_perm
    {firstMethods secondMethods : List Method}
    (inputPermutation : firstMethods.Perm secondMethods) :
    firstDuplicateSignature? (canonicalMethodEntries firstMethods) = none ↔
      firstDuplicateSignature? (canonicalMethodEntries secondMethods) = none := by
  rw [firstDuplicateSignature?_eq_none_iff,
    firstDuplicateSignature?_eq_none_iff]
  exact pairwise_signatures_iff_of_perm
    (canonicalMethodEntries_perm_of_input_perm inputPermutation)

/-- Selector-scan success is invariant under input permutation. -/
theorem selectorScanNone_iff_of_input_perm
    {firstMethods secondMethods : List Method}
    (inputPermutation : firstMethods.Perm secondMethods) :
    firstSelectorCollision? (canonicalMethodEntries firstMethods) = none ↔
      firstSelectorCollision? (canonicalMethodEntries secondMethods) = none := by
  rw [firstSelectorCollision?_eq_none_iff,
    firstSelectorCollision?_eq_none_iff]
  exact pairwise_selectors_iff_of_perm
    (canonicalMethodEntries_perm_of_input_perm inputPermutation)

/-- Canonical emptiness is invariant under input permutation. -/
theorem canonicalEntriesNil_iff_of_input_perm
    {firstMethods secondMethods : List Method}
    (inputPermutation : firstMethods.Perm secondMethods) :
    canonicalMethodEntries firstMethods = [] ↔
      canonicalMethodEntries secondMethods = [] := by
  have entriesPermutation :=
    canonicalMethodEntries_perm_of_input_perm inputPermutation
  constructor
  · intro firstNil
    rw [firstNil] at entriesPermutation
    exact entriesPermutation.nil_eq.symm
  · intro secondNil
    rw [secondNil] at entriesPermutation
    exact entriesPermutation.eq_nil

/-- Canonical entries are nondecreasing by signature. -/
theorem canonicalMethodEntries_sorted (methods : List Method) :
    (canonicalMethodEntries methods).Pairwise fun left right =>
      IndexedMethod.signatureLE left right = true := by
  unfold canonicalMethodEntries
  apply List.pairwise_mergeSort
  · intro first second third firstSecond secondThird
    exact IndexedMethod.signatureLE_trans firstSecond secondThird
  · intro left right
    rcases IndexedMethod.signatureLE_total left right with forward | backward
    · simp [forward]
    · simp [backward]

namespace MethodTable

inductive ErrorKind where
  | empty
  | duplicateSignature
  | selectorCollision
  deriving Repr, BEq, DecidableEq

def ErrorKind.ofError : MethodTableError → ErrorKind
  | .empty => .empty
  | .duplicateSignature .. => .duplicateSignature
  | .selectorCollision .. => .selectorCollision

/-- Every rejected validation has exactly one exhaustive scan classification. -/
theorem rejected_classification
    {methods : List Method} {error : MethodTableError}
    (rejected : MethodTable.validate methods = .error error) :
    (ErrorKind.ofError error = .empty ∧
      canonicalMethodEntries methods = []) ∨
    (ErrorKind.ofError error = .duplicateSignature ∧
      canonicalMethodEntries methods ≠ [] ∧
      firstDuplicateSignature? (canonicalMethodEntries methods) ≠ none) ∨
    (ErrorKind.ofError error = .selectorCollision ∧
      canonicalMethodEntries methods ≠ [] ∧
      firstDuplicateSignature? (canonicalMethodEntries methods) = none ∧
      firstSelectorCollision? (canonicalMethodEntries methods) ≠ none) := by
  simp only [MethodTable.validate] at rejected
  split at rejected
  · rename_i entriesEq
    injection rejected with errorEq
    rw [← errorEq]
    exact Or.inl ⟨rfl, entriesEq⟩
  · split at rejected
    · rename_i first rest entriesEq conflict duplicateEq
      injection rejected with errorEq
      rw [← errorEq]
      exact Or.inr <| Or.inl ⟨rfl, by simp [entriesEq], by simp [entriesEq,
        duplicateEq]⟩
    · split at rejected
      · rename_i first rest entriesEq duplicateEq conflict collisionEq
        injection rejected with errorEq
        rw [← errorEq]
        exact Or.inr <| Or.inr ⟨rfl, by simp [entriesEq], by
          simpa [entriesEq] using duplicateEq, by simp [entriesEq,
            collisionEq]⟩
      · cases rejected

private theorem eq_of_signature_eq_of_mem
    {entries : List IndexedMethod}
    (unique : entries.Pairwise fun left right =>
      left.signature ≠ right.signature)
    {left right : IndexedMethod}
    (leftMember : left ∈ entries) (rightMember : right ∈ entries)
    (signatureEq : left.signature = right.signature) : left = right := by
  induction entries with
  | nil => simp at leftMember
  | cons head tail inductionHypothesis =>
      rw [List.pairwise_cons] at unique
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember <;>
        rcases rightMember with rfl | rightMember
      · rfl
      · exact (unique.1 right rightMember signatureEq).elim
      · exact (unique.1 left leftMember signatureEq.symm).elim
      · exact inductionHypothesis unique.2 leftMember rightMember

/-- Validation success exposes the complete canonical entry list. -/
theorem entries_eq_canonical
    {methods : List Method} {table : MethodTable}
    (accepted : MethodTable.validate methods = .ok table) :
    table.entries = canonicalMethodEntries methods := by
  simp only [MethodTable.validate] at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · rename_i first rest entriesEq duplicateEq collisionEq
        injection accepted with tableEq
        rw [← tableEq]
        exact entriesEq.symm

/-- Every accepted entry is an indexed input method. -/
theorem entries_provenance
    {methods : List Method} {table : MethodTable}
    (accepted : MethodTable.validate methods = .ok table)
    {entry : IndexedMethod} (member : entry ∈ table.entries) :
    ∃ method, method ∈ methods ∧ Method.index method = entry := by
  apply mem_canonicalMethodEntries_iff.mp
  rw [← entries_eq_canonical accepted]
  exact member

/-- Accepted entries retain the indexed input multiset exactly. -/
theorem entries_perm_input
    {methods : List Method} {table : MethodTable}
    (accepted : MethodTable.validate methods = .ok table) :
    table.entries.Perm (methods.map Method.index) := by
  rw [entries_eq_canonical accepted]
  exact canonicalMethodEntries_perm methods

/-- An accepted table is nonempty. -/
theorem entries_nonempty (table : MethodTable) : table.entries ≠ [] :=
  table.nonempty

/-- Accepted signatures are pairwise unique. -/
theorem signatures_pairwise (table : MethodTable) :
    table.entries.Pairwise fun left right =>
      left.signature ≠ right.signature :=
  (firstDuplicateSignature?_eq_none_iff table.entries).mp
    table.noDuplicateSignature

/-- Accepted selectors are pairwise unique. -/
theorem selectors_pairwise (table : MethodTable) :
    table.entries.Pairwise fun left right => left.selector ≠ right.selector :=
  (firstSelectorCollision?_eq_none_iff table.entries).mp
    table.noSelectorCollision

/-- Accepted entries remain in canonical signature order. -/
theorem entries_sorted
    {methods : List Method} {table : MethodTable}
    (accepted : MethodTable.validate methods = .ok table) :
    table.entries.Pairwise fun left right =>
      IndexedMethod.signatureLE left right = true := by
  rw [entries_eq_canonical accepted]
  exact canonicalMethodEntries_sorted methods

/-- Successful canonical tables are exactly invariant under input permutation. -/
theorem entries_eq_of_input_perm
    {firstMethods secondMethods : List Method}
    {firstTable secondTable : MethodTable}
    (inputPermutation : firstMethods.Perm secondMethods)
    (firstAccepted : MethodTable.validate firstMethods = .ok firstTable)
    (secondAccepted : MethodTable.validate secondMethods = .ok secondTable) :
    firstTable.entries = secondTable.entries := by
  have entriesPermutation : firstTable.entries.Perm secondTable.entries :=
    (entries_perm_input firstAccepted).trans <|
      (inputPermutation.map Method.index).trans <|
        (entries_perm_input secondAccepted).symm
  apply List.Perm.eq_of_pairwise
      (le := fun left right => IndexedMethod.signatureLE left right = true)
      _ (entries_sorted firstAccepted) (entries_sorted secondAccepted)
      entriesPermutation
  intro left right leftMember rightMember forward backward
  have comparisonEq : compare left.signature right.signature = .eq :=
    Std.OrientedCmp.isLE_antisymm (cmp := compare) forward backward
  have signatureEq : left.signature = right.signature :=
    Std.LawfulEqCmp.eq_of_compare comparisonEq
  exact eq_of_signature_eq_of_mem (signatures_pairwise firstTable)
    leftMember (entriesPermutation.symm.subset rightMember) signatureEq

/-- Reordering input cannot change the validator's rejection class. -/
theorem errorKind_eq_of_input_perm
    {firstMethods secondMethods : List Method}
    {firstError secondError : MethodTableError}
    (inputPermutation : firstMethods.Perm secondMethods)
    (firstRejected : MethodTable.validate firstMethods = .error firstError)
    (secondRejected : MethodTable.validate secondMethods = .error secondError) :
    ErrorKind.ofError firstError = ErrorKind.ofError secondError := by
  have nilIff := canonicalEntriesNil_iff_of_input_perm inputPermutation
  have duplicateNoneIff :=
    duplicateScanNone_iff_of_input_perm inputPermutation
  rcases rejected_classification firstRejected with firstEmpty |
      firstDuplicate | firstCollision <;>
    rcases rejected_classification secondRejected with secondEmpty |
      secondDuplicate | secondCollision
  · exact firstEmpty.1.trans secondEmpty.1.symm
  · exact (secondDuplicate.2.1 (nilIff.mp firstEmpty.2)).elim
  · exact (secondCollision.2.1 (nilIff.mp firstEmpty.2)).elim
  · exact (firstDuplicate.2.1 (nilIff.mpr secondEmpty.2)).elim
  · exact firstDuplicate.1.trans secondDuplicate.1.symm
  · exact (firstDuplicate.2.2
      (duplicateNoneIff.mpr secondCollision.2.2.1)).elim
  · exact (firstCollision.2.1 (nilIff.mpr secondEmpty.2)).elim
  · exact (secondDuplicate.2.2
      (duplicateNoneIff.mp firstCollision.2.2.1)).elim
  · exact firstCollision.1.trans secondCollision.1.symm

/-- One successful ordering yields a successful reordered table with identical
canonical entries. -/
theorem validate_ok_of_input_perm
    {firstMethods secondMethods : List Method} {firstTable : MethodTable}
    (inputPermutation : firstMethods.Perm secondMethods)
    (firstAccepted : MethodTable.validate firstMethods = .ok firstTable) :
    ∃ secondTable,
      MethodTable.validate secondMethods = .ok secondTable ∧
      firstTable.entries = secondTable.entries := by
  have firstNonempty : canonicalMethodEntries firstMethods ≠ [] := by
    rw [← entries_eq_canonical firstAccepted]
    exact firstTable.nonempty
  have secondNonempty : canonicalMethodEntries secondMethods ≠ [] :=
    fun secondNil => firstNonempty
      ((canonicalEntriesNil_iff_of_input_perm inputPermutation).mpr secondNil)
  have firstDuplicateNone :
      firstDuplicateSignature? (canonicalMethodEntries firstMethods) = none := by
    rw [← entries_eq_canonical firstAccepted]
    exact firstTable.noDuplicateSignature
  have secondDuplicateNone :
      firstDuplicateSignature? (canonicalMethodEntries secondMethods) = none :=
    (duplicateScanNone_iff_of_input_perm inputPermutation).mp
      firstDuplicateNone
  have firstSelectorNone :
      firstSelectorCollision? (canonicalMethodEntries firstMethods) = none := by
    rw [← entries_eq_canonical firstAccepted]
    exact firstTable.noSelectorCollision
  have secondSelectorNone :
      firstSelectorCollision? (canonicalMethodEntries secondMethods) = none :=
    (selectorScanNone_iff_of_input_perm inputPermutation).mp firstSelectorNone
  cases secondEq : MethodTable.validate secondMethods with
  | ok secondTable =>
      exact ⟨secondTable, rfl,
        entries_eq_of_input_perm inputPermutation firstAccepted secondEq⟩
  | error secondError =>
      rcases rejected_classification secondEq with empty | duplicate | collision
      · exact (secondNonempty empty.2).elim
      · exact (duplicate.2.2 secondDuplicateNone).elim
      · exact (collision.2.2.2 secondSelectorNone).elim

/-- Validation acceptance is invariant under arbitrary input permutation. -/
theorem validate_accepts_iff_of_input_perm
    {firstMethods secondMethods : List Method}
    (inputPermutation : firstMethods.Perm secondMethods) :
    (∃ table, MethodTable.validate firstMethods = .ok table) ↔
      ∃ table, MethodTable.validate secondMethods = .ok table := by
  constructor
  · rintro ⟨firstTable, firstAccepted⟩
    obtain ⟨secondTable, secondAccepted, _⟩ :=
      validate_ok_of_input_perm inputPermutation firstAccepted
    exact ⟨secondTable, secondAccepted⟩
  · rintro ⟨secondTable, secondAccepted⟩
    obtain ⟨firstTable, firstAccepted, _⟩ :=
      validate_ok_of_input_perm inputPermutation.symm secondAccepted
    exact ⟨firstTable, firstAccepted⟩

end MethodTable

end Solcore.Abi.V1

/-!
## Consolidated module: `Solcore.Abi.StaticWordDispatcher`
-/

/-! Checked Core dispatchers for validated Static Word ABI method tables. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.Core
open Solcore.ContractRuntime

/-- Calldata shorter than one selector and one static word is malformed. -/
def minimumCallDataSize : Word := ⟨36, by decide⟩

/-- The selector occupies the high four bytes of the first calldata word. -/
def selectorRightShift : Word := ⟨224, by decide⟩

/-- Stable revert payload for malformed calldata. -/
def malformedCalldataReason : Word := Word.zero

/-- Stable revert payload for a selector absent from the validated table. -/
def unknownSelectorReason : Word := ⟨1, by decide⟩

/-- Embed the selector's exact big-endian `Fin (2^32)` view into a Core word. -/
def Selector.toWord (selector : Selector) : Word :=
  ⟨selector.toFin.val,
    Nat.lt_trans selector.toFin.isLt (by decide)⟩

private def returned (payload : Expr) : Expr :=
  .inLeft (.sum .word .word) payload

private def reverted (reason : Word) : Expr :=
  .inRight .word (.inLeft .word (.word reason))

private theorem reverted_hasType (context : Context) (reason : Word) :
    HasType context (reverted reason)
      CoreContractEntryProfile.wordOutcomeV1.resultType [] := by
  exact .inRight .word (.inLeft .word .word)

private theorem binaryWordOperands_hasType
    (context : Context) (op : BinaryOp) (left right : Expr)
    (leftTyping : HasType context left .word [])
    (rightTyping : HasType context right .word []) :
    HasType context (.binary op left right) op.resultType [] := by
  apply HasType.binary
  · simpa [BinaryOp.leftType] using leftTyping
  · simpa [BinaryOp.rightType] using rightTyping

/-- Move one method implementation beneath the dispatcher's four locals. -/
private def underDispatcherLocals (implementation : WordImplementation) : Expr :=
  implementation.code.program.body
    |>.weakenAt 0
    |>.weakenAt 0
    |>.weakenAt 0
    |>.weakenAt 0

/-- Route with locals `arg`, `selector`, `selectorWindow`, and `size` at
indices zero through three. Host capabilities therefore begin at index four. -/
private def route : List IndexedMethod → Expr
  | [] => reverted unknownSelectorReason
  | entry :: rest =>
      .ifE
        (.binary .wordEq (.var 1) (.word entry.selector.toWord))
        (returned
          (.apply
            (underDispatcherLocals entry.method.implementation)
            (.var 0)))
        (route rest)

private theorem route_hasType (entries : List IndexedMethod) :
    HasType
      (Ty.word :: Ty.word :: Ty.word :: Ty.word :: hostContext)
      (route entries)
      CoreContractEntryProfile.wordOutcomeV1.resultType [] := by
  induction entries with
  | nil => exact reverted_hasType _ unknownSelectorReason
  | cons entry rest inductionHypothesis =>
      apply HasType.ifE
      · simpa [BinaryOp.resultType] using
          binaryWordOperands_hasType _ .wordEq _ _
            (HasType.var (by simp)) HasType.word
      · apply HasType.inLeft
        · exact .sum .word .word
        · apply HasType.apply
          · have implementationTyping :=
              Program.checkHost_sound entry.method.implementation.code.checked
            rw [entry.method.implementation.resultType_eq,
              entry.method.implementation.dataDefinitions_eq]
              at implementationTyping
            have first := implementationTyping.weakenAt
              (inserted := .word) 0
            have second := first.weakenAt (inserted := .word) 0
            have third := second.weakenAt (inserted := .word) 0
            have fourth := third.weakenAt (inserted := .word) 0
            simpa [underDispatcherLocals, Context.insertAt] using fourth
          · exact HasType.var (by simp)
      · exact inductionHypothesis

/-- Generate the unchecked syntax candidate. The public constructor below
rechecks this exact candidate before exposing executable checked code. -/
def MethodTable.dispatchProgram (table : MethodTable) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.inputDataSize.index) .unit)
      (.ifE
        (.binary .wordGt (.word minimumCallDataSize) (.var 0))
        (reverted malformedCalldataReason)
        (.caseE
          (.apply
            (.var (HostFunction.inputDataWordBE?.index + 1))
            (.word Word.zero))
          (reverted malformedCalldataReason)
          (.letE
            (.binary .wordShr (.var 0) (.word selectorRightShift))
            (.caseE
              (.apply
                (.var (HostFunction.inputDataWordBE?.index + 3))
                (.word ⟨4, by decide⟩))
              (reverted malformedCalldataReason)
              (route table.entries)))))
}

/-- Every dispatcher generated from a validated method table is accepted by
the same ordinary host checker used for handwritten Core programs. -/
theorem MethodTable.dispatchProgram_checked (table : MethodTable) :
    table.dispatchProgram.checkHost = true := by
  apply Program.checkHost_complete
  constructor
  · change DataEnvironment.WellFormed []
    simp [DataEnvironment.WellFormed]
  · exact .sum .word (.sum .word .word)
  · change HasType hostContext table.dispatchProgram.body
      CoreContractEntryProfile.wordOutcomeV1.resultType []
    apply HasType.letE
    · exact HasType.apply
        (HasType.var hostContext_inputDataSize) HasType.unit
    · apply HasType.ifE
      · simpa [BinaryOp.resultType] using
          binaryWordOperands_hasType _ .wordGt _ _
            HasType.word (HasType.var (by simp))
      · exact reverted_hasType _ malformedCalldataReason
      · apply HasType.caseE (leftType := .unit) (rightType := .word)
        · exact HasType.apply (HasType.var (by simpa using
            hostContext_inputDataWordBE?)) HasType.word
        · exact reverted_hasType _ malformedCalldataReason
        · apply HasType.letE
          · simpa [BinaryOp.resultType] using
              binaryWordOperands_hasType _ .wordShr _ _
                (HasType.var (by simp)) HasType.word
          · apply HasType.caseE (leftType := .unit) (rightType := .word)
            · exact HasType.apply (HasType.var (by simpa using
                hostContext_inputDataWordBE?)) HasType.word
            · exact reverted_hasType _ malformedCalldataReason
            · simpa using route_hasType table.entries

/-- Recheck generated syntax under the ordinary host checker and expose an
exact `wordOutcomeV1` contract only after successful admission. -/
def MethodTable.generate? (table : MethodTable) : Option CheckedCoreContract := do
  if checked : table.dispatchProgram.checkHost = true then
    some (CheckedCoreContract.wordOutcomeV1
      ⟨table.dispatchProgram, checked⟩ rfl)
  else
    none

@[simp] theorem MethodTable.generate?_eq_some (table : MethodTable) :
    table.generate? = some
      (CheckedCoreContract.wordOutcomeV1
        ⟨table.dispatchProgram, table.dispatchProgram_checked⟩ rfl) := by
  simp [MethodTable.generate?, table.dispatchProgram_checked]

/-- Total proof-carrying dispatcher generation after table validation. -/
def MethodTable.generate (table : MethodTable) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨table.dispatchProgram, table.dispatchProgram_checked⟩ rfl

end Solcore.Abi.V1

/-!
## Consolidated module: `Solcore.Abi.StaticWordContract`
-/

/-! Admission and balanced top-level execution for Static Word ABI contracts. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.Core
open Solcore.ContractRuntime

/--
A validated Static Word method table paired with exactly the checked dispatcher
generated from that table. The source method list remains in the type, so an
admitted value cannot lose its validation provenance.
-/
structure StaticWordContract (methods : List Method) where
  private mk ::
  table : MethodTable
  table_valid : MethodTable.validate methods = .ok table
  checkedCore : CheckedCoreContract
  checkedCore_eq : checkedCore = table.generate

namespace StaticWordContract

/-- Validate a finite method list and retain the validator's exact error. -/
def admit (methods : List Method) :
    Except MethodTableError (StaticWordContract methods) :=
  match validated : MethodTable.validate methods with
  | .error failure => .error failure
  | .ok table => .ok {
      table := table
      table_valid := validated
      checkedCore := table.generate
      checkedCore_eq := rfl
    }

/-- Admission rejects with precisely the method-table validation error. -/
@[simp] theorem admit_eq_error_iff
    (methods : List Method) (failure : MethodTableError) :
    admit methods = .error failure ↔
      MethodTable.validate methods = .error failure := by
  unfold admit
  split <;> simp_all

/-- One method carrying proof that it belongs to this validated table. -/
structure Member
    {methods : List Method}
    (contract : StaticWordContract methods) where
  private mk ::
  indexed : IndexedMethod
  present : indexed ∈ contract.table.entries

/-- Seal an explicit table-membership proof for use at the call boundary. -/
def member
    {methods : List Method}
    (contract : StaticWordContract methods)
    (indexed : IndexedMethod)
    (present : indexed ∈ contract.table.entries) : contract.Member :=
  ⟨indexed, present⟩

/-- The nonempty validation invariant always exposes one callable member. -/
def firstMember
    {methods : List Method}
    (contract : StaticWordContract methods) : contract.Member :=
  match entriesEq : contract.table.entries with
  | [] => False.elim (contract.table.nonempty entriesEq)
  | first :: _rest =>
      ⟨first, by simp [entriesEq]⟩

/-- Canonical calldata for a selected validated method. -/
def Member.inputData
    {methods : List Method}
    {contract : StaticWordContract methods}
    (selected : contract.Member)
    (argument : Word) : HostStorageDriver.InputData := {
  bytes := encodeCall selected.indexed.selector argument
  size_lt_wordModulus := by
    simp [encodeCall_size, callSize, wordModulus]
}

@[simp] theorem Member.inputData_bytes
    {methods : List Method}
    {contract : StaticWordContract methods}
    (selected : contract.Member)
    (argument : Word) :
    (selected.inputData argument).bytes =
      encodeCall selected.indexed.selector argument := by
  rfl

/-- Construct the exact direct invocation used by the raw ABI entry point. -/
def rawInvocation
    (target caller : Address)
    (callValue : Word)
    (inputData : HostStorageDriver.InputData) : TopLevelInvocation := {
  target := target
  caller := caller
  callValue := callValue
  inputData := inputData
}

/--
Delegate explicit calldata to the sealed balanced top-level runner without
changing its total result type or execution environment.
-/
def runRaw
    {methods : List Method}
    {initialWorld : WorldState}
    (contract : StaticWordContract methods)
    (target caller : Address)
    (callValue : Word)
    (inputData : HostStorageDriver.InputData)
    (installed : InstalledCheckedCoreContract initialWorld target
      contract.checkedCore)
    (environment : ExecutionEnvironment)
    (fuel : Nat) :
    BalancedTopLevelExecution.Result initialWorld contract.checkedCore
      (rawInvocation target caller callValue inputData) :=
  BalancedTopLevelExecution.runWithEnvironment contract.checkedCore
    (rawInvocation target caller callValue inputData) installed environment fuel

/-- Invocation whose selector is sealed by membership in the validated table. -/
def callInvocation
    {methods : List Method}
    {contract : StaticWordContract methods}
    (target caller : Address)
    (callValue : Word)
    (selected : contract.Member)
    (argument : Word) : TopLevelInvocation :=
  rawInvocation target caller callValue (selected.inputData argument)

@[simp] theorem callInvocation_inputData_bytes
    {methods : List Method}
    {contract : StaticWordContract methods}
    (target caller : Address)
    (callValue : Word)
    (selected : contract.Member)
    (argument : Word) :
    (callInvocation target caller callValue selected argument).inputData.bytes =
      encodeCall selected.indexed.selector argument := by
  rfl

/-- Execute canonical calldata for one member of the admitted method table. -/
def run
    {methods : List Method}
    {initialWorld : WorldState}
    (contract : StaticWordContract methods)
    (target caller : Address)
    (callValue : Word)
    (selected : contract.Member)
    (argument : Word)
    (installed : InstalledCheckedCoreContract initialWorld target
      contract.checkedCore)
    (environment : ExecutionEnvironment)
    (fuel : Nat) :
    BalancedTopLevelExecution.Result initialWorld contract.checkedCore
      (callInvocation target caller callValue selected argument) :=
  runRaw contract target caller callValue (selected.inputData argument)
    installed environment fuel

end StaticWordContract

end Solcore.Abi.V1
