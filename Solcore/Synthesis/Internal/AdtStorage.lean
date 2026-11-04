import Solcore.Abi.Keccak256
import Solcore.Synthesis.Internal.Storage
import Solcore.Synthesis.Core.StdDispatch
import Solcore.Synthesis.Internal.Aggregates
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract
import Solcore.Synthesis.Stateful.Sequence

/-!
# Profiles: ADT storage and event logs

The profiles `stateful-adt-storage` and `stateful-logs`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.AdtStorage
/-! A checked contract over enum and struct values in storage, behind the
pinned std's dispatcher. A case's shape fixes an enum of two to four variants,
each with zero to three Word fields or one two-Word struct, and a three-field
record of two Words and that enum at a drawn position. The contract keeps a
Word accumulator at slot zero, an enum field, a record field, and two
mappings from a Word key to the enum and to the record. Its methods write,
clear and read the enum, and write, update one field of and read the record,
each in its field or behind a key.

The layout is computed here from the shape alone, as the pinned std lays out
algebraic values, without std's code: a sum of variants occupies one tag slot
and the larger of its first variant and the sum of the rest, so variant `i`
of `n` writes tag one at its `i` outer levels, tag zero at its own level
unless it is the last, and its payload after them. A product's fields follow
each other. A payload-free write leaves every payload slot as it was. The
mapping entry of key `k` at base slot `b` starts at `keccak256(b ++ k)`,
through the mapping profile's Keccak closure. Every written payload Word at
offset `o` from the written value's first slot holds `r + o·K`, where `r` is
the step of the input plus the accumulator; a read digests the decoded
variant index and payload Words, and an update writes only its field. The
accumulator keeps each method's result, which odd flags revert after the
writes. Two closures, bound once, store and load an enum value at a base
slot; the dispatch, head checks and protocols follow
`Solcore.Synthesis.Core.ContractMethods`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.AdtStorage

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.StdDispatch (noSelectorError truncatedError reject selectorWord readAt)

def version : String := "core-adt-storage-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- A variant's payload: zero to three Word fields, or one two-Word struct. -/
inductive Payload where
  | words (count : Nat)
  | pair
  deriving BEq, Repr, DecidableEq, Inhabited

namespace Payload

def width : Payload → Nat
  | .words count => count
  | .pair => 2

def valid : Payload → Bool
  | .words count => count ≤ 3
  | .pair => true

def name : Payload → String
  | .words count => "words" ++ toString count
  | .pair => "pair"

def all : List Payload := [.words 0, .words 1, .words 2, .words 3, .pair]

def ofName? (name : String) : Option Payload := all.find? (·.name == name)

end Payload

/-- The slots of a right-nested sum of variants: one tag slot and the larger of
the first variant and the sum of the rest; a single variant has no tag. -/
def choiceSize : List Payload → Nat
  | [] => 0
  | [only] => only.width
  | first :: rest => 1 + max first.width (choiceSize rest)

def minVariants : Nat := 2
def maxVariants : Nat := 4
/-- At most four enum slots keep every observed set within the declared-slot
Hull runner's 32 slots. -/
def maxChoiceSlots : Nat := 4
def recordFields : Nat := 3

/-- The source type of every Word field of the declared types; the layout and
the Core reference do not depend on it. -/
inductive WordType where
  | word
  | uint256
  deriving BEq, Repr, DecidableEq, Inhabited

def WordType.name : WordType → String
  | .word => "word"
  | .uint256 => "uint256"

def WordType.ofName? : String → Option WordType
  | "word" => some .word
  | "uint256" => some .uint256
  | _ => none

/-- A case's type shape: the enum's variants, the enum field's position in the
record, whose other two fields are Words, and the Words' source type. -/
structure Shape where
  variants : List Payload
  position : Nat
  wordType : WordType
  deriving BEq, Repr, DecidableEq, Inhabited

def accumulatorSlot : Nat := 0
def choiceSlot : Nat := 1

namespace Shape

def count (shape : Shape) : Nat := shape.variants.length
def choiceSlots (shape : Shape) : Nat := choiceSize shape.variants
def recordSlots (shape : Shape) : Nat := recordFields - 1 + shape.choiceSlots
def width (shape : Shape) (index : Nat) : Nat := (shape.variants.getD index (.words 0)).width

def valid (shape : Shape) : Bool :=
  minVariants ≤ shape.count && shape.count ≤ maxVariants && shape.variants.all Payload.valid &&
    shape.variants.contains (.words 0) && shape.choiceSlots ≤ maxChoiceSlots && shape.position < recordFields

/-- The first payload-free variant, which a clear writes. -/
def clearVariant (shape : Shape) : Nat := (shape.variants.findIdx? (· == .words 0)).getD 0

def fieldSlots (shape : Shape) (field : Nat) : Nat := if field == shape.position then shape.choiceSlots else 1
def fieldOffset (shape : Shape) (field : Nat) : Nat := ((List.range field).map shape.fieldSlots).sum

/-- Fields in declaration order: the accumulator, the enum, the record and the
two mappings, each at the slot after the previous field's slots. -/
def recordSlot (shape : Shape) : Nat := choiceSlot + shape.choiceSlots
def choiceMapSlot (shape : Shape) : Nat := shape.recordSlot + shape.recordSlots
def recordMapSlot (shape : Shape) : Nat := shape.choiceMapSlot + 1

end Shape

/-- The tag Words variant `index` of `count` writes, at their offsets from the
enum's first slot. -/
def tagWrites (count index : Nat) : List (Nat × Nat) :=
  if index + 1 < count then (List.range index).map (fun depth => (depth, 1)) ++ [(index, 0)]
  else (List.range (count - 1)).map (fun depth => (depth, 1))

/-- The offset of variant `index`'s first payload slot. -/
def payloadOffset (count index : Nat) : Nat := if index + 1 < count then index + 1 else count - 1

/-- The odd multiplier that separates written Words by their offsets and
combines decoded Words into a digest. -/
def multiplier : Nat := 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95

/-- The constant added to `r` at offset `offset`. -/
def offsetConstant (offset : Nat) : Nat := offset * multiplier % 2 ^ 256

/-- `K ^ (1 + width)`, the digest weight of a decoded enum of `width` payload Words. -/
def digestScale (width : Nat) : Nat := multiplier ^ (1 + width) % 2 ^ 256

/-- The external methods, in declaration and dispatch order. -/
inductive Method where
  | putChoice | putChoiceAt | clearChoice | clearChoiceAt | getChoice | getChoiceAt
  | putRecord | putRecordAt | setRecord | setRecordAt | getRecord | getRecordAt
  deriving BEq, Repr, DecidableEq, Inhabited

namespace Method

def all : List Method :=
  [.putChoice, .putChoiceAt, .clearChoice, .clearChoiceAt, .getChoice, .getChoiceAt,
    .putRecord, .putRecordAt, .setRecord, .setRecordAt, .getRecord, .getRecordAt]

def ordinal (method : Method) : Nat := all.idxOf method

def name : Method → String
  | .putChoice => "putChoice" | .putChoiceAt => "putChoiceAt"
  | .clearChoice => "clearChoice" | .clearChoiceAt => "clearChoiceAt"
  | .getChoice => "getChoice" | .getChoiceAt => "getChoiceAt"
  | .putRecord => "putRecord" | .putRecordAt => "putRecordAt"
  | .setRecord => "setRecord" | .setRecordAt => "setRecordAt"
  | .getRecord => "getRecord" | .getRecordAt => "getRecordAt"

def ofName? (name : String) : Option Method := all.find? (·.name == name)

def keyed : Method → Bool
  | .putChoiceAt | .clearChoiceAt | .getChoiceAt | .putRecordAt | .setRecordAt | .getRecordAt => true
  | _ => false

/-- The method targets the record, not the enum. -/
def record : Method → Bool
  | .putRecord | .putRecordAt | .setRecord | .setRecordAt | .getRecord | .getRecordAt => true
  | _ => false

def reads : Method → Bool
  | .getChoice | .getChoiceAt | .getRecord | .getRecordAt => true
  | _ => false

def clears : Method → Bool
  | .clearChoice | .clearChoiceAt => true
  | _ => false

def updates : Method → Bool
  | .setRecord | .setRecordAt => true
  | _ => false

def takesVariant (method : Method) : Bool := !method.reads && !method.clears

def parameters (method : Method) : List String :=
  ["flags"] ++ (if method.keyed then ["key"] else []) ++ (if method.updates then ["field"] else []) ++
    (if method.takesVariant then ["variant"] else []) ++ (if method.reads then [] else ["input"])

def arity (method : Method) : Nat := method.parameters.length

def signature (method : Method) : String :=
  method.name ++ "(" ++ ",".intercalate (method.parameters.map fun _ => "uint256") ++ ")"

/-- The first four bytes of the signature's Keccak-256. -/
def selector (method : Method) : Nat :=
  let digest := Solcore.Abi.V1.Keccak256.hash method.signature.toUTF8
  (List.range 4).foldl (fun total index => total * 256 + digest[index]!.toNat) 0

end Method

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index depth : Nat) (argument : Expr) : Expr := .apply (.var (index + depth)) argument
/-- The binder at `position`, counted from the outermost, in a frame of `depth` binders. -/
private def bound (depth position : Nat) : Expr := .var (depth - 1 - position)
private def add (left right : Expr) : Expr := .binary .wordAdd left right
private def mul (left right : Expr) : Expr := .binary .wordMul left right
private def eq (left right : Expr) : Expr := .binary .wordEq left right
private def sload (depth : Nat) (slot : Expr) : Expr := host 0 depth slot
private def sstore (depth : Nat) (slot value : Expr) : Expr := host 1 depth (.pair slot value)

/-- `let` each value in turn, then the body. -/
private def chain : List Expr → Expr → Expr
  | [], body => body
  | value :: rest, body => .letE value (chain rest body)

/-- Outer binders: the hash closure, the step, the enum store and load closures,
the calldata size and the selector Word. -/
private def hashPosition : Nat := 0
private def stepPosition : Nat := 1
private def storePosition : Nat := 2
private def loadPosition : Nat := 3
private def sizePosition : Nat := 4
private def selectorPosition : Nat := 5
private def outerDepth : Nat := 6

/-- Inside the store closure: its argument, then the base slot, the variant and
the value Word. -/
private def storeBase : Nat := 3
private def storeVariant : Nat := 4
private def storeValue : Nat := 5
private def storeDepth : Nat := 6

/-- One store per pair of offset and Word (a tag, or the value plus the
offset's constant), each bound in turn, ending in Unit. -/
private def stores : List (Nat × Option Nat) → Nat → Expr
  | [], _ => .unit
  | (offset, tag) :: rest, depth =>
      let value := match tag with
        | some tag => word tag
        | none => add (bound depth storeValue) (word (offsetConstant offset))
      .letE (sstore depth (add (bound depth storeBase) (word offset)) value) (stores rest (depth + 1))

/-- The tag and payload stores of variant `index`. -/
private def variantStores (shape : Shape) (index : Nat) : Expr :=
  let offset := payloadOffset shape.count index
  stores ((tagWrites shape.count index).map (fun (place, tag) => (place, some tag)) ++
    (List.range (shape.width index)).map fun field => (offset + field, none)) storeDepth

/-- `fun (base, (variant, value)) => ...`: variant `variant` compared in
declaration order, the last taking every other Word. -/
def storeClosure (shape : Shape) : Expr :=
  .lambda (.product .word (.product .word .word)) .unit
    (chain [.first (.var 0), .first (.second (.var 1)), .second (.second (.var 2))]
      ((List.range (shape.count - 1)).foldr (fun index rest =>
          .ifE (eq (bound storeDepth storeVariant) (word index)) (variantStores shape index) rest)
        (variantStores shape (shape.count - 1))))

/-- Inside the load closure: its argument, the base slot. -/
private def loadBase : Nat := 3
private def loadDepth : Nat := 4

/-- Variant `index` decoded: the digest of its index and payload Words, and
the digest weight of that many Words. -/
private def decoded (shape : Shape) (index : Nat) : Expr :=
  let offset := payloadOffset shape.count index
  .pair ((List.range (shape.width index)).foldl (fun total field =>
      add (mul total (word multiplier)) (sload loadDepth (add (bound loadDepth loadBase) (word (offset + field)))))
    (word index))
    (word (digestScale (shape.width index)))

/-- `fun base => (digest, weight)`: a zero tag at level `i` selects variant
`i`; past every level the last variant. -/
def loadClosure (shape : Shape) : Expr :=
  .lambda .word (.product .word .word)
    ((List.range (shape.count - 1)).foldr (fun index rest =>
        .ifE (eq (sload loadDepth (add (bound loadDepth loadBase) (word index))) (word 0)) (decoded shape index) rest)
      (decoded shape (shape.count - 1)))

/-- The odd-flags completion: revert or return the result. -/
private def completion (depth flags : Nat) (result : Expr) : Expr :=
  .ifE (eq (.binary .wordAnd (bound depth flags) (word 1)) (word 1))
    (.inRight .word (.inLeft .word result))
    (.inLeft (.sum .word .word) result)

private def parameterPosition (method : Method) (parameter : String) : Nat :=
  outerDepth + method.parameters.idxOf parameter

/-- The value's base slot: its field's slot, or the binder of the key's entry. -/
private def baseAt (shape : Shape) (method : Method) (entry : Nat) (depth : Nat) : Expr :=
  if method.keyed then bound depth entry
  else word (if method.record then shape.recordSlot else choiceSlot)

private def entryBinder (shape : Shape) (method : Method) (depth : Nat) : List Expr :=
  if method.keyed then
    [.apply (bound depth hashPosition) (.pair (word (if method.record then shape.recordMapSlot else shape.choiceMapSlot))
      (bound depth (parameterPosition method "key")))]
  else []

/-- Field `field` of the record at `base`, written with `r` as `putRecord` writes it. -/
private def fieldStore (shape : Shape) (method : Method) (field depth : Nat) (base : Nat → Expr) (result : Nat) : Expr :=
  let offset := shape.fieldOffset field
  let value := add (bound depth result) (word (offsetConstant offset))
  if field == shape.position then
    .apply (bound depth storePosition)
      (.pair (add (base depth) (word offset)) (.pair (bound depth (parameterPosition method "variant")) value))
  else sstore depth (add (base depth) (word offset)) value

/-- A writing method: `r = step(input + slot 0)`, the entry slot if keyed,
the writes, the accumulator, and the completion. -/
private def writeProtocol (shape : Shape) (method : Method) : Expr :=
  let start := outerDepth + method.arity
  let result := start
  let entry := start + 1
  let writing := if method.keyed then start + 2 else start + 1
  let base := baseAt shape method entry
  let writes : Expr :=
    if method.record then
      if method.updates then
        let field := bound writing (parameterPosition method "field")
        .ifE (eq field (word 0)) (fieldStore shape method 0 writing base result)
          (.ifE (eq field (word 1)) (fieldStore shape method 1 writing base result)
            (fieldStore shape method 2 writing base result))
      else
        chain ((List.range recordFields).map fun field => fieldStore shape method field (writing + field) base result) .unit
    else
      let variant := if method.clears then word shape.clearVariant
        else bound writing (parameterPosition method "variant")
      .apply (bound writing storePosition) (.pair (base writing) (.pair variant (bound writing result)))
  chain ([.apply (bound start stepPosition)
      (add (bound start (parameterPosition method "input")) (sload start (word accumulatorSlot)))] ++
      entryBinder shape method (start + 1) ++
      [writes, sstore (writing + 1) (word accumulatorSlot) (bound (writing + 1) result)])
    (completion (writing + 2) (parameterPosition method "flags") (bound (writing + 2) result))

/-- A reading method: the entry slot if keyed, the decoded enum, the digest,
the accumulator, and the completion. The record's digest combines its Words
and the enum's digest in field order. -/
private def readProtocol (shape : Shape) (method : Method) : Expr :=
  let start := outerDepth + method.arity
  let entry := start
  let loading := if method.keyed then start + 1 else start
  let base := baseAt shape method entry
  let loaded := .apply (bound loading loadPosition)
    (if method.record then add (base loading) (word (shape.fieldOffset shape.position)) else base loading)
  let digesting := loading + 1
  let digest : Expr :=
    if method.record then
      (List.range recordFields).foldl (fun total field =>
          if field == shape.position then
            add (mul total (.second (bound digesting loading))) (.first (bound digesting loading))
          else add (mul total (word multiplier))
            (sload digesting (add (base digesting) (word (shape.fieldOffset field)))))
        (word 0)
    else .first (bound digesting loading)
  chain (entryBinder shape method start ++
      [loaded, digest, sstore (digesting + 1) (word accumulatorSlot) (bound (digesting + 1) digesting)])
    (completion (digesting + 2) (parameterPosition method "flags") (bound (digesting + 2) digesting))

/-- Method `method`: std's head check, its Word arguments, then its protocol. -/
private def methodBody (shape : Shape) (method : Method) : Expr :=
  .ifE (.binary .wordGt (word (4 + 32 * method.arity)) (bound outerDepth sizePosition)) (reject truncatedError)
    (chain ((List.range method.arity).map fun index => readAt (outerDepth + index) (word (4 + 32 * index)))
      (if method.reads then readProtocol shape method else writeProtocol shape method))

/-- Compare the selector Word with each declared method's selector in
declaration order; the first match runs and no match is rejected. -/
private def dispatch (shape : Shape) : List Method → Expr
  | [] => reject noSelectorError
  | method :: rest =>
      .ifE (eq (bound outerDepth selectorPosition) (word method.selector)) (methodBody shape method) (dispatch shape rest)

private def contractExpression (shape : Shape) (methods : List Method) (stepBody : Expr) : Expr :=
  chain [Solcore.Synthesis.Core.StorageMapping.hashClosure, stepBody, storeClosure shape, loadClosure shape,
      host 7 4 .unit]
    (.ifE (.binary .wordGt (word 4) (.var 0)) (reject noSelectorError)
      (.letE (selectorWord 5) (dispatch shape methods)))

def canonicalProgram (shape : Shape) (methods : List Method) (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression shape methods step.program.body
}

/-- The fixed Keccak closure, which lies outside a case's node budget. -/
abbrev hashNodes : Nat := Solcore.Synthesis.Core.StorageMapping.hashNodes

/-- The two enum closures of a shape, which lie outside a case's node budget. -/
def closureNodes (shape : Shape) : Nat := exprNodes (storeClosure shape) + exprNodes (loadClosure shape)

private def placeholderNodes (shape : Shape) (methods : List Method) : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression shape methods (word 0)}

private def stepPlaceholderNodes : Nat :=
  programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

/-- The selector comparisons, head checks and protocols of the declared
methods, which lie outside a case's node budget. -/
def methodNodes (shape : Shape) (methods : List Method) : Nat :=
  placeholderNodes shape methods - placeholderNodes shape []

/-- Syntax-only measurement of the shell without methods, the closures and the
step, using a one-node placeholder step that is never admitted or run, as the
mapping profile measures its overhead. It is the same for every shape and lies
inside a case's node budget. -/
def shellNodes : Nat :=
  let shape : Shape := {variants := [.words 0, .words 0], position := 0, wordType := .word}
  placeholderNodes shape [] - stepPlaceholderNodes - hashNodes - closureNodes shape

/-- Every valid variant list of `count` variants, in a fixed order: the
payloads of each variant in `Payload.all` order, the first variant varying
slowest. -/
def variantLists (count : Nat) : List (List Payload) :=
  ((List.range count).foldr (fun _ rest => Payload.all.flatMap fun payload => rest.map (payload :: ·)) [[]]).filter
    fun variants => ({variants, position := 0, wordType := .word} : Shape).valid

/-- Every valid shape, by variant count, variant list, position and type. -/
def allShapes : List Shape :=
  (List.range (maxVariants - minVariants + 1)).flatMap fun extra =>
    (variantLists (minVariants + extra)).flatMap fun variants =>
      (List.range recordFields).flatMap fun position => [WordType.word, .uint256].map fun wordType =>
        {variants, position, wordType}

/-- The largest closures and methods of any valid shape with every method;
tests recompute it over `allShapes`. -/
def maxOutsideNodes : Nat := 1263

/-- The declared methods: one to twelve distinct methods in declaration order. -/
def validMethods (methods : List Method) : Bool :=
  !methods.isEmpty && methods == Method.all.filter methods.contains

structure CheckedPlan where private mk ::
  shape : Shape
  methods : List Method
  keyBase : Word
  step : Aggregates.CheckedDAG
  shaped : shape.valid = true
  declared : validMethods methods = true
  checked : (canonicalProgram shape methods step).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.shape plan.methods plan.step

def ofParts? (shape : Shape) (methods : List Method) (keyBase : Word) (step : Aggregates.CheckedDAG) :
    Option CheckedPlan :=
  if shaped : shape.valid = true then
    if declared : validMethods methods = true then
      if checked : (canonicalProgram shape methods step).check = true then
        some ⟨shape, methods, keyBase, step, shaped, declared, checked⟩
      else none
    else none
  else none

/-- The two keys of the case: the key base and the next Word. -/
def keys (plan : CheckedPlan) : List Word := [plan.keyBase, Word.ofNatModulo (plan.keyBase.val + 1)]

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

theorem hostChecked (plan : CheckedPlan) : plan.program.toCore.checkHost = true :=
  Program.check_promotes_current plan.checked

def code (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.program.toCore, plan.hostChecked⟩

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.code rfl

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

end CheckedPlan
end Solcore.Synthesis.Core.AdtStorage
end

section
-- leanmerge: from Solcore.Synthesis.Core.EventLog
/-! A checked event-log protocol around a closed aggregate step. The ABI
supplies a flags Word and an input Word. The contract writes the step result
to slot zero and a counter to slot one, then runs up to three static log sites.
A site whose guard bit is set in the flags applies the step once more and
emits one log with zero to four topics and zero to two data Words.

Core's host interface offers one log primitive, `emitLogWord`, carrying one
topic Word and one payload Word. Each site is therefore written as a frame of
word logs under `framingVersion`: a header naming the topic count and data
length, the data Words, then the topics. The observer decodes committed
journals into multi-topic logs; the frame is a convention of this profile and
not a Core log semantics. The original flags parity then selects return or
revert, and the public contract runtime commits or discards the working world
and journal together. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.EventLog

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-event-log-contract-v1"
def framingVersion : String := "core-word-log-framing-v1"
def resultType : Ty := .sum .word (.sum .word .word)

def maxSites : Nat := 3
def maxTopics : Nat := 4
def maxDataWords : Nat := 2

/-- One static log site. `guard` names the flags bit that enables it,
`topics` the log's topic count and `dataWords` its data length in Words. -/
structure Site where
  guard : Nat
  topics : Nat
  dataWords : Nat
  deriving Repr, BEq, DecidableEq

/-- At most three sites, guards one to three in strictly increasing order, at
most four topics and two data Words each. Removing a site keeps the others'
guards, so their emissions do not move to another flags bit. -/
def validSites (sites : List Site) : Bool :=
  sites.length ≤ maxSites &&
    sites.all (fun site => 1 ≤ site.guard && site.guard ≤ 3 &&
      site.topics ≤ maxTopics && site.dataWords ≤ maxDataWords) &&
    (sites.zip (sites.drop 1)).all fun (left, right) => left.guard < right.guard

/-- Frame tags. The header carries payload zero; data and topic records are
numbered from one in emission order. -/
def headerTag (site : Site) : Nat := 256 + 16 * site.dataWords + site.topics
def dataTag (index : Nat) : Nat := 512 + index
def topicTag (index : Nat) : Nat := 768 + index

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- The binder at `position`, counted from the outermost, in a frame with
`depth` binders. -/
private def bound (depth position : Nat) : Expr := .var (depth - 1 - position)
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

private def stepPosition : Nat := 0
private def flagsPosition : Nat := 1
private def inputPosition : Nat := 2
private def oldPosition : Nat := 3
private def countPosition : Nat := 4
private def basePosition : Nat := 5
private def resultPosition : Nat := 6
/-- Binders before the first site: the step, flags, input, both reads, the
base, the result and the two Unit writes. -/
private def siteDepth : Nat := 9

/-- Header, data Words and topics of one site. Each payload is built at the
depth where its record is bound; `value` is the site's own binder. -/
def frame (site : Site) (value : Nat) : List (Nat × (Nat → Expr)) :=
  [(headerTag site, fun _ => word 0)] ++
    ((List.range site.dataWords).map fun index =>
      (dataTag (index + 1), fun depth => bound depth (if index = 0 then value else resultPosition))) ++
    ((List.range site.topics).map fun index =>
      (topicTag (index + 1), fun depth => .binary .wordAdd (bound depth value) (word (index + 1))))

def emitRecords (depth : Nat) : List (Nat × (Nat → Expr)) → Expr
  | [] => .unit
  | (tag, payload) :: rest =>
      .letE (host 13 depth (.pair (word tag) (payload depth))) (emitRecords (depth + 1) rest)

/-- A guarded site binds `step(result + guard)` and then its frame records. -/
def siteExpression (depth : Nat) (site : Site) : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (bound depth flagsPosition) (word (2 ^ site.guard)))
      (word (2 ^ site.guard)))
    (.letE (.apply (bound depth stepPosition)
        (.binary .wordAdd (bound depth resultPosition) (word site.guard)))
      (emitRecords (depth + 1) (frame site depth)))
    .unit

private def completion (depth : Nat) : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (bound depth flagsPosition) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (bound depth resultPosition)))
    (.inLeft (.sum .word .word) (bound depth resultPosition))

def withSites (depth : Nat) : List Site → Expr
  | [] => completion depth
  | site :: rest => .letE (siteExpression depth site) (withSites (depth + 1) rest)

/-- Every host application names its exact local depth. Both writes precede
every log, and every log precedes the completion. -/
def contractExpression (stepBody : Expr) (sites : List Site) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (host 0 3 (word 0))
          (.letE (host 0 4 (word 1))
            (.letE (.binary .wordAdd (bound 5 inputPosition) (bound 5 oldPosition))
              (.letE (.apply (bound 6 stepPosition) (bound 6 basePosition))
                (.letE (host 1 7 (.pair (word 0) (bound 7 resultPosition)))
                  (.letE (host 1 8 (.pair (word 1) (.binary .wordAdd (bound 8 countPosition) (word 1))))
                    (withSites siteDepth sites)))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) (sites : List Site) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body sites
}

/-- Syntax-only overhead measurement; the placeholder is never admitted or run. -/
def programOverhead (sites : List Site) : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0) sites} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  sites : List Site
  sitesValid : validSites sites = true
  checked : (canonicalProgram step sites).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.sites

def ofParts? (step : Aggregates.CheckedDAG) (sites : List Site) : Option CheckedPlan :=
  if sitesValid : validSites sites = true then
    if checked : (canonicalProgram step sites).check = true then some ⟨step, sites, sitesValid, checked⟩
    else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

theorem hostChecked (plan : CheckedPlan) : plan.program.toCore.checkHost = true :=
  Program.check_promotes_current plan.checked

def code (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.program.toCore, plan.hostChecked⟩

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.code rfl

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

end CheckedPlan
end Solcore.Synthesis.Core.EventLog
end

section
-- leanmerge: from Solcore.Synthesis.Source.AdtStorageEmitter
/-! Emit the enum and struct storage contract. The module declares `ScPair`
when a variant carries it, the enum `ScChoice` and the record `ScRecord`, with
the shape's Word type for every Word field, and std's `StorageGeneric` derives
their layouts; the source never computes a slot. The contract declares the
accumulator, the enum and record fields and the two mappings, and the case's
methods in declaration order. A method converts its parameters, computes the
step of the input plus the accumulator, and branches on the variant and the
field in nested `if`/`else`. Its values are constructor applications of the
step result plus literal offsets; reads `match` the value with one arm per
variant and nested patterns. A mapping entry's field update matches the entry
and writes a whole record, since the pinned front end rejects a field
assignment through a mapping index. This implementation is separate from the
original Core contract's slot arithmetic. No emitter proof covers this
wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AdtStorage

open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.AdtStorage (CheckedPlan Method Shape Payload WordType payloadOffset offsetConstant multiplier)

def emitterVersion : String := "solcore-source-adt-storage-v1"
def wrapperVersion : String := "solcore-word-adt-storage-contract-v1"
def contractName : String := "SynthesizedAdtStorage"
def deployPath : List String := ["SynthesizedAdtStorageDeploy"]
def runtimePath : List String := ["SynthesizedAdtStorageDeploy", "SynthesizedAdtStorage"]

/-- The emitted source of an enum and struct storage contract; its methods are the case's. -/
structure EmittedAdtStorage where
  source : String
  contractName : String
  deployPath : List String
  runtimePath : List String
  deriving Repr, BEq

private def hexLiteral (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

/-- A Word expression as a field value of the shape's Word type. -/
private def wrapped (shape : Shape) (expression : String) : String :=
  match shape.wordType with
  | .word => expression
  | .uint256 => "uint256(" ++ expression ++ ")"

/-- A bound field value of the shape's Word type as a Word expression. -/
private def unwrapped (shape : Shape) (name : String) : String :=
  match shape.wordType with
  | .word => name
  | .uint256 => "Typedef.rep(" ++ name ++ ")"

/-- The value written at offset `offset` of the written value: `r + offset·K`. -/
private def valueAt (shape : Shape) (offset : Nat) : String :=
  wrapped shape (if offset == 0 then "sc_r" else "(sc_r + " ++ hexLiteral (offsetConstant offset) ++ ")")

/-- Variant `index` applied to its payload arguments, or as a pattern over names. -/
private def construct (shape : Shape) (index : Nat) (arguments : List String) : String :=
  let name := "ScChoice.V" ++ toString index
  match shape.variants.getD index (.words 0) with
  | .words 0 => name
  | .words _ => name ++ "(" ++ ", ".intercalate arguments ++ ")"
  | .pair => name ++ "(ScPair(" ++ ", ".intercalate arguments ++ "))"

/-- Variant `index` written as part of a value whose first slot lies `origin`
slots before the enum's first slot. -/
private def constructAt (shape : Shape) (index origin : Nat) : String :=
  construct shape index ((List.range (shape.width index)).map fun field =>
    valueAt shape (origin + payloadOffset shape.count index + field))

/-- The record written with its enum field's variant `index`. -/
private def recordValue (shape : Shape) (index : Nat) : String :=
  "ScRecord(" ++ ", ".intercalate ((List.range AdtStorage.recordFields).map fun field =>
    if field == shape.position then constructAt shape index (shape.fieldOffset field)
    else valueAt shape (shape.fieldOffset field)) ++ ")"

/-- Horner's rule over Word expressions with the multiplier, from zero. -/
private def digest (tokens : List String) : String :=
  match tokens with
  | [] => "0"
  | first :: rest => rest.foldl (fun total token => "((" ++ total ++ " * " ++ hexLiteral multiplier ++ ") + " ++ token ++ ")")
      first

/-- Nested `if`/`else` over `selector` for `count` branches, the last taking
every other Word. -/
private def branches (selector : String) (count indent : Nat) (branch : Nat → List String) : List String :=
  let pad := String.ofList (List.replicate indent ' ')
  let rec go (index fuel depth : Nat) : List String :=
    match fuel with
    | 0 => (branch index).map (pad ++ String.ofList (List.replicate (4 * depth) ' ') ++ ·)
    | fuel + 1 =>
        let inner := pad ++ String.ofList (List.replicate (4 * depth) ' ')
        [inner ++ "if (" ++ selector ++ " == " ++ toString index ++ ") {"] ++
          (branch index).map (inner ++ "    " ++ ·) ++ [inner ++ "} else {"] ++
          go (index + 1) fuel (depth + 1) ++ [inner ++ "}"]
  go 0 (count - 1) 0

private def completion (result : String) : List String :=
  ["        acc = " ++ result ++ ";",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, " ++ result ++ ");",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(" ++ result ++ ");"]

private def header (method : Method) : List String :=
  ["    function " ++ method.name ++ "(" ++ ", ".intercalate (method.parameters.map (· ++ ": uint256")) ++
      ") public returns (uint256) {"] ++
    ((method.parameters.filter (· != "input")).map fun parameter =>
      "        let sc_" ++ parameter ++ ": word = Typedef.rep(" ++ parameter ++ ");") ++
    (if method.reads then [] else ["        let sc_r: word = sc_step((Typedef.rep(input) + acc));"])

/-- The match arms of a decoded enum, each assigning its digest. -/
private def choiceArms (shape : Shape) (target : String) : List String :=
  ["        let sc_digest: word = 0;", "        match (" ++ target ++ ") {"] ++
    ((List.range shape.count).flatMap fun index =>
      let names := (List.range (shape.width index)).map fun field => "sc_a" ++ toString field
      ["            case " ++ construct shape index names ++ " {",
        "                sc_digest = " ++ digest ([toString index] ++ names.map (unwrapped shape)) ++ ";",
        "            }"]) ++ ["        }"]

/-- The match arms of a decoded record, one per variant of its enum field. -/
private def recordArms (shape : Shape) (target : String) : List String :=
  ["        let sc_digest: word = 0;", "        match (" ++ target ++ ") {"] ++
    ((List.range shape.count).flatMap fun index =>
      let names := (List.range (shape.width index)).map fun field => "sc_a" ++ toString field
      let fields := (List.range AdtStorage.recordFields).map fun field =>
        if field == shape.position then (construct shape index names, [toString index] ++ names.map (unwrapped shape))
        else ("sc_x" ++ toString field, [unwrapped shape ("sc_x" ++ toString field)])
      ["            case ScRecord(" ++ ", ".intercalate (fields.map Prod.fst) ++ ") {",
        "                sc_digest = " ++ digest (fields.flatMap Prod.snd) ++ ";",
        "            }"]) ++ ["        }"]

/-- The writes of field `field`, through `assign` of each new field value. -/
private def fieldUpdate (shape : Shape) (field : Nat) (assign : String → String) : List String :=
  let offset := shape.fieldOffset field
  if field == shape.position then
    branches "sc_variant" shape.count 0 fun index => [assign (constructAt shape index offset)]
  else [assign (valueAt shape offset)]

private def fieldBranches (shape : Shape) (indent : Nat) (assign : Nat → String → String) : List String :=
  branches "sc_field" AdtStorage.recordFields indent fun field => fieldUpdate shape field (assign field)

private def methodLines (shape : Shape) (method : Method) : List String :=
  let choice := if method.keyed then "choices[sc_key]" else "choice"
  let record := if method.keyed then "records[sc_key]" else "record"
  let body : List String :=
    match method with
    | .putChoice | .putChoiceAt =>
        branches "sc_variant" shape.count 8 (fun index => [choice ++ " = " ++ constructAt shape index 0 ++ ";"]) ++
          completion "sc_r"
    | .clearChoice | .clearChoiceAt =>
        ["        " ++ choice ++ " = " ++ construct shape shape.clearVariant [] ++ ";"] ++ completion "sc_r"
    | .getChoice | .getChoiceAt => choiceArms shape choice ++ completion "sc_digest"
    | .putRecord | .putRecordAt =>
        branches "sc_variant" shape.count 8 (fun index => [record ++ " = " ++ recordValue shape index ++ ";"]) ++
          completion "sc_r"
    | .setRecord =>
        fieldBranches shape 8 (fun field value => "record.f" ++ toString field ++ " = " ++ value ++ ";") ++
          completion "sc_r"
    | .setRecordAt =>
        let bound := (List.range AdtStorage.recordFields).map fun field => "sc_x" ++ toString field
        let replaced := fun (field : Nat) (value : String) =>
          record ++ " = ScRecord(" ++ ", ".intercalate (bound.zipIdx.map fun (name, index) =>
            if index == field then value else name) ++ ");"
        ["        match (" ++ record ++ ") {", "            case ScRecord(" ++ ", ".intercalate bound ++ ") {"] ++
          fieldBranches shape 16 replaced ++ ["            }", "        }"] ++ completion "sc_r"
    | .getRecord | .getRecordAt => recordArms shape record ++ completion "sc_digest"
  header method ++ body ++ ["    }"]

/-- The type declarations, the Word type for every Word field. -/
private def typeLines (shape : Shape) : List String :=
  let type := shape.wordType.name
  let pair := if shape.variants.contains .pair then
      ["struct ScPair {", "    a: " ++ type ++ ";", "    b: " ++ type ++ ";", "}", ""]
    else []
  let variants := (List.range shape.count).map fun index =>
    "    V" ++ toString index ++
      match shape.variants.getD index (.words 0) with
      | .words 0 => ""
      | .words count => "(" ++ ", ".intercalate (List.replicate count type) ++ ")"
      | .pair => "(ScPair)"
  pair ++ ["enum ScChoice {"] ++ (variants.zipIdx.map fun (line, index) =>
      if index + 1 < variants.length then line ++ "," else line) ++ ["}", "",
    "struct ScRecord {"] ++ ((List.range AdtStorage.recordFields).map fun field =>
      "    f" ++ toString field ++ ": " ++ (if field == shape.position then "ScChoice" else type) ++ ";") ++ ["}", ""]

def emit (plan : CheckedPlan) : Except EmitError EmittedAdtStorage := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", "import * from std.Generic;",
    "import * from std.StorageGeneric;",
    AggregateRenderer.opcodeImportWith ["mstore", "revert_"] (plan.step.helpers ++ [plan.step.entry]), ""] ++
    typeLines plan.shape
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    acc: word;",
    "    choice: ScChoice;",
    "    record: ScRecord;",
    "    choices: mapping(word => ScChoice);",
    "    records: mapping(word => ScRecord);"]
  for method in plan.methods do
    lines := lines ++ [""] ++ methodLines plan.shape method
  lines := lines ++ ["}"]
  return {source := String.intercalate "\n" lines ++ "\n", contractName, deployPath, runtimePath}

end Solcore.Synthesis.Source.AdtStorage
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.AdtStorageExecution
/-! Execute the original checked enum and struct storage contract over a
persistent account world. A transaction calls one declared method with its
Word arguments in canonical calldata: the flags, then the key, the record
field and the variant where the method takes them, then the input unless it
reads. The observed slots are the accumulator, the enum and record fields'
slots and the entry slots of both mappings at the case's two keys, derived
with the separate `Solcore.Abi.V1.Keccak256` rather than the Core builders the
contract runs.

`model` is a second reading of the emitted source over a slot map: a write
stores its variant's tags and payload at the layout's offsets, a clear writes
the payload-free variant's tags alone, an update writes its field alone and a
read decodes the tags from the outermost level. It evaluates the step's Core
alone at each argument and shares nothing with the contract but that step and
the layout's sizes. Tests compare the two; neither is an oracle for the
differential paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.AdtStorageExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.AdtStorage (CheckedPlan Method Shape Payload)

def historySchema : String := "solcore-lean.adt-storage-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- A call of one method. Arguments the method does not take are zero. -/
structure Transaction where
  id : String
  method : Method
  flags : Word
  key : Word
  field : Nat
  variant : Nat
  input : Word
  deriving BEq

/-- The Word of each of the method's parameters, in order. -/
def arguments (tx : Transaction) : List Word :=
  tx.method.parameters.map fun
    | "key" => tx.key
    | "field" => Word.ofNatModulo tx.field
    | "variant" => Word.ofNatModulo tx.variant
    | "input" => tx.input
    | _ => tx.flags

/-- A transaction fits a plan when it calls a declared method, names one of the
case's keys, a record field and a variant of the shape where the method takes
them, and leaves every other argument zero. -/
def Transaction.valid (tx : Transaction) (plan : CheckedPlan) : Bool :=
  plan.methods.contains tx.method &&
    (if tx.method.keyed then plan.keys.contains tx.key else tx.key == Word.zero) &&
    (if tx.method.updates then tx.field < AdtStorage.recordFields else tx.field == 0) &&
    (if tx.method.takesVariant then tx.variant < plan.shape.count else tx.variant == 0) &&
    (!tx.method.reads || tx.input == Word.zero)

private def selectorBytes (selector : Nat) : ByteArray :=
  ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

/-- The canonical calldata: the method's selector, then each argument Word. -/
def inputBytes (tx : Transaction) : ByteArray :=
  (arguments tx).foldl (fun bytes value => bytes ++ encodeWordBytesBE value) (selectorBytes tx.method.selector)

def calldata (tx : Transaction) : String := encodeBytesText (inputBytes tx)

def inputData? (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

/-- The pinned std's first slot of `m[key]` for a mapping at base slot `base`:
`keccak256(base ++ key)`, from the independent ABI Keccak. -/
def entrySlot (base : Nat) (key : Word) : Word :=
  (decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash
    (encodeWordBytesBE (Word.ofNatModulo base) ++ encodeWordBytesBE key))).getD Word.zero

/-- `count` consecutive slots from `first`, wrapping as slot arithmetic does. -/
def region (first : Word) (count : Nat) : List Word :=
  (List.range count).map fun offset => first + Word.ofNatModulo offset

private def insertSlot (slot : Word) : List Word → List Word
  | [] => [slot]
  | head :: tail =>
      if slot.val < head.val then slot :: head :: tail
      else if slot.val = head.val then head :: tail
      else head :: insertSlot slot tail

/-- The accumulator, the enum and record fields' slots, and each key's entry
slots in both mappings, in increasing numeric order without duplicates: every
slot the protocol writes, stale payload slots included. -/
def observedSlots (shape : Shape) (keys : List Word) : List Word :=
  ([Word.ofNatModulo AdtStorage.accumulatorSlot] ++
      region (Word.ofNatModulo AdtStorage.choiceSlot) shape.choiceSlots ++
      region (Word.ofNatModulo shape.recordSlot) shape.recordSlots ++
      keys.flatMap (fun key =>
        region (entrySlot shape.choiceMapSlot key) shape.choiceSlots ++
          region (entrySlot shape.recordMapSlot key) shape.recordSlots)).foldl
    (fun slots slot => insertSlot slot slots) []

def planSlots (plan : CheckedPlan) : List Word := observedSlots plan.shape plan.keys

private def worldStorage (world : WorldState) (bindings : Bindings) (slots : List Word) : Json :=
  match world.account? bindings.address with
  | some account => KeyedStorageExecution.storageJson account slots
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation, as for the storage profiles, with
each transaction's calldata selecting its method. -/
def observeContract (contract : CheckedCoreContract) (slots : List Word) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings slots
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match inputData? transaction, registry.resolve? prior bindings.address with
      | none, _ =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "input-limit"), ("committedStorage", worldStorage prior bindings slots),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | _, none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings slots),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some input, some ⟨resolved, installed⟩ =>
          let invocation : TopLevelInvocation := {
            target := bindings.address, caller := bindings.caller,
            callValue := Word.zero, inputData := input }
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings slots),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
              match terminal.outcome with
              | .trapped _ => stopped := some transaction.id
              | _ => pure ()
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings slots),
                ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", KeyedStorageExecution.slotsJson slots),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings slots),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract (planSlots plan) transactions bindings fuel

/-- The step's own Core result at one argument. -/
def stepResult (step : Aggregates.CheckedDAG) (fuel : Nat) (argument : Word) : Option Word :=
  match (step.instantiate argument).toCore.runStateful fuel with
  | .done (.word value) _ => some value
  | _ => none

/-- One modelled transaction: whether it reverts, its result Word and the
slots it leaves committed as `(slot, value)` pairs. -/
structure ModelRow where
  reverted : Bool
  result : Word
  storage : List (Word × Word)
  deriving BEq

private def lookup (storage : List (Word × Word)) (slot : Word) : Word :=
  ((storage.find? fun (candidate, _) => candidate == slot).map Prod.snd).getD Word.zero

private def update (storage : List (Word × Word)) (slot value : Word) : List (Word × Word) :=
  (slot, value) :: storage.filter fun (candidate, _) => candidate != slot

private def multiplier : Word := Word.ofNatModulo AdtStorage.multiplier

/-- The Word written at offset `offset` of a value written with `result`. -/
private def written (result : Word) (offset : Nat) : Word := result + Word.ofNatModulo offset * multiplier

/-- Variant `variant` of the shape's enum written at `first`: one at each outer
level, zero at its own level unless it is the last variant, then its payload,
each payload Word at offset `o` from `origin` holding `result + o·K`. -/
private def writeChoice (shape : Shape) (storage : List (Word × Word)) (first : Word) (origin variant : Nat)
    (result : Word) : List (Word × Word) := Id.run do
  let count := shape.count
  let mut current := storage
  for level in List.range (min variant (count - 1)) do
    current := update current (first + Word.ofNatModulo level) (Word.ofNatModulo 1)
  let payload := if variant + 1 < count then
      (update current (first + Word.ofNatModulo variant) Word.zero, variant + 1)
    else (current, count - 1)
  current := payload.1
  for index in List.range (shape.width variant) do
    let offset := payload.2 + index
    current := update current (first + Word.ofNatModulo offset) (written result (origin + offset))
  return current

/-- The decoded variant at `first` and its payload Words: the outermost zero
tag selects its level's variant, and past every level the last one. -/
private def readChoice (shape : Shape) (storage : List (Word × Word)) (first : Word) : List Word := Id.run do
  let count := shape.count
  for level in List.range (count - 1) do
    if lookup storage (first + Word.ofNatModulo level) == Word.zero then
      return [Word.ofNatModulo level] ++ (List.range (shape.width level)).map fun index =>
        lookup storage (first + Word.ofNatModulo (level + 1 + index))
  return [Word.ofNatModulo (count - 1)] ++ (List.range (shape.width (count - 1))).map fun index =>
    lookup storage (first + Word.ofNatModulo (count - 1 + index))

/-- The record's field `field` at `first`, written as a whole-record write writes it. -/
private def writeField (shape : Shape) (storage : List (Word × Word)) (first : Word) (field variant : Nat)
    (result : Word) : List (Word × Word) :=
  let offset := shape.fieldOffset field
  if field == shape.position then writeChoice shape storage (first + Word.ofNatModulo offset) offset variant result
  else update storage (first + Word.ofNatModulo offset) (written result offset)

private def readRecord (shape : Shape) (storage : List (Word × Word)) (first : Word) : List Word :=
  (List.range AdtStorage.recordFields).flatMap fun field =>
    let slot := first + Word.ofNatModulo (shape.fieldOffset field)
    if field == shape.position then readChoice shape storage slot else [lookup storage slot]

/-- Horner's rule over the decoded Words with the multiplier. -/
def digest (tokens : List Word) : Word := tokens.foldl (fun total token => total * multiplier + token) Word.zero

def modelTransaction (plan : CheckedPlan) (fuel : Nat) (prior : List (Word × Word)) (tx : Transaction) :
    Option ModelRow := do
  let shape := plan.shape
  let accumulator := Word.ofNatModulo AdtStorage.accumulatorSlot
  let first : Word :=
    if tx.method.keyed then entrySlot (if tx.method.record then shape.recordMapSlot else shape.choiceMapSlot) tx.key
    else Word.ofNatModulo (if tx.method.record then shape.recordSlot else AdtStorage.choiceSlot)
  let (result, storage) ← if tx.method.reads then
      let tokens := if tx.method.record then readRecord shape prior first else readChoice shape prior first
      pure (digest tokens, prior)
    else do
      let result ← stepResult plan.step fuel (tx.input + lookup prior accumulator)
      let storage :=
        if tx.method.clears then writeChoice shape prior first 0 shape.clearVariant result
        else if !tx.method.record then writeChoice shape prior first 0 tx.variant result
        else if tx.method.updates then writeField shape prior first tx.field tx.variant result
        else (List.range AdtStorage.recordFields).foldl
          (fun current field => writeField shape current first field tx.variant result) prior
      pure (result, storage)
  let reverted := tx.flags.val % 2 == 1
  return ⟨reverted, result, if reverted then prior else update storage accumulator result⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let mut storage : List (Word × Word) := []
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction plan fuel storage transaction with
    | some row =>
        rows := rows.push row
        storage := row.storage
    | none => return none
  return some rows.toList

/-- A modelled row's value at each observed slot. -/
def modelSlots (row : ModelRow) (slots : List Word) : List Word := slots.map (lookup row.storage)

end Solcore.Synthesis.Stateful.AdtStorageExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.AdtStorageCases
/-! Enum and struct storage cases retain one original host-aware Core contract,
its type shape, declared methods, key base and step, and an ordered history of
method calls. Each transaction records its method and the arguments it takes.
The observed slots are derived from the shape and the two keys and are part of
the case. Reductions remove transactions, then methods no transaction calls,
then shrink the shape, reduce the step and simplify arguments. Saved outputs
are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AdtStorage
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (encodeBytesText encodeWordBytesBE)
open Solcore.Synthesis.Core.AdtStorage (CheckedPlan Method Shape Payload WordType)
open Solcore.Synthesis.Stateful.AdtStorageExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-adt-storage-case.v1"
def planSchema : String := "solcore-lean.adt-storage-plan.v1"
def profileVersion : String := "stateful-adt-storage-v1/adt-storage-sequence-seed-v2"
def templateVersion : String := "std-storage-generic-enum-record-fields-mappings-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-adt-storage-corpus.v1"

/-- Flags and inputs; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- The key bases a generated case draws from; the last wraps to zero. -/
def keyBases : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 3, Word.ofNatModulo (2 ^ 255), Word.maximum]

/-- Complete contracts may exceed the step budget by the Keccak closure, the
enum closures and the methods. -/
def maxProgramNodes : Nat := 512 + AdtStorage.hashNodes + AdtStorage.maxOutsideNodes

def validTransactions (plan : CheckedPlan) (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id && tx.valid plan) = true

instance (plan : CheckedPlan) (transactions : List Transaction) : Decidable (validTransactions plan transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions plan transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions plan transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical enum and struct storage contract exceeds its case limit"
  else throw s!"enum and struct storage scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, each calling a declared method with a key of the case, a record field and a variant of the shape where it takes them"

def CheckedScenario.observedSlots (scenario : CheckedScenario) : List Word :=
  Solcore.Synthesis.Stateful.AdtStorageExecution.planSlots scenario.plan

def transactionJson (tx : Transaction) : Json := Json.mkObj <|
  [("id", toJson tx.id), ("method", toJson tx.method.name), ("flags", toJson (toString tx.flags.val))] ++
    (if tx.method.keyed then [("key", toJson (toString tx.key.val))] else []) ++
    (if tx.method.updates then [("field", toJson tx.field)] else []) ++
    (if tx.method.takesVariant then [("variant", toJson tx.variant)] else []) ++
    (if tx.method.reads then [] else [("input", toJson (toString tx.input.val))]) ++
    [("calldata", toJson (Solcore.Synthesis.Stateful.AdtStorageExecution.calldata tx)), ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

private def optionalWord (row : Json) (name : String) : Except String Word :=
  match row.getObjVal? name with
  | .ok value => do word (← value.getStr?)
  | .error _ => pure Word.zero

private def optionalNat (row : Json) (name : String) : Except String Nat :=
  match row.getObjVal? name with
  | .ok value => do
      let number ← value.getNat?
      unless number < 16 do throw "a transaction's field or variant is below sixteen"
      pure number
  | .error _ => pure 0

def decodeTransactions (plan : CheckedPlan) (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let name ← row.getObjValAs? String "method"
    let some method := Method.ofName? name | throw "transaction names an unknown method"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", method,
      ← word (← row.getObjValAs? String "flags"), ← optionalWord row "key", ← optionalNat row "field",
      ← optionalNat row "variant", ← optionalWord row "input"⟩
    unless Storage.validId transaction.id && transaction.valid plan do
      throw "invalid transaction ID, undeclared method, or a key, field or variant outside the case"
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, method, arguments, calldata or zero-value metadata"
    return transaction
  unless validTransactions plan transactions do
    throw "enum and struct storage scenario requires distinct valid transaction IDs"
  return transactions

def shapeJson (shape : Shape) : Json := Json.mkObj [
  ("variants", toJson (shape.variants.map Payload.name)), ("position", toJson shape.position),
  ("wordType", toJson shape.wordType.name)]

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("shape", shapeJson plan.shape),
  ("methods", toJson (plan.methods.map (·.name))), ("keyBase", toJson (toString plan.keyBase.val)),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def decodeShape (json : Json) : Except String Shape := do
  let names ← json.getObjValAs? (List String) "variants"
  unless names.length ≤ AdtStorage.maxVariants do throw "a shape has at most four variants"
  let variants ← names.mapM fun name => match Payload.ofName? name with
    | some payload => pure payload
    | none => throw "unknown variant payload"
  let some wordType := WordType.ofName? (← json.getObjValAs? String "wordType") | throw "unknown Word type"
  let shape : Shape := {variants, position := ← json.getObjValAs? Nat "position", wordType}
  unless shape.valid do
    throw "a shape has two to four variants of zero to three Words or a pair, one payload-free, at most four enum slots and the enum at record position 0, 1 or 2"
  unless json == shapeJson shape do throw "noncanonical shape"
  return shape

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported enum and struct storage plan schema"
  let shape ← decodeShape (← json.getObjVal? "shape")
  let names ← json.getObjValAs? (List String) "methods"
  unless names.length ≤ Method.all.length do throw "a plan declares at most twelve methods"
  let methods ← names.mapM fun name => match Method.ofName? name with
    | some method => pure method
    | none => throw "plan declares an unknown method"
  let keyBase ← word (← json.getObjValAs? String "keyBase")
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? shape methods keyBase step |
    throw "enum and struct storage plan needs one to twelve distinct methods in declaration order and full host-Core admission"
  unless json == planJson plan do throw "enum and struct storage plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "enum and struct storage contract exceeds its case limit"
  return plan

def emitted (plan : CheckedPlan) : Except String EmittedAdtStorage := (emit plan).mapError reprStr

/-- The layout the Core contract and the observed slots use, recorded for the
adapter to recompute independently. -/
def layoutJson (shape : Shape) : Json := Json.mkObj [
  ("accumulatorSlot", toJson AdtStorage.accumulatorSlot), ("choiceSlot", toJson AdtStorage.choiceSlot),
  ("choiceSlots", toJson shape.choiceSlots), ("recordSlot", toJson shape.recordSlot),
  ("recordSlots", toJson shape.recordSlots),
  ("fieldOffsets", toJson ((List.range AdtStorage.recordFields).map shape.fieldOffset)),
  ("choicesSlot", toJson shape.choiceMapSlot), ("recordsSlot", toJson shape.recordMapSlot),
  ("clearVariant", toJson shape.clearVariant)]

def contractJson (plan : CheckedPlan) (emitted : EmittedAdtStorage) : Json := Json.mkObj [
  ("name", toJson emitted.contractName),
  ("methods", toJson (plan.methods.map fun method => Json.mkObj [
    ("name", toJson method.name), ("signature", toJson method.signature),
    ("selector", toJson (Stateful.StdCalldata.selectorText method.selector)),
    ("parameters", toJson method.parameters)])),
  ("layout", layoutJson plan.shape),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedAdtStorage) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("adtStoragePlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson scenario.observedSlots),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson AdtStorage.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson scenario.plan emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let source ← emitted scenario.plan
  return makeCase scenario source origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic enum and struct storage case schema"
  let plan ← checkedPlan (← json.getObjVal? "adtStoragePlan")
  let transactions ← decodeTransactions plan (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical enum and struct storage plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let scenario ← checkedScenario plan transactions
  unless (← json.getObjVal? "observedSlots") ==
      Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson scenario.observedSlots do
    throw "observed slots must be the accumulator, the enum and record fields and both keys' entry slots"
  return scenario

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.AdtStorageExecution.observe scenario.plan scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Per transaction a method, a variant (taken modulo the variant count), a
record field, a key, a flags bank index and an input bank index, then the
completion pattern. Each choice uses the high half of one draw from a
separate stream. The stream starts at SplitMix64's finalizer of the seed xor its
domain, so that consecutive seeds' choices do not step by a fixed residue. -/
def sequenceBounds : List Nat := (List.replicate 3 [12, 12, 3, 2, 6, 6]).flatten ++ [4]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6164747374727371))
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 18 0) [false, false, false]

/-- A transaction of the shape and keys from its six choices; arguments the
method does not take are zero. -/
def drawnTransaction (shape : Shape) (keys : List Word) (id : String) (odd : Bool) (choices : List Nat) : Transaction :=
  let method := Method.all.getD (choices.getD 0 0) .getChoice
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  ⟨id, method, parityInput odd (bank 4),
    if method.keyed then keys.getD (choices.getD 3 0) Word.zero else Word.zero,
    if method.updates then choices.getD 2 0 else 0,
    if method.takesVariant then choices.getD 1 0 % shape.count else 0,
    if method.reads then Word.zero else bank 5⟩

def blockTransactions (shape : Shape) (keys : List Word) (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    drawnTransaction shape keys ("tx-" ++ toString (first + index)) odd (choices.drop (6 * index))

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (shape : Shape) (keys : List Word) (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks (blockTransactions shape keys) seed count

/-- Separate the shape and key streams from each other and from other uses of
a case seed. -/
private def countDomain : UInt64 := 0x6164747374726301
private def listDomain : UInt64 := 0x6164747374726c01
private def positionDomain : UInt64 := 0x6164747374727001
private def typeDomain : UInt64 := 0x6164747374727401
private def keyDomain : UInt64 := 0x6164747374726b01

private def drawn (seed : Seed) (domain : UInt64) (bound : Nat) : Nat :=
  (GeneratorV2.mix (seed.toUInt64 ^^^ domain)).toNat % bound

/-- SplitMix64 hashes of the seed: the variant count, a list among that
count's valid lists, the enum's position and the Word type, each uniform. -/
def shapeFor (seed : Seed) : Shape :=
  let count := AdtStorage.minVariants + drawn seed countDomain (AdtStorage.maxVariants - AdtStorage.minVariants + 1)
  let lists := AdtStorage.variantLists count
  {variants := lists.getD (drawn seed listDomain lists.length) [], position := drawn seed positionDomain AdtStorage.recordFields,
    wordType := if drawn seed typeDomain 2 == 0 then .word else .uint256}

def keyBaseFor (seed : Seed) : Word := keyBases.getD (drawn seed keyDomain keyBases.length) Word.zero

/-- The methods a sequence calls, in declaration order. -/
def calledMethods (transactions : List Transaction) : List Method :=
  Method.all.filter fun method => transactions.any (·.method == method)

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The shell lies inside the budget; the Keccak closure, the enum closures and
the methods lie outside it. The complete contract is remeasured as the final
budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && AdtStorage.shellNodes < nodes do
    throw "node budget is too small for the enum and struct storage wrapper or exceeds 512"
  let shape := shapeFor seed
  let keyBase := keyBaseFor seed
  let keys := [keyBase, Word.ofNatModulo (keyBase.val + 1)]
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - AdtStorage.shellNodes) revision
  let sequence := generatedTransactions shape keys seed transactions
  let methods := calledMethods sequence
  let some plan := CheckedPlan.ofParts? shape methods keyBase step |
    throw "generated enum and struct storage plan failed full Core admission"
  let scenario ← checkedScenario plan sequence
  unless Wire.programNodes scenario.program ≤
      nodes + AdtStorage.hashNodes + AdtStorage.closureNodes shape + AdtStorage.methodNodes shape methods do
    throw "enum and struct storage contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "adt-storage-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("shape", shapeJson shape), ("keyBase", toJson (toString keyBase.val)), ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "enum and struct storage history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "enum and struct storage history did not follow its prescribed flags parities"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let source ← emitted scenario.plan
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), source)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "enum and struct storage history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "adt-storage-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, source) =>
          cases := cases.push (makeCase scenario source origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Variants, payload Words, pair payloads and the `uint256` type. -/
def shapeWeight (shape : Shape) : Nat :=
  shape.count + (shape.variants.map Payload.width).sum + (shape.variants.filter (· == .pair)).length +
    (if shape.wordType == .uint256 then 1 else 0)

/-- A transaction's argument values; the key counts as its index among the case's keys. -/
def argumentWeight (plan : CheckedPlan) (tx : Transaction) : Nat :=
  tx.flags.val + tx.input.val + tx.field + tx.variant + (if tx.method.keyed && tx.key != plan.keyBase then 1 else 0)

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total tx => total + argumentWeight scenario.plan tx) 0

/-- Transaction count, method count, shape weight, complete program
size/literals, then argument values. Every axis is a natural number and the
comparison is lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (candidate.plan.methods.length < source.plan.methods.length ∨
    (candidate.plan.methods.length = source.plan.methods.length ∧
      (shapeWeight candidate.plan.shape < shapeWeight source.plan.shape ∨
      (shapeWeight candidate.plan.shape = shapeWeight source.plan.shape ∧
        ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
        (complexity candidate.program.body = complexity source.program.body ∧
          valueWeight candidate < valueWeight source)))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  sameKeys : candidate.plan.keyBase = source.plan.keyBase
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

def sealReduction (source : CheckedScenario) (shape : Shape) (methods : List Method) (step : Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? shape methods source.plan.keyBase step
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if keys : candidate.plan.keyBase = source.plan.keyBase then
        if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
          if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, keys, ids, strict⟩
          else none
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) :
    List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- Without variant `removed`, later variants move down by one. -/
private def renumber (removed : Nat) (tx : Transaction) : Transaction :=
  if tx.method.takesVariant && tx.variant > removed then {tx with variant := tx.variant - 1} else tx

/-- The narrower payloads of a variant: a pair as two Words, `k` Words as `k - 1`. -/
private def narrower : Payload → List Payload
  | .pair => [.words 2]
  | .words (count + 1) => [.words count]
  | .words 0 => []

/-- One-transaction removals first, from the last back; then the removal of
each declared method no transaction calls; then shape reductions: removing a
variant no transaction names, narrowing a payload and `uint256` to `word`;
then step reductions; then per transaction the flags' parity bit, smaller bank
inputs, and smaller variant, field and key arguments. Candidates still need
execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let shape := source.plan.shape
  let methods := source.plan.methods
  let step := source.plan.step
  let transactions := source.transactions
  let mut raw : List (Shape × List Method × Aggregates.CheckedDAG × List Transaction) := []
  for index in (List.range transactions.length).reverse do
    raw := raw ++ [(shape, methods, step, (transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for method in methods.reverse do
    if transactions.all (·.method != method) then
      raw := raw ++ [(shape, methods.erase method, step, transactions)]
  for index in (List.range shape.count).reverse do
    if transactions.all (fun tx => !tx.method.takesVariant || tx.variant != index) then
      raw := raw ++ [({shape with variants := shape.variants.eraseIdx index}, methods, step, transactions.map (renumber index))]
  for (payload, index) in shape.variants.zipIdx do
    for smaller in narrower payload do
      raw := raw ++ [({shape with variants := shape.variants.set index smaller}, methods, step, transactions)]
  if shape.wordType == .uint256 then
    raw := raw ++ [({shape with wordType := .word}, methods, step, transactions)]
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(shape, methods, reduced.candidate.function, transactions)]
  for (transaction, index) in transactions.zipIdx do
    raw := raw ++ [(shape, methods, step, replaceAt transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    for smaller in boundaryInputs do
      if smaller.val < transaction.input.val then
        raw := raw ++ [(shape, methods, step, replaceAt transactions index fun tx => {tx with input := smaller})]
    if transaction.variant > 0 then
      raw := raw ++ [(shape, methods, step, replaceAt transactions index fun tx => {tx with variant := 0})]
    if transaction.field > 0 then
      raw := raw ++ [(shape, methods, step, replaceAt transactions index fun tx => {tx with field := 0})]
    if transaction.method.keyed && transaction.key != source.plan.keyBase then
      raw := raw ++ [(shape, methods, step, replaceAt transactions index fun tx => {tx with key := source.plan.keyBase})]
  let mut seen : List String := []
  let mut result := []
  for (shape, methods, step, transactions) in raw do
    if let some reduced := sealReduction source shape methods step transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentTransactions", transactionsJson parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", AdtStorage.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let source ← emitted admitted.plan
  unless (← json.getObjValAs? String "source") = source.source do
    throw "saved source differs from the enum and struct storage emission"
  unless (← json.getObjVal? "contract") == contractJson admitted.plan source do
    throw "saved contract metadata differs from the enum and struct storage wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "adt-storage-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated enum and struct storage provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions parentPlan (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.shape admitted.plan.methods admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not keep the step's bindings, the keys and the IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported enum and struct storage case origin"
  return makeCase admitted source origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced =>
    emitCase reduced.candidate (reducedOrigin source) fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.AdtStorage
end

section
-- leanmerge: from Solcore.Synthesis.Source.EventLogEmitter
/-! Emit the fixed event-log protocol. Slot zero receives the step result and
slot one the counter, in the same order as the original Core contract. Each
guarded site then applies the step to `result + guard` and calls the pinned
`std.opcodes` wrapper `log0` to `log4` with its topics and data Words, over a
64-byte buffer reserved from the free-memory pointer. Odd flags revert after
every write and log with the result encoded as exactly 32 bytes; even flags
return it through the ABI. Only the log arities a plan uses are imported. The
arbitrary checked aggregate entry is preserved.
`ScalarMeaning.EventLog.emit_source_meaning` relates the emitted text to the
original Core contract's top-level transaction, returned with its storage and
logs or reverted with no log, under an independent event-log source semantics;
see `docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EventLog

open Solcore.Synthesis.Core.EventLog (CheckedPlan Site)

def emitterVersion : String := "solcore-source-event-log-v1"
def wrapperVersion : String := "solcore-word-event-log-contract-v1"
def contractName : String := "SynthesizedLogs"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedLogsDeploy"]
def runtimePath : List String := ["SynthesizedLogsDeploy", "SynthesizedLogs"]

/-- The wrapper alias of a topic count; the `sc_` prefix avoids the generic
`log1` that `std` exports. -/
def logAlias (topics : Nat) : String := "sc_log" ++ toString topics

/-- Arities used by the plan, ascending and without duplicates. -/
def usedArities (sites : List Site) : List Nat :=
  (List.range 5).filter fun topics => sites.any (·.topics == topics)

def siteLines (site : Site) : List String :=
  let value := "sc_value" ++ toString site.guard
  let mask := toString (2 ^ site.guard)
  let data := (List.range site.dataWords).map fun index =>
    "            mstore(sc_ptr" ++ (if index = 0 then "" else " + 32") ++ ", " ++
      (if index = 0 then value else "sc_result") ++ ");"
  let topics := (List.range site.topics).map fun index => value ++ " + " ++ toString (index + 1)
  ["        if ((sc_flags & " ++ mask ++ ") == " ++ mask ++ ") {",
    "            let " ++ value ++ ": word = sc_step(sc_result + " ++ toString site.guard ++ ");"] ++ data ++
    ["            " ++ logAlias site.topics ++ "(" ++ ", ".intercalate
      (["sc_ptr", toString (32 * site.dataWords)] ++ topics) ++ ");", "        }"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let wrappers := (usedArities plan.sites).map fun topics => "log" ++ toString topics ++ " as " ++ logAlias topics
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith (["sload", "sstore", "mload", "mstore", "revert_"] ++ wrappers)
      (plan.step.helpers ++ [plan.step.entry]), ""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_old: word = sload(0);",
    "        let sc_count: word = sload(1);",
    "        let sc_result: word = sc_step(sc_input + sc_old);",
    "        sstore(0, sc_result);",
    "        sstore(1, sc_count + 1);",
    "        let sc_ptr: word = mload(64);",
    "        mstore(64, sc_ptr + 64);"] ++ plan.sites.flatMap siteLines ++
    ["        if ((sc_flags & 1) == 1) {",
    "            mstore(sc_ptr, sc_result);",
    "            revert_(sc_ptr, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.EventLog
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.EventLogExecution
/-! Execute the original checked event-log contract over a persistent account
world. Each invocation starts a fresh Core heap and an empty transaction
journal; only the public terminal `finalWorld` becomes the next transaction's
world, and only its `committedJournal` is reported. That journal is the working
journal on return and the checkpoint journal on revert, so rollback is chosen
by `ContractRuntime`, not by this observer. Committed word logs are decoded
into multi-topic logs by `Solcore.Synthesis.Core.EventLog.framingVersion`; a
journal that is not a sequence of complete frames is reported as an observer
failure, never as a shorter log list. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.EventLogExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.EventLog (CheckedPlan headerTag dataTag topicTag maxTopics maxDataWords)

def historySchema : String := "solcore-lean.log-history.v2"

/-- One caller and one installed contract, as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  deriving BEq

/-- The selector of `run(uint256,uint256)`, followed by the flags and the input
as two big-endian Words. Malformed calldata is outside this profile. -/
def inputData (flags input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input : Word) : String := encodeBytesText (inputData flags input).bytes

/-- Slot zero holds the step result and slot one the transaction counter. -/
def observedSlots : List Word := [Word.ofNatModulo 0, Word.ofNatModulo 1]

/-- One decoded log: its emitter, topics and data Words in order. -/
structure Event where
  emitter : Address
  topics : List Word
  data : List Word
  deriving BEq, Repr

def eventJson (event : Event) : Json := Json.mkObj [
  ("address", toJson (toString event.emitter.val)),
  ("topics", toJson (event.topics.map fun topic => toString topic.val)),
  ("data", toJson (encodeBytesText (event.data.foldl (fun bytes value => bytes ++ encodeWordBytesBE value) ByteArray.empty)))]

def eventsJson (events : List Event) : Json := toJson (events.map eventJson)

/-- Read `count` records numbered from one under `tag`, all from `emitter`. -/
private def tagged (emitter : Address) (tag : Nat → Nat) (count : Nat) (records : List CheckedCoreWordLog) :
    Except String (List Word × List CheckedCoreWordLog) := do
  let mut rest := records
  let mut values : Array Word := #[]
  for index in List.range count do
    match rest with
    | [] => throw "truncated log frame"
    | record :: tail =>
        unless record.emitter == emitter do throw "log frame mixes emitters"
        unless record.topic.val == tag (index + 1) do throw "unexpected log frame record"
        values := values.push record.payload
        rest := tail
  return (values.toList, rest)

/-- Decode a committed journal frame by frame. Every frame consumes at least its
header, so the journal length bounds the loop. -/
def decodeJournal (records : List CheckedCoreWordLog) : Except String (List Event) := do
  let mut rest := records
  let mut events : Array Event := #[]
  for _ in records do
    match rest with
    | [] => pure ()
    | header :: tail =>
        let value := header.topic.val
        unless 256 ≤ value do throw "log frame does not start with a header"
        let dataWords := (value - 256) / 16
        let topics := (value - 256) % 16
        unless dataWords ≤ maxDataWords && topics ≤ maxTopics &&
            value == headerTag {guard := 0, topics, dataWords} do
          throw "invalid log frame header"
        unless header.payload == Word.zero do throw "log frame header has a nonzero payload"
        let (data, afterData) ← tagged header.emitter dataTag dataWords tail
        let (topicWords, afterTopics) ← tagged header.emitter topicTag topics afterData
        events := events.push {emitter := header.emitter, topics := topicWords, data}
        rest := afterTopics
  unless rest.isEmpty do throw "log journal has records after its frames"
  return events.toList

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => KeyedStorageExecution.storageJson account observedSlots
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation. The code registry is resolved again
against each current committed world, so persistence cannot install a different
contract or retain one invocation's local heap or journal. -/
def observeContract (contract : CheckedCoreContract) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let invocation : TopLevelInvocation := {
        target := bindings.address, caller := bindings.caller,
        callValue := Word.zero, inputData := inputData transaction.flags transaction.input }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"),
            ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address), ("logs", Json.null)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              match decodeJournal terminal.committedJournal.logList with
              | .ok events =>
                  rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                    ("committedStorage", worldStorage world bindings),
                    ("accountStorage", AccountStorage.contractJson world bindings.address), ("logs", eventsJson events)]))
                  match terminal.outcome with
                  | .trapped _ => stopped := some transaction.id
                  | _ => pure ()
              | .error error =>
                  rows := rows.push (Json.mkObj (common ++ [
                    ("status", toJson "observer-error"), ("detail", toJson error),
                    ("committedStorage", worldStorage world bindings),
                    ("accountStorage", AccountStorage.contractJson world bindings.address), ("logs", Json.null)]))
                  stopped := some transaction.id
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"),
                ("committedStorage", worldStorage prior bindings),
                ("accountStorage", AccountStorage.contractJson prior bindings.address), ("logs", Json.null)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", KeyedStorageExecution.slotsJson observedSlots),
    ("framing", toJson Solcore.Synthesis.Core.EventLog.framingVersion),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("initialLogs", toJson ([] : List Json)),
    ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.EventLogExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.EventLogCases
/-! Event-log cases retain one original host-aware Core contract, its static
log sites and an ordered history of `(flags, input)` transactions. The plan
fixes each site's guard bit, topic count and data length, so the log shapes a
transaction may commit are known before execution; their topics and data are
not. Saved outputs and logs are never an execution oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EventLog
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EventLog (CheckedPlan Site validSites)
open Solcore.Synthesis.Stateful.EventLogExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-log-case.v1"
def planSchema : String := "solcore-lean.log-plan.v1"
def profileVersion : String := "stateful-logs-v1/log-sequence-seed-v2"
def templateVersion : String := "slot-counter-guarded-log-sites-revert-odd-flags-v1"
def logCorpusSchema : String := "solcore-lean.semantic-log-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs

/-- Flags bits above the guards. Generated transactions may set them; the
contract must ignore them. -/
def flagsNoise : Word := Word.ofNatModulo (2 ^ 255 + 16)

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true

instance (transactions : List Transaction) : Decidable (validTransactions transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.program ≤ 512

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ 512 then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical event-log contract exceeds the 512-node case limit"
  else throw s!"event-log scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.EventLogExecution.calldata tx.flags tx.input)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def wordField (row : Json) (key : String) : Except String Word := do
  let text ← row.getObjValAs? String key
  unless text.length ≤ 78 do throw ("transaction " ++ key ++ " exceeds a Word")
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", ← wordField row "flags", ← wordField row "input"⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, input, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "event-log scenario requires distinct valid transaction IDs"
  return transactions

def siteJson (site : Site) : Json := Json.mkObj [
  ("guard", toJson site.guard), ("topics", toJson site.topics), ("dataWords", toJson site.dataWords)]

def sitesJson (sites : List Site) : Json := toJson (sites.map siteJson)

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("sites", sitesJson plan.sites)]

private def decodeSites (json : Json) : Except String (List Site) := do
  let rows ← json.getArr?
  unless rows.size ≤ Solcore.Synthesis.Core.EventLog.maxSites do throw "an event-log plan has at most three sites"
  let sites ← rows.toList.mapM fun row => do
    let site : Site := ⟨← row.getObjValAs? Nat "guard", ← row.getObjValAs? Nat "topics",
      ← row.getObjValAs? Nat "dataWords"⟩
    unless row == siteJson site do throw "log site differs from its canonical guard, topics and dataWords"
    return site
  unless validSites sites do
    throw "log sites need increasing guards one to three, at most four topics and two data Words"
  return sites

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported event-log plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let sites ← decodeSites (← json.getObjVal? "sites")
  let some plan := CheckedPlan.ofParts? step sites | throw "event-log contract failed full host-Core admission"
  unless json == planJson plan do throw "event-log plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ 512 do throw "event-log contract exceeds the 512-node case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def observedSlotsJson : Json :=
  Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson Solcore.Synthesis.Stateful.EventLogExecution.observedSlots

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("logPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.EventLog.version),
      ("framingVersion", toJson Solcore.Synthesis.Core.EventLog.framingVersion),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic event-log case schema"
  let plan ← checkedPlan (← json.getObjVal? "logPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical event-log plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson do throw "observed slots must be zero and one"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.EventLogExecution.observe scenario.plan scenario.transactions bindings fuel

private def bitSet (value : Word) (bit : Nat) : Bool :=
  value.bitAnd (Word.ofNatModulo (2 ^ bit)) == Word.ofNatModulo (2 ^ bit)

def reverts (tx : Transaction) : Bool := bitSet tx.flags 0

/-- Sites whose guard bit is set, in emission order. Whether their logs commit
depends on the completion. -/
def guardedSites (plan : CheckedPlan) (tx : Transaction) : List Site :=
  plan.sites.filter fun site => bitSet tx.flags site.guard

/-- The static topic counts and data lengths in bytes of the committed logs:
one per guarded site on return, none on revert. -/
def expectedShapes (plan : CheckedPlan) (tx : Transaction) : List (Nat × Nat) :=
  if reverts tx then [] else (guardedSites plan tx).map fun site => (site.topics, 32 * site.dataWords)

def parityFlags (odd : Bool) (flags : Word) : Word :=
  if odd then flags.bitOr (Word.ofNatModulo 1)
  else flags.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Guard sets for one and two sites; three sites use every guard. -/
private def guardChoices : Nat → List (List Nat)
  | 1 => [[1], [2], [3]]
  | 2 => [[1, 2], [1, 3], [2, 3]]
  | _ => [[1, 2, 3]]

/-- A separate stream keeps site and sequence choices independent of the step
seed's helper-count and template digits. Each choice uses the high half of one
draw: the low bits of a power-of-two LCG have short periods. The draws are the
site count, three topic counts and data lengths, the guard set, three inputs,
three guard masks, three noise choices and the completion pattern. The stream
starts at SplitMix64's finalizer of the seed xor its domain, so that consecutive
seeds' choices do not step by a fixed residue. -/
def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6c6f672d73697465))
  let mut values : Array Nat := #[]
  for bound in [3, 5, 3, 5, 3, 5, 3, 3, 6, 6, 6, 8, 8, 8, 2, 2, 2, 4] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedSites (seed : Seed) : List Site :=
  let choices := sequenceChoices seed
  let count := 1 + choices.getD 0 0
  let guards := (guardChoices count).getD (choices.getD 7 0) [1, 2, 3]
  guards.zipIdx.map fun (guard, index) =>
    ⟨guard, choices.getD (1 + 2 * index) 0, choices.getD (2 + 2 * index) 0⟩

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 17 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    let mask := Word.ofNatModulo (2 * choices.getD (11 + index) 0)
    let noise := if choices.getD (14 + index) 0 = 1 then flagsNoise else Word.zero
    ⟨"tx-" ++ toString (first + index), parityFlags odd (mask.bitOr noise),
      boundaryInputs.getD (choices.getD (8 + index) 0) Word.zero⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- Reserve the measured host wrapper of the chosen sites before generating the
independent step; the complete contract is remeasured as the final authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let sites := generatedSites seed
  let overhead := Solcore.Synthesis.Core.EventLog.programOverhead sites
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the event-log wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step sites | throw "generated event-log plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do throw "event-log contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "log-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

private def shapes (logs : Json) : Except String (List (Nat × Nat)) := do
  let rows ← logs.getArr?
  rows.toList.mapM fun row => do
    let topics ← row.getObjValAs? (List String) "topics"
    let data ← row.getObjValAs? String "data"
    unless data.length ≥ 2 && data.length % 2 == 0 do throw "noncanonical log data"
    return (topics.length, (data.length - 2) / 2)

/-- Original Core must complete every transaction with a decodable journal
whose logs have the static shapes of the plan, and the given completions. -/
def checkShapes (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "event-log history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "event-log history length changed"
  let mut statuses : List String := []
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    unless status == statusName (reverts tx) do throw "event-log history did not follow its flags parities"
    unless (← shapes (← row.getObjVal? "logs")) == expectedShapes scenario.plan tx do
      throw "event-log history differs from the static site shapes"
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  let statuses ← checkShapes scenario observed
  unless statuses == scenario.transactions.map (fun tx => statusName (reverts tx)) do
    throw "event-log history did not follow its prescribed flags parities"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "event-log history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "event-log-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson logCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Flags and inputs both contribute; clearing a flags bit lowers the weight. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.flags.val + transaction.input.val) 0

/-- Transaction count, complete program size/literals, then runtime flags and
inputs. Removing or simplifying a site shrinks the program. Every axis is a
natural number and the comparison is lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      valueWeight candidate < valueWeight source)))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (sites : List Site)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step sites
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) :
    List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- Each site may be removed, or lose its last topic or last data Word. -/
private def siteReductions (sites : List Site) : List (List Site) :=
  (List.range sites.length).flatMap fun position =>
    let site := sites.getD position ⟨0, 0, 0⟩
    [sites.eraseIdx position] ++
      (if site.topics > 0 then [sites.set position {site with topics := site.topics - 1}] else []) ++
      (if site.dataWords > 0 then [sites.set position {site with dataWords := site.dataWords - 1}] else [])

/-- Step reductions, site removals and simplifications, then per transaction:
removal, bank replacements of the input, clearing one of flags bits zero to
three, and keeping only those four bits. Candidates still need execution to
preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let sites := source.plan.sites
  let mut raw : List (Aggregates.CheckedDAG × List Site × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(step, sites,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, sites, source.transactions)]
  for candidate in siteReductions sites do
    raw := raw ++ [(step, candidate, source.transactions)]
  for index in List.range source.transactions.length do
    for input in boundaryInputs do
      raw := raw ++ [(step, sites, replaceAt source.transactions index fun tx => {tx with input := input})]
    for bit in List.range 4 do
      raw := raw ++ [(step, sites, replaceAt source.transactions index fun tx =>
        {tx with flags := tx.flags.bitAnd (Word.ofNatModulo (2 ^ bit)).bitNot})]
    raw := raw ++ [(step, sites, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 15)})]
  let mut seen : List String := []
  let mut result := []
  for (step, sites, transactions) in raw do
    if let some reduced := sealReduction source step sites transactions then
      let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.candidate.program),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.EventLog.version),
      ("framingVersion", Solcore.Synthesis.Core.EventLog.framingVersion), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from event-log plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from event-log wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "log-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated event-log provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.sites admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported event-log case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentProgram", Wire.encodeProgram source.program), ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson logCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.EventLog
end
