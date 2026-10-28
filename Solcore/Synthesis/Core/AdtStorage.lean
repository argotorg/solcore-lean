import Solcore.Abi.Keccak256
import Solcore.Synthesis.Core.StorageMapping
import Solcore.Synthesis.Core.StdDispatch

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
