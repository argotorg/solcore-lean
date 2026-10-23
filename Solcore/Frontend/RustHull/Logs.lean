import Solcore.Frontend.RustHull.Memory

/-! Event capture using existing Core mappings and cells. The log stream stores
whole words: address, topic count, byte count, topics, then padded data words.
The cursor counts words. Each append snapshots memory before publishing a log. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Logs
open Core

def capacityReason : Word := Word.ofNatModulo 10
def topicReason : Word := Word.ofNatModulo 11

private def number (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def add (left right : Expr) : Expr := .binary .wordAdd left right
private def packet : List Expr → Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)
private def field (index : Nat) : Nat → Expr → Expr
  | 0, _ => .unit
  | 1, value => value
  | count + 2, value => if index = 0 then .first value
      else field (index - 1) (count + 1) (.second value)
private def types : List Ty → Ty
  | [] => .unit
  | [type] => type
  | type :: rest => .product type (types rest)

private def wordCount (bytes : Expr) : Expr :=
  add (.binary .wordDiv bytes (number 32))
    (.ifE (.binary .wordEq (.binary .wordMod bytes (number 32)) (number 0)) (number 0) (number 1))

private def insertWords (mapping cursor : Expr) (values : List Expr) : Expr :=
  match values with
  | [] => LanguageResult.success mapping
  | value :: rest => LanguageResult.bind WordMapping.type (WordMapping.insert mapping cursor value)
      (insertWords (.var 0) (add (cursor.weakenAt 0) (number 1)) (rest.map (·.weakenAt 0)))

termination_by values.length
decreasing_by simp_wf

private def copyType : Ty := types [WordMapping.type, .word, .word, WordMapping.type, .word]

private def copyBody : Expr :=
  let parameter := Expr.var 0
  .ifE (.binary .wordEq (field 2 5 parameter) (number 0))
    (LanguageResult.success (field 3 5 parameter))
    (LanguageResult.bind WordMapping.type
      (Memory.readMemoryWord (field 0 5 parameter) (field 1 5 parameter))
      (.letE (.ifE (.binary .wordGt (field 2 5 (.var 1)) (number 31))
          (number 32) (field 2 5 (.var 1)))
        (.letE (.binary .wordMul (.binary .wordSub (number 32) (.var 0)) (number 8))
          (LanguageResult.bind WordMapping.type
            (WordMapping.insert (field 3 5 (.var 3)) (field 4 5 (.var 3))
              (.binary .wordShl (.binary .wordShr (.var 2) (.var 0)) (.var 0)))
            (WordMapping.invoke copyType WordMapping.type (.var 5)
              (packet [field 0 5 (.var 4), add (field 1 5 (.var 4)) (.var 2),
                .binary .wordSub (field 2 5 (.var 4)) (.var 2), .var 0,
                add (field 4 5 (.var 4)) (number 1)]))))))

private def copyPayload (memory offset length mapping cursor : Expr) : Expr :=
  WordMapping.runHelper copyType WordMapping.type copyBody (packet [memory, offset, length, mapping, cursor])

/-- Append a log with zero to four topics. Inputs are evaluated once. Cursor
capacity is checked before memory expansion. The data snapshot is copied with
zero trailing padding, then ordinary sequential cell writes publish the
stream and cursor. -/
def append (memoryReference sizeReference logReference lengthReference address : Expr)
    (topics : List Expr) (offset length : Expr) : Expr :=
  if topics.length > 4 then LanguageResult.failure .unit (.word topicReason)
  else
    .letE (packet [memoryReference, sizeReference, logReference, lengthReference,
      address, offset, length, packet topics])
      (.letE (.loadCell (field 3 8 (.var 0)))
        (.letE (add (.var 0) (add (number (3 + topics.length)) (wordCount (field 6 8 (.var 1)))))
          (.ifE (.binary .wordGt (.var 1) (.var 0))
            (LanguageResult.failure .unit (.word capacityReason))
            (LanguageResult.bind .unit
              (Memory.touch (field 1 8 (.var 2)) (field 5 8 (.var 2)) (field 6 8 (.var 2)))
              (.letE (.loadCell (field 0 8 (.var 3)))
                (let headers := [field 4 8 (.var 4), number topics.length, field 6 8 (.var 4)] ++
                   (List.range topics.length).map (fun index => field index topics.length (field 7 8 (.var 4)))
                 LanguageResult.bind .unit
                   (insertWords (.loadCell (field 2 8 (.var 4))) (.var 3) headers)
                   (LanguageResult.bind .unit
                     (copyPayload (.var 1) (field 5 8 (.var 5)) (field 6 8 (.var 5))
                       (.var 0) (add (.var 4) (number (3 + topics.length))))
                     (LanguageResult.success
                       (.letE (.storeCell (field 2 8 (.var 6)) (.var 0))
                         (.storeCell (field 3 8 (.var 7)) (.var 5)))))))))))

structure Event where
  address : Word
  topics : List Word
  data : List UInt8
  deriving Repr, BEq

private def lookup (words : Array Word) (index : Nat) : Except String Word :=
  match words[index]? with
  | some value => pure value
  | none => .error s!"missing log stream word at {index}"

private def decodeLoop (stream : Array Word) (wordLength : Nat) :
    Nat → Nat → Nat → List Event → Except String (List Event)
  | fuel, budget, cursor, accumulator => do
      if cursor = wordLength then return accumulator.reverse
      match fuel with
      | 0 => throw "log export count limit exceeded"
      | fuel + 1 =>
          unless cursor + 3 ≤ wordLength do throw "truncated log header"
          let address ← lookup stream cursor
          let count ← lookup stream (cursor + 1)
          let size ← lookup stream (cursor + 2)
          unless count.val ≤ 4 do throw "log has more than four topics"
          unless size.val ≤ budget do throw "log data export byte limit exceeded"
          let words := (size.val + 31) / 32
          let dataStart := cursor + 3 + count.val
          let next := dataStart + words
          unless next ≤ wordLength do throw "truncated log data"
          let topics ← (List.range count.val).mapM fun index => lookup stream (cursor + 3 + index)
          let unused := (32 - size.val % 32) % 32
          if unused > 0 then
            let last ← lookup stream (next - 1)
            unless last.val % (256 ^ unused) = 0 do throw "nonzero log data padding"
          let data := (List.range size.val).map fun index =>
            UInt8.ofNat ((stream[dataStart + index / 32]?.getD Word.zero).val /
              (256 ^ (31 - index % 32)) % 256)
          decodeLoop stream wordLength fuel (budget - size.val) next ({address, topics, data} :: accumulator)

/-- Export a validated stream with bounded log count and total payload bytes.
Missing words, duplicate keys, malformed headers and padding are rejected.
The bounded mapping is indexed once before decoding payload bytes. -/
def decode (entries : WordMapping.Entries) (wordLength : Word)
    (maxLogs : Nat := 4096) (maxDataBytes : Nat := 1048576) : Except String (List Event) := do
  if wordLength.val > 8 * maxLogs + maxDataBytes / 32 then
    throw "log stream exceeds export limits"
  unless entries.length = wordLength.val do throw "log mapping size differs from its cursor"
  let mut words : Array (Option Word) := Array.replicate wordLength.val none
  for (key, value) in entries do
    unless key.val < wordLength.val do throw "log mapping key lies past its cursor"
    if words[key.val]!.isSome then throw "duplicate log stream words"
    words := words.set! key.val (some value)
  decodeLoop (words.map (·.getD Word.zero)) wordLength.val maxLogs maxDataBytes 0 []

/-- Decode the two Core cell snapshots used by contract receipts. -/
def decodeValues (mapping : Value) (wordLength : Value)
    (maxLogs : Nat := 4096) (maxDataBytes : Nat := 1048576) : Except String (List Event) := do
  let .word length := wordLength | throw "invalid log cursor value"
  if length.val > 8 * maxLogs + maxDataBytes / 32 then throw "log stream exceeds export limits"
  let rec entries : Nat → Value → WordMapping.Entries → Except String WordMapping.Entries
    | _, .constructed constructor .unit, accumulator =>
        if constructor = WordMapping.nilConstructor then pure accumulator.reverse
        else .error "invalid empty log mapping"
    | fuel + 1, .constructed constructor (.pair (.pair (.word key) (.word value)) tail), accumulator => do
        unless constructor = WordMapping.consConstructor do throw "invalid log mapping constructor"
        entries fuel tail ((key, value) :: accumulator)
    | _, _, _ => .error "invalid log mapping value or size"
  decode (← entries length.val mapping []) length maxLogs maxDataBytes

end Solcore.Frontend.RustHull.Logs
