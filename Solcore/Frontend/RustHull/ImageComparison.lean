import Solcore.Frontend.RustHull.CodeBuilder
import Solcore.Frontend.RustHull.Memory

/-! Exact packed image comparison on Core. One pass over the input mapping
uses a bitmap to preserve first-key semantics, including duplicate and missing
entries. A balanced constant table avoids repeated linear mapping lookups. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ImageComparison
open Core CodeBuilder

private def table (values : List Code) (key : Code) (base : Nat := 0) : Code :=
  match _equality : values with
  | [] => number 0
  | [value] => value
  | _ :: _ :: _ =>
    let middle := values.length / 2
    choose (binary .wordGt (number (base + middle)) key)
      (table (values.take middle) key base)
      (table (values.drop middle) key (base + middle))
termination_by values.length
 decreasing_by all_goals simp_wf; simp_all only [List.length_cons]; omega

private def compareBody (bytes : List UInt8) : Core.Expr := Id.run do
  let count := (bytes.length + 31) / 32
  let buckets := (count + 255) / 256
  let masksType := bundleType (List.replicate buckets .word)
  let parameter := Core.Ty.product WordMapping.type masksType
  let entries := Memory.packBytes bytes
  let words := (List.range count).map fun index =>
    WordMapping.lookupEntries (Word.ofNatModulo index) entries
  let needed := (List.range buckets).map fun bucket =>
    (List.range (min 256 (count - bucket * 256))).foldl (fun mask offset =>
      if (words[bucket * 256 + offset]?.getD Word.zero).val == 0 then mask else mask + 2 ^ offset) 0
  let complete (masks : Code) := needed.zipIdx.foldr (fun (bits, index) next =>
    choose (binary .wordEq (binary .wordAnd (part index buckets masks) (number bits)) (number bits))
      next (success (boolean false))) (success (boolean true))
  let step := bind (constant (bundle [.var 0, .var 1, .var 2])) fun args =>
    let entry := part 0 3 args
    let key := part 0 2 (part 0 2 entry)
    let value := part 1 2 (part 0 2 entry)
    let tail := part 1 2 entry
    let seen := part 1 2 (part 1 3 args)
    let recurse (masks : Code) : Code := fun depth => WordMapping.invoke parameter .bool
      (part 2 3 args depth) (.pair (tail depth) (masks depth))
    choose (binary .wordGt (number count) key)
      (bind (binary .wordDiv key (number 256)) fun bucket =>
       bind (binary .wordShl (number 1) (binary .wordMod key (number 256))) fun bit =>
       bind (table ((List.range buckets).map fun index => part index buckets seen) bucket) fun mask =>
       choose (binary .wordEq (binary .wordAnd mask bit) (number 0))
         (let expected := table (words.map (constant ∘ Core.Expr.word)) key
          let shift := choose (binary .wordEq key (number (count - 1)))
            (number ((32 - (bytes.length - (count - 1) * 32)) * 8)) (number 0)
          choose (binary .wordEq (binary .wordShr value shift) (binary .wordShr expected shift))
            (recurse (packet ((List.range buckets).map fun index =>
              choose (binary .wordEq bucket (number index)) (binary .wordOr mask bit)
                (part index buckets seen))))
            (success (boolean false)))
         (recurse seen))
      (recurse seen)
  return .matchData WordMapping.dataType (LanguageResult.resultType .bool) (.first (.var 0))
    [(complete (constant (.second (.var 1)))) 0, step 0]

/-- Compare every byte in the image; bytes beyond the image are ignored only
when `allowSuffix` is true. Missing entries are zero and the first duplicate
key wins, exactly as in packed memory reads. Inputs evaluate once. -/
def compareBytes (bytes : List UInt8) (memory size : Core.Expr) (allowSuffix : Bool := false) : Core.Expr :=
  let buckets := (((bytes.length + 31) / 32) + 255) / 256
  let masksType := bundleType (List.replicate buckets .word)
  (bind (constant (.pair memory size)) fun input =>
    let compare : Code := fun depth => WordMapping.runHelper (.product WordMapping.type masksType) .bool
      (compareBody bytes) (.pair (part 0 2 input depth) (bundle (List.replicate buckets (.word Word.zero))))
    choose (if allowSuffix then binary .wordGt (number bytes.length) (part 1 2 input)
      else binary .wordEq (part 1 2 input) (number bytes.length))
      (if allowSuffix then success (boolean false) else compare)
      (if allowSuffix then compare else success (boolean false))) 0

end Solcore.Frontend.RustHull.ImageComparison
