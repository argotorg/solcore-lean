import Solcore.Frontend.RustHull.CodeBuilder
import Solcore.Frontend.RustHull.Memory

/-! Retained byte ranges in packed Core memory. Aligned ranges traverse the
mapping once, retaining entry order and therefore first-match lookup semantics.
Unaligned ranges use the existing byte-accurate copy operation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemorySnapshot
open Core CodeBuilder

def definitions : DataEnvironment := Memory.definitions
private def parameter : Core.Ty := bundleType [WordMapping.type, .word, .word, .word]

private def alignedBody : Core.Expr :=
  .matchData WordMapping.dataType (LanguageResult.resultType WordMapping.type)
    (projectArgument 0 4 (.var 0))
    [LanguageResult.success WordMapping.empty,
      (bind (constant (bundle [.var 0, .var 1, .var 2])) fun args =>
        let entry := part 0 3 args
        let key := part 0 2 (part 0 2 entry)
        let value := part 1 2 (part 0 2 entry)
        let tail := part 1 2 entry
        let inputs := part 1 3 args
        let start := part 1 4 inputs
        let last := part 2 4 inputs
        let shift := part 3 4 inputs
        let recurse : Code := fun depth => WordMapping.invoke parameter WordMapping.type
          (part 2 3 args depth) (packet [tail, start, last, shift] depth)
        choose (binary .wordGt start key) recurse <|
        choose (binary .wordGt key (number ((wordModulus - 1) / 32))) recurse <|
        bind (binary .wordSub key start) fun rebased =>
        choose (binary .wordGt rebased last) recurse <|
        bindResult WordMapping.type recurse fun next =>
        success (fun depth => WordMapping.cons (rebased depth)
          (choose (binary .wordEq rebased last)
            (binary .wordShl (binary .wordShr value shift) shift) value depth) (next depth))) 0]

/-- Copy a retained memory range to byte zero. Inputs evaluate once. The aligned
path filters and rebases packed entries without repeated mapping lookups;
missing bytes and bytes beyond the Word address space remain zero. Length is
subject to the same destination-size check as `Memory.copyPackedFrom`. -/
def extract (mapping offset length : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [mapping, offset, length])) fun args =>
    let source := part 0 3 args
    let offset := part 1 3 args
    let length := part 2 3 args
    bind (allocate .word (number 0)) fun size =>
    bindResult WordMapping.type (fun depth => Memory.touch (size depth) (number 0 depth) (length depth)) fun _ =>
    choose (binary .wordEq length (number 0)) (success empty) <|
    choose (binary .wordEq (binary .wordMod offset (number 32)) (number 0))
      (fun depth => WordMapping.runHelper parameter WordMapping.type alignedBody
        (packet [source, binary .wordDiv offset (number 32),
          binary .wordDiv (binary .wordSub length (number 1)) (number 32),
          binary .wordMul (binary .wordMod
            (binary .wordSub (number 32) (binary .wordMod length (number 32))) (number 32))
            (number 8)] depth))
      (bind (allocate WordMapping.type empty) fun destination =>
        bindResult WordMapping.type (fun depth => Memory.copyPackedFrom
          (destination depth) (size depth) (number 0 depth) (source depth) (offset depth) (length depth)) fun _ =>
        success (load destination))) 0

end Solcore.Frontend.RustHull.MemorySnapshot
