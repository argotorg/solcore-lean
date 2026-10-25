import Solcore.Frontend.RustHull.MemoryCopySemantics
import Solcore.Frontend.RustHull.TerminationSemantics

/-! Return-data copying checks its complete source range before touching memory.
An invalid source range terminates the message even for a zero-length copy;
a valid range follows the ordinary packed-input copy and its destination faults. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ReturnDataSemantics
open Core

inductive Execute (entries : MemorySemantics.Entries) (size destination source length : Word) :
    RuntimeEffectsSemantics.State → Semantics.Result Semantics.Value → RuntimeEffectsSemantics.State → Prop where
  | sourceOverflow (initial : RuntimeEffectsSemantics.State) (invalid : source > size) :
      Execute entries size destination source length initial
        (TerminationSemantics.terminate initial 3 Word.zero Word.zero).1
        (TerminationSemantics.terminate initial 3 Word.zero Word.zero).2
  | lengthOverflow (initial : RuntimeEffectsSemantics.State)
      (sourceValid : ¬ source > size) (invalid : length > size.sub source) :
      Execute entries size destination source length initial
        (TerminationSemantics.terminate initial 3 Word.zero Word.zero).1
        (TerminationSemantics.terminate initial 3 Word.zero Word.zero).2
  | copied {initial : RuntimeEffectsSemantics.State} {memory : MemorySemantics.State}
      {result : Semantics.Result Semantics.Value}
      (sourceValid : ¬ source > size) (lengthValid : ¬ length > size.sub source)
      (executed : MemoryCopySemantics.From entries destination source length initial.memory result memory) :
      Execute entries size destination source length initial result {initial with memory := memory}

inductive Builtin (entries : MemorySemantics.Entries) (size : Word) : String → Ty → List Semantics.Value →
    RuntimeEffectsSemantics.State → Semantics.Result Semantics.Value → RuntimeEffectsSemantics.State → Prop where
  | copy {type : Ty} {destination source length : Word}
      {initial final : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
      (executed : Execute entries size destination source length initial result final) :
      Builtin entries size "returndatacopy" type [.word destination, .word source, .word length] initial result final

theorem Builtin.named {entries : MemorySemantics.Entries} {size : Word} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : Builtin entries size name type arguments initial result final) : name = "returndatacopy" := by
  cases called
  rfl

end Solcore.Frontend.RustHull.ReturnDataSemantics
