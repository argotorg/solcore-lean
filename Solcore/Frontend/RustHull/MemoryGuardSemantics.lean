import Solcore.Frontend.RustHull.Semantics

/-! A memory guard supplies the same word to its caller. It carries no runtime
state transition in the independent Hull semantics. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryGuardSemantics

inductive Builtin : String → Ty → List Semantics.Value → Semantics.Result Semantics.Value → Prop where
  | guarded {type : Ty} {value : Core.Word} :
      Builtin "memoryguard" type [.word value] (.value (.word value))

theorem Builtin.named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {result : Semantics.Result Semantics.Value} (called : Builtin name type arguments result) :
    name = "memoryguard" := by
  cases called
  rfl

end Solcore.Frontend.RustHull.MemoryGuardSemantics
