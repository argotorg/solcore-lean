import Solcore.Frontend.RustHull.GlobalFunctionCorrespondence

/-! The real entry invocation after global installation: lookup reads the
registered closure and passes the original bundle past global and runtime
bindings, including the Unit binders introduced during installation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

theorem globalEnvironment_argument (signatures : List Signature) (base : Nat)
    (runtimeValues : Core.Environment) (input : Core.Value) (caller : Core.Environment) :
    (globalEnvironment signatures base (runtimeValues ++ input :: caller))[signatures.length + runtimeValues.length]? = some input := by
  rw [globalEnvironment_eq, List.getElem?_append_right (by simp)]
  simp only [List.length_reverse, List.length_map, List.length_zipIdx, Nat.add_sub_cancel_left]
  simp

theorem globalInvocation_rename (own : Signature) (index globals runtime offsetCount : Nat) :
    (globalInvocation own index globals runtime).rename (globalShift offsetCount) =
      Core.LanguageResult.bind own.result
        (Core.OptionalCell.read own.functionType (.var (offsetCount + index)) (Core.Word.ofNatModulo 1))
        (.apply (.var 0) (.var (offsetCount + (globals + runtime) + 1))) := by
  simp [globalInvocation, Core.LanguageResult.bind, Core.OptionalCell.read,
    Core.LanguageResult.failure, Core.LanguageResult.success, Core.Expr.rename,
    Core.Renaming.lift, globalShift]

/-- The selected installed closure is called in its exact capture environment.
The argument is the original public input bundle, with no host reconstruction. -/
theorem globalInvocation_evaluates {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse)
    {index : Nat} {code : GlobalCode} (selected : codes[index]? = some code)
    {base : Nat} {runtimeValues caller : Core.Environment} {input result : Core.Value}
    {store final : Core.Store}
    (installed : InstalledGlobals codes (globalLocations signatures base)
      (globalEnvironment signatures base (runtimeValues ++ input :: caller)) store)
    (evaluated : Core.Evaluates
      (input :: installationEnvironment
        (globalEnvironment signatures base (runtimeValues ++ input :: caller)) index)
      store (code.body.rename (globalShift index).lift) result final) :
    Core.Evaluates
      (installationEnvironment
        (globalEnvironment signatures base (runtimeValues ++ input :: caller)) codes.length)
      store ((globalInvocation code.own index signatures.length runtimeValues.length).rename
        (globalShift codes.length)) result final := by
  rw [globalInvocation_rename]
  have reference : (globalEnvironment signatures base (runtimeValues ++ input :: caller))[index]? =
      some (.cellRef (Core.OptionalCell.cellType code.own.functionType)
        (globalLocations signatures base index)) := by
    apply globalEnvironment_lookup
    simp only [← aligned, List.getElem?_map, selected, Option.map_some]
  have read := Core.OptionalCell.read_success (Core.Word.ofNatModulo 1)
    (Core.Evaluates.var (installationEnvironment_lookup reference codes.length))
    (installed index code selected)
  apply Core.LanguageResult.bind_success code.own.result read
  apply Core.Evaluates.apply (.var rfl) (Core.Evaluates.var ?_) evaluated
  exact installationEnvironment_lookup
    (globalEnvironment_argument signatures base runtimeValues input caller) codes.length

end Solcore.Frontend.RustHull.Correspondence
