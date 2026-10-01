import Solcore.SourceSemantics.CoreLowering.CompatibleBuiltinMeaning
import Solcore.Test.SourceCompilerFeatureSupport

/-! The real seven builtin bodies retain arbitrary captures and stores. A
selected argument allocates once before invocation; completed executions recover
the independent source primitive result and exactly that post-argument store. -/
set_option autoImplicit false
namespace Tests.SourceCoreBuiltinBodyMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open BuiltinBodyMeaning

private def effectfulArgument : Expr :=
  .letE (.newCell .integer (.integer 37)) (.pair (.integer (-9)) (.integer 4))

private theorem argument_meaning (environment : Environment) (store : Store) :
    Evaluates environment store effectfulArgument (.pair (.integer (-9)) (.integer 4))
      (store ++ [.integer 37]) :=
  .letE (.newCell .integer) (.pair .integer .integer)

/-- The primitive body uses the selected packed argument after its allocation,
even when arbitrary ambient values are captured by the actual compiler closure. -/
theorem effectful_sub_preserves (environment : Environment) (store : Store) :
    Evaluates environment store
      (.apply (SourceCoreInteger.builtinClosure .integerSub) effectfulArgument)
      (.inRight .word (.integer (-13))) (store ++ [.integer 37]) := by
  obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ :=
    (InputRep.integerSub (-9) 4).closure_preserves (argument_meaning environment store)
  cases applied
  cases related
  exact evaluated

/-- Completion alone determines the source result, retains the argument effect,
and preserves the entire supplied native store prefix. -/
theorem effectful_sub_reflects {environment : Environment} {store finalStore : Store}
    {result : Value}
    (completed : Evaluates environment store
      (.apply (SourceCoreInteger.builtinClosure .integerSub) effectfulArgument)
      result finalStore) :
    Dynamic.BuiltinApplies .integerSub [.integer (-9), .integer 4] (.integer (-13)) ∧
      result = .inRight .word (.integer (-13)) ∧ finalStore = store ++ [.integer 37] := by
  obtain ⟨sourceResult, nativeResult, applied, related, resultEq, storeEq⟩ :=
    (InputRep.integerSub (-9) 4).closure_reflects (argument_meaning environment store) completed
  cases applied
  cases related
  exact ⟨.integerSub (-9) 4, resultEq, storeEq⟩

private def huge : Int := (2 : Int) ^ 1024 + 17
private def ambient : Value := .closure .integer .integer (.loadCell (.var 1)) [.cellRef .integer 1]
private def environment : Environment := [.integer 999, ambient]
private def store : Store := [ambient, .integer huge]

private def cases : List (BuiltinFunctionId × Expr × Value) := [
  (.integerSub, .pair (.integer (-huge)) (.integer 19), .integer (-huge - 19)),
  (.integerAdd, .pair (.integer huge) (.integer (-19)), .integer (huge - 19)),
  (.integerMul, .pair (.integer huge) (.integer (-huge)), .integer (-(huge * huge))),
  (.integerEq, .pair (.integer huge) (.integer huge), .bool true),
  (.integerEq, .pair (.integer huge) (.integer (-huge)), .bool false),
  (.integerLt, .pair (.integer (-huge)) (.integer 0), .bool true),
  (.integerLt, .pair (.integer huge) (.integer 0), .bool false),
  (.wordFromInteger, .integer (-huge), .word (Word.ofIntModulo (-huge))),
  (.wordFromInteger, .integer huge, .word (Word.ofIntModulo huge)),
  (.wordToInteger, .word (Word.ofNatModulo (wordModulus - 1)), .integer (Int.ofNat (wordModulus - 1)))
]

private def check (function : BuiltinFunctionId) (argument : Expr) (expected : Value) : IO Unit := do
  let argument := Expr.letE (.newCell .integer (.integer 37)) argument
  let initial : Core.State := ⟨.eval (.apply (SourceCoreInteger.builtinClosure function) argument) environment, [], store⟩
  let complete := runStateful 1000 initial
  SourceCompilerFeatureSupport.require
    (complete == .done (.inRight .word expected) (store ++ [.integer 37]))
    "actual builtin body changed its result, captures, store prefix, or argument allocation"
  for fuel in [0, 3, 9, 15] do
    match runStateful fuel initial with
    | .outOfFuel checkpoint =>
        SourceCompilerFeatureSupport.require (runStateful 1000 checkpoint == complete)
          "actual builtin resume repeated argument effects or changed result/store"
    | .done value finalStore =>
        SourceCompilerFeatureSupport.require
          (StatefulRunResult.done value finalStore == complete) "completed builtin prefix differed"
    | _ => throw (IO.userError "actual builtin prefix became stuck")

def run : IO Unit := do
  for (function, argument, expected) in cases do
    check function argument expected
  IO.println "actual builtin bodies: seven independent meanings, captures, argument effects, integers and resume GREEN"
end Tests.SourceCoreBuiltinBodyMeaning
