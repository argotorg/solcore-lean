import Solcore.SourceSemantics.CoreLowering.BuiltinCallCertificates
import Solcore.SourceSemantics.CoreLowering.BuiltinCallProtocol
import Solcore.SourceSemantics.CoreLowering.BuiltinCallSource
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.ProgramChecking

/-! Actual tagged/contracted builtin invocation retains argument effects and
skips later arguments after a source failure. Independent source application
and static compiler selection are exercised without a source evaluator. -/
set_option autoImplicit false
namespace Tests.SourceCoreBuiltinCalls
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open BuiltinBodyMeaning BuiltinCalls.Protocol

private def identity : Word := Word.ofNatModulo 9
private def contract : Word := Word.ofNatModulo 17
private def unknown : Word := Word.ofNatModulo 29
private def arguments : Expr :=
  .letE (.newCell .integer (.integer 37))
    (LanguageResult.success (.pair (.integer (-9)) (.integer 4)))

private theorem argument_meaning (environment : Environment) (store : Store) :
    Evaluates (.unit :: contractedValue .integerSub identity contract environment :: environment) store
      ((arguments.weakenAt 0).weakenAt 0) (.inRight .word (.pair (.integer (-9)) (.integer 4)))
      (store ++ [.integer 37]) := by
  simp only [arguments, Expr.weakenAt, LanguageResult.success]
  exact .letE (.newCell .integer) (.inRight (.pair .integer .integer))

theorem contracted_sub_preserves (environment : Environment) (store : Store) :
    Evaluates environment store
      (CallableContract.call [⟨contract, none, none⟩] unknown .integer
        (contracted .integerSub identity contract) arguments)
      (.inRight .word (.integer (-13))) (store ++ [.integer 37]) := by
  obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ :=
    contracted_preserves (InputRep.integerSub (-9) 4) (argument_meaning environment store)
  cases applied
  cases related
  exact evaluated

theorem contracted_sub_reflects {environment : Environment} {store finalStore : Store} {result : Value}
    (completed : Evaluates environment store
      (CallableContract.call [⟨contract, none, none⟩] unknown .integer
        (contracted .integerSub identity contract) arguments) result finalStore) :
    Dynamic.BuiltinApplies .integerSub [.integer (-9), .integer 4] (.integer (-13)) ∧
      result = .inRight .word (.integer (-13)) ∧ finalStore = store ++ [.integer 37] := by
  obtain ⟨sourceResult, nativeResult, applied, related, resultEq, storeEq⟩ :=
    contracted_reflects (InputRep.integerSub (-9) 4) (argument_meaning environment store) completed
  cases applied
  cases related
  exact ⟨.integerSub (-9) 4, resultEq, storeEq⟩

private def huge : Int := (2 : Int) ^ 1024 + 17
private def ambient : Value := .closure .integer .integer (.loadCell (.var 1)) [.cellRef .integer 1]
private def store : Store := [ambient, .integer huge]
private def environment : Environment := [.integer 99, ambient]

private def checkNative (code : Expr) (result : Value) (after : Store) : IO Unit := do
  let initial : Core.State := ⟨.eval code environment, [], store⟩
  let complete := runStateful 1000 initial
  SourceCompilerFeatureSupport.require (complete == .done result after)
    "builtin call changed argument order/effects, result or ambient store"
  for fuel in [0, 5, 11, 23, 37] do
    match runStateful fuel initial with
    | .outOfFuel checkpoint =>
        SourceCompilerFeatureSupport.require (runStateful 1000 checkpoint == complete)
          "builtin checkpoint/resume changed argument effects or result/store"
    | .done value finalStore =>
        SourceCompilerFeatureSupport.require (StatefulRunResult.done value finalStore == complete)
          "completed builtin prefix changed result/store"
    | _ => throw (IO.userError "builtin call became stuck")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function sub(a: integer, b: integer) returns (integer) { return integerSub(a, b); }",
    "function add(a: integer, b: integer) returns (integer) { return integerAdd(a, b); }",
    "function mul(a: integer, b: integer) returns (integer) { return integerMul(a, b); }",
    "function eq(a: integer, b: integer) returns (Bool) { return integerEq(a, b); }",
    "function lt(a: integer, b: integer) returns (Bool) { return integerLt(a, b); }",
    "function from(a: integer) returns (Word) { return wordFromInteger(a); }",
    "function to(a: Word) returns (integer) { return wordToInteger(a); }"]}] }

def run : IO Unit := do
  checkNative (TaggedFunction.call .integer (tagged .integerSub identity) arguments)
    (.inRight .word (.integer (-13))) (store ++ [.integer 37])
  checkNative (CallableContract.call [⟨contract, none, none⟩] unknown .integer
    (contracted .integerSub identity contract) arguments)
    (.inRight .word (.integer (-13))) (store ++ [.integer 37])
  let reason := Word.ofNatModulo 41
  let failed : Expr := .letE (.newCell .integer (.integer 37)) (LanguageResult.failure .integer (.word reason))
  let later : Expr := .letE (.newCell .integer (.integer 73)) (LanguageResult.success (.integer 4))
  let failedArguments := LocalSequence.pair .integer .integer failed later
  checkNative (TaggedFunction.call .integer (tagged .integerSub identity) failedArguments)
    (.inLeft .integer (.word reason)) (store ++ [.integer 37])
  checkNative (CallableContract.call [⟨contract, none, none⟩] unknown .integer
    (contracted .integerSub identity contract) failedArguments)
    (.inLeft .integer (.word reason)) (store ++ [.integer 37])
  let checked ← SourceCompilerFeatureSupport.get "builtin actual source checker" (checkProgram workspace)
  let cases : List (String × List SourceCoreExecution.Value × SourceCoreExecution.Value) := [
    ("sub", [.integer (-huge), .integer 19], .integer (-huge - 19)),
    ("add", [.integer huge, .integer (-19)], .integer (huge - 19)),
    ("mul", [.integer huge, .integer (-huge)], .integer (-(huge * huge))),
    ("eq", [.integer huge, .integer huge], .bool true),
    ("eq", [.integer huge, .integer (-huge)], .bool false),
    ("lt", [.integer (-huge), .integer 0], .bool true),
    ("lt", [.integer huge, .integer 0], .bool false),
    ("from", [.integer (-huge)], .word (Word.ofIntModulo (-huge))),
    ("from", [.integer huge], .word (Word.ofIntModulo huge)),
    ("to", [.word (Word.ofNatModulo (wordModulus - 1))], .integer (Int.ofNat (wordModulus - 1)))
  ]
  for (name, inputs, expected) in cases do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    SourceCompilerFeatureSupport.require ((← entry.run inputs) == expected)
      "actual cached compiler builtin call changed fixed signature, identity, code or scalar result"
    entry.checkResume inputs expected
  IO.println "actual builtin calls: compiler receipts, pure gates, ordered argument effects, failures and resume GREEN"
end Tests.SourceCoreBuiltinCalls
