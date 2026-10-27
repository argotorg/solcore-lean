import Solcore.Synthesis.Source.MethodsCases

/-! Golden dispatch cases for the several-methods profile. The expected outcome
of every case is written out from the pinned std's `dispatch.sol` and the
compiler's `prepare.rs`, not computed by either model: a method runs exactly
when the calldata selector is its own; calldata shorter than four bytes or
with another selector reverts with `0x4924aef0`; a method whose arguments are
missing reverts with `0x08638556`. The steps add a known constant, so each
method's slots and result follow by hand: with input `x` and constant `c` from
empty storage, slot zero and the method's slot hold `x + c`, slot one holds 1
and the result is `2(x + c) + 1`, which an odd input reverts. Contracts declare
the same methods with ascending, descending and mixed selectors, and one
sequence checks the shared slots across methods. Both the Core wrapper and the
byte-level `stdDispatch` must give each outcome. -/
set_option autoImplicit false

namespace Tests.SourceMethodsGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.MethodsExecution (Method Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The byte model's dispatch decision: the method position, or the rejection. -/
private def dispatches (shapes : List ContractMethods.Shape) (input : ByteArray) (expected : Except Nat Nat) : Bool :=
  match MethodsExecution.stdDispatch shapes input, expected with
  | .ok actual, .ok wanted => actual == wanted
  | .error actual, .error wanted => actual == wanted
  | _, _ => false

/-- The four methods with their selectors, as `cast sig` prints them, and
their constants. -/
private def P : Method := ⟨"m_00000001", 1⟩
private def Q : Method := ⟨"m_00000002", 0⟩
private def R : Method := ⟨"m_00000003", 2⟩
private def S : Method := ⟨"m_00000004", 1⟩
private def selectors : List (Method × Nat) :=
  [(P, 0x935853e4), (Q, 0xf3cfdf58), (R, 0x336e1e08), (S, 0x06d154aa)]
private def constant (method : Method) : Nat :=
  if method == P then 1 else if method == Q then 2 else if method == R then 3 else 4
/-- The missing selector, of `m_0000000f(uint256)`. -/
private def missing : Nat := 0x43c9d5b5

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
private def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- Contracts by name and expected selector order. -/
private def contracts : List (String × List Method × String) := [
  ("two-ascending", [S, P], "ascending"), ("two-descending", [Q, R], "descending"),
  ("three-ascending", [R, P, Q], "ascending"), ("three-descending", [Q, P, S], "descending"),
  ("three-mixed", [P, S, Q], "mixed"), ("four-ascending", [S, R, P, Q], "ascending"),
  ("four-descending", [Q, P, R, S], "descending"), ("four-mixed", [P, Q, R, S], "mixed")]

private def slots (values : List Nat) : Json :=
  toJson ((List.range 6).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def wordText (value : Nat) : String := encodeBytesText (encodeWordBytesBE (w value))

/-- The expected row: status, output Word and slots zero to five. -/
private structure Expected where
  status : String
  output : Nat
  values : List Nat

private def noSelector : Expected := ⟨"reverted", StdDispatch.noSelectorError, []⟩
private def truncated : Expected := ⟨"reverted", StdDispatch.truncatedError, []⟩

/-- One call of method `position` with input sum `x` from empty storage. -/
private def fromEmpty (methods : List Method) (position x : Nat) : Expected :=
  let computed := x + constant (methods.getD position P)
  let result := 2 * computed + 1
  if x % 2 = 1 then ⟨"reverted", result, []⟩
  else ⟨"returned", result, (List.range 6).map fun slot =>
    if slot = 0 || slot = 2 + position then computed else if slot = 1 then 1 else 0⟩

private def selectorBytes (selector : Nat) : List UInt8 :=
  [(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

private def raw (selector : Nat) (words : List Nat) : ByteArray :=
  words.foldl (fun bytes value => bytes ++ encodeWordBytesBE (w value)) (ByteArray.mk (selectorBytes selector).toArray)

/-- The original Core contract run once from an empty world on raw calldata. -/
private def runRaw (contract : CheckedCoreContract) (input : ByteArray) (fuel : Nat) : IO Json := do
  let bindings := StorageExecution.fixtureBindings
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let world := StorageExecution.initialWorldForContract contract bindings
  let some ⟨resolved, installed⟩ := registry.resolve? world bindings.address
    | throw (IO.userError "contract does not resolve")
  if bounded : input.size < Solcore.Core.wordModulus then
    let invocation : TopLevelInvocation := {
      target := bindings.address, caller := bindings.caller, callValue := Word.zero,
      inputData := ⟨input, bounded⟩ }
    match TopLevelExecution.run resolved invocation installed fuel with
    | .completed terminal =>
        let storage := match terminal.finalWorld.account? bindings.address with
          | some account => MethodsExecution.storageJson account
          | none => Json.null
        let fields := match terminal.outcome with
          | .returned output => [("status", toJson "returned"), ("output", toJson (encodeBytesText output))]
          | .reverted output => [("status", toJson "reverted"), ("output", toJson (encodeBytesText output))]
          | .trapped _ => [("status", toJson "trapped")]
        return Json.mkObj (fields ++ [("committedStorage", storage)])
    | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "golden case exhausted fuel")
  else throw (IO.userError "golden input exceeds a Word")

private def check (name : String) (row : Json) (expected : Expected) : IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (wordText expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (slots expected.values))
    s!"{name}: original Core differs from the expected row {row.compress}"

def testSourceMethodsGolden : IO Unit := do
  let fuel := 1000000
  for (method, expected) in selectors do
    ensure (method.selector == expected) s!"{method.signature}: the Keccak selector differs from cast sig"
  ensure ((⟨"m_0000000f", 1⟩ : Method).selector == missing) "the missing selector differs from cast sig"
  for (name, methods, order) in contracts do
    let shapes := methods.map (·.shape)
    let some plan := ContractMethods.CheckedPlan.ofParts? shapes (← methods.mapM (step ∘ constant))
      | throw (IO.userError s!"{name}: the methods wrapper failed admission")
    ensure (Solcore.Synthesis.Source.Methods.selectorOrder methods == order) s!"{name}: selector order differs"
    for (method, position) in methods.zipIdx do
      -- Each method with an even and, if it has arguments, an odd input.
      let inputs : List (List Nat) := match method.arity with
        | 0 => [[]]
        | 1 => [[6], [7]]
        | _ => [[2, 4], [2, 5]]
      for values in inputs do
        let tx : Transaction := ⟨"tx-0", some position, values.map w⟩
        let input := MethodsExecution.inputBytes methods missing tx
        ensure (dispatches shapes input (.ok position)) s!"{name}: the byte model dispatches elsewhere"
        let history := MethodsExecution.observe plan methods missing [tx] StorageExecution.fixtureBindings fuel
        let some row := (← get (history.getObjValAs? (Array Json) "transactions"))[0]? | throw (IO.userError "no row")
        check s!"{name} {method.name} {values}" row (fromEmpty methods position (values.foldl (· + ·) 0))
      -- Missing arguments are truncated; an extra Word is ignored.
      if method.arity > 0 then
        let input := raw method.selector []
        ensure (dispatches shapes input (.error StdDispatch.truncatedError))
          s!"{name}: the byte model accepts missing arguments"
        check s!"{name} {method.name} without arguments" (← runRaw plan.contract input fuel) truncated
      let extra := raw method.selector ((List.replicate method.arity 2) ++ [9])
      ensure (dispatches shapes extra (.ok position)) s!"{name}: the byte model rejects an extra Word"
      check s!"{name} {method.name} with an extra Word" (← runRaw plan.contract extra fuel)
        (fromEmpty methods position (2 * method.arity))
    -- The missing selector, short calldata and the empty calldata reach the fallback.
    for input in [raw missing [1], ByteArray.mk ((selectorBytes (methods.getD 0 P).selector).take 3).toArray,
        ByteArray.empty] do
      ensure (dispatches shapes input (.error StdDispatch.noSelectorError))
        s!"{name}: the byte model dispatches a missing selector"
      check s!"{name} missing selector" (← runRaw plan.contract input fuel) noSelector
  -- One sequence on four mixed methods [P, Q, R, S] shares slots zero and one.
  let methods := [P, Q, R, S]
  let some plan := ContractMethods.CheckedPlan.ofParts? (methods.map (·.shape)) (← methods.mapM (step ∘ constant))
    | throw (IO.userError "the four-method wrapper failed admission")
  let transactions : List Transaction := [⟨"tx-0", some 2, [w 2, w 4]⟩, ⟨"tx-1", some 0, [w 10]⟩,
    ⟨"tx-2", none, [w 1]⟩, ⟨"tx-3", some 3, [w 3]⟩, ⟨"tx-4", some 1, []⟩]
  let history := MethodsExecution.observe plan methods missing transactions StorageExecution.fixtureBindings fuel
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  -- R(2, 4): 6 + 0 + 3 = 9, result 9 + 1 + 9. P(10): 10 + 9 + 1 = 20, result 20 + 2 + 20.
  -- The missing selector and S(3), odd with 3 + 20 + 4 = 27 and result 57, commit nothing.
  -- Q(): 0 + 20 + 2 = 22, result 22 + 3 + 22.
  let expected : List Expected := [⟨"returned", 19, [9, 1, 0, 0, 9, 0]⟩, ⟨"returned", 42, [20, 2, 20, 0, 9, 0]⟩,
    ⟨"reverted", StdDispatch.noSelectorError, [20, 2, 20, 0, 9, 0]⟩, ⟨"reverted", 57, [20, 2, 20, 0, 9, 0]⟩,
    ⟨"returned", 47, [22, 3, 20, 22, 9, 0]⟩]
  ensure (rows.size == expected.length) "the shared sequence lost a row"
  for (row, golden) in rows.toList.zip expected do
    check "shared sequence" row golden

end Tests.SourceMethodsGolden
