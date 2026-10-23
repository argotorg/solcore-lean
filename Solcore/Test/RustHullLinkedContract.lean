import Solcore.Frontend.RustHull.LinkedContract

/-! Synthetic object-frame regressions for linking, constructor input and
storage transfer. Actual compiler image parity is exercised by the export gate. -/
set_option autoImplicit false
namespace Tests.RustHullLinkedContract
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (label : String) : LowerM α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def name (value : String) : YulName := {name := value}
private def w (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def symbol (value : String) : YulExpr := ⟨.literal (.string ("\"" ++ value ++ "\"")), none⟩
private def call (value : String) (args : List YulExpr := []) : YulExpr := ⟨.call (name value) args, none⟩
private def action (value : String) (args : List YulExpr := []) : YulStmt := ⟨.expression (call value args), none⟩
private def code (body : List YulStmt) : CodeBlock := {
  stmts := [⟨.assembly body, none⟩]
  functions := []
}
private def bytes (values : List Nat) : List UInt8 := values.map UInt8.ofNat
private def wordBytes (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value / 256 ^ (31 - index) % 256)
private def deployName := "ConstructorObjectNameLongerThanAnEvmWordBytes"
private def runtimeName := "RuntimeObjectNameLongerThanThirtyTwoBytes"
private def runtimeBytes : List UInt8 := bytes [0x60, 0, 0x55, 0xf3]
private def images : List CodeImage.Image := [
  {path := [deployName], bytes := bytes [0xaa, 0xbb] ++ runtimeBytes,
    embeds := [{name := runtimeName, offset := 2, size := runtimeBytes.length}]},
  {path := [deployName, runtimeName], bytes := runtimeBytes}]
private def runtimeBody : List YulStmt := [
  action "mstore" [w 0, call "sload" [w 0]],
  action "mstore" [w 32, call "sload" [w 1]],
  action "mstore" [w 64, call "codesize"], action "return" [w 0, w 96]]
private def source (init : List YulStmt) (runtime : List YulStmt := runtimeBody) : Program := {
  functions := []
  entryPoints := []
  objects := [.object deployName (code init) [.object runtimeName (code runtime) [] none] none]
}
private def initializer : List YulStmt := [
  action "sstore" [w 0, w 7],
  action "codecopy" [w 0, call "datasize" [symbol deployName],
    call "sub" [call "codesize", call "datasize" [symbol deployName]]],
  action "sstore" [w 0, call "mload" [w 0]],
  action "sstore" [w 1, call "calldatasize"],
  action "codecopy" [w 0, call "dataoffset" [symbol runtimeName], call "datasize" [symbol runtimeName]],
  action "return" [w 0, call "datasize" [symbol runtimeName]],
  action "sstore" [w 0, w 99]]

private def rejects (label : String) (value : LowerM Contract.Prepared) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{label}: malformed linked object was accepted")

private def expectBytes (label : String) (outcome : Contract.Outcome) (expected : List UInt8) : IO Core.WordMapping.Entries :=
  match outcome with
  | .returned actual storage => do
      require (actual == expected) s!"{label}: unexpected output {reprStr actual}"
      pure storage
  | other => throw (IO.userError s!"{label}: {reprStr other}")

def runDeploymentContext : IO Unit := do
  let program := source [
    action "sstore" [w 0, call "calldatasize"],
    action "sstore" [w 1, call "callvalue"],
    action "sstore" [w 2, call "selfbalance"],
    action "sstore" [w 3, call "call" [w 0, call "address", w 0, w 0, w 0, w 0, w 0]],
    action "codecopy" [w 0, call "datasize" [symbol deployName], w 32],
    action "sstore" [w 4, call "mload" [w 0]],
    action "codecopy" [w 0, call "dataoffset" [symbol runtimeName], call "datasize" [symbol runtimeName]],
    action "return" [w 0, call "datasize" [symbol runtimeName]]]
  let prepared ← get "deployment context helper" (LinkedContract.prepareDeployment program [deployName]
    images (wordBytes 42) {
      calldata := bytes [0xaa, 0xbb]
      address := Core.Word.ofNatModulo 0xaaa
      value := Core.Word.ofNatModulo 17
      balance := Core.Word.ofNatModulo 117})
  require (prepared.context.calldata.isEmpty && !prepared.context.selfCodeAvailable)
    "deployment helper retained runtime-only frame context"
  let storage ← expectBytes "deployment helper preserves linked constructor arguments"
    (Contract.run prepared) runtimeBytes
  for (slot, value) in [(0, 0), (1, 17), (2, 117), (3, 1), (4, 42)] do
    require ((Core.WordMapping.lookupEntries (Core.Word.ofNatModulo slot) storage).val = value)
      s!"deployment helper lost constructor state at {slot}"

def run : IO Unit := do
  runDeploymentContext
  let program := source initializer
  let constructor ← get "constructor" (LinkedContract.prepare program [deployName] images (wordBytes 42))
  let state ← expectBytes "constructor returns exact embedded bytes" (Contract.run constructor) runtimeBytes
  require ((Core.WordMapping.lookupEntries Core.Word.zero state).val = 42)
    "constructor tail arguments were not loaded into storage"
  require ((Core.WordMapping.lookupEntries (Core.Word.ofNatModulo 1) state).val = 0)
    "constructor arguments leaked into calldata"
  let runtime ← get "runtime compilation" (LinkedContract.compileObject program [deployName, runtimeName] images)
  let _ ← expectBytes "runtime retains constructor storage"
    (Contract.run (runtime.instantiate {storage := state, calldata := bytes [1, 2, 3]}))
    (wordBytes 42 ++ wordBytes 0 ++ wordBytes runtimeBytes.length)
  let initialStorage := [(Core.Word.zero, Core.Word.ofNatModulo 5)]
  let revertedSource := source [action "sstore" [w 0, w 99], action "mstore8" [w 0, w 0xde],
    action "revert" [w 0, w 1], action "sstore" [w 0, w 77]]
  let reverted ← get "reverting constructor" (LinkedContract.prepare revertedSource [deployName] images []
    {storage := initialStorage})
  match Contract.run reverted with
  | .reverted actual => require (actual == bytes [0xde]) "wrong constructor revert payload"
  | other => throw (IO.userError s!"constructor did not revert: {reprStr other}")
  let _ ← expectBytes "reverting constructor does not publish storage"
    (Contract.run (runtime.instantiate reverted.context))
    (wordBytes 5 ++ wordBytes 0 ++ wordBytes runtimeBytes.length)
  match Contract.run constructor 100 with
  | .outOfFuel machine =>
      let resumed ← expectBytes "linked constructor resume" (Contract.resume machine) runtimeBytes
      require ((Core.WordMapping.lookupEntries Core.Word.zero resumed).val = 42)
        "resumed constructor lost storage writes"
  | other => throw (IO.userError s!"constructor should suspend: {reprStr other}")
  let badInit := source [action "pop" [call "datasize" [symbol "UnknownObject"]]]
  rejects "unknown linked symbol" (LinkedContract.prepare badInit [deployName] images)
  let childOnly ← get "unselected object's symbols stay independent"
    (LinkedContract.prepare badInit [deployName, runtimeName] images)
  let _ ← expectBytes "runtime skips unrelated invalid constructor symbols" (Contract.run childOnly)
    (wordBytes 0 ++ wordBytes 0 ++ wordBytes runtimeBytes.length)
  rejects "missing linked image" (LinkedContract.prepare program [deployName] images.tail)
  let badImages := images.map fun image => if image.path == [deployName] then
    {image with bytes := bytes [0xaa, 0xbb, 0, 0, 0, 0]} else image
  rejects "mismatched embedded bytes" (LinkedContract.prepare program [deployName] badImages)
  let shadowed := source [] [
    action "mstore" [w 0, call "datasize" [w 41]], action "return" [w 0, w 32],
    ⟨.functionDef (name "datasize") [name "x"] [name "r"] [
      ⟨.assign [name "r"] (call "add" [⟨.ident (name "x"), none⟩, w 1]), none⟩], none⟩]
  let shadowed ← get "hoisted local datasize shadow"
    (LinkedContract.prepare shadowed [deployName, runtimeName] images)
  let _ ← expectBytes "local symbol intrinsic shadowing" (Contract.run shadowed) (wordBytes 42)
  let selfOffset := source [] [action "mstore" [w 0, call "dataoffset" [symbol runtimeName]],
    action "return" [w 0, w 32]]
  let selfOffset ← get "current image offset"
    (LinkedContract.prepare selfOffset [deployName, runtimeName] images)
  let _ ← expectBytes "current object starts at zero" (Contract.run selfOffset) (wordBytes 0)
  pure ()

end Tests.RustHullLinkedContract
