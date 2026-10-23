import Solcore.Frontend.RustHull.CodeImage
import Solcore.Core.Machine

set_option autoImplicit false
namespace Tests.RustHullCodeImage
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def success {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def emptyCode : CodeBlock := {stmts := [], functions := []}

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def scalar (value : Nat) : Value := .word (Word.ofNatModulo value)
private def bytes (values : List Nat) : List UInt8 := values.map UInt8.ofNat
private def images : List CodeImage.Image := [
  {path := ["Root"], bytes := bytes [1, 2, 3, 4, 5, 6, 7],
    embeds := [{name := "A", offset := 2, size := 3}, {name := "B", offset := 5, size := 2}]},
  {path := ["Root", "A"], bytes := bytes [3, 4, 5], embeds := [{name := "Leaf", offset := 2, size := 1}]},
  {path := ["Root", "A", "Leaf"], bytes := bytes [5]},
  {path := ["Root", "B"], bytes := bytes [6, 7]}]
private def objects : List Object := [
  .object "Root" emptyCode [
    .object "A" emptyCode [.object "Leaf" emptyCode [] none] none,
    .object "B" emptyCode [] none] none]

private def memory (body : Expr) : Expr :=
  .letE (.newCell WordMapping.type WordMapping.empty)
    (.letE (.newCell .word (word 0)) body)

private def sequence (result : Ty) (action next : Expr) : Expr :=
  LanguageResult.bind result action (next.weakenAt 0)

private def expect (label : String) (type : Ty) (body : Expr) (expected : Value) : IO Unit := do
  let program : Program := {
    resultType := LanguageResult.resultType type
    body
    dataDefinitions := Memory.definitions
  }
  require program.check s!"{label}: ill-typed Core"
  match program.run 3000000 with
  | .done actual => require (actual == .inRight .word expected) s!"{label}: {reprStr actual}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def jsonEnvelope (entries : String) : String :=
  "{\"schema\":\"solcore-rs.code-images.v1\",\"upstreamCommit\":\"" ++ upstreamCommit ++
  "\",\"backend\":{\"name\":\"sonatina\",\"revision\":\"" ++ CodeImage.backendRevision ++
  "\",\"optimization\":\"O0\"},\"images\":" ++ entries ++ "}"

def run : IO Unit := do
  let _ ← success (CodeImage.validate objects images)
  let root ← success (CodeImage.select images ["Root"])
  let a ← success (CodeImage.select images ["Root", "A"])
  require ((← success (CodeImage.resolve root "Root")) == ⟨0, 7⟩) "current section extent"
  require ((← success (CodeImage.resolve root "A")) == ⟨2, 3⟩) "direct embed extent"
  require ((← success (CodeImage.resolve a "Leaf")) == ⟨2, 1⟩) "nested relative extent"
  require (CodeImage.resolve root "Leaf" |> rejected) "nested symbol leaked into parent namespace"
  require (CodeImage.select images ["A"] |> rejected) "suffix path accepted as full path"
  require (CodeImage.validate objects images.tail |> rejected) "missing image accepted"
  require (CodeImage.validate objects (root :: images) |> rejected) "duplicate image accepted"
  require (CodeImage.validate objects ({root with bytes := bytes [1, 2, 9, 4, 5, 6, 7]} :: images.tail) |> rejected)
    "mismatched child bytes accepted"
  let badExtent := {root with embeds := [{name := "A", offset := 6, size := 3},
      {name := "B", offset := 5, size := 2}]}
  require (CodeImage.validate objects (badExtent :: images.tail) |> rejected) "out-of-range embed accepted"
  let overlappingObjects := [.object "Root" emptyCode [.object "A" emptyCode [] none, .object "B" emptyCode [] none] none]
  let overlapping : List CodeImage.Image := [
    {path := ["Root"], bytes := bytes [1, 2, 3],
      embeds := [{name := "A", offset := 0, size := 2}, {name := "B", offset := 1, size := 2}]},
    {path := ["Root", "A"], bytes := bytes [1, 2]},
    {path := ["Root", "B"], bytes := bytes [2, 3]}]
  require (CodeImage.validate overlappingObjects overlapping |> rejected) "overlapping child images accepted"
  let execution ← success (CodeImage.executionBytes root (bytes [0xaa, 0xbb]))
  require ((← success (CodeImage.resolve root "Root")).size = 7) "constructor arguments changed datasize"
  expect "codesize includes constructor input" .word (CodeImage.codeSize execution) (scalar 9)
  expect "copy constructor suffix" .word
    (memory (sequence .word (CodeImage.copy execution (.var 1) (.var 0) (word 0) (word 7) (word 2))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar (0xaabb * 256 ^ 30))
  expect "copy embedded runtime" .word
    (memory (sequence .word (CodeImage.copy execution (.var 1) (.var 0) (word 0) (word 2) (word 3))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar (0x030405 * 256 ^ 29))
  expect "codecopy zero pads" .word
    (memory (sequence .word (CodeImage.copy execution (.var 1) (.var 0) (word 0) (word 8) (word 4))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar (0xbb * 256 ^ 31))
  expect "codecopy source does not wrap" .word
    (memory (sequence .word (CodeImage.copy execution (.var 1) (.var 0)
      (word 0) (word (wordModulus - 1)) (word 2))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar 0)
  let json := jsonEnvelope "[{\"path\":[\"Root\"],\"bytes\":\"0x0102ff\",\"embeds\":[]}]"
  let decoded ← success (CodeImage.decode json)
  require (decoded == [{path := ["Root"], bytes := bytes [1, 2, 255]}]) "code image decode"
  for malformed in [json.replace "0x0102ff" "0x1", json.replace "0x0102ff" "0xFF",
      json.replace "O0" "O2", json.replace CodeImage.backendRevision "wrong",
      json.replace "\"embeds\":[]" "\"embeds\":[],\"extra\":0"] do
    require (CodeImage.decode malformed |> rejected) "malformed artifact accepted"
  for malformed in [String.ofList (List.replicate 17 '['),
      json.replace "\"embeds\":[]" "\"embeds\":1e999999999",
      json.replace "\"embeds\":[]" "\"embeds\":12345678901"] do
    require (CodeImage.decode malformed |> rejected) "parser resource guard ignored"
  require (CodeImage.decode json 10 |> rejected) "artifact input byte limit ignored"

end Tests.RustHullCodeImage
