import Solcore.SourceSemantics.CoreLowering.CallableAncestryCache

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.CallableAncestryCache.Prepared.mk

/-! The universal theorem consumes a completed finite closure certificate.
The concrete table test below tests only table lookup, not table ownership or
successful preparation of every compiler artifact. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryCache
open Solcore Solcore.Frontend SourceInference
open Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
open Solcore.SourceSemantics.CoreLowering.CallableAncestryCache

example {checked : Checked} {base : Base checked} {owned : Owned base}
    (prepared : Prepared owned) {frame : ContextFrame}
    {state : Option Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State} :
    prepared.table.lookup? frame = some (state.map nativeState) ↔ Authenticates owned frame state :=
  prepared.lookup_iff

example {checked : Checked} {base : Base checked} {owned : Owned base}
    (prepared : Prepared owned) {leftFrame rightFrame : ContextFrame}
    {left right : SourceCoreCallableAncestryCache.State}
    (leftFound : prepared.table.lookup? leftFrame = some (some left))
    (rightFound : prepared.table.lookup? rightFrame = some (some right))
    (same : left.key = right.key) : left = right :=
  prepared.lookup_key_injective leftFound rightFound same

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"ancestry_cache", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def state (requirement : Nat) : SourceCoreCallableAncestryCache.State := {
  owner := ⟨owner, []⟩, active := [], source := {
    owner, inputs := [], roots := [], nodes := [.expression {
      id := ⟨⟨owner, 0⟩⟩,
      span := { source := {origin := .main, path := "ancestry_cache.solc"}, startByte := 0, endByte := 1 },
      type := .word, requirements := [⟨requirement⟩], form := .literal (.decimal "1")
    }]
  }
}
private def table : SourceCoreCallableAncestryCache.Table := {
  states := [state 0, state 2, state 4]
  named := [⟨word 7, 0⟩]
  lambdas := [⟨0, word 9⟩, ⟨1, word 9⟩, ⟨2, word 9⟩]
  views := [⟨0, word 1, word 9, 1⟩, ⟨0, word 2, word 9, 2⟩]
}
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let left : ContextFrame := .view (word 1) (word 9) (.named (word 7))
  let right : ContextFrame := .view (word 2) (word 9) (.named (word 7))
  let repeated := (List.range 2000).foldl (fun (frame : ContextFrame) _ => .lambda (word 9) frame) right
  assertTrue (decide (table.lookup? .empty = some none)) "empty ancestry was rejected"
  assertTrue (decide (table.lookup? left = some (some (state 2)))) "left occurrence profile lost"
  assertTrue (decide (table.lookup? repeated = some (some (state 4)))) "repeated ancestry changed its cached state"
  assertTrue (decide ((state 2).key ≠ (state 4).key)) "key ignored occurrence-specific requirement IDs"
  let rejected : List ContextFrame := [.lambda (word 9) .empty,
      .named (word 999), .lambda (word 99) right, .view (word 1) (word 99) (.named (word 7)),
      .view (word 1) (word 9) right]
  for frame in rejected do
    assertTrue ((table.lookup? frame).isNone) "unprepared transition accepted"
  let malformed := {table with named := [⟨word 7, 999⟩]}
  assertTrue ((malformed.lookup? (.named (word 7))).isNone) "missing state row accepted"
  IO.println "finite ancestry table: 2000 repeated frames, exact occurrence profiles, invalid transitions rejected GREEN"
end Tests.SourceCoreCallableAncestryCache
