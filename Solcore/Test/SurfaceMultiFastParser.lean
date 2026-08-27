import Solcore.Surface.Multi.FastParserPhaseAAtom

/-! Executable regressions for the terminal-atom fast-parser base. -/

set_option autoImplicit false

namespace Tests

open Solcore.Workspace
open Solcore.Surface.Multi

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def fastParserSource : IO SourceId := do
  match CanonicalSourcePath.parse "FastParser.solc" with
  | some path => pure { library := .main, path }
  | none => throw (IO.userError "the fast-parser test path is invalid")

/-- Exercise the complete terminal worklist on one retained identifier and
logical EOF. -/
def testMultiFastParser : IO Unit := do
  let source <- fastParserSource
  let file : WorkspaceFile := {
    id := source
    content := "x"
  }
  let token : Token := {
    span := {
      source
      startByte := 0
      endByte := 1
    }
    payload := .identifier "x"
  }
  let tokens := [token]
  have owned : TokensOwnedBy file tokens := by
    intro candidate member
    simp only [tokens, List.mem_singleton] at member
    subst candidate
    simp [token, file, SourceSpan.ValidFor]
    decide

  let optionalExecution := executeFastTerminalPhaseA? file owned
  assertTrue optionalExecution.isSome
    "the canonical terminal Phase-A option executor returned none"

  let execution := executeFastTerminalPhaseA file owned
  let atomSeeds := execution.atomSeeds
  assertTrue
    (execution.trace.actualUnits ==
      1 + (allFastTerminalWorkItems tokens).length)
    "the terminal Phase-A unit count diverged from startup plus its worklist"
  assertTrue (execution.trace.ledger == {
      fixedUnits := 1
      boundarySlotUnits := 0
      memoSlotUnits := (allFastTerminalWorkItems tokens).length
    })
    "the terminal Phase-A component ledger diverged from its address families"
  assertTrue
    (FastParserUnitAddress.addressLedger
      (allFastTerminalAddresses tokens) == execution.trace.ledger)
    "the terminal Phase-A trace ledger diverged from its address ledger"
  assertTrue
    (decide (execution.trace.actualUnits <= parseBound (tokens.length + 1)))
    "the terminal Phase-A execution exceeded parseBound"
  assertTrue (atomSeeds.length == execution.facts.length)
    "terminal atom materialization changed the successful fact count"
  assertTrue
    (decide (allFastTerminalAtomScannedEdges file owned).Nodup)
    "terminal atom materialization repeated a canonical raw scan edge"

  let hasIdentifierAtToken := execution.facts.any fun fact =>
    fact.work.cursor.val == 0 &&
      fact.work.atom.terminal == Grammar.TerminalSymbol.category .identifier
  assertTrue hasIdentifierAtToken
    "the identifier token did not produce an identifier terminal fact"

  let hasIdentifierAtomSeed := atomSeeds.any fun seed =>
    seed.fact.work.cursor.val == 0 &&
      seed.fact.work.atom.terminal ==
        Grammar.TerminalSymbol.category .identifier
  assertTrue hasIdentifierAtomSeed
    "the identifier terminal fact did not materialize an atom seed"

  let hasEofAtEnd := execution.facts.any fun fact =>
    fact.work.cursor.val == 1 &&
      fact.work.atom.terminal == Grammar.TerminalSymbol.endOfFile
  assertTrue hasEofAtEnd
    "logical EOF did not produce an end-of-file terminal fact"

  let hasEofAtomSeed := atomSeeds.any fun seed =>
    seed.fact.work.cursor.val == 1 &&
      seed.fact.work.atom.terminal == Grammar.TerminalSymbol.endOfFile
  assertTrue hasEofAtomSeed
    "the logical EOF terminal fact did not materialize an atom seed"

  let hasEofAtToken := execution.facts.any fun fact =>
    fact.work.cursor.val == 0 &&
      fact.work.atom.terminal == Grammar.TerminalSymbol.endOfFile
  assertTrue (!hasEofAtToken)
    "the retained identifier incorrectly produced an end-of-file fact"

  assertTrue (decide (allFastTerminalAddresses tokens).Nodup)
    "the canonical terminal Phase-A schedule addresses contain a duplicate"

end Tests
