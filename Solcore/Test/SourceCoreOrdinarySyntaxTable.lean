import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySyntaxTable
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission
import Solcore.Test.SourceCoreCanonicalFormationFixture
import Solcore.Test.SourceCoreConstructorCallsSource
import Solcore.Test.SourceCoreMethodOriginEvidenceFixture
set_option autoImplicit false
open Solcore Frontend SourceInference SourceSemantics CoreLowering

namespace Tests.SourceCoreOrdinarySyntaxTable

def run : IO Unit := do
  let fixture ← Tests.SourceCoreCanonicalFormation.compiledFixture
  let observed ← Tests.SourceCoreCanonicalFormation.observeProgram fixture
  let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect fixture.recipe.compiled fixture.source_wellFormed 100
  unless table.rows.length == 3 && table.rows.any (· == observed.identityRow.row) do
    throw (IO.userError "actual ordinary cache table mismatch")
  match fixture.recipe.compiled.indexed.base.functions[observed.relayRow.index]? with
  | none => throw (IO.userError "relay cache missing")
  | some named =>
    match CallableIndexedOwnedPreparedNamedScopedAdmission.admitSource fixture.recipe.compiled named named.specialized.function.typedBody
        [observed.relayShape.statement.id] .word table.rows 100 with
    | none => throw (IO.userError "actual nonempty direct table source rejected")
    | some _ => IO.println "SYNTAX_TABLE_DIRECT_PASS: actual 3-row table admitted the original relay direct call"
  let nominal ← Tests.SourceCoreConstructorCalls.checkedFixture
  unless (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 100 (.nominal nominal.dataType.id [])).isSome do
    throw (IO.userError "actual nominal formation rejected")
  unless (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 100 (.nominal nominal.dataType.id [.word])).isNone do
    throw (IO.userError "wrong nominal arity accepted")
  unless (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 100 (.nominal nominal.makeSignature.id [])).isNone do
    throw (IO.userError "function declaration accepted as nominal")
  unless (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 100 (.variable ⟨0⟩)).isNone &&
      (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 100 (.parameter ⟨nominal.makeSignature.id, 0⟩)).isNone &&
      (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 0 .word).isNone do
    throw (IO.userError "open or exhausted type accepted")
  unless (CallableIndexedOwnedPreparedOrdinarySyntaxTable.type? nominal.program.signatures 100
      (.function (.product .word .bool) (.mapping .word (.proxy .bool)))).isSome do
    throw (IO.userError "closed compound type rejected")
  let parameter : TypeSystem.TypeParameterId := ⟨nominal.makeSignature.id, 0⟩
  unless (CallableIndexedOwnedPreparedOrdinarySyntaxTable.range? nominal.program.signatures 100
      [(parameter, .word), (parameter, .nominal nominal.makeSignature.id [])]).isNone do
    throw (IO.userError "invalid later replacement in a duplicate row was ignored")
  IO.println "SYNTAX_TABLE_TYPES_PASS: nominal/compound accepted; wrong arity/nondata/open/fuel/full-range rejected"
  let late ← Tests.SourceCoreMethodOriginEvidence.compiledFixture
  let observedLate ← Tests.SourceCoreMethodOriginEvidence.observeProgram late
  let lateTable := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect late.recipe.compiled late.source_wellFormed 100
  unless lateTable.rows.any (· == observedLate.identityWordRow.row) &&
      lateTable.rows.any (· == observedLate.identityBoolRow.row) do
    throw (IO.userError "late identity rows missing from executable table")
  IO.println s!"SYNTAX_TABLE_LATE_PASS: {lateTable.rows.length} ordinary rows include both method-discovered identities"

end Tests.SourceCoreOrdinarySyntaxTable
