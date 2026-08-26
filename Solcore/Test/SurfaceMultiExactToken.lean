import Solcore.Surface.Multi.ExactTokenCorrespondence

/-! Executable regressions for exact Multi retained-token correspondence. -/

set_option autoImplicit false

namespace Tests

open Solcore.Workspace
open Solcore.Surface.Multi

private structure FrontendFixture where
  name : String
  source : String
  expectedItems : Nat

/-- Representative source programs exercised by the exact-token frontend
regression. -/
private def frontendFixtures : List FrontendFixture := [
  ⟨"empty", "", 0⟩,
  ⟨"tiny", "data A;", 1⟩,
  ⟨"import-path", "import lib.core;", 1⟩,
  ⟨"return-literal", "function f() { return 0; }", 1⟩,
  ⟨"spaced-call-terminal", "function f() { x (y) }", 1⟩,
  ⟨"data-constructors", "data Bool = False | True;", 1⟩,
  ⟨"contract-field", "contract C { value: word; }", 1⟩]

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def exactTokenTestSource : IO SourceId := do
  match CanonicalSourcePath.parse "ExactToken.solc" with
  | some path => pure { library := .main, path }
  | none => throw (IO.userError "the exact-token test path is invalid")

private def testSpan
    (source : SourceId) (startByte endByte : Nat) : SourceSpan := {
  source
  startByte
  endByte
}

private def locatedWith {α : Type}
    (span : SourceSpan) (payload : α) : Located α := {
  span
  payload
}

private def expectIdentifier (text : String) : IO Identifier := do
  match Identifier.parse text with
  | some identifier => pure identifier
  | none => throw (IO.userError s!"invalid exact-token test identifier: {text}")

private def testFrontendFixture
    (sourceId : SourceId) (fixture : FrontendFixture) : IO Unit := do
  let file : WorkspaceFile := { id := sourceId, content := fixture.source }
  match lexModule file with
  | .error diagnostic =>
      throw (IO.userError
        s!"exact-token fixture {fixture.name} failed lexing: {reprStr diagnostic}")
  | .ok lexed =>
      match executeObservedContextualFrontend file with
      | .error diagnostic =>
          throw (IO.userError
            s!"exact-token fixture {fixture.name} failed parsing: {reprStr diagnostic}")
      | .ok parsed =>
          assertTrue (parsed.payload.items.length == fixture.expectedItems)
            s!"exact-token fixture {fixture.name} changed its item count"
          assertTrue
            (exactTokenCorrespondence file lexed.tokens lexed.comments parsed)
            s!"exact-token fixture {fixture.name} failed correspondence"

/-- Exercise visitor-only source-impossible shapes without invoking parsing. -/
private def testVisitorRejects (source : SourceId) : IO Unit := do
  let identifier ← expectIdentifier "value"
  let nameSpan := testSpan source 0 5
  let expressionSpan := testSpan source 0 5
  let statementSpan := testSpan source 0 6
  let terminatorSpan := testSpan source 5 6
  let markerSpan := testSpan source 0 1
  let name : IdentifierOccurrence := locatedWith nameSpan identifier
  let expression : Expression :=
    locatedWith expressionSpan (.name name)
  let singletonTuple : Expression :=
    locatedWith expressionSpan (.tuple [expression])
  assertTrue (expressionTokenPlan? singletonTuple).isNone
    "the expression visitor accepted a singleton tuple"

  let wrongMarker : Marker :=
    locatedWith markerSpan .publicModifier
  let wildcard : Pattern :=
    locatedWith expressionSpan (.wildcard wrongMarker)
  assertTrue (patternTokenPlan? wildcard).isNone
    "the pattern visitor accepted a wildcard with the wrong marker role"

  let unterminated : Statement :=
    locatedWith expressionSpan (.expression expression none)
  let terminated : Statement :=
    locatedWith statementSpan
      (.expression expression (some terminatorSpan))
  assertTrue (statementTokenPlans? [unterminated, terminated]).isNone
    "a non-final expression statement omitted its semicolon"

/-- Lex, parse, and check exact correspondence for every M2c benchmark source,
then exercise representative visitor rejection paths. -/
def testMultiExactTokenCorrespondence : IO Unit := do
  let source ← exactTokenTestSource
  for fixture in frontendFixtures do
    testFrontendFixture source fixture
  testVisitorRejects source

end Tests
