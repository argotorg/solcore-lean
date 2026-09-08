import Solcore.Syntax.Parser.PostfixTailTraceCompletenessProperties
import Solcore.Syntax.Parser.DiagnosticTraceStateProperties
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Exact test children are defined by independent remainder transformations.
They preserve diagnostic prefixes and have no rejection outcomes; their window
contract requires only that the transformation preserve the numeric endIndex. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxPostfixTailProgressSupport

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

def source : SourceId := { origin := .main, path := "postfix-progress.sol" }
def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
def sym (startByte endByte : Nat) (kind : Symbol) : Token := { span := span startByte endByte, value := .symbol kind }
def name (startByte endByte : Nat) : Token := { span := span startByte endByte, value := .identifier "x" }
def fixed : Expr := { span := span 0 1, value := .error }
def remainder (tokens : Array Token) (cursor endIndex : Nat) : Remainder := { tokens, cursor, endIndex }
def state (before : Remainder) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := before.tokens, cursor := before.cursor
  window := { endIndex := before.endIndex, endByte := 6 }, diagnosticsRev := prior.reverse
}

def child (step : Remainder → Remainder) : Parser Expr := fun input =>
  .ok fixed (input.traceResult (step input.declarativeRemainder) [])
def childTrace (step : Remainder → Remainder) (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (value : Expr) (after : Remainder) (trace : List ParseDiagnostic) : Prop :=
  value = fixed ∧ after = step input ∧ trace = []
def neverReject (_source : SourceId) (_endByte : Nat) (_input _after : Remainder)
    (_report : ParseDiagnostic) (_trace : List ParseDiagnostic) : Prop := False

theorem child_success_sound (step : Remainder → Remainder) : ParserTraceSuccessSound (child step) (childTrace step) := by
  intro input output value result
  cases result
  exact ⟨[], ⟨rfl, input.traceResult_declarativeRemainder _ [], rfl⟩, input.traceResult_diagnostics _ []⟩

theorem child_success_complete (step : Remainder → Remainder) : ParserTraceSuccessComplete (child step) (childTrace step) := by
  rintro input value after trace ⟨rfl, rfl, rfl⟩
  exact ⟨_, rfl, input.traceResult_declarativeRemainder _ [], input.traceResult_diagnostics _ []⟩

theorem child_success_context (step : Remainder → Remainder)
    (endIndex : ∀ before, (step before).endIndex = before.endIndex) : ParserSuccessContext (child step) := by
  intro input output value result
  cases result
  exact ⟨rfl, by simp only [State.traceResult, endIndex, State.declarativeRemainder]⟩

theorem child_reject_sound (step : Remainder → Remainder) : ParserTraceRejectSound (child step) neverReject := by
  intro input output failure result
  cases result

theorem child_reject_complete (step : Remainder → Remainder) : ParserTraceRejectComplete (child step) neverReject := by
  intro input after report trace impossible
  exact False.elim impossible

theorem child_ordinary (step : Remainder → Remainder) : Parser.Ordinary (child step) :=
  fun _ => .inl ⟨_, _, rfl⟩

theorem child_exact (step : Remainder → Remainder) (sourceId : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec (childTrace step) neverReject sourceId endByte where
  successResultUnique := by
    rintro input left right afterLeft afterRight leftTrace rightTrace
      ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  rejectResultUnique := by intros; contradiction
  successRejectDisjoint := by intros; contradiction

theorem absent_of_token {input : Remainder} {token : Token} {kind : TokenKind}
    (found : TokenAt input.tokens input.endIndex input.cursor token) (different : token.value ≠ kind) :
    TokenKindAbsentAt input.tokens input.endIndex input.cursor kind := by
  rintro ⟨span, other⟩
  have same := Option.some.inj (found.2.symm.trans other.2)
  exact different (congrArg (fun item : Token => item.value) same)

end Solcore.Test.SyntaxPostfixTailProgressSupport
