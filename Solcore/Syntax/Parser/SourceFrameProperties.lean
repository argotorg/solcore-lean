import Solcore.Syntax.Parser.QualifiedNameRejectionTraceStateProperties

/-! Source-file preservation for all ordinary replies, independently of input
validity, diagnostic events, and token/window preservation. Invariants carry
no state and therefore impose no source obligation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace Reply

def PreservesFile {α : Type} (reply : Reply α) (input : State) : Prop :=
  match reply with
  | .ok _ next | .reject _ next => next.file = input.file
  | .invariant _ => True

theorem PreservesFile.trans {α : Type} {reply : Reply α} {middle input : State}
    (preserved : reply.PreservesFile middle) (fileEq : middle.file = input.file) :
    reply.PreservesFile input := by
  cases reply with
  | ok value next => exact Eq.trans preserved fileEq
  | reject failure next => exact Eq.trans preserved fileEq
  | invariant error => trivial

end Reply

namespace Parser

def PreservesFile {α : Type} (parser : Parser α) : Prop :=
  ∀ input, (parser input).PreservesFile input

theorem PreservesFile.file_eq_of_ok {α : Type} {parser : Parser α}
    (preserved : PreservesFile parser) {input output : State} {value : α}
    (result : parser input = .ok value output) : output.file = input.file := by
  have frame := preserved input
  rwa [result] at frame

theorem PreservesFile.file_eq_of_reject {α : Type} {parser : Parser α}
    (preserved : PreservesFile parser) {input rejected : State} {failure : Failure}
    (result : parser input = .reject failure rejected) : rejected.file = input.file := by
  have frame := preserved input
  rwa [result] at frame

theorem pure_preservesFile {α : Type} (value : α) : PreservesFile (pure value : Parser α) :=
  fun _ => rfl

theorem bind_preservesFile {α β : Type} {first : Parser α} {next : α → Parser β}
    (firstFile : PreservesFile first) (nextFile : ∀ value, PreservesFile (next value)) :
    PreservesFile (first >>= next) := by
  intro input
  change (match first input with
    | .ok value middle => next value middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error).PreservesFile input
  cases firstResult : first input with
  | ok value middle =>
      exact (nextFile value middle).trans (firstFile.file_eq_of_ok firstResult)
  | reject failure rejected => exact firstFile.file_eq_of_reject firstResult
  | invariant error => trivial

end Parser

theorem getState_preservesFile : Parser.PreservesFile getState := fun _ => rfl

theorem modifyState_preservesFile (update : State → State)
    (fileEq : ∀ input, (update input).file = input.file) :
    Parser.PreservesFile (modifyState update) := fileEq

theorem emitDiagnostic_preservesFile (diagnostic : ParseDiagnostic) :
    Parser.PreservesFile (emitDiagnostic diagnostic) := fun _ => rfl

theorem rejectAt_preservesFile {α : Type} (input : State)
    (expected : NonemptyList ParseExpectation) (context : ParseContext) :
    (rejectAt (α := α) input expected context).PreservesFile input := rfl

theorem acceptToken_preservesFile (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) : Parser.PreservesFile (acceptToken expected context accepts) := by
  intro input
  unfold acceptToken
  cases input.peek? with
  | none => rfl
  | some token => simp only; split <;> rfl

theorem keyword_preservesFile (value : HardKeyword) (context : ParseContext) :
    Parser.PreservesFile (keyword value context) :=
  acceptToken_preservesFile (.keyword value) context (· == .keyword value)

theorem symbol_preservesFile (value : Symbol) (context : ParseContext) :
    Parser.PreservesFile (symbol value context) :=
  acceptToken_preservesFile (.symbol value) context (· == .symbol value)

theorem contextual_preservesFile (value : ContextualKeyword) (context : ParseContext) :
    Parser.PreservesFile (contextual value context) :=
  acceptToken_preservesFile (.contextual value) context (·.isContextual value)

theorem rawIdentifier_preservesFile (context : ParseContext) :
    Parser.PreservesFile (rawIdentifier context) := by
  intro input
  unfold rawIdentifier
  cases input.peek? with
  | none => rfl
  | some token => cases token with
    | mk span kind => cases kind <;> rfl

theorem identifier_preservesFile (context : ParseContext) :
    Parser.PreservesFile (identifier context) := by
  intro input
  cases result : identifier context input with
  | ok name output => exact (identifier_success_context_eq context result).1
  | reject failure rejected => rw [identifier_reject_state_eq context result]; rfl
  | invariant error => trivial

theorem qualifiedName_preservesFile (context : ParseContext) (phase : ParserPhase) :
    Parser.PreservesFile (qualifiedName context phase) := by
  intro input
  cases result : qualifiedName context phase input with
  | ok name output => exact (qualifiedName_success_context context phase result).1
  | reject failure rejected => exact (qualifiedName_reject_context context phase result).1
  | invariant error => trivial

end Solcore.Syntax.Parser
