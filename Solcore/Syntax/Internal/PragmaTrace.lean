import Solcore.Syntax.Internal.NameTrace
import Solcore.Syntax.Grammar.Modules
import Solcore.Syntax.Internal.ImportOutcomes
import Solcore.Syntax.Grammar.SourceFile
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Internal.BlockTrace
import Solcore.Syntax.Internal.StatementOutcomes

/-!
Exact diagnostic traces of pragmas: trace grammars, unique outcomes and protection of
earlier events.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaTraceGrammar
/-! Independent ordered identifier events and complete pragma success traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Concatenate the checked-name events once per identifier in written order. -/
inductive IdentifierListDiagnosticTrace :
    List Syntax.Identifier → List ParseDiagnostic → Prop where
  | nil : IdentifierListDiagnosticTrace [] []
  | cons {name : Syntax.Identifier} {names : List Syntax.Identifier}
      {headTrace tailTrace : List ParseDiagnostic}
      (head : IdentifierDiagnosticTrace name headTrace)
      (tail : IdentifierListDiagnosticTrace names tailTrace) :
      IdentifierListDiagnosticTrace (name :: names) (headTrace ++ tailTrace)

/-- A pragma tail retains only events of newly parsed suffix identifiers. -/
def PragmaItemsTailTraceParses (input : Remainder) (items : List Syntax.Identifier)
    (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  PragmaItemsTailOrdinaryParses input items output ∧
    IdentifierListDiagnosticTrace items trace

/-- Complete item scanning retains its exact grammar and ordered name events. -/
def PragmaItemsTraceParses (input : Remainder) (items : List Syntax.Identifier)
    (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  PragmaItemsOrdinaryParses input items output ∧
    IdentifierListDiagnosticTrace items trace

/-- Only checked items emit diagnostics: the raw pragma name, keyword,
commas, and final semicolon contribute no events. -/
def PragmaDeclTraceParses (input : Remainder) (declaration : Syntax.PragmaDecl)
    (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  PragmaDeclOrdinaryParses input declaration output ∧
    IdentifierListDiagnosticTrace declaration.value.items trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaTraceProperties
/-! Exact event order and functional successful pragma traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every written identifier list determines a complete event sequence. -/
theorem identifierListDiagnosticTrace_total (names : List Syntax.Identifier) :
    ∃ trace, IdentifierListDiagnosticTrace names trace := by
  induction names with
  | nil => exact ⟨[], .nil⟩
  | cons name names ih =>
      rcases identifierDiagnosticTrace_total name with ⟨head, headTrace⟩
      rcases ih with ⟨tail, tailTrace⟩
      exact ⟨head ++ tail, .cons headTrace tailTrace⟩

/-- Ordered per-name emission fixes the complete trace including duplicates. -/
theorem IdentifierListDiagnosticTrace.trace_unique
    {names : List Syntax.Identifier} {left right : List ParseDiagnostic}
    (leftTrace : IdentifierListDiagnosticTrace names left)
    (rightTrace : IdentifierListDiagnosticTrace names right) : left = right := by
  induction leftTrace generalizing right with
  | nil => cases rightTrace; rfl
  | cons leftHead leftTail ih =>
      cases rightTrace with
      | cons rightHead rightTail =>
          rw [leftHead.trace_unique rightHead, ih rightTail]

/-- Joining two written name sequences appends their event sequences. -/
theorem IdentifierListDiagnosticTrace.append
    {leftNames rightNames : List Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : IdentifierListDiagnosticTrace leftNames leftTrace)
    (right : IdentifierListDiagnosticTrace rightNames rightTrace) :
    IdentifierListDiagnosticTrace (leftNames ++ rightNames) (leftTrace ++ rightTrace) := by
  induction left with
  | nil => exact right
  | cons head tail ih =>
      simpa only [List.cons_append, List.append_assoc] using
        IdentifierListDiagnosticTrace.cons head ih

/-- The exact tail grammar fixes its full suffix, endpoint, and added trace. -/
theorem PragmaItemsTailTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : List Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : PragmaItemsTailTraceParses input left afterLeft leftTrace)
    (rightParsed : PragmaItemsTailTraceParses input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  rcases pragmaItemsTailExactOutcomeSpec.successResultUnique leftParsed.1
    rightParsed.1 with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, leftParsed.2.trace_unique rightParsed.2⟩

/-- The complete item grammar fixes all names and their diagnostic order. -/
theorem PragmaItemsTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : List Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : PragmaItemsTraceParses input left afterLeft leftTrace)
    (rightParsed : PragmaItemsTraceParses input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  rcases pragmaItemsExactOutcomeSpec.successResultUnique leftParsed.1
    rightParsed.1 with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, leftParsed.2.trace_unique rightParsed.2⟩

/-- A pragma's exact AST fixes only its checked-item diagnostic sequence. -/
theorem PragmaDeclTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.PragmaDecl}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : PragmaDeclTraceParses input left afterLeft leftTrace)
    (rightParsed : PragmaDeclTraceParses input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  rcases pragmaDeclExactOutcomeSpec.successResultUnique leftParsed.1
    rightParsed.1 with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, leftParsed.2.trace_unique rightParsed.2⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaSequenceTraceGrammar
/-! Independent exact syntax and raw diagnostic traces for complete windows
containing only successful pragmas. No executor state, reply, or fuel occurs. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The source-order top-level node belonging to one exact pragma declaration. -/
def pragmaSequenceItem (declaration : Syntax.PragmaDecl) : Syntax.TopItem := {
  span := declaration.span, leadingComments := [], value := .pragmaDecl declaration
}

/-- Lift written declarations without changing their order or multiplicity. -/
def pragmaSequenceItems (declarations : List Syntax.PragmaDecl) : List Syntax.TopItem :=
  declarations.map pragmaSequenceItem

/-- Exact pragma-only scan through the active window end. Each declaration
contributes its checked-item events, followed by the suffix's events. -/
inductive PragmaSequenceTraceParses :
    Remainder → List Syntax.PragmaDecl → Remainder → List ParseDiagnostic → Prop where
  | done {input : Remainder} (atEnd : input.endIndex ≤ input.cursor) :
      PragmaSequenceTraceParses input [] input []
  | cons {input afterHead output : Remainder}
      {head : Syntax.PragmaDecl} {tail : List Syntax.PragmaDecl}
      {headTrace tailTrace : List ParseDiagnostic}
      (headParsed : PragmaDeclTraceParses input head afterHead headTrace)
      (tailParsed : PragmaSequenceTraceParses afterHead tail output tailTrace) :
      PragmaSequenceTraceParses input (head :: tail) output (headTrace ++ tailTrace)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaSequenceTraceProperties
/-! Carrier, progress, exactness, and ordinary-file erasure for independent
pragma-only sequences. Traces and written declaration order are retained. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem pragmaTail_shape {input output : Remainder}
    {items : List Syntax.Identifier}
    (parsed : PragmaItemsTailOrdinaryParses input items output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.cursor ≤ output.cursor := by
  induction parsed with
  | done => exact ⟨rfl, rfl, Nat.le_refl _⟩
  | trailing _ _ comma _ =>
      rw [comma.2]
      exact ⟨rfl, rfl, by simp⟩
  | next _ _ comma _ item _ ih =>
      rcases comma with ⟨_, rfl⟩
      exact ⟨ih.1.trans item.2.1, ih.2.1.trans item.2.2.1,
        by have advance := item.2.2.2; have monotone := ih.2.2; simp only at advance; omega⟩

private theorem pragmaItems_shape {input output : Remainder}
    {items : List Syntax.Identifier}
    (parsed : PragmaItemsOrdinaryParses input items output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.cursor ≤ output.cursor := by
  cases parsed with
  | empty => exact ⟨rfl, rfl, Nat.le_refl _⟩
  | nonempty _ first tail =>
      have tailShape := pragmaTail_shape tail
      exact ⟨tailShape.1.trans first.2.1, tailShape.2.1.trans first.2.2.1,
        by have advance := first.2.2.2; have monotone := tailShape.2.2; omega⟩

/-- The marker starts inside the active window, independently of diagnostics. -/
theorem PragmaDeclOrdinaryParses.startsInside
    {input output : Remainder} {declaration : Syntax.PragmaDecl}
    (parsed : PragmaDeclOrdinaryParses input declaration output) :
    input.cursor < input.endIndex := by
  cases parsed with
  | parsed _ _ marker _ _ _ => exact marker.1.1

/-- Successful pragma grammar preserves its carrier and active end, makes
strict progress, and never consumes beyond the active window. -/
theorem PragmaDeclOrdinaryParses.carrier_progress
    {input output : Remainder} {declaration : Syntax.PragmaDecl}
    (parsed : PragmaDeclOrdinaryParses input declaration output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.cursor < output.cursor ∧ output.cursor ≤ input.endIndex := by
  cases parsed with
  | parsed _ _ marker name items semicolon =>
      rcases marker with ⟨_, rfl⟩
      have itemsShape := pragmaItems_shape items
      rcases semicolon with ⟨inside, rfl⟩
      have tokensEq := itemsShape.1.trans name.2.1
      have endEq := itemsShape.2.1.trans name.2.2.1
      have advance := name.2.2.2
      have monotone := itemsShape.2.2
      simp only at tokensEq endEq advance ⊢
      exact ⟨tokensEq, endEq, by omega, by have bound := inside.1; omega⟩

/-- A fixed pragma token selects its plain top-item branch and excludes hash,
import, and export priority guards without executable lookahead premises. -/
theorem PragmaDeclOrdinaryParses.toTopItem
    {input output : Remainder} {declaration : Syntax.PragmaDecl}
    (parsed : PragmaDeclOrdinaryParses input declaration output) :
    TopItemOrdinaryParses input (pragmaSequenceItem declaration) output := by
  have marker : ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .keyword .pragmaKw } := by
    cases parsed with
    | parsed span _ present _ _ _ => exact ⟨span, present.1⟩
  rcases marker with ⟨span, present⟩
  have absent (kind : TokenKind) (different : kind ≠ .keyword .pragmaKw) :
      TokenKindAbsentAt input.tokens input.endIndex input.cursor kind := by
    rintro ⟨otherSpan, other⟩
    exact different (congrArg (fun token : Token => token.value) (other.token_unique present))
  exact .plain (absent (.symbol .hash) (by decide))
    (.pragmaDecl (.pragmaDecl (absent (.keyword .importKw) (by decide))
      (absent (.keyword .exportKw) (by decide)) ⟨span, present⟩) parsed)

/-- The complete independent scan retains its carrier/end and finishes at or
past that same window end; an empty input may already be past it. -/
theorem PragmaSequenceTraceParses.carrier_atEnd
    {input output : Remainder} {declarations : List Syntax.PragmaDecl}
    {trace : List ParseDiagnostic}
    (parsed : PragmaSequenceTraceParses input declarations output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.endIndex ≤ output.cursor := by
  induction parsed with
  | done atEnd => exact ⟨rfl, rfl, atEnd⟩
  | cons head _ ih =>
      have headShape := head.1.carrier_progress
      exact ⟨ih.1.trans headShape.1, ih.2.1.trans headShape.2.1,
        by simpa only [headShape.2.1] using ih.2.2⟩

/-- Declaration count is bounded by remaining tokens, without a token-array
validity assumption. This can later justify an executor's chosen fuel. -/
theorem PragmaSequenceTraceParses.length_le_remaining
    {input output : Remainder} {declarations : List Syntax.PragmaDecl}
    {trace : List ParseDiagnostic}
    (parsed : PragmaSequenceTraceParses input declarations output trace) :
    declarations.length ≤ input.endIndex - input.cursor := by
  induction parsed with
  | done => simp
  | cons head _ ih =>
      have shape := head.1.carrier_progress
      simp only [List.length_cons]
      omega

/-- Erasing trace information yields the existing ordinary file-item grammar
with the same written-order pragma AST list and exact endpoint. -/
theorem PragmaSequenceTraceParses.toFileItems
    {input output : Remainder} {declarations : List Syntax.PragmaDecl}
    {trace : List ParseDiagnostic}
    (parsed : PragmaSequenceTraceParses input declarations output trace) :
    FileItemsOrdinaryParses input (pragmaSequenceItems declarations) output := by
  induction parsed with
  | done atEnd => exact .done atEnd
  | cons head _ ih =>
      exact .direct head.1.startsInside head.1.toTopItem head.1.carrier_progress.2.2.1 ih

/-- The independent scan fixes the entire declaration list, remainder, and
diagnostic trace, preserving duplicates as well as source order. -/
theorem PragmaSequenceTraceParses.result_unique
    {input leftOutput rightOutput : Remainder}
    {left right : List Syntax.PragmaDecl} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : PragmaSequenceTraceParses input left leftOutput leftTrace)
    (rightParsed : PragmaSequenceTraceParses input right rightOutput rightTrace) :
    left = right ∧ leftOutput = rightOutput ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right rightOutput rightTrace with
  | done atEnd =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl, rfl⟩
      | cons head _ => have inside := head.1.startsInside; omega
  | cons leftHead leftTail ih =>
      cases rightParsed with
      | done atEnd => have inside := leftHead.1.startsInside; omega
      | cons rightHead rightTail =>
          rcases leftHead.result_unique rightHead with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaItemsRejectionTraceGrammar
/-! Independent successful prefixes, uncommitted reports, and rejection events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The newly consumed checked names before the first rejecting tail item.
A comma followed by a semicolon is deliberately excluded from rejection. -/
inductive PragmaItemsTailRejectedPrefix :
    Remainder → List Syntax.Identifier → Remainder → Prop where
  | identifierRejected {input afterComma rejected : Remainder}
      (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (semicolonAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol .semicolon))
      (itemRejected : IdentifierRejects afterComma rejected) :
      PragmaItemsTailRejectedPrefix input [] rejected
  | laterRejected {input afterComma afterItem rejected : Remainder}
      {item : Syntax.Identifier} {consumed : List Syntax.Identifier}
      (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (semicolonAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol .semicolon))
      (itemParsed : IdentifierParses afterComma item afterItem)
      (tailRejected : PragmaItemsTailRejectedPrefix afterItem consumed rejected) :
      PragmaItemsTailRejectedPrefix input (item :: consumed) rejected

/-- Complete item scanning retains its first item when a later suffix fails. -/
inductive PragmaItemsRejectedPrefix :
    Remainder → List Syntax.Identifier → Remainder → Prop where
  | firstIdentifierRejected {input rejected : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .semicolon))
      (firstRejected : IdentifierRejects input rejected) :
      PragmaItemsRejectedPrefix input [] rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.Identifier} {consumed : List Syntax.Identifier}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .semicolon))
      (firstParsed : IdentifierParses input first afterFirst)
      (tailRejected : PragmaItemsTailRejectedPrefix afterFirst consumed rejected) :
      PragmaItemsRejectedPrefix input (first :: consumed) rejected

/-- Tail rejection exposes its exact endpoint and uncommitted identifier
report. Only new prefix names contribute diagnostic events; existing names
held by an enclosing accumulator are outside this relation. -/
def PragmaItemsTailTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (diagnostic : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop :=
  ∃ consumed, PragmaItemsTailRejectedPrefix input consumed rejected ∧
    IdentifierListDiagnosticTrace consumed trace ∧
    RejectAtReports source endByte { head := .identifier, tail := [] }
      .pragmaDecl rejected diagnostic

/-- Rejected replies do not return a prefix AST, so the independently fixed
successful prefix is hidden while the endpoint, report, and events remain exact. -/
def PragmaItemsTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (diagnostic : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop :=
  ∃ consumed, PragmaItemsRejectedPrefix input consumed rejected ∧
    IdentifierListDiagnosticTrace consumed trace ∧
    RejectAtReports source endByte { head := .identifier, tail := [] }
      .pragmaDecl rejected diagnostic

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaItemsRejectionTraceProperties
/-! Prefix erasure and exact functionality for rejected pragma item traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Prefix refinement preserves the established rejecting tail grammar. -/
theorem PragmaItemsTailRejectedPrefix.ordinary
    {input rejected : Remainder} {consumed : List Syntax.Identifier}
    (parsed : PragmaItemsTailRejectedPrefix input consumed rejected) :
    PragmaItemsTailRejects input rejected := by
  induction parsed with
  | identifierRejected span comma absent rejected =>
      exact .identifierRejected span ⟨span, comma.1⟩ comma absent rejected
  | laterRejected span comma absent item tail ih =>
      exact .laterRejected span ⟨span, comma.1⟩ comma absent item ih

/-- Every established tail rejection has its independently retained prefix. -/
theorem PragmaItemsTailRejects.exists_prefix
    {input rejected : Remainder} (rejection : PragmaItemsTailRejects input rejected) :
    ∃ consumed, PragmaItemsTailRejectedPrefix input consumed rejected := by
  induction rejection with
  | identifierRejected span _ comma absent rejected =>
      exact ⟨[], .identifierRejected span comma absent rejected⟩
  | laterRejected span _ comma absent item tail ih =>
      rcases ih with ⟨consumed, rejected⟩
      exact ⟨_, .laterRejected span comma absent item rejected⟩

/-- Complete prefix refinement erases to the established item rejection. -/
theorem PragmaItemsRejectedPrefix.ordinary
    {input rejected : Remainder} {consumed : List Syntax.Identifier}
    (parsed : PragmaItemsRejectedPrefix input consumed rejected) :
    PragmaItemsRejects input rejected := by
  cases parsed with
  | firstIdentifierRejected absent rejected => exact .firstIdentifierRejected absent rejected
  | tailRejected absent first tail => exact .tailRejected absent first tail.ordinary

/-- Every established item rejection has a successful-prefix refinement. -/
theorem PragmaItemsRejects.exists_prefix
    {input rejected : Remainder} (rejection : PragmaItemsRejects input rejected) :
    ∃ consumed, PragmaItemsRejectedPrefix input consumed rejected := by
  cases rejection with
  | firstIdentifierRejected absent rejected =>
      exact ⟨[], .firstIdentifierRejected absent rejected⟩
  | tailRejected absent first tail =>
      rcases tail.exists_prefix with ⟨consumed, rejected⟩
      exact ⟨_, .tailRejected absent first rejected⟩

/-- The rejected tail determines every prior name and the final remainder. -/
theorem PragmaItemsTailRejectedPrefix.result_unique
    {input afterLeft afterRight : Remainder} {left right : List Syntax.Identifier}
    (leftParsed : PragmaItemsTailRejectedPrefix input left afterLeft)
    (rightParsed : PragmaItemsTailRejectedPrefix input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  have endpoint := pragmaItemsTailExactOutcomeSpec.rejectOutputUnique
    leftParsed.ordinary rightParsed.ordinary
  refine ⟨?_, endpoint⟩
  induction leftParsed generalizing right afterRight with
  | identifierRejected span comma absent rejected =>
      cases rightParsed with
      | identifierRejected => rfl
      | laterRejected rightSpan rightComma rightAbsent rightItem rightTail =>
          have same := comma.output_unique rightComma
          cases same
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint rejected
            ⟨_, _, rightItem⟩)
  | laterRejected span comma absent item tail ih =>
      cases rightParsed with
      | identifierRejected rightSpan rightComma rightAbsent rightRejected =>
          have same := comma.output_unique rightComma
          cases same
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint rightRejected
            ⟨_, _, item⟩)
      | laterRejected rightSpan rightComma rightAbsent rightItem rightTail =>
          have same := comma.output_unique rightComma
          cases same
          rcases item.result_unique rightItem with ⟨rfl, rfl⟩
          have tailEq := ih rightTail endpoint
          rw [tailEq]

/-- Full item rejection uniquely fixes its hidden successful prefix. -/
theorem PragmaItemsRejectedPrefix.result_unique
    {input afterLeft afterRight : Remainder} {left right : List Syntax.Identifier}
    (leftParsed : PragmaItemsRejectedPrefix input left afterLeft)
    (rightParsed : PragmaItemsRejectedPrefix input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  have endpoint := pragmaItemsExactOutcomeSpec.rejectOutputUnique
    leftParsed.ordinary rightParsed.ordinary
  refine ⟨?_, endpoint⟩
  cases leftParsed with
  | firstIdentifierRejected absent rejected =>
      cases rightParsed with
      | firstIdentifierRejected => rfl
      | tailRejected rightAbsent rightFirst rightTail =>
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint rejected
            ⟨_, _, rightFirst⟩)
  | tailRejected absent first tail =>
      cases rightParsed with
      | firstIdentifierRejected rightAbsent rightRejected =>
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint rightRejected
            ⟨_, _, first⟩)
      | tailRejected rightAbsent rightFirst rightTail =>
          rcases first.result_unique rightFirst with ⟨rfl, rfl⟩
          rw [(tail.result_unique rightTail).1]

/-- Fixed context and rejected input determine the endpoint, report, and events. -/
theorem PragmaItemsTailTraceRejects.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {leftDiagnostic rightDiagnostic : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : PragmaItemsTailTraceRejects source endByte input afterLeft leftDiagnostic leftTrace)
    (right : PragmaItemsTailTraceRejects source endByte input afterRight rightDiagnostic rightTrace) :
    afterLeft = afterRight ∧ leftDiagnostic = rightDiagnostic ∧ leftTrace = rightTrace := by
  rcases left with ⟨leftPrefix, leftParsed, leftEvents, leftReport⟩
  rcases right with ⟨rightPrefix, rightParsed, rightEvents, rightReport⟩
  rcases leftParsed.result_unique rightParsed with ⟨rfl, rfl⟩
  exact ⟨rfl, leftReport.diagnostic_unique rightReport, leftEvents.trace_unique rightEvents⟩

/-- Complete item rejection also fixes every externally visible trace field. -/
theorem PragmaItemsTraceRejects.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {leftDiagnostic rightDiagnostic : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : PragmaItemsTraceRejects source endByte input afterLeft leftDiagnostic leftTrace)
    (right : PragmaItemsTraceRejects source endByte input afterRight rightDiagnostic rightTrace) :
    afterLeft = afterRight ∧ leftDiagnostic = rightDiagnostic ∧ leftTrace = rightTrace := by
  rcases left with ⟨leftPrefix, leftParsed, leftEvents, leftReport⟩
  rcases right with ⟨rightPrefix, rightParsed, rightEvents, rightReport⟩
  rcases leftParsed.result_unique rightParsed with ⟨rfl, rfl⟩
  exact ⟨rfl, leftReport.diagnostic_unique rightReport, leftEvents.trace_unique rightEvents⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaRejectionTraceGrammar
/-! Exact first-failure pragma traces, separating emitted events from the
uncommitted report. Source and window-end byte remain explicit context. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Each rejecting stage retains only checked-item events already emitted;
the failure report itself is not committed until an enclosing recovery does so. -/
inductive PragmaDeclTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | keywordMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .pragmaKw))
      (reported : RejectAtReports source endByte
        { head := .keyword .pragmaKw, tail := [] } .pragmaDecl input diagnostic) :
      PragmaDeclTraceRejects source endByte input input diagnostic []
  | nameRejected {input afterKeyword rejected : Remainder} {diagnostic : ParseDiagnostic}
      (marker : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
      (nameRejected : IdentifierRejects afterKeyword rejected)
      (reported : RejectAtReports source endByte
        { head := .identifier, tail := [] } .pragmaDecl rejected diagnostic) :
      PragmaDeclTraceRejects source endByte input rejected diagnostic []
  | itemsRejected {input afterKeyword afterName rejected : Remainder}
      {name : Syntax.Identifier} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (marker : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (itemsRejected : PragmaItemsTraceRejects source endByte afterName rejected diagnostic trace) :
      PragmaDeclTraceRejects source endByte input rejected diagnostic trace
  | semicolonMissing {input afterKeyword afterName afterItems : Remainder}
      {name : Syntax.Identifier} {items : List Syntax.Identifier}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (marker : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (itemsParsed : PragmaItemsTraceParses afterName items afterItems trace)
      (absent : TokenKindAbsentAt afterItems.tokens afterItems.endIndex
        afterItems.cursor (.symbol .semicolon))
      (reported : RejectAtReports source endByte
        { head := .symbol .semicolon, tail := [] } .pragmaDecl afterItems diagnostic) :
      PragmaDeclTraceRejects source endByte input afterItems diagnostic trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaPrefixBoundaryTraceGrammar
/-! Independent successful pragma prefixes ending at a recognized rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Written successful declarations precede a recognized rejected pragma.
The endpoint is that last declaration's start, not its internal failure point.
The trace contains prior events only; the separate final report is committed
once by the enclosing file boundary. -/
inductive PragmaPrefixBoundaryTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → List Syntax.PragmaDecl → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop where
  | stopped {input afterKeyword rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (marker : SourceSpan)
      (recognized : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
      (rejected : PragmaDeclTraceRejects source endByte input rejected diagnostic trace) :
      PragmaPrefixBoundaryTraceParses source endByte input [] input diagnostic trace
  | cons {input afterHead stopped : Remainder}
      {head : Syntax.PragmaDecl} {tail : List Syntax.PragmaDecl}
      {diagnostic : ParseDiagnostic} {headTrace tailTrace : List ParseDiagnostic}
      (headParsed : PragmaDeclTraceParses input head afterHead headTrace)
      (tailParsed : PragmaPrefixBoundaryTraceParses source endByte
        afterHead tail stopped diagnostic tailTrace) :
      PragmaPrefixBoundaryTraceParses source endByte input (head :: tail)
        stopped diagnostic (headTrace ++ tailTrace)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaCascadeProperties
/-! The ordered checked-item events of successful pragmas are all protected
from lexical-cascade suppression, including repeated spelling diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Concatenating protected identifier events preserves the full ordered trace. -/
theorem IdentifierListDiagnosticTrace.cascadeFilters
    {names : List Syntax.Identifier} {trace : List ParseDiagnostic}
    (diagnostics : IdentifierListDiagnosticTrace names trace)
    (source : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters source lexical trace trace := by
  induction diagnostics with
  | nil => exact .nil
  | cons head tail ih => exact (head.cascadeFilters source lexical).append ih

/-- Successful pragma traces contain no removable expectation or recovery event. -/
theorem PragmaDeclTraceParses.cascadeFilters
    {input output : Remainder} {declaration : Syntax.PragmaDecl}
    {trace : List ParseDiagnostic}
    (parsed : PragmaDeclTraceParses input declaration output trace)
    (source : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters source lexical trace trace :=
  parsed.2.cascadeFilters source lexical

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaRejectionTraceProperties
/-! Erasure, coverage, and raw-event protection for complete pragma rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Complete rejection traces refine the established first-rejecting-stage grammar. -/
theorem PragmaDeclTraceRejects.ordinary
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace) :
    PragmaDeclRejects input rejected := by
  cases traced with
  | keywordMissing absent reported => exact .keywordMissing absent
  | nameRejected marker keywordParsed nameRejected reported =>
      exact .nameRejected marker keywordParsed nameRejected
  | itemsRejected marker keywordParsed nameParsed itemsRejected =>
      rcases itemsRejected with ⟨names, rejectedPrefix, events, reported⟩
      exact .itemsRejected marker keywordParsed nameParsed rejectedPrefix.ordinary
  | semicolonMissing marker keywordParsed nameParsed itemsParsed absent reported =>
      exact .semicolonMissing marker keywordParsed nameParsed itemsParsed.1 absent

/-- Every ordinary rejection has an independent report and emitted event trace.
The successful prefix stays hidden, because a rejected reply does not return it. -/
theorem PragmaDeclRejects.exists_trace (source : SourceId) (endByte : Nat)
    {input rejected : Remainder} (rejection : PragmaDeclRejects input rejected) :
    ∃ diagnostic trace, PragmaDeclTraceRejects source endByte input rejected diagnostic trace := by
  cases rejection with
  | keywordMissing absent =>
      rcases rejectAtReports_total source endByte
        { head := .keyword .pragmaKw, tail := [] } .pragmaDecl input with ⟨diagnostic, reported⟩
      exact ⟨diagnostic, [], .keywordMissing absent reported⟩
  | nameRejected marker keywordParsed nameRejected =>
      rcases rejectAtReports_total source endByte
        { head := .identifier, tail := [] } .pragmaDecl rejected with ⟨diagnostic, reported⟩
      exact ⟨diagnostic, [], .nameRejected marker keywordParsed nameRejected reported⟩
  | itemsRejected marker keywordParsed nameParsed itemsRejected =>
      rcases itemsRejected.exists_prefix with ⟨names, rejectedPrefix⟩
      rcases identifierListDiagnosticTrace_total names with ⟨trace, events⟩
      rcases rejectAtReports_total source endByte
        { head := .identifier, tail := [] } .pragmaDecl rejected with ⟨diagnostic, reported⟩
      exact ⟨diagnostic, trace, .itemsRejected marker keywordParsed nameParsed
        ⟨names, rejectedPrefix, events, reported⟩⟩
  | semicolonMissing marker keywordParsed nameParsed itemsParsed absent =>
      rcases identifierListDiagnosticTrace_total _ with ⟨trace, events⟩
      rcases rejectAtReports_total source endByte
        { head := .symbol .semicolon, tail := [] } .pragmaDecl rejected with ⟨diagnostic, reported⟩
      exact ⟨diagnostic, trace, .semicolonMissing marker keywordParsed nameParsed
        ⟨itemsParsed, events⟩ absent reported⟩

/-- Previously emitted checked-item events remain protected even when a later
stage rejects. This does not claim protection of the separate failure report. -/
theorem PragmaDeclTraceRejects.cascadeFilters
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases traced with
  | keywordMissing => exact .nil
  | nameRejected => exact .nil
  | itemsRejected marker keywordParsed nameParsed itemsRejected =>
      rcases itemsRejected with ⟨names, rejectedPrefix, events, reported⟩
      exact events.cascadeFilters text lexical
  | semicolonMissing marker keywordParsed nameParsed itemsParsed absent reported =>
      exact itemsParsed.2.cascadeFilters text lexical

private theorem itemsRejection_ordinary
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaItemsTraceRejects source endByte input rejected diagnostic trace) :
    PragmaItemsRejects input rejected := by
  rcases traced with ⟨names, rejectedPrefix, events, reported⟩
  exact rejectedPrefix.ordinary

/-- Fixed context and input determine the exact first failure and every earlier
event; different rejecting stages cannot select competing reports. -/
theorem PragmaDeclTraceRejects.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {leftDiagnostic rightDiagnostic : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : PragmaDeclTraceRejects source endByte input afterLeft leftDiagnostic leftTrace)
    (right : PragmaDeclTraceRejects source endByte input afterRight rightDiagnostic rightTrace) :
    afterLeft = afterRight ∧ leftDiagnostic = rightDiagnostic ∧ leftTrace = rightTrace := by
  cases left with
  | keywordMissing absent reported =>
      cases right with
      | keywordMissing _ rightReported => exact ⟨rfl, reported.diagnostic_unique rightReported, rfl⟩
      | nameRejected marker keywordParsed _ _ => exact False.elim (absent ⟨marker, keywordParsed.1⟩)
      | itemsRejected marker keywordParsed _ _ => exact False.elim (absent ⟨marker, keywordParsed.1⟩)
      | semicolonMissing marker keywordParsed _ _ _ _ =>
          exact False.elim (absent ⟨marker, keywordParsed.1⟩)
  | nameRejected marker keywordParsed nameRejected reported =>
      cases right with
      | keywordMissing absent _ => exact False.elim (absent ⟨marker, keywordParsed.1⟩)
      | nameRejected rightMarker rightKeyword rightName rightReported =>
          cases keywordParsed.output_unique rightKeyword
          cases identifierExactOutcomeSpec.rejectOutputUnique nameRejected rightName
          exact ⟨rfl, reported.diagnostic_unique rightReported, rfl⟩
      | itemsRejected rightMarker rightKeyword rightName rightItems =>
          cases keywordParsed.output_unique rightKeyword
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint nameRejected
            ⟨_, _, rightName⟩)
      | semicolonMissing rightMarker rightKeyword rightName rightItems rightAbsent rightReported =>
          cases keywordParsed.output_unique rightKeyword
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint nameRejected
            ⟨_, _, rightName⟩)
  | itemsRejected marker keywordParsed nameParsed itemsRejected =>
      cases right with
      | keywordMissing absent _ => exact False.elim (absent ⟨marker, keywordParsed.1⟩)
      | nameRejected rightMarker rightKeyword rightName rightReported =>
          cases keywordParsed.output_unique rightKeyword
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint rightName
            ⟨_, _, nameParsed⟩)
      | itemsRejected rightMarker rightKeyword rightName rightItems =>
          cases keywordParsed.output_unique rightKeyword
          rcases nameParsed.result_unique rightName with ⟨rfl, rfl⟩
          exact itemsRejected.result_unique rightItems
      | semicolonMissing rightMarker rightKeyword rightName rightItems rightAbsent rightReported =>
          cases keywordParsed.output_unique rightKeyword
          rcases nameParsed.result_unique rightName with ⟨rfl, rfl⟩
          exact False.elim (pragmaItemsExactOutcomeSpec.successRejectDisjoint
            (itemsRejection_ordinary itemsRejected) ⟨_, _, rightItems.1⟩)
  | semicolonMissing marker keywordParsed nameParsed itemsParsed absent reported =>
      cases right with
      | keywordMissing absent _ => exact False.elim (absent ⟨marker, keywordParsed.1⟩)
      | nameRejected rightMarker rightKeyword rightName rightReported =>
          cases keywordParsed.output_unique rightKeyword
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint rightName
            ⟨_, _, nameParsed⟩)
      | itemsRejected rightMarker rightKeyword rightName rightItems =>
          cases keywordParsed.output_unique rightKeyword
          rcases nameParsed.result_unique rightName with ⟨rfl, rfl⟩
          exact False.elim (pragmaItemsExactOutcomeSpec.successRejectDisjoint
            (itemsRejection_ordinary rightItems) ⟨_, _, itemsParsed.1⟩)
      | semicolonMissing rightMarker rightKeyword rightName rightItems rightAbsent rightReported =>
          cases keywordParsed.output_unique rightKeyword
          rcases nameParsed.result_unique rightName with ⟨rfl, rfl⟩
          rcases itemsParsed.result_unique rightItems with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique rightReported, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaPrefixBoundaryTraceProperties
/-! Exact prefix order, stopping position, and protected pre-failure events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The stopping boundary stays inside the original carrier and active window. -/
theorem PragmaPrefixBoundaryTraceParses.carrier_stop
    {source : SourceId} {endByte : Nat} {input stopped : Remainder}
    {declarations : List Syntax.PragmaDecl} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses source endByte input
      declarations stopped diagnostic trace) :
    stopped.tokens = input.tokens ∧ stopped.endIndex = input.endIndex ∧
      input.cursor ≤ stopped.cursor ∧ stopped.cursor < input.endIndex := by
  induction parsed with
  | stopped marker recognized rejected =>
      exact ⟨rfl, rfl, Nat.le_refl _, recognized.1.1⟩
  | cons head tail ih =>
      have shape := head.1.carrier_progress
      exact ⟨ih.1.trans shape.1, ih.2.1.trans shape.2.1,
        by have advance := shape.2.2.1; have monotone := ih.2.2.1; omega,
        by simpa only [shape.2.1] using ih.2.2.2⟩

/-- Every successful prefix item consumes tokens, and the final recognized
marker requires another remaining token even when its declaration rejects. -/
theorem PragmaPrefixBoundaryTraceParses.length_lt_remaining
    {source : SourceId} {endByte : Nat} {input stopped : Remainder}
    {declarations : List Syntax.PragmaDecl} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses source endByte input
      declarations stopped diagnostic trace) :
    declarations.length < input.endIndex - input.cursor := by
  induction parsed with
  | stopped marker recognized rejected =>
      have inside := recognized.1.1
      simp only [List.length_nil]
      omega
  | cons head tail ih =>
      have shape := head.1.carrier_progress
      simp only [List.length_cons]
      omega

/-- Input and report context uniquely determine the complete successful
prefix, rewound stopping position, uncommitted report, and preceding events. -/
theorem PragmaPrefixBoundaryTraceParses.result_unique
    {source : SourceId} {endByte : Nat} {input leftStop rightStop : Remainder}
    {left right : List Syntax.PragmaDecl} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : PragmaPrefixBoundaryTraceParses source endByte input
      left leftStop leftReport leftTrace)
    (rightParsed : PragmaPrefixBoundaryTraceParses source endByte input
      right rightStop rightReport rightTrace) :
    left = right ∧ leftStop = rightStop ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right rightStop rightReport rightTrace with
  | stopped marker recognized rejected =>
      cases rightParsed with
      | stopped rightMarker rightRecognized rightRejected =>
          rcases rejected.result_unique rightRejected with ⟨_, report, events⟩
          exact ⟨rfl, rfl, report, events⟩
      | cons head tail =>
          exact False.elim (pragmaDeclExactOutcomeSpec.successRejectDisjoint
            rejected.ordinary ⟨_, _, head.1⟩)
  | cons head tail ih =>
      cases rightParsed with
      | stopped marker recognized rejected =>
          exact False.elim (pragmaDeclExactOutcomeSpec.successRejectDisjoint
            rejected.ordinary ⟨_, _, head.1⟩)
      | cons rightHead rightTail =>
          rcases head.result_unique rightHead with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every event preceding the final report is protected from lexical cascade
filtering; this deliberately makes no such claim about the report itself. -/
theorem PragmaPrefixBoundaryTraceParses.cascadeFilters
    {source : SourceId} {endByte : Nat} {input stopped : Remainder}
    {declarations : List Syntax.PragmaDecl} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses source endByte input
      declarations stopped diagnostic trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | stopped marker recognized rejected => exact rejected.cascadeFilters text lexical
  | cons head tail ih => exact (head.cascadeFilters text lexical).append ih

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaRejectionCascadeProperties
/-! Independent filtering after a caller commits a pragma's failure report.
The rejecting grammar's raw trace still excludes that report; only the explicit
appended event is classified here. Every earlier protected occurrence is kept. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Committing an unsuppressed failure appends it after every protected event,
without collapsing equal reports or changing their metadata. -/
theorem PragmaDeclTraceRejects.committedCascadeFilters_of_retained
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace)
    (text : String) (lexical : List SourceSpan)
    (retained : ¬ ParseDiagnosticCascadeSuppresses text lexical diagnostic) :
    ParseDiagnosticCascadeFilters text lexical
      (trace ++ [diagnostic]) (trace ++ [diagnostic]) :=
  (traced.cascadeFilters text lexical).append (.keep retained .nil)

/-- Suppression removes only the newly committed failure, never the earlier
checked-item trace, even when it contains repeated identical reports. -/
theorem PragmaDeclTraceRejects.committedCascadeFilters_of_suppressed
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace)
    (text : String) (lexical : List SourceSpan)
    (suppressed : ParseDiagnosticCascadeSuppresses text lexical diagnostic) :
    ParseDiagnosticCascadeFilters text lexical (trace ++ [diagnostic]) trace := by
  simpa only [List.append_nil] using
    (traced.cascadeFilters text lexical).append (.drop suppressed .nil)

/-- Exact classification of a committed rejection: all raw prefix events
survive, and only the final full failure report may be suppressed. -/
theorem PragmaDeclTraceRejects.committedCascadeFilters_iff
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace kept : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical (trace ++ [diagnostic]) kept ↔
      (¬ ParseDiagnosticCascadeSuppresses text lexical diagnostic ∧
        kept = trace ++ [diagnostic]) ∨
      (ParseDiagnosticCascadeSuppresses text lexical diagnostic ∧ kept = trace) := by
  classical
  constructor
  · intro filtered
    by_cases suppressed : ParseDiagnosticCascadeSuppresses text lexical diagnostic
    · exact Or.inr ⟨suppressed, filtered.output_unique
        (traced.committedCascadeFilters_of_suppressed text lexical suppressed)⟩
    · exact Or.inl ⟨suppressed, filtered.output_unique
        (traced.committedCascadeFilters_of_retained text lexical suppressed)⟩
  · rintro (⟨retained, rfl⟩ | ⟨suppressed, rfl⟩)
    · exact traced.committedCascadeFilters_of_retained text lexical retained
    · exact traced.committedCascadeFilters_of_suppressed text lexical suppressed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaSequenceCascadeProperties
/-! Every event in an independently parsed pragma sequence is protected from
lexical-cascade suppression. Empty sequences and repeated events are retained. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordered concatenation of pragma traces preserves every complete report. -/
theorem PragmaSequenceTraceParses.cascadeFilters
    {input output : Remainder} {declarations : List Syntax.PragmaDecl}
    {trace : List ParseDiagnostic}
    (parsed : PragmaSequenceTraceParses input declarations output trace)
    (source : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters source lexical trace trace := by
  induction parsed with
  | done atEnd => exact .nil
  | cons head tail ih => exact (head.cascadeFilters source lexical).append ih

/-- Independent filtering cannot change even one event of a pragma sequence. -/
theorem PragmaSequenceTraceParses.cascadeFilters_iff
    {input output : Remainder} {declarations : List Syntax.PragmaDecl}
    {trace kept : List ParseDiagnostic}
    (parsed : PragmaSequenceTraceParses input declarations output trace)
    (source : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters source lexical trace kept ↔ kept = trace := by
  constructor
  · intro filtered
    exact filtered.output_unique (parsed.cascadeFilters source lexical)
  · intro same
    subst kept
    exact parsed.cascadeFilters source lexical

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTopItemRecoveryTrace
/-!
Parser-independent diagnostic traces of standalone top-item recovery. Each
event is a source span; the relation fixes its kind and site as top-item
recovery. Events are listed in emission order and exclude earlier diagnostics.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Successful top-item recovery emits exactly its full recovered span. -/
inductive TopItemRecoveryTraceParses :
    Remainder → Syntax.TopItem → Remainder → List SourceSpan → Prop where
  | recovered {input output : Remainder} {item : Syntax.TopItem}
      (parsed : TopItemRecoveryParses input item output) :
      TopItemRecoveryTraceParses input item output [item.span]

/-- Recovery rejecting its mandatory first token emits no diagnostic. -/
inductive TopItemRecoveryTraceRejects :
    Remainder → Remainder → List SourceSpan → Prop where
  | rejected {input output : Remainder}
      (rejection : TopItemRecoveryRejects input output) :
      TopItemRecoveryTraceRejects input output []

/-- Erasure retains the existing exact recovery grammar and singleton event. -/
theorem topItemRecoveryTraceParses_iff
    {input output : Remainder} {item : Syntax.TopItem}
    {trace : List SourceSpan} :
    TopItemRecoveryTraceParses input item output trace ↔
      TopItemRecoveryParses input item output ∧ trace = [item.span] := by
  constructor
  · intro traced
    cases traced with
    | recovered parsed => exact ⟨parsed, rfl⟩
  · rintro ⟨parsed, rfl⟩
    exact .recovered parsed

/-- Rejection erasure retains its exact endpoint and empty event sequence. -/
theorem topItemRecoveryTraceRejects_iff
    {input output : Remainder} {trace : List SourceSpan} :
    TopItemRecoveryTraceRejects input output trace ↔
      TopItemRecoveryRejects input output ∧ trace = [] := by
  constructor
  · intro traced
    cases traced with
    | rejected rejection => exact ⟨rejection, rfl⟩
  · rintro ⟨rejection, rfl⟩
    exact .rejected rejection

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTerminatedControlTraceExactnessProperties
/-! Total, mutually exclusive exact control-leaf traces, derived only from
token observations. Their joint laws instantiate raw and isolated block laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem TerminatedControlStatementTraceRejects.disjoint_success
    {keyword : HardKeyword} {statementValue : Syntax.StatementValue}
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TerminatedControlStatementTraceRejects keyword source endByte
      input rejected diagnostic trace) :
    ¬ ∃ statement output events, TerminatedControlStatementTraceParses keyword statementValue
      source endByte input statement output events := by
  rintro ⟨statement, output, events, parsed⟩
  exact rejection.ordinary.disjointOrdinary ⟨statement, output, parsed.1⟩

/-- Every carrier, including an exhausted window or missing array slot,
determines either silent success or one silent first-failure report. -/
theorem terminatedControlStatementTrace_exists_outcome
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue)
    (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ statement output, TerminatedControlStatementTraceParses keyword statementValue
      source endByte input statement output []) ∨
    (∃ rejected diagnostic, TerminatedControlStatementTraceRejects keyword
      source endByte input rejected diagnostic []) := by
  by_cases marker : ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .keyword keyword }
  · rcases marker with ⟨markerSpan, marker⟩
    let afterMarker : Remainder := { input with cursor := input.cursor + 1 }
    have parsedMarker : ExactTokenParses (.keyword keyword) input markerSpan afterMarker :=
      ⟨marker, rfl⟩
    by_cases semicolon : ∃ span, TokenAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor
        { span, value := .symbol .semicolon }
    · rcases semicolon with ⟨semicolonSpan, semicolon⟩
      exact Or.inl ⟨_, _, .parsed markerSpan semicolonSpan parsedMarker ⟨semicolon, rfl⟩, rfl⟩
    · rcases rejectAtReports_total source endByte { head := .symbol .semicolon, tail := [] }
          .statement afterMarker with ⟨diagnostic, reported⟩
      exact Or.inr ⟨afterMarker, diagnostic,
        .semicolonMissing markerSpan parsedMarker semicolon reported⟩
  · rcases rejectAtReports_total source endByte { head := .keyword keyword, tail := [] }
        .statement input with ⟨diagnostic, reported⟩
    exact Or.inr ⟨input, diagnostic, .markerMissing marker reported⟩

/-- Complete AST/remainder/event uniqueness and exact first-failure exclusion
are unconditional for each fixed keyword-plus-semicolon leaf. -/
theorem terminatedControlStatementTraceExactOutcomeSpec
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue)
    (source : SourceId) (endByte : Nat) :
    StatementTraceExactOutcomeSpec
      (TerminatedControlStatementTraceParses keyword statementValue)
      (TerminatedControlStatementTraceRejects keyword) source endByte where
  successResultUnique := TerminatedControlStatementTraceParses.result_unique
  rejectResultUnique := TerminatedControlStatementTraceRejects.result_unique
  successRejectDisjoint := TerminatedControlStatementTraceRejects.disjoint_success

theorem breakStatementTraceExactOutcomeSpec (source : SourceId) (endByte : Nat) :
    StatementTraceExactOutcomeSpec BreakStatementTraceParses BreakStatementTraceRejects
      source endByte :=
  terminatedControlStatementTraceExactOutcomeSpec .breakKw .breakStmt source endByte

theorem continueStatementTraceExactOutcomeSpec (source : SourceId) (endByte : Nat) :
    StatementTraceExactOutcomeSpec ContinueStatementTraceParses ContinueStatementTraceRejects
      source endByte :=
  terminatedControlStatementTraceExactOutcomeSpec .continueKw .continueStmt source endByte

/-- Blocks restricted to one fixed control leaf have exact independent
outcomes without an abstract statement-outcome assumption. -/
theorem terminatedControlCoreBlockTraceExactOutcomeSpec
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue)
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    BlockTraceExactOutcomeSpec
      (CoreBlockTraceParses (TerminatedControlStatementTraceParses keyword statementValue) policy)
      (CoreBlockTraceRejects (TerminatedControlStatementTraceParses keyword statementValue)
        (TerminatedControlStatementTraceRejects keyword) policy) source endByte :=
  coreBlockTraceExactOutcomeSpec policy
    (terminatedControlStatementTraceExactOutcomeSpec keyword statementValue source endByte)

/-- Every captured child byte boundary has the same unconditional leaf laws,
so isolated restricted blocks also have jointly exact traces and reports. -/
theorem isolatedTerminatedControlCoreBlockTraceExactOutcomeSpec
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue)
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    BlockTraceExactOutcomeSpec
      (IsolatedBlockTraceParses
        (CoreBlockTraceParses (TerminatedControlStatementTraceParses keyword statementValue) policy)
        (CoreBlockTraceRejects (TerminatedControlStatementTraceParses keyword statementValue)
          (TerminatedControlStatementTraceRejects keyword) policy))
      (IsolatedBlockTraceRejects
        (CoreBlockTraceRejects (TerminatedControlStatementTraceParses keyword statementValue)
          (TerminatedControlStatementTraceRejects keyword) policy)) source endByte :=
  isolatedCoreBlockTraceExactOutcomeSpec policy (fun childEndByte =>
    terminatedControlStatementTraceExactOutcomeSpec keyword statementValue source childEndByte)

end Solcore.Syntax.DeclarativeGrammar
end
