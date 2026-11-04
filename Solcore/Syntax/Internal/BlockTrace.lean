import Solcore.Syntax.Grammar.Statements
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Internal.StatementOutcomes
import Solcore.Syntax.Internal.TraceBasics
import Solcore.Syntax.Internal.TypeOutcomes
import Solcore.Syntax.Internal.ExpressionTrace
import Solcore.Syntax.Internal.DotConstructorTrace
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Internal.NameTrace

/-!
Exact diagnostic traces of Core blocks, block statements, return statements and terminated
control: trace grammars, unique outcomes and protection of earlier events.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeReturnStatementTraceGrammar
/-! Independent successful return traces. A current semicolon selects no
value without consuming it; otherwise exactly the expression's events survive. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive OptionalReturnValueTraceParses
    (expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Option Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | absent {input : Remainder} (semicolonSpan : SourceSpan)
      (semicolonCurrent : TokenAt input.tokens input.endIndex input.cursor
        { span := semicolonSpan, value := .symbol .semicolon }) :
      OptionalReturnValueTraceParses expressionTrace source endByte input none input []
  | present {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .semicolon))
      (valueParsed : expressionTrace source endByte input value output trace) :
      OptionalReturnValueTraceParses expressionTrace source endByte input (some value) output trace

inductive ReturnStatementTraceParses
    (expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Statement → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker afterValue output : Remainder}
      {value : Option Syntax.Expr} {trace : List ParseDiagnostic}
      (markerSpan semicolonSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker)
      (valueParsed : OptionalReturnValueTraceParses expressionTrace source endByte
        afterMarker value afterValue trace)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) afterValue semicolonSpan output) :
      ReturnStatementTraceParses expressionTrace source endByte input {
        span := SourceSpan.cover markerSpan semicolonSpan, value := .returnStmt value
      } output trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeReturnStatementRejectionTraceGrammar
/-! Exact independent rejection traces of optional return values and return
statements. Earlier expression events are separate from the uncommitted report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Only the non-semicolon branch can reject, through the expression outcome. -/
inductive OptionalReturnValueTraceRejects
    (expressionRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | expressionRejected {input rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (rejectedExpression : expressionRejects source endByte input rejected diagnostic trace) :
      OptionalReturnValueTraceRejects expressionRejects source endByte
        input rejected diagnostic trace

/-- Return rejection records the first failure: keyword, value, or mandatory
semicolon. A semicolon failure retains the successful value's complete trace. -/
inductive ReturnStatementTraceRejects
    (expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (expressionRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerRejected {input : Remainder} {diagnostic : ParseDiagnostic}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .returnKw))
      (reported : RejectAtReports source endByte
        { head := .keyword .returnKw, tail := [] } .statement input diagnostic) :
      ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
        input input diagnostic []
  | valueRejected {input afterMarker rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker)
      (rejectedValue : OptionalReturnValueTraceRejects expressionRejects source endByte
        afterMarker rejected diagnostic trace) :
      ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
        input rejected diagnostic trace
  | semicolonRejected {input afterMarker afterValue : Remainder} {value : Option Syntax.Expr}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker)
      (valueParsed : OptionalReturnValueTraceParses expressionTrace source endByte
        afterMarker value afterValue trace)
      (semicolonAbsent : TokenKindAbsentAt afterValue.tokens afterValue.endIndex
        afterValue.cursor (.symbol .semicolon))
      (reported : RejectAtReports source endByte
        { head := .symbol .semicolon, tail := [] } .statement afterValue diagnostic) :
      ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
        input afterValue diagnostic trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeReturnStatementTraceProperties
/-! Independent return-trace erasure, context structure, and exact uniqueness. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
  {source : SourceId} {endByte : Nat}

theorem OptionalReturnValueTraceParses.ordinary
    (erases : ∀ {input value output trace}, expressionTrace source endByte input value output trace →
      expressionOrdinary input value output)
    {input output : Remainder} {value : Option Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : OptionalReturnValueTraceParses expressionTrace source endByte input value output trace) :
    OptionalReturnValueParses expressionOrdinary input value output := by
  cases parsed with
  | absent span current => exact .absent span current
  | present absent valueParsed => exact .present absent (erases valueParsed)

theorem ReturnStatementTraceParses.ordinary
    (erases : ∀ {input value output trace}, expressionTrace source endByte input value output trace →
      expressionOrdinary input value output)
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : ReturnStatementTraceParses expressionTrace source endByte input statement output trace) :
    ReturnStatementParses expressionOrdinary input statement output := by
  cases parsed with
  | parsed marker semicolon markerParsed valueParsed semicolonParsed =>
      exact .parsed marker semicolon markerParsed (valueParsed.ordinary erases) semicolonParsed

theorem OptionalReturnValueTraceParses.output_window
    (expressionWindow : ∀ {input value output trace},
      expressionTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Option Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : OptionalReturnValueTraceParses expressionTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | absent => exact ⟨rfl, rfl⟩
  | present _ valueParsed => exact expressionWindow valueParsed

theorem ReturnStatementTraceParses.output_window
    (expressionWindow : ∀ {input value output trace},
      expressionTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : ReturnStatementTraceParses expressionTrace source endByte input statement output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed marker semicolon markerParsed valueParsed semicolonParsed =>
      rcases markerParsed with ⟨_, rfl⟩
      rcases semicolonParsed with ⟨_, rfl⟩
      exact valueParsed.output_window expressionWindow

theorem OptionalReturnValueTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      expressionTrace source endByte input left afterLeft leftTrace →
      expressionTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Option Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : OptionalReturnValueTraceParses expressionTrace source endByte
      input left afterLeft leftTrace)
    (rightParsed : OptionalReturnValueTraceParses expressionTrace source endByte
      input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | absent span current =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl, rfl⟩
      | present absent _ => exact False.elim (absent ⟨span, current⟩)
  | present absent valueParsed =>
      cases rightParsed with
      | absent span current => exact False.elim (absent ⟨span, current⟩)
      | present _ rightValue =>
          rcases unique valueParsed rightValue with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ReturnStatementTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      expressionTrace source endByte input left afterLeft leftTrace →
      expressionTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Statement}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ReturnStatementTraceParses expressionTrace source endByte
      input left afterLeft leftTrace)
    (rightParsed : ReturnStatementTraceParses expressionTrace source endByte
      input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftMarker leftSemicolon markerLeft valueLeft semicolonLeft =>
      cases rightParsed with
      | parsed rightMarker rightSemicolon markerRight valueRight semicolonRight =>
          rcases markerLeft.result_unique markerRight with ⟨rfl, rfl⟩
          rcases valueLeft.result_unique unique valueRight with ⟨rfl, rfl, rfl⟩
          rcases semicolonLeft.result_unique semicolonRight with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeReturnStatementRejectionTraceProperties
/-! Exact first-return-failure outcomes under explicit expression laws.
Uncommitted reports and preceding event sequences are independently unique. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop}
  {source : SourceId} {endByte : Nat}

theorem OptionalReturnValueTraceRejects.ordinary
    (rejectErases : ∀ {input rejected diagnostic trace},
      expressionRejects source endByte input rejected diagnostic trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalReturnValueTraceRejects expressionRejects source endByte
      input rejected diagnostic trace) : OptionalReturnValueRejects ordinaryRejects input rejected := by
  cases rejection with
  | expressionRejected absent rejected => exact .expressionRejected absent (rejectErases rejected)

theorem ReturnStatementTraceRejects.ordinary
    (successErases : ∀ {input value output trace},
      expressionTrace source endByte input value output trace → expressionOrdinary input value output)
    (rejectErases : ∀ {input rejected diagnostic trace},
      expressionRejects source endByte input rejected diagnostic trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input rejected diagnostic trace) :
    ReturnStatementRejects expressionOrdinary ordinaryRejects input rejected := by
  cases rejection with
  | markerRejected absent reported => exact .markerRejected absent
  | valueRejected span marker rejected => exact .valueRejected span marker (rejected.ordinary rejectErases)
  | semicolonRejected span marker value absent reported =>
      exact .semicolonRejected span marker (value.ordinary successErases) absent

variable
  (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    expressionTrace source endByte input left afterLeft leftTrace →
    expressionTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
  (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    expressionRejects source endByte input afterLeft leftReport leftTrace →
    expressionRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
  (disjoint : ∀ {input rejected diagnostic trace},
    expressionRejects source endByte input rejected diagnostic trace →
      ¬ ∃ value output events, expressionTrace source endByte input value output events)

include rejectUnique in
theorem OptionalReturnValueTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : OptionalReturnValueTraceRejects expressionRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : OptionalReturnValueTraceRejects expressionRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | expressionRejected _ rejected =>
      cases right with
      | expressionRejected _ other => exact rejectUnique rejected other

include disjoint in
theorem OptionalReturnValueTraceRejects.disjoint_success
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalReturnValueTraceRejects expressionRejects source endByte
      input rejected diagnostic trace) :
    ¬ ∃ value output events,
      OptionalReturnValueTraceParses expressionTrace source endByte input value output events := by
  rintro ⟨_, _, _, parsed⟩
  cases rejection with
  | expressionRejected absent rejected =>
      cases parsed with
      | absent span token => exact absent ⟨span, token⟩
      | present _ parsed => exact disjoint rejected ⟨_, _, _, parsed⟩

include successUnique rejectUnique disjoint in
theorem ReturnStatementTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | markerRejected absent reported =>
      cases right with
      | markerRejected _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | valueRejected span marker _ | semicolonRejected span marker _ _ _ =>
          exact False.elim (absent ⟨span, marker.1⟩)
  | valueRejected span marker rejected =>
      cases right with
      | markerRejected absent _ => exact False.elim (absent ⟨span, marker.1⟩)
      | valueRejected _ otherMarker other =>
          cases marker.output_unique otherMarker
          exact rejected.result_unique rejectUnique other
      | semicolonRejected _ otherMarker parsed _ _ =>
          cases marker.output_unique otherMarker
          exact False.elim (rejected.disjoint_success disjoint ⟨_, _, _, parsed⟩)
  | semicolonRejected span marker parsed absent reported =>
      cases right with
      | markerRejected missing _ => exact False.elim (missing ⟨span, marker.1⟩)
      | valueRejected _ otherMarker rejected =>
          cases marker.output_unique otherMarker
          exact False.elim (rejected.disjoint_success disjoint ⟨_, _, _, parsed⟩)
      | semicolonRejected _ otherMarker other _ otherReport =>
          cases marker.output_unique otherMarker
          rcases parsed.result_unique successUnique other with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique otherReport, rfl⟩

include successUnique disjoint in
theorem ReturnStatementTraceRejects.disjoint_success
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input rejected diagnostic trace) :
    ¬ ∃ statement output events,
      ReturnStatementTraceParses expressionTrace source endByte input statement output events := by
  rintro ⟨_, _, _, parsed⟩
  cases parsed with
  | parsed markerSpan semicolonSpan marker value semicolon =>
      cases rejection with
      | markerRejected absent _ => exact absent ⟨markerSpan, marker.1⟩
      | valueRejected _ otherMarker rejected =>
          cases marker.output_unique otherMarker
          exact rejected.disjoint_success disjoint ⟨_, _, _, value⟩
      | semicolonRejected _ otherMarker other absent _ =>
          cases marker.output_unique otherMarker
          cases (value.result_unique successUnique other).2.1
          exact absent ⟨semicolonSpan, semicolon.1⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeIsolatedBlockTraceGrammar
/-! Independent diagnostic traces through balanced block isolation. Inner
judgments carry source and end-byte context explicitly: a captured child uses
its own closing-byte boundary, while the parent retains its original window.
Only recovered child rejection appends the previously uncommitted report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact successful isolation over abstract inner block trace judgments. -/
inductive IsolatedBlockTraceParses
    (blockParses : SourceId → Nat → Remainder → Syntax.Block → Remainder →
      List ParseDiagnostic → Prop)
    (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
      List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop where
  | direct {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
      (captureAbsent : BalancedBlockCaptureAbsentAt input)
      (bodyParsed : blockParses source endByte input body output trace) :
      IsolatedBlockTraceParses blockParses blockRejects source endByte input body output trace
  | captured {input childOutput : Remainder} {body : Syntax.Block}
      {capture : BalancedBlockCapture} {trace : List ParseDiagnostic}
      (captureParsed : BalancedBlockCaptures input capture)
      (bodyParsed : blockParses source capture.endByte
        (capture.childRemainder input) body childOutput trace) :
      IsolatedBlockTraceParses blockParses blockRejects source endByte input body
        (capture.parentRemainder input) trace
  | recovered {input childRejected : Remainder} {capture : BalancedBlockCapture}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (captureParsed : BalancedBlockCaptures input capture)
      (bodyRejected : blockRejects source capture.endByte
        (capture.childRemainder input) childRejected diagnostic trace) :
      IsolatedBlockTraceParses blockParses blockRejects source endByte input
        { span := capture.span, value := [] } (capture.parentRemainder input)
        (trace ++ [diagnostic])

/-- An uncaptured rejection escapes with exactly its original report and
trace. Captured ordinary rejection is a success of the recovery wrapper. -/
inductive IsolatedBlockTraceRejects
    (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
      List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | direct {input rejected : Remainder} {diagnostic : ParseDiagnostic}
      {trace : List ParseDiagnostic}
      (captureAbsent : BalancedBlockCaptureAbsentAt input)
      (bodyRejected : blockRejects source endByte input rejected diagnostic trace) :
      IsolatedBlockTraceRejects blockRejects source endByte input rejected diagnostic trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeIsolatedBlockTraceErasureProperties
/-! Trace erasure preserves the existing independent isolation outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Any sound erasure of the inner trace judgments lifts through direct
execution, successful capture, and captured rejection recovery. -/
theorem IsolatedBlockTraceParses.ordinary
    {blockParses : SourceId → Nat → Remainder → Syntax.Block → Remainder →
      List ParseDiagnostic → Prop}
    {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
      List ParseDiagnostic → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejected : Remainder → Remainder → Prop}
    (successErases : ∀ source endByte input body output trace,
      blockParses source endByte input body output trace → blockOrdinary input body output)
    (rejectionErases : ∀ source endByte input rejected diagnostic trace,
      blockRejects source endByte input rejected diagnostic trace → blockRejected input rejected)
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {body : Syntax.Block} {trace : List ParseDiagnostic}
    (parsed : IsolatedBlockTraceParses blockParses blockRejects source endByte
      input body output trace) :
    IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejected input body output := by
  cases parsed with
  | direct absent bodyParsed => exact .direct absent (successErases _ _ _ _ _ _ bodyParsed)
  | captured capture bodyParsed => exact .captured capture (successErases _ _ _ _ _ _ bodyParsed)
  | recovered capture bodyRejected =>
      exact .recovered capture (rejectionErases _ _ _ _ _ _ bodyRejected)

/-- An escaping rejection erases to the direct, uncaptured ordinary branch. -/
theorem IsolatedBlockTraceRejects.ordinary
    {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
      List ParseDiagnostic → Prop}
    {blockRejected : Remainder → Remainder → Prop}
    (rejectionErases : ∀ source endByte input rejected diagnostic trace,
      blockRejects source endByte input rejected diagnostic trace → blockRejected input rejected)
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : IsolatedBlockTraceRejects blockRejects source endByte
      input rejected diagnostic trace) :
    IsolatedCoreBlockRejects blockRejected input rejected := by
  cases rejection with
  | direct absent bodyRejected => exact .direct absent (rejectionErases _ _ _ _ _ _ bodyRejected)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeIsolatedBlockTraceProperties
/-! Exact ASTs, endpoints, reports, and ordered traces through block isolation.
Only fixed-context inner functionality and disjointness are assumed; totality
is not asserted. Captured children use their own end byte, not their parent's. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Three exactness laws at one source and byte boundary, without executable
state, outcomes, or any assumption that a grammar derivation exists. -/
structure BlockTraceExactOutcomeSpec
    (blockParses : SourceId → Nat → Remainder → Syntax.Block → Remainder →
      List ParseDiagnostic → Prop)
    (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
      List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) : Prop where
  successResultUnique : ∀ {input leftOutput rightOutput left right leftTrace rightTrace},
    blockParses source endByte input left leftOutput leftTrace →
    blockParses source endByte input right rightOutput rightTrace →
    left = right ∧ leftOutput = rightOutput ∧ leftTrace = rightTrace
  rejectResultUnique : ∀ {input leftOutput rightOutput leftReport rightReport leftTrace rightTrace},
    blockRejects source endByte input leftOutput leftReport leftTrace →
    blockRejects source endByte input rightOutput rightReport rightTrace →
    leftOutput = rightOutput ∧ leftReport = rightReport ∧ leftTrace = rightTrace
  successRejectDisjoint : ∀ {input rejected diagnostic trace},
    blockRejects source endByte input rejected diagnostic trace →
    ¬ ∃ body output events, blockParses source endByte input body output events

variable
  {blockParses : SourceId → Nat → Remainder → Syntax.Block → Remainder →
    List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
    List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

/-- Parent-context direct parsing and child-context capture/recovery have one
exact outer AST, parent remainder, and trace, including an appended failure. -/
theorem IsolatedBlockTraceParses.result_unique
    (innerOutcomes : ∀ childEndByte, BlockTraceExactOutcomeSpec
      blockParses blockRejects source childEndByte)
    {input leftOutput rightOutput : Remainder} {left right : Syntax.Block}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : IsolatedBlockTraceParses blockParses blockRejects source endByte
      input left leftOutput leftTrace)
    (rightParsed : IsolatedBlockTraceParses blockParses blockRejects source endByte
      input right rightOutput rightTrace) :
    left = right ∧ leftOutput = rightOutput ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | direct leftAbsent leftBody =>
      cases rightParsed with
      | direct rightAbsent rightBody =>
          exact (innerOutcomes endByte).successResultUnique leftBody rightBody
      | captured rightCapture rightBody => exact False.elim (leftAbsent ⟨_, rightCapture⟩)
      | recovered rightCapture rightRejected => exact False.elim (leftAbsent ⟨_, rightCapture⟩)
  | captured leftCapture leftBody =>
      cases rightParsed with
      | direct rightAbsent rightBody => exact False.elim (rightAbsent ⟨_, leftCapture⟩)
      | captured rightCapture rightBody =>
          cases leftCapture.output_unique rightCapture
          rcases (innerOutcomes _).successResultUnique leftBody rightBody with
            ⟨bodyEq, _childEndpoint, traceEq⟩
          exact ⟨bodyEq, rfl, traceEq⟩
      | recovered rightCapture rightRejected =>
          cases leftCapture.output_unique rightCapture
          exact False.elim ((innerOutcomes _).successRejectDisjoint rightRejected
            ⟨_, _, _, leftBody⟩)
  | recovered leftCapture leftRejected =>
      cases rightParsed with
      | direct rightAbsent rightBody => exact False.elim (rightAbsent ⟨_, leftCapture⟩)
      | captured rightCapture rightBody =>
          cases leftCapture.output_unique rightCapture
          exact False.elim ((innerOutcomes _).successRejectDisjoint leftRejected
            ⟨_, _, _, rightBody⟩)
      | recovered rightCapture rightRejected =>
          cases leftCapture.output_unique rightCapture
          rcases (innerOutcomes _).rejectResultUnique leftRejected rightRejected with
            ⟨_childEndpoint, reportEq, traceEq⟩
          exact ⟨rfl, rfl, by rw [traceEq, reportEq]⟩

/-- Escaping rejection is always direct, so only the original parent-context
exactness is needed to fix its endpoint, uncommitted report, and earlier events. -/
theorem IsolatedBlockTraceRejects.result_unique
    (innerOutcomes : BlockTraceExactOutcomeSpec blockParses blockRejects source endByte)
    {input leftOutput rightOutput : Remainder}
    {leftReport rightReport : ParseDiagnostic} {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : IsolatedBlockTraceRejects blockRejects source endByte
      input leftOutput leftReport leftTrace)
    (rightRejected : IsolatedBlockTraceRejects blockRejects source endByte
      input rightOutput rightReport rightTrace) :
    leftOutput = rightOutput ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | direct leftAbsent leftBody =>
      cases rightRejected with
      | direct rightAbsent rightBody => exact innerOutcomes.rejectResultUnique leftBody rightBody

/-- No captured success or recovered child rejection can compete with an
uncaptured escaping rejection. Direct competition uses only parent exactness. -/
theorem IsolatedBlockTraceRejects.disjoint_success
    (innerOutcomes : BlockTraceExactOutcomeSpec blockParses blockRejects source endByte)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : IsolatedBlockTraceRejects blockRejects source endByte
      input rejected diagnostic trace) :
    ¬ ∃ body output events,
      IsolatedBlockTraceParses blockParses blockRejects source endByte input body output events := by
  rintro ⟨body, output, events, parsed⟩
  cases rejection with
  | direct absent rejectedBody =>
      cases parsed with
      | direct otherAbsent bodyParsed =>
          exact innerOutcomes.successRejectDisjoint rejectedBody ⟨_, _, _, bodyParsed⟩
      | captured captured bodyParsed => exact absent ⟨_, captured⟩
      | recovered captured otherRejected => exact absent ⟨_, captured⟩

/-- Lift fixed-source inner trace exactness across all possible child byte
boundaries. The source never changes; the parent's end byte is not reused for a capture. -/
theorem isolatedBlockTraceExactOutcomeSpec
    (innerOutcomes : ∀ childEndByte, BlockTraceExactOutcomeSpec
      blockParses blockRejects source childEndByte) :
    BlockTraceExactOutcomeSpec (IsolatedBlockTraceParses blockParses blockRejects)
      (IsolatedBlockTraceRejects blockRejects) source endByte where
  successResultUnique := IsolatedBlockTraceParses.result_unique innerOutcomes
  rejectResultUnique := IsolatedBlockTraceRejects.result_unique (innerOutcomes endByte)
  successRejectDisjoint := IsolatedBlockTraceRejects.disjoint_success (innerOutcomes endByte)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockTraceGrammar
/-! Independent successful raw Core blocks with exact diagnostic sequences.
Statement events follow source order. Tail-validation events are appended only
after the closing brace, not interleaved with individual statement events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Successful statements followed by the preferred exact closing brace.
Source and byte-window context are shared by every abstract statement judgment. -/
inductive CoreBlockItemsTraceParses
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → List Syntax.Statement → SourceSpan → Remainder →
      List ParseDiagnostic → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingToken : ExactTokenParses (.symbol .rightBrace) input closingSpan output) :
      CoreBlockItemsTraceParses statementTrace source endByte input [] closingSpan output []
  | next {input afterStatement output : Remainder}
      {statement : Syntax.Statement} {statements : List Syntax.Statement}
      {closingSpan : SourceSpan} {statementEvents tailEvents : List ParseDiagnostic}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementParsed : statementTrace source endByte input statement afterStatement statementEvents)
      (progress : input.cursor < afterStatement.cursor)
      (tail : CoreBlockItemsTraceParses statementTrace source endByte afterStatement
        statements closingSpan output tailEvents) :
      CoreBlockItemsTraceParses statementTrace source endByte input
        (statement :: statements) closingSpan output (statementEvents ++ tailEvents)

/-- The completed AST retains exact braces and written statement order. Only
then does policy-dependent tail validation append its complete ordered trace. -/
inductive CoreBlockTraceParses
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterOpening output : Remainder}
      {statements : List Syntax.Statement} {statementEvents validationEvents : List ParseDiagnostic}
      (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBrace) input openingSpan afterOpening)
      (bodyParsed : CoreBlockItemsTraceParses statementTrace source endByte afterOpening
        statements closingSpan output statementEvents)
      (validated : CoreBlockTailsDiagnosticTrace policy statements validationEvents) :
      CoreBlockTraceParses statementTrace policy source endByte input {
        span := SourceSpan.cover openingSpan closingSpan
        value := statements
      } output (statementEvents ++ validationEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockRejectionTraceGrammar
/-! Independent ordinary rejection traces of raw Core blocks. A missing
closing brace or rejected statement returns before tail validation. Only
statement events already emitted precede the separate uncommitted report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact first rejecting item stage, with the closing-brace branch preferred.
The source and byte endpoint stay fixed throughout the abstract statement chain. -/
inductive CoreBlockItemsTraceRejects
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (statementRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | missingClose {input : Remainder} {diagnostic : ParseDiagnostic}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (atEnd : input.endIndex ≤ input.cursor)
      (reported : RejectAtReports source endByte
        { head := .symbol .rightBrace, tail := [] } .statement input diagnostic) :
      CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
        input input diagnostic []
  | statementRejected {input rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementRejected : statementRejects source endByte input rejected diagnostic trace) :
      CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
        input rejected diagnostic trace
  | laterRejected {input afterStatement rejected : Remainder}
      {statement : Syntax.Statement} {diagnostic : ParseDiagnostic}
      {statementEvents tailEvents : List ParseDiagnostic}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementParsed : statementTrace source endByte input statement afterStatement statementEvents)
      (progress : input.cursor < afterStatement.cursor)
      (tailRejected : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
        afterStatement rejected diagnostic tailEvents) :
      CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
        input rejected diagnostic (statementEvents ++ tailEvents)

/-- A missing opening brace emits no prior event. After an exact opening,
only the item-rejection trace survives; no block-tail check has run. -/
inductive CoreBlockTraceRejects
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (statementRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | openingMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBrace))
      (reported : RejectAtReports source endByte
        { head := .symbol .leftBrace, tail := [] } .statement input diagnostic) :
      CoreBlockTraceRejects statementTrace statementRejects policy source endByte
        input input diagnostic []
  | itemsRejected {input afterOpening rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) input openingSpan afterOpening)
      (itemsRejected : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
        afterOpening rejected diagnostic trace) :
      CoreBlockTraceRejects statementTrace statementRejects policy source endByte
        input rejected diagnostic trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeBlockStatementTraceGrammar
/-! Exact block-statement traces wrap a raw Core block with required tail
semicolons. No balanced capture, recovery, or parent-window restoration occurs. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive BlockStatementTraceParses
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Statement → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
      (bodyParsed : CoreBlockTraceParses statementTrace .require source endByte input body output trace) :
      BlockStatementTraceParses statementTrace source endByte input
        { span := body.span, value := .block body.value } output trace

inductive BlockStatementTraceRejects
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (statementRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | rejected {input output : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (bodyRejected : CoreBlockTraceRejects statementTrace statementRejects .require
        source endByte input output diagnostic trace) :
      BlockStatementTraceRejects statementTrace statementRejects source endByte
        input output diagnostic trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockTailTraceProperties
/-! Total, unique, protected statement-termination traces. Empty traces recover
the existing diagnostic-free tail predicate without imposing it on all parses. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every statement has a mandatory-termination diagnostic trace. -/
theorem CoreBlockStatementDiagnosticTrace.exists_trace (statement : Syntax.Statement) :
    ∃ trace, CoreBlockStatementDiagnosticTrace statement trace := by
  classical
  by_cases terminated : CoreBlockStatementTerminated statement
  · exact ⟨[], .clean terminated⟩
  · exact ⟨_, .missing terminated⟩

/-- The statement's own span and termination status determine its entire trace. -/
theorem CoreBlockStatementDiagnosticTrace.output_unique
    {statement : Syntax.Statement} {left right : List ParseDiagnostic}
    (leftParsed : CoreBlockStatementDiagnosticTrace statement left)
    (rightParsed : CoreBlockStatementDiagnosticTrace statement right) : left = right := by
  cases leftParsed with
  | clean terminated =>
      cases rightParsed with
      | clean => rfl
      | missing absent => exact False.elim (absent terminated)
  | missing absent =>
      cases rightParsed with
      | clean terminated => exact False.elim (absent terminated)
      | missing => rfl

/-- A mandatory check is silent exactly when statement termination is valid. -/
theorem CoreBlockStatementDiagnosticTrace.empty_iff
    {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : CoreBlockStatementDiagnosticTrace statement trace) :
    trace = [] ↔ CoreBlockStatementTerminated statement := by
  cases parsed with
  | clean terminated => exact ⟨fun _ => terminated, fun _ => rfl⟩
  | missing absent => simp only [List.cons_ne_self, false_iff]; exact absent

/-- Constraint reports are protected regardless of the lexical error context. -/
theorem CoreBlockStatementDiagnosticTrace.cascadeFilters
    {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : CoreBlockStatementDiagnosticTrace statement trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | clean => exact .nil
  | missing => exact .keep (fun suppressed => suppressed.1) .nil

/-- Every statement list and final-expression policy has a complete trace. -/
theorem CoreBlockTailsDiagnosticTrace.exists_trace
    (policy : CoreBlockTailPolicy) (statements : List Syntax.Statement) :
    ∃ trace, CoreBlockTailsDiagnosticTrace policy statements trace := by
  induction statements with
  | nil => exact ⟨[], .nil⟩
  | cons first rest ih =>
      cases rest with
      | nil =>
          cases policy with
          | allow => exact ⟨[], .lastAllowed⟩
          | require =>
              rcases CoreBlockStatementDiagnosticTrace.exists_trace first with ⟨trace, parsed⟩
              exact ⟨trace, .lastRequired parsed⟩
      | cons second rest =>
          rcases CoreBlockStatementDiagnosticTrace.exists_trace first with ⟨headTrace, head⟩
          rcases ih with ⟨tailTrace, tail⟩
          exact ⟨headTrace ++ tailTrace, .cons head tail⟩

/-- Tail validation has exactly one ordered trace, including all duplicates. -/
theorem CoreBlockTailsDiagnosticTrace.output_unique
    {policy : CoreBlockTailPolicy} {statements : List Syntax.Statement}
    {left right : List ParseDiagnostic}
    (leftParsed : CoreBlockTailsDiagnosticTrace policy statements left)
    (rightParsed : CoreBlockTailsDiagnosticTrace policy statements right) : left = right := by
  induction leftParsed generalizing right with
  | nil => cases rightParsed; rfl
  | lastAllowed => cases rightParsed; rfl
  | lastRequired checked =>
      cases rightParsed with
      | lastRequired other => exact checked.output_unique other
  | cons checked tail ih =>
      cases rightParsed with
      | cons other otherTail => rw [checked.output_unique other, ih otherTail]

/-- A complete trace is empty precisely under the original tail-validity
predicate, including the exemption for the final allowed expression. -/
theorem CoreBlockTailsDiagnosticTrace.empty_iff
    {policy : CoreBlockTailPolicy} {statements : List Syntax.Statement}
    {trace : List ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements trace) :
    trace = [] ↔ CoreBlockTailsValid policy statements := by
  induction parsed with
  | nil => simp only [CoreBlockTailsValid, iff_self]
  | lastAllowed => simp only [CoreBlockTailsValid, iff_self]
  | lastRequired checked => exact checked.empty_iff
  | cons checked tail ih =>
      simp only [List.append_eq_nil_iff, checked.empty_iff, ih, CoreBlockTailsValid]

/-- Every emitted constraint survives lexical normalization in source order. -/
theorem CoreBlockTailsDiagnosticTrace.cascadeFilters
    {policy : CoreBlockTailPolicy} {statements : List Syntax.Statement}
    {trace : List ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | nil | lastAllowed => exact .nil
  | lastRequired checked => exact checked.cascadeFilters text lexical
  | cons checked tail ih => exact (checked.cascadeFilters text lexical).append ih

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockTailCascadeProperties
/-! Independent normalization of statement events followed by tail validation.
Only the leading events may be filtered; the complete protected tail stays last. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Filtering arbitrary earlier events preserves the complete appended tail
trace, including its original order, full reports, and duplicate occurrences. -/
theorem CoreBlockTailsDiagnosticTrace.append_cascadeFilters
    {policy : CoreBlockTailPolicy} {statements : List Syntax.Statement}
    {tailTrace events keptEvents : List ParseDiagnostic}
    {text : String} {lexical : List SourceSpan}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements tailTrace)
    (filtered : ParseDiagnosticCascadeFilters text lexical events keptEvents) :
    ParseDiagnosticCascadeFilters text lexical
      (events ++ tailTrace) (keptEvents ++ tailTrace) :=
  filtered.append (parsed.cascadeFilters text lexical)

/-- Every possible normalized result is exactly a normalized event prefix
followed by the unchanged tail-validation trace; the converse also holds. -/
theorem CoreBlockTailsDiagnosticTrace.append_cascadeFilters_iff
    {policy : CoreBlockTailPolicy} {statements : List Syntax.Statement}
    {tailTrace events kept : List ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements tailTrace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical (events ++ tailTrace) kept ↔
      ∃ keptEvents, ParseDiagnosticCascadeFilters text lexical events keptEvents ∧
        kept = keptEvents ++ tailTrace := by
  constructor
  · intro filtered
    rcases parseDiagnosticCascadeFilters_total text lexical events with ⟨keptEvents, leading⟩
    exact ⟨keptEvents, leading,
      filtered.output_unique (parsed.append_cascadeFilters leading)⟩
  · rintro ⟨keptEvents, leading, rfl⟩
    exact parsed.append_cascadeFilters leading

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockTraceProperties
/-! Raw-block trace erasure, exact functionality, and cursor/window laws.
Only the abstract statement judgment needs corresponding context-preservation
and result-uniqueness premises; no execution or rejection assumptions occur. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
  {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}

/-- Erasing every inner event sequence recovers the existing block-items grammar. -/
theorem CoreBlockItemsTraceParses.ordinary
    (statementErases : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        statementOrdinary input statement output)
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) :
    CoreBlockItemsParses statementOrdinary input statements closingSpan output := by
  induction parsed with
  | close span token => exact .close span token
  | next inside absent statement progress tail ih =>
      exact .next inside absent (statementErases statement) progress ih

/-- Tail reports do not remove ordinary success or modify its AST and remainder. -/
theorem CoreBlockTraceParses.ordinary
    (statementErases : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        statementOrdinary input statement output)
    {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace) :
    CoreBlockOrdinaryParses statementOrdinary policy input body output := by
  cases parsed with
  | parsed opening closing token items validated =>
      exact .parsed opening closing token (items.ordinary statementErases)

/-- At least the final closing brace is consumed. -/
theorem CoreBlockItemsTraceParses.cursor_lt
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) : input.cursor < output.cursor := by
  induction parsed with
  | close span token => rcases token with ⟨_, rfl⟩; simp
  | next _ _ _ progress _ ih => exact Nat.lt_trans progress ih

/-- The closing token bounds the final cursor, even before any statement
carrier-preservation premise is imposed. -/
theorem CoreBlockItemsTraceParses.output_cursor_le_endIndex
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) : output.cursor ≤ output.endIndex := by
  induction parsed with
  | close span token => rcases token with ⟨inside, rfl⟩; exact inside.1
  | next _ _ _ _ _ ih => exact ih

/-- Each statement advances strictly and the closing brace needs one more slot. -/
theorem CoreBlockItemsTraceParses.length_lt_cursor_distance
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) :
    statements.length < output.cursor - input.cursor := by
  induction parsed with
  | close span token => rcases token with ⟨_, rfl⟩; simp
  | next _ _ _ progress _ ih => simp only [List.length_cons]; omega

/-- Abstract statement window preservation lifts through the ordered list. -/
theorem CoreBlockItemsTraceParses.output_window
    (statementWindow : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  induction parsed with
  | close span token => rcases token with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
  | next _ _ statement _ _ ih =>
      have step := statementWindow statement
      exact ⟨ih.1.trans step.1, ih.2.trans step.2⟩

theorem CoreBlockTraceParses.cursor_lt
    {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed opening closing token items validated =>
      rcases token with ⟨_, rfl⟩
      exact Nat.lt_trans (by simp) items.cursor_lt

theorem CoreBlockTraceParses.output_cursor_le_endIndex
    {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace) :
    output.cursor ≤ output.endIndex := by
  cases parsed with
  | parsed opening closing token items validated => exact items.output_cursor_le_endIndex

theorem CoreBlockTraceParses.output_window
    (statementWindow : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed opening closing token items validated =>
      rcases token with ⟨_, rfl⟩
      exact items.output_window statementWindow

/-- Closing-branch priority and exact inner traces fix the complete statement
list, final brace span, remainder, and all events, including duplicate events. -/
theorem CoreBlockItemsTraceParses.result_unique
    (statementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      statementTrace source endByte input left afterLeft leftTrace →
      statementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : List Syntax.Statement}
    {leftClosing rightClosing : SourceSpan} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : CoreBlockItemsTraceParses statementTrace source endByte
      input left leftClosing afterLeft leftTrace)
    (rightParsed : CoreBlockItemsTraceParses statementTrace source endByte
      input right rightClosing afterRight rightTrace) :
    left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right afterRight rightClosing rightTrace with
  | close span token =>
      cases rightParsed with
      | close rightSpan rightToken =>
          rcases token.result_unique rightToken with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩
      | next _ absent _ _ _ =>
          exact False.elim (typeTokenAbsent_conflicts_token absent token.1)
  | next _ absent statement _ _ ih =>
      cases rightParsed with
      | close span token => exact False.elim (typeTokenAbsent_conflicts_token absent token.1)
      | next _ _ rightStatement _ rightTail =>
          rcases statementUnique statement rightStatement with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩

/-- Exact statement traces and deterministic tail validation fix the covering
AST, remainder, and full statement-events-then-validation-events sequence. -/
theorem CoreBlockTraceParses.result_unique
    (statementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      statementTrace source endByte input left afterLeft leftTrace →
      statementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Block}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : CoreBlockTraceParses statementTrace policy source endByte
      input left afterLeft leftTrace)
    (rightParsed : CoreBlockTraceParses statementTrace policy source endByte
      input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftOpening leftClosing leftToken leftItems leftValidated =>
      cases rightParsed with
      | parsed rightOpening rightClosing rightToken rightItems rightValidated =>
          rcases leftToken.result_unique rightToken with ⟨rfl, rfl⟩
          rcases leftItems.result_unique statementUnique rightItems with ⟨rfl, rfl, rfl, rfl⟩
          rw [leftValidated.output_unique rightValidated]
          exact ⟨rfl, rfl, rfl⟩

/-- An empty total trace forces tail validity; ordinary parses with nonempty
constraint traces are not incorrectly reclassified as diagnostic-free syntax. -/
theorem CoreBlockTraceParses.empty_trace_tailsValid
    {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace)
    (empty : trace = []) : CoreBlockTailsValid policy body.value := by
  cases parsed with
  | parsed opening closing token items validated =>
      exact validated.empty_iff.mp (List.append_eq_nil_iff.mp empty).2

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockCascadeProperties
/-! Complete raw-block trace normalization keeps the delayed validation suffix.
The body AST determines that suffix, independently of earlier statement events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {policy : CoreBlockTailPolicy} {source : SourceId} {endByte : Nat}
  {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}

/-- The block trace is the ordered statement events followed by the whole
body's validation events. Any independent validation trace fixes that suffix. -/
theorem CoreBlockTraceParses.split_at_validation
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace)
    {validationEvents : List ParseDiagnostic}
    (validated : CoreBlockTailsDiagnosticTrace policy body.value validationEvents) :
    ∃ openingSpan closingSpan afterOpening statementEvents,
      ExactTokenParses (.symbol .leftBrace) input openingSpan afterOpening ∧
      CoreBlockItemsTraceParses statementTrace source endByte afterOpening body.value
        closingSpan output statementEvents ∧
      body.span = SourceSpan.cover openingSpan closingSpan ∧
      trace = statementEvents ++ validationEvents := by
  cases parsed with
  | parsed opening closing token items actual =>
      exact ⟨opening, closing, _, _, token, items, rfl,
        congrArg (fun tail => _ ++ tail) (actual.output_unique validated)⟩

/-- Normalization filters only the statement-event prefix. Every validation
report remains at the end with its full payload, source span, and multiplicity. -/
theorem CoreBlockTraceParses.cascadeFilters_iff
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace)
    {validationEvents kept : List ParseDiagnostic}
    (validated : CoreBlockTailsDiagnosticTrace policy body.value validationEvents)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace kept ↔
      ∃ statementEvents keptStatementEvents,
        trace = statementEvents ++ validationEvents ∧
        ParseDiagnosticCascadeFilters text lexical statementEvents keptStatementEvents ∧
        kept = keptStatementEvents ++ validationEvents := by
  constructor
  · intro filtered
    rcases parsed.split_at_validation validated with
      ⟨_, _, _, statementEvents, _, _, _, traceEq⟩
    rw [traceEq] at filtered
    rcases (validated.append_cascadeFilters_iff text lexical).mp filtered with
      ⟨keptEvents, leading, keptEq⟩
    exact ⟨statementEvents, keptEvents, traceEq, leading, keptEq⟩
  · rintro ⟨statementEvents, keptEvents, traceEq, leading, keptEq⟩
    rw [traceEq, keptEq]
    exact validated.append_cascadeFilters leading

/-- With a fixed validation trace, every normalized block trace ends with that
unchanged suffix, including a suffix containing repeated identical reports. -/
theorem CoreBlockTraceParses.normalized_validation_suffix
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace)
    {validationEvents kept : List ParseDiagnostic}
    (validated : CoreBlockTailsDiagnosticTrace policy body.value validationEvents)
    {text : String} {lexical : List SourceSpan}
    (filtered : ParseDiagnosticCascadeFilters text lexical trace kept) :
    ∃ keptStatementEvents, kept = keptStatementEvents ++ validationEvents := by
  rcases (parsed.cascadeFilters_iff validated text lexical).mp filtered with
    ⟨_, keptEvents, _, _, keptEq⟩
  exact ⟨keptEvents, keptEq⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockRejectionTraceProperties
/-! Exact raw-block rejection traces and exclusion of successful traces.
All functionality assumptions belong to the abstract statement judgments;
fixed source/byte context determines primitive brace reports independently. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop}
  {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}

/-- Erasure preserves the exact first rejecting statement/closing stage. -/
theorem CoreBlockItemsTraceRejects.ordinary
    (successErases : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        statementOrdinary input statement output)
    (rejectErases : ∀ {input rejected diagnostic trace},
      statementRejects source endByte input rejected diagnostic trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
      input rejected diagnostic trace) :
    CoreBlockItemsRejects statementOrdinary ordinaryRejects input rejected := by
  induction rejection with
  | missingClose absent atEnd reported => exact .missingClose absent atEnd
  | statementRejected inside absent statement =>
      exact .statementRejected inside absent (rejectErases statement)
  | laterRejected inside absent statement progress tail ih =>
      exact .laterRejected inside absent (successErases statement) progress ih

/-- A raw-block rejection refines its established ordinary rejection grammar. -/
theorem CoreBlockTraceRejects.ordinary
    (successErases : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        statementOrdinary input statement output)
    (rejectErases : ∀ {input rejected diagnostic trace},
      statementRejects source endByte input rejected diagnostic trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input rejected diagnostic trace) :
    CoreBlockRejects statementOrdinary ordinaryRejects policy input rejected := by
  cases rejection with
  | openingMissing absent reported => exact .openingMissing absent
  | itemsRejected span opening items =>
      exact .itemsRejected span opening (items.ordinary successErases rejectErases)

/-- Tail policy cannot change a rejection that returns before tail validation. -/
theorem CoreBlockTraceRejects.withPolicy
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input rejected diagnostic trace) (otherPolicy : CoreBlockTailPolicy) :
    CoreBlockTraceRejects statementTrace statementRejects otherPolicy source endByte
      input rejected diagnostic trace := by
  cases rejection with
  | openingMissing absent reported => exact .openingMissing absent reported
  | itemsRejected span opening items => exact .itemsRejected span opening items

variable
  (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    statementTrace source endByte input left afterLeft leftTrace →
    statementTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
  (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    statementRejects source endByte input afterLeft leftReport leftTrace →
    statementRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
  (disjoint : ∀ {input rejected diagnostic trace},
    statementRejects source endByte input rejected diagnostic trace →
      ¬ ∃ statement output events, statementTrace source endByte input statement output events)

include successUnique rejectUnique disjoint in
/-- The first rejecting endpoint, full report, and ordered preceding events
are unique; at-end and next-statement branches cannot compete. -/
theorem CoreBlockItemsTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  induction left generalizing afterRight rightReport rightTrace with
  | missingClose absent atEnd reported =>
      cases right with
      | missingClose _ _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | statementRejected inside _ _ | laterRejected inside _ _ _ _ =>
          exact False.elim (Nat.not_lt_of_ge atEnd inside)
  | statementRejected inside absent statement =>
      cases right with
      | missingClose _ atEnd _ => exact False.elim (Nat.not_lt_of_ge atEnd inside)
      | statementRejected _ _ other => exact rejectUnique statement other
      | laterRejected _ _ other _ _ => exact False.elim (disjoint statement ⟨_, _, _, other⟩)
  | laterRejected inside absent statement progress tail ih =>
      cases right with
      | missingClose _ atEnd _ => exact False.elim (Nat.not_lt_of_ge atEnd inside)
      | statementRejected _ _ other => exact False.elim (disjoint other ⟨_, _, _, statement⟩)
      | laterRejected _ _ other _ otherTail =>
          rcases successUnique statement other with ⟨rfl, rfl, rfl⟩
          rcases ih otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include successUnique rejectUnique disjoint in
/-- Exact opening recognition and exact item rejection fix the full result.
No delayed validation trace is present in either rejecting branch. -/
theorem CoreBlockTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input afterLeft leftReport leftTrace)
    (right : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | openingMissing absent reported =>
      cases right with
      | openingMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | itemsRejected span opening _ => exact False.elim (absent ⟨span, opening.1⟩)
  | itemsRejected span opening items =>
      cases right with
      | openingMissing absent _ => exact False.elim (absent ⟨span, opening.1⟩)
      | itemsRejected otherSpan otherOpening otherItems =>
          cases opening.output_unique otherOpening
          exact items.result_unique successUnique rejectUnique disjoint otherItems

include successUnique disjoint in
/-- A rejected item chain excludes every successful closing chain, regardless
of what later block-tail validation would have reported. -/
theorem CoreBlockItemsTraceRejects.disjoint_success
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
      input rejected diagnostic trace) :
    ¬ ∃ statements closingSpan output events,
      CoreBlockItemsTraceParses statementTrace source endByte input statements closingSpan output events := by
  induction rejection with
  | missingClose absent atEnd reported =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | close span token => exact absent ⟨_, token.1⟩
      | next inside _ _ _ _ => exact Nat.not_lt_of_ge atEnd inside
  | statementRejected inside absent statement =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | close span token => exact absent ⟨_, token.1⟩
      | next _ _ other _ _ => exact disjoint statement ⟨_, _, _, other⟩
  | laterRejected inside absent statement progress tail ih =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | close span token => exact absent ⟨_, token.1⟩
      | next _ _ other _ otherTail =>
          cases (successUnique statement other).2.1
          exact ih ⟨_, _, _, _, otherTail⟩

include successUnique disjoint in
/-- An exact raw rejection excludes all full successful traces. -/
theorem CoreBlockTraceRejects.disjoint_success
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input rejected diagnostic trace) :
    ¬ ∃ body output events,
      CoreBlockTraceParses statementTrace policy source endByte input body output events := by
  rintro ⟨_, _, _, parsed⟩
  cases rejection with
  | openingMissing absent reported =>
      cases parsed with
      | parsed opening closing token items validated => exact absent ⟨opening, token.1⟩
  | itemsRejected span opening items =>
      cases parsed with
      | parsed otherOpening closing token otherItems validated =>
          cases opening.output_unique token
          exact items.disjoint_success successUnique disjoint ⟨_, _, _, _, otherItems⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockTraceExactnessProperties
/-! Joint exactness of raw and isolated Core block traces. The only abstract
premises concern statement outcomes at the explicit source and byte boundary.
No premise asserts that an outcome exists or that a concrete parser implements it. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact statement outcomes at one source/window context, including complete
event lists and the report that remains uncommitted on ordinary rejection. -/
structure StatementTraceExactOutcomeSpec
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (statementRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) : Prop where
  successResultUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    statementTrace source endByte input left afterLeft leftTrace →
    statementTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace
  rejectResultUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    statementRejects source endByte input afterLeft leftReport leftTrace →
    statementRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace
  successRejectDisjoint : ∀ {input rejected diagnostic trace},
    statementRejects source endByte input rejected diagnostic trace →
      ¬ ∃ statement output events, statementTrace source endByte input statement output events

variable
  {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

/-- Statement exactness determines raw block ASTs, remainders, reports, and
traces under either tail policy, including rejecting paths with no validation. -/
theorem coreBlockTraceExactOutcomeSpec (policy : CoreBlockTailPolicy)
    (statements : StatementTraceExactOutcomeSpec statementTrace statementRejects source endByte) :
    BlockTraceExactOutcomeSpec (CoreBlockTraceParses statementTrace policy)
      (CoreBlockTraceRejects statementTrace statementRejects policy) source endByte where
  successResultUnique := CoreBlockTraceParses.result_unique statements.successResultUnique
  rejectResultUnique := CoreBlockTraceRejects.result_unique statements.successResultUnique
    statements.rejectResultUnique statements.successRejectDisjoint
  successRejectDisjoint := CoreBlockTraceRejects.disjoint_success statements.successResultUnique
    statements.successRejectDisjoint

/-- The same source's statement laws at every captured end byte determine
isolated blocks, including recovery to an empty body with one committed report. -/
theorem isolatedCoreBlockTraceExactOutcomeSpec (policy : CoreBlockTailPolicy)
    (statements : ∀ childEndByte,
      StatementTraceExactOutcomeSpec statementTrace statementRejects source childEndByte) :
    BlockTraceExactOutcomeSpec
      (IsolatedBlockTraceParses (CoreBlockTraceParses statementTrace policy)
        (CoreBlockTraceRejects statementTrace statementRejects policy))
      (IsolatedBlockTraceRejects (CoreBlockTraceRejects statementTrace statementRejects policy))
      source endByte :=
  isolatedBlockTraceExactOutcomeSpec (fun childEndByte =>
    coreBlockTraceExactOutcomeSpec policy (statements childEndByte))

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeReturnStatementTraceExactnessProperties
/-! Independent expression trace laws lift through return statements and
restricted raw/isolated blocks. Conditional outcome existence is proved apart. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem returnStatementTraceExactOutcomeSpec
    (expressions : ExpressionTraceExactOutcomeSpec expressionTrace expressionRejects source endByte) :
    StatementTraceExactOutcomeSpec (ReturnStatementTraceParses expressionTrace)
      (ReturnStatementTraceRejects expressionTrace expressionRejects) source endByte where
  successResultUnique := ReturnStatementTraceParses.result_unique expressions.successResultUnique
  rejectResultUnique := ReturnStatementTraceRejects.result_unique expressions.successResultUnique
    expressions.rejectResultUnique expressions.successRejectDisjoint
  successRejectDisjoint := ReturnStatementTraceRejects.disjoint_success
    expressions.successResultUnique expressions.successRejectDisjoint

/-- This describes blocks restricted to return statements; no mixed Core
statement-dispatch or concrete expression trace claim is implicit. -/
theorem returnCoreBlockTraceExactOutcomeSpec (policy : CoreBlockTailPolicy)
    (expressions : ExpressionTraceExactOutcomeSpec expressionTrace expressionRejects source endByte) :
    BlockTraceExactOutcomeSpec (CoreBlockTraceParses (ReturnStatementTraceParses expressionTrace) policy)
      (CoreBlockTraceRejects (ReturnStatementTraceParses expressionTrace)
        (ReturnStatementTraceRejects expressionTrace expressionRejects) policy) source endByte :=
  coreBlockTraceExactOutcomeSpec policy (returnStatementTraceExactOutcomeSpec expressions)

theorem isolatedReturnCoreBlockTraceExactOutcomeSpec (policy : CoreBlockTailPolicy)
    (expressions : ∀ childEndByte,
      ExpressionTraceExactOutcomeSpec expressionTrace expressionRejects source childEndByte) :
    BlockTraceExactOutcomeSpec
      (IsolatedBlockTraceParses (CoreBlockTraceParses (ReturnStatementTraceParses expressionTrace) policy)
        (CoreBlockTraceRejects (ReturnStatementTraceParses expressionTrace)
          (ReturnStatementTraceRejects expressionTrace expressionRejects) policy))
      (IsolatedBlockTraceRejects (CoreBlockTraceRejects (ReturnStatementTraceParses expressionTrace)
        (ReturnStatementTraceRejects expressionTrace expressionRejects) policy)) source endByte :=
  isolatedCoreBlockTraceExactOutcomeSpec policy (fun childEndByte =>
    returnStatementTraceExactOutcomeSpec (expressions childEndByte))

/-- The semicolon guard either skips the expression or uses one of its
independent outcomes. No uniqueness, cursor, or window premise is needed. -/
theorem optionalReturnValueTrace_exists_outcome
    (expressions : ExpressionTraceOutcomeExists expressionTrace expressionRejects source endByte)
    (input : Remainder) :
    (∃ value output trace,
      OptionalReturnValueTraceParses expressionTrace source endByte input value output trace) ∨
    (∃ rejected diagnostic trace,
      OptionalReturnValueTraceRejects expressionRejects source endByte input rejected diagnostic trace) := by
  by_cases current : ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .symbol .semicolon }
  · rcases current with ⟨span, current⟩
    exact Or.inl ⟨none, input, [], .absent span current⟩
  · rcases expressions input with successful | rejected
    · rcases successful with ⟨value, output, trace, parsed⟩
      exact Or.inl ⟨some value, output, trace, .present current parsed⟩
    · rcases rejected with ⟨output, diagnostic, trace, rejection⟩
      exact Or.inr ⟨output, diagnostic, trace, .expressionRejected current rejection⟩

/-- Return outcome existence follows from expression existence alone, keeping
the exact first report and all expression events. It does not assert block totality. -/
theorem returnStatementTrace_exists_outcome
    (expressions : ExpressionTraceOutcomeExists expressionTrace expressionRejects source endByte)
    (input : Remainder) :
    (∃ statement output trace,
      ReturnStatementTraceParses expressionTrace source endByte input statement output trace) ∨
    (∃ rejected diagnostic trace,
      ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
        input rejected diagnostic trace) := by
  by_cases current : ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .keyword .returnKw }
  · rcases current with ⟨markerSpan, current⟩
    let afterMarker : Remainder := { input with cursor := input.cursor + 1 }
    have marker : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker := ⟨current, rfl⟩
    rcases optionalReturnValueTrace_exists_outcome expressions afterMarker with successful | rejected
    · rcases successful with ⟨value, afterValue, trace, parsed⟩
      by_cases semicolon : ∃ span, TokenAt afterValue.tokens afterValue.endIndex afterValue.cursor
          { span, value := .symbol .semicolon }
      · rcases semicolon with ⟨semicolonSpan, semicolon⟩
        exact Or.inl ⟨_, _, trace, .parsed markerSpan semicolonSpan marker parsed ⟨semicolon, rfl⟩⟩
      · rcases rejectAtReports_total source endByte { head := .symbol .semicolon, tail := [] }
            .statement afterValue with ⟨diagnostic, reported⟩
        exact Or.inr ⟨afterValue, diagnostic, trace,
          .semicolonRejected markerSpan marker parsed semicolon reported⟩
    · rcases rejected with ⟨output, diagnostic, trace, rejection⟩
      exact Or.inr ⟨output, diagnostic, trace, .valueRejected markerSpan marker rejection⟩
  · rcases rejectAtReports_total source endByte { head := .keyword .returnKw, tail := [] }
        .statement input with ⟨diagnostic, reported⟩
    exact Or.inr ⟨input, diagnostic, [], .markerRejected current reported⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeBlockStatementTraceProperties
/-! Independent ordinary erasure and exact block-statement outcome laws.
The raw block's complete AST, remainder, reports, and event order are retained. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop}
  {source : SourceId} {endByte : Nat}

theorem BlockStatementTraceParses.ordinary
    (erases : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace → statementOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses statementTrace source endByte input statement output trace) :
    BlockStatementOrdinaryParses statementOrdinary input statement output := by
  cases parsed with
  | parsed body => exact .parsed (body.ordinary erases)

theorem BlockStatementTraceRejects.ordinary
    (successErases : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace → statementOrdinary input statement output)
    (rejectErases : ∀ {input rejected diagnostic trace},
      statementRejects source endByte input rejected diagnostic trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : BlockStatementTraceRejects statementTrace statementRejects source endByte
      input rejected diagnostic trace) : BlockStatementRejects statementOrdinary ordinaryRejects input rejected := by
  cases rejection with
  | rejected body => exact body.ordinary successErases rejectErases

theorem BlockStatementTraceParses.cursor_lt
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses statementTrace source endByte input statement output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed body => exact body.cursor_lt

theorem BlockStatementTraceParses.output_cursor_le_endIndex
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses statementTrace source endByte input statement output trace) :
    output.cursor ≤ output.endIndex := by
  cases parsed with
  | parsed body => exact body.output_cursor_le_endIndex

theorem BlockStatementTraceParses.output_window
    (statementWindow : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses statementTrace source endByte input statement output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed body => exact body.output_window statementWindow

theorem BlockStatementTraceParses.result_unique
    (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      statementTrace source endByte input left afterLeft leftTrace →
      statementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Statement}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : BlockStatementTraceParses statementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : BlockStatementTraceParses statementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftBody =>
      cases rightParsed with
      | parsed rightBody =>
          rcases leftBody.result_unique successUnique rightBody with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem BlockStatementTraceRejects.result_unique
    (statements : StatementTraceExactOutcomeSpec statementTrace statementRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : BlockStatementTraceRejects statementTrace statementRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : BlockStatementTraceRejects statementTrace statementRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | rejected leftBody =>
      cases right with
      | rejected rightBody =>
          exact leftBody.result_unique statements.successResultUnique statements.rejectResultUnique
            statements.successRejectDisjoint rightBody

theorem BlockStatementTraceRejects.disjoint_success
    (statements : StatementTraceExactOutcomeSpec statementTrace statementRejects source endByte)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : BlockStatementTraceRejects statementTrace statementRejects source endByte
      input rejected diagnostic trace) :
    ¬ ∃ statement output events,
      BlockStatementTraceParses statementTrace source endByte input statement output events := by
  rintro ⟨_, _, _, parsed⟩
  cases rejection with
  | rejected bodyRejected =>
      cases parsed with
      | parsed bodyParsed =>
          exact bodyRejected.disjoint_success statements.successResultUnique
            statements.successRejectDisjoint ⟨_, _, _, bodyParsed⟩

theorem blockStatementTraceExactOutcomeSpec
    (statements : StatementTraceExactOutcomeSpec statementTrace statementRejects source endByte) :
    StatementTraceExactOutcomeSpec (BlockStatementTraceParses statementTrace)
      (BlockStatementTraceRejects statementTrace statementRejects) source endByte where
  successResultUnique := BlockStatementTraceParses.result_unique statements.successResultUnique
  rejectResultUnique := BlockStatementTraceRejects.result_unique statements
  successRejectDisjoint := BlockStatementTraceRejects.disjoint_success statements

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeStatementTraceProtectionProperties
/-! Complete protected traces compose through returns and raw block
statements. Recovered unexpected-token reports are not presumed protected. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem OptionalReturnValueTraceParses.cascadeFilters
    (expressionProtected : ∀ {input value output trace},
      expressionTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Option Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : OptionalReturnValueTraceParses expressionTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | absent => exact .nil
  | present _ value => exact expressionProtected value

theorem ReturnStatementTraceParses.cascadeFilters
    (expressionProtected : ∀ {input value output trace},
      expressionTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : ReturnStatementTraceParses expressionTrace source endByte input statement output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ _ value _ => exact value.cascadeFilters expressionProtected

theorem CoreBlockItemsTraceParses.cascadeFilters
    (statementProtected : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | close => exact .nil
  | next _ _ statement _ _ ih => exact (statementProtected statement).append ih

/-- Delayed validation emits only protected constraints, so a raw block
whose statement events are protected retains its entire successful trace. -/
theorem CoreBlockTraceParses.cascadeFilters
    (statementProtected : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {policy : CoreBlockTailPolicy} {input output : Remainder} {body : Syntax.Block}
    {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ _ items validation =>
      exact (items.cascadeFilters statementProtected).append (validation.cascadeFilters text lexical)

theorem BlockStatementTraceParses.cascadeFilters
    (statementProtected : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses statementTrace source endByte input statement output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed body => exact body.cascadeFilters statementProtected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeRejectionTraceProtectionProperties
/-! Protected earlier events survive normalization even when parsing later
rejects. The uncommitted final report is not asserted to be protected. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem OptionalReturnValueTraceRejects.cascadeFilters
    (rejectProtected : ∀ {input rejected diagnostic trace},
      expressionRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalReturnValueTraceRejects expressionRejects source endByte
      input rejected diagnostic trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | expressionRejected _ expression => exact rejectProtected expression

theorem ReturnStatementTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      expressionTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      expressionRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input rejected diagnostic trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerRejected => exact .nil
  | valueRejected _ _ value => exact value.cascadeFilters rejectProtected
  | semicolonRejected _ _ value _ _ => exact value.cascadeFilters successProtected

theorem CoreBlockItemsTraceRejects.cascadeFilters
    (successProtected : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      statementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
      input rejected diagnostic trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction rejection with
  | missingClose => exact .nil
  | statementRejected _ _ statement => exact rejectProtected statement
  | laterRejected _ _ statement _ _ ih => exact (successProtected statement).append ih

theorem CoreBlockTraceRejects.cascadeFilters
    (successProtected : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      statementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {policy : CoreBlockTailPolicy} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input rejected diagnostic trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | openingMissing => exact .nil
  | itemsRejected _ _ items => exact items.cascadeFilters successProtected rejectProtected

theorem BlockStatementTraceRejects.cascadeFilters
    (successProtected : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      statementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : BlockStatementTraceRejects statementTrace statementRejects source endByte
      input rejected diagnostic trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | rejected body => exact body.cascadeFilters successProtected rejectProtected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTerminatedControlTraceGrammar
/-! Independent exact traces for keyword-plus-semicolon control statements.
Both success and rejection are silent; the first missing token fixes the report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A fixed control statement retains both exact tokens and emits no event.
Context parameters permit direct composition with other statement traces. -/
def TerminatedControlStatementTraceParses (keyword : HardKeyword)
    (statementValue : Syntax.StatementValue) (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (statement : Syntax.Statement) (output : Remainder)
    (trace : List ParseDiagnostic) : Prop :=
  TerminatedControlStatementOrdinaryParses keyword statementValue input statement output ∧ trace = []

/-- Keyword rejection takes priority; semicolon rejection requires the exact
successful keyword. The final report is uncommitted, so the trace remains empty. -/
inductive TerminatedControlStatementTraceRejects (keyword : HardKeyword)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword keyword))
      (reported : RejectAtReports source endByte { head := .keyword keyword, tail := [] }
        .statement input diagnostic) :
      TerminatedControlStatementTraceRejects keyword source endByte input input diagnostic []
  | semicolonMissing {input afterMarker : Remainder} {diagnostic : ParseDiagnostic}
      (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.keyword keyword) input markerSpan afterMarker)
      (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
        afterMarker.cursor (.symbol .semicolon))
      (reported : RejectAtReports source endByte { head := .symbol .semicolon, tail := [] }
        .statement afterMarker diagnostic) :
      TerminatedControlStatementTraceRejects keyword source endByte input afterMarker diagnostic []

abbrev BreakStatementTraceParses := TerminatedControlStatementTraceParses .breakKw .breakStmt
abbrev ContinueStatementTraceParses := TerminatedControlStatementTraceParses .continueKw .continueStmt
abbrev BreakStatementTraceRejects := TerminatedControlStatementTraceRejects .breakKw
abbrev ContinueStatementTraceRejects := TerminatedControlStatementTraceRejects .continueKw

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTerminatedControlTraceProperties
/-! Exact functionality and ordinary erasure of silent control traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {keyword : HardKeyword} {statementValue : Syntax.StatementValue}
  {source : SourceId} {endByte : Nat}

theorem TerminatedControlStatementTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Statement}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TerminatedControlStatementTraceParses keyword statementValue
      source endByte input left afterLeft leftTrace)
    (rightParsed : TerminatedControlStatementTraceParses keyword statementValue
      source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  rcases leftParsed with ⟨leftParsed, rfl⟩
  rcases rightParsed with ⟨rightParsed, rfl⟩
  cases leftParsed with
  | parsed leftMarker leftSemicolon markerLeft semicolonLeft =>
      cases rightParsed with
      | parsed rightMarker rightSemicolon markerRight semicolonRight =>
          rcases markerLeft.result_unique markerRight with ⟨rfl, rfl⟩
          rcases semicolonLeft.result_unique semicolonRight with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem TerminatedControlStatementTraceRejects.ordinary
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : TerminatedControlStatementTraceRejects keyword source endByte
      input rejected diagnostic trace) : TerminatedControlStatementRejects keyword input rejected := by
  cases traced with
  | markerMissing absent _ => exact .markerMissing absent
  | semicolonMissing span marker absent _ => exact .semicolonMissing span marker absent

theorem TerminatedControlStatementTraceRejects.trace_eq_nil
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : TerminatedControlStatementTraceRejects keyword source endByte
      input rejected diagnostic trace) : trace = [] := by
  cases traced <;> rfl

theorem TerminatedControlStatementTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {left right : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : TerminatedControlStatementTraceRejects keyword source endByte
      input afterLeft left leftTrace)
    (rightRejected : TerminatedControlStatementTraceRejects keyword source endByte
      input afterRight right rightTrace) :
    afterLeft = afterRight ∧ left = right ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | markerMissing absent reported =>
      cases rightRejected with
      | markerMissing _ rightReported => exact ⟨rfl, reported.diagnostic_unique rightReported, rfl⟩
      | semicolonMissing span marker _ _ => exact False.elim (absent ⟨span, marker.1⟩)
  | semicolonMissing span marker absent reported =>
      cases rightRejected with
      | markerMissing rightAbsent _ => exact False.elim (rightAbsent ⟨span, marker.1⟩)
      | semicolonMissing rightSpan rightMarker _ rightReported =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique rightReported, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLiteralExpressionTraceExactnessProperties
/-! Concrete literal-expression traces discharge both independent expression
assumptions and supply exact return-only block outcomes without abstract laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem literalExpressionTraceExactOutcomeSpec (source : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec LiteralExpressionTraceParses LiteralExpressionTraceRejects
      source endByte where
  successResultUnique := LiteralExpressionTraceParses.result_unique
  rejectResultUnique := CoreLiteralTraceRejects.result_unique
  successRejectDisjoint := by
    intro input rejected diagnostic trace rejection
    rintro ⟨value, output, events, parsed⟩
    exact LiteralExpressionTraceRejects.disjoint_success rejection parsed

theorem literalExpressionTraceOutcomeExists (source : SourceId) (endByte : Nat) :
    ExpressionTraceOutcomeExists LiteralExpressionTraceParses LiteralExpressionTraceRejects
      source endByte :=
  literalExpressionTrace_outcome_total source endByte

theorem literalReturnStatementTraceExactOutcomeSpec (source : SourceId) (endByte : Nat) :
    StatementTraceExactOutcomeSpec (ReturnStatementTraceParses LiteralExpressionTraceParses)
      (ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects)
      source endByte :=
  returnStatementTraceExactOutcomeSpec (literalExpressionTraceExactOutcomeSpec source endByte)

/-- Empty returns and one-literal returns have an independent ordinary
outcome on every carrier, including exact reports for malformed inputs. -/
theorem literalReturnStatementTrace_exists_outcome
    (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ statement output trace,
      ReturnStatementTraceParses LiteralExpressionTraceParses source endByte
        input statement output trace) ∨
    (∃ rejected diagnostic trace,
      ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects
        source endByte input rejected diagnostic trace) :=
  returnStatementTrace_exists_outcome (literalExpressionTraceOutcomeExists source endByte) input

theorem literalReturnCoreBlockTraceExactOutcomeSpec
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    BlockTraceExactOutcomeSpec
      (CoreBlockTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses) policy)
      (CoreBlockTraceRejects (ReturnStatementTraceParses LiteralExpressionTraceParses)
        (ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects) policy)
      source endByte :=
  returnCoreBlockTraceExactOutcomeSpec policy (literalExpressionTraceExactOutcomeSpec source endByte)

theorem isolatedLiteralReturnCoreBlockTraceExactOutcomeSpec
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    BlockTraceExactOutcomeSpec
      (IsolatedBlockTraceParses
        (CoreBlockTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses) policy)
        (CoreBlockTraceRejects (ReturnStatementTraceParses LiteralExpressionTraceParses)
          (ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects) policy))
      (IsolatedBlockTraceRejects
        (CoreBlockTraceRejects (ReturnStatementTraceParses LiteralExpressionTraceParses)
          (ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects) policy))
      source endByte :=
  isolatedReturnCoreBlockTraceExactOutcomeSpec policy (literalExpressionTraceExactOutcomeSpec source)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionAtomDispatchTraceProperties
/-! Concrete raw leaf/type exactness and explicit nested-expression/block
exactness lift through one prioritized atom layer. Values, full remainders,
terminal reports, and ordered event sequences are preserved. Neither child
existence nor recursive expression execution follows from this joint bundle. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ExpressionAtomDispatchFinalTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ExpressionAtomDispatchFinalTraceRejects source endByte input afterLeft leftReport leftTrace)
    (right : ExpressionAtomDispatchFinalTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | rejected report =>
      cases right with
      | rejected other => exact ⟨rfl, report.diagnostic_unique other, rfl⟩

theorem ExpressionAtomDispatchTraceParses.raw_of_selected
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    {branch : ExpressionAtomDispatchBranch} (selection : ExpressionAtomDispatchSelects input branch)
    (parsed : ExpressionAtomDispatchTraceParses nestedTrace blockTrace source endByte input value output trace) :
    ExpressionAtomDispatchRawTraceParses nestedTrace blockTrace branch source endByte input value output trace := by
  cases parsed with
  | selected actual actualSelection raw =>
      cases selection.branch_unique actualSelection
      exact raw

theorem ExpressionAtomDispatchTraceRejects.raw_of_selected
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    {branch : ExpressionAtomDispatchBranch} (selection : ExpressionAtomDispatchSelects input branch)
    (rejection : ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects
      source endByte input rejected report trace) :
    ExpressionAtomDispatchRawTraceRejects nestedTrace nestedRejects blockRejects branch
      source endByte input rejected report trace := by
  cases rejection with
  | selected actual actualSelection raw =>
      cases selection.branch_unique actualSelection
      exact raw

theorem ExpressionAtomDispatchTraceParses.not_final
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (selection : ExpressionAtomDispatchSelects input .final)
    (parsed : ExpressionAtomDispatchTraceParses nestedTrace blockTrace source endByte input value output trace) : False :=
  parsed.raw_of_selected selection

theorem ExpressionAtomDispatchTraceRejects.final_iff
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (selection : ExpressionAtomDispatchSelects input .final) :
    ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects source endByte input rejected report trace ↔
      rejected = input ∧
      RejectAtReports source endByte { head := .expression, tail := [] } .expression input report ∧ trace = [] := by
  constructor
  · intro rejection
    have raw := rejection.raw_of_selected selection
    cases raw with
    | rejected reported => exact ⟨rfl, reported, rfl⟩
  · rintro ⟨rfl, reported, rfl⟩
    exact .selected .final selection (.rejected reported)

/-- Raw forms need only independent nested/body uniqueness and disjointness.
All literal, name, type, parameter, and return-type laws are concrete. -/
theorem expressionAtomDispatchRawTraceExactOutcomeSpec
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    (blocks : TraceExactOutcomeSpec blockTrace blockRejects source endByte)
    (branch : ExpressionAtomDispatchBranch) :
    TraceExactOutcomeSpec (ExpressionAtomDispatchRawTraceParses nestedTrace blockTrace branch)
      (ExpressionAtomDispatchRawTraceRejects nestedTrace nestedRejects blockRejects branch) source endByte := by
  cases branch with
  | literal => exact (literalExpressionTraceExactOutcomeSpec source endByte).toTraceExactOutcomeSpec
  | name => exact (identifierExpressionTrace_exactOutcomeSpec source endByte).toTraceExactOutcomeSpec
  | dotConstructor => exact (dotConstructorTraceExactOutcomeSpec nested.toExpressionTraceExactOutcomeSpec).toTraceExactOutcomeSpec
  | proxy => exact (proxyExpressionTraceExactOutcomeSpec typeExprTraceExactOutcomeSpec).toTraceExactOutcomeSpec
  | parenthesized => exact (parenthesizedTraceExactOutcomeSpec nested.toExpressionTraceExactOutcomeSpec).toTraceExactOutcomeSpec
  | array => exact (arrayLiteralTraceExactOutcomeSpec nested.toExpressionTraceExactOutcomeSpec).toTraceExactOutcomeSpec
  | lambda => exact lambdaExpressionTraceExactOutcomeSpec blocks
  | final =>
      refine {
        successResultUnique := ?_
        rejectResultUnique := ExpressionAtomDispatchFinalTraceRejects.result_unique
        successRejectDisjoint := ?_ }
      · intro _ _ _ _ _ _ _ impossible _
        exact False.elim impossible
      · rintro _ _ _ _ _ ⟨_, _, _, impossible⟩
        exact impossible

variable (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
  (blocks : TraceExactOutcomeSpec blockTrace blockRejects source endByte)

include nested blocks

theorem ExpressionAtomDispatchTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ExpressionAtomDispatchTraceParses nestedTrace blockTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ExpressionAtomDispatchTraceParses nestedTrace blockTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | selected branch selection raw =>
      exact (expressionAtomDispatchRawTraceExactOutcomeSpec nested blocks branch).successResultUnique
        raw (rightParsed.raw_of_selected selection)

theorem ExpressionAtomDispatchTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects
      source endByte input afterLeft leftReport leftTrace)
    (right : ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects
      source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | selected branch selection raw =>
      exact (expressionAtomDispatchRawTraceExactOutcomeSpec nested blocks branch).rejectResultUnique
        raw (right.raw_of_selected selection)

theorem ExpressionAtomDispatchTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects
      source endByte input rejected report trace) :
    ¬ ∃ value output events, ExpressionAtomDispatchTraceParses nestedTrace blockTrace source endByte
      input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | selected branch selection raw =>
      exact (expressionAtomDispatchRawTraceExactOutcomeSpec nested blocks branch).successRejectDisjoint
        raw ⟨value, output, events, parsed.raw_of_selected selection⟩

theorem expressionAtomDispatchTraceExactOutcomeSpec :
    TraceExactOutcomeSpec (ExpressionAtomDispatchTraceParses nestedTrace blockTrace)
      (ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects) source endByte where
  successResultUnique := ExpressionAtomDispatchTraceParses.result_unique nested blocks
  rejectResultUnique := ExpressionAtomDispatchTraceRejects.result_unique nested blocks
  successRejectDisjoint := ExpressionAtomDispatchTraceRejects.disjoint_success nested blocks

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionAtomLayerTraceProperties
/-! One public atom layer: prioritized raw traces followed by cursor-only
rewind/recovery. Recursive expression and block relations remain explicit;
the joint bundle still expresses only uniqueness and disjointness. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
  (nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
  (blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop)
  (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)

abbrev ExpressionAtomLayerTraceParses :=
  ExpressionAtomTraceParses (ExpressionAtomDispatchTraceParses nestedTrace blockTrace)
    (ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects)

abbrev ExpressionAtomLayerTraceRejects :=
  ExpressionAtomTraceRejects (ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects)

variable {nestedTrace nestedRejects blockTrace blockRejects}

theorem expressionAtomLayerTraceExactOutcomeSpec {source : SourceId} {endByte : Nat}
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    (blocks : TraceExactOutcomeSpec blockTrace blockRejects source endByte) :
    TraceExactOutcomeSpec (ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects)
      (ExpressionAtomLayerTraceRejects nestedTrace nestedRejects blockRejects) source endByte :=
  expressionAtomTraceExactOutcomeSpec (expressionAtomDispatchTraceExactOutcomeSpec nested blocks)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionPostfixLayerTraceProperties
/-! A selected/recovering atom followed by its maximal postfix tail, leaving
only nested-expression and block relations abstract. This is a one-layer
independent relation, not a recursive least closure or existence theorem. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
  (nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
  (blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop)
  (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)

abbrev ExpressionPostfixLayerTraceParses :=
  ExpressionPostfixTraceParses (ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects)
    nestedTrace

abbrev ExpressionPostfixLayerTraceRejects :=
  ExpressionPostfixTraceRejects (ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects)
    nestedTrace (ExpressionAtomLayerTraceRejects nestedTrace nestedRejects blockRejects) nestedRejects

variable {nestedTrace nestedRejects blockTrace blockRejects}

theorem expressionPostfixLayerTraceExactOutcomeSpec {source : SourceId} {endByte : Nat}
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    (blocks : TraceExactOutcomeSpec blockTrace blockRejects source endByte) :
    TraceExactOutcomeSpec (ExpressionPostfixLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects)
      (ExpressionPostfixLayerTraceRejects nestedTrace nestedRejects blockTrace blockRejects) source endByte :=
  expressionPostfixTraceExactOutcomeSpec (expressionAtomLayerTraceExactOutcomeSpec nested blocks) nested

end Solcore.Syntax.DeclarativeGrammar
end
