import Solcore.Syntax.DeclarativeIsolatedBlockTraceErasureProperties
import Solcore.Syntax.DeclarativeCoreBlockIsolationOutcomeProperties

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
