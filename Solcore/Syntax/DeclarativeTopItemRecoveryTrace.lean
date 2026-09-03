import Solcore.Syntax.DeclarativeTopItemRecoveryOutcomeGrammar

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
