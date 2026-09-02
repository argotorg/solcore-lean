import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent broad ordinary outcomes for import terminators.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact finite token kinds recognized as top-item starts by import recovery. -/
def ImportTerminatorTopItemStartKinds : List TokenKind := [
  .keyword .importKw,
  .keyword .exportKw,
  .keyword .pragmaKw,
  .keyword .typeKw,
  .keyword .contractKw,
  .keyword .functionKw,
  .keyword .defaultKw,
  .symbol .hash,
  .identifier ContextualKeyword.enum.spelling,
  .identifier ContextualKeyword.trait.spelling,
  .identifier ContextualKeyword.impl.spelling
]

/-- A token recognized as a top-item start occurs at the current cursor. -/
def ImportTerminatorTopItemStartsAt (input : Remainder) : Prop :=
  ∃ kind ∈ ImportTerminatorTopItemStartKinds, ∃ span,
    TokenAt input.tokens input.endIndex input.cursor { span, value := kind }

/-- Exact prioritized success of an import terminator.  A semicolon consumes
one token and returns its span.  Otherwise a top-item start recovers without
consuming input and returns the fixed preceding span. -/
inductive ImportTerminatorOrdinaryParses (lastSpan : SourceSpan) :
    Remainder → SourceSpan → Remainder → Prop where
  | semicolon {input output : Remainder} (semicolonSpan : SourceSpan)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) input
        semicolonSpan output) :
      ImportTerminatorOrdinaryParses lastSpan input semicolonSpan output
  | recovered {input : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (topItemStarts : ImportTerminatorTopItemStartsAt input) :
      ImportTerminatorOrdinaryParses lastSpan input lastSpan input

/-- Exact nonconsuming rejection when neither a semicolon nor a top-item start
occurs at the current cursor. -/
inductive ImportTerminatorRejects : Remainder → Remainder → Prop where
  | missing {input : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (topItemStartAbsent : TopItemKindsAbsentAt input
        ImportTerminatorTopItemStartKinds) :
      ImportTerminatorRejects input input

end Solcore.Syntax.DeclarativeGrammar
