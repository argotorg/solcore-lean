import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceGrammar

/-! Ordinary erasure and separately supplied carrier/progress laws. No such
law, and no diagnostic silence of the type relation, is part of the grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop}
  {source : SourceId} {endByte : Nat}

theorem OptionalLambdaReturnTypeTraceParses.ordinary
    (erases : ∀ {input type output trace},
      typeTrace source endByte input type output trace → typeOrdinary input type output)
    {input output : Remainder} {type : Option Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input type output trace) :
    OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input type output := by
  cases parsed with
  | absent absent => exact .absent absent
  | present span arrow type => exact .present span arrow (erases type)

theorem OptionalLambdaReturnTypeTraceRejects.ordinary
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (erases : ∀ {input rejected diagnostic trace},
      typeRejects source endByte input rejected diagnostic trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalLambdaReturnTypeTraceRejects typeRejects source endByte
      input rejected diagnostic trace) :
    OptionalLambdaReturnTypeRejects typeOrdinary ordinaryRejects input rejected := by
  cases rejection with
  | typeRejected span arrow type => exact .typeRejected span arrow (erases type)

theorem OptionalLambdaReturnTypeTraceParses.output_window
    (typeWindow : ∀ {input type output trace},
      typeTrace source endByte input type output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {type : Option Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input type output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | absent => exact ⟨rfl, rfl⟩
  | present span arrow type => simpa only [arrow.2] using typeWindow type

theorem OptionalLambdaReturnTypeTraceParses.cursor_le
    (typeProgress : ∀ {input type output trace},
      typeTrace source endByte input type output trace → input.cursor ≤ output.cursor)
    {input output : Remainder} {type : Option Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input type output trace) :
    input.cursor ≤ output.cursor := by
  cases parsed with
  | absent => exact Nat.le_refl _
  | present span arrow type =>
      have progress := typeProgress type
      rw [arrow.2] at progress
      exact Nat.le_trans (Nat.le_succ _) progress

theorem OptionalLambdaReturnTypeTraceParses.present_cursor_lt
    (typeProgress : ∀ {input type output trace},
      typeTrace source endByte input type output trace → input.cursor ≤ output.cursor)
    {input output : Remainder} {type : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input (some type) output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | present span arrow type =>
      have progress := typeProgress type
      rw [arrow.2] at progress
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) progress

end Solcore.Syntax.DeclarativeGrammar
