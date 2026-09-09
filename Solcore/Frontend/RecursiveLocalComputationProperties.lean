import Solcore.Frontend.RecursiveLocalComputationTypingProperties
import Solcore.Frontend.DirectWordBinaryProperties

/-! Exact static provenance for recursive calls, groups, unary/binary operations and conditionals.
Pure overlap is reconciled internally without restricting source or callers. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem short_circuit_children {table : LocalNameTable} {context : Resolved.Context}
    {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty} (isOr : Bool) :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .binary left ⟨operatorSpan, if isOr then .logicalOr else .logicalAnd⟩ right⟩ = some (core, type) ↔
      ∃ leftCore rightCore,
        elaborateRecursiveLocalComputation? table context left = some (leftCore, .bool) ∧
        elaborateRecursiveLocalComputation? table context right = some (rightCore, .bool) ∧
        core = (if isOr then .ifE leftCore (.bool true) rightCore else .ifE leftCore rightCore (.bool false)) ∧
        type = .bool := by
  cases isOr <;> simp only [Bool.false_eq_true, ↓reduceIte, elaborateRecursiveLocalComputation?,
    bind, Option.bind_eq_some_iff] <;> constructor
  all_goals first
    | rintro ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩
      exact ⟨_, leftAccepted, _, rightAccepted, by simp⟩
    | rintro ⟨⟨leftCore, leftType⟩, leftAccepted, ⟨rightCore, rightType⟩, rightAccepted, result⟩
      dsimp only at result
      split at result
      next same => cases result; exact ⟨leftCore, rightCore, same.1 ▸ leftAccepted, same.2 ▸ rightAccepted, rfl, rfl⟩
      next => cases result

private theorem unary_children {table : LocalNameTable} {context : Resolved.Context}
    {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
    {sourceOp : Syntax.UnaryOp} {op : Core.UnaryOp} {core : Core.Expr} {type : Core.Ty}
    (operator : sourceOp = .logicalNot ∧ op = .boolNot ∨ sourceOp = .bitNot ∧ op = .wordNot) :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .unary ⟨operatorSpan, sourceOp⟩ operand⟩ = some (core, type) ↔
      ∃ operandCore,
        elaborateRecursiveLocalComputation? table context operand = some (operandCore, op.operandType) ∧
        core = .unary op operandCore ∧ type = op.resultType := by
  rcases operator with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff] <;> constructor
  all_goals first
    | rintro ⟨operandCore, child, rfl, rfl⟩
      exact ⟨_, child, by simp [Core.UnaryOp.operandType, Core.UnaryOp.resultType]⟩
    | rintro ⟨⟨operandCore, operandType⟩, child, result⟩
      dsimp only at result
      split at result
      next same => cases result; cases same; exact ⟨operandCore, child, rfl, rfl⟩
      next => cases result

private theorem binary_children {table : LocalNameTable} {context : Resolved.Context}
    {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
    {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} {core : Core.Expr} {type : Core.Ty}
    (operator : DirectWordBinary sourceOp op) :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ = some (core, type) ↔
      ∃ leftCore rightCore,
        elaborateRecursiveLocalComputation? table context left = some (leftCore, op.leftType) ∧
        elaborateRecursiveLocalComputation? table context right = some (rightCore, op.rightType) ∧
        core = .binary op leftCore rightCore ∧ type = op.resultType := by
  have notAnd : sourceOp ≠ .logicalAnd := by cases operator <;> intro same <;> cases same
  have notOr : sourceOp ≠ .logicalOr := by cases operator <;> intro same <;> cases same
  simp only [elaborateRecursiveLocalComputation?, directWordBinary?_iff.mpr operator,
    bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨leftCore, leftType⟩, leftAccepted, ⟨rightCore, rightType⟩, rightAccepted, result⟩
    dsimp only at result
    split at result
    next same =>
      cases result
      exact ⟨leftCore, rightCore, same.1 ▸ leftAccepted, same.2 ▸ rightAccepted, rfl, rfl⟩
    next => cases result
  · rintro ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩
    exact ⟨(leftCore, op.leftType), leftAccepted, (rightCore, op.rightType), rightAccepted, by simp⟩

private theorem conditional_children {table : LocalNameTable} {context : Resolved.Context}
    {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty} :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ = some (core, type) ↔
      ∃ conditionCore thenCore elseCore,
        elaborateRecursiveLocalComputation? table context condition = some (conditionCore, .bool) ∧
        elaborateRecursiveLocalComputation? table context thenBranch = some (thenCore, type) ∧
        elaborateRecursiveLocalComputation? table context elseBranch = some (elseCore, type) ∧
        core = .ifE conditionCore thenCore elseCore := by
  simp only [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨conditionCore, conditionType⟩, conditionAccepted, ⟨thenCore, thenType⟩, thenAccepted,
      ⟨elseCore, elseType⟩, elseAccepted, result⟩
    dsimp only at result
    split at result
    next same =>
      cases result
      exact ⟨conditionCore, thenCore, elseCore, same.1 ▸ conditionAccepted,
        thenAccepted, same.2 ▸ elseAccepted, rfl⟩
    next => cases result
  · rintro ⟨conditionCore, thenCore, elseCore, conditionAccepted, thenAccepted, elseAccepted, rfl⟩
    exact ⟨(conditionCore, .bool), conditionAccepted, (thenCore, type), thenAccepted,
      (elseCore, type), elseAccepted, by simp⟩

private theorem pure_complete {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr} {core : Core.Expr} {type : Core.Ty}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers context.ids resolved core)
    (typing : Resolved.HasType context resolved type) :
    elaborateRecursiveLocalComputation? table context source = some (core, type) := by
  induction resolution generalizing core type with
  | group _ ih => simpa only [elaborateRecursiveLocalComputation?] using ih lowered typing
  | logicalNot _ ih | bitNot _ ih =>
      cases lowered with
      | unary childLowered =>
          cases typing with
          | unary childTyped => simp [elaborateRecursiveLocalComputation?, ih childLowered childTyped,
              Core.UnaryOp.operandType, Core.UnaryOp.resultType]
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases lowered with
      | ifE conditionLowered thenLowered elseLowered =>
          cases typing with
          | ifE conditionTyped thenTyped elseTyped =>
              exact conditional_children.mpr ⟨_, _, _, conditionIH conditionLowered conditionTyped,
                thenIH thenLowered thenTyped, elseIH elseLowered elseTyped, rfl⟩
  | logicalAnd _ _ leftIH rightIH =>
      cases lowered with
      | ifE leftLowered rightLowered constant =>
          cases constant; cases typing with
          | ifE leftTyped rightTyped constant =>
              cases constant
              exact (short_circuit_children false).mpr ⟨_, _, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped, rfl, rfl⟩
  | logicalOr _ _ leftIH rightIH =>
      cases lowered with
      | ifE leftLowered constant rightLowered =>
          cases constant; cases typing with
          | ifE leftTyped constant rightTyped =>
              cases constant
              exact (short_circuit_children true).mpr ⟨_, _, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped, rfl, rfl⟩
  | add _ _ leftIH rightIH | subtract _ _ leftIH rightIH
  | multiply _ _ leftIH rightIH | divide _ _ leftIH rightIH
  | modulo _ _ leftIH rightIH | greater _ _ leftIH rightIH | equal _ _ leftIH rightIH
  | bitAnd _ _ leftIH rightIH | bitOr _ _ leftIH rightIH | bitXor _ _ leftIH rightIH =>
      cases lowered with
      | binary leftLowered rightLowered =>
          cases typing with
          | binary leftTyped rightTyped =>
              rw [elaborateRecursiveLocalComputation?] <;>
                simp [directWordBinary?, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped]
  | _ =>
      rw [elaborateRecursiveLocalComputation?] <;> try simp [directWordBinary?]
      exact elaborateLocalExpression?_complete (by constructor <;> assumption) lowered typing

private theorem application_children {table : LocalNameTable} {context : Resolved.Context}
    {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty} :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ = some (core, type) ↔
      ∃ functionCore argumentCore parameterType,
        elaborateRecursiveLocalComputation? table context callee =
          some (functionCore, .function parameterType type) ∧
        elaborateRecursiveLocalComputation? table context argument = some (argumentCore, parameterType) ∧
        core = .apply functionCore argumentCore := by
  simp only [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨functionCore, functionType⟩, functionAccepted,
      ⟨argumentCore, argumentType⟩, argumentAccepted, result⟩
    cases functionType <;> try cases result
    case function parameterType resultType =>
      dsimp only at result
      split at result
      next same =>
        cases result
        exact ⟨functionCore, argumentCore, parameterType, functionAccepted, same ▸ argumentAccepted, rfl⟩
      next => cases result
  · rintro ⟨functionCore, argumentCore, parameterType, functionAccepted, argumentAccepted, rfl⟩
    exact ⟨(functionCore, .function parameterType type), functionAccepted,
      (argumentCore, parameterType), argumentAccepted, by simp⟩

private theorem complete {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type) :
    elaborateRecursiveLocalComputation? table context source = some (core, type) := by
  induction elaboration with
  | pure resolution lowered typing =>
      exact pure_complete resolution lowered typing
  | group _ ih => simpa only [elaborateRecursiveLocalComputation?] using ih
  | application _ _ functionIH argumentIH =>
      exact application_children.mpr ⟨_, _, _, functionIH, argumentIH, rfl⟩
  | binary operator _ _ leftIH rightIH =>
      exact (binary_children operator).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | conditional _ _ _ conditionIH thenIH elseIH =>
      exact conditional_children.mpr ⟨_, _, _, conditionIH, thenIH, elseIH, rfl⟩
  | logicalNot _ ih => exact (unary_children (Or.inl ⟨rfl, rfl⟩)).mpr ⟨_, ih, rfl, rfl⟩
  | bitNot _ ih => exact (unary_children (Or.inr ⟨rfl, rfl⟩)).mpr ⟨_, ih, rfl, rfl⟩
  | logicalAnd _ _ leftIH rightIH => exact (short_circuit_children false).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | logicalOr _ _ leftIH rightIH => exact (short_circuit_children true).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩

private theorem pure_sound {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type)) :
    RecursiveLocalComputationElaborates table context source core type := by
  obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound accepted
  exact .pure resolution lowered typing

private theorem sound {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateRecursiveLocalComputation? table context source = some (core, type)) :
    RecursiveLocalComputationElaborates table context source core type := by
  cases source with
  | mk span payload =>
      cases payload
      case group inner =>
        exact .group (sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted))
      case unary operator operand =>
        cases operator with
        | mk operatorSpan sourceOp =>
            cases sourceOp
            case logicalNot =>
              obtain ⟨childCore, child, rfl, rfl⟩ := (unary_children (Or.inl ⟨rfl, rfl⟩)).mp accepted
              exact .logicalNot (sound child)
            case bitNot =>
              obtain ⟨childCore, child, rfl, rfl⟩ := (unary_children (Or.inr ⟨rfl, rfl⟩)).mp accepted
              exact .bitNot (sound child)
      case conditional condition question thenBranch colon elseBranch =>
        obtain ⟨conditionCore, thenCore, elseCore, conditionAccepted, thenAccepted, elseAccepted, rfl⟩ :=
          conditional_children.mp accepted
        exact .conditional (sound conditionAccepted) (sound thenAccepted) (sound elseAccepted)
      case binary left operator right =>
        cases operator with
        | mk operatorSpan sourceOp =>
            by_cases isAnd : sourceOp = .logicalAnd
            · subst sourceOp
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (short_circuit_children false).mp accepted
              exact .logicalAnd (sound leftAccepted) (sound rightAccepted)
            by_cases isOr : sourceOp = .logicalOr
            · subst sourceOp
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (short_circuit_children true).mp accepted
              exact .logicalOr (sound leftAccepted) (sound rightAccepted)
            cases mapped : directWordBinary? sourceOp with
            | none => exact pure_sound (by cases sourceOp <;> simp_all [elaborateRecursiveLocalComputation?, directWordBinary?])
            | some op =>
                have operator := directWordBinary?_iff.mp mapped
                obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ :=
                  (binary_children operator).mp accepted
                exact .binary operator (sound leftAccepted) (sound rightAccepted)
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan arguments =>
            cases arguments with
            | nil => exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
            | cons argument rest =>
                cases rest with
                | nil =>
                    obtain ⟨functionCore, argumentCore, parameterType, functionAccepted, argumentAccepted, rfl⟩ :=
                      application_children.mp accepted
                    exact .application (sound functionAccepted) (sound argumentAccepted)
                | cons _ _ => exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
      all_goals exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
termination_by sizeOf source

theorem elaborateRecursiveLocalComputation?_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateRecursiveLocalComputation? table context source = some (core, type) ↔
      RecursiveLocalComputationElaborates table context source core type :=
  ⟨sound, complete⟩

end Solcore.Frontend
