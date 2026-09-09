import Solcore.Frontend.RecursiveLocalComputationTypingProperties
import Solcore.Frontend.DirectWordBinaryProperties

/-! Exact static provenance for recursive calls, groups, tuples, operators and conditionals.
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
  cases isOr <;>
    simp [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff,
      Prod.exists, and_assoc, and_left_comm, and_comm] <;> simp only [eq_comm]

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
    simp [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff,
      Prod.exists, and_left_comm, and_comm, Core.UnaryOp.operandType, Core.UnaryOp.resultType] <;> simp only [eq_comm]

private theorem binary_children {table : LocalNameTable} {context : Resolved.Context}
    {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
    {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} {core : Core.Expr} {type : Core.Ty}
    (ordered negated : Bool) (operator :
      (DirectWordBinary sourceOp op ∧ ordered = false ∧ negated = false) ∨
      (sourceOp = .notEqual ∧ op = .wordEq ∧ ordered = false ∧ negated = true) ∨
      (sourceOp = .lessEqual ∧ op = .wordGt ∧ ordered = false ∧ negated = true) ∨
      (sourceOp = .less ∧ op = .wordGt ∧ ordered = true ∧ negated = false) ∨
      (sourceOp = .greaterEqual ∧ op = .wordGt ∧ ordered = true ∧ negated = true)) :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ = some (core, type) ↔
      ∃ leftCore rightCore,
        elaborateRecursiveLocalComputation? table context left = some (leftCore, op.leftType) ∧
        elaborateRecursiveLocalComputation? table context right = some (rightCore, op.rightType) ∧
        core = (let body := if ordered then leftCore.wordLt rightCore else .binary op leftCore rightCore
          if negated then .unary .boolNot body else body) ∧
        type = op.resultType := by
  rcases operator with ⟨direct, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  all_goals try cases direct
  all_goals simp [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff,
      Prod.exists, and_assoc, and_left_comm, and_comm, directWordBinary?, Core.BinaryOp.leftType,
    Core.BinaryOp.rightType, Core.BinaryOp.resultType] <;> simp only [eq_comm]

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
  simp [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff,
      Prod.exists, and_assoc, and_left_comm, and_comm] <;> simp only [eq_comm]

private theorem pure_complete {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr} {core : Core.Expr} {type : Core.Ty}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers context.ids resolved core)
    (typing : Resolved.HasType context resolved type) :
    elaborateRecursiveLocalComputation? table context source = some (core, type) := by
  induction resolution generalizing core type with
  | group _ ih => simpa only [elaborateRecursiveLocalComputation?] using ih lowered typing
  | pair _ _ leftIH rightIH | many _ _ leftIH rightIH =>
      cases lowered with | pair leftLowered rightLowered =>
        cases typing with | pair leftTyped rightTyped =>
          rw [elaborateRecursiveLocalComputation?]
          simp only [leftIH leftLowered leftTyped, rightIH rightLowered rightTyped, bind, Option.bind_some, pure]
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
  | notEqual _ _ leftIH rightIH | lessEqual _ _ leftIH rightIH =>
      cases lowered with | unary comparisonLowered =>
        cases comparisonLowered with | binary leftLowered rightLowered =>
          cases typing with | unary comparisonTyped =>
            cases comparisonTyped with | binary leftTyped rightTyped =>
              simp [elaborateRecursiveLocalComputation?, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped,
                Core.BinaryOp.leftType, Core.BinaryOp.rightType, Core.UnaryOp.resultType]
  | less _ _ leftIH rightIH =>
      cases lowered with | wordLt leftLowered rightLowered =>
        cases typing with | wordLt leftTyped rightTyped =>
          simp [elaborateRecursiveLocalComputation?, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped]
  | greaterEqual _ _ leftIH rightIH =>
      cases lowered with | unary comparison =>
        cases comparison with | wordLt leftLowered rightLowered =>
          cases typing with | unary comparison =>
            cases comparison with | wordLt leftTyped rightTyped =>
              simp [elaborateRecursiveLocalComputation?, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped, Core.UnaryOp.resultType]
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
      rw [elaborateRecursiveLocalComputation?] <;> try simp
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
      next same => cases result; exact ⟨functionCore, argumentCore, parameterType, functionAccepted, same ▸ argumentAccepted, rfl⟩
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
  | pair _ _ leftIH rightIH | many _ _ leftIH rightIH =>
      rw [elaborateRecursiveLocalComputation?]
      simp only [leftIH, rightIH, bind, Option.bind_some, pure]
  | application _ _ functionIH argumentIH =>
      exact application_children.mpr ⟨_, _, _, functionIH, argumentIH, rfl⟩
  | binary operator _ _ leftIH rightIH =>
      exact (binary_children false false (.inl ⟨operator, rfl, rfl⟩)).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | conditional _ _ _ conditionIH thenIH elseIH =>
      exact conditional_children.mpr ⟨_, _, _, conditionIH, thenIH, elseIH, rfl⟩
  | logicalNot _ ih => exact (unary_children (Or.inl ⟨rfl, rfl⟩)).mpr ⟨_, ih, rfl, rfl⟩
  | bitNot _ ih => exact (unary_children (Or.inr ⟨rfl, rfl⟩)).mpr ⟨_, ih, rfl, rfl⟩
  | logicalAnd _ _ leftIH rightIH => exact (short_circuit_children false).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | logicalOr _ _ leftIH rightIH => exact (short_circuit_children true).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | notEqual _ _ leftIH rightIH => exact (binary_children false true (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | lessEqual _ _ leftIH rightIH => exact (binary_children false true (.inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩)))).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | less _ _ leftIH rightIH => exact (binary_children true false (.inr (.inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))))).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | greaterEqual _ _ leftIH rightIH => exact (binary_children true true (.inr (.inr (.inr (.inr ⟨rfl, rfl, rfl, rfl⟩))))).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩

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
  cases source with | mk span payload =>
    cases payload
    case group inner =>
      exact .group (sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted))
    case tuple elements =>
      cases elements with | mk tupleSpan elements =>
        cases elements with
        | nil => exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
        | cons first rest =>
            cases rest with
            | nil => exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
            | cons second rest =>
                cases rest with
                | nil =>
                    simp only [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff, pure] at accepted
                    obtain ⟨⟨leftCore, leftType⟩, leftAccepted, ⟨rightCore, rightType⟩, rightAccepted, same⟩ := accepted
                    cases same; exact .pair (sound leftAccepted) (sound rightAccepted)
                | cons third rest =>
                    rw [elaborateRecursiveLocalComputation?] at accepted
                    simp only [bind, Option.bind_eq_some_iff, pure] at accepted
                    obtain ⟨⟨headCore, headType⟩, headAccepted, ⟨tailCore, tailType⟩, tailAccepted, same⟩ := accepted
                    cases same; exact .many (sound headAccepted) (sound tailAccepted)
    case unary operator operand =>
      cases operator with | mk operatorSpan sourceOp =>
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
      cases operator with | mk operatorSpan sourceOp =>
        cases mapped : directWordBinary? sourceOp with
        | some op =>
            have operator := directWordBinary?_iff.mp mapped
            obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ :=
              (binary_children false false (.inl ⟨operator, rfl, rfl⟩)).mp accepted
            exact .binary operator (sound leftAccepted) (sound rightAccepted)
        | none =>
            cases sourceOp <;> simp [directWordBinary?] at mapped
            case logicalAnd =>
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (short_circuit_children false).mp accepted
              exact .logicalAnd (sound leftAccepted) (sound rightAccepted)
            case logicalOr =>
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (short_circuit_children true).mp accepted
              exact .logicalOr (sound leftAccepted) (sound rightAccepted)
            case notEqual =>
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (binary_children false true (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))).mp accepted
              exact .notEqual (sound leftAccepted) (sound rightAccepted)
            case lessEqual =>
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (binary_children false true (.inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩)))).mp accepted
              exact .lessEqual (sound leftAccepted) (sound rightAccepted)
            case less =>
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (binary_children true false (.inr (.inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))))).mp accepted
              exact .less (sound leftAccepted) (sound rightAccepted)
            case greaterEqual =>
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (binary_children true true (.inr (.inr (.inr (.inr ⟨rfl, rfl, rfl, rfl⟩))))).mp accepted
              exact .greaterEqual (sound leftAccepted) (sound rightAccepted)
    case call callee arguments =>
      cases arguments with | mk argumentsSpan arguments =>
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
