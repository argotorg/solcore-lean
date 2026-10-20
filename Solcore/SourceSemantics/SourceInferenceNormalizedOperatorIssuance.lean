import Solcore.SourceSemantics.SourceInferenceFinalizedProducerFormation

/-! Every obligation issued by the actual unary and binary operator paths is
formed after the same final substitution, including expected-type unification. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

private theorem batch_inference (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.inference = state.inference := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate predicates ih => exact ih (state.addRequirementWithId predicate).2

private theorem batch_origin (state : State) (predicates : List ProgramPredicate)
    {row : Requirement} (member : row ∈ (state.addRequirementsWithIds predicates).2.requirements) :
    row ∈ state.requirements ∨ row.predicate ∈ predicates := by
  induction predicates generalizing state with
  | nil => exact Or.inl member
  | cons predicate predicates ih =>
    rcases ih (state.addRequirementWithId predicate).2 member with old | issued
    · rcases List.mem_append.mp old with old | new
      · exact .inl old
      · simp only [List.mem_singleton] at new
        subst row
        exact .inr (by simp)
    · exact .inr (by simp [issued])

private theorem actual_operator_predicates
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {outer : Substitution} {trait : Resolved.DeclarationId} {methodName : String}
    {operand : Ty} {parameters returns : List Ty} {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed semantic.signatures)
    (signatures : semantic.signatures = context.signatures)
    (operandFormed : TypeAdmissible semantic (outer.apply operand))
    (accepted : Detail.operatorTraitPredicates context trait methodName operand parameters returns = .ok predicates) :
    ∀ predicate ∈ predicates, PredicateAdmissible semantic
      (TypedTraitResolution.applySubstitution outer predicate) := by
  cases found : context.signatures.trait? trait with
  | none => simp [Detail.operatorTraitPredicates, Detail.exactOperatorTraitMethod, found,
      bind, Except.bind] at accepted
  | some signature =>
    exact operator_issuance_normalized (traitName := signature.name) catalog signatures (by simp [found]) operandFormed accepted

private abbrev finishOperator (context : SourceInference.Context) (dispatch : Detail.OperatorDispatch)
    (operand builtin builtinResult resultType : Ty) (parameterTypes : List Ty)
    (hasOpenLiteralOperand : Bool) (state : State) : Except Error Detail.OperatorInferenceResult :=
  if operand = builtin then
    pure {type := builtinResult, requirements := [], state}
  else
    match dispatch with
    | .function name =>
      if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand builtin operand ||
          Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand builtin operand then
        pure {type := resultType, requirements := [], state}
      else throw (.unknownVariable name)
    | .traitMethod traitName methodName => do
      match ← Detail.operatorTrait? context traitName with
      | some trait =>
        let predicates ← Detail.operatorTraitPredicates context trait methodName operand parameterTypes [resultType]
        let (requirements,state) := state.addRequirementsWithIds predicates
        pure {type := resultType, requirements, state}
      | none =>
        if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand builtin operand ||
            Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand builtin operand then
          pure {type := resultType, requirements := [], state}
        else throw (.operatorNotSupported traitName operand)

private theorem finishOperator_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    {dispatch : Detail.OperatorDispatch} {operand builtin builtinResult resultType : Ty}
    {parameterTypes : List Ty} {openLiteral : Bool} {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed semantic.signatures)
    (signatures : semantic.signatures = context.signatures)
    (operandFormed : outer.SemanticallyExtends state.inference.substitution →
      TypeAdmissible semantic (outer.apply operand))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : finishOperator context dispatch operand builtin builtinResult resultType
      parameterTypes openLiteral state = .ok result) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  unfold finishOperator at accepted
  split at accepted
  · cases Except.ok.inj accepted
    exact fun _ member fresh => (fresh member).elim
  · cases dispatch with
    | function name =>
      simp only at accepted
      split at accepted
      · cases Except.ok.inj accepted
        exact fun _ member fresh => (fresh member).elim
      · cases accepted
    | traitMethod traitName methodName =>
      cases traitResult : Detail.operatorTrait? context traitName with
      | error error => simp [traitResult, bind, Except.bind] at accepted
      | ok option =>
        cases option with
        | none =>
          simp only [traitResult, bind, Except.bind] at accepted
          split at accepted
          · cases Except.ok.inj accepted
            exact fun _ member fresh => (fresh member).elim
          · cases accepted
        | some trait =>
          simp only [traitResult, bind, Except.bind] at accepted
          cases predicatesResult : Detail.operatorTraitPredicates context trait methodName operand parameterTypes [resultType] with
          | error error => simp [predicatesResult] at accepted
          | ok predicates =>
            simp only [predicatesResult, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
            cases accepted
            have extension : outer.SemanticallyExtends state.inference.substitution := by
              simpa only [batch_inference] using continuation
            intro row member fresh
            rcases batch_origin state predicates member with old | issued
            · exact (fresh old).elim
            · exact actual_operator_predicates catalog signatures (operandFormed extension) predicatesResult
                row.predicate issued

private abbrev finishUnary (context : SourceInference.Context) (operator : Syntax.UnaryOp)
    (operandType : Ty) (openLiteral : Bool) (state : State) :=
  let operand := state.resolve operandType
  let builtin := match operator with | .logicalNot => Ty.bool | .bitNot => Ty.word
  finishOperator context (Detail.unaryOperatorDispatch operator) operand builtin builtin
    (if operator == Syntax.UnaryOp.logicalNot then .bool else operand) [operand] openLiteral state

private abbrev finishBinary (context : SourceInference.Context) (operator : Syntax.BinaryOp)
    (operandType : Ty) (openLiteral : Bool) (state : State) :=
  let operand := state.resolve operandType
  let builtin := Detail.binaryBuiltinType operator
  finishOperator context (Detail.binaryOperatorDispatch operator) operand builtin
    (if Detail.binaryResultIsBool operator then .bool else builtin)
    (if Detail.binaryResultIsBool operator then .bool else operand)
    [operand,operand] openLiteral state

private theorem unify_requirements {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) : after.requirements = before.requirements := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] at accepted
    cases accepted
    rfl

/-- The final continuation normalizes the actual operator operand after any
successful expected-type unification. No intermediate unifier range or
operator-expression typing premise is required. -/
theorem inferUnaryOperator_normalized_issuance
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    {operator : Syntax.UnaryOp} {operandType : Ty} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed semantic.signatures)
    (signatures : semantic.signatures = context.signatures)
    (operandFormed : TypeAdmissible semantic (outer.apply operandType))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have finish {before : State} {openLiteral : Bool}
      (accepted : finishUnary context operator operandType openLiteral before = .ok result) :
      ∀ row ∈ result.state.requirements, row ∉ before.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) :=
    finishOperator_formation catalog signatures
      (fun extension => (extension operandType).symm ▸ operandFormed) continuation accepted
  let openLiteral := Detail.isOpenIntegerLiteralTarget state integerLiterals operandType
  unfold Detail.inferUnaryOperator at accepted
  cases expected with
  | none =>
    simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    exact finish accepted
  | some expectedType =>
    cases skip : (operator == Syntax.UnaryOp.logicalNot ||
        (state.resolve operandType).freeVariables.isEmpty || !openLiteral) with
    | true =>
      simp only [openLiteral, skip, if_true, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      exact finish accepted
    | false =>
      simp only [openLiteral, skip, Bool.false_eq_true, if_false] at accepted
      cases unified : Detail.unify state (state.resolve operandType) expectedType with
      | error error => simp [unified, bind, Except.bind] at accepted
      | ok fitted =>
        simp only [unified, bind, Except.bind] at accepted
        simpa only [unify_requirements unified] using finish accepted

/-- Both real binary unifications precede the same actual trait issuance;
requirements are transported through their unchanged ledger fields. -/
theorem inferBinaryOperator_normalized_issuance
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    {operator : Syntax.BinaryOp} {left right : Ty} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed semantic.signatures)
    (signatures : semantic.signatures = context.signatures)
    (operandFormed : TypeAdmissible semantic (outer.apply left))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have finish {before : State} {openLiteral : Bool}
      (accepted : finishBinary context operator left openLiteral before = .ok result) :
      ∀ row ∈ result.state.requirements, row ∉ before.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) :=
    finishOperator_formation catalog signatures
      (fun extension => (extension left).symm ▸ operandFormed) continuation accepted
  let openLiteral := Detail.isOpenIntegerLiteralTarget state integerLiterals left ||
    Detail.isOpenIntegerLiteralTarget state integerLiterals right
  unfold Detail.inferBinaryOperator at accepted
  cases unified : Detail.unify state left right with
  | error error => simp [unified, bind, Except.bind] at accepted
  | ok unifiedState =>
    simp only [unified, bind, Except.bind] at accepted
    rw [← unify_requirements unified]
    cases expected with
    | none =>
      simp only [pure, Pure.pure, Except.pure] at accepted
      exact finish accepted
    | some expectedType =>
      cases skip : (Detail.binaryResultIsBool operator ||
          (unifiedState.resolve left).freeVariables.isEmpty || !openLiteral) with
      | true =>
        simp only [openLiteral, skip, if_true, pure, Pure.pure, Except.pure] at accepted
        exact finish accepted
      | false =>
        simp only [openLiteral, skip, Bool.false_eq_true, if_false] at accepted
        cases fitted : Detail.unify unifiedState (unifiedState.resolve left) expectedType with
        | error error => simp [fitted] at accepted
        | ok fittedState =>
          simp only [fitted] at accepted
          simpa only [unify_requirements fitted] using finish accepted

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
