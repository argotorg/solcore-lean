import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyApplications

/-! Operator obligations are private because the checked method catalog is
closed and its actual rigid replacement is the already private operand. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem formed_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceSemantics.Context} {type : Ty} (formed : TypeWellFormed context type) :
    Safe protectedVars state type := by
  apply safe_closed
  intro metavariable occurs
  have closed := StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed
  simp [closed] at occurs

/-- The executable operator-profile lookup supplies the actual trait and
method membership used to consult the catalog. -/
theorem operatorTraitPredicates_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {trait : Resolved.DeclarationId}
    {methodName : String} {operand : Ty} {parameters returns : List Ty}
    {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (operandSafe : Safe protectedVars state operand)
    (accepted : Detail.operatorTraitPredicates context trait methodName operand parameters returns =
      .ok predicates) :
    ∀ predicate ∈ predicates, PredicateSafe protectedVars state predicate := by
  cases found : context.signatures.trait? trait with
  | none => simp [Detail.operatorTraitPredicates, Detail.exactOperatorTraitMethod, found,
      bind, Except.bind] at accepted
  | some signature =>
    have signatureMember : signature ∈ context.signatures.traits := List.mem_of_find?_eq_some found
    simp only [Detail.operatorTraitPredicates, Detail.exactOperatorTraitMethod, found,
      pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
    cases methods : signature.methods.filter (fun candidate => candidate.name == methodName) with
    | nil => simp [methods] at accepted
    | cons method rest =>
      cases rest with
      | cons second tail => simp [methods] at accepted
      | nil =>
        simp only [methods] at accepted
        have methodMember : method ∈ signature.methods :=
          (List.mem_filter.mp (show method ∈ signature.methods.filter
            (fun candidate => candidate.name == methodName) by rw [methods]; simp)).1
        split at accepted
        · split at accepted
          · simp only [Except.ok.injEq] at accepted
            subst predicates
            intro predicate member
            rcases List.mem_cons.mp member with rfl | member
            · intro type member
              have same : type = operand := by simpa using member
              exact same ▸ operandSafe
            · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
              have formed := ((catalog.traits_semantic signature signatureMember).methods method methodMember).predicates
                original originalMember
              have range : ∀ parameter replacement, (parameter,replacement) ∈ signature.parameters.zip [operand] →
                  Safe protectedVars state replacement := by
                intro parameter replacement member
                have same : replacement = operand := by simpa using (List.of_mem_zip member).2
                exact same ▸ operandSafe
              intro type member
              rcases List.mem_cons.mp member with rfl | member
              · exact safe_parameterApply range (formed_private formed.subject)
              · obtain ⟨originalType, originalTypeMember, rfl⟩ := List.mem_map.mp member
                exact safe_parameterApply range (formed_private (formed.arguments _ originalTypeMember))
          · simp [throw] at accepted
        · simp [throw] at accepted

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

private theorem finishOperator_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {dispatch : Detail.OperatorDispatch}
    {operand builtin builtinResult resultType : Ty} {parameterTypes : List Ty}
    {hasOpenLiteralOperand : Bool} {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (operandSafe : Safe protectedVars state operand)
    (builtinSafe : Safe protectedVars state builtinResult)
    (resultSafe : Safe protectedVars state resultType)
    (live : LiveBindersSafe protectedVars state)
    (accepted : finishOperator context dispatch operand builtin builtinResult resultType
      parameterTypes hasOpenLiteralOperand state = .ok result) :
    SafeTransport protectedVars state result.state ∧
    Safe protectedVars result.state result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  unfold finishOperator at accepted
  split at accepted
  · cases Except.ok.inj accepted
    exact ⟨.refl _ _, builtinSafe, live, fun _ member fresh => (fresh member).elim⟩
  · cases dispatch with
    | function name =>
      simp only at accepted
      split at accepted
      · cases Except.ok.inj accepted
        exact ⟨.refl _ _, resultSafe, live, fun _ member fresh => (fresh member).elim⟩
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
            exact ⟨.refl _ _, resultSafe, live, fun _ member fresh => (fresh member).elim⟩
          · cases accepted
        | some trait =>
          simp only [traitResult, bind, Except.bind] at accepted
          cases predicatesResult : Detail.operatorTraitPredicates context trait methodName operand parameterTypes [resultType] with
          | error error => simp [predicatesResult] at accepted
          | ok predicates =>
            simp only [predicatesResult, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
            cases accepted
            have transport : SafeTransport protectedVars state (state.addRequirementsWithIds predicates).2 :=
              .of_substitution_eq (congrArg InferState.substitution (requirementBatch_inference _ _))
            refine ⟨transport, transport _ resultSafe,
              live.transport (requirementBatch_binders _ _) transport, ?_⟩
            intro row member fresh
            rcases requirementBatch_row_origin _ _ member with old | issued
            · exact (fresh old).elim
            · intro type typeMember
              exact transport _ (operatorTraitPredicates_private catalog operandSafe predicatesResult
                row.predicate issued type typeMember)


private abbrev finishUnary (context : SourceInference.Context) (operator : Syntax.UnaryOp)
    (operandType : Ty) (hasOpenLiteralOperand : Bool) (state : State) :=
  let operand := state.resolve operandType
  let builtin := match operator with | .logicalNot => Ty.bool | .bitNot => Ty.word
  finishOperator context (Detail.unaryOperatorDispatch operator) operand builtin builtin
    (if operator == Syntax.UnaryOp.logicalNot then .bool else operand) [operand] hasOpenLiteralOperand state

private abbrev finishBinary (context : SourceInference.Context) (operator : Syntax.BinaryOp)
    (operandType : Ty) (hasOpenLiteralOperand : Bool) (state : State) :=
  let operand := state.resolve operandType
  let builtin := Detail.binaryBuiltinType operator
  finishOperator context (Detail.binaryOperatorDispatch operator) operand builtin
    (if Detail.binaryResultIsBool operator then .bool else builtin)
    (if Detail.binaryResultIsBool operator then .bool else operand)
    [operand,operand] hasOpenLiteralOperand state

private theorem bool_private (protectedVars : List TypeVarId) (state : State) :
    Safe protectedVars state Ty.bool := safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.bool, Ty.freeVariables])

private theorem finishUnary_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {openLiteral : Bool} {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady) (operandSafe : Safe protectedVars state operandType)
    (live : LiveBindersSafe protectedVars state)
    (accepted : finishUnary context operator operandType openLiteral state = .ok result) :
    SafeTransport protectedVars state result.state ∧ Safe protectedVars result.state result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  have resolvedSafe := safe_resolved ready operandSafe
  apply finishOperator_private catalog resolvedSafe _ _ live accepted
  · cases operator <;> exact safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.bool, Ty.word, Ty.freeVariables])
  · split
    · exact bool_private _ _
    · exact resolvedSafe

private theorem finishBinary_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.BinaryOp} {operandType : Ty}
    {openLiteral : Bool} {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady) (operandSafe : Safe protectedVars state operandType)
    (live : LiveBindersSafe protectedVars state)
    (accepted : finishBinary context operator operandType openLiteral state = .ok result) :
    SafeTransport protectedVars state result.state ∧ Safe protectedVars result.state result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  have resolvedSafe := safe_resolved ready operandSafe
  apply finishOperator_private catalog resolvedSafe _ _ live accepted
  · split
    · exact bool_private _ _
    · cases operator <;> exact safe_closed _ _ (by simp [Detail.binaryBuiltinType, Ty.VariablesBelow, Ty.bool, Ty.word, Ty.freeVariables])
  · split
    · exact bool_private _ _
    · exact resolvedSafe

private theorem unify_requirements {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    after.requirements = before.requirements := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] at accepted
    cases accepted
    rfl

/-- Unary inference protects its operand through the optional real expected
unification and the selected builtin or trait method result. -/
theorem inferUnaryOperator_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures) (ready : state.InferenceReady)
    (operandBelow : operandType.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (operandSafe : Safe protectedVars state operandType)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    SafeTransport protectedVars state result.state ∧ Safe protectedVars result.state result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  let openLiteral := Detail.isOpenIntegerLiteralTarget state integerLiterals operandType
  unfold Detail.inferUnaryOperator at accepted
  cases expected with
  | none =>
    simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    exact finishUnary_private catalog ready operandSafe live accepted
  | some expectedType =>
    have expectedBelow := expectedBelow expectedType (by simp)
    have expectedSafe := expectedSafe expectedType (by simp)
    cases skip : (operator == Syntax.UnaryOp.logicalNot ||
        (state.resolve operandType).freeVariables.isEmpty || !openLiteral) with
    | true =>
      simp only [openLiteral, skip, if_true, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      exact finishUnary_private catalog ready operandSafe live accepted
    | false =>
      simp only [openLiteral, skip, Bool.false_eq_true, if_false] at accepted
      cases unified : Detail.unify state (state.resolve operandType) expectedType with
      | error error => simp [unified, bind, Except.bind] at accepted
      | ok fitted =>
        simp only [unified, bind, Except.bind] at accepted
        have fitReady := Detail.unify_preserves_inferenceReady ready
          (ready.solved.variablesBelow_apply operandBelow) expectedBelow unified
        have fitPrivacy := ProtectedVariables.unify (safe_resolved ready operandSafe) expectedSafe unified
        have fitLive := live.unify (safe_resolved ready operandSafe) expectedSafe unified
        have tail := finishUnary_private catalog fitReady (fitPrivacy _ operandSafe) fitLive accepted
        refine ⟨fitPrivacy.trans tail.1, tail.2.1, tail.2.2.1, ?_⟩
        intro row member fresh
        apply tail.2.2.2 row member
        simpa only [unify_requirements unified] using fresh


private theorem prepend_unify {protectedVars : List TypeVarId} {before after : State}
    {left right : Ty} {result : Detail.OperatorInferenceResult}
    (leftSafe : Safe protectedVars before left) (rightSafe : Safe protectedVars before right)
    (unified : Detail.unify before left right = .ok after)
    (tail : SafeTransport protectedVars after result.state ∧ Safe protectedVars result.state result.type ∧
      LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ after.requirements →
        PredicateSafe protectedVars result.state row.predicate) :
    SafeTransport protectedVars before result.state ∧ Safe protectedVars result.state result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ before.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  refine ⟨(ProtectedVariables.unify leftSafe rightSafe unified).trans tail.1,
    tail.2.1, tail.2.2.1, ?_⟩
  intro row member fresh
  apply tail.2.2.2 row member
  simpa only [unify_requirements unified] using fresh

/-- Binary inference follows both actual unifications before selecting its
builtin result or cataloged method obligations. -/
theorem inferBinaryOperator_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures) (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (leftSafe : Safe protectedVars state left) (rightSafe : Safe protectedVars state right)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    SafeTransport protectedVars state result.state ∧ Safe protectedVars result.state result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  let openLiteral := Detail.isOpenIntegerLiteralTarget state integerLiterals left ||
    Detail.isOpenIntegerLiteralTarget state integerLiterals right
  unfold Detail.inferBinaryOperator at accepted
  cases unified : Detail.unify state left right with
  | error error => simp [unified, bind, Except.bind] at accepted
  | ok unifiedState =>
    simp only [unified, bind, Except.bind] at accepted
    have unifiedReady := Detail.unify_preserves_inferenceReady ready leftBelow rightBelow unified
    have unifiedProgress := Detail.unify_inferenceProgress ready.solved leftBelow rightBelow unified
    have unifiedPrivacy := ProtectedVariables.unify leftSafe rightSafe unified
    have operandSafe := unifiedPrivacy _ leftSafe
    have unifiedLive := live.unify leftSafe rightSafe unified
    apply prepend_unify leftSafe rightSafe unified
    cases expected with
    | none =>
      simp only [pure, Pure.pure, Except.pure] at accepted
      exact finishBinary_private catalog unifiedReady operandSafe unifiedLive accepted
    | some expectedType =>
      have expectedBelow := (expectedBelow expectedType (by simp)).weaken unifiedProgress.next_le
      have expectedSafe := unifiedPrivacy _ (expectedSafe expectedType (by simp))
      cases skip : (Detail.binaryResultIsBool operator ||
          (unifiedState.resolve left).freeVariables.isEmpty || !openLiteral) with
      | true =>
        simp only [openLiteral, skip, if_true, pure, Pure.pure, Except.pure] at accepted
        exact finishBinary_private catalog unifiedReady operandSafe unifiedLive accepted
      | false =>
        simp only [openLiteral, skip, Bool.false_eq_true, if_false] at accepted
        cases fitted : Detail.unify unifiedState (unifiedState.resolve left) expectedType with
        | error error => simp [fitted] at accepted
        | ok fittedState =>
          simp only [fitted] at accepted
          have operandBelow := unifiedReady.solved.variablesBelow_apply
            (leftBelow.weaken unifiedProgress.next_le)
          have fittedReady := Detail.unify_preserves_inferenceReady unifiedReady operandBelow expectedBelow fitted
          have resolvedSafe := safe_resolved unifiedReady operandSafe
          have fittedPrivacy := ProtectedVariables.unify resolvedSafe expectedSafe fitted
          have fittedLive := unifiedLive.unify resolvedSafe expectedSafe fitted
          exact prepend_unify resolvedSafe expectedSafe fitted
            (finishBinary_private catalog fittedReady (fittedPrivacy _ operandSafe) fittedLive accepted)

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
