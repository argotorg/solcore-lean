import Solcore.Test.SourceCoreCapturedAssignmentFixture
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots

/-! Original Source typing determines the lexical extension, writable captured
cell and ordered read children of the real mutable closure body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreCapturedAssignment
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ObservedFactory.previous_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.previous.id = .ok observed.shape.previous := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, observed.shape.initialRead.form, observed.shape.argumentRead.form,
    observed.shape.previousRead.form, observed.shape.initializedForm, observed.shape.assignmentForm,
    observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.previousOwner, Ne.symm observed.shape.previousDistinct,
    Ne.symm observed.shape.previousArgument, observed.shape.previousScheme, TypeSystem.Scheme.mono,
    observed.shape.previousRequirements]

theorem ObservedFactory.seed_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.binder.id = .ok observed.shape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, observed.shape.initialRead.form, observed.shape.argumentRead.form,
    observed.shape.previousRead.form, observed.shape.initializedForm, observed.shape.assignmentForm,
    observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.binderOwner, observed.shape.previousDistinct,
    observed.shape.argumentDistinct, observed.binderScheme, TypeSystem.Scheme.mono,
    observed.shape.binderRequirements]

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedBareAssignmentTree.Shape observed.row.function.typedBody
      [observed.shape.initialized.id, observed.shape.assignment.id, observed.shape.innerReturn.id] :=
  .initialized observed.shape.initializedFound observed.shape.initializedForm
    (.assign observed.shape.assignmentFound observed.shape.assignmentForm observed.shape.targetBare
      (.returnValue [] observed.shape.innerReturnFound observed.shape.innerReturnForm))

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody)
    {approved : ExpressionId → Prop}
    (initializerApproved : approved observed.shape.initialRead.node.id)
    (argumentApproved : approved observed.shape.argumentRead.node.id)
    (previousApproved : approved observed.shape.previousRead.node.id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context [observed.shape.initialized.id, observed.shape.assignment.id, observed.shape.innerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true [observed.shape.initialized.id, observed.shape.assignment.id, observed.shape.innerReturn.id]) .word := by
  have declaration := observed.previous_declaration
  have seed := observed.seed_declaration
  have mono : observed.shape.previous.scheme.quantified = [] := by rw [observed.shape.previousScheme]; rfl
  have ordinary : observed.row.function.typedBody.inputs.any
      (fun input => decide (input.id = observed.shape.previous.id)) = false := by
    simp [observed.inputs, Ne.symm observed.shape.previousDistinct]
  cases typed with
  | cons head tail =>
    cases tail with
    | cons assigned tail =>
      cases tail with
      | singleton last =>
        cases head with
        | letInitialized contains form initializer monoActual generalized extended type =>
          have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.shape.initializedFound)
          cases same
          rw [observed.shape.initializedForm] at form
          obtain ⟨sameBinder, sameInitializer⟩ := StatementForm.letDecl.inj form
          cases sameBinder
          cases Option.some.inj sameInitializer
          apply GenericImperativeMatch.Syntax.initialized observed.shape.initializedFound observed.shape.initializedForm
            declaration mono extended ordinary observed.shape.initialRead.found
            (by rw [observed.shape.initialRead.type, observed.shape.previousScheme]; rfl)
            (by simpa only [observed.shape.initialRead.type, observed.shape.previousScheme, TypeSystem.Scheme.mono] using initializer)
            initializerApproved
          cases assigned with
          | assignValue contains form typedAssignment type =>
            have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.shape.assignmentFound)
            cases same
            rw [observed.shape.assignmentForm] at form
            obtain ⟨sameAssignment, sameOperator, sameRhs⟩ := StatementForm.assignValue.inj form
            cases sameAssignment
            cases sameOperator
            cases sameRhs
            cases typedAssignment with
            | wordCompound operator _ _ _ => cases operator
            | equal target rhs requirements =>
              cases target with
              | intro writable projections targetType =>
                have rootFound : SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.resolution.target.root =
                    .ok observed.shape.binder := by rw [observed.shape.targetRoot]; exact seed
                apply GenericImperativeMatch.Syntax.assign observed.shape.assignmentFound observed.shape.assignmentForm
                · intro binder found
                  have equal := Except.ok.inj (rootFound.symm.trans found)
                  cases equal
                  rw [observed.binderScheme, observed.shape.targetBare, observed.shape.targetType]
                  exact .nil _
                · intro binder found
                  have equal := Except.ok.inj (rootFound.symm.trans found)
                  cases equal
                  rw [observed.shape.targetBare] at projections
                  cases projections
                  have word := targetType.symm.trans observed.shape.targetType
                  simpa only [word, observed.binderScheme, TypeSystem.Scheme.mono] using writable
                · simpa only [targetType] using rhs
                · exact .inl rfl
                · intro id member
                  simp only [observed.shape.targetBare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
                  cases member
                  exact ⟨argumentApproved, observed.shape.argumentRead.node, observed.shape.argumentRead.found,
                    by simpa only [← targetType, observed.shape.targetType, observed.shape.argumentRead.type] using rhs⟩
                · apply GenericImperativeMatch.Syntax.body
                  cases last with
                  | returnValue contains form expression type =>
                    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.shape.innerReturnFound)
                    cases same
                    rw [observed.shape.innerReturnForm] at form
                    cases Option.some.inj (StatementForm.returnStmt.inj form)
                    exact .returnValue [] observed.shape.innerReturnFound observed.shape.innerReturnForm type
                      observed.shape.previousRead.found observed.shape.previousRead.type
                      (by simpa only [observed.shape.previousRead.type] using expression) previousApproved
                  | _ =>
                    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.shape.innerReturnFound)
                    cases same
                    simp_all [observed.shape.innerReturnForm]
          | _ =>
            have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.shape.assignmentFound)
            cases same
            simp_all [observed.shape.assignmentForm]
        | letInitializedGeneralized contains form polymorphic _requirements _generalizes _initializer _extended _type =>
          have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.shape.initializedFound)
          cases same
          rw [observed.shape.initializedForm] at form
          obtain ⟨sameBinder, _⟩ := StatementForm.letDecl.inj form
          cases sameBinder
          exact False.elim (polymorphic mono)
        | _ =>
          have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.shape.initializedFound)
          cases same
          simp_all [observed.shape.initializedForm, observed.shape.previousScheme, TypeSystem.Scheme.mono]

theorem ObservedFactory.body_reads {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context [observed.shape.initialized.id, observed.shape.assignment.id, observed.shape.innerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody
      (CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.Read observed.row.function.typedBody) context
      (.statements true [observed.shape.initialized.id, observed.shape.assignment.id, observed.shape.innerReturn.id]) .word :=
  observed.body_syntax unique
    ⟨_, _, _, observed.shape.initialRead.found, observed.shape.initialRead.form⟩
    ⟨_, _, _, observed.shape.argumentRead.found, observed.shape.argumentRead.form⟩
    ⟨_, _, _, observed.shape.previousRead.found, observed.shape.previousRead.form⟩ typed

end Tests.SourceCoreCapturedAssignment
