import Solcore.Test.SourceCoreCapturedCopyFixture
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalLambdaBodySupport

/-! The actual Source typing provides the lexical extension and both child
judgments for the accepted initializer/return body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ObservedFactory.local_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.localBinder.id = .ok observed.localBinder := by
  have distinct : observed.binder.id ≠ observed.localBinder.id := Ne.symm observed.shape.localDistinct
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, observed.shape.initialReadForm, observed.shape.initializedForm,
    observed.readForm, observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.localOwner, distinct, observed.shape.localScheme, TypeSystem.Scheme.mono,
    observed.shape.localRequirements]

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody)
    {approved : ExpressionId → Prop}
    (initializerApproved : approved observed.shape.initialRead.id)
    (readApproved : approved observed.bodyRead.id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context [observed.shape.initialized.id, observed.innerReturn.id] final facts) :
    GenericLexicalStatements.Syntax observed.row.function.typedBody approved
      context true [observed.shape.initialized.id, observed.innerReturn.id] .word := by
  have declaration := observed.local_declaration
  have mono : observed.localBinder.scheme.quantified = [] := by rw [observed.localScheme]; rfl
  have ordinary : observed.row.function.typedBody.inputs.any
      (fun input => decide (input.id = observed.localBinder.id)) = false := by
    simp [observed.inputs, Ne.symm observed.shape.localDistinct]
  cases typed with
  | cons head tail =>
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
        apply GenericLexicalStatements.Syntax.initialized observed.shape.initializedFound observed.shape.initializedForm
          declaration mono extended ordinary observed.shape.initialReadFound
          (by rw [observed.shape.initialReadType, observed.localScheme]; rfl)
          (by simpa only [observed.shape.initialReadType, observed.localScheme, TypeSystem.Scheme.mono] using initializer)
          initializerApproved
        cases last with
        | returnValue contains form expression type =>
          have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.foundInnerReturn)
          cases same
          rw [observed.innerReturnForm] at form
          cases Option.some.inj (StatementForm.returnStmt.inj form)
          exact .returnValue [] observed.foundInnerReturn observed.innerReturnForm type
            observed.foundRead
            observed.readType
            (by simpa only [observed.readType] using expression)
            readApproved
        | _ =>
          have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.foundInnerReturn)
          cases same
          simp_all [observed.innerReturnForm]
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
        simp_all [observed.shape.initializedForm, observed.localScheme, TypeSystem.Scheme.mono]

end Tests.SourceCoreCapturedCopy
