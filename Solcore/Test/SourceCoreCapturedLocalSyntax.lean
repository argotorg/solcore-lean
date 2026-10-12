import Solcore.Test.SourceCoreCapturedLocalBodyReceipt
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree

/-! The actual Source typing provides the lexical extension and both child
judgments for the accepted initializer/return body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreCapturedLocal
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ObservedFactory.local_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.localBinder.id = .ok observed.localBinder := by
  have distinct : observed.binder.id ≠ observed.localBinder.id := Ne.symm observed.shape.localDistinct
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, observed.shape.initialReadForm, observed.shape.initializedForm,
    observed.readForm, observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.localOwner, distinct, observed.shape.localScheme, TypeSystem.Scheme.mono,
    observed.shape.localRequirements]

def childSyntax {fixture : CompiledFixture} (observed : ObservedFactory fixture) (id : ExpressionId) : Prop :=
  id = observed.shape.initialRead.id ∨ id = observed.expression.id

theorem ActualHeader.lexical_syntax {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    GenericLexicalStatements.Syntax actual.header.function.source (childSyntax observed)
      actual.header.context true actual.header.function.body actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  have source := actual.source
  have body := actual.statements
  rw [source] at typed
  rw [observed.roots] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [source, body]
  have unique : NodeOccurrencesUnique observed.row.function.typedBody := source ▸ actual.header.unique
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
          (Or.inl rfl)
        cases last with
        | returnValue contains form expression type =>
          have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.foundStatement)
          cases same
          rw [observed.returnStatement] at form
          cases Option.some.inj (StatementForm.returnStmt.inj form)
          exact .returnValue [] observed.foundStatement observed.returnStatement type
            observed.foundExpression
            (observed.shape.expressionType.trans actual.result_type.symm)
            (by simpa only [observed.shape.expressionType, actual.result_type] using expression)
            (Or.inr rfl)
        | _ =>
          have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.foundStatement)
          cases same
          simp_all [observed.returnStatement]
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

end Tests.SourceCoreCapturedLocal
