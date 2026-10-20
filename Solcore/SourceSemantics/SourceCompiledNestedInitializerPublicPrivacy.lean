import Solcore.SourceSemantics.SourceCompiledNestedInitializerFinalPrivacy

/-! Public compilation supplies the same selected checker receipt used for
the complete nested initializer privacy continuation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem

theorem compile_nested_lambda_privacy
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {outerIndex innerIndex : Nat} {outerSource innerSource : Syntax.Statement},
        selected.signature.source.value.body.value[outerIndex]? = some outerSource →
        ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
          outerSource.value = .letDecl name annotation (some initializer) →
          ∀ {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
            {returnAnnotation : Option Syntax.TypeExpr} {body : Syntax.Block},
            initializer.value = .lambda keyword parameters returnAnnotation body →
            body.value[innerIndex]? = some innerSource →
            ∀ {innerName : Syntax.Identifier} {innerAnnotation : Option Syntax.TypeExpr}
              {innerInitializer : Syntax.Expr},
              innerSource.value = .letDecl innerName innerAnnotation (some innerInitializer) →
              Nonempty (NestedInitializerFinalPrivacy selected outerSource innerSource) := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected,?_⟩
  intro outerIndex innerIndex outerSource innerSource outerPosition name annotation initializer
    outerForm keyword parameters returnAnnotation body lambdaForm innerPosition
    innerName innerAnnotation innerInitializer innerForm
  exact selected.nestedLambdaPrivacy accepted member outerPosition outerForm lambdaForm innerPosition innerForm

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
