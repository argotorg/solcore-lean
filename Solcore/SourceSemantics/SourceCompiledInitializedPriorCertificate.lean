import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledInitializerCertificate
import Solcore.SourceSemantics.SourceCompiledInitializedPriorPrivacy

/-! The actual selected prefix supplies prior-quantifier privacy to the
initializer certificate consumer. The remaining inputs describe the exact child
and its selected-scope generalization barrier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

/-- The real prefix closes the prior blocker using the same child entry's local
alignment. The certificate uses actual whole-body predicate formation. -/
theorem InitializedPriorPrivate.certificate_of_child
    {continuation : InitializerContinuation selected source}
    (privateVars : InitializedPriorPrivate continuation)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (invariant : RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry target)
    (actual : ActualContext
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized frames target)
    (covered : ActualContext.Covers selected.body.finalized frames
      (.statement continuation.entry.allocateStatementId.1))
    (barrier : GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
      selected.body.finalized.substitution target
      (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)))
    (child :
      RecursiveExpressionInvariant
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized continuation.entry.allocateStatementId.2
        (localSchemeInitializerContext target continuation.initializerBinding.binder) →
      ActualContext
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized (frames ++ [continuation.initializerBinding])
        (localSchemeInitializerContext target continuation.initializerBinding.binder) →
      ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
        (.expression continuation.receipt.value.id) →
      ExpressionHasType selected.body.finalized.typedSource
        (localSchemeInitializerContext target continuation.initializerBinding.binder)
        continuation.receipt.value.id
        (selected.body.finalized.substitution.apply continuation.receipt.value.type)) :
    UnannotatedInitializedLetCertificate
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
      target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id := by
  exact continuation.certificate_of_child checked invariant actual covered barrier
    (privateVars.prior_blocked invariant.active.aligned) child

/-- At an actual selected top-level declaration, prior privacy and predicate
formation are generated internally. The callback is only the exact smaller child
in the scope opened by that same declaration. -/
theorem BodySelection.initializedCertificate_of_child
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ continuation : InitializerContinuation selected source,
      ∀ {target : SourceSemantics.Context} {frames : List InitializedLetBinding},
        RecursiveExpressionInvariant
          (context compiled.program.environment compiled.program.signatures
            selected.signature selected.body.declaration)
          selected.body.finalized continuation.entry target →
        ActualContext
          (context compiled.program.environment compiled.program.signatures
            selected.signature selected.body.declaration)
          selected.body.finalized frames target →
        ActualContext.Covers selected.body.finalized frames
          (.statement continuation.entry.allocateStatementId.1) →
        GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
          continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
          selected.body.finalized.substitution target
          (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)) →
        (RecursiveExpressionInvariant
            (context compiled.program.environment compiled.program.signatures
              selected.signature selected.body.declaration)
            selected.body.finalized continuation.entry.allocateStatementId.2
            (localSchemeInitializerContext target continuation.initializerBinding.binder) →
          ActualContext
            (context compiled.program.environment compiled.program.signatures
              selected.signature selected.body.declaration)
            selected.body.finalized (frames ++ [continuation.initializerBinding])
            (localSchemeInitializerContext target continuation.initializerBinding.binder) →
          ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
            (.expression continuation.receipt.value.id) →
          ExpressionHasType selected.body.finalized.typedSource
            (localSchemeInitializerContext target continuation.initializerBinding.binder)
            continuation.receipt.value.id
            (selected.body.finalized.substitution.apply continuation.receipt.value.type)) →
        UnannotatedInitializedLetCertificate
          (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
          target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id := by
  obtain ⟨continuation,privateVars⟩ := selected.initializedPriorPrivate checked position form
  refine ⟨continuation,?_⟩
  intro target frames invariant actual covered barrier child
  exact privateVars.certificate_of_child checked invariant actual covered barrier child

/-- Successful public compilation selects the same original body and finalizer
used by each conditional initializer certificate. The selected-scope barrier and
concrete child typing are the remaining semantic inputs. -/
theorem compile_initialized_certificate_of_child
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {index : Nat} {source : Syntax.Statement},
        selected.signature.source.value.body.value[index]? = some source →
        ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
          source.value = .letDecl name annotation (some initializer) →
    ∃ continuation : InitializerContinuation selected.toBodySelection source,
      ∀ {target : SourceSemantics.Context} {frames : List InitializedLetBinding},
        RecursiveExpressionInvariant
          (context compiled.program.environment compiled.program.signatures
            selected.signature selected.body.declaration)
          selected.body.finalized continuation.entry target →
        ActualContext
          (context compiled.program.environment compiled.program.signatures
            selected.signature selected.body.declaration)
          selected.body.finalized frames target →
        ActualContext.Covers selected.body.finalized frames
          (.statement continuation.entry.allocateStatementId.1) →
        GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
          continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
          selected.body.finalized.substitution target
          (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)) →
        (RecursiveExpressionInvariant
            (context compiled.program.environment compiled.program.signatures
              selected.signature selected.body.declaration)
            selected.body.finalized continuation.entry.allocateStatementId.2
            (localSchemeInitializerContext target continuation.initializerBinding.binder) →
          ActualContext
            (context compiled.program.environment compiled.program.signatures
              selected.signature selected.body.declaration)
            selected.body.finalized (frames ++ [continuation.initializerBinding])
            (localSchemeInitializerContext target continuation.initializerBinding.binder) →
          ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
            (.expression continuation.receipt.value.id) →
          ExpressionHasType selected.body.finalized.typedSource
            (localSchemeInitializerContext target continuation.initializerBinding.binder)
            continuation.receipt.value.id
            (selected.body.finalized.substitution.apply continuation.receipt.value.type)) →
        UnannotatedInitializedLetCertificate
          (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
          target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected,?_⟩
  intro index source position name annotation initializer form
  exact selected.toBodySelection.initializedCertificate_of_child
    (SourceCoreCompiler.compile_checked_source accepted) position form


theorem Selected.initializedCertificate_of_child
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ continuation : InitializerContinuation selected.toBodySelection source,
      ∀ {target : SourceSemantics.Context} {frames : List InitializedLetBinding},
        RecursiveExpressionInvariant
          (context compiled.program.environment compiled.program.signatures
            selected.signature selected.body.declaration)
          selected.body.finalized continuation.entry target →
        ActualContext
          (context compiled.program.environment compiled.program.signatures
            selected.signature selected.body.declaration)
          selected.body.finalized frames target →
        ActualContext.Covers selected.body.finalized frames
          (.statement continuation.entry.allocateStatementId.1) →
        GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
          continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
          selected.body.finalized.substitution target
          (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)) →
        (RecursiveExpressionInvariant
            (context compiled.program.environment compiled.program.signatures
              selected.signature selected.body.declaration)
            selected.body.finalized continuation.entry.allocateStatementId.2
            (localSchemeInitializerContext target continuation.initializerBinding.binder) →
          ActualContext
            (context compiled.program.environment compiled.program.signatures
              selected.signature selected.body.declaration)
            selected.body.finalized (frames ++ [continuation.initializerBinding])
            (localSchemeInitializerContext target continuation.initializerBinding.binder) →
          ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
            (.expression continuation.receipt.value.id) →
          ExpressionHasType selected.body.finalized.typedSource
            (localSchemeInitializerContext target continuation.initializerBinding.binder)
            continuation.receipt.value.id
            (selected.body.finalized.substitution.apply continuation.receipt.value.type)) →
        UnannotatedInitializedLetCertificate
          (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
          target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id :=
  selected.toBodySelection.initializedCertificate_of_child checked position form

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
