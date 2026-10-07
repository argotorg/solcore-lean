import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSourceReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission

/-! A method's actual lambda site obtains its Source closure frame from the
original typed occurrence at the reached lexical context. The full selected
method dictionary and Source graph remain genuine; no ordinary Header or
native callable type supplies Source authority or body support. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFrames
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaGeneration CallableIndexedOwnedMethodLambdaSourceReceipts

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (site : Site compiled.indexed principal.named parameters result statements context
    principal.dictionary environment scope administrative)

/-- Static Source facts at this actual site establish its complete closure
frame. The original method certificate provides graph uniqueness, and the
same raw lambda typing determines the original monomorphic body occurrence. -/
theorem closure_frame
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      context principal.sourceBody.source)
    (covers : principal.dictionary.Covers context)
    (typed : ExpressionHasType principal.sourceBody.source context site.code.id site.code.sourceNode.type) :
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
      (closure principal.named parameters result statements context principal.dictionary environment) := by
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      context (CallableIndexedNamedGeneration.source principal.named) := by
    simpa only [principal.source_eq] using runtime
  have typed : ExpressionHasType (CallableIndexedNamedGeneration.source principal.named)
      context site.code.id site.code.sourceNode.type := by
    simpa only [principal.source_eq] using typed
  have unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named) := by
    simpa only [principal.source_eq] using source_unique principal wellFormed
  refine ⟨runtime.signatures, runtime.owner, ?_, runtime.requirements.idsUnique, covers⟩
  generalize selectedType : site.code.sourceNode.type = annotation at typed
  cases typed with
  | @intro _ _ node rawType plan contains formTyped rawEq _ _ _ =>
    have sameNode : node = site.code.sourceNode := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans site.code.sourceFound)
    subst node
    rw [site.code.sourceForm] at formTyped
    cases formTyped with
    | lambda names extended body completes =>
      have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      change parameters.map (fun binder => binder.scheme.body) = _ at bodyTypes
      exact {
        owner := runtime.owner
        closed := runtime.closed
        variables_closed := runtime.variables_closed
        residual_variables_open := runtime.residual_variables_open
        graph := runtime.graph
        requirement_ledger := runtime.requirements
        occurrence := ⟨site.code.id, site.code.sourceNode, lookupExpression?_sound site.code.sourceFound,
          site.code.sourceForm, by simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq extended] using rawEq,
          by rw [site.code.sourceForm]
             simpa only [closure, bodyTypes] using
               (ExpressionFormHasRawType.lambda names extended body completes)⟩ }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFrames
