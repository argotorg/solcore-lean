import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaScalarNativeTyping

/-! The actual typed contracted lambda already contains its original body's
native typing. Snapshot, frame, manifest and parameter wrappers are inverted
through their literal accepted compiler receipts. Only unused syntax binders
are removed. Source typing, body syntax, selected authority and execution are
independent; no expected body typing premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaBodyNativeInversion
open Core Frontend SourceInference
open CallableIndexedLambdaValues

/-- Remove the one unused packed argument after the real parameter references.
The arbitrary prefix remains exact; this is static typing pullback only. -/
theorem remove_prefix_slot {definitions : DataEnvironment}
    (front suffix : Core.Context) (inserted : Ty) {expression : Expr} {result : Ty}
    (typed : HasType (front ++ inserted :: suffix)
      (expression.weakenAt front.length) result definitions) :
    HasType (front ++ suffix) expression result definitions := by
  have back : TypedLexicalWhile.Native.PullsBack (Renaming.insertion front.length)
      (front ++ suffix) (front ++ inserted :: suffix) := by
    clear typed
    induction front with
    | nil =>
      intro index type found
      simpa [Renaming.insertion] using found
    | cons first rest ih =>
      simpa only [List.length_cons, List.cons_append, Renaming.lift_insertion] using ih.lift first
  rw [← Expr.rename_insertion] at typed
  exact TypedLexicalWhile.Native.typing expression back typed

/-- The real manifest hook inserts only its metadata product. Acceptance
identifies that literal wrapper; its native let body gives the same allocation. -/
theorem manifest_body {checked : SourceCoreCompatibleCatalog.Checked}
    {inventory : SourceCoreLambdaTemplates.Inventory checked}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {node : ExpressionNode} {parameter result : Ty} {body emitted : Expr}
    (accepted : SourceCoreLambdaTemplates.hook inventory owner active compilation source scope node
      parameter result body = .ok emitted)
    {definitions : DataEnvironment} {context : Core.Context}
    (typed : HasType context emitted (LanguageResult.resultType result) definitions) :
    HasType context body (LanguageResult.resultType result) definitions := by
  simp only [SourceCoreLambdaTemplates.hook, bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw] at accepted
  repeat' first | split at accepted | contradiction
  rename_i _ template selected metadata header _ fields fieldsAccepted _ checkedScope scopeChecks
  cases accepted
  cases typed with
  | letE metadataTyped bodyTyped =>
    exact TypedLexicalWhile.Native.remove_front bodyTyped

/-- The contracted carrier fixes the literal anonymous snapshot lambda.
The saved lexical frame and two frame temporaries do not alter its original
raw body code, so its typing follows without a separately typed body input. -/
theorem raw_body {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) :
    HasType (code.receipt.parameterCore :: SourceCoreLocalCell.coreContext scope ++ administrative)
      code.receipt.rawBody (LanguageResult.resultType code.receipt.resultCore) prepared.layouts.definitions := by
  have typed := code.typed
  rw [code.emitted] at typed
  cases typed with
  | inRight _ wrapped =>
    cases wrapped with
    | pair tagged contract =>
      cases tagged with
      | pair identity snapshot =>
        cases snapshot with
        | letE saved lambda =>
          cases lambda with
          | lambda parameter result native =>
            have raw := CallableIndexedParameterNativeInversion.withFrame_body native
            exact TypedLexicalWhile.Native.remove_second raw

/-- The actual allocation receipt fixes every parameter reference. The real
packed argument is the sole unused slot removed after those references. The
returned native typing has exactly the Site's canonical source body scope. -/
theorem body_native {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) :
    HasType (SourceCoreLocalCell.coreContext
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative)
      code.receipt.body (LanguageResult.resultType code.receipt.resultCore) prepared.layouts.definitions := by
  have allocated := manifest_body (code.manifest ▸ code.receipt.bodyHook) (raw_body code)
  have body := CallableIndexedParameterNativeInversion.accepted_body code.allocationError
    (CallableIndexedLambdaEntryPrefix.prefix_accepted (values := .initial checked) code) allocated
  rw [CallableIndexedParameterNativeInversion.final_context] at body
  let front := SourceCoreLocalCell.coreContext
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)))
  have length : front.length = code.receipt.loweredParameters.length := by
    simp [front, SourceCoreLocalCell.coreContext]
  have body := remove_prefix_slot
    front (SourceCoreLocalCell.coreContext scope ++ administrative) code.receipt.parameterCore
    (by simpa only [front, length, List.cons_append, List.append_assoc] using body)
  simpa only [front, SourceCoreLocalCell.coreContext, List.map_append, List.append_assoc] using body

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaBodyNativeInversion
