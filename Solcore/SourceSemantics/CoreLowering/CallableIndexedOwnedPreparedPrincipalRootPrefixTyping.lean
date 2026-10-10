import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalCaptures
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeInversion

/-! The actual selected method cache and prepared bootstrap bound one emitted
lambda to its genuine globals/frame prefix. Native entry typing then loses
only its unused wrapper input suffix before the original hook and marked
parameter fold are inverted. No ordinary Header, arbitrary body bound, Site
reindexing or Source execution law is an input. Child occurrence typing and
same-Site extraction remain separate static producer obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalRootPrefixTyping
open Core Frontend SourceInference

/-- The selected method's actual compiled body has exactly its canonical
parameter/global/frame prefix. The Source selector and dictionary remain in
the independent Principal; this theorem only derives native syntax typing. -/
theorem body_native_at_prefix
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    {recipe : SourceCoreIndexedSession.Recipe}
    (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries) :
    HasType (SourceCoreLocalCell.coreContext
        (principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) ++
      CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal)
      principal.cached.compilation.body
      (LanguageResult.resultType principal.named.signature.resultType) compiled.indexed.layouts.definitions := by
  have selected : compiled.indexed.secondPass.closures[principal.cached.index]? = some
      (.lambda principal.named.signature.parameterType
        (LanguageResult.resultType principal.named.signature.resultType) principal.cached.compilation.output) := by
    simpa only [principal.cached.compilation.emitted] using principal.cached.cached
  have cachedTyped := CallableIndexedCachedNativeTyping.prepared_native_closure
    compiled.indexedPrepared member selected
    (CallableIndexedPreparedInventories.cached_global_at compiled principal.cached.selected)
  have cachedBound := RecursiveNamedCatalogPreparedInitialization.supported_cached recipeAccepted selected
  let leading : Core.Context := compiled.indexed.base.globals.map (·.referenceType) ++
    [.cell compiled.indexed.ancestry.layout.frame.type]
  have prefixed : HasType
      (leading ++ SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      (.lambda principal.named.signature.parameterType
        (LanguageResult.resultType principal.named.signature.resultType) principal.cached.compilation.output)
      principal.named.signature.functionType compiled.indexed.layouts.definitions := by
    simpa only [leading, List.append_assoc, List.cons_append, List.nil_append] using cachedTyped
  have bounded : NativeExpressionContextSupport.supported
      (.lambda principal.named.signature.parameterType
        (LanguageResult.resultType principal.named.signature.resultType) principal.cached.compilation.output)
      leading.length = true := by
    simpa only [leading, List.length_append, List.length_map, List.length_cons, List.length_nil,
      Nat.add_zero] using cachedBound
  have minimal : HasType leading
      (.lambda principal.named.signature.parameterType
        (LanguageResult.resultType principal.named.signature.resultType) principal.cached.compilation.output)
      principal.named.signature.functionType compiled.indexed.layouts.definitions := by
    simpa only [List.append_nil] using
      (NativeExpressionContextSupport.prefix_typing (targetSuffix := []) prefixed bounded)
  cases minimal with
  | lambda _ _ body =>
    simpa only [leading, CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix, List.append_assoc,
      List.cons_append] using CallableIndexedParameterNativeInversion.body_native principal.cached.compilation body

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalRootPrefixTyping
