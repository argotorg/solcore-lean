import Solcore.SourceSemantics.CoreLowering.GenericMatchMeaning

/-! The source-ordered selection can drive the same certified Core branch
prefix. These lemmas provide the forward direction without assuming global
source determinism or changing how malformed patterns are specified. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchSelection
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues DataPatternLeaves
open DataPatternExecution DataPatternSuccess DataPatternTypedValues DataMatchCertificates DataMatchDecision

private theorem pattern_success {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : DataPatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context) {sourceValue : Dynamic.Value} {value : Value}
    {bindings : List (TypedBinder × Dynamic.Value)}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings) :
    ∃ values, DataPatternBindings.BindingsRep compilation.checked.catalog compilation.signatures compiled.bindings bindings values ∧
      MatcherRuns compiled value values := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context valid.signatures _ _ _ root
  have originalMatch := matched
  cases matched with
  | intro matchedSource instructionMatch =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep matchedSource
    subst arityEq
    subst instructions
    obtain ⟨values, _, bindingsRep, evaluates⟩ := Tree.success tree sourceValue value bindings [] represented.erase instructionMatch
    exact ⟨values, DataPatternBindings.Certificate.bindings_typed certificate valid.signatures represented originalMatch bindingsRep, evaluates⟩

/-- An independently selected source arm has the matching certified Core
prefix, with its exact source binder values authenticated. -/
theorem Arms.selects {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (valid : ContextValid compilation context) {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value)
    {selection : Dynamic.MatchCaseSelection}
    (selected : Dynamic.MatchCasesSelect context sourceValue cases fallback selection) :
    Decision compilation context scope bodyCertificate resultType sourceValue value cases arms fallback fallbackCode selection := by
  induction selected generalizing arms with
  | head matched =>
    cases certificates with
    | cons certificate typed bodyCertified tail =>
      obtain ⟨values, related, runs⟩ := pattern_success certificate valid represented matched
      exact .head matched related runs bodyCertified
  | tail notMatched selected ih =>
    cases certificates with
    | cons certificate typed bodyCertified tail =>
      cases pattern_decides certificate valid represented with
      | inl found =>
        obtain ⟨_, _, matched, _⟩ := found
        exact False.elim (notMatched.excludes matched)
      | inr failed => exact .tail notMatched failed.2 (ih tail fallbackCertificate)
  | default => cases certificates; cases fallbackCertificate with
    | some certified => exact .default certified
  | noBranch => cases certificates; cases fallbackCertificate; exact .noBranch

private theorem pattern_not_malformed {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : DataPatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context) : ¬ Dynamic.PatternMalformed context pattern := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context valid.signatures _ _ _ root
  intro malformed
  cases malformed with
  | source absent => exact absent arity sourceRep
  | «prefix» other absent =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep other
    subst arityEq
    subst instructions
    exact absent (DataPatternCertificates.Tree.skips tree)

theorem Arms.not_pattern_fault {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (valid : ContextValid compilation context) (value : Dynamic.Value) :
    ¬ Dynamic.MatchCasesPatternFault context value cases := by
  induction certificates with
  | nil => intro fault; cases fault
  | cons certificate typed body tail ih =>
    intro fault
    cases fault with
    | head malformed => exact pattern_not_malformed certificate valid malformed
    | tail _ next => exact ih next

end Solcore.SourceSemantics.CoreLowering.GenericMatchSelection
