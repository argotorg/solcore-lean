import Solcore.SourceSemantics.CoreLowering.CompatibleMatchSelectionPrefix

/-! Independent source arm selection drives the actual compatible compiler's
ordered decision. Malformed-pattern exclusion is a static certificate law,
independent of scrutinee execution, body execution and heap representation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchSourceSelection
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open SourceCoreCompatibleDataMatches CompatiblePatternCertificates CompatiblePatternLeaves
open CompatiblePatternExecution CompatibleMatchCertificates CompatibleMatchDecision
variable {compilation : Compilation} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}

private theorem pattern_success_with_signatures {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (signatures : context.signatures = compilation.signatures)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty} {bindings : List (TypedBinder × Dynamic.Value)}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value payload)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings) :
    ∃ values, BindingsRep compilation.checked registry functions mapping world compiled.bindings bindings values ∧
      MatcherRuns compiled value values := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  have payloadEq : payload = compiled.type := Except.ok.inj
    (represented.projection.symm.trans (CompatiblePatternSuccess.Tree.projected tree))
  cases payloadEq
  cases matched with
  | intro spelling instructionMatch =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep spelling
    subst arityEq
    subst instructions
    obtain ⟨values, _, bindingsRep, runs⟩ := CompatiblePatternSuccess.Tree.success catalogValid extended tree
      sourceValue value bindings [] represented instructionMatch
    exact ⟨values, bindingsRep, runs⟩

private theorem pattern_success {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty} {bindings : List (TypedBinder × Dynamic.Value)}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value payload)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings) :
    ∃ values, BindingsRep compilation.checked registry functions mapping world compiled.bindings bindings values ∧
      MatcherRuns compiled value values := by
  exact pattern_success_with_signatures certificate valid.signatures catalogValid extended represented matched


/-- A source-selected arm preserves its exact source binder values and first
match order. Every matcher child is closed by the compatible pattern Tree. -/
theorem Arms.selects_with_literals {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (requirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Arms.LiteralSites literals certificates)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value payload)
    {selection : Dynamic.MatchCaseSelection}
    (selected : Dynamic.MatchCasesSelect context sourceValue cases fallback selection) :
    Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection := by
  induction selected generalizing arms with
  | head matched =>
    cases certificates with
    | cons certificate typed bodyCertified tail =>
      obtain ⟨values, related, runs⟩ := pattern_success_with_signatures certificate signatures catalogValid extended represented matched
      exact .head matched related runs bodyCertified
  | tail notMatched selected ih =>
    cases certificates with
    | cons certificate typed bodyCertified tail =>
      cases sites with
      | cons headSites tailSites =>
        cases pattern_decides_with_literals certificate literals signatures requirements headSites catalogValid extended represented with
        | inl found =>
          obtain ⟨_, _, matched, _⟩ := found
          exact False.elim (notMatched.excludes matched)
        | inr failed => exact .tail notMatched failed.2 (ih tail fallbackCertificate tailSites)
  | default => cases certificates; cases fallbackCertificate with
    | some certified => exact .default certified
  | noBranch => cases certificates; cases fallbackCertificate; exact .noBranch

theorem Arms.selects {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value payload)
    {selection : Dynamic.MatchCaseSelection}
    (selected : Dynamic.MatchCasesSelect context sourceValue cases fallback selection) :
    Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection := by
  exact Arms.selects_with_literals certificates fallbackCertificate _ valid.signatures (fun _ proof => proof)
    (CompatibleMatchDecision.Arms.ordinary_sites certificates valid) catalogValid extended represented selected


/-- Accepted compatible metadata always supplies a delimited source pattern;
this uses no runtime value or native type authentication assumption. -/
theorem pattern_not_malformed_with_signatures {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (signatures : context.signatures = compilation.signatures) : ¬ Dynamic.PatternMalformed context pattern := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  intro malformed
  cases malformed with
  | source absent => exact absent arity sourceRep
  | «prefix» other absent =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep other
    subst arityEq
    subst instructions
    exact absent (CompatiblePatternCertificates.Tree.skips tree)


theorem pattern_not_malformed {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context) : ¬ Dynamic.PatternMalformed context pattern := by
  exact pattern_not_malformed_with_signatures certificate valid.signatures

theorem Arms.not_pattern_fault_with_signatures {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (signatures : context.signatures = compilation.signatures) (value : Dynamic.Value) :
    ¬ Dynamic.MatchCasesPatternFault context value cases := by
  induction certificates with
  | nil => intro fault; cases fault
  | cons certificate typed body tail ih =>
    intro fault
    cases fault with
    | head malformed => exact pattern_not_malformed_with_signatures certificate signatures malformed
    | tail _ next => exact ih next


theorem Arms.not_pattern_fault {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (valid : ContextValid compilation context) (value : Dynamic.Value) :
    ¬ Dynamic.MatchCasesPatternFault context value cases := by
  exact Arms.not_pattern_fault_with_signatures certificates valid.signatures value

theorem Certificate.not_pattern_fault_with_signatures {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (signatures : context.signatures = compilation.signatures) (value : Dynamic.Value) :
    ¬ Dynamic.MatchCasesPatternFault context value resolution.cases := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection expression
      sameType arms fallback branches hiddenCompiled =>
    exact Arms.not_pattern_fault_with_signatures arms signatures value


theorem Certificate.not_pattern_fault {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (valid : ContextValid compilation context) (value : Dynamic.Value) :
    ¬ Dynamic.MatchCasesPatternFault context value resolution.cases := by
  exact Certificate.not_pattern_fault_with_signatures certificate valid.signatures value

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchSourceSelection
