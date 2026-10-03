import Solcore.SourceSemantics.CoreLowering.CompatiblePatternDecision
import Solcore.SourceSemantics.CoreLowering.CompatiblePatternLiteralRuntime

/-! Composite compatible patterns consume numeric evidence only at their actual
literal leaves. The full ordered compiler tree, requirement list, raw constructor
guards and binding metadata are retained. No evidence dictionary, ordinary
ledger validity or template exclusion is required here. Whole ordered Match
selection and catalog Header/Profile integration remain separate boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternRuntime
open Core Frontend Frontend.SourceInference
open SourceCoreCompatibleDataMatches CompatiblePatternCertificates CompatiblePatternLeaves
open GeneralHeap CompatiblePayload

structure ContextValid (compilation : Compilation) (context : SourceSemantics.Context) : Prop where
  signatures : context.signatures = compilation.signatures
  ledger : context.solvedRequirements = compilation.solvedRequirements
  runtime : RuntimeRequirementLedgerValid context

/-- Actual singleton validator rows are attached to occurrences in the original
pattern tree. No runtime meaning law is stored in this certificate. -/
abbrev Certificate (compilation : Compilation) (source : TypedSource) (scope : Scope)
    (site : StatementId) (span : Syntax.SourceSpan) (expected : TypeSystem.Ty)
    (pattern : TypedMatchPattern) (compiled : Pattern) : Prop :=
  CompatiblePatternDecision.WithLiterals
    (fun numeric => ∃ implementation, NumericLiteralEvidenceReceipts.Selected compilation.solvedRequirements numeric implementation)
    compilation source scope site span expected pattern compiled

theorem of_certificate {compilation : Compilation} {source : TypedSource} {scope : Scope}
    {site : StatementId} {span : Syntax.SourceSpan} {expected : TypeSystem.Ty}
    {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled) :
    Certificate compilation source scope site span expected pattern compiled :=
  CompatiblePatternDecision.WithLiterals.of_certificate certificate _
    (fun expected literal resolution matcher accepted =>
      CompatiblePatternLiteralRuntime.literalMatcher_selected compilation site span expected literal resolution matcher accepted)

theorem of_compilePattern (compilation : Compilation) (fuel : Nat) (source : TypedSource)
    (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan) (expected : TypeSystem.Ty)
    (pattern : TypedMatchPattern) (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled) :
    Certificate compilation source scope site span expected pattern compiled.pattern :=
  of_certificate (certificate_of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)

section Meaning
variable {compilation : Compilation} {source : TypedSource} {scope : Scope} {site : StatementId}
  {span : Syntax.SourceSpan} {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
  {context : SourceSemantics.Context}
  (certificate : Certificate compilation source scope site span expected pattern compiled)
  (valid : ContextValid compilation context)
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)

include certificate valid catalogValid extended in
theorem preserves {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.matcher (.var 0)) outcome store := by
  apply CompatiblePatternDecision.preserves_with_literals certificate valid.signatures ?_ catalogValid extended represented environment store
  intro numeric selected
  obtain ⟨implementation, chosen⟩ := selected
  exact chosen.proves valid.ledger valid.runtime

include certificate valid catalogValid extended in
theorem reflects {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.type)
    {environment : Environment} {store after : Store} {outcome : Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.matcher (.var 0)) outcome after) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled sourceValue outcome ∧ after = store := by
  apply CompatiblePatternDecision.reflects_with_literals certificate valid.signatures ?_ catalogValid extended represented completed
  intro numeric selected
  obtain ⟨implementation, chosen⟩ := selected
  exact chosen.proves valid.ledger valid.runtime
end Meaning
end Solcore.SourceSemantics.CoreLowering.CompatiblePatternRuntime
