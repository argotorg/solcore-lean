import Solcore.SourceSemantics.CoreLowering.CompatiblePatternLeaves
import Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts

/-! Accepted numeric matchers retain the exact validator-selected implementation
row. The complete runtime ledger supplies only that row's independent validity;
unused assumption and template rows remain unchanged. Pattern matching has no
dictionary argument, so evidence coverage is not an additional condition here.
Composite patterns, whole Match statements and catalog Header entry are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternLiteralRuntime
open Core Frontend Frontend.SourceInference
open SourceCoreCompatibleDataMatches CompatiblePatternCertificates CompatiblePatternLeaves
open GeneralHeap CompatiblePayload

/-- Each actual numeric resolution retains its complete selected row. -/
def NumericSelected (compilation : Compilation) (resolution : MatchPatternResolution) : Prop :=
  ∀ literal numeric, resolution = .integerLiteral literal numeric →
    ∃ implementation, NumericLiteralEvidenceReceipts.Selected compilation.solvedRequirements numeric implementation

/-- This inversion uses the validator inside the real matcher, including its
synthetic expression occurrence. Metadata membership alone is not sufficient. -/
theorem literalMatcher_selected (compilation : Compilation) (site : StatementId) (span : Syntax.SourceSpan)
    (type : TypeSystem.Ty) (literal : Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution)
    (matcher : Expr) (accepted : literalMatcher compilation site span type literal resolution = .ok matcher) :
    ∃ implementation, NumericLiteralEvidenceReceipts.Selected compilation.solvedRequirements resolution implementation := by
  have code := literalMatcher_sound compilation site span type literal resolution matcher accepted
  cases code with
  | word target meaning retained =>
    let node : ExpressionNode := ⟨⟨site.occurrence⟩, span, .word, .integerLiteral literal resolution, [resolution.requirement], [], none⟩
    cases validated : SourceCoreElaboration.validateWordIntegerLiteral compilation.solvedRequirements node literal resolution with
    | error error =>
      simp only [node, TypeSystem.Ty.word] at validated
      simp [literalMatcher, TypeSystem.Ty.word, validated, Except.mapError, bind, Except.bind] at accepted
    | ok value => exact ⟨_, NumericLiteralEvidenceReceipts.word validated⟩
  | integer target meaning retained =>
    let node : ExpressionNode := ⟨⟨site.occurrence⟩, span, .integer, .integerLiteral literal resolution, [resolution.requirement], [], none⟩
    cases validated : SourceCoreElaboration.validateNativeIntegerLiteral compilation.solvedRequirements node literal resolution with
    | error error =>
      simp only [node, TypeSystem.Ty.integer] at validated
      simp [literalMatcher, TypeSystem.Ty.integer, validated, Except.mapError, bind, Except.bind] at accepted
    | ok value => exact ⟨_, NumericLiteralEvidenceReceipts.integer validated⟩

/-- The original pattern certificate and the selected numeric row share all
source, instruction, matcher, requirement and binding indices. -/
structure Certificate (compilation : Compilation) (source : TypedSource) (scope : Scope)
    (site : StatementId) (span : Syntax.SourceSpan) (expected : TypeSystem.Ty)
    (pattern : TypedMatchPattern) (compiled : Pattern) : Prop where
  original : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled
  numeric : NumericSelected compilation pattern.resolution

theorem of_certificate {compilation : Compilation} {source : TypedSource} {scope : Scope}
    {site : StatementId} {span : Syntax.SourceSpan} {expected : TypeSystem.Ty}
    {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled) :
    Certificate compilation source scope site span expected pattern compiled := by
  refine ⟨certificate, ?_⟩
  intro literal numeric form
  rcases pattern with ⟨spelling, patternType, resolution, requirements⟩
  dsimp only at form
  subst resolution
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨_, instructionsEq, _⟩ := rootInstructions_sound compilation
    (SourceSemantics.Context.ofSignatures compilation.signatures) rfl spelling (.integerLiteral literal numeric) instructions root
  subst instructions
  cases tree with
  | literal projection validated => exact literalMatcher_selected compilation site span expected literal numeric _ validated

theorem of_compilePattern (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled) :
    Certificate compilation source scope site span expected pattern compiled.pattern :=
  of_certificate (certificate_of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)

/-- Only actual implementation rows are consumed. No whole ordinary validity,
coverage, template exclusion or ledger filtering is inferred. -/
theorem NumericSelected.requirements {compilation : Compilation} {resolution : MatchPatternResolution}
    (selected : NumericSelected compilation resolution) {context : SourceSemantics.Context}
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context) : NumericRequirements context resolution := by
  intro literal numeric form
  obtain ⟨implementation, chosen⟩ := selected literal numeric form
  exact chosen.proves sameLedger runtime

section Meaning
variable {compilation : Compilation} {context : SourceSemantics.Context}
  {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
  {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
  (certificate : Certificate compilation source scope site span expected pattern compiled)
  (signatures : context.signatures = compilation.signatures)
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context) (leaf : LeafResolution pattern.resolution)
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
  {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
  (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.type)

include certificate signatures sameLedger runtime leaf represented in
theorem preserves (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.matcher (.var 0)) outcome store :=
  leaf_preserves_with_requirements certificate.original signatures
    (certificate.numeric.requirements sameLedger runtime) leaf represented environment store

include certificate signatures sameLedger runtime leaf represented in
theorem reflects {environment : Environment} {store finalStore : Store} {outcome : Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.matcher (.var 0)) outcome finalStore) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled sourceValue outcome ∧ finalStore = store :=
  leaf_reflects_with_requirements certificate.original signatures
    (certificate.numeric.requirements sameLedger runtime) leaf represented completed
end Meaning
end Solcore.SourceSemantics.CoreLowering.CompatiblePatternLiteralRuntime
