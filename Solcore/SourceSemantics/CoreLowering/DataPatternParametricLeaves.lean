import Solcore.SourceSemantics.CoreLowering.DataPatternDecision

/-! Wildcard and binder patterns preserve any relation on source/Core values.
They never inspect a value's representation or clone its captured state. This
lemma is usable for functions, mappings and proxies once the caller's value
relation covers those carriers. It does not establish that relation itself. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternParametricLeaves
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues DataPatternExecution

inductive OpaqueLeaf : MatchPatternResolution → Prop where
  | wildcard : OpaqueLeaf .wildcard
  | binder (binder : TypedBinder) : OpaqueLeaf (.binder binder)

inductive BindingsRelated (relation : Dynamic.Value → Value → Prop) :
    List (TypedBinder × Ty) → List (TypedBinder × Dynamic.Value) → List Value → Prop where
  | nil : BindingsRelated relation [] [] []
  | cons {binder : TypedBinder} {type : Ty} {source : Dynamic.Value} {value : Value}
      {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
      (head : relation source value) (tail : BindingsRelated relation binders sources values) :
      BindingsRelated relation ((binder, type) :: binders) ((binder, source) :: sources) (value :: values)

/-- Compiler acceptance preserves the caller's arbitrary value relation through
opaque pattern binding. The source and Core heap/capture identity is untouched. -/
theorem compilePattern_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (signatures : context.signatures = compilation.signatures)
    (leaf : OpaqueLeaf pattern.resolution) (relation : Dynamic.Value → Value → Prop)
    {sourceValue : Dynamic.Value} {value : Value} (represented : relation sourceValue value) :
    ∃ bindings values, Dynamic.PatternMatches context pattern sourceValue bindings ∧
      BindingsRelated relation compiled.pattern.bindings bindings values ∧ MatcherRuns compiled.pattern value values := by
  have certificate := certificate_of_compilePattern compilation compilationFuel source scope site span expected pattern compiled accepted
  generalize compiledEq : compiled.pattern = lowered at certificate ⊢
  rcases pattern with ⟨spelling, patternType, resolution, requirements⟩
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures spelling resolution instructions root
  subst instructions
  cases leaf with
  | wildcard =>
    cases tree with
    | wildcard projection =>
      exact ⟨[], [], .intro sourceRep .wildcard, .nil,
        fun _ store _ path => .apply .lambda (path.evaluates store) (.inRight .unit)⟩
  | binder binder =>
    cases tree with
    | binder projection sourceType binderValid =>
      exact ⟨[(binder, sourceValue)], [value], .intro sourceRep .binder, .cons represented .nil,
        fun _ store _ path => .apply .lambda (path.evaluates store) (.inRight (.var rfl))⟩

end Solcore.SourceSemantics.CoreLowering.DataPatternParametricLeaves
