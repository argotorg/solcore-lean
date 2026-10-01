import Solcore.SourceSemantics.CoreLowering.CompatiblePatternCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues
import Solcore.Core.Correspondence

/-! Actual compatible wildcard, binder and numeric patterns preserve the
general payload relation, including functions, mappings and proxies. Numeric
leaves use the independent evidence ledger. No input matcher execution or
separate runtime type witness is required. Composite patterns are subsequent
consumers of the static certificate. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternLeaves
open Core Frontend Frontend.SourceInference
open SourceCoreCompatibleDataMatches CompatiblePatternCertificates DataPatternValues
open GeneralHeap CompatiblePayload

structure ContextValid (compilation : Compilation) (context : Context) : Prop where
  signatures : context.signatures = compilation.signatures
  ledger : context.solvedRequirements = compilation.solvedRequirements
  valid : RequirementLedgerWellFormed context

inductive LiteralCode (compilation : Compilation) (literal : Syntax.CoreLiteralValue)
    (resolution : IntegerLiteralResolution) : TypeSystem.Ty → Expr → Prop where
  | word
      (target : resolution.targetType = .word)
      (meaning : NumericLiteralDenotes literal resolution.rawValue)
      (requirement : ∃ solved ∈ compilation.solvedRequirements, solved.id = resolution.requirement ∧
        solved.predicate = ProgramSignatures.builtinIntPredicate .word) :
      LiteralCode compilation literal resolution .word
        (.lambda .word (.sum .unit .unit)
          (.ifE (.binary .wordEq (.var 0) (.word (Word.ofNatModulo resolution.rawValue)))
            (.inRight .unit .unit) (.inLeft .unit .unit)))
  | integer
      (target : resolution.targetType = .integer)
      (meaning : NumericLiteralDenotes literal resolution.rawValue)
      (requirement : ∃ solved ∈ compilation.solvedRequirements, solved.id = resolution.requirement ∧
        solved.predicate = ProgramSignatures.builtinIntPredicate .integer) :
      LiteralCode compilation literal resolution .integer
        (.lambda .integer (.sum .unit .unit)
          (.ifE (.binary .integerEq (.var 0) (.integer (Int.ofNat resolution.rawValue)))
            (.inRight .unit .unit) (.inLeft .unit .unit)))

theorem literalMatcher_sound (compilation : Compilation) (site : StatementId) (span : Syntax.SourceSpan)
    (type : TypeSystem.Ty) (literal : Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution)
    (matcher : Expr) (accepted : literalMatcher compilation site span type literal resolution = .ok matcher) :
    LiteralCode compilation literal resolution type matcher := by
  cases type with
  | constructor constructor =>
    cases constructor with
    | declaration => simp [literalMatcher, bind, Except.bind] at accepted
    | builtin builtin =>
      cases builtin with
      | unit | bool => simp [literalMatcher, bind, Except.bind] at accepted
      | word =>
        let node : ExpressionNode := ⟨⟨site.occurrence⟩, span, .word, .integerLiteral literal resolution, [resolution.requirement], [], none⟩
        cases validated : SourceCoreElaboration.validateWordIntegerLiteral compilation.solvedRequirements node literal resolution with
        | error error =>
          simp only [node, TypeSystem.Ty.word] at validated
          simp [literalMatcher, validated, Except.mapError, bind, Except.bind] at accepted
        | ok validatedValue =>
          simp only [node, TypeSystem.Ty.word] at validated
          have certificate := SourceCoreElaboration.validateWordIntegerLiteral_sound validated
          have same : matcher = .lambda .word (.sum .unit .unit)
              (.ifE (.binary .wordEq (.var 0) (.word validatedValue.value)) (.inRight .unit .unit) (.inLeft .unit .unit)) := by
            simpa [literalMatcher, validated, Except.mapError, bind, Except.bind, pure, Except.pure] using accepted.symm
          rw [same, certificate.value]
          exact .word certificate.targetType certificate.meaning certificate.solved
      | integer =>
        let node : ExpressionNode := ⟨⟨site.occurrence⟩, span, .integer, .integerLiteral literal resolution, [resolution.requirement], [], none⟩
        cases validated : SourceCoreElaboration.validateNativeIntegerLiteral compilation.solvedRequirements node literal resolution with
        | error error =>
          simp only [node, TypeSystem.Ty.integer] at validated
          simp [literalMatcher, validated, Except.mapError, bind, Except.bind] at accepted
        | ok validatedValue =>
          simp only [node, TypeSystem.Ty.integer] at validated
          have certificate := SourceCoreElaboration.validateNativeIntegerLiteral_sound validated
          have same : matcher = .lambda .integer (.sum .unit .unit)
              (.ifE (.binary .integerEq (.var 0) (.integer validatedValue.value)) (.inRight .unit .unit) (.inLeft .unit .unit)) := by
            simpa [literalMatcher, validated, Except.mapError, bind, Except.bind, pure, Except.pure] using accepted.symm
          rw [same, certificate.value]
          exact .integer certificate.targetType certificate.meaning certificate.solved
  | «variable» | parameter | application | product | function | mapping | proxy | comptime | error =>
    simp [literalMatcher, bind, Except.bind] at accepted

/-- Ordered source binding records correspond to the values packed in Core's
successful result, retaining exact binder identity and metadata. -/
inductive BindingsRep (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping) :
    List (TypedBinder × Ty) → List (TypedBinder × Dynamic.Value) → List Value → Prop where
  | nil : BindingsRep checked registry functions mapping world [] [] []
  | cons {binder : TypedBinder} {type : Ty} {source : Dynamic.Value} {value : Value}
      {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
      (head : ValueRep checked registry functions mapping world binder.scheme.body source value type) (tail : BindingsRep checked registry functions mapping world binders sources values) :
      BindingsRep checked registry functions mapping world ((binder, type) :: binders) ((binder, source) :: sources) (value :: values)

inductive OutcomeRep (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping) (context : Context)
    (pattern : TypedMatchPattern) (compiled : Pattern) (sourceValue : Dynamic.Value) : Value → Prop where
  | matched {bindings : List (TypedBinder × Dynamic.Value)} {values : List Value}
      (meaning : Dynamic.PatternMatches context pattern sourceValue bindings)
      (represented : BindingsRep checked registry functions mapping world compiled.bindings bindings values) :
      OutcomeRep checked registry functions mapping world context pattern compiled sourceValue (.inRight .unit (packValues values))
  | noMatch (meaning : Dynamic.PatternDoesNotMatch context pattern sourceValue) :
      OutcomeRep checked registry functions mapping world context pattern compiled sourceValue (.inLeft (bundleType compiled.bindingTypes) .unit)

inductive LeafResolution : MatchPatternResolution → Prop where
  | wildcard : LeafResolution .wildcard
  | binder (binder : TypedBinder) : LeafResolution (.binder binder)
  | literal (literal : Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution) :
      LeafResolution (.integerLiteral literal resolution)

private theorem proves {compilation : Compilation} {context : Context} (valid : ContextValid compilation context)
    {requirement : RequirementId} {predicate : ProgramPredicate}
    (retained : ∃ solved ∈ compilation.solvedRequirements, solved.id = requirement ∧ solved.predicate = predicate) :
    RequirementProves context requirement predicate := by
  obtain ⟨solved, member, identifier, same⟩ := retained
  have member : solved ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
  exact ⟨solved, ⟨member, identifier⟩, same, valid.valid.entriesValid solved member⟩

theorem LiteralCode.constructs_word {compilation : Compilation} {context : Context}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    (valid : ContextValid compilation context) (target : resolution.targetType = .word)
    (meaning : NumericLiteralDenotes literal resolution.rawValue)
    (requirement : ∃ solved ∈ compilation.solvedRequirements, solved.id = resolution.requirement ∧
      solved.predicate = ProgramSignatures.builtinIntPredicate .word) :
    Dynamic.ResolvedIntegerLiteralConstructs context literal resolution (.word (Word.ofNatModulo resolution.rawValue)) := by
  cases resolution with
  | mk raw type requirementId =>
    dsimp at target
    subst type
    exact .word meaning (proves valid requirement)

theorem LiteralCode.constructs_integer {compilation : Compilation} {context : Context}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    (valid : ContextValid compilation context) (target : resolution.targetType = .integer)
    (meaning : NumericLiteralDenotes literal resolution.rawValue)
    (requirement : ∃ solved ∈ compilation.solvedRequirements, solved.id = resolution.requirement ∧
      solved.predicate = ProgramSignatures.builtinIntPredicate .integer) :
    Dynamic.ResolvedIntegerLiteralConstructs context literal resolution (.integer (Int.ofNat resolution.rawValue)) := by
  cases resolution with
  | mk raw type requirementId =>
    dsimp at target
    subst type
    exact .integer meaning (proves valid requirement)


private theorem projected_word (compilation : Compilation) (source : TypedSource) :
    projected compilation source TypeSystem.Ty.word = .ok .word := rfl
private theorem projected_integer (compilation : Compilation) (source : TypedSource) :
    projected compilation source TypeSystem.Ty.integer = .ok .integer := rfl

theorem LeafResolution.bindings_unique {context : Context} {pattern : TypedMatchPattern}
    {value : Dynamic.Value} {left right : List (TypedBinder × Dynamic.Value)}
    (leaf : LeafResolution pattern.resolution)
    (first : Dynamic.PatternMatches context pattern value left)
    (second : Dynamic.PatternMatches context pattern value right) : left = right := by
  rcases pattern with ⟨spelling, type, resolution, requirements⟩
  cases first with
  | intro firstSource firstMatch =>
    cases second with
    | intro secondSource secondMatch =>
      cases leaf <;>
        simp only [Dynamic.PatternResolutionMatches, matchPatternResolutionInstructions] at firstMatch secondMatch <;>
        cases firstMatch <;> cases secondMatch <;> rfl

theorem LeafResolution.excludes {context : Context} {pattern : TypedMatchPattern}
    {value : Dynamic.Value} {bindings : List (TypedBinder × Dynamic.Value)}
    (leaf : LeafResolution pattern.resolution)
    (failure : Dynamic.PatternDoesNotMatch context pattern value)
    (matched : Dynamic.PatternMatches context pattern value bindings) : False := by
  rcases pattern with ⟨spelling, type, resolution, requirements⟩
  cases failure with
  | intro failedSource failedMatch =>
    cases matched with
    | intro matchedSource matchedMatch =>
      cases leaf <;>
        simp only [Dynamic.PatternResolutionDoesNotMatch, Dynamic.PatternResolutionMatches,
          matchPatternResolutionInstructions] at failedMatch matchedMatch <;>
        exact failedMatch.mismatch _ matchedMatch

/-- Every accepted leaf pattern produces its independent source outcome in
finite Core steps, packs the exact ordered bindings, and preserves the store. -/
theorem leaf_preserves {compilation : Compilation} {context : Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.matcher (.var 0)) outcome store := by
  rcases pattern with ⟨spelling, patternType, resolution, requirements⟩
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context valid.signatures
    spelling resolution instructions root
  subst instructions
  cases leaf with
  | wildcard =>
    cases tree with
    | wildcard projection =>
      refine ⟨.inRight .unit .unit, .matched (bindings := []) (values := []) ?_ .nil, ?_⟩
      · exact .intro sourceRep .wildcard
      exact SourceCoreCompatibleDataMatches.wildcard_evaluates environment store _ value
  | binder binder =>
    cases tree with
    | binder projection sourceType binderValid =>
      refine ⟨.inRight .unit value, .matched (bindings := [(binder, sourceValue)]) (values := [value]) ?_ (.cons (sourceType.symm ▸ represented) .nil), ?_⟩
      · exact .intro sourceRep .binder
      exact SourceCoreCompatibleDataMatches.binder_evaluates environment store _ value
  | literal literal resolution =>
    cases tree with
    | literal projection validated =>
      have code := literalMatcher_sound compilation site span expected literal resolution _ validated
      cases code with
      | word target meaning retained =>
        have coreType := projection
        rw [projected_word] at coreType
        cases coreType
        obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields represented
        have constructs := LiteralCode.constructs_word valid target meaning retained
        by_cases same : actual = Word.ofNatModulo resolution.rawValue
        · subst actual
          refine ⟨.inRight .unit .unit, .matched (values := []) (.intro sourceRep (.integerLiteral constructs)) .nil, ?_⟩
          exact .apply .lambda (.var rfl)
            (.ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply])) (.inRight .unit))
        · refine ⟨.inLeft .unit .unit, .noMatch (.intro sourceRep ⟨.integerLiteral, ?_⟩), ?_⟩
          · intro bindings matched
            cases matched with
            | integerLiteral construction => exact same (Dynamic.Value.word.inj (construction.functional constructs))
          · exact .apply .lambda (.var rfl)
              (.ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, same])) (.inLeft .unit))
      | integer target meaning retained =>
        have coreType := projection
        rw [projected_integer] at coreType
        cases coreType
        obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.integer_fields represented
        have constructs := LiteralCode.constructs_integer valid target meaning retained
        by_cases same : actual = Int.ofNat resolution.rawValue
        · subst actual
          refine ⟨.inRight .unit .unit, .matched (values := []) (.intro sourceRep (.integerLiteral constructs)) .nil, ?_⟩
          exact .apply .lambda (.var rfl)
            (.ifTrue (.binary (.var rfl) .integer (by simp [BinaryOp.apply])) (.inRight .unit))
        · refine ⟨.inLeft .unit .unit, .noMatch (.intro sourceRep ⟨.integerLiteral, ?_⟩), ?_⟩
          · intro bindings matched
            cases matched with
            | integerLiteral construction => exact same (Dynamic.Value.integer.inj (construction.functional constructs))
          · exact .apply .lambda (.var rfl)
              (.ifFalse (.binary (.var rfl) .integer (by
                simp only [BinaryOp.apply, Option.some.injEq, Value.bool.injEq, beq_eq_false_iff_ne]
                exact same)) (.inLeft .unit))


/-- Public entry consumes actual compiler success; the structural certificate
is obtained internally and is never an extra caller obligation. -/
theorem compilePattern_leaf_preserves (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store :=
  leaf_preserves (certificate_of_compilePattern compilation fuel source scope site span expected pattern compiled accepted)
    valid leaf represented environment store

/-- Any completed native leaf matcher reconstructs independent source meaning
and leaves every surrounding cell unchanged. -/
theorem compilePattern_leaf_reflects (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    {environment : Environment} {store finalStore : Store} {outcome : Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome finalStore) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      finalStore = store := by
  obtain ⟨predicted, meaning, evaluated⟩ := compilePattern_leaf_preserves compilation fuel source scope site span
    expected pattern compiled accepted context valid leaf represented environment store
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic completed evaluated
  exact ⟨sameValue.symm ▸ meaning, sameStore⟩

/-- A supplied independent success fixes exact source binding order. No
evaluation of the generated matcher is assumed. -/
theorem compilePattern_leaf_success_preserves (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    {bindings : List (TypedBinder × Dynamic.Value)} (matched : Dynamic.PatternMatches context pattern sourceValue bindings)
    (environment : Environment) (store : Store) :
    ∃ values, BindingsRep compilation.checked registry functions mapping world compiled.pattern.bindings bindings values ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0))
        (.inRight .unit (packValues values)) store := by
  obtain ⟨outcome, meaning, evaluated⟩ := compilePattern_leaf_preserves compilation fuel source scope site span
    expected pattern compiled accepted context valid leaf represented environment store
  cases meaning with
  | matched actual bindingsRep =>
    have same := leaf.bindings_unique actual matched
    exact ⟨_, same ▸ bindingsRep, evaluated⟩
  | noMatch failure => exact False.elim (leaf.excludes failure matched)

/-- Independent source rejection returns the native no-match tag, with no
bindings or store changes escaping the matcher. -/
theorem compilePattern_leaf_failure_preserves (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (failure : Dynamic.PatternDoesNotMatch context pattern sourceValue)
    (environment : Environment) (store : Store) :
    Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0))
      (.inLeft (bundleType compiled.pattern.bindingTypes) .unit) store := by
  obtain ⟨outcome, meaning, evaluated⟩ := compilePattern_leaf_preserves compilation fuel source scope site span
    expected pattern compiled accepted context valid leaf represented environment store
  cases meaning with
  | matched actual bindingsRep => exact False.elim (leaf.excludes failure actual)
  | noMatch actual => exact evaluated

/-- The finite abstract result is the result of every completed machine run;
its sufficient fuel budget is independent of compilation fuel. -/
theorem compilePattern_leaf_run_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context) (leaf : LeafResolution pattern.resolution)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap}
    {sourceValue : Dynamic.Value} {value : Value} {world : StoreTyping}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done outcome store) ∧
      (∀ fuel actual finalStore,
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done actual finalStore →
        actual = outcome ∧ finalStore = store) := by
  obtain ⟨outcome, meaning, evaluated⟩ := compilePattern_leaf_preserves compilation compilationFuel source scope site span
    expected pattern compiled accepted context valid leaf represented environment store
  exact ⟨outcome, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePatternLeaves
