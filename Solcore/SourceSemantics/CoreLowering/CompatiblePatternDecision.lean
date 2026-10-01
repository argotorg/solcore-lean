import Solcore.SourceSemantics.CoreLowering.CompatiblePatternSuccess
import Solcore.SourceSemantics.Dynamic.PatternCompletenessProperties

/-! Complete finite decisions for the actual compatible matcher tree. Every
recursive child obligation is discharged by the tree induction. Exact raw
constructor identity is checked before traversing any payload child. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternDecision
open Core Frontend SourceInference GeneralHeap DataPatternValues DataPatternExecution DataEquality
open CompatiblePayload CompatiblePatternLeaves CompatiblePatternCertificates CompatiblePatternExecution
open SourceCoreCompatibleDataMatches
variable {compilation : Compilation} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}

def TreeDecision (context : Context) (type : TypeSystem.Ty) (instructions : List MatchPatternInstruction)
    (pattern : Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ source value, ValueRep compilation.checked registry functions mapping world type source value pattern.type →
    (∃ bindings values, Dynamic.PatternInstructionMatches context source instructions bindings rest ∧
      BindingsRep compilation.checked registry functions mapping world pattern.bindings bindings values ∧
      CompatiblePatternExecution.MatcherRuns pattern value values) ∨ CompatiblePatternExecution.MatcherFails pattern value

def ForestDecision (context : Context) (types : List TypeSystem.Ty) (instructions : List MatchPatternInstruction)
    (patterns : List Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ sources values coreTypes, ValuesRep compilation.checked registry functions mapping world types sources values coreTypes →
    (∃ bindings boundValues, Dynamic.PatternInstructionsMatch context sources instructions bindings rest ∧
      BindingsRep compilation.checked registry functions mapping world (patterns.flatMap (·.bindings)) bindings boundValues ∧
      CompatiblePatternExecution.ChildrenRun patterns values boundValues) ∨ CompatiblePatternExecution.ChildrenFail patterns values

theorem Tree.decides {context : Context} {source : TypedSource} {site : StatementId} {span : Syntax.SourceSpan}
    {scope : Scope} {type : TypeSystem.Ty} {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (valid : ContextValid compilation context) (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    (tree : Tree compilation source site span scope type instructions pattern rest) :
    TreeDecision (compilation := compilation) (registry := registry) (functions := functions)
      (mapping := mapping) (world := world) context type instructions pattern rest := by
  induction tree using Tree.rec
    (motive_2 := fun types instructions patterns rest _ =>
      ForestDecision (compilation := compilation) (registry := registry) (functions := functions)
        (mapping := mapping) (world := world) context types instructions patterns rest) with
  | wildcard projection =>
    intro source value represented
    exact .inl ⟨[], [], .wildcard, .nil, fun _ store _ selected => .apply .lambda (selected.evaluates store) (.inRight .unit)⟩
  | binder projection sourceType binderValid =>
    intro source value represented
    exact .inl ⟨[(_, source)], [value], .binder, .cons (sourceType.symm ▸ represented) .nil,
      fun _ store _ selected => .apply .lambda (selected.evaluates store) (.inRight (.var rfl))⟩
  | @literal expected coreType literal resolution matcher rest projection validated =>
    intro sourceValue value represented
    have code := literalMatcher_sound compilation _ _ _ _ _ _ validated
    cases code with
    | word target meaning retained =>
      have typeEq : _ = Ty.word := Except.ok.inj projection.symm
      subst typeEq
      obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields represented
      by_cases same : actual = Word.ofNatModulo resolution.rawValue
      · subst actual
        exact .inl ⟨[], [], .integerLiteral (LiteralCode.constructs_word valid target meaning retained), .nil,
          fun _ store _ selected => .apply .lambda (selected.evaluates store)
            (.ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply])) (.inRight .unit))⟩
      · exact .inr (fun _ store _ selected => .apply .lambda (selected.evaluates store)
          (.ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, same])) (.inLeft .unit)))
    | integer target meaning retained =>
      have typeEq : _ = Ty.integer := Except.ok.inj projection.symm
      subst typeEq
      obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.integer_fields represented
      by_cases same : actual = Int.ofNat resolution.rawValue
      · subst actual
        exact .inl ⟨[], [], .integerLiteral (LiteralCode.constructs_integer valid target meaning retained), .nil,
          fun _ store _ selected => .apply .lambda (selected.evaluates store)
            (.ifTrue (.binary (.var rfl) .integer (by simp [BinaryOp.apply])) (.inRight .unit))⟩
      · exact .inr (fun _ store _ selected => .apply .lambda (selected.evaluates store)
          (.ifFalse (.binary (.var rfl) .integer (by
            simp only [BinaryOp.apply, Option.some.injEq, Value.bool.injEq, beq_eq_false_iff_ne]
            exact same)) (.inLeft .unit)))
  | @tuple expected coreType count types instructions rest children coreTypes projection unpacked childrenTree projectedChildren ih =>
    intro sourceValue value represented
    obtain ⟨sources, values, actualTypes, valueReps, packing, valueEq, typeEq⟩ := CompatiblePatternValues.unpack unpacked represented
    subst value
    have nativeTypes : actualTypes = coreTypes := Except.ok.inj (valueReps.projection.symm.trans (projectedList_catalog projectedChildren))
    subst actualTypes
    have lengths := CompatiblePayload.ValuesRep.length valueReps
    have length := lengths.2.2.symm.trans lengths.2.1
    cases ih _ _ _ valueReps with
    | inl success =>
      obtain ⟨bindings, boundValues, matched, bindingRep, childrenRun⟩ := success
      refine .inl ⟨bindings, boundValues, .tuple packing (lengths.1.symm.trans (unpackTypes_length unpacked)) matched, bindingRep, ?_⟩
      intro environment store expression selected
      apply Evaluates.apply .lambda (selected.evaluates store)
      have paths := projectionList_selects (environment := packValues values :: environment) (expression := .var 0) (.var rfl) length
      simpa [tuplePattern, Pattern.bindingTypes, childValues] using childrenRun _ store _ [] [] _ paths .nil
    | inr failed =>
      refine .inr ?_
      intro environment store expression selected
      apply Evaluates.apply .lambda (selected.evaluates store)
      have paths := projectionList_selects (environment := packValues values :: environment) (expression := .var 0) (.var rfl) length
      simpa [tuplePattern, Pattern.bindingTypes, childValues] using failed _ store _ [] [] _ paths .nil
  | @constructor expected coreType instantiation count constructor definition metadata instructions rest children coreTypes
      projection result arity resolved sameType raw childrenTree projectedChildren registered ih =>
    intro sourceValue value represented
    obtain ⟨signature, declaration, arguments, _, _, _, _, _, nominalResult⟩ :=
      CompatibleConstructorMetadata.facts (CompatibleConstructorMetadata.resolved_facts resolved).1
    have nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType expected) =
        some (signature.id, arguments.map SourceCoreRawMetadata.runtimeType) := by
      rw [← result, nominalResult, CompatibleConstructorMetadata.runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal]
    obtain ⟨actual, sources, tag, actualId, values, actualTypes, rfl, valueEq, typeEq, fields⟩ := CompatiblePatternValues.nominal_fields represented nominal
    subst value
    have ownerEq : tag.owner = constructor.owner := Ty.namedData.inj (typeEq.symm.trans sameType)
    have lookup : definition.constructorPayloadTypes[tag.index]? =
        some (.product .word (SourceCoreCompatibleCatalog.packTypes actualTypes)) := by
      simpa [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, ownerEq, registered] using fields.registered
    by_cases sameTag : tag = constructor
    · subst tag
      have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
          if index = constructor.index then rawConstructor metadata (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd))
            (matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children
              (coreTypes.zipIdx.map fun (item : Ty × Nat) => SourceCoreDataExpressions.projectPacked item.2 coreTypes (.second (.var 0))) [])
          else .inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit)[constructor.index]? =
          some (rawConstructor metadata (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd))
            (matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children
              (coreTypes.zipIdx.map fun (item : Ty × Nat) => SourceCoreDataExpressions.projectPacked item.2 coreTypes (.second (.var 0))) [])) := by
        simp [List.getElem?_map, List.getElem?_zipIdx, lookup]
      by_cases sameId : actualId = metadata
      · have expectedRep : MetadataRep registry (.constructor instantiation) metadata :=
          ⟨extended.lookup (SourceCoreRawMetadata.Registry.id?_reconstruct raw)⟩
        have sourceEq := SourceCoreRawMetadata.Metadata.constructor.inj ((fields.metadataRep.ids_equal_iff expectedRep).mp sameId)
        rw [sourceEq] at fields
        subst actualId
        have nativeTypes : actualTypes = coreTypes := Except.ok.inj (fields.payloads.projection.symm.trans (projectedList_catalog projectedChildren))
        subst actualTypes
        have lengths := CompatiblePayload.ValuesRep.length fields.payloads
        have length := lengths.2.2.symm.trans lengths.2.1
        cases ih _ _ _ fields.payloads with
        | inl success =>
          obtain ⟨bindings, boundValues, matched, bindingRep, childrenRun⟩ := success
          refine .inl ⟨bindings, boundValues,
            .constructor ⟨congrArg (·.constructor) sourceEq, congrArg (·.payloadTypes) sourceEq, congrArg (·.resultType) sourceEq⟩
              (lengths.1.symm.trans arity.symm) matched, bindingRep, ?_⟩
          intro environment store expression selected
          apply Evaluates.apply .lambda (selected.evaluates store)
          apply Evaluates.matchData (.var rfl) rfl branchLookup
          apply rawConstructor_matches
          have paths := projectionList_selects
            (environment := .pair (.word metadata) (packValues values) :: .constructed constructor (.pair (.word metadata) (packValues values)) :: environment)
            (expression := .second (.var 0)) (Selects.second (.var rfl)) length
          simpa [constructorPattern, Pattern.bindingTypes] using childrenRun _ store _ [] [] _ paths .nil
        | inr failed =>
          refine .inr ?_
          intro environment store expression selected
          apply Evaluates.apply .lambda (selected.evaluates store)
          apply Evaluates.matchData (.var rfl) rfl branchLookup
          apply rawConstructor_matches
          have paths := projectionList_selects
            (environment := .pair (.word metadata) (packValues values) :: .constructed constructor (.pair (.word metadata) (packValues values)) :: environment)
            (expression := .second (.var 0)) (Selects.second (.var rfl)) length
          simpa [constructorPattern, Pattern.bindingTypes] using failed _ store _ [] [] _ paths .nil
      · refine .inr ?_
        intro environment store expression selected
        apply Evaluates.apply .lambda (selected.evaluates store)
        apply Evaluates.matchData (.var rfl) rfl branchLookup
        exact rawConstructor_misses _ store actualId metadata sameId _ _ _
    · have indexDifferent : tag.index ≠ constructor.index := by
        intro indices
        apply sameTag
        cases tag; cases constructor; cases ownerEq; cases indices; rfl
      have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
          if index = constructor.index then rawConstructor metadata (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd))
            (matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children
              (coreTypes.zipIdx.map fun (item : Ty × Nat) => SourceCoreDataExpressions.projectPacked item.2 coreTypes (.second (.var 0))) [])
          else .inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit)[tag.index]? =
          some (.inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit) := by
        simp [List.getElem?_map, List.getElem?_zipIdx, lookup, indexDifferent]
      exact .inr (fun _ store _ selected => .apply .lambda (selected.evaluates store)
        (.matchData (.var rfl) ownerEq branchLookup (.inLeft .unit)))
  | nil =>
    intro sources values coreTypes represented
    cases represented
    exact .inl ⟨[], [], .nil, .nil, CompatiblePatternExecution.ChildrenRun.nil⟩
  | @cons type types instructions afterHead rest head tail headTree tailTree headIH tailIH =>
    intro sources values coreTypes represented
    cases represented with
    | cons valueRep valuesRep =>
      have sameType := Except.ok.inj (valueRep.projection.symm.trans (CompatiblePatternSuccess.Tree.projected headTree))
      subst sameType
      cases headIH _ _ valueRep with
      | inr failed => exact .inr (CompatiblePatternExecution.ChildrenFail.head failed)
      | inl success =>
        obtain ⟨headBindings, headValues, headMatch, headBindingRep, headRun⟩ := success
        have length : head.bindingTypes.length = headValues.length := by simpa [Pattern.bindingTypes] using bindings_length headBindingRep
        cases tailIH _ _ _ valuesRep with
        | inr failed => exact .inr (CompatiblePatternExecution.ChildrenFail.tail length headRun failed)
        | inl success =>
          obtain ⟨tailBindings, tailValues, tailMatch, tailBindingRep, tailRun⟩ := success
          exact .inl ⟨headBindings ++ tailBindings, headValues ++ tailValues, .cons headMatch tailMatch,
            bindings_append headBindingRep tailBindingRep, CompatiblePatternExecution.ChildrenRun.cons length headRun tailRun⟩

/-- Actual compatible compilation decides a represented input independently
of Core execution. Failure excludes every source binding sequence by success
preservation and native determinism, including raw guard mismatches. -/
theorem compilePattern_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern) (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store := by
  have certificate := certificate_of_compilePattern compilation compilationFuel source scope site span expected pattern compiled accepted
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context valid.signatures _ _ _ root
  cases Tree.decides valid extended tree sourceValue value represented with
  | inl success =>
    obtain ⟨bindings, values, matched, bindingRep, runs⟩ := success
    subst instructions
    exact ⟨.inRight .unit (packValues values), .matched (.intro sourceRep matched) bindingRep,
      runs (value :: environment) store (.var 0) (.var rfl)⟩
  | inr failed =>
    have evaluated := failed (value :: environment) store (.var 0) (.var rfl)
    refine ⟨.inLeft (bundleType compiled.pattern.bindingTypes) .unit, .noMatch (.intro sourceRep ?_), evaluated⟩
    subst instructions
    refine ⟨CompatiblePatternCertificates.Tree.skips tree, ?_⟩
    intro bindings matched
    obtain ⟨values, _, _, runs⟩ := CompatiblePatternSuccess.Tree.success catalogValid extended tree _ _ _ _ represented matched
    have impossible := (evaluation_deterministic evaluated (runs (value :: environment) store (.var 0) (.var rfl))).1
    cases impossible

/-- Any completed compatible matcher reconstructs an independent source match
or non-match and preserves the exact initial store. -/
theorem compilePattern_reflects (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern) (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    {environment : Environment} {store after : Store} {outcome : Value}
    (completed : Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome after) :
    OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧ after = store := by
  obtain ⟨predicted, meaning, evaluated⟩ := compilePattern_preserves compilation compilationFuel source scope site span expected
    pattern compiled accepted context valid catalogValid extended represented environment store
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic completed evaluated
  exact ⟨sameValue.symm ▸ meaning, sameStore⟩

/-- Enough machine fuel computes the independent outcome, and every completed
machine execution agrees with it. Compilation fuel is a separate parameter. -/
theorem compilePattern_run_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern) (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked registry functions mapping world context pattern compiled.pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done outcome store) ∧
      (∀ fuel actual after, runStateful fuel
        (.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done actual after →
        actual = outcome ∧ after = store) := by
  obtain ⟨outcome, meaning, evaluated⟩ := compilePattern_preserves compilation compilationFuel source scope site span expected
    pattern compiled accepted context valid catalogValid extended represented environment store
  exact ⟨outcome, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

/-- Every independent non-match preserves absence, with no candidate binding
bundle or allocation escaping the pure matcher. -/
theorem compilePattern_failure_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern) (compiled : CertifiedPattern compilation.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep compilation.checked registry functions mapping world expected sourceValue value compiled.pattern.type)
    (failure : Dynamic.PatternDoesNotMatch context pattern sourceValue) (environment : Environment) (store : Store) :
    Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0))
      (.inLeft (bundleType compiled.pattern.bindingTypes) .unit) store := by
  obtain ⟨outcome, meaning, evaluated⟩ := compilePattern_preserves compilation compilationFuel source scope site span expected
    pattern compiled accepted context valid catalogValid extended represented environment store
  cases meaning with
  | matched matched bindings => exact False.elim (failure.excludes matched)
  | noMatch => exact evaluated
end Solcore.SourceSemantics.CoreLowering.CompatiblePatternDecision
