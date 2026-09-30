import Solcore.SourceSemantics.CoreLowering.DataPatternAuthenticity

/-! Every accepted matcher decides the authenticated closed scalar/product/
nominal value profile. Both outcomes execute finitely without changing the
store; nested failures do not require evaluating the remaining children. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternDecision
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues DataPatternLeaves
open DataPatternExecution DataPatternSuccess DataPatternTypedValues DataPatternAuthenticity DataEquality

def MatcherFails (pattern : Pattern) (input : Value) : Prop :=
  ∀ environment store expression, Selects environment expression input →
    Evaluates environment store (.apply pattern.matcher expression)
      (.inLeft (bundleType pattern.bindingTypes) .unit) store

def ChildrenFail (patterns : List Pattern) (inputs : List Value) : Prop :=
  ∀ environment store expressions accumulated accumulatedValues outputType,
    ListRel (Selects environment) expressions inputs →
    ListRel (Selects environment) accumulated accumulatedValues →
    Evaluates environment store (matchChildren outputType patterns expressions accumulated)
      (.inLeft outputType .unit) store

theorem ChildrenFail.head {pattern : Pattern} {patterns : List Pattern} {input : Value} {inputs : List Value}
    (failed : MatcherFails pattern input) : ChildrenFail (pattern :: patterns) (input :: inputs) := by
  intro environment store expressions accumulated accumulatedValues outputType selected previous
  cases selected with
  | cons inputSelected restSelected => exact .caseLeft (failed _ _ _ inputSelected) (.inLeft .unit)

theorem ChildrenFail.tail {pattern : Pattern} {patterns : List Pattern} {input : Value}
    {inputs bindings : List Value} (length : pattern.bindingTypes.length = bindings.length)
    (head : MatcherRuns pattern input bindings) (tail : ChildrenFail patterns inputs) :
    ChildrenFail (pattern :: patterns) (input :: inputs) := by
  intro environment store expressions accumulated accumulatedValues outputType selected previous
  cases selected with
  | cons inputSelected restSelected =>
    apply Evaluates.caseRight (head environment store _ inputSelected)
    have projections := projectionList_selects (environment := packValues bindings :: environment)
      (expression := .var 0) (types := pattern.bindingTypes) (values := bindings) (.var rfl) length
    exact tail (packValues bindings :: environment) store _ _ _ outputType
      (selects_weaken_list restSelected _) (ListRel.append (selects_weaken_list previous _) projections)

def TreeDecision (compilation : Compilation) (context : Context) (type : TypeSystem.Ty)
    (instructions : List MatchPatternInstruction) (pattern : Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ source value, TypedValueRep compilation.checked.catalog compilation.signatures type source value →
    (∃ bindings values, Dynamic.PatternInstructionMatches context source instructions bindings rest ∧
      BindingsRep compilation.checked.catalog pattern.bindings bindings values ∧ MatcherRuns pattern value values) ∨
    MatcherFails pattern value

def ForestDecision (compilation : Compilation) (context : Context) (types : List TypeSystem.Ty)
    (instructions : List MatchPatternInstruction) (patterns : List Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ sources values, TypedValuesRep compilation.checked.catalog compilation.signatures types sources values →
    (∃ bindings boundValues, Dynamic.PatternInstructionsMatch context sources instructions bindings rest ∧
      BindingsRep compilation.checked.catalog (patterns.flatMap (·.bindings)) bindings boundValues ∧
      ChildrenRun patterns values boundValues) ∨ ChildrenFail patterns values

theorem Tree.decides {compilation : Compilation} {context : Context} {source : TypedSource}
    {site : StatementId} {span : Syntax.SourceSpan} {scope : Scope} {type : TypeSystem.Ty}
    {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (valid : ContextValid compilation context)
    (tree : Tree compilation source site span scope type instructions pattern rest) :
    TreeDecision compilation context type instructions pattern rest := by
  induction tree using Tree.rec
      (motive_2 := fun types instructions patterns rest _ => ForestDecision compilation context types instructions patterns rest) with
  | wildcard projection =>
    intro source value represented
    exact .inl ⟨[], [], .wildcard, .nil, fun _ store _ path =>
      .apply .lambda (path.evaluates store) (.inRight .unit)⟩
  | binder projection sourceType binderValid =>
    intro source value represented
    exact .inl ⟨[(_, source)], [value], .binder, .cons (TypedValueRep.erase represented) .nil,
      fun _ store _ path => .apply .lambda (path.evaluates store) (.inRight (.var rfl))⟩
  | @literal expected coreType literal resolution matcher rest projection validated =>
    intro sourceValue value represented
    have code := literalMatcher_sound compilation site span _ _ _ _ validated
    cases code with
    | word target meaning retained =>
      cases represented with
      | constructed nominal => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.word] at nominal
      | word actual =>
        by_cases same : actual = Word.ofNatModulo resolution.rawValue
        · subst actual
          exact .inl ⟨[], [], .integerLiteral (LiteralCode.constructs_word valid target meaning retained), .nil,
            fun _ store _ path => .apply .lambda (path.evaluates store)
              (.ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply])) (.inRight .unit))⟩
        · exact .inr (fun _ store _ path => .apply .lambda (path.evaluates store)
            (.ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, same])) (.inLeft .unit)))
    | integer target meaning retained =>
      cases represented with
      | constructed nominal => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.integer] at nominal
      | integer actual =>
        by_cases same : actual = Int.ofNat resolution.rawValue
        · subst actual
          exact .inl ⟨[], [], .integerLiteral (LiteralCode.constructs_integer valid target meaning retained), .nil,
            fun _ store _ path => .apply .lambda (path.evaluates store)
              (.ifTrue (.binary (.var rfl) .integer (by simp [BinaryOp.apply])) (.inRight .unit))⟩
        · exact .inr (fun _ store _ path => .apply .lambda (path.evaluates store)
            (.ifFalse (.binary (.var rfl) .integer (by
              simp only [BinaryOp.apply, Option.some.injEq, Value.bool.injEq, beq_eq_false_iff_ne]
              exact same)) (.inLeft .unit)))
  | @tuple expected coreType count types instructions rest children coreTypes projection unpacked childrenTree projectedChildren ih =>
    intro sourceValue value represented
    obtain ⟨sources, values, representations, packing, valueEq⟩ := TypedValueRep.unpack unpacked represented
    subst value
    have length := (projectionList_length projectedChildren).symm.trans (TypedValuesRep.length representations).2
    cases ih sources values representations with
    | inl success =>
      obtain ⟨bindings, boundValues, matched, bindingRep, childrenRun⟩ := success
      refine .inl ⟨bindings, boundValues, .tuple packing
        ((TypedValuesRep.length representations).1.symm.trans (unpackTypes_length unpacked)) matched, bindingRep, ?_⟩
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
  | @constructor expected coreType metadata count constructor definition instructions rest children coreTypes
      projection result arity resolved sameType childrenTree projectedChildren registered ih =>
    intro sourceValue value represented
    have nominalExpected : ∃ declaration arguments, SourceCoreDataCatalog.nominalParts expected = some (declaration, arguments) := by
      obtain ⟨signature, _, _, _, _, nominalResult, _⟩ := metadataFacts resolved
      rw [result] at nominalResult
      rw [nominalResult]
      exact ⟨_, _, nominalParts_nominal _ _⟩
    cases represented with
    | unit | bool | word | integer | product =>
      obtain ⟨_, _, impossible⟩ := nominalExpected
      simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.unit, TypeSystem.Ty.bool, TypeSystem.Ty.word, TypeSystem.Ty.integer] at impossible
    | @constructed actualType actual actualTag declaration arguments sourceArguments values nominal actualResult authenticated payloads =>
      have resultEq : actual.resultType = metadata.resultType := actualResult.trans result.symm
      have ownerEq : actualTag.owner = constructor.owner := by
        have first := constructor_identity (SourceCoreDataValues.resolveConstructor_lookup authenticated)
        have second := constructor_identity (SourceCoreDataValues.resolveConstructor_lookup resolved)
        rw [resultEq] at first
        exact Option.some.inj (first.symm.trans second)
      obtain ⟨payloadType, payloadLookup⟩ := SourceCoreDataValues.resolveConstructor_registered authenticated
      have lookup : definition.constructorPayloadTypes[actualTag.index]? = some payloadType := by
        simpa [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, ownerEq, registered] using payloadLookup
      by_cases same : actualTag = constructor
      · subst actualTag
        have agreement := resolveConstructor_agree authenticated resolved resultEq
        have payloads : TypedValuesRep compilation.checked.catalog compilation.signatures metadata.payloadTypes sourceArguments values := agreement.payload_types_eq ▸ payloads
        have length := (projectionList_length projectedChildren).symm.trans (TypedValuesRep.length payloads).2
        have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
            if index = constructor.index then matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children (childValues coreTypes) []
            else .inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit)[constructor.index]? =
            some (matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children (childValues coreTypes) []) := by
          simp [List.getElem?_map, List.getElem?_zipIdx, lookup]
        cases ih sourceArguments values payloads with
        | inl success =>
          obtain ⟨bindings, boundValues, matched, bindingsRep, childrenRun⟩ := success
          refine .inl ⟨bindings, boundValues, .constructor agreement ((TypedValuesRep.length payloads).1.symm.trans arity.symm) matched, bindingsRep, ?_⟩
          intro environment store expression selected
          apply Evaluates.apply .lambda (selected.evaluates store)
          apply Evaluates.matchData (.var rfl) rfl branchLookup
          have paths := projectionList_selects (environment := packValues values :: .constructed constructor (packValues values) :: environment) (expression := .var 0) (.var rfl) length
          simpa [constructorPattern, Pattern.bindingTypes, childValues] using childrenRun _ store _ [] [] _ paths .nil
        | inr failed =>
          refine .inr ?_
          intro environment store expression selected
          apply Evaluates.apply .lambda (selected.evaluates store)
          apply Evaluates.matchData (.var rfl) rfl branchLookup
          have paths := projectionList_selects (environment := packValues values :: .constructed constructor (packValues values) :: environment) (expression := .var 0) (.var rfl) length
          simpa [constructorPattern, Pattern.bindingTypes, childValues] using failed _ store _ [] [] _ paths .nil
      · have indexDifferent : actualTag.index ≠ constructor.index := by
          intro indices
          apply same
          cases actualTag; cases constructor; cases ownerEq; cases indices; rfl
        have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
            if index = constructor.index then matchChildren (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) children (childValues coreTypes) []
            else .inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit)[actualTag.index]? =
            some (.inLeft (bundleType ((children.flatMap (fun (p : Pattern) => p.bindings)).map Prod.snd)) .unit) := by
          simp [List.getElem?_map, List.getElem?_zipIdx, lookup, indexDifferent]
        exact .inr (fun _ store _ selected => .apply .lambda (selected.evaluates store)
          (.matchData (.var rfl) ownerEq branchLookup (.inLeft .unit)))
  | nil =>
    intro sources values represented
    cases represented
    exact .inl ⟨[], [], .nil, .nil, ChildrenRun.nil⟩
  | @cons type types instructions afterHead rest head tail headTree tailTree headIH tailIH =>
    intro sources values represented
    cases represented with
    | cons valueRep valuesRep =>
      cases headIH _ _ valueRep with
      | inr failed => exact .inr (ChildrenFail.head failed)
      | inl success =>
        obtain ⟨headBindings, headValues, headMatch, headBindingRep, headRun⟩ := success
        have length : head.bindingTypes.length = headValues.length := by
          simpa [Pattern.bindingTypes] using BindingsRep.length headBindingRep
        cases tailIH _ _ valuesRep with
        | inr failed => exact .inr (ChildrenFail.tail length headRun failed)
        | inl success =>
          obtain ⟨tailBindings, tailValues, tailMatch, tailBindingRep, tailRun⟩ := success
          exact .inl ⟨headBindings ++ tailBindings, headValues ++ tailValues, .cons headMatch tailMatch,
            BindingsRep.append headBindingRep tailBindingRep, ChildrenRun.cons length headRun tailRun⟩


/-- Actual compiler acceptance yields an independent source success or
non-match and finite execution of the emitted matcher. Nominal input metadata
is authenticated by TypedValueRep, rather than inferred from its Core type. -/
theorem compilePattern_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked.catalog context pattern compiled.pattern sourceValue outcome ∧
      Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0)) outcome store := by
  have certificate := certificate_of_compilePattern compilation compilationFuel source scope site span expected pattern compiled accepted
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context valid.signatures _ _ _ root
  cases Tree.decides valid tree sourceValue value represented with
  | inl success =>
    obtain ⟨bindings, values, matched, bindingRep, executes⟩ := success
    subst instructions
    exact ⟨.inRight .unit (packValues values), .matched (.intro sourceRep matched) bindingRep,
      executes _ store _ (.var rfl)⟩
  | inr failed =>
    have evaluation := failed (value :: environment) store (.var 0) (.var rfl)
    refine ⟨.inLeft (bundleType compiled.pattern.bindingTypes) .unit, .noMatch (.intro sourceRep ?_), evaluation⟩
    subst instructions
    refine ⟨DataPatternCertificates.Tree.skips tree, ?_⟩
    intro bindings matched
    obtain ⟨values, _, _, executes⟩ := DataPatternSuccess.Tree.success tree sourceValue value bindings []
      (TypedValueRep.erase represented) matched
    have impossible := (evaluation_deterministic evaluation (executes _ store _ (.var rfl))).1
    cases impossible

/-- Sufficient machine fuel returns the independent pattern outcome; every
completed run has that same outcome and exactly the original store. -/
theorem compilePattern_run_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value)
    (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep compilation.checked.catalog context pattern compiled.pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done outcome store) ∧
      (∀ fuel actual finalStore,
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) = .done actual finalStore →
        actual = outcome ∧ finalStore = store) := by
  obtain ⟨outcome, meaning, evaluates⟩ := compilePattern_preserves compilation compilationFuel source scope site span expected pattern compiled
    accepted context valid represented environment store
  exact ⟨outcome, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluates,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluates⟩


/-- In particular, an independently established source non-match evaluates to
absence. Candidate bindings stay lexical to the matcher until it succeeds. -/
theorem compilePattern_failure_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (valid : ContextValid compilation context)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value)
    (failed : Dynamic.PatternDoesNotMatch context pattern sourceValue)
    (environment : Environment) (store : Store) :
    Evaluates (value :: environment) store (.apply compiled.pattern.matcher (.var 0))
      (.inLeft (bundleType compiled.pattern.bindingTypes) .unit) store := by
  obtain ⟨outcome, meaning, evaluation⟩ := compilePattern_preserves compilation compilationFuel source scope site span expected pattern
    compiled accepted context valid represented environment store
  cases meaning with
  | matched matched => exact False.elim (failed.excludes matched)
  | noMatch => exact evaluation

end Solcore.SourceSemantics.CoreLowering.DataPatternDecision
