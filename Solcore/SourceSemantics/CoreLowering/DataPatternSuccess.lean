import Solcore.SourceSemantics.CoreLowering.DataPatternExecution
import Solcore.Frontend.SourceCoreDataValues
import Solcore.SourceSemantics.Dynamic.PatternCompletenessProperties
import Solcore.Core.Correspondence

/-! Independent successful source matching implies finite execution of the
actual compiled matcher, including arbitrary finite nominal/tuple nesting.
Constructor metadata agreement is supplied by Dynamic.PatternMatches and the
compiler authenticates the selected pattern constructor against its catalog. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternSuccess
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues DataPatternLeaves DataPatternExecution DataEquality

theorem projectionList_length {compilation : Compilation} {source : TypedSource}
    {types : List TypeSystem.Ty} {coreTypes : List Ty}
    (projected : types.mapM (SourceCoreDataMatches.projected compilation source) = .ok coreTypes) :
    types.length = coreTypes.length := by
  induction types generalizing coreTypes with
  | nil => simp [List.mapM_nil, pure, Except.pure] at projected; subst coreTypes; rfl
  | cons type types ih =>
    cases first : SourceCoreDataMatches.projected compilation source type with
    | error error => simp [List.mapM_cons, first, bind, Except.bind] at projected
    | ok coreType =>
      cases rest : types.mapM (SourceCoreDataMatches.projected compilation source) with
      | error error => simp [List.mapM_cons, first, rest, bind, Except.bind] at projected
      | ok tail =>
        simp [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure] at projected
        subst coreTypes
        simp [ih rest]

private theorem constructorLookup_agrees {catalog : SourceCoreDataCatalog.Catalog}
    {actual expected : DataConstructorInstantiation}
    (agree : Dynamic.ConstructorInstantiationsAgree actual expected) :
    catalog.constructor? actual = catalog.constructor? expected := by
  simp [SourceCoreDataCatalog.Catalog.constructor?, agree.constructor_eq, agree.result_type_eq]

private theorem literal_success {compilation : Compilation} {context : Context}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution} {expected : TypeSystem.Ty}
    {matcher : Expr} {source : Dynamic.Value} {value : Value} (type : Ty)
    (code : LiteralCode compilation literal resolution expected matcher)
    (constructed : Dynamic.ResolvedIntegerLiteralConstructs context literal resolution source)
    (represented : ValueRep compilation.checked.catalog source value) :
    MatcherRuns ⟨type, [], [resolution.requirement], matcher⟩ value [] := by
  cases constructed with
  | word meaning evidence =>
    cases code with
    | word target numeric retained =>
      cases represented
      intro environment store expression selected
      exact .apply .lambda (selected.evaluates store)
        (.ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply])) (.inRight .unit))
    | integer target => cases target
  | integer meaning evidence =>
    cases code with
    | word target => cases target
    | integer target numeric retained =>
      cases represented
      intro environment store expression selected
      exact .apply .lambda (selected.evaluates store)
        (.ifTrue (.binary (.var rfl) .integer (by simp [BinaryOp.apply])) (.inRight .unit))

/-- A successful source prefix can be consumed only over the same suffix as
the compiler certificate. The binder bundle remains ordered and unmodified. -/
def TreeSuccess (compilation : Compilation) (context : Context)
    (instructions : List MatchPatternInstruction) (pattern : Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ source value bindings sourceRest,
    ValueRep compilation.checked.catalog source value →
    Dynamic.PatternInstructionMatches context source instructions bindings sourceRest →
    ∃ values, sourceRest = rest ∧ BindingsRep compilation.checked.catalog pattern.bindings bindings values ∧
      MatcherRuns pattern value values

def ForestSuccess (compilation : Compilation) (context : Context) (types : List TypeSystem.Ty)
    (instructions : List MatchPatternInstruction) (patterns : List Pattern) (rest : List MatchPatternInstruction) : Prop :=
  ∀ sources values bindings sourceRest,
    ValuesRep compilation.checked.catalog sources values →
    sources.length = types.length →
    Dynamic.PatternInstructionsMatch context sources instructions bindings sourceRest →
    ∃ boundValues, sourceRest = rest ∧
      BindingsRep compilation.checked.catalog (patterns.flatMap (·.bindings)) bindings boundValues ∧
      ChildrenRun patterns values boundValues

theorem Tree.success {compilation : Compilation} {context : Context} {source : TypedSource}
    {site : StatementId} {span : Syntax.SourceSpan} {scope : Scope} {type : TypeSystem.Ty}
    {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (tree : Tree compilation source site span scope type instructions pattern rest) :
    TreeSuccess compilation context instructions pattern rest := by
  induction tree using Tree.rec
      (motive_2 := fun types instructions patterns rest _ => ForestSuccess compilation context types instructions patterns rest) with
  | wildcard projection =>
    intro source value bindings sourceRest represented matched
    cases matched
    refine ⟨[], rfl, .nil, ?_⟩
    intro environment store expression selected
    exact .apply .lambda (selected.evaluates store) (.inRight .unit)
  | binder projection sourceType valid =>
    intro source value bindings sourceRest represented matched
    cases matched
    refine ⟨[value], rfl, .cons represented .nil, ?_⟩
    intro environment store expression selected
    exact .apply .lambda (selected.evaluates store) (.inRight (.var rfl))
  | literal projection validated =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | integerLiteral construction =>
      exact ⟨[], rfl, .nil,
        literal_success _ (literalMatcher_sound compilation site span _ _ _ _ validated) construction represented⟩
  | @tuple expected coreType count types instructions rest children coreTypes projection unpacked childrenTree projectedChildren ih =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | tuple packed arity matchedChildren =>
      obtain ⟨values, valuesRep, valueEq⟩ := ValueRep.unpack packed represented
      subst value
      obtain ⟨boundValues, restEq, bindingRep, childrenRun⟩ :=
        ih _ _ _ _ valuesRep (arity.trans (unpackTypes_length unpacked).symm) matchedChildren
      refine ⟨boundValues, restEq, bindingRep, ?_⟩
      intro environment store expression selected
      apply Evaluates.apply .lambda (selected.evaluates store)
      have length : coreTypes.length = values.length :=
        (projectionList_length projectedChildren).symm.trans
          ((unpackTypes_length unpacked).trans (arity.symm.trans valuesRep.length))
      have paths := projectionList_selects (environment := packValues values :: environment)
        (expression := .var 0) (.var rfl) length
      simpa [tuplePattern, childValues] using
        childrenRun (packValues values :: environment) store _ [] [] _ paths .nil
  | @constructor expected coreType instantiation count constructor definition instructions rest children coreTypes
      projection result arity resolved sameType childrenTree projectedChildren registered ih =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | constructor agree countEq matchedChildren =>
      cases represented with
      | @constructed actual tag arguments values selected payloads =>
        have tagEq : _ = some constructor := (constructorLookup_agrees agree).trans
          (SourceCoreDataValues.resolveConstructor_lookup resolved)
        rw [selected] at tagEq
        cases tagEq
        obtain ⟨boundValues, restEq, bindingRep, childrenRun⟩ :=
          ih _ _ _ _ payloads (countEq.trans arity) matchedChildren
        refine ⟨boundValues, restEq, bindingRep, ?_⟩
        intro environment store expression selectedValue
        apply Evaluates.apply .lambda (selectedValue.evaluates store)
        obtain ⟨payloadType, payloadLookup⟩ := SourceCoreDataValues.resolveConstructor_registered resolved
        have lookup : definition.constructorPayloadTypes[constructor.index]? = some payloadType := by
          simpa [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, registered] using payloadLookup
        have branchLookup : (definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
            if index = constructor.index then matchChildren (bundleType ((children.flatMap (·.bindings)).map Prod.snd)) children (childValues coreTypes) []
            else .inLeft (bundleType ((children.flatMap (·.bindings)).map Prod.snd)) .unit)[constructor.index]? =
            some (matchChildren (bundleType ((children.flatMap (·.bindings)).map Prod.snd)) children (childValues coreTypes) []) := by
          simp [List.getElem?_map, List.getElem?_zipIdx, lookup]
        apply Evaluates.matchData (.var rfl) rfl branchLookup
        have length := (projectionList_length projectedChildren).symm.trans ((countEq.trans arity).symm.trans payloads.length)
        have paths := projectionList_selects
          (environment := packValues values :: .constructed constructor (packValues values) :: environment)
          (expression := .var 0) (Selects.var rfl) length
        simpa [constructorPattern, childValues] using childrenRun _ store _ [] [] _ paths .nil
  | nil =>
    intro sources values bindings sourceRest represented length matched
    have empty : sources = [] := by simpa using length
    subst sources
    cases represented
    cases matched
    exact ⟨[], rfl, .nil, ChildrenRun.nil⟩
  | @cons type types instructions afterHead rest head tail headTree tailTree headIH tailIH =>
    intro sources values bindings sourceRest represented length matched
    cases represented with
    | nil => simp at length
    | cons valueRep valuesRep =>
      cases matched with
      | cons headMatch tailMatch =>
        obtain ⟨headValues, headRestEq, headBindings, headRun⟩ := headIH _ _ _ _ valueRep headMatch
        subst headRestEq
        obtain ⟨tailValues, tailRestEq, tailBindings, tailRun⟩ := tailIH _ _ _ _ valuesRep (Nat.succ.inj length) tailMatch
        exact ⟨headValues ++ tailValues, tailRestEq, BindingsRep.append headBindings tailBindings,
          ChildrenRun.cons (by simpa [Pattern.bindingTypes] using BindingsRep.length headBindings) headRun tailRun⟩


/-- Accepted compilation preserves every independently derived successful
source match in the scalar/product/nominal value profile. No child evaluator
correctness premise is required. -/
theorem compilePattern_success_preserves (compilation : Compilation) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled)
    (context : Context) (signatures : context.signatures = compilation.signatures)
    {sourceValue : Dynamic.Value} {value : Value} {bindings : List (TypedBinder × Dynamic.Value)}
    (represented : ValueRep compilation.checked.catalog sourceValue value)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings) :
    ∃ values, BindingsRep compilation.checked.catalog compiled.pattern.bindings bindings values ∧
      MatcherRuns compiled.pattern value values := by
  have certificate := certificate_of_compilePattern compilation fuel source scope site span expected pattern compiled accepted
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  cases matched with
  | intro matchedSource instructionMatch =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep matchedSource
    subst arityEq
    subst instructions
    obtain ⟨values, _, bindingsRep, evaluates⟩ := Tree.success tree sourceValue value bindings [] represented instructionMatch
    exact ⟨values, bindingsRep, evaluates⟩

/-- The actual machine eventually returns the ordered successful binder bundle;
any completed run returns that same bundle and the unchanged input store. -/
theorem compilePattern_success_run (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (signatures : context.signatures = compilation.signatures)
    {sourceValue : Dynamic.Value} {value : Value} {bindings : List (TypedBinder × Dynamic.Value)}
    (represented : ValueRep compilation.checked.catalog sourceValue value)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings)
    (environment : Environment) (store : Store) :
    ∃ values, BindingsRep compilation.checked.catalog compiled.pattern.bindings bindings values ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) =
          .done (.inRight .unit (packValues values)) store) ∧
      (∀ fuel outcome finalStore,
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (value :: environment) store) =
          .done outcome finalStore → outcome = .inRight .unit (packValues values) ∧ finalStore = store) := by
  obtain ⟨values, bindingsRep, executes⟩ := compilePattern_success_preserves compilation compilationFuel
    source scope site span expected pattern compiled accepted context signatures represented matched
  have evaluation := executes (value :: environment) store (.var 0) (.var rfl)
  exact ⟨values, bindingsRep, evaluation_runStateful_complete_with_sufficient_fuel evaluation,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluation⟩

end Solcore.SourceSemantics.CoreLowering.DataPatternSuccess
