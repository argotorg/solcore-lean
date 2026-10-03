import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderPost
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime
import Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity
import Solcore.Test.SourceCoreRecursiveNamedProtectedHeaderBounds

/-! Runtime header conditions retain the entire ledger and the actual covering
entry. Concrete builtin certificates close expression meaning at every reached
child. Source costs and original native continuation costs remain independent.
The Header catalog and whole named profile are not weakened by this unit. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedForHeaderRuntimeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open CallableIndexedHistory (NativeFrame)
section Concrete
variable {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include definitions registered extension faithful observations runtimeViews unique uninitialized missing transport bindings in
theorem runtime_prefix_preserves (budget : Nat) {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop} {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => (CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)) ambient.definitions administrative type continuation
      context scope items code)
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (size : Nat) (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : ProtectedForHeader.TailFor (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  exact ProtectedForHeader.Tree.preserves_prefix_bounded_for functions definitions registered extension program evidence
    transport
    bindings
    faithful observations
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget
    (fun current currentValid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations runtimeViews
          program evidence currentValid.ledger currentValid.runtime unique uninitialized missing)) budget)
    tree valid environments heaps locals agrees actualTyped reference read unmapped installed trace bounded

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
theorem runtime_prefix_reflects (budget : Nat) {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop}
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => (CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)) ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (size : Nat) (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    RecursiveNamedHeaderContracts.ResultAtFor (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) size (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  exact ProtectedForHeader.Tree.reflects_reachable_bounded_for functions definitions registered extension program evidence
    transport
    bindings
    faithful observations
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget
    (fun current currentValid => RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations runtimeViews
          program evidence currentValid.ledger currentValid.runtime uninitialized missing)) budget)
    runtimeViews tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated bounded

variable {administrative : Core.Context} {type : Ty} {context : SourceSemantics.Context} {scope : Scope}
  {post : List ForItemForm} {postCode : Expr}
  (postTree : ProtectedForHeader.Tree layouts owner active frame globals onError values source
    (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
    ambient.definitions administrative type (TypedForHeader.Fallthrough type) context scope post postCode)
  (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {conditionCode bodyCode : Expr} {selfReason : Word}
  (agrees : EnvironmentsAgree ξ canonical actual)
  (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))

include definitions registered extension faithful observations runtimeViews unique uninitialized missing transport bindings postTree valid agrees reference in
theorem runtime_post_preserves (budget : Nat) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size =>
      RecursiveNamedForContracts.PostPreservesAt size functions program evidence
        (entry := entry)
        (source := source) (registry := registry) (administrative := administrative) (actualContext := actualContext) (frameLayout := frame)
        (context := context) (scope := scope) (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode) (body := bodyCode) (selfReason := selfReason) post postCode) := by
  intro size bounded mapping world before after store finalContext finalEnvironment state continued executed
  exact ProtectedForHeader.post_preserves_bounded_for (solved := solved) functions definitions registered extension program evidence
    transport
    bindings
    faithful observations
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget
    (fun current currentValid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations runtimeViews
          program evidence currentValid.ledger currentValid.runtime unique uninitialized missing)) budget)
    postTree valid agrees reference state continued executed bounded

include definitions registered extension faithful observations runtimeViews unique uninitialized missing transport bindings postTree postErrors valid agrees reference in
theorem runtime_post_faults (budget : Nat) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size =>
      RecursiveNamedForContracts.PostFaultsAt size functions program evidence
        (entry := entry) (faults := faults)
        (source := source) (registry := registry) (administrative := administrative) (actualContext := actualContext) (frameLayout := frame)
        (context := context) (scope := scope) (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode) (body := bodyCode) (selfReason := selfReason) post postCode) := by
  intro size bounded mapping world before after store finalContext reason state continued executed
  exact ProtectedForHeader.post_fault_reachable_bounded_for functions definitions registered extension program evidence
    transport
    bindings
    faithful observations
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget
    (fun current currentValid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations runtimeViews
          program evidence currentValid.ledger currentValid.runtime unique uninitialized missing)) budget)
    postTree postErrors valid agrees reference state continued executed bounded

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings postTree postErrors valid agrees reference in
theorem runtime_post_reflects (budget : Nat) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size =>
      RecursiveNamedForContracts.PostReflectsAt size functions program evidence
        (entry := entry)
        (source := source) (registry := registry) (administrative := administrative) (actualContext := actualContext) (frameLayout := frame)
        (context := context) (scope := scope) (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode) (body := bodyCode) (selfReason := selfReason) faults post postCode) := by
  intro size bounded mapping world before store finalStore value state continued executed
  exact ProtectedForHeader.post_reflects_reachable_bounded_for (solved := solved) functions definitions registered extension program evidence
    transport
    bindings
    faithful observations
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget
    (fun current currentValid => RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations runtimeViews
          program evidence currentValid.ledger currentValid.runtime uninitialized missing)) budget)
    runtimeViews postTree postErrors valid agrees reference state continued executed bounded
end Concrete

section Continuation
variable {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {program : SourceSemantics.Program}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {solved : List SolvedRequirement}
  {administrative : Core.Context} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {registry : SourceCoreRawMetadata.Registry} {type : Core.Ty} {faults : FunctionCalls.FaultRep}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
  {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {contextLocation : Location} {native : NativeFrame} {value : Core.Value} {finalStore : Store}
  {items : List ForItemForm} {size budget : Nat}
  {meaning : Nat → SourceSemantics.Context → Scope → Expr → Prop}

/-- Initializers select the continuation at its original inclusive native
size; the independently reconstructed source prefix is never bounded by it. -/
theorem continuation_at_remaining
    (receipt : RecursiveNamedHeaderContracts.ResultAtFor (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) size (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults
      (RecursiveNamedHeaderContracts.ContinuationWithin budget meaning) context environment heap items mapping world store value finalStore)
    (bounded : size ≤ budget) :
    (∃ sourceSize finalContext reason after,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment heap items finalContext reason after) ∨
    (∃ sourceSize finalContext finalEnvironment after,
      ∃ tail : ProtectedForHeader.TailFor (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native
        (RecursiveNamedHeaderContracts.ContinuationWithin budget meaning) finalContext finalEnvironment after,
      ∃ remainingSize, SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment heap items finalContext finalEnvironment after ∧
      remainingSize ≤ size ∧ remainingSize ≤ budget ∧
      EvaluationSize remainingSize tail.actual tail.store (tail.code.rename tail.embedding) value finalStore ∧
      meaning remainingSize finalContext tail.scope tail.code ∧ entry tail.scope tail.mapping tail.world after tail.store tail.canonical) := by
  cases receipt with
  | fault trace _ _ _ _ _ _ _ => exact .inl ⟨_, _, _, _, trace⟩
  | continues tail trace _ _ _ _ remaining smaller =>
    exact .inr ⟨_, _, _, _, tail, _, trace, smaller, Nat.le_trans smaller bounded, remaining,
      RecursiveNamedHeaderContracts.tail_at_remaining_for tail smaller bounded, tail.installed⟩

/-- An empty initializer keeps the exact same native witness and inclusive
bound. A strict-only continuation family would exclude this case. -/
theorem empty_continuation
    (tail : ProtectedForHeader.TailFor (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native
      (RecursiveNamedHeaderContracts.ContinuationWithin size meaning) context environment heap)
    (evaluated : EvaluationSize size tail.actual tail.store (tail.code.rename tail.embedding) value finalStore) :
    RecursiveNamedHeaderContracts.ResultAtFor (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) size (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults
      (RecursiveNamedHeaderContracts.ContinuationWithin size meaning) context environment heap [] tail.mapping tail.world tail.store value finalStore ∧
    meaning size context tail.scope tail.code ∧ ¬ size < size :=
  ⟨.nil tail evaluated, RecursiveNamedHeaderContracts.tail_at_remaining_for tail (Nat.le_refl _) (Nat.le_refl _), Nat.lt_irrefl _⟩
end Continuation

section Boundary
variable {solved : List SolvedRequirement} {context next : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {owner : Resolved.DeclarationId} {binder : TypedBinder}

/-- The actual binder relation transports all runtime rows and coverage. -/
theorem runtime_extend (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
    (extended : BinderExtends owner context binder next) :
    CompatibleRuntimeContextValidity.Valid solved next evidence := valid.extend extended

/-- Unused and repeated occurrences are retained in the same complete ledger. -/
theorem full_ledger {row : SolvedRequirement}
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence) (member : row ∈ solved) :
    row ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
end Boundary

section OrdinaryBoundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def context : SourceSemantics.Context := (Context.ofSignatures signatures).withSolvedRequirements [row]

/-- Runtime tails cannot be erased into a false ordinary-ledger premise. -/
theorem runtime_not_ordinary :
    CompatibleRuntimeContextValidity.Valid [row] context [] ∧
      ¬ CompatibleExpressionLiterals.ContextValid [row] context [] := by
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · change ([⟨0⟩] : List RequirementId).Nodup; decide
    · intro item evidence member implementation
      have same : item = row := by simpa [context, Context.withSolvedRequirements] using member
      subst item
      cases implementation
  · constructor
    · intro predicate evidence found; cases found
    · intro predicate member; cases member
  · intro ordinary
    have valid := ordinary.valid.entriesValid row (by simp [context, Context.withSolvedRequirements])
    cases valid with
    | intro retained =>
      cases retained with
      | intro represents valid =>
        cases represents
        cases valid with
        | assumption member => cases member
end OrdinaryBoundary

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- Actual template-bearing headers are compiled unchanged. This exercises
only their reached Bool children; the enclosing qualified callable is not
claimed to compile. Post executions retain the actual six loop temporaries. -/
private def template_headers : IO Unit := do
  let program ← get "runtime header template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " for (let initialized = false, initialized = true, initialized; false; let changed = true, changed = false, changed) {}",
      " for (let missing: Bool, missing; false;) {}",
      " for (; false; let missing: Bool, missing) {}",
      " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "header template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "header template body missing")
  let specialized ← get "header template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := specialized.function.typedBody
  let ledger := specialized.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger.map (·.id) == generic.solvedRequirements.map (·.id))
    "header template full ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !specialized.assumptions.contains predicate)
          "header template assumption promoted"
      | _ => throw (IO.userError "header template implementation fabricated")
    | _ => throw (IO.userError "header template row missing or duplicated")
  let roots := source.roots.filterMap fun
    | .statement id => (source.lookupStatement? id).bind fun node => match node.form with
      | .forLoop _ _ _ _ => some node | _ => none
    | _ => none
  require (roots.length == 3) "header template actual loop count"
  let policy : SourceCoreLoops.Policy := {lowerExpression := SourceCoreControl.lowerExpressionWithReasons}
  let reason := Word.ofNatModulo 877
  let captured := Core.Value.closure .word .word (.var 0) [.word (Word.ofNatModulo 881)]
  let before : Store := [.integer (-883), captured, .inLeft (LocalLoop.functionType .unit) .unit]
  for (node, index) in roots.zipIdx do
    match node.form with
    | .forLoop initializers _ post _ =>
      for (items, isPost) in [(initializers, false), (post, true)] do
        let code ← get "runtime actual header accepted"
          (SourceCoreLoops.lowerForItems policy (.occurrence node.id.occurrence) 300 source [] items .unit
            (fun _ => reason) (fun _ => .ok (LocalLoop.fallthrough .unit)))
        require (Core.infer? [] code [] == some (LocalLoop.resultType .unit)) "runtime bare header type"
        let fault := (index == 1 && !isPost) || (index == 2 && isPost)
        let cells : List Core.Value := if index == 0 then [.inRight .unit (.bool (!isPost))]
          else if fault then [.inLeft .bool .unit] else []
        let expected : Core.Value := if fault then .inLeft (LocalLoop.controlType .unit) (.word reason)
          else LocalLoop.fallthroughValue .unit
        for continued in [false, true] do
          let actual := if isPost then TypedImperativeFor.postValues .unit 2 continued ++ [captured] else [captured]
          let issued := if isPost then ForLoop.postCode code else code
          require (!isPost || (TypedImperativeFor.postValues .unit 2 continued).length == 6) "post actual six slots"
          for fuel in [0, 1, 23, 10000] do
            let first := Core.runStateful fuel (.initial issued actual before)
            let completed := match first with
              | .outOfFuel state => Core.runStateful 10000 state | other => other
            match completed with
            | .done value after =>
              require (value == expected && after == before ++ cells) "runtime header complete result/store/resume"
            | other => throw (IO.userError s!"runtime header unfinished {reprStr other}")
    | _ => throw (IO.userError "header template loop changed")

def run : IO Unit := do
  template_headers
  SourceCoreRecursiveNamedProtectedHeaderBounds.run
  IO.println "runtime header/post: concrete supported builtin children / full template ledger / original continuation bounds / actual six slots / complete cells and resume GREEN"

end Tests.SourceCoreRecursiveNamedForHeaderRuntimeBounds
