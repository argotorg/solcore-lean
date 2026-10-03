import Solcore.SourceSemantics.CoreLowering.CompatibleMatchRuntimeHead
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
import Solcore.SourceSemantics.CoreLowering.ProtectedLexicalStatementControl
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Concrete literal scrutinees and empty request bodies close the pointwise
interfaces of the runtime match head. The parent typing, actual compiler
certificate, allocation/frame authority and independent source semantics stay
explicit. Public runtime fixtures also exercise nonempty selected bodies. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleMatchRuntimeHead
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates GenericMatchChildren
open TypedLexicalWhile (ValuesContext)
open RecursiveNamedLoopContracts (PreservesAtFor ReflectsAtFor)

section EmptyBody
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} {frame : SourceCoreCallableIndexedFrames.Layout}
  {globals : Nat} {administrative : Core.Context} {scope : Scope} {expected : TypeSystem.Ty} {type : Ty}

/-- The empty body closes at every original source grade and every predicate. -/
theorem empty_preserves_at (validity : SourceSemantics.Context → Prop) (size : Nat) :
    PreservesAtFor functions program evidence validity (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      (administrative := administrative) (scope := scope) size false [] expected type (LocalLoop.fallthrough type) := by
  intro _ mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals _ _ _ _ _ _ trace
  cases trace with
  | control executed =>
    obtain ⟨rfl, rfl, rfl⟩ := ScalarStatementViews.nil_view false executed.sound
    exact ⟨_, store, mapping, world, LocalLoop.fallthrough_evaluates _ _ _, .fallthrough environment,
      heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩
  | fault failed => exact False.elim (ScalarStatementViews.nil_cannot_fault false failed.sound)

/-- Reflection keeps the native grade and constructs a separate source grade. -/
theorem empty_reflects_at (validity : SourceSemantics.Context → Prop) (size : Nat) :
    ReflectsAtFor functions program evidence validity (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      (administrative := administrative) (scope := scope) size false [] expected type (LocalLoop.fallthrough type) := by
  intro _ mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals _ _ _ _ _ _ evaluated
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.fallthrough_evaluates type actual store)
  have original := ProtectedLexicalStatements.nil_executes false program context evidence source environment before
  obtain ⟨sourceSize, trace⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size original
  exact ⟨sourceSize, context, _, before, mapping, world, trace, .fallthrough environment, heaps,
    .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩
end EmptyBody

section Concrete
variable {compilation : SourceCoreCompatibleDataMatches.Context}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends compilation.values.registry registry)
  {source : TypedSource} {context : SourceSemantics.Context} {control : ControlContext}
  {program : SourceSemantics.Program} {evidence : Dynamic.EvidenceEnvironment} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {solved : List SolvedRequirement} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
    (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved source id lowered) (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (signatures : context.signatures = compilation.signatures)
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
  (sameLedger : compilation.solvedRequirements = solved) {administrative : Core.Context} {faults : FunctionCalls.FaultRep}

  (emptyRequests : ∀ request ∈ requests, request.statements = [] ∧ request.code = LocalLoop.fallthrough type)

include allocator definitions registered extension ordinary signatures sameLedger catalogValid found casesTyped defaultTyped emptyRequests in
theorem concrete_preserves_at (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size ≤ budget) {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry) :
    RecursiveNamedMatchSourceBounds.Head.HeadPreservesAtFor (entry := entry) functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (values := compilation.values) (source := source)
      (context := context) (registry := registry) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) size (scope := scope) id expected type code := by
  apply CompatibleMatchRuntimeHead.head_preserves_bounded onError allocator functions definitions registered extension
    receipt ordinary signatures catalogValid found casesTyped defaultTyped sameLedger unique budget size bounded transport bindings
  · intro valid child smaller
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (TypedGenericExpressionMeaning.preserves_of_unrestricted
          (CompatibleExpressionLiteralRuntime.preserves functions program context evidence valid.ledger valid.runtime unique faults))) child
  · intro request member childContext related child smaller
    obtain ⟨statements, nativeCode⟩ := emptyRequests request member
    rw [statements, nativeCode]
    exact empty_preserves_at functions program evidence _ child

include allocator definitions registered extension ordinary signatures sameLedger catalogValid found casesTyped defaultTyped emptyRequests in
theorem concrete_reflects_at (budget size : Nat) (bounded : size ≤ budget) {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry) :
    RecursiveNamedMatchSourceBounds.Head.HeadReflectsAtFor (entry := entry) functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (values := compilation.values) (source := source)
      (context := context) (registry := registry) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) size (scope := scope) id expected type code := by
  apply CompatibleMatchRuntimeHead.head_reflects_bounded onError allocator functions definitions registered extension
    receipt ordinary signatures catalogValid found casesTyped defaultTyped sameLedger budget size bounded transport bindings
  · intro valid child smaller
    exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (TypedGenericExpressionMeaning.reflects_of_unrestricted
          (CompatibleExpressionLiteralRuntime.reflects functions program context evidence valid.ledger valid.runtime source faults))) child
  · intro request member childContext related child smaller
    obtain ⟨statements, nativeCode⟩ := emptyRequests request member
    rw [statements, nativeCode]
    exact empty_reflects_at functions program evidence _ child

end Concrete

section Frame
variable {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
  {types : List TypeSystem.Ty} {solved : List SolvedRequirement}

/-- The real frame supplies the same complete dictionary and ledger, with no
empty-template or ordinary-validity condition. -/
theorem frame_runtime_valid
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved) :
    CompatibleRuntimeContextValidity.Valid solved context function.evidence :=
  CompatibleRuntimeContextValidity.of_frame frame extended programTyped sameLedger

/-- Every retained row, including an unused template, is kept by the consumer. -/
theorem full_ledger_retained {row : SolvedRequirement}
    (valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence) (member : row ∈ solved) :
    row ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
end Frame

section Boundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def context : SourceSemantics.Context := (Context.ofSignatures signatures).withSolvedRequirements [row]

/-- Runtime validity cannot supply the old ordinary premise for an unused row. -/
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
end Boundary

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)

/-- A real template-bearing source retains every row while the actual literal
scrutinee compiler and empty-body compiler lower this reached Match head.
The enclosing qualified lambda/function compilation is not claimed. -/
private def template_head : IO Unit := do
  let program ← get "runtime head template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " match (61) { case 61 {} default {} }",
      " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "head template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "head template function missing")
  let actual ← get "head template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger.map (·.id) == generic.solvedRequirements.map (·.id))
    "head template IDs or complete ordered ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !actual.assumptions.contains predicate)
          "head template assumption promoted"
      | _ => throw (IO.userError "head template implementation fabricated")
    | _ => throw (IO.userError "head template row missing/duplicated")
  let checked ← get "head template catalog" (SourceCoreCompatibleCatalog.prepare program.signatures 100 [.word, .bool])
  let compilation : SourceCoreCompatibleDataMatches.Context := ⟨.initial checked, ledger, none, none⟩
  let functions : SourceCoreFunctions.Context := {
    plan := ⟨[actual.key], [actual], [], []⟩,
    owner := actual.key, globals := [], administrativePrefix := 1, solvedRequirements := ledger, internalReason := Word.zero}
  let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .error (.traversalExhausted (.declaration actual.function.declaration))
  let expression : ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithReasons noBody fuel functions source scope id reasonAt
  let body : BodyLowerer := fun _ _ _ statements type _ _ =>
    if statements.isEmpty then .ok (LocalLoop.fallthrough type) else .error (.traversalExhausted (.declaration actual.function.declaration))
  let mut count := 0
  for node in source.nodes do
    match node with
    | .statement statement => match statement.form with
      | .matchWith resolution =>
        match accepted : lowerWithReasons compilation expression body 100 source [] statement.id resolution
            .unit (fun _ => Word.zero) Word.zero with
        | .error error => throw (IO.userError s!"head template lowering {reprStr error}")
        | .ok code =>
          have receipt := certificate_of_lowerWithReasons (expressionCertificate := fun _ _ _ => True)
            (bodyCertificate := fun _ _ _ => True) (fun _ _ _ _ _ => True.intro) (fun _ _ _ _ _ => True.intro) accepted
          have sites := CompatibleMatchRuntimeSelection.of_certificate receipt
          let _sites := sites
          require (Core.infer? [] code compilation.definitions == some (LocalLoop.resultType .unit)) "head actual type"
          let before : Core.Store := [.integer 977, .closure .unit .integer (.var 1) [.integer 983], .cellRef .integer 0]
          for fuel in [0, 1, 19, 10000] do
            let done := match Core.runStateful fuel (.initial code [] before) with
              | .outOfFuel state => Core.runStateful 10000 state | other => other
            match done with
            | .done value after =>
              require (value == LocalLoop.fallthroughValue .unit &&
                after == before ++ [.inRight .unit (.word (Word.ofNatModulo 61))]) "head template full native store/result"
            | other => throw (IO.userError s!"head template unfinished {reprStr other}")
          count := count + 1
      | _ => pure ()
    | _ => pure ()
  require (count == 1) "head template occurrence count"

private def content : String := String.intercalate "\n" [
  "function empty() returns (Word) { match (37) { case 37 {} default {} } return 41; }",
  "function bound() returns (Word) { match (9) { case binding {} } return 43; }",
  "function integerHead(value: integer) returns (Word) { match (value) { case 73 {} default {} } return 47; }",
  "function selected(a: Word, b: Word) returns (Word) { match ((a, b)) { case (37, chosen) { return chosen; } case (left, right) { return left + right; } } }",
  "function faultArm() returns (Word) { match (37) { case 37 { let prior: Word = 41; let missing: Word; return missing; } default { return 19; } } }",
  "function faultScrutinee() returns (Word) { let missing: Word; match (missing) { case 0 { return 23; } default { return 29; } } }"
]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "head public resume" (first.resume 300000)).observation

def run : IO Unit := do
  template_head
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "runtime whole match head" content
    ["empty", "bound", "integerHead", "selected", "faultArm", "faultScrutinee"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (word 991)⟩]}
  let cases : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("empty", [], word 41, [(.word, some (word 37))]),
    ("bound", [], word 43, [(.word, some (word 9)), (.word, some (word 9))]),
    ("integerHead", [.integer 73], word 47, [(.integer, some (.integer 73)), (.integer, some (.integer 73))]),
    ("integerHead", [.integer 74], word 47, [(.integer, some (.integer 74)), (.integer, some (.integer 74))]),
    ("selected", [word 37, word 8], word 8, [(.word, some (word 37)), (.word, some (word 8)), (.product .word .word, some (.product (word 37) (word 8))), (.word, some (word 8))]),
    ("selected", [word 38, word 8], word 46, [(.word, some (word 38)), (.word, some (word 8)), (.product .word .word, some (.product (word 38) (word 8))), (.word, some (word 38)), (.word, some (word 8))])]
  for (name, arguments, expected, cells) in cases do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 1, 19, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) "head success resume changed"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected &&
          reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"head public full source cells {name}"
      | other => throw (IO.userError s!"head success expected {reprStr other}")
  let failures : List (String × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("faultArm", [(.word, some (word 37)), (.word, some (word 41)), (.word, none)]),
    ("faultScrutinee", [(.word, none)])]
  for (name, cells) in failures do
    let named ← match compiled.indexed.base.functions.find? (fun named =>
        compiled.sourceProgram.signatures.functions.any (fun signature => signature.id == named.specialized.function.declaration && signature.name == name)) with
      | some named => pure named | none => throw (IO.userError "head source function missing")
    let missing ← match (SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
      | [binder] => pure binder.id | _ => throw (IO.userError "head missing binder identity")
    let baseline ← finish compiled name [] 300000 initial
    for fuel in [0, 1, 19, 300000] do
      let observed ← finish compiled name [] fuel initial
      require (reprStr observed == reprStr baseline) "head fault resume changed"
      match observed with
      | .fault (.uninitializedLocal found) final =>
        require (found == missing &&
          reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          "head first fault/full ordered cells"
      | other => throw (IO.userError s!"head fault expected {reprStr other}")
  IO.println "runtime whole match head: literal/empty concrete meaning / actual template full ledger / first and later arm/default / independent strict sizes / full cells and original fault / resume GREEN"

end Tests.SourceCoreCompatibleMatchRuntimeHead
