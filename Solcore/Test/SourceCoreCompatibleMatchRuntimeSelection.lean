import Solcore.SourceSemantics.CoreLowering.CompatibleMatchRuntimeSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedInitialContextValidity
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Ordered accepted arm receipts supply runtime numeric support without a
whole ordinary ledger. Formal prefixes retain the original strict continuation;
callback-marker runtime tests exercise actual lowering and ordered selection.
They do not claim source meaning for arbitrary callbacks. Public execution tests
separately check full source cells and first-fault/resumption behavior. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleMatchRuntimeSelection
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates DataMatchBranchPrefix
open CallableIndexedHistory CompatibleMatchSelectionPrefix

theorem accepted_sites
    {compilation : SourceCoreCompatibleDataMatches.Context} {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer}
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId}
    {resolution : MatchResolution} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {internalReason : Core.Word} {code : Core.Expr}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate}
    (expressionExtract : ∀ childFuel scope id result,
      lowerExpression childFuel source scope id reasonAt = .ok result → expressionCertificate scope id result)
    (bodyExtract : ∀ childFuel scope statements code,
      lowerBody childFuel source scope statements resultType reasonAt internalReason = .ok code →
      bodyCertificate scope statements code)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      resultType reasonAt internalReason = .ok code) :
    CompatibleMatchDecision.Certificate.LiteralSites (CompatibleMatchRuntimeSelection.LiteralRows compilation)
      (certificate_of_lowerWithReasons expressionExtract bodyExtract accepted) :=
  CompatibleMatchRuntimeSelection.of_certificate _

theorem actual_remaining
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternRuntime.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry)
    (initial : entry scope mapping world heap store canonical)
    {wholeSize : Nat} {result : Value} {endStore : Store}
    (completed : EvaluationSize wholeSize actual before (code.rename ξ) result endStore) :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      entry finalScope finalMap finalWorld finalHeap finalStore finalCanonical ∧
      ∃ remainingSize, remainingSize < wholeSize ∧
        EvaluationSize remainingSize finalActual finalStore (body.rename finalEmbedding) result endStore := by
  obtain ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, spine, installedEntry, agreement⟩ :=
    CompatibleMatchRuntimeSelection.success_prefix certificate ordinary onError allocator valid catalogValid definitions registered extended found uniqueExpression
      represented environments heaps agrees actualTyped reference read unmapped evaluated transport bindings initial
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, spine, installedEntry,
    agreement.remaining completed⟩

section Boundaries

theorem repeated_arms {compilation : SourceCoreCompatibleDataMatches.Context}
    {source site scope expected} {arm : TypedMatchCase} {pattern : Pattern} {body : Core.Expr}
    {bodyCertificate : BodyCertificate}
    (certified : CompatiblePatternCertificates.Certificate compilation source scope site arm.span expected arm.pattern pattern)
    (typed : HasType [] pattern.matcher pattern.functionType compilation.definitions)
    (bodyAccepted : bodyCertificate (armScope scope pattern) arm.body body) :
    CompatibleMatchDecision.Arms.LiteralSites (CompatibleMatchRuntimeSelection.LiteralRows compilation)
      (Arms.cons certified typed bodyAccepted (Arms.cons certified typed bodyAccepted .nil)) :=
  CompatibleMatchRuntimeSelection.of_arms _

theorem empty_arms {compilation : SourceCoreCompatibleDataMatches.Context}
    {source site scope expected bodyCertificate} :
    CompatibleMatchDecision.Arms.LiteralSites (CompatibleMatchRuntimeSelection.LiteralRows compilation)
      (Arms.nil (compilation := compilation) (source := source) (site := site) (scope := scope)
        (expected := expected) (bodyCertificate := bodyCertificate)) :=
  CompatibleMatchRuntimeSelection.of_arms _

theorem actual_frame_runtime {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) {compilation : SourceCoreCompatibleDataMatches.Context}
    (signatures : context.signatures = compilation.signatures)
    (sameLedger : function.context.solvedRequirements = compilation.solvedRequirements) :
    CompatiblePatternRuntime.ContextValid compilation context :=
  ⟨signatures, (RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger,
    RecursiveNamedInitialContextValidity.runtime frame extended programTyped⟩

end Boundaries

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def content : String := String.intercalate "\n" [
  "function ordered(a: Word, b: Word) returns (Word) { match ((a, b)) { case (37, bound) { return bound; } case (37, later) { return later + 1; } case (left, right) { return left + right; } } }",
  "function choose(a: Word) returns (Word) { match (a) { case 0 { return 11; } case 1 { return 13; } default { return 17; } } }",
  "function failed(a: Word) returns (Word) { match (a) { case 0 { let prior: Word = 41; let missing: Word; return missing; } default { return 19; } } }",
  "function scrutineeFault() returns (Word) { let missing: Word; match (missing) { case 0 { return 23; } default { return 29; } } }"
]

/-- The actual whole match lowerer is supplied explicit constant scrutinee and
marker bodies. Full native cells expose exactly which ordered arm was reached. -/
private def auditLower (compilation : SourceCoreCompatibleDataMatches.Context) (source : TypedSource)
    (statement : StatementNode) (resolution : MatchResolution) (payload : Core.Ty)
    (input : Core.Value) (expected : Core.Value) (bindings : List Core.Value)
    (scrutineeFails : Bool := false) : IO Unit := do
  let lowerExpression : ExpressionLowerer := fun _ _ _ _ _ => .ok ⟨payload,
    if scrutineeFails then Core.LanguageResult.failure payload (.word (Word.ofNatModulo 811))
    else Core.LanguageResult.success (.var 0)⟩
  let lowerBody : BodyLowerer := fun _ _ _ statements _ _ _ =>
    let selected := resolution.cases.zipIdx.find? (fun (arm, _) => arm.body == statements)
    let marker := selected.map (fun (_, index) => 100 + index) |>.getD 900
    .ok (Core.LocalLoop.returned (.word (Word.ofNatModulo marker)))
  match accepted : lowerWithReasons compilation lowerExpression lowerBody 100 source [] statement.id resolution
      .word (fun _ => Word.ofNatModulo 813) (Word.ofNatModulo 817) with
  | .error error => throw (IO.userError s!"ordered match lowering rejected {reprStr error}")
  | .ok code =>
    have actual := certificate_of_lowerWithReasons (expressionCertificate := fun _ _ _ => True)
      (bodyCertificate := fun _ _ _ => True) (fun _ _ _ _ _ => True.intro) (fun _ _ _ _ _ => True.intro) accepted
    have support := CompatibleMatchRuntimeSelection.of_certificate actual
    let _support := support
    require (Core.infer? [payload] code compilation.definitions == some (Core.LocalLoop.resultType .word))
      "ordered matcher actual code type changed"
    let sentinel : Core.Store := [.integer 919, .closure .unit .integer (.var 1) [.integer 921], .cellRef .integer 0]
    let appended := if scrutineeFails then [] else (input :: bindings).map (Core.Value.inRight .unit)
    for fuel in [0, 3, 23, 10000] do
      let result := match Core.runStateful fuel (.initial code [input] sentinel) with
        | .outOfFuel pending => Core.runStateful 10000 pending | other => other
      match result with
      | .done value finalStore =>
        require (value == expected && finalStore == sentinel ++ appended)
          s!"ordered selection/full native store mismatch: {reprStr result}"
      | other => throw (IO.userError s!"ordered match prefix unfinished {reprStr other}")

private def replaceMatch (source : TypedSource) (statement : StatementNode) (resolution : MatchResolution) : TypedSource :=
  {source with nodes := source.nodes.map (fun node => match node with
    | .statement found => if found.id == statement.id then .statement {found with form := .matchWith resolution} else node
    | _ => node)}

private def inspect (artifact : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let w := Word.ofNatModulo
  let mut count := 0
  for named in artifact.indexed.base.functions do
    let actual ← get "ordered actual specialization" (SourceCompilationPlan.exactSpecialization artifact.indexed.base.plan named.signature.key)
    require (actual == named.specialized) "ordered full selected record changed"
    let source := actual.function.typedBody
    let signature ← match artifact.sourceProgram.signatures.functions.find? (·.id == actual.function.declaration) with
      | some value => pure value | none => throw (IO.userError "ordered signature missing")
    for node in source.nodes do
      match node with
      | .statement statement => match statement.form with
        | .matchWith resolution =>
          if signature.name == "ordered" || signature.name == "choose" then
            let ledger := actual.function.solvedRequirements
            let compilation : SourceCoreCompatibleDataMatches.Context := ⟨(.initial artifact.compatible.checked), ledger, none, none⟩
            let row ← match ledger.head? with
              | some value => pure value | none => throw (IO.userError "numeric row missing")
            let unused : SolvedRequirement := ⟨⟨(ledger.map (·.id.index)).foldl max 0 + 10000⟩, row.predicate, .assumption row.predicate⟩
            for changed in [compilation, {compilation with solvedRequirements := unused :: ledger},
                {compilation with solvedRequirements := ledger ++ [unused]}] do
              if signature.name == "ordered" then
                auditLower changed source statement resolution (.product .word .word)
                  (.pair (.word (w 37)) (.word (w 8))) (Core.LocalLoop.returnedValue (.word (w 100))) [.word (w 8)]
                auditLower changed source statement resolution (.product .word .word)
                  (.pair (.word (w 38)) (.word (w 8))) (Core.LocalLoop.returnedValue (.word (w 102))) [.word (w 38), .word (w 8)]
              else
                for (input, marker) in [(0, 100), (1, 101), (2, 900)] do
                  auditLower changed source statement resolution .word (.word (w input)) (Core.LocalLoop.returnedValue (.word (w marker))) []
            if signature.name == "ordered" then
              let first ← match resolution.cases.head? with
                | some value => pure value | none => throw (IO.userError "first ordered arm missing")
              let cases := resolution.cases.mapIdx (fun index arm => if index == 1 then {arm with pattern := first.pattern} else arm)
              let repeated := {resolution with cases := cases, requirements := cases.flatMap (·.pattern.requirements)}
              require (repeated.requirements.take 2 == first.pattern.requirements ++ first.pattern.requirements)
                "repeated requirement order lost"
              auditLower compilation (replaceMatch source statement repeated) statement repeated (.product .word .word)
                (.pair (.word (w 37)) (.word (w 8))) (Core.LocalLoop.returnedValue (.word (w 100))) [.word (w 8)]
            else
              let empty := {resolution with cases := [], defaultBody := none, requirements := []}
              auditLower compilation (replaceMatch source statement empty) statement empty .word (.word (w 3))
                (Core.LocalLoop.fallthroughValue .word) []
              let fallbackOnly := {resolution with cases := [], requirements := []}
              auditLower compilation (replaceMatch source statement fallbackOnly) statement fallbackOnly .word (.word (w 3))
                (Core.LocalLoop.returnedValue (.word (w 900))) []
              auditLower compilation source statement resolution .word (.word (w 0))
                (.inLeft (Core.LocalLoop.controlType .word) (.word (w 811))) [] true
            count := count + 1
        | _ => pure ()
      | _ => pure ()
  require (count == 2) "ordered match source count changed"

/-- Only the actual whole match is lowered; template-bearing lambda body
execution and whole callable acceptance are not claimed by this fixture. -/
private def template_root : IO Unit := do
  let program ← get "ordered template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word) {",
      " let f = lam(item) { return keep(item); }; let other: Bool = f(flag); let number: Word = 61;",
      " match ((number, number)) { case (61, 61) { return f(1); } default { return f(2); } } }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "ordered template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "ordered template function missing")
  let actual ← get "ordered actual template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger.map (·.id) == generic.solvedRequirements.map (·.id))
    "ordered template IDs or complete ordered ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !actual.assumptions.contains predicate)
          "ordered template assumption was promoted"
      | _ => throw (IO.userError "ordered template implementation fabricated")
    | _ => throw (IO.userError "ordered template row missing or duplicated")
  let checked ← get "ordered template catalog"
    (SourceCoreCompatibleCatalog.prepare program.signatures 100 [.word, .bool, .product .word .word])
  let compilation : SourceCoreCompatibleDataMatches.Context := ⟨.initial checked, ledger, none, none⟩
  let w := Word.ofNatModulo
  let mut count := 0
  for node in source.nodes do
    match node with
    | .statement statement => match statement.form with
      | .matchWith metadata =>
        auditLower compilation source statement metadata (.product .word .word)
          (.pair (.word (w 61)) (.word (w 61))) (Core.LocalLoop.returnedValue (.word (w 100))) []
        auditLower compilation source statement metadata (.product .word .word)
          (.pair (.word (w 62)) (.word (w 61))) (Core.LocalLoop.returnedValue (.word (w 900))) []
        count := count + 1
      | _ => pure ()
    | _ => pure ()
  require (count == 1) "ordered template occurrence count changed"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "ordered public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "runtime ordered match selection" content
    ["ordered", "choose", "failed", "scrutineeFault"]
  inspect compiled
  template_root
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (word 929)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("ordered", [word 37, word 8], word 8, [(.word, some (word 37)), (.word, some (word 8)), (.product .word .word, some (.product (word 37) (word 8))), (.word, some (word 8))]),
    ("ordered", [word 38, word 8], word 46, [(.word, some (word 38)), (.word, some (word 8)), (.product .word .word, some (.product (word 38) (word 8))), (.word, some (word 38)), (.word, some (word 8))]),
    ("choose", [word 0], word 11, [(.word, some (word 0)), (.word, some (word 0))]),
    ("choose", [word 1], word 13, [(.word, some (word 1)), (.word, some (word 1))]),
    ("choose", [word 2], word 17, [(.word, some (word 2)), (.word, some (word 2))]),
    ("failed", [word 1], word 19, [(.word, some (word 1)), (.word, some (word 1))])]
  for (name, arguments, expected, cells) in successes do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 7, 53, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) "ordered public resume changed"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected && reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"ordered public full cells changed {name}"
      | other => throw (IO.userError s!"ordered public success expected {reprStr other}")
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
      ("failed", [word 0], [(.word, some (word 0)), (.word, some (word 0)), (.word, some (word 41)), (.word, none)]),
      ("scrutineeFault", [], [(.word, none)])]
  for (name, arguments, cells) in failures do
    let actual ← match compiled.indexed.base.functions.find? (fun named =>
        compiled.sourceProgram.signatures.functions.any (fun signature => signature.id == named.specialized.function.declaration && signature.name == name)) with
      | some value => pure value | none => throw (IO.userError "fault source missing")
    let missing ← match (SourceCoreDataPlaces.declaredBinders actual.specialized.function.typedBody).findSome? (fun binder =>
        if binder.name == "missing" then some binder.id else none) with
      | some value => pure value | none => throw (IO.userError "fault binder missing")
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 7, 53, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) "ordered public fault resume changed"
      match observed with
      | .fault (.uninitializedLocal found) final =>
        require (found == missing && reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          "ordered public first fault/full cells changed"
      | other => throw (IO.userError s!"ordered public fault expected {reprStr other}")
  IO.println "runtime ordered match: actual root support / repeated arms and IDs / first selection and misses / empty default / full stores-heaps / original strict continuation / resume GREEN"

end Tests.SourceCoreCompatibleMatchRuntimeSelection
