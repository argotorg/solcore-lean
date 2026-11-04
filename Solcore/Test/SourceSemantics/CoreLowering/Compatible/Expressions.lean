import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualReads
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualConditionals
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualConstructors
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualIndices
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualLiterals
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualMembers
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualPrimitives
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualProducts
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualProxies
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingReadMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualRecursive
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberNativeTyping
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadNativeTyping

/-!
# Compatible expression tests

Compatible expressions: conditionals, constructors, indices, literals, members and reads.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleContextualReads
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! The actual shared traversal is exercised at named roots and inside a
prepared generic parent with a nonempty full substitution. Both static read
receipts are extracted from its actual successful result before native runs.
The source typing premise of the semantic bridge remains independent. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleContextualReads
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open CompatibleExpressionReads

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (n : Nat) : Word := Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function root(value: Bool) returns (Bool) { return value; }",
    "function parent(seed: Word) returns (Word) { let echo = lam(value) { return seed; }; return echo(true); }",
    "function lazy() returns (mapping(Word => Word)) { let table: mapping(Word => Word); return table; }"
  ]}] }

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) : IO Nat := do
  let values := SourceCoreCompatibleValues.Context.initial checked
  let representation := SourceCoreCompatibleFunctions.representation values 100
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program
    | none => throw (IO.userError "contextual read diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "contextual root diagnostics missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let mut count := 0
  for entry in source.nodes do
    match entry with
    | .expression node =>
      match form : node.form with
      | .reference _name (.local binder) =>
        if found : source.lookupExpression? node.id = some node then
          if requirements : node.requirements = [] then
            if coercions : node.coercions = [] then
              if ordinary : prepared.locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false then
                if notInitializer : prepared.locals.bindings.find? (fun binding => decide (binding.caller = owner ∧ binding.initializer = node.id)) = none then
                  let declared ← get "ordinary source binder" (SourceCoreDataPlaces.rootBinder source binder)
                  let type ← get "ordinary native type" (checked.catalog.project declared.scheme.body)
                  let scope := [(binder, type)]
                  match accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation
                      checked.signatures prepared.locals prepared.contexts own.assignments diagnostics context prepared.callableContext
                      parent none 100 source scope node.id reasonAt with
                  | .error error => throw (IO.userError s!"actual contextual read rejected: {reprStr error}")
                  | .ok lowered =>
                    have receipts := contextual_read_receipts (readFuel := 100) (values := values)
                      found form requirements coercions ordinary notInitializer rfl rfl accepted
                    have staticReceipt : Nonempty (Certificate 100 values source scope node.id (reasonAt node.id) lowered.expression) :=
                      of_accepted receipts.2
                    let _receipt := staticReceipt
                    let (_, projected) ← get "retained read metadata" (SourceCoreCompatibleDataExpressions.readExpression checked source node.id)
                    assertTrue (projected == lowered.type && type == lowered.type) "contextual read changed native type"
                    let direct ← get "direct compatible read" (SourceCoreCompatibleDataExpressions.lowerRead 100 values source scope node.id (reasonAt node.id))
                    assertTrue (direct == lowered.expression) "contextual traversal changed ordinary read code"
                    let initializers : List (Expr × Core.Value) ← match declared.scheme.body with
                      | .bool => pure [(OptionalCell.allocateInitialized type (.bool true), .inRight .word (.bool true)),
                          (OptionalCell.allocate type, .inLeft type (.word (reasonAt node.id)))]
                      | .word => pure [(OptionalCell.allocateInitialized type (.word (word 23)), .inRight .word (.word (word 23))),
                          (OptionalCell.allocate type, .inLeft type (.word (reasonAt node.id)))]
                      | .mapping key value => do
                        let encoded ← get "empty mapping" (SourceCoreCompatibleValues.encode 100 values declared.scheme.body (.mapping key value []))
                        pure [(OptionalCell.allocate type, .inRight .word encoded.value)]
                      | _ => throw (IO.userError s!"unexpected ordinary fixture type: {reprStr declared.scheme.body}")
                    for (initializer, expected) in initializers do
                      let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE initializer lowered.expression, checked.catalog.definitions⟩
                      assertTrue native.check "actual contextual read failed Core checker"
                      for fuel in [0, 2, 1000] do
                        let completed := match native.runStateful fuel with
                          | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
                          | other => other
                        match completed with
                        | .done value store =>
                          assertTrue (value == expected && store.length == 1) "actual contextual read outcome/effect mismatch"
                        | other => throw (IO.userError s!"actual contextual read did not complete: {reprStr other}")
                    count := count + 1
      | _ => pure ()
    | _ => pure ()
  pure count

def run : IO Unit := do
  let program ← get "contextual source checker" (checkProgram workspace)
  let roots ← ["root", "parent", "lazy"].mapM fun name =>
    match program.signatures.functions.find? (·.name == name) with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
    | none => throw (IO.userError "contextual fixture root missing")
  let plan ← match SourceSpecializationWorklist.run program roots 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"contextual specialization: {reprStr other}")
  let automatic ← get "actual compatible factory" (SourceCoreCompatibleFunctions.prepare program plan 300)
  let mut rootReads := 0
  for function in automatic.prepared.functions do
    rootReads := rootReads + (← inspect automatic.prepared function.specialized.function.typedBody
      function.signature.key none function.specialized.function.solvedRequirements)
  let mut contextualReads := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      contextualReads := contextualReads + (← inspect automatic.prepared parent.source parent.caller.key
        (some parent) parent.caller.function.solvedRequirements)
  assertTrue (rootReads ≥ 3) "named root read receipts missing"
  assertTrue (contextualReads > 0) "nonempty full parent context read receipt missing"
  IO.println "actual contextual ordinary reads: named roots, full parent substitution, initialization, fault and resume GREEN"

end Tests.SourceCoreCompatibleContextualReads
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleExpressionConditionals
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! The kernel tests consume actual compiler results and independent source
shape typing. Runtime tests cover a lazy mapping read before a right-hand
fault, inserted slots, a full parent context, and administrative closures. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionConditionals
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionConditionals CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_products", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "products.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def boolean (index : Nat) (value : Bool) : ExpressionNode :=
  { id := id index, span, type := .bool, form := .reference "boolean" (.builtinBoolean value) }
private def unaryNode : ExpressionNode := { id := id 2, span, type := .bool, form := .unary .logicalNot (id 0) }
private def binaryNode : ExpressionNode := { id := id 3, span, type := .bool, form := .binary (id 2) .logicalOr (id 1) }
private def grouped : ExpressionNode := { id := id 4, span, type := .bool, form := .group (id 6) }
private def paired : ExpressionNode := { id := id 5, span, type := .product .bool .bool, form := .tuple [id 4, id 1] }
private def conditionalNode : ExpressionNode := { id := id 6, span, type := .bool, form := .conditional (id 3) (id 0) (id 1) }
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 5)],
    nodes := [.expression (boolean 0 true), .expression (boolean 1 false), .expression unaryNode, .expression binaryNode, .expression grouped, .expression paired, .expression conditionalNode] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private def faults : FunctionCalls.FaultRep := fun error token =>
  (∃ location, error = .uninitializedLocation location) ∧ token = reason
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index native selected
  cases selected
private theorem syntaxTree : CompatibleExpressionConditionals.Syntax source (id 5) :=
  .pair (node := paired) (by cbv) rfl
    (.group (node := grouped) (by cbv) rfl
      (.conditional (node := conditionalNode) (by cbv) rfl
        (.primitive (.binary (node := binaryNode) (by cbv) rfl
          (.unary (node := unaryNode) (by cbv) rfl (.product (.literal (node := boolean 0 true) (by cbv) (.bool _ _))))
          (.product (.literal (node := boolean 1 false) (by cbv) (.bool _ _)))))
        (.primitive (.product (.literal (node := boolean 0 true) (by cbv) (.bool _ _))))
        (.primitive (.product (.literal (node := boolean 1 false) (by cbv) (.bool _ _))))))
    (.primitive (.product (.literal (node := boolean 1 false) (by cbv) (.bool _ _))))
private theorem boolTyped {index : Nat} {value : Bool}
    (found : source.lookupExpression? (id index) = some (boolean index value)) :
    ExpressionHasType source context (id index) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := boolean index value) (rawType := .bool)
    (lookupExpression?_sound found) (.reference (.builtinBoolean value)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem unaryTyped : ExpressionHasType source context (id 2) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := unaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.unary (boolTyped (value := true) (by cbv)) .logicalNot) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem binaryTyped : ExpressionHasType source context (id 3) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := binaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.binary unaryTyped (boolTyped (value := false) (by cbv)) .booleanOr) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem conditionalTyped : ExpressionHasType source context (id 6) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := conditionalNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.conditional binaryTyped
      (boolTyped (value := true) (by cbv)) (boolTyped (value := false) (by cbv))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem groupedTyped : ExpressionHasType source context (id 4) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := grouped) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.group conditionalTyped) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem pairedTyped : ExpressionHasType source context (id 5) (.product .bool .bool) := by
  have boolAdmitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  have admitted : TypeAdmissible context (.product .bool .bool) := .product boolAdmitted boolAdmitted
  apply ExpressionHasType.ofOrdinary (node := paired) (rawType := .product .bool .bool)
    (lookupExpression?_sound (by cbv)) (.tuple (.cons groupedTyped (.cons (boolTyped (value := false) (by cbv)) (.nil _)))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures]
  · intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; simp [context, SourceSemantics.Context.ofSignatures] at member
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.product .bool .bool]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.product .bool .bool]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def policy := SourceCoreCompatibleDataExpressions.functionPolicy 20 values
private def unaryCode := LocalPrimitiveResults.unary .boolNot (LanguageResult.success (.bool true))
private def binaryCode := SourceCorePrimitive.binary .logicalOr unaryCode (LanguageResult.success (.bool false))
private def conditionalCode := LocalControl.choose .bool binaryCode
  (LanguageResult.success (.bool true)) (LanguageResult.success (.bool false))
private def code : SourceCoreBasic.LoweredExpr :=
  ⟨.product .bool .bool, LocalSequence.pair .bool .bool conditionalCode (LanguageResult.success (.bool false))⟩
private theorem boolAccepted (fuel index : Nat) (value : Bool)
    (found : source.lookupExpression? (id index) = some (boolean index value))
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id index) = .ok (boolean index value, .bool))
    (basic : SourceCoreBasic.lowerExpression (fuel + 1) source [] (id index) reason =
      .ok ⟨.bool, LanguageResult.success (.bool value)⟩) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 1) compilation source [] (id index) (fun _ => reason) =
      .ok ⟨.bool, LanguageResult.success (.bool value)⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id index).occurrence.owner = source.owner := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure]
  simp only [boolean]
  rw [read]
  simp only [bind, Except.bind, boolean]
  unfold SourceCoreCompatibleDataExpressions.leafLowerer
  rw [read]
  exact basic
private theorem unaryAccepted (fuel : Nat) : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 2) compilation source [] (id 2) (fun _ => reason) = .ok ⟨.bool, unaryCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 2).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 2) = some unaryNode := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 2) = .ok (unaryNode, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, unaryNode]
  rw [read]
  simp only [bind, Except.bind, unaryNode]
  have childEq := boolAccepted fuel 0 true rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at childEq
  rw [childEq]
  rfl
private theorem binaryAccepted (fuel : Nat) : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 3) compilation source [] (id 3) (fun _ => reason) = .ok ⟨.bool, binaryCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 3).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 3) = some binaryNode := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 3) = .ok (binaryNode, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, binaryNode]
  rw [read]
  simp only [bind, Except.bind, binaryNode]
  have firstEq := unaryAccepted fuel
  have secondEq := boolAccepted (fuel + 1) 1 false rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at firstEq secondEq
  rw [firstEq]
  simp only [bind, Except.bind]
  rw [secondEq]
  rfl
private theorem conditionalAccepted (fuel : Nat) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 4) compilation source [] (id 6) (fun _ => reason) =
      .ok ⟨.bool, conditionalCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 6).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 6) = some conditionalNode := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 6) = .ok (conditionalNode, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, conditionalNode]
  rw [read]
  simp only [bind, Except.bind, conditionalNode]
  have conditionEq := binaryAccepted fuel
  have thenEq := boolAccepted (fuel + 2) 0 true rfl rfl rfl
  have elseEq := boolAccepted (fuel + 2) 1 false rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at conditionEq thenEq elseEq
  rw [conditionEq]
  change (do
    let thenCode ← SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 3) compilation source [] (id 0) (fun _ => reason)
    let elseCode ← SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 3) compilation source [] (id 1) (fun _ => reason)
    SourceCoreBasic.ensureType _ .bool thenCode.type
    SourceCoreBasic.ensureType _ .bool elseCode.type
    pure (⟨.bool, LocalControl.choose .bool binaryCode thenCode.expression elseCode.expression⟩ : SourceCoreBasic.LoweredExpr)) = _
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure]
  rw [thenEq]
  simp only [bind, Except.bind]
  rw [elseEq]
  rfl
private theorem groupAccepted (fuel : Nat) : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 5) compilation source [] (id 4) (fun _ => reason) = .ok ⟨.bool, conditionalCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 4).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 4) = some grouped := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 4) = .ok (grouped, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, grouped]
  rw [read]
  simp only [bind, Except.bind, grouped]
  have childEq := conditionalAccepted fuel
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at childEq
  rw [childEq]
  rfl
private theorem accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 7 compilation source [] (id 5) (fun _ => reason) = .ok code := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 5).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 5) = some paired := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 5) = .ok (paired, (.product .bool .bool)) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, paired]
  rw [read]
  simp only [bind, Except.bind, paired]
  have firstEq := groupAccepted 1
  have secondEq := boolAccepted 5 1 false rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at firstEq secondEq
  rw [firstEq]
  simp only [bind, Except.bind]
  rw [secondEq]
  rfl
private theorem certified : Tree 20 values source context [] (fun _ => reason) [] (id 5) code :=
  tree_of_functions unique declarations ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) pairedTyped accepted

/-- The actual production contextual dispatcher is also the source of the
static tree; the compilation equation is the only compiler-result premise. -/
theorem contextual_certificate
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {lowered : SourceCoreBasic.LoweredExpr}
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead 20 values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (generated : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures ⟨[]⟩ parents assignments
      diagnostics compilation native parent none 7 source [] (id 5) (fun _ => reason) = .ok lowered) :
    Tree 20 values source context [] (fun _ => reason) [] (id 5) lowered := by
  exact tree_of_contextual
    ⟨fun _ _ _ found => (metadata found).1, fun _ _ _ found => (metadata found).2, by intros; rfl, by intros; rfl⟩
    unique declarations syntaxTree (by cbv) pairedTyped readPolicy lowerPolicy leafPolicy generated

/-- Both directions use the whole tree induction. No child evaluator proof is
supplied, even when the ambient heap contains captures of fresh nominal frames. -/
theorem actual_preserves {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked values.registry functions)
      program context [] source (Tree 20 values source context [] (fun _ => reason)) faults :=
  preserves (values := values) (source := source) (fuel := 20) (reasonAt := fun _ => reason) (faults := faults) functions (.refl _) program [] valid unique (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)
theorem actual_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked values.registry functions)
      program context [] source (Tree 20 values source context [] (fun _ => reason)) faults :=
  reflects (values := values) (source := source) (fuel := 20) (reasonAt := fun _ => reason) (faults := faults) functions (.refl _) program [] valid (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)

theorem accepted_conditional_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {mapping world administrative environment canonical actual before store ξ value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
      administrative [] environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (completed : Evaluates actual store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source environment before (id 5) outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked values.registry functions)
        finalMap finalWorld paired.type code.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  actual_reflects functions certified (by cbv) environments heaps locals agrees completed


private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)


private def sources : List String := [
  "function true_skip() returns (Word) { let missing: Word; return true ? 7 : missing; }",
  "function false_skip() returns (Word) { let missing: Word; return false ? missing : 3; }",
  "function condition_fault() returns (Word) { let missing: Bool; let otherMissing: Word; return missing ? otherMissing : 1; }",
  "function true_fault() returns (Word) { let missing: Word; let otherMissing: Word; return true ? missing : otherMissing; }",
  "function false_fault() returns (Word) { let missing: Word; let otherMissing: Word; return false ? otherMissing : missing; }",
  "function nested() returns (Bool) { let missing: Bool; return !(false ? (true && missing) : (true ? false : missing)); }",
  "function arithmetic() returns (Word) { let missing: Word; return (true ? 7 : missing) + (false ? missing : 3); }",
  "function map_true() returns (mapping(Word => Word)) { let m: mapping(Word => Word); let other: mapping(Word => Word); return true ? m : other; }",
  "function map_false() returns (mapping(Word => Word)) { let m: mapping(Word => Word); let other: mapping(Word => Word); return false ? other : m; }",
  "function map_skip() returns ((mapping(Word => Word), Bool)) { let m: mapping(Word => Word); let missing: Bool; return (m, false ? missing : true); }",
  "function map_fault() returns ((mapping(Word => Word), Bool)) { let m: mapping(Word => Word); let other: mapping(Word => Word); let missing: Bool; return true ? (m, missing) : (other, false); }",
  "function parent(seed: Word) returns ((Word, Bool)) { let f = lam(flag) { return (true ? ~seed : seed + 3, flag); }; return f(true); }"]
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" sources}] }

private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | fuel + 1, source, expression => match source.lookupExpression? expression with
    | none => []
    | some node => node :: (match node.form with
      | .unary _ operand => reached fuel source operand
      | .binary left _ right => reached fuel source left ++ reached fuel source right
      | .conditional condition thenId elseId => reached fuel source condition ++ reached fuel source thenId ++ reached fuel source elseId
      | .group inner => reached fuel source inner
      | .tuple ids => ids.flatMap (reached fuel source)
      | _ => [])
private def expected (name : String) (mapping : Value) : Option Value := match name with
  | "true_skip" => some (.word (Word.ofNatModulo 7))
  | "false_skip" => some (.word (Word.ofNatModulo 3))
  | "nested" => some (.bool true)
  | "arithmetic" => some (.word (Word.ofNatModulo 10))
  | "map_true" | "map_false" => some mapping
  | "map_skip" => some (.pair mapping (.bool true))
  | "parent" => some (.pair (.word (Word.ofNatModulo 7).bitNot) (.bool true))
  | _ => none
private def inspect {catalog : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (name : String) (expression : ExpressionId) : IO Unit := do
  let contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let representation := SourceCoreCompatibleFunctions.representation contextValues 150
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "conditional diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "conditional root diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let nodes := reached 100 source expression
  for node in nodes do
    assertTrue node.coercions.isEmpty "conditional fixture acquired an output coercion"
    match node.form with
    | .unary .. | .binary .. | .conditional .. => assertTrue node.requirements.isEmpty "conditional fixture acquired method dispatch evidence"
    | _ => pure ()
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let bindings ← ids.mapM fun binder => do
    let declared ← get "conditional binder" (SourceCoreDataPlaces.rootBinder source binder)
    let type ← get "conditional binder projection" (catalog.catalog.project declared.scheme.body)
    let initializer ← if declared.name == "missing" || declared.name == "otherMissing" then pure (OptionalCell.allocate type)
      else match declared.scheme.body with
      | .bool => pure (OptionalCell.allocateInitialized type (.bool true))
      | .word => pure (OptionalCell.allocateInitialized type (.word (Word.ofNatModulo (if declared.name == "b" then 3 else 7))))
      | .integer => pure (OptionalCell.allocateInitialized type (.integer (if declared.name == "b" then 3 else -7)))
      | .mapping .. => pure (OptionalCell.allocate type)
      | other => throw (IO.userError s!"unexpected conditional scope: {reprStr other}")
    pure (binder, type, initializer)
  let scope := bindings.map fun (id, type, _) => (id, type)
  let lowered ← get s!"actual contextual conditional {name}" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
    representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
    parent none 150 source scope expression reasonAt)
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"actual contextual conditional {name} failed native checker"
  let mappingValue ← if name.startsWith "map_" then do
    let encoded ← get "expected empty mapping" (SourceCoreCompatibleValues.encode 100 contextValues
      (.mapping .word .word) (.mapping .word .word []))
    pure encoded.value
    else pure .unit
  for fuel in [0, 3, 15, 1000] do
    let finished := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 3000 checkpoint
      | other => other
    match finished with
    | .done value store =>
      assertTrue (store.length == bindings.length + 1) "conditional allocated unexpected cells"
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "conditional changed administrative closure"
      match expected name mappingValue with
      | some expected => assertTrue (value == .inRight .word expected) s!"conditional {name} wrong result: {reprStr value}"
      | none =>
        let faultNode ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "fault fixture lacks missing occurrence")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt faultNode.id))) s!"conditional {name} fault reason/order changed"
      for (position, (binder, type, _)) in bindings.zipIdx.map (fun (binding, position) => (position, binding)) do
        if type != .bool && type != .word && type != .integer then
          let declared ← get "mapping branch binder" (SourceCoreDataPlaces.rootBinder source binder)
          let expectedCell := if declared.name == "m" then Value.inRight .unit mappingValue else .inLeft type .unit
          assertTrue (store[bindings.length - position]? == some expectedCell)
            "conditional initialized the skipped mapping or lost the selected mapping"
    | other => throw (IO.userError s!"conditional {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let checkedProgram ← get "conditional checker" (checkProgram workspace)
  let roots := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"conditional specialization: {reprStr other}")
  let automatic ← get "actual conditional factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      let source := function.specialized.function.typedBody
      let expression ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some expression => pure expression | none => throw (IO.userError "conditional return missing")
      inspect automatic.prepared source function.signature.key none function.specialized.function.solvedRequirements name expression
      rootsSeen := rootsSeen + 1
  let mut parentsSeen := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      for entry in parent.source.nodes do
        match entry with
        | .expression node => match node.form with
          | .tuple [_, _] =>
            inspect automatic.prepared parent.source parent.caller.key (some parent) parent.caller.function.solvedRequirements "parent" node.id
            parentsSeen := parentsSeen + 1
          | _ => pure ()
        | _ => pure ()
  assertTrue (rootsSeen == 11) s!"conditional cases missing: {rootsSeen}"
  assertTrue (parentsSeen > 0) "full parent substitution conditional case missing"
  IO.println "actual contextual conditionals: lazy branches, nested primitives/products, fault order, mapping effects, ambient closure and resume GREEN"

end Tests.SourceCoreCompatibleExpressionConditionals
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleExpressionConstructors
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual accepted constructor lowering supplies a recursive static tree. The
kernel consumers require no child runtime hypothesis; checked-source executions
exercise exact raw metadata, first-fault ordering and administrative stores. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionConstructors
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionConstructors CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"constructor_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "constructor_meaning.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def sourceType : TypeSystem.Ty := .nominal owner []
private def leafSignature : ProgramDataConstructorSignature :=
  ⟨⟨owner, 0⟩, "Leaf", [.bool], ⟨span, ⟨[], ⟨span, "Leaf"⟩, none⟩⟩⟩
private def branchSignature : ProgramDataConstructorSignature :=
  ⟨⟨owner, 1⟩, "Branch", [sourceType, sourceType], ⟨span, ⟨[], ⟨span, "Branch"⟩, none⟩⟩⟩
private def signature : ProgramDataSignature := {
  id := owner, name := "Tree", parameters := [], constructors := [leafSignature, branchSignature]
  source := ⟨span, ⟨none, ⟨span, "Tree"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def leaf : DataConstructorInstantiation := ⟨leafSignature.id, [], [.bool], sourceType⟩
private def branch : DataConstructorInstantiation := ⟨branchSignature.id, [], [sourceType, sourceType], sourceType⟩
private def boolean : ExpressionNode := { id := id 0, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def leafNode : ExpressionNode := { id := id 1, span, type := sourceType, form := .constructor leaf [id 0] }
private def branchNode : ExpressionNode := { id := id 2, span, type := sourceType, form := .constructor branch [id 1, id 1] }
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 2)],
    nodes := [.expression boolean, .expression leafNode, .expression branchNode] }
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private def faults : FunctionCalls.FaultRep := fun error token =>
  (∃ location, error = .uninitializedLocation location) ∧ token = reason
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index native selected
  cases selected
private theorem leafValid : SourceSemantics.DataConstructorInstantiation.Valid context leaf := by
  refine .intro signature leafSignature (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    (by simp [signature]) rfl rfl ⟨by simp [signature], by simp [ParameterSubstitution.domain, leaf, signature]⟩ ?_ rfl rfl
  intro parameter replacement member; cases member
private theorem branchValid : SourceSemantics.DataConstructorInstantiation.Valid context branch := by
  refine .intro signature branchSignature (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    (by simp [signature]) rfl rfl ⟨by simp [signature], by simp [ParameterSubstitution.domain, branch, signature]⟩ ?_ rfl rfl
  intro parameter replacement member; cases member
private theorem nominalAdmitted : TypeAdmissible context sourceType :=
  ⟨TypeParameterBindersWellFormed.ofSignatures signatures,
    .nominal signature [] (by simp [context, SourceSemantics.Context.ofSignatures, signatures]) rfl .nil⟩
private theorem boolTyped : ExpressionHasType source context (id 0) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := boolean) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem leafTyped : ExpressionHasType source context (id 1) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := leafNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.constructor leafValid.toAdmissible (.cons boolTyped (.nil _))) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem branchTyped : ExpressionHasType source context (id 2) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := branchNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.constructor branchValid.toAdmissible (.cons leafTyped (.cons leafTyped (.nil _)))) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem syntaxTree : CompatibleExpressionConstructors.Syntax source (id 2) := by
  refine .constructor (node := branchNode) (by cbv) rfl ?_
  intro child member
  have same : child = id 1 := by simpa using member
  subst child
  refine .constructor (node := leafNode) (by cbv) rfl ?_
  intro child member
  have same : child = id 0 := by simpa using member
  subst child
  exact .fragment (.primitive (.product (.literal (node := boolean) (by cbv) (.bool _ _))))
private theorem contextValid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures]
  · intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; simp [context, SourceSemantics.Context.ofSignatures] at member
variable {checked : SourceCoreCompatibleCatalog.Checked}
private abbrev values (checked : SourceCoreCompatibleCatalog.Checked) := SourceCoreCompatibleValues.Context.initial checked
private abbrev policy (checked : SourceCoreCompatibleCatalog.Checked) := SourceCoreCompatibleDataExpressions.functionPolicy 20 (values checked)
private theorem certified {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 5 compilation source [] (id 2) (fun _ => reason) = .ok code) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 2) code :=
  tree_of_functions unique declarations rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) branchTyped accepted

/-- The authentic contextual dispatcher equation supplies the same tree for
root and prepared-parent calls; no child compiler/semantic premise remains. -/
theorem contextual_certificate
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {lowered : SourceCoreBasic.LoweredExpr}
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead 20 (values checked))
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer (values checked))
    (generated : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures ⟨[]⟩ parents assignments
      diagnostics compilation native parent none 5 source [] (id 2) (fun _ => reason) = .ok lowered) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 2) lowered := by
  exact tree_of_contextual
    ⟨fun _ _ _ found => (metadata found).1, fun _ _ _ found => (metadata found).2, by intros; rfl, by intros; rfl⟩
    unique rfl rfl declarations syntaxTree (by cbv) branchTyped readPolicy lowerPolicy leafPolicy generated

theorem actual_preserves {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked (values checked).registry functions)
      program context [] source (Tree 20 (values checked) source context [] (fun _ => reason)) faults :=
  preserves (values := values checked) functions (.refl _) program [] contextValid unique (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)
theorem actual_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked (values checked).registry functions)
      program context [] source (Tree 20 (values checked) source context [] (fun _ => reason)) faults :=
  reflects (values := values checked) functions (.refl _) program [] contextValid (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)

theorem accepted_constructor_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 5 compilation source [] (id 2) (fun _ => reason) = .ok code)
    {mapping world administrative environment canonical actual before store ξ value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
      administrative [] environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked (values checked).registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (completed : Evaluates actual store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source environment before (id 2) outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked (values checked).registry functions)
        finalMap finalWorld branchNode.type code.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked (values checked).registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  actual_reflects functions (certified accepted) (by cbv) environments heaps locals agrees completed

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)


private def sources : List String := [
  "enum Tree<T> { Empty(), Leaf(T), Branch(Tree<T>, Tree<T>) }",
  "enum Pair<A,B> { Pair(A,B) }",
  "function empty() returns (Tree<Word>) { return .Empty(); }",
  "function literal() returns (Tree<Word>) { return .Leaf(7); }",
  "function nested() returns (Tree<Word>) { return .Branch(.Leaf((true ? 7 : 9) + 3), .Leaf(~3)); }",
  "function first_fault() returns (Pair<Word,Word>) { let missing: Word; let otherMissing: Word; return .Pair(missing, otherMissing); }",
  "function second_fault() returns (Pair<Word,Word>) { let missing: Word; return .Pair(7, missing); }",
  "function nested_fault() returns (Tree<Word>) { let missing: Word; let otherMissing: Word; return .Branch(.Leaf(missing), .Leaf(otherMissing)); }",
  "function map_success() returns (Pair<mapping(Word => Word), Bool>) { let m: mapping(Word => Word); return .Pair(m, false ? false : true); }",
  "function map_fault() returns (Pair<mapping(Word => Word), Pair<Bool, mapping(Word => Word)>>) { let m: mapping(Word => Word); let other: mapping(Word => Word); let missing: Bool; return .Pair(m, .Pair(missing, other)); }",
  "function parent(seed: Word) returns (Tree<Word>) { let f = lam(item) -> Tree<Word> { return .Leaf(true ? ~seed : seed + 3); }; return f(true); }"]
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" sources}] }

private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | fuel + 1, source, expression => match source.lookupExpression? expression with
    | none => []
    | some node => node :: (match node.form with
      | .unary _ operand => reached fuel source operand
      | .binary left _ right => reached fuel source left ++ reached fuel source right
      | .conditional condition thenId elseId => reached fuel source condition ++ reached fuel source thenId ++ reached fuel source elseId
      | .group inner => reached fuel source inner
      | .tuple ids | .constructor _ ids => ids.flatMap (reached fuel source)
      | _ => [])
private def inspect {catalog : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (name : String) (expression : ExpressionId) : IO Unit := do
  let contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let representation := SourceCoreCompatibleFunctions.representation contextValues 150
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "constructor diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "constructor root diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let nodes := reached 100 source expression
  for node in nodes do
    assertTrue node.coercions.isEmpty "constructor fixture acquired an output coercion"
    match node.form with
    | .unary .. | .binary .. | .conditional .. => assertTrue node.requirements.isEmpty "constructor fixture acquired method dispatch evidence"
    | _ => pure ()
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let bindings ← ids.mapM fun binder => do
    let declared ← get "constructor binder" (SourceCoreDataPlaces.rootBinder source binder)
    let type ← get "constructor binder projection" (catalog.catalog.project declared.scheme.body)
    let initializer ← if declared.name == "missing" || declared.name == "otherMissing" then pure (OptionalCell.allocate type)
      else match declared.scheme.body with
      | .bool => pure (OptionalCell.allocateInitialized type (.bool true))
      | .word => pure (OptionalCell.allocateInitialized type (.word (Word.ofNatModulo (if declared.name == "b" then 3 else 7))))
      | .integer => pure (OptionalCell.allocateInitialized type (.integer (if declared.name == "b" then 3 else -7)))
      | .mapping .. => pure (OptionalCell.allocate type)
      | other => throw (IO.userError s!"unexpected constructor scope: {reprStr other}")
    pure (binder, type, initializer)
  let scope := bindings.map fun (id, type, _) => (id, type)
  let lowered ← get s!"actual contextual constructor {name}" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
    representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
    parent none 150 source scope expression reasonAt)
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"actual contextual constructor {name} failed native checker"
  let mappingValue ← if name.startsWith "map_" then do
    let encoded ← get "expected empty mapping" (SourceCoreCompatibleValues.encode 100 contextValues
      (.mapping .word .word) (.mapping .word .word []))
    pure encoded.value
    else pure .unit
  for fuel in [0, 3, 15, 1000] do
    let finished := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 3000 checkpoint
      | other => other
    match finished with
    | .done value store =>
      assertTrue (store.length == bindings.length + 1) "constructor allocated unexpected cells"
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "constructor changed administrative closure"
      if name.endsWith "fault" then
        let faultNode ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "fault fixture lacks missing occurrence")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt faultNode.id))) s!"constructor {name} fault reason/order changed"
      else
        let payload ← match value with
          | .inRight .word payload => pure payload
          | _ => throw (IO.userError s!"constructor {name} did not succeed: {reprStr value}")
        let root ← match source.lookupExpression? expression with
          | some node => pure node | none => throw (IO.userError "root source metadata missing")
        let decoded ← get "actual constructor decode" (SourceCoreCompatibleValues.decode 100 contextValues root.type payload)
        match root.form, decoded with
        | .constructor original _, .constructed retained fields =>
          assertTrue (original == retained) "constructor lost its exact original metadata header"
          match name, fields with
          | "empty", [] => pure ()
          | "literal", [.word seven] => assertTrue (seven == Word.ofNatModulo 7) "literal payload changed"
          | "nested", [.constructed _ [.word ten], .constructed _ [.word inverted]] =>
            assertTrue (ten == Word.ofNatModulo 10 && inverted == (Word.ofNatModulo 3).bitNot) "nested constructor argument order changed"
          | "map_success", [.mapping .word .word [], .bool true] => pure ()
          | "parent", [.word inverted] => assertTrue (inverted == (Word.ofNatModulo 7).bitNot) "parent constructor captured wrong source context"
          | _, _ => throw (IO.userError s!"unexpected constructor {name} fields: {reprStr fields}")
        | _, _ => throw (IO.userError "constructor result did not retain raw source header")
      for (position, (binder, type, _)) in bindings.zipIdx.map (fun (binding, position) => (position, binding)) do
        if type != .bool && type != .word && type != .integer then
          let declared ← get "mapping branch binder" (SourceCoreDataPlaces.rootBinder source binder)
          let expectedCell := if declared.name == "m" then Value.inRight .unit mappingValue else .inLeft type .unit
          assertTrue (store[bindings.length - position]? == some expectedCell)
            "constructor initialized the skipped mapping or lost the selected mapping"
    | other => throw (IO.userError s!"constructor {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let checkedProgram ← get "constructor checker" (checkProgram workspace)
  let roots := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"constructor specialization: {reprStr other}")
  let automatic ← get "actual constructor factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      let source := function.specialized.function.typedBody
      let expression ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some expression => pure expression | none => throw (IO.userError "constructor return missing")
      inspect automatic.prepared source function.signature.key none function.specialized.function.solvedRequirements name expression
      rootsSeen := rootsSeen + 1
  let mut parentsSeen := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      for entry in parent.source.nodes do
        match entry with
        | .expression node => match node.form with
          | .constructor _ _ =>
            inspect automatic.prepared parent.source parent.caller.key (some parent) parent.caller.function.solvedRequirements "parent" node.id
            parentsSeen := parentsSeen + 1
          | _ => pure ()
        | _ => pure ()
  assertTrue (rootsSeen == 8) s!"constructor cases missing: {rootsSeen}"
  assertTrue (parentsSeen > 0) "full parent substitution constructor case missing"
  IO.println "actual contextual constructors: nullary/nested payloads, first fault, lazy mapping effects, raw headers, parent context, ambient closure and resume GREEN"

end Tests.SourceCoreCompatibleExpressionConstructors
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleExpressionIndices
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual scalar-key indexing discharges its own child meanings. The theorem
fixture has an ambient closure and a typed hidden Integer slot; generated
comparators allocate after that prefix while lazy source initialization persists. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionIndices
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionIndices CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"index_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "index_meaning.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def mappingType : TypeSystem.Ty := .mapping .bool .bool
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono mappingType, [], false, none⟩
private def baseNode : ExpressionNode := { id := id 0, span, type := mappingType, form := .reference "table" (.local binder.id) }
private def keyNode : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def indexNode : ExpressionNode := { id := id 2, span, type := .bool, form := .index (id 0) (id 1) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression (id 2)], nodes := [.expression baseNode, .expression keyNode, .expression indexNode] }
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem mappingAdmitted : TypeAdmissible context mappingType := .mapping boolAdmitted boolAdmitted
private theorem baseTyped : ExpressionHasType source context (id 0) mappingType := by
  apply ExpressionHasType.ofOrdinary (node := baseNode) (rawType := mappingType) (lookupExpression?_sound (by rfl))
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible mappingAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply mappingType)
      (by simp) (by intro _ member; cases member) (.nil)))) mappingAdmitted mappingAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem keyTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.index baseTyped keyTyped) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem syntaxTree : CompatibleExpressionIndices.Syntax source (id 2) :=
  .index (node := indexNode) (keyNode := keyNode) (by cbv) rfl (by cbv) .bool
    (.fragment (.fragment (.fragment (.primitive (.product (.read (node := baseNode) (by cbv) rfl))))))
    (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := keyNode) (by cbv) (.bool _ _)))))))
private theorem contextValid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private theorem nativeExists : (checked.catalog.project mappingType).toOption.isSome = true := by cbv
private def nativeType := (checked.catalog.project mappingType).toOption.get nativeExists
private theorem projected : checked.catalog.project mappingType = .ok nativeType := by cbv
private def scope : SourceCoreLocalCell.Scope := [(binder.id, nativeType)]
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope context := by
  intro actual declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst actual
    have actual : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := by rfl
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected
private abbrev policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
private theorem certified {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 2) (fun _ => reason) = .ok code) :
    Tree 100 values source context [] (fun _ => reason) scope (id 2) code :=
  tree_of_functions unique declarations (by rfl) rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) indexTyped accepted

private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def model := CompatibleAmbientHeap.payloadModel checked values.registry functions
private def faults : FunctionCalls.FaultRep := fun error token =>
  ((∃ location, error = .uninitializedLocation location) ∧ token = reason) ∨
  (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ error = .missingMappingDefault value ∧ token = reason.add tag)
private theorem uninitialized : ∀ (id : ExpressionId) location, faults (.uninitializedLocation location) ((fun _ => reason) id) :=
  fun _ location => .inl ⟨⟨location, rfl⟩, rfl⟩
private theorem missing : ∀ (id : ExpressionId) key value tag, MetadataRep values.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((fun _ => reason) id).add tag) :=
  fun _ key value tag owned => .inr ⟨key, value, tag, owned, rfl, rfl⟩
private def administrativeType : Ty := .function .unit frameLayout.type
private def administrativeValue : Value := .closure .unit frameLayout.type (.var 1) [SourceCoreCallableIndexedFrames.encode frameLayout .empty]
private theorem frameRegistered : frameLayout.Registered ambient.definitions := by
  constructor
  simp [ambient, AmbientDefinitions.append, frameLayout]
private theorem administrativeTyped : RuntimeValueHasType [] administrativeValue administrativeType ambient.definitions :=
  .closure (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty) .nil) (.var rfl)
private def world : StoreTyping := [administrativeType, OptionalCell.cellType nativeType]
private def store : Store := [administrativeValue, .inLeft nativeType .unit]
private def environment : Environment := [.cellRef (OptionalCell.cellType nativeType) 1]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def before : Dynamic.Heap := ⟨[⟨mappingType, none, none⟩]⟩
private def after : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping .bool .bool []), none⟩]⟩
private theorem initial : GenericHeap.HeapRepresents model [1] world before store ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [1] world [] scope sourceEnvironment environment ambient.definitions := by
  have empty := (GenericHeap.HeapRepresents.empty (model := model)).allocate_administrative administrativeTyped
  obtain ⟨heap, reference⟩ := empty.allocate (.uninitialized projected) Dynamic.Heap.Allocates.append
  exact ⟨heap, .cons reference (.nil .nil)⟩
private theorem locals : Dynamic.EnvironmentAgrees before context.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem actualTyped : RuntimeEnvironmentHasTypes world (.integer 99 :: administrativeValue :: environment)
    [.integer, administrativeType, .cell (OptionalCell.cellType nativeType)] ambient.definitions :=
  .cons .integer (.cons (administrativeTyped.weaken ⟨world, rfl⟩) (.cons (.cellRef rfl) .nil))
private def ξ : Renaming := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
private theorem agrees : EnvironmentsAgree ξ environment (.integer 99 :: administrativeValue :: environment) :=
  GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (show EnvironmentsAgree Renaming.id environment environment from fun {_ _} found => found) administrativeValue) (.integer 99)
private theorem sourceTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 2) (.value (.bool false)) after := by
  apply Dynamic.ExpressionEvaluatesOutcome.value
  apply Dynamic.ExpressionEvaluates.intro (raw := .bool false) (middle := after) (lookupExpression?_sound (node := indexNode) (by cbv))
  · change Dynamic.ExpressionFormEvaluates program context [] source sourceEnvironment before (.index (id 0) (id 1)) [] [] (.bool false) after
    apply Dynamic.ExpressionFormEvaluates.indexDefault (coercions := []) rfl
    · exact .intro (lookupExpression?_sound (node := baseNode) (by rfl))
        (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil
    · exact .intro (lookupExpression?_sound (node := keyNode) (by cbv)) (.builtinBoolean rfl) .nil
    · exact .nil
    · exact .bool
  · exact .nil

/-- A real accepted expression constructs its own comparator execution after
source initialization, retaining an ambient closure that is not base-typable. -/
theorem accepted_lazy_preserves {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 2) (fun _ => reason) = .ok code) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (.integer 99 :: administrativeValue :: environment) store (code.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .bool code.type faults (.value (.bool false)) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves (values := values) functions (.refl _) program [] contextValid unique uninitialized missing (certified accepted)
    (show source.lookupExpression? (id 2) = some indexNode by cbv) initial.2 initial.1 locals agrees actualTyped sourceTrace

/-- Source traces and effects follow from completion alone; no source run or
helper evaluation is supplied as a premise. -/
theorem accepted_index_reflects {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 2) (fun _ => reason) = .ok code)
    {value : Value} {finalStore : Store} (completed : Evaluates (.integer 99 :: administrativeValue :: environment) store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source sourceEnvironment before (id 2) outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld .bool code.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [1] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects (values := values) functions (.refl _) program [] contextValid uninitialized missing (certified accepted)
    (show source.lookupExpression? (id 2) = some indexNode by cbv) initial.2 initial.1 locals agrees actualTyped completed

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def sources : List String := [
  "enum Empty { Missing(Word) }",
  "function word_duplicate(m: mapping(Word => Word)) returns (Word) { return m[1]; }",
  "function word_default(m: mapping(Word => Word)) returns (Word) { return m[9]; }",
  "function bool_alias(m: mapping(Bool => Bool)) returns (Bool) { return m[true]; }",
  "function nested(m: mapping(Bool => mapping(Bool => Bool))) returns (Bool) { return m[true][false]; }",
  "function nested_default(m: mapping(Bool => mapping(Bool => Bool))) returns (Bool) { return m[false][true]; }",
  "function missing_default(m: mapping(Bool => Empty)) returns (Empty) { return m[true]; }",
  "function key_fault() returns (Word) { let m: mapping(Word => Word); let missing: Word; return m[missing]; }",
  "function base_fault() returns (Word) { let m: mapping(Bool => mapping(Word => Word)); let missing: Bool; return m[missing][1]; }",
  "function lazy_skip() returns (Bool) { let m: mapping(Bool => Bool); let missing: Bool; return m[false && missing]; }",
  "function parent(seed: Word) returns (Word) { let f = lam(item) -> Word { let m: mapping(Word => Word); return m[~seed]; }; return f(true); }"]
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" sources}] }
private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | fuel + 1, source, expression => match source.lookupExpression? expression with
    | none => []
    | some node => node :: (match node.form with
      | .unary _ operand => reached fuel source operand
      | .binary left _ right => reached fuel source left ++ reached fuel source right
      | .conditional condition thenId elseId => reached fuel source condition ++ reached fuel source thenId ++ reached fuel source elseId
      | .member base _ _ => reached fuel source base
      | .index base key => reached fuel source base ++ reached fuel source key
      | .group inner => reached fuel source inner
      | .tuple ids | .constructor _ ids => ids.flatMap (reached fuel source)
      | _ => [])
private def initialMapping (name : String) (type : TypeSystem.Ty) : SourceCoreCompatibleValues.Value :=
  if name == "word_duplicate" then .mapping .word .word [(.word (Word.ofNatModulo 1), .word (Word.ofNatModulo 7)), (.word (Word.ofNatModulo 1), .word (Word.ofNatModulo 9))]
  else if name == "bool_alias" then .mapping (.comptime .bool) .bool [(.bool true, .bool true), (.bool true, .bool false)]
  else if name == "integer_duplicate" then .mapping .integer .integer [(.integer (-1), .integer (-7)), (.integer (-1), .integer 99)]
  else if name == "nested" || name == "nested_default" then
    .mapping .bool (.mapping .bool .bool) [(.bool true, .mapping .bool .bool [(.bool false, .bool true), (.bool false, .bool false)])]
  else match type with | .mapping key value => .mapping key value [] | _ => .unit
private def inspect {catalog : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (name : String) (expression : ExpressionId) : IO Unit := do
  let mut contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "index diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "index owner diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let nodes := reached 100 source expression
  for node in nodes do
    assertTrue node.coercions.isEmpty "index fixture acquired an output coercion"
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let mut bindings : List (Resolved.LocalId × Ty × Expr × Option Value) := []
  for binderId in ids do
    let declared ← get "index binder" (SourceCoreDataPlaces.rootBinder source binderId)
    let type ← get "index binder projection" (catalog.catalog.project declared.scheme.body)
    let (initializer, expected) ← if declared.name == "missing" then pure (OptionalCell.allocate type, none)
      else if declared.name == "seed" then pure (OptionalCell.allocateInitialized type (.word (Word.ofNatModulo 7)), some (.word (Word.ofNatModulo 7)))
      else if name == "key_fault" || name == "base_fault" || name == "lazy_skip" || name == "parent" then do
        let encoded ← get "expected initialized empty mapping" (SourceCoreCompatibleValues.encode 150 contextValues declared.scheme.body (initialMapping "empty" declared.scheme.body))
        contextValues := encoded.context
        pure (OptionalCell.allocate type, some encoded.value)
      else do
        let encoded ← get "index input encoding" (SourceCoreCompatibleValues.encode 150 contextValues declared.scheme.body (initialMapping name declared.scheme.body))
        contextValues := encoded.context
        let literal ← match SourceCoreCompatibleDataExpressions.quote encoded.value with
          | some literal => pure literal
          | none => throw (IO.userError "mapping input is not quotable")
        pure (OptionalCell.allocateInitialized type literal, some encoded.value)
    bindings := bindings ++ [(binderId, type, initializer, expected)]
  let scope := bindings.map fun (id, type, _, _) => (id, type)
  let representation := SourceCoreCompatibleFunctions.representation contextValues 150
  let lowered ← get s!"actual contextual index {name}" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
    representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
    parent none 150 source scope expression reasonAt)
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer, _) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"actual contextual index {name} failed native checker"
  let root ← match source.lookupExpression? expression with
    | some node => pure node | none => throw (IO.userError "index root missing")
  let malformed : TypedSource := {source with nodes := source.nodes.map fun
    | .expression node => if node.id == expression then .expression {node with type := .unit} else .expression node
    | other => other}
  match SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation catalog.signatures prepared.locals prepared.contexts
    own.assignments diagnostics compilation prepared.callableContext parent none 150 malformed scope expression reasonAt with
  | .ok _ => throw (IO.userError "index mismatched result type accepted")
  | .error _ => pure ()
  for fuel in [0, 3, 15, 1000] do
    let finished := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 30000 checkpoint
      | other => other
    match finished with
    | .done value store =>
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "index changed administrative prefix"
      if name == "key_fault" || name == "base_fault" then
        let missing ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "index missing occurrence absent")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt missing.id))) s!"index {name} changed fault order"
        assertTrue (store.length == bindings.length + 1) "index prepared comparator before successful key"
      else if name == "missing_default" then
        let input ← get "missing-default expected carrier" (SourceCoreCompatibleValues.encode 150 contextValues
          (match root.form with | .index base _ => (source.lookupExpression? base).map (·.type) |>.getD .unit | _ => .unit)
          (initialMapping name (match root.form with | .index base _ => (source.lookupExpression? base).map (·.type) |>.getD .unit | _ => .unit)))
        let .pair (.word tag) _ := input.value | throw (IO.userError "missing-default carrier shape")
        assertTrue (value == .inLeft lowered.type (.word ((reasonAt root.id).add tag))) "index missing-default token lost raw header"
        assertTrue (store.length > bindings.length + 1) "index skipped comparator allocation"
      else
        let .inRight .word payload := value | throw (IO.userError s!"index {name} unexpectedly failed: {reprStr value}")
        let decoded ← get "index result decode" (SourceCoreCompatibleValues.decode 150 contextValues root.type payload)
        let expected := match name with
          | "word_duplicate" => SourceCoreDataValues.Value.word (Word.ofNatModulo 7)
          | "word_default" | "parent" => .word Word.zero
          | "bool_alias" | "nested" => .bool true
          | "integer_duplicate" => .integer (-7)
          | _ => .bool false
        assertTrue (decoded == expected) s!"index {name} wrong selection/default: {reprStr decoded}"
        assertTrue (store.length > bindings.length + 1) "index comparator did not allocate its typed cells"
      for ((_, _, _, expected), position) in bindings.zipIdx do
        match expected with
        | some payload => assertTrue (store[bindings.length - position]? == some (.inRight .unit payload)) "index lost base/key prefix effects"
        | none => pure ()
    | other => throw (IO.userError s!"index {name} failed to finish: {reprStr other}")
/-- Integer is exercised as retained IR; the surface checker does not expose
an Integer type name. The compiler and independent static profile do support it. -/
private def inspectIntegerIR : IO Unit := do
  let checked ← get "Integer retained catalog" (SourceCoreCompatibleCatalog.prepare signatures 100 [.mapping .integer .integer])
  let values := SourceCoreCompatibleValues.Context.initial checked
  let encoded ← get "Integer retained input" (SourceCoreCompatibleValues.encode 100 values (.mapping .integer .integer)
    (initialMapping "integer_duplicate" (.mapping .integer .integer)))
  let values := encoded.context
  let native ← get "Integer retained projection" (checked.catalog.project (.mapping .integer .integer))
  let tableBinder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono (.mapping .integer .integer), [], false, none⟩
  let keyBinder : TypedBinder := ⟨⟨owner, 1⟩, "key", .mono .integer, [], false, none⟩
  let tableNode : ExpressionNode := {id := id 0, span, type := .mapping .integer .integer, form := .reference "table" (.local tableBinder.id)}
  let keyNode : ExpressionNode := {id := id 1, span, type := .integer, form := .reference "key" (.local keyBinder.id)}
  let root : ExpressionNode := {id := id 2, span, type := .integer, form := .index (id 0) (id 1)}
  let source : TypedSource := {owner, inputs := [tableBinder, keyBinder], roots := [.expression root.id], nodes := [.expression tableNode, .expression keyNode, .expression root]}
  let scope := [(tableBinder.id, native), (keyBinder.id, Ty.integer)]
  let code ← get "Integer retained actual lowering" (SourceCoreFunctions.lowerExpressionWithPolicy
    (SourceCoreCompatibleDataExpressions.functionPolicy 100 values) noBody 20 compilation source scope root.id (fun _ => reason))
  let literal ← match SourceCoreCompatibleDataExpressions.quote encoded.value with
    | some expression => pure expression | none => throw (IO.userError "Integer input quote failed")
  let body := Expr.letE (OptionalCell.allocateInitialized .integer (.integer (-1)))
    (.letE (OptionalCell.allocateInitialized native literal) code.expression)
  let program : Core.Program := ⟨LanguageResult.resultType code.type, body, checked.catalog.definitions⟩
  assertTrue program.check "Integer retained index failed Core checker"
  match program.runStateful 30000 with
  | .done (.inRight .word (.integer value)) store =>
    assertTrue (value == -7 && store.length > 2) "Integer retained duplicate selection/comparator allocation failed"
  | other => throw (IO.userError s!"Integer retained index failed: {reprStr other}")

def run : IO Unit := do
  inspectIntegerIR
  let checkedProgram ← get "index checker" (checkProgram workspace)
  let roots := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"index specialization: {reprStr other}")
  let automatic ← get "actual index factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      let source := function.specialized.function.typedBody
      let expression ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some expression => pure expression | none => throw (IO.userError "index return missing")
      inspect automatic.prepared source function.signature.key none function.specialized.function.solvedRequirements name expression
      rootsSeen := rootsSeen + 1
  let mut parentsSeen := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      for entry in parent.source.nodes do
        match entry with
        | .expression node => match node.form with
          | .index _ _ =>
            inspect automatic.prepared parent.source parent.caller.key (some parent) parent.caller.function.solvedRequirements "parent" node.id
            parentsSeen := parentsSeen + 1
          | _ => pure ()
        | _ => pure ()
  assertTrue (rootsSeen == 9) s!"index cases missing: {rootsSeen}"
  assertTrue (parentsSeen > 0) "full parent substitution index case missing"
  IO.println "actual contextual indices: scalar keys, duplicates, defaults, nested/raw header, ordered faults, lazy effects, parent, ambient comparator closures and resume GREEN"

end Tests.SourceCoreCompatibleExpressionIndices
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleExpressionLiterals
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual root and specialized-parent literal emissions are certified before
execution. Both numeric targets, Unit, Bool, legacy Word spelling, malformed
retained evidence and exact store preservation are exercised. Unary minus is
outside the atomic certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionLiterals
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionLiterals CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_literals", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_literals.solc"⟩, 0, 4⟩
private def id : ExpressionId := ⟨⟨owner, 0⟩⟩
private def boolNode : ExpressionNode := { id, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def boolSource : TypedSource := { owner, inputs := [], roots := [.expression id], nodes := [.expression boolNode] }
private def boolCode : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def sourceContext : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private theorem valid : ContextValid [] sourceContext [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, sourceContext, SourceSemantics.Context.ofSignatures]
  · intro requirement member
    simp [sourceContext, SourceSemantics.Context.ofSignatures] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [sourceContext, SourceSemantics.Context.ofSignatures] at member

private theorem boolAccepted (values : SourceCoreCompatibleValues.Context) (compilation : SourceCoreFunctions.Context)
    (body : SourceCoreFunctions.BodyLowerer)
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked boolSource id = .ok (boolNode, .bool)) :
    SourceCoreFunctions.lowerExpressionWithPolicy (SourceCoreCompatibleDataExpressions.functionPolicy 10 values)
      body 10 {compilation with solvedRequirements := []} boolSource [] id (fun _ => Word.zero) = .ok boolCode := by
  have found : boolSource.lookupExpression? id = some boolNode := rfl
  have sameOwner : id.occurrence.owner = boolSource.owner := rfl
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  simp only [SourceCoreCompatibleDataExpressions.functionPolicy, sameOwner, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure]
  simp only [boolNode]
  rw [read]
  simp only [bind, Except.bind, boolNode]
  unfold SourceCoreCompatibleDataExpressions.leafLowerer
  rw [read]
  change SourceCoreBasic.lowerExpression 10 boolSource [] id Word.zero = .ok boolCode
  rfl


/-- Completed actual Bool code reconstructs its independent source trace even
with arbitrary ambient closures in the represented heap and inserted slots. -/
theorem bool_reflects {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (values : SourceCoreCompatibleValues.Context) (compilation : SourceCoreFunctions.Context)
    (body : SourceCoreFunctions.BodyLowerer)
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked boolSource id = .ok (boolNode, .bool))
    {mapping world administrative environment canonical actual before store ξ value after}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
      administrative [] environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (boolCode.expression.rename ξ) value after) :
    ∃ outcome sourceAfter finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext [] boolSource environment before id outcome sourceAfter ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        finalMap finalWorld .bool boolCode.type (fun _ _ => False) outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked registry functions finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap after ∧ Dynamic.HeapMetadataExtend before sourceAfter := by
  have receipt : Certificate [] boolSource id boolCode := of_functions (values := values)
    (by rfl) (.bool _ _) (by intro impossible; cases impossible)
    (by intros; rfl) rfl rfl (boolAccepted values compilation body read)
  exact reflects functions program sourceContext [] valid boolSource (fun _ _ => False)
    receipt (by rfl) environments heaps locals agrees evaluated

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def huge : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639937
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function unit() { return (); }",
    "function boolean() returns (Bool) { return true; }",
    "function word() returns (Word) { return 37; }",
    s!"function wordWrap() returns (Word) \{ return {huge}; }",
    s!"function big() returns (integer) \{ return {huge}; }",
    "function parent(seed: Word) returns (Word) { let echo = lam(value) { return seed + 37; }; return echo(true); }"
  ]}] }

private def scalar? : Expr → Option Core.Value
  | .unit => some .unit | .bool b => some (.bool b) | .word w => some (.word w)
  | .integer n => some (.integer n) | _ => none

private def inspectNode {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (node : ExpressionNode) (atomic : Atomic node.form) : IO (Option Ty) := do
  let values := SourceCoreCompatibleValues.Context.initial checked
  let representation := SourceCoreCompatibleFunctions.representation values 100
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "literal diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "literal root diagnostics missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  if found : source.lookupExpression? node.id = some node then
    if requirements : node.requirements = owned node.form then
      if coercions : node.coercions = [] then
        if notInitializer : prepared.locals.bindings.find? (fun binding => decide (binding.caller = owner ∧ binding.initializer = node.id)) = none then
          if unitType : node.form = .tuple [] → node.type = .unit then
            match accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation
                checked.signatures prepared.locals prepared.contexts own.assignments diagnostics context prepared.callableContext
                parent none 100 source [] node.id reasonAt with
            | .error error => throw (IO.userError s!"actual contextual literal rejected: {reprStr error}")
            | .ok lowered =>
              have receipt : Certificate solved source node.id lowered := of_contextual (values := values)
                found atomic unitType requirements coercions notInitializer rfl rfl accepted
              let _receipt := receipt
              let expected ← match lowered.expression with
                | .inRight .word payload => match scalar? payload with
                  | some value => pure (.inRight .word value)
                  | none => throw (IO.userError "atomic output is not a scalar")
                | _ => throw (IO.userError "literal changed language result carrier")
              match node.form with
              | .integerLiteral _ resolution =>
                match resolution.targetType, expected with
                | .word, .inRight .word (.word value) =>
                  assertTrue (value == Word.ofNatModulo resolution.rawValue) "Word literal lost modulo meaning"
                | .integer, .inRight .word (.integer value) =>
                  assertTrue (value == Int.ofNat resolution.rawValue) "Integer literal lost unbounded meaning"
                | _, _ => throw (IO.userError "numeric target changed")
                let malformed := { node with requirements := [] }
                let bad := { source with nodes := source.nodes.map fun
                  | .expression old => if old.id = node.id then .expression malformed else .expression old
                  | .statement old => .statement old }
                assertTrue ((SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation
                  checked.signatures prepared.locals prepared.contexts own.assignments diagnostics context prepared.callableContext
                  parent none 100 bad [] node.id reasonAt).toOption.isNone) "missing numeric requirement was accepted"
              | _ => pure ()
              let code := .letE (.newCell (.function .unit .unit) (.lambda .unit .unit .unit)) (lowered.expression.weakenAt 0)
              let native : Core.Program := ⟨LanguageResult.resultType lowered.type, code, checked.catalog.definitions⟩
              assertTrue native.check "actual literal failed Core checker"
              for fuel in [0, 2, 1000] do
                let completed := match native.runStateful fuel with
                  | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
                  | other => other
                match completed with
                | .done value store =>
                  assertTrue (value == expected && store == [.closure .unit .unit .unit []]) "literal modified administrative closure store"
                | other => throw (IO.userError s!"literal did not complete: {reprStr other}")
              pure (some lowered.type)
          else pure none
        else pure none
      else pure none
    else pure none
  else pure none

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) : IO (List Ty) := do
  let mut types := []
  for entry in source.nodes do
    match entry with
    | .expression node =>
      let result ← match form : node.form with
        | .tuple [] => inspectNode prepared source owner parent solved node (form ▸ .unit)
        | .reference name (.builtinBoolean value) => inspectNode prepared source owner parent solved node (form ▸ .bool name value)
        | .literal value => inspectNode prepared source owner parent solved node (form ▸ .word value)
        | .integerLiteral value resolution => inspectNode prepared source owner parent solved node (form ▸ .integer value resolution)
        | _ => pure none
      if let some type := result then types := types ++ [type]
    | _ => pure ()
  pure types

def run : IO Unit := do
  let program ← get "literal source checker" (checkProgram workspace)
  let roots ← ["unit", "boolean", "word", "wordWrap", "big", "parent"].mapM fun name =>
    match program.signatures.functions.find? (·.name == name) with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
    | none => throw (IO.userError s!"literal root missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program roots 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"literal specialization: {reprStr other}")
  let automatic ← get "actual literal compatible factory" (SourceCoreCompatibleFunctions.prepare program plan 300)
  let mut types := []
  for function in automatic.prepared.functions do
    types := types ++ (← inspect automatic.prepared function.specialized.function.typedBody
      function.signature.key none function.specialized.function.solvedRequirements)
  let wordId ← match program.signatures.functions.find? (·.name == "word") with
    | some signature => pure signature.id | none => throw (IO.userError "legacy literal declaration missing")
  let wordFunction ← match automatic.prepared.functions.find? (·.signature.key.declaration == wordId) with
    | some function => pure function | none => throw (IO.userError "legacy literal owner missing")
  let original := wordFunction.specialized.function.typedBody
  let numeric ← match original.nodes.findSome? fun
    | .expression node => match node.form with | .integerLiteral .. => some node | _ => none
    | _ => none with
    | some node => pure node | none => throw (IO.userError "legacy literal occurrence missing")
  let legacy := { numeric with form := .literal (.decimal "37"), requirements := [], coercions := [] }
  let legacySource := { original with nodes := original.nodes.map fun
    | .expression old => if old.id = legacy.id then .expression legacy else .expression old
    | .statement old => .statement old }
  let legacyResult ← inspectNode automatic.prepared legacySource wordFunction.signature.key none
    wordFunction.specialized.function.solvedRequirements legacy (.word _)
  assertTrue (legacyResult == some .word) "legacy Word-spelling branch missing"
  let mut contextual := []
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      contextual := contextual ++ (← inspect automatic.prepared parent.source parent.caller.key
        (some parent) parent.caller.function.solvedRequirements)
  for required in [Ty.unit, .bool, .word, .integer] do
    assertTrue (types.contains required) s!"literal target missing: {reprStr required}"
  assertTrue (!contextual.isEmpty) "full parent context literal missing"
  IO.println "actual contextual literal certificates: Unit/Bool/Word/Integer, parent substitution, malformed evidence and resume GREEN"

end Tests.SourceCoreCompatibleExpressionLiterals
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleExpressionMembers
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Member syntax is retained typed IR, with independent uniform-field typing.
Actual checked catalogs and contextual compilation exercise native selection;
no claim is made that the surface parser admits positional member expressions. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionMembers
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionMembers CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"member_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "member_meaning.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def sourceType : TypeSystem.Ty := .nominal owner []
private def firstSignature : ProgramDataConstructorSignature :=
  ⟨⟨owner, 0⟩, "First", [.bool, .bool], ⟨span, ⟨[], ⟨span, "First"⟩, none⟩⟩⟩
private def secondSignature : ProgramDataConstructorSignature :=
  ⟨⟨owner, 1⟩, "Second", [.bool, .bool], ⟨span, ⟨[], ⟨span, "Second"⟩, none⟩⟩⟩
private def signature : ProgramDataSignature := {
  id := owner, name := "Row", parameters := [], constructors := [firstSignature, secondSignature]
  source := ⟨span, ⟨none, ⟨span, "Row"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def instantiation : DataConstructorInstantiation := ⟨secondSignature.id, [], [.bool, .bool], sourceType⟩
private def boolean : ExpressionNode := { id := id 0, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def constructorNode : ExpressionNode := { id := id 1, span, type := sourceType, form := .constructor instantiation [id 0, id 0] }
private def memberNode : ExpressionNode := { id := id 2, span, type := .bool, form := .member (id 1) "1" 1 }
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 2)], nodes := [.expression boolean, .expression constructorNode, .expression memberNode] }
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private def faults : FunctionCalls.FaultRep := fun error token =>
  (∃ location, error = .uninitializedLocation location) ∧ token = reason
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index native selected; cases selected
private theorem instanceValid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation := by
  refine .intro signature secondSignature (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    (by simp [signature]) rfl rfl ⟨by simp [signature], by simp [ParameterSubstitution.domain, instantiation, signature]⟩ ?_ rfl rfl
  intro parameter replacement member; cases member
private theorem nominalAdmitted : TypeAdmissible context sourceType :=
  ⟨TypeParameterBindersWellFormed.ofSignatures signatures,
    .nominal signature [] (by simp [context, SourceSemantics.Context.ofSignatures, signatures]) rfl .nil⟩
private theorem boolAdmitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
private theorem boolTyped : ExpressionHasType source context (id 0) .bool := by
  apply ExpressionHasType.ofOrdinary (node := boolean) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem constructorTyped : ExpressionHasType source context (id 1) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := constructorNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.constructor instanceValid.toAdmissible (.cons boolTyped (.cons boolTyped (.nil _)))) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem projection : UniformMemberProjection context sourceType 1 .bool := by
  refine .intro (dataType := signature) (substitution := []) (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    ⟨by simp [signature], by simp [ParameterSubstitution.domain, signature]⟩ rfl nominalAdmitted boolAdmitted (by simp [signature]) ?_ ?_
  · intro constructor member
    simp only [signature, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro actual admissible resultType
    cases admissible with
    | intro dataType constructor dataMember constructorMember _ _ _ _ payloads _ =>
      have same : dataType = signature := by simpa [context, SourceSemantics.Context.ofSignatures, signatures] using dataMember
      subst dataType
      simp only [signature, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at constructorMember
      rcases constructorMember with rfl | rfl <;> rw [payloads] <;> rfl
private theorem memberTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := memberNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.member constructorTyped projection) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem syntaxTree : CompatibleExpressionMembers.Syntax source (id 2) := by
  refine .member (node := memberNode) (by cbv) rfl (.fragment (.constructor (node := constructorNode) (by cbv) rfl ?_))
  intro child member
  have same : child = id 0 := by simpa using member
  subst child
  exact .fragment (.primitive (.product (.literal (node := boolean) (by cbv) (.bool _ _))))
private theorem contextValid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures]
  · intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; simp [context, SourceSemantics.Context.ofSignatures] at member
variable {checked : SourceCoreCompatibleCatalog.Checked}
private abbrev values (checked : SourceCoreCompatibleCatalog.Checked) := SourceCoreCompatibleValues.Context.initial checked
private abbrev policy (checked : SourceCoreCompatibleCatalog.Checked) := SourceCoreCompatibleDataExpressions.functionPolicy 20 (values checked)
private theorem certified (catalogSignatures : checked.signatures = signatures) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 5 compilation source [] (id 2) (fun _ => reason) = .ok code) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 2) code :=
  tree_of_functions (values := values checked) unique declarations catalogSignatures.symm rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) memberTyped accepted

theorem contextual_certificate
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {lowered : SourceCoreBasic.LoweredExpr}
    (catalogSignatures : checked.signatures = signatures)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead 20 (values checked))
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer (values checked))
    (generated : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures ⟨[]⟩ parents assignments
      diagnostics compilation native parent none 5 source [] (id 2) (fun _ => reason) = .ok lowered) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 2) lowered := by
  exact tree_of_contextual (values := values checked)
    ⟨fun _ _ _ found => (metadata found).1, fun _ _ _ found => (metadata found).2, by intros; rfl, by intros; rfl⟩
    unique rfl rfl declarations catalogSignatures.symm syntaxTree (by cbv) memberTyped readPolicy lowerPolicy leafPolicy generated

theorem actual_preserves {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked (values checked).registry functions)
      program context [] source (Tree 20 (values checked) source context [] (fun _ => reason)) faults :=
  preserves (values := values checked) functions (.refl _) program [] contextValid unique (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)
theorem actual_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked (values checked).registry functions)
      program context [] source (Tree 20 (values checked) source context [] (fun _ => reason)) faults :=
  reflects (values := values checked) functions (.refl _) program [] contextValid (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)

theorem accepted_member_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (catalogSignatures : checked.signatures = signatures)
    {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 5 compilation source [] (id 2) (fun _ => reason) = .ok code)
    {mapping world administrative environment canonical actual before store ξ value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
      administrative [] environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked (values checked).registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (completed : Evaluates actual store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source environment before (id 2) outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked (values checked).registry functions)
        finalMap finalWorld memberNode.type code.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked (values checked).registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  actual_reflects functions (certified catalogSignatures accepted) (by cbv) environments heaps locals agrees completed

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)


private def sources : List String := [
  "enum Row<T> { First(T, Bool), Second(T, Bool) }",
  "enum Box<T> { Box(T) }",
  "function first() returns (Row<Word>) { return .First(7, true); }",
  "function second() returns (Row<Word>) { return .Second(9, false); }",
  "function flag() returns (Row<Word>) { return .Second(9, false); }",
  "function nested() returns (Box<Row<Word>>) { return .Box(.Second(9, false)); }",
  "function nominal() returns (Box<Row<Word>>) { return .Box(.First(7, true)); }",
  "function first_fault() returns (Row<Word>) { let missing: Word; return .First(missing, true); }",
  "function base_fault() returns (Row<Word>) { let missing: Row<Word>; return missing; }",
  "function map_success() returns (Row<mapping(Word => Word)>) { let m: mapping(Word => Word); return .First(m, false); }",
  "function map_fault() returns (Row<mapping(Word => Word)>) { let m: mapping(Word => Word); let missing: Bool; return .First(m, missing); }",
  "function parent(seed: Word) returns (Row<Word>) { let f = lam(item) -> Row<Word> { return .First(~seed, true); }; return f(true); }"]
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" sources}] }

private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | fuel + 1, source, expression => match source.lookupExpression? expression with
    | none => []
    | some node => node :: (match node.form with
      | .unary _ operand => reached fuel source operand
      | .binary left _ right => reached fuel source left ++ reached fuel source right
      | .conditional condition thenId elseId => reached fuel source condition ++ reached fuel source thenId ++ reached fuel source elseId
      | .member base _ _ => reached fuel source base
      | .group inner => reached fuel source inner
      | .tuple ids | .constructor _ ids => ids.flatMap (reached fuel source)
      | _ => [])
private def inspect {catalog : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (name : String) (expression : ExpressionId) : IO Unit := do
  let contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let representation := SourceCoreCompatibleFunctions.representation contextValues 150
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "member diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "member root diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let originalRoot ← match source.lookupExpression? expression with
    | some node => pure node | none => throw (IO.userError "member original root missing")
  let path := if name == "nested" then [0, 0] else if name == "flag" then [1] else [0]
  let mut source := source
  let mut expression := expression
  let mut expectedRaw := originalRoot.type
  for (index, position) in path.zipIdx do
    let (declaration, arguments) ← match SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType expectedRaw) with
      | some parts => pure parts | none => throw (IO.userError "member fixture nominal path missing")
    let signature ← match catalog.signatures.dataTypes.find? (·.id == declaration) with
      | some signature => pure signature | none => throw (IO.userError "member fixture signature missing")
    let first ← match signature.constructors with
      | first :: _ => pure first | [] => throw (IO.userError "member fixture empty declaration")
    let payloads := first.payloadTypes.map
      (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip arguments))
    let field ← match payloads[index]? with
      | some type => pure type | none => throw (IO.userError "member fixture index absent")
    let next : ExpressionId := ⟨⟨source.owner, 100000 + position⟩⟩
    let node : ExpressionNode := { id := next, span := originalRoot.span, type := field, form := .member expression (toString index) index }
    source := {source with roots := [.expression next], nodes := source.nodes ++ [.expression node]}
    expression := next
    expectedRaw := field
  let nodes := reached 100 source expression
  for node in nodes do
    assertTrue node.coercions.isEmpty "member fixture acquired an output coercion"
    match node.form with
    | .unary .. | .binary .. | .conditional .. => assertTrue node.requirements.isEmpty "member fixture acquired method dispatch evidence"
    | _ => pure ()
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let bindings ← ids.mapM fun binder => do
    let declared ← get "member binder" (SourceCoreDataPlaces.rootBinder source binder)
    let type ← get "member binder projection" (catalog.catalog.project declared.scheme.body)
    let initializer ← if declared.name == "missing" || declared.name == "otherMissing" then pure (OptionalCell.allocate type)
      else match declared.scheme.body with
      | .bool => pure (OptionalCell.allocateInitialized type (.bool true))
      | .word => pure (OptionalCell.allocateInitialized type (.word (Word.ofNatModulo (if declared.name == "b" then 3 else 7))))
      | .integer => pure (OptionalCell.allocateInitialized type (.integer (if declared.name == "b" then 3 else -7)))
      | .mapping .. => pure (OptionalCell.allocate type)
      | other => throw (IO.userError s!"unexpected member scope: {reprStr other}")
    pure (binder, type, initializer)
  let scope := bindings.map fun (id, type, _) => (id, type)
  let lowered ← get s!"actual contextual member {name}" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
    representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
    parent none 150 source scope expression reasonAt)
  if name == "first" then
    for malformed in [(.member originalRoot.id "2" 2, .word), (.member originalRoot.id "0" 0, .bool)] do
      let forged := { source with nodes := source.nodes.map fun
        | .expression node => if node.id == expression then .expression {node with form := malformed.1, type := malformed.2} else .expression node
        | other => other }
      match SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation catalog.signatures
        prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext parent none 150 forged scope expression reasonAt with
      | .ok _ => throw (IO.userError "malformed member metadata accepted")
      | .error _ => pure ()
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"actual contextual member {name} failed native checker"
  let mappingValue ← if name.startsWith "map_" then do
    let encoded ← get "expected empty mapping" (SourceCoreCompatibleValues.encode 100 contextValues
      (.mapping .word .word) (.mapping .word .word []))
    pure encoded.value
    else pure .unit
  for fuel in [0, 3, 15, 1000] do
    let finished := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 3000 checkpoint
      | other => other
    match finished with
    | .done value store =>
      assertTrue (store.length == bindings.length + 1) "member allocated unexpected cells"
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "member changed administrative closure"
      if name.endsWith "fault" then
        let faultNode ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "fault fixture lacks missing occurrence")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt faultNode.id))) s!"member {name} fault reason/order changed"
      else
        let payload ← match value with
          | .inRight .word payload => pure payload
          | _ => throw (IO.userError s!"member {name} did not succeed: {reprStr value}")
        let root ← match source.lookupExpression? expression with
          | some node => pure node | none => throw (IO.userError "root source metadata missing")
        let decoded ← get "actual member decode" (SourceCoreCompatibleValues.decode 100 contextValues root.type payload)
        match name, decoded with
        | "first", .word value => assertTrue (value == Word.ofNatModulo 7) "first constructor selected wrong field"
        | "second", .word value | "nested", .word value => assertTrue (value == Word.ofNatModulo 9) "second constructor selected wrong field"
        | "flag", .bool false => pure ()
        | "nominal", .constructed retained [.word value, .bool true] =>
          let expected ← match nodes.find? (fun node => match node.form with | .constructor _ ids => ids.length == 2 | _ => false) with
            | some node => pure node | none => throw (IO.userError "nested original header missing")
          let .constructor original _ := expected.form | throw (IO.userError "expected source constructor")
          assertTrue (retained == original && value == Word.ofNatModulo 7) "member erased selected raw constructor header"
        | "map_success", .mapping .word .word [] => pure ()
        | "parent", .word value => assertTrue (value == (Word.ofNatModulo 7).bitNot) "parent member selected wrong payload"
        | _, _ => throw (IO.userError s!"unexpected member {name}: {reprStr decoded}")
      for (position, (binder, type, _)) in bindings.zipIdx.map (fun (binding, position) => (position, binding)) do
        if (match (← get "member binder metadata" (SourceCoreDataPlaces.rootBinder source binder)).scheme.body with | .mapping .. => true | _ => false) then
          let declared ← get "mapping branch binder" (SourceCoreDataPlaces.rootBinder source binder)
          let expectedCell := if declared.name == "m" then Value.inRight .unit mappingValue else .inLeft type .unit
          assertTrue (store[bindings.length - position]? == some expectedCell)
            "member initialized the skipped mapping or lost the selected mapping"
    | other => throw (IO.userError s!"member {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let checkedProgram ← get "member checker" (checkProgram workspace)
  let roots := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"member specialization: {reprStr other}")
  let automatic ← get "actual member factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      let source := function.specialized.function.typedBody
      let expression ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some expression => pure expression | none => throw (IO.userError "member return missing")
      inspect automatic.prepared source function.signature.key none function.specialized.function.solvedRequirements name expression
      rootsSeen := rootsSeen + 1
  let mut parentsSeen := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      for entry in parent.source.nodes do
        match entry with
        | .expression node => match node.form with
          | .constructor _ _ =>
            inspect automatic.prepared parent.source parent.caller.key (some parent) parent.caller.function.solvedRequirements "parent" node.id
            parentsSeen := parentsSeen + 1
          | _ => pure ()
        | _ => pure ()
  assertTrue (rootsSeen == 9) s!"member cases missing: {rootsSeen}"
  assertTrue (parentsSeen > 0) "full parent substitution member case missing"
  IO.println "actual contextual members: both tags, chained/raw nominal field, base/child fault, lazy mapping effects, parent context, ambient closure and resume GREEN"

end Tests.SourceCoreCompatibleExpressionMembers
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleExpressionPrimitives
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! The kernel tests consume actual compiler results and independent source
shape typing. Runtime tests cover a lazy mapping read before a right-hand
fault, inserted slots, a full parent context, and administrative closures. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionPrimitives
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionPrimitives CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_products", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "products.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def boolean (index : Nat) (value : Bool) : ExpressionNode :=
  { id := id index, span, type := .bool, form := .reference "boolean" (.builtinBoolean value) }
private def unaryNode : ExpressionNode := { id := id 2, span, type := .bool, form := .unary .logicalNot (id 0) }
private def binaryNode : ExpressionNode := { id := id 3, span, type := .bool, form := .binary (id 2) .logicalOr (id 1) }
private def grouped : ExpressionNode := { id := id 4, span, type := .bool, form := .group (id 3) }
private def paired : ExpressionNode := { id := id 5, span, type := .product .bool .bool, form := .tuple [id 4, id 1] }
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 5)],
    nodes := [.expression (boolean 0 true), .expression (boolean 1 false), .expression unaryNode, .expression binaryNode, .expression grouped, .expression paired] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private def faults : FunctionCalls.FaultRep := fun error token =>
  (∃ location, error = .uninitializedLocation location) ∧ token = reason
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index native selected
  cases selected
private theorem syntaxTree : CompatibleExpressionPrimitives.Syntax source (id 5) :=
  .pair (node := paired) (by cbv) rfl
    (.group (node := grouped) (by cbv) rfl
      (.binary (node := binaryNode) (by cbv) rfl
        (.unary (node := unaryNode) (by cbv) rfl (.product (.literal (node := boolean 0 true) (by cbv) (.bool _ _))))
        (.product (.literal (node := boolean 1 false) (by cbv) (.bool _ _)))))
    (.product (.literal (node := boolean 1 false) (by cbv) (.bool _ _)))
private theorem boolTyped {index : Nat} {value : Bool}
    (found : source.lookupExpression? (id index) = some (boolean index value)) :
    ExpressionHasType source context (id index) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := boolean index value) (rawType := .bool)
    (lookupExpression?_sound found) (.reference (.builtinBoolean value)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem unaryTyped : ExpressionHasType source context (id 2) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := unaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.unary (boolTyped (value := true) (by cbv)) .logicalNot) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem binaryTyped : ExpressionHasType source context (id 3) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := binaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.binary unaryTyped (boolTyped (value := false) (by cbv)) .booleanOr) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem groupedTyped : ExpressionHasType source context (id 4) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := grouped) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.group binaryTyped) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem pairedTyped : ExpressionHasType source context (id 5) (.product .bool .bool) := by
  have boolAdmitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  have admitted : TypeAdmissible context (.product .bool .bool) := .product boolAdmitted boolAdmitted
  apply ExpressionHasType.ofOrdinary (node := paired) (rawType := .product .bool .bool)
    (lookupExpression?_sound (by cbv)) (.tuple (.cons groupedTyped (.cons (boolTyped (value := false) (by cbv)) (.nil _)))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures]
  · intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; simp [context, SourceSemantics.Context.ofSignatures] at member
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.product .bool .bool]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.product .bool .bool]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def policy := SourceCoreCompatibleDataExpressions.functionPolicy 20 values
private def unaryCode := LocalPrimitiveResults.unary .boolNot (LanguageResult.success (.bool true))
private def binaryCode := SourceCorePrimitive.binary .logicalOr unaryCode (LanguageResult.success (.bool false))
private def code : SourceCoreBasic.LoweredExpr :=
  ⟨.product .bool .bool, LocalSequence.pair .bool .bool binaryCode (LanguageResult.success (.bool false))⟩
private theorem boolAccepted (fuel index : Nat) (value : Bool)
    (found : source.lookupExpression? (id index) = some (boolean index value))
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id index) = .ok (boolean index value, .bool))
    (basic : SourceCoreBasic.lowerExpression (fuel + 1) source [] (id index) reason =
      .ok ⟨.bool, LanguageResult.success (.bool value)⟩) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 1) compilation source [] (id index) (fun _ => reason) =
      .ok ⟨.bool, LanguageResult.success (.bool value)⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id index).occurrence.owner = source.owner := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure]
  simp only [boolean]
  rw [read]
  simp only [bind, Except.bind, boolean]
  unfold SourceCoreCompatibleDataExpressions.leafLowerer
  rw [read]
  exact basic
private theorem unaryAccepted (fuel : Nat) : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 2) compilation source [] (id 2) (fun _ => reason) = .ok ⟨.bool, unaryCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 2).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 2) = some unaryNode := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 2) = .ok (unaryNode, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, unaryNode]
  rw [read]
  simp only [bind, Except.bind, unaryNode]
  have childEq := boolAccepted fuel 0 true rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at childEq
  rw [childEq]
  rfl
private theorem binaryAccepted (fuel : Nat) : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 3) compilation source [] (id 3) (fun _ => reason) = .ok ⟨.bool, binaryCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 3).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 3) = some binaryNode := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 3) = .ok (binaryNode, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, binaryNode]
  rw [read]
  simp only [bind, Except.bind, binaryNode]
  have firstEq := unaryAccepted fuel
  have secondEq := boolAccepted (fuel + 1) 1 false rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at firstEq secondEq
  rw [firstEq]
  simp only [bind, Except.bind]
  rw [secondEq]
  rfl
private theorem groupAccepted (fuel : Nat) : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 4) compilation source [] (id 4) (fun _ => reason) = .ok ⟨.bool, binaryCode⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 4).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 4) = some grouped := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 4) = .ok (grouped, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, grouped]
  rw [read]
  simp only [bind, Except.bind, grouped]
  have childEq := binaryAccepted fuel
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at childEq
  rw [childEq]
  rfl
private theorem accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 6 compilation source [] (id 5) (fun _ => reason) = .ok code := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 5).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 5) = some paired := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 5) = .ok (paired, (.product .bool .bool)) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, paired]
  rw [read]
  simp only [bind, Except.bind, paired]
  have firstEq := groupAccepted 1
  have secondEq := boolAccepted 4 1 false rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at firstEq secondEq
  rw [firstEq]
  simp only [bind, Except.bind]
  rw [secondEq]
  rfl
private theorem certified : Tree 20 values source context [] (fun _ => reason) [] (id 5) code :=
  tree_of_functions unique declarations ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) pairedTyped accepted

/-- The actual production contextual dispatcher is also the source of the
static tree; the compilation equation is the only compiler-result premise. -/
theorem contextual_certificate
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {lowered : SourceCoreBasic.LoweredExpr}
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead 20 values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (generated : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures ⟨[]⟩ parents assignments
      diagnostics compilation native parent none 6 source [] (id 5) (fun _ => reason) = .ok lowered) :
    Tree 20 values source context [] (fun _ => reason) [] (id 5) lowered := by
  exact tree_of_contextual
    ⟨fun _ _ _ found => (metadata found).1, fun _ _ _ found => (metadata found).2, by intros; rfl, by intros; rfl⟩
    unique declarations syntaxTree (by cbv) pairedTyped readPolicy lowerPolicy leafPolicy generated

/-- Both directions use the whole tree induction. No child evaluator proof is
supplied, even when the ambient heap contains captures of fresh nominal frames. -/
theorem actual_preserves {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked values.registry functions)
      program context [] source (Tree 20 values source context [] (fun _ => reason)) faults :=
  preserves (values := values) (source := source) (fuel := 20) (reasonAt := fun _ => reason) (faults := faults) functions (.refl _) program [] valid unique (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)
theorem actual_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked values.registry functions)
      program context [] source (Tree 20 values source context [] (fun _ => reason)) faults :=
  reflects (values := values) (source := source) (fuel := 20) (reasonAt := fun _ => reason) (faults := faults) functions (.refl _) program [] valid (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)

theorem accepted_pair_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {mapping world administrative environment canonical actual before store ξ value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
      administrative [] environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (completed : Evaluates actual store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source environment before (id 5) outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked values.registry functions)
        finalMap finalWorld paired.type code.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  actual_reflects functions certified (by cbv) environments heaps locals agrees completed



private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def operators : List (String × String × Bool × Value × Value) := [
  ("mul", "*", false, .word (Word.ofNatModulo 21), .integer (-21)),
  ("div", "/", false, .word (Word.ofNatModulo 2), .integer ((-7 : Int) / 3)),
  ("mod", "%", false, .word (Word.ofNatModulo 1), .integer ((-7 : Int) % 3)),
  ("add", "+", false, .word (Word.ofNatModulo 10), .integer (-4)),
  ("sub", "-", false, .word (Word.ofNatModulo 4), .integer (-10)),
  ("band", "&", false, .word (Word.ofNatModulo 3), .integer 1),
  ("bxor", "^", false, .word (Word.ofNatModulo 4), .integer (-6)),
  ("bor", "|", false, .word (Word.ofNatModulo 7), .integer (-5)),
  ("lt", "<", true, .bool false, .bool true),
  ("gt", ">", true, .bool true, .bool false),
  ("le", "<=", true, .bool false, .bool true),
  ("ge", ">=", true, .bool true, .bool false),
  ("eq", "==", true, .bool false, .bool false),
  ("ne", "!=", true, .bool true, .bool true)]
private def operatorSources : List String := (operators.filter fun (name, _, _, _, _) => !["lt", "le", "ge", "ne"].contains name).map fun (name, op, comparison, _, _) =>
  s!"function word_{name}(a: Word, b: Word) returns ({if comparison then "Bool" else "Word"}) \{ return a {op} b; }"
private def extraSources : List String := [
  "function bool_not(flag: Bool) returns (Bool) { return !flag; }",
  "function word_not(a: Word) returns (Word) { return ~a; }",
  "function and_skip() returns (Bool) { let missing: Bool; return false && missing; }",
  "function or_skip() returns (Bool) { let missing: Bool; return true || missing; }",
  "function and_fault() returns (Bool) { let missing: Bool; return true && missing; }",
  "function or_fault() returns (Bool) { let missing: Bool; return false || missing; }",
  "function left_fault() returns (Word) { let missing: Word; let otherMissing: Word; return missing + otherMissing; }",
  "function right_fault(a: Word) returns (Word) { let missing: Word; return a + missing; }",
  "function map_fault() returns ((mapping(Word => Word), Bool)) { let m: mapping(Word => Word); let missing: Bool; return (m, !missing); }",
  "function map_skip() returns ((mapping(Word => Word), Bool)) { let m: mapping(Word => Word); let missing: Bool; return (m, false && missing); }",
  "function parent(seed: Word) returns ((Bool, Bool)) { let f = lam(flag) { return (~seed > 3, flag); }; return f(true); }"]
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" (operatorSources ++ extraSources)}] }

private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | fuel + 1, source, expression => match source.lookupExpression? expression with
    | none => []
    | some node => node :: (match node.form with
      | .unary _ operand => reached fuel source operand
      | .binary left _ right => reached fuel source left ++ reached fuel source right
      | .group inner => reached fuel source inner
      | .tuple ids => ids.flatMap (reached fuel source)
      | _ => [])
private def expected (name : String) (mapping : Value) : Option Value :=
  match operators.find? (fun (label, _, _, _, _) => name == s!"word_{label}" || name == s!"int_{label}") with
  | some (label, _, _, word, integer) => some (if name == s!"word_{label}" then word else integer)
  | none => match name with
    | "bool_not" => some (.bool false)
    | "word_not" => some (.word (Word.ofNatModulo 7).bitNot)
    | "int_not" => some (.integer (~~~(-7 : Int)))
    | "and_skip" => some (.bool false)
    | "or_skip" => some (.bool true)
    | "map_skip" => some (.pair mapping (.bool false))
    | "parent" => some (.pair (.bool true) (.bool true))
    | _ => none

private def inspect {catalog : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (name : String) (expression : ExpressionId) : IO Unit := do
  let contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let representation := SourceCoreCompatibleFunctions.representation contextValues 150
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "primitive diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "primitive root diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let nodes := reached 100 source expression
  for node in nodes do
    assertTrue node.coercions.isEmpty "primitive fixture acquired an output coercion"
    match node.form with
    | .unary .. | .binary .. => assertTrue node.requirements.isEmpty "primitive fixture acquired method dispatch evidence"
    | _ => pure ()
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let bindings ← ids.mapM fun binder => do
    let declared ← get "primitive binder" (SourceCoreDataPlaces.rootBinder source binder)
    let type ← get "primitive binder projection" (catalog.catalog.project declared.scheme.body)
    let initializer ← if declared.name == "missing" || declared.name == "otherMissing" then pure (OptionalCell.allocate type)
      else match declared.scheme.body with
      | .bool => pure (OptionalCell.allocateInitialized type (.bool true))
      | .word => pure (OptionalCell.allocateInitialized type (.word (Word.ofNatModulo (if declared.name == "b" then 3 else 7))))
      | .integer => pure (OptionalCell.allocateInitialized type (.integer (if declared.name == "b" then 3 else -7)))
      | .mapping .. => pure (OptionalCell.allocate type)
      | other => throw (IO.userError s!"unexpected primitive scope: {reprStr other}")
    pure (binder, type, initializer)
  let scope := bindings.map fun (id, type, _) => (id, type)
  let lowered ← get s!"actual contextual primitive {name}" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
    representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
    parent none 150 source scope expression reasonAt)
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"actual contextual primitive {name} failed native checker"
  let mappingValue ← if name == "map_fault" || name == "map_skip" then do
    let encoded ← get "expected empty mapping" (SourceCoreCompatibleValues.encode 100 contextValues
      (.mapping .word .word) (.mapping .word .word []))
    pure encoded.value
    else pure .unit
  for fuel in [0, 3, 15, 1000] do
    let finished := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 3000 checkpoint
      | other => other
    match finished with
    | .done value store =>
      assertTrue (store.length == bindings.length + 1) "primitive allocated unexpected cells"
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "primitive changed administrative closure"
      match expected name mappingValue with
      | some expected => assertTrue (value == .inRight .word expected) s!"primitive {name} wrong result: {reprStr value}"
      | none =>
        let faultNode ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "fault fixture lacks missing occurrence")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt faultNode.id))) s!"primitive {name} fault reason/order changed"
      for (position, (_, type, _)) in bindings.zipIdx.map (fun (binding, position) => (position, binding)) do
        if type != .bool && type != .word && type != .integer then
          assertTrue (store[bindings.length - position]? == some (.inRight .unit mappingValue))
            "left mapping initialization lost after primitive completion"
    | other => throw (IO.userError s!"primitive {name} failed to finish: {reprStr other}")

private def sourceOperator : String → Solcore.Syntax.BinaryOp
  | "mul" => .multiply | "div" => .divide | "mod" => .modulo | "add" => .add | "sub" => .subtract
  | "band" => .bitAnd | "bxor" => .bitXor | "bor" => .bitOr | "lt" => .less | "gt" => .greater
  | "le" => .lessEqual | "ge" => .greaterEqual | "eq" => .equal | _ => .notEqual

/-- These direct operator nodes exercise the retained IR admission separately
from source surface desugaring and inference. Integer operator typing is part
of the declarative rules; this test does not widen checker admission. -/
private def inspectPrimitiveIR : IO Unit := do
  for (name, _, comparison, wordExpected, integerExpected) in operators do
    for isInteger in [false, true] do
      let rawType : TypeSystem.Ty := if isInteger then .integer else .word
      let nativeType : Ty := if isInteger then .integer else .word
      let resultRaw : TypeSystem.Ty := if comparison then .bool else rawType
      let a : TypedBinder := ⟨⟨owner, 0⟩, "a", .mono rawType, [], false, none⟩
      let b : TypedBinder := ⟨⟨owner, 1⟩, "b", .mono rawType, [], false, none⟩
      let left : ExpressionNode := { id := id 0, span, type := rawType, form := .reference "a" (.local a.id) }
      let right : ExpressionNode := { id := id 1, span, type := rawType, form := .reference "b" (.local b.id) }
      let operation : ExpressionNode := { id := id 2, span, type := resultRaw, form := .binary left.id (sourceOperator name) right.id }
      let source : TypedSource := { owner, inputs := [a, b], roots := [.expression operation.id], nodes := [.expression left, .expression right, .expression operation] }
      let lowered ← get "direct primitive IR admission" (SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 10 compilation source
        [(a.id, nativeType), (b.id, nativeType)] operation.id (fun _ => reason))
      let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
      let adminType := Ty.function .unit frameLayout.type
      let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
      let leftValue : Expr := if isInteger then .integer (-7) else .word (Word.ofNatModulo 7)
      let rightValue : Expr := if isInteger then .integer 3 else .word (Word.ofNatModulo 3)
      let body := Expr.letE (.newCell adminType adminExpr)
        (.letE (OptionalCell.allocateInitialized nativeType rightValue)
          (.letE (OptionalCell.allocateInitialized nativeType leftValue) lowered.expression))
      let native : Core.Program := ⟨LanguageResult.resultType lowered.type, body, checked.catalog.definitions ++ [frameLayout.definition]⟩
      assertTrue native.check "direct IR native checker rejected accepted primitive"
      for fuel in [0, 3, 15, 1000] do
        let finished := match native.runStateful fuel with | .outOfFuel saved => Core.runStateful 2000 saved | result => result
        match finished with
        | .done value store =>
          assertTrue (value == .inRight .word (if isInteger then integerExpected else wordExpected)) s!"direct IR {name} result differs"
          assertTrue (store.length == 3) "direct primitive IR changed store shape"
          assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
            "direct primitive IR changed administrative closure"
        | result => throw (IO.userError s!"direct primitive IR completion: {reprStr result}")
  let integerProfile : UnaryOperatorHasType context .bitNot .integer .integer [] := .integerBitNot
  let _ := UnaryProfile.of_typing integerProfile

def run : IO Unit := do
  inspectPrimitiveIR
  let checkedProgram ← get "primitive checker" (checkProgram workspace)
  let roots := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"primitive specialization: {reprStr other}")
  let automatic ← get "actual primitive factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      let source := function.specialized.function.typedBody
      let expression ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some expression => pure expression | none => throw (IO.userError "primitive return missing")
      inspect automatic.prepared source function.signature.key none function.specialized.function.solvedRequirements name expression
      rootsSeen := rootsSeen + 1
  let mut parentsSeen := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      for entry in parent.source.nodes do
        match entry with
        | .expression node => match node.form with
          | .tuple [_, _] =>
            inspect automatic.prepared parent.source parent.caller.key (some parent) parent.caller.function.solvedRequirements "parent" node.id
            parentsSeen := parentsSeen + 1
          | _ => pure ()
        | _ => pure ()
  assertTrue (rootsSeen == 20) s!"primitive cases missing: {rootsSeen}"
  assertTrue (parentsSeen > 0) "full parent substitution primitive case missing"
  IO.println "actual contextual primitives: Word/Integer, short circuit, fault order, mapping prefix, ambient closure and resume GREEN"

end Tests.SourceCoreCompatibleExpressionPrimitives
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleExpressionProducts
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! The kernel tests consume actual compiler results and independent source
shape typing. Runtime tests cover a lazy mapping read before a right-hand
fault, inserted slots, a full parent context, and administrative closures. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionProducts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionProducts CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_products", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "products.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def boolean (index : Nat) (value : Bool) : ExpressionNode :=
  { id := id index, span, type := .bool, form := .reference "boolean" (.builtinBoolean value) }
private def grouped : ExpressionNode := { id := id 2, span, type := .bool, form := .group (id 0) }
private def paired : ExpressionNode := { id := id 3, span, type := .product .bool .bool, form := .tuple [id 2, id 1] }
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 3)],
    nodes := [.expression (boolean 0 true), .expression (boolean 1 false), .expression grouped, .expression paired] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private def faults : FunctionCalls.FaultRep := fun error token =>
  (∃ location, error = .uninitializedLocation location) ∧ token = reason
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index native selected
  cases selected
private theorem syntaxTree : CompatibleExpressionProducts.Syntax source (id 3) :=
  .pair (node := paired) (by cbv) rfl
    (.group (node := grouped) (by cbv) rfl (.literal (node := boolean 0 true) (by cbv) (.bool _ _)))
    (.literal (node := boolean 1 false) (by cbv) (.bool _ _))
private theorem boolTyped {index : Nat} {value : Bool}
    (found : source.lookupExpression? (id index) = some (boolean index value)) :
    ExpressionHasType source context (id index) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := boolean index value) (rawType := .bool)
    (lookupExpression?_sound found) (.reference (.builtinBoolean value)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem groupedTyped : ExpressionHasType source context (id 2) .bool := by
  have admitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  apply ExpressionHasType.ofOrdinary (node := grouped) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.group (boolTyped (value := true) (by cbv))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem pairedTyped : ExpressionHasType source context (id 3) (.product .bool .bool) := by
  have boolAdmitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
  have admitted : TypeAdmissible context (.product .bool .bool) := .product boolAdmitted boolAdmitted
  apply ExpressionHasType.ofOrdinary (node := paired) (rawType := .product .bool .bool)
    (lookupExpression?_sound (by cbv)) (.tuple (.cons groupedTyped (.cons (boolTyped (value := false) (by cbv)) (.nil _)))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures]
  · intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; simp [context, SourceSemantics.Context.ofSignatures] at member
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.product .bool .bool]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.product .bool .bool]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def policy := SourceCoreCompatibleDataExpressions.functionPolicy 20 values
private def code : SourceCoreBasic.LoweredExpr :=
  ⟨.product .bool .bool, LocalSequence.pair .bool .bool (LanguageResult.success (.bool true)) (LanguageResult.success (.bool false))⟩
private theorem boolAccepted (fuel index : Nat) (value : Bool)
    (found : source.lookupExpression? (id index) = some (boolean index value))
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id index) = .ok (boolean index value, .bool))
    (basic : SourceCoreBasic.lowerExpression (fuel + 1) source [] (id index) reason =
      .ok ⟨.bool, LanguageResult.success (.bool value)⟩) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy noBody (fuel + 1) compilation source [] (id index) (fun _ => reason) =
      .ok ⟨.bool, LanguageResult.success (.bool value)⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id index).occurrence.owner = source.owner := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure]
  simp only [boolean]
  rw [read]
  simp only [bind, Except.bind, boolean]
  unfold SourceCoreCompatibleDataExpressions.leafLowerer
  rw [read]
  exact basic
private theorem groupAccepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 9 compilation source [] (id 2) (fun _ => reason) =
    .ok ⟨.bool, LanguageResult.success (.bool true)⟩ := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 2).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 2) = some grouped := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 2) = .ok (grouped, .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, grouped]
  rw [read]
  simp only [bind, Except.bind, grouped]
  have childEq := boolAccepted 7 0 true rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at childEq
  rw [childEq]
  rfl
private theorem accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 10 compilation source [] (id 3) (fun _ => reason) = .ok code := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy]
  have ownerEq : (id 3).occurrence.owner = source.owner := rfl
  have found : source.lookupExpression? (id 3) = some paired := rfl
  have read : SourceCoreCompatibleDataExpressions.readExpression values.checked source (id 3) = .ok (paired, .product .bool .bool) := rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, ownerEq, ne_eq, not_true_eq_false,
    ↓reduceIte, found, bind, Except.bind, pure, Except.pure, paired]
  rw [read]
  simp only [bind, Except.bind, paired]
  have firstEq := groupAccepted
  have secondEq := boolAccepted 8 1 false rfl rfl rfl
  simp only [policy, SourceCoreCompatibleDataExpressions.functionPolicy, bind, Except.bind, pure, Except.pure] at firstEq secondEq
  rw [firstEq]
  simp only [bind, Except.bind]
  rw [secondEq]
  rfl
private theorem certified : Tree 20 values source context [] (fun _ => reason) [] (id 3) code :=
  tree_of_functions unique declarations ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) pairedTyped accepted

/-- The actual production contextual dispatcher is also the source of the
static tree; the compilation equation is the only compiler-result premise. -/
theorem contextual_certificate
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {lowered : SourceCoreBasic.LoweredExpr}
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead 20 values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (generated : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures ⟨[]⟩ parents assignments
      diagnostics compilation native parent none 10 source [] (id 3) (fun _ => reason) = .ok lowered) :
    Tree 20 values source context [] (fun _ => reason) [] (id 3) lowered := by
  exact tree_of_contextual
    ⟨fun _ _ _ found => (metadata found).1, fun _ _ _ found => (metadata found).2, by intros; rfl, by intros; rfl⟩
    unique declarations syntaxTree (by cbv) pairedTyped readPolicy lowerPolicy leafPolicy generated

/-- Both directions use the whole tree induction. No child evaluator proof is
supplied, even when the ambient heap contains captures of fresh nominal frames. -/
theorem actual_preserves {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked values.registry functions)
      program context [] source (Tree 20 values source context [] (fun _ => reason)) faults :=
  preserves (values := values) (source := source) (fuel := 20) (reasonAt := fun _ => reason) (faults := faults) functions (.refl _) program [] valid unique (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)
theorem actual_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked values.registry functions)
      program context [] source (Tree 20 values source context [] (fun _ => reason)) faults :=
  reflects (values := values) (source := source) (fuel := 20) (reasonAt := fun _ => reason) (faults := faults) functions (.refl _) program [] valid (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)

theorem accepted_pair_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {mapping world administrative environment canonical actual before store ξ value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
      administrative [] environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (completed : Evaluates actual store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context [] source environment before (id 3) outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked values.registry functions)
        finalMap finalWorld paired.type code.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  actual_reflects functions certified (by cbv) environments heaps locals agrees completed

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function constants() returns ((Bool, Bool)) { return ((true), false); }",
    "function inputs(flag: Bool) returns ((Bool, Bool)) { return ((flag), true); }",
    "function lazyFault() returns ((mapping(Word => Word), Bool)) { let m: mapping(Word => Word); let b: Bool; return ((m), b); }",
    "function lazySuccess() returns ((mapping(Word => Word), Bool)) { let m: mapping(Word => Word); return ((m), true); }",
    "function parent(seed: Word) returns ((Word, Bool)) { let pairer = lam(flag) { return ((seed), flag); }; return pairer(true); }"
  ]}] }

private def selectedIds : Nat → TypedSource → ExpressionId → List Resolved.LocalId
  | 0, _, _ => []
  | fuel + 1, source, expression => match source.lookupExpression? expression with
    | none => []
    | some node => match node.form with
      | .reference _ (.local binder) => [binder]
      | .group inner => selectedIds fuel source inner
      | .tuple ids => ids.flatMap (selectedIds fuel source)
      | _ => []

private def inspect {catalog : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (faulting : Bool) (constantRight : Bool := true) : IO Nat := do
  let contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let representation := SourceCoreCompatibleFunctions.representation contextValues 100
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "product diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "product root diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let mut count := 0
  for entry in source.nodes do
    match entry with
    | .expression node =>
      match node.form with
      | .tuple [_, _] =>
        let ids := (selectedIds 100 source node.id).eraseDups
        let bindings ← ids.mapM fun binder => do
          let declared ← get "product binder" (SourceCoreDataPlaces.rootBinder source binder)
          let type ← get "product binder projection" (catalog.catalog.project declared.scheme.body)
          let initializer ← match declared.scheme.body with
            | .bool => pure (if faulting then OptionalCell.allocate type else OptionalCell.allocateInitialized type (.bool true))
            | .word => pure (OptionalCell.allocateInitialized type (.word (Word.ofNatModulo 5)))
            | .mapping .. => pure (OptionalCell.allocate type)
            | other => throw (IO.userError s!"unexpected pair scope: {reprStr other}")
          pure (binder, type, initializer)
        let scope := bindings.map fun (id, type, _) => (id, type)
        let lowered ← get "actual contextual pair" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
          representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
          parent none 100 source scope node.id reasonAt)
        let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
        let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
        let adminType := Ty.function .unit frameLayout.type
        let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
        let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
        let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
          .letE (.newCell adminType adminExpr) body, definitions⟩
        assertTrue native.check "actual contextual pair failed native checker"
        for fuel in [0, 3, 15, 1000] do
          let finished := match native.runStateful fuel with
            | .outOfFuel checkpoint => Core.runStateful 2000 checkpoint
            | other => other
          match finished with
          | .done value store =>
            assertTrue (store.length == bindings.length + 1) "pair allocated unexpected cells"
            assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
              "pair changed administrative closure"
            if faulting then
              match value with
              | .inLeft _ (.word token) =>
                let boolId ← match source.nodes.findSome? fun
                  | .expression node => match node.form with
                    | .reference _ (.local binder) => if (ids.contains binder && node.type == .bool) then some node.id else none
                    | _ => none
                  | _ => none with
                  | some id => pure id | none => throw (IO.userError "fault read missing")
                assertTrue (token == reasonAt boolId) "right fault lost occurrence token"
              | _ => throw (IO.userError "uninitialized right child did not fault")
            else
              let expectedLeft ← match node.type with
                | .product .bool .bool => pure (.bool true)
                | .product .word .bool => pure (.word (Word.ofNatModulo 5))
                | .product (.mapping key payload) .bool => do
                  let encoded ← get "expected empty mapping" (SourceCoreCompatibleValues.encode 100 contextValues
                    (.mapping key payload) (.mapping key payload []))
                  pure encoded.value
                | other => throw (IO.userError s!"unexpected product raw type: {reprStr other}")
              assertTrue (value == .inRight .word (.pair expectedLeft (.bool constantRight))) "pair success value/order changed"
            for (position, (_, type, _)) in bindings.zipIdx.map (fun (binding, position) => (position, binding)) do
              if type != .bool && type != .word then
                let location := bindings.length - position
                match store[location]? with
                | some (.inRight .unit _) => pure ()
                | _ => throw (IO.userError "left mapping effect missing after right completion")
          | other => throw (IO.userError s!"pair failed to finish: {reprStr other}")
        count := count + 1
      | _ => pure ()
    | _ => pure ()
  pure count

def run : IO Unit := do
  let checkedProgram ← get "product checker" (checkProgram workspace)
  let roots ← ["constants", "inputs", "lazyFault", "lazySuccess", "parent"].mapM fun name =>
    match checkedProgram.signatures.functions.find? (·.name == name) with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
    | none => throw (IO.userError s!"product root missing: {name}")
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"product specialization: {reprStr other}")
  let automatic ← get "actual product factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 300)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      rootsSeen := rootsSeen + (← inspect automatic.prepared function.specialized.function.typedBody
        function.signature.key none function.specialized.function.solvedRequirements (name == "lazyFault") (name != "constants"))
  let mut parentsSeen := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      parentsSeen := parentsSeen + (← inspect automatic.prepared parent.source parent.caller.key
        (some parent) parent.caller.function.solvedRequirements false)
  assertTrue (rootsSeen == 4) "root group/pair cases missing"
  assertTrue (parentsSeen > 0) "full parent substitution group/pair missing"
  IO.println "actual contextual group/pair: left effects, right fault, ambient closure, parent and resume GREEN"

end Tests.SourceCoreCompatibleExpressionProducts
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleExpressionProxies
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Real contextual proxy emissions preserve original metadata, including
staging inside a proxy. Retained-IR negative cases distinguish raw type and
registry authentication from their shared native identity. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleExpressionProxies
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionProxies CompatiblePayload

/-- The actual leaf receipt supplies an independent source trace and typed
finite Core execution for arbitrary ambient definitions and stores. -/
theorem accepted_finite
    {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {node : ExpressionNode} {inner : TypeSystem.Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id reasonAt = .ok lowered)
    (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (program : SourceSemantics.Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) (actual : Core.Environment)
    (store : Store) (ξ : Renaming) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id (.proxy inner) heap ∧
    HasType [] lowered.expression (LanguageResult.resultType lowered.type) ambient.definitions ∧
    ∃ result, Evaluates actual store (lowered.expression.rename ξ) result store := by
  obtain ⟨owner, header, rfl, receipt⟩ := proxy_of_lower found form accepted
  exact ⟨receipt.source_evaluates program context evidence environment heap,
    receipt.hasType ambient [], _, receipt.native_evaluates actual store ξ⟩

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function word() returns (@Word) { return @Word; }",
    "function boolean() returns (@Bool) { return @Bool; }",
    "function integer() returns (@integer) { return @integer; }",
    "function parent() returns (@Word) { let make = lam(value) { return @Word; }; return make(true); }"
  ]}] }

private def replace (source : TypedSource) (node : ExpressionNode) : TypedSource :=
  { source with nodes := source.nodes.map fun
    | .expression old => if old.id = node.id then .expression node else .expression old
    | .statement old => .statement old }

private def inspectNode {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (values : ValuesContext) (same : values.checked = checked)
    (source : TypedSource) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) (solved : List SolvedRequirement)
    (node : ExpressionNode) (inner : TypeSystem.Ty) (form : node.form = .proxy inner) : IO (Ty × Word) := do
  let representation := SourceCoreCompatibleFunctions.representation values 100
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "proxy diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "proxy owner missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  if found : source.lookupExpression? node.id = some node then
    if requirements : node.requirements = [] then
      if coercions : node.coercions = [] then
        if notInitializer : prepared.locals.bindings.find? (fun binding => decide (binding.caller = owner ∧ binding.initializer = node.id)) = none then
          match accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation
              checked.signatures prepared.locals prepared.contexts own.assignments diagnostics context prepared.callableContext
              parent none 100 source [] node.id reasonAt with
          | .error error => throw (IO.userError s!"actual contextual proxy rejected: {reprStr error}")
          | .ok lowered =>
            have receipt : Certificate values source [] node.id lowered := certificate_of_contextual
              found form requirements coercions notInitializer rfl rfl accepted
            let _receipt := receipt
            let (payload, header) ← match lowered.expression with
              | .inRight .word (.construct tag (.word header)) => pure (Core.Value.constructed tag (.word header), header)
              | _ => throw (IO.userError "proxy carrier shape changed")
            let decoded ← get "proxy raw decode" (SourceCoreCompatibleValues.decode 100 values node.type payload)
            assertTrue (decoded == .proxy inner) "proxy inner metadata changed"
            assertTrue (values.registry.lookup header == some (.proxy inner)) "proxy header is not the raw inner type"
            let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
            let frameValue := Core.Value.constructed frame.empty .unit
            let code := Expr.letE (.construct frame.empty .unit)
              (.letE (.newCell (.function .unit frame.type) (.lambda .unit frame.type (.var 1)))
                (.letE (.integer 91) (lowered.expression.weakenAt 0 |>.weakenAt 0 |>.weakenAt 0)))
            let native : Core.Program := ⟨LanguageResult.resultType lowered.type, code,
              checked.catalog.definitions ++ [frame.definition]⟩
            assertTrue native.check "proxy failed actual ambient checker"
            for fuel in [0, 2, 1000] do
              let result := match native.runStateful fuel with
                | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
                | other => other
              match result with
              | .done value store =>
                assertTrue (value == .inRight .word payload) "proxy native result changed"
                assertTrue (store == [.closure .unit frame.type (.var 1) [frameValue]]) "proxy changed ambient closure store"
              | other => throw (IO.userError s!"proxy did not complete: {reprStr other}")
            let _same := same
            pure (lowered.type, header)
        else throw (IO.userError "unexpected specialized proxy initializer")
      else throw (IO.userError "unexpected proxy coercion")
    else throw (IO.userError "unexpected proxy requirement")
  else throw (IO.userError "proxy occurrence missing")

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) : IO Nat := do
  let mut count := 0
  for entry in source.nodes do
    match entry with
    | .expression node =>
      match form : node.form with
      | .proxy inner =>
        let _ ← inspectNode prepared (.initial checked) rfl source owner parent solved node inner form
        count := count + 1
      | _ => pure ()
    | _ => pure ()
  pure count

def run : IO Unit := do
  let program ← get "proxy source checker" (checkProgram workspace)
  let roots ← ["word", "boolean", "integer", "parent"].mapM fun name =>
    match program.signatures.functions.find? (·.name == name) with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
    | none => throw (IO.userError s!"proxy root missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program roots 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"proxy specialization: {reprStr other}")
  let automatic ← get "proxy actual factory" (SourceCoreCompatibleFunctions.prepare program plan 300)
  let mut count := 0
  for function in automatic.prepared.functions do
    count := count + (← inspect automatic.prepared function.specialized.function.typedBody
      function.signature.key none function.specialized.function.solvedRequirements)
  let mut contextual := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      contextual := contextual + (← inspect automatic.prepared parent.source parent.caller.key
        (some parent) parent.caller.function.solvedRequirements)
  assertTrue (count ≥ 3 && contextual > 0) "proxy root or full-parent coverage missing"
  let wordId ← match program.signatures.functions.find? (·.name == "word") with
    | some signature => pure signature.id | none => throw (IO.userError "word root missing")
  let function ← match automatic.prepared.functions.find? (·.signature.key.declaration == wordId) with
    | some function => pure function | none => throw (IO.userError "word function missing")
  let source := function.specialized.function.typedBody
  let node ← match source.nodes.findSome? fun
    | .expression node => match node.form with | .proxy _ => some node | _ => none
    | _ => none with
    | some node => pure node | none => throw (IO.userError "word proxy missing")
  let original := SourceCoreCompatibleValues.Context.initial automatic.checked
  let rawInner := TypeSystem.Ty.comptime .word
  let rawNode := { node with type := .proxy rawInner, form := .proxy rawInner }
  let rawSource := replace source rawNode
  let encoded ← get "raw proxy registry" (SourceCoreCompatibleValues.encode 100 original (.proxy rawInner) (.proxy rawInner))
  let raw ← inspectNode automatic.prepared encoded.context rfl rawSource function.signature.key none
    function.specialized.function.solvedRequirements rawNode rawInner rfl
  let canonicalNode := { node with type := .proxy .word, form := .proxy .word }
  let canonical ← inspectNode automatic.prepared encoded.context rfl (replace source canonicalNode) function.signature.key none
    function.specialized.function.solvedRequirements canonicalNode .word rfl
  assertTrue (raw.1 == canonical.1 && raw.2 != canonical.2) "raw proxy metadata collapsed to native identity"
  let child : Child := fun _ _ _ id _ => .error (.unsupportedExpression id (.tuple []))
  let badRaw := { rawNode with type := .proxy .word }
  let badOuter := { canonicalNode with type := .comptime (.proxy .word) }
  let lower := fun values source => SourceCoreCompatibleDataExpressions.lowerWithReasons 100 values child source [] node.id (fun _ => Word.zero)
  assertTrue ((lower encoded.context (replace source badRaw)).toOption.isNone) "mismatched raw proxy type accepted"
  assertTrue ((lower original rawSource).toOption.isNone) "unregistered raw metadata accepted"
  assertTrue ((lower encoded.context (replace source badOuter)).toOption.isNone) "outer staging bypassed ordinary raw type check"
  IO.println "actual contextual proxies: raw/staged headers, full parent, malformed metadata, ambient captures and resume GREEN"

end Tests.SourceCoreCompatibleExpressionProxies
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleExpressionReadCompletion
/-! Consumers of shared original-completion inversion. The actual compiler and
independent source typing supply a receipt; native typing alone never supplies
a source declaration or a generalized-cell history. No runner is added. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleExpressionReadCompletion
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload
open CompatibleMapping.VirtualRoot

section Actual
variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode}
  (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id) = .ok lowered.expression)
  (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
  (unique : NodeOccurrencesUnique source)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (typed : ExpressionHasType source context id node.type)
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

include accepted read unique declarations typed extension in
/-- All actual ordinary reads use the unchanged public reflection interface. -/
theorem actual_completed (uninitialized : ∀ expression location, faults (.uninitializedLocation location) (reasonAt expression)) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (fun current occurrence code => current = scope ∧ occurrence = id ∧ code = lowered) faults := by
  intro current occurrence code receipt
  obtain ⟨rfl, rfl, rfl⟩ := receipt
  exact CompatibleExpressionReads.loweredRead_reflects functions extension program context evidence reasonAt uninitialized
    (CompatibleExpressionReads.loweredRead_of_accepted accepted read unique declarations typed)

include accepted read unique declarations typed extension in
/-- The mapping branch returns the independent raw source rule. Ordinary and
staged consumers can wrap this same result without rerunning native code. -/
theorem actual_mapping_form {name : String} {binder : Resolved.LocalId} {declared : TypedBinder}
    {key value : TypeSystem.Ty}
    (form : node.form = .reference name (.local binder))
    (declaration : SourceCoreDataPlaces.rootBinder source binder = .ok declared)
    (declaredType : declared.scheme.body = .mapping key value)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    {result : Value} {finalStore : Store}
    (completed : Evaluates actual store (lowered.expression.rename ξ) result finalStore) :
    ∃ sourceValue after,
      Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form [] [] sourceValue after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping world node.type lowered.type faults (.value sourceValue) result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  obtain ⟨certificate, sameType, binding, mappingType⟩ :=
    RecursiveStageMappingReadMeaning.of_accepted accepted read unique declarations typed form declaration declaredType
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans (CompatibleExpressionReads.metadata_of_read read).found)
  obtain ⟨sourceValue, after, raw, represented, rest⟩ :=
    certificate.mapping_completed (faults := faults) functions extension program context evidence binding mappingType
      environments heaps locals agrees completed
  exact ⟨sourceValue, after, by simpa only [nodeEq] using raw,
    by simpa only [nodeEq, sameType] using represented, rest⟩
end Actual

section Native
/-- A present ordinary optional cell keeps the complete original store. -/
theorem ordinary_present {environment : Environment} {before after : Store}
    {index target : Nat} {type : Ty} {reason : Word} {present result : Value}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : before.read? target = some (.inRight .unit present))
    (completed : Evaluates environment before (OptionalCell.read type (.var index) reason) result after) :
    result = .inRight .word present ∧ after = before := by
  rcases CompatibleExpressionReadCompletion.ordinary_completed lookup read completed with
    ⟨_, _, same, resultEq, storeEq⟩ | ⟨_, _, impossible, _⟩
  · cases same; exact ⟨resultEq, storeEq⟩
  · cases impossible

/-- An absent ordinary nonmapping cell returns its real fault carrier and
preserves the original store. Its source attribution is supplied separately. -/
theorem ordinary_absent {environment : Environment} {before after : Store}
    {index target : Nat} {type : Ty} {reason : Word} {result : Value}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : before.read? target = some (.inLeft type .unit))
    (completed : Evaluates environment before (OptionalCell.read type (.var index) reason) result after) :
    result = .inLeft type (.word reason) ∧ after = before := by
  rcases CompatibleExpressionReadCompletion.ordinary_completed lookup read completed with
    ⟨_, _, impossible, _⟩ | ⟨_, _, _, resultEq, storeEq⟩
  · cases impossible
  · exact ⟨resultEq, storeEq⟩

/-- Lazy mapping initialization exposes the exact original write and retains
all other native cells, including arbitrary unused administrative payloads. -/
theorem mapping_write_other {environment : Environment} {before after : Store}
    {index target other : Nat} {type : Ty} {empty result : Value} {literal : Expr}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : before.read? target = some (.inLeft type .unit)) (quoted : Quoted empty literal)
    (completed : Evaluates environment before
      (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal) result after)
    (different : other ≠ target) :
    result = .inRight .word empty ∧ before.write? target (.inRight .unit empty) = some after ∧
      after.read? other = before.read? other := by
  rcases RecursiveStageMappingReadMeaning.read_completed lookup read quoted completed with
    ⟨_, _, impossible, _⟩ | ⟨_, _, same, resultEq, written⟩
  · cases impossible
  · cases same
    exact ⟨resultEq, written, Store.write?_preserves_other written different⟩
end Native

/-- Generalized-cell history is outside ordinary optional-cell representation. -/
theorem generalized_excluded {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : Core.DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {value : Value} {type : Ty}
    (represented : GenericHeap.CellRepresents model mapping world cell value type)
    (generalized : cell.generalized ≠ none) : False := generalized represented.ordinary

end Tests.SourceCoreCompatibleExpressionReadCompletion
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleExpressionReads
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual compatible read receipts are consumed by both semantic directions.
The native heap has an administrative closure prefix and a source cell at a
different location. Mapping initialization keeps that prefix intact. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleExpressionReads
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionReads

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_read", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_read.solc"⟩, 0, 1⟩
private def id : ExpressionId := ⟨⟨owner, 1⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def binder (type : TypeSystem.Ty) : TypedBinder := ⟨⟨owner, 0⟩, "value", .mono type, [], false, none⟩
private def node (type : TypeSystem.Ty) : ExpressionNode :=
  { id, span, type, form := .reference "value" (.local (binder type).id) }
private def source (type : TypeSystem.Ty) : TypedSource :=
  { owner, inputs := [binder type], roots := [.expression id], nodes := [.expression (node type)] }
private def sourceContext (type : TypeSystem.Ty) :=
  (SourceSemantics.Context.ofSignatures signatures).withLocal (binder type).id (binder type).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def sourceEnvironment (type : TypeSystem.Ty) : Dynamic.Environment := [((binder type).id, ⟨0⟩)]
private def reason : Word := Word.ofNatModulo 17
private def faults : FunctionCalls.FaultRep := fun error token =>
  (∃ location, error = .uninitializedLocation location) ∧ token = reason
private theorem unique (type : TypeSystem.Ty) : NodeOccurrencesUnique (source type) := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]
private theorem contains (type : TypeSystem.Ty) : ContainsExpression (source type) id (node type) :=
  lookupExpression?_sound (by rfl)
private theorem schemeTyped {type : TypeSystem.Ty} (typed : TypeAdmissible (sourceContext type) type) :
    SchemeWellFormed (sourceContext type) (binder type).scheme := SchemeWellFormed.monoAdmissible typed
private theorem sourceTyped {type : TypeSystem.Ty} (typed : TypeAdmissible (sourceContext type) type) :
    ExpressionHasType (source type) (sourceContext type) id type := by
  apply ExpressionHasType.ofOrdinary (node := node type) (rawType := type) (contains type)
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (schemeTyped typed) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply type)
      (by simp) (by intro _ member; cases member) (.nil)))) typed typed
  · intro requirement member; cases member
  · exact .nil _
  · rfl

private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, .mapping (.comptime .bool) .word]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, .mapping (.comptime .bool) .word]).toOption.get checkExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frameLayout.definition]
private def functions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def model := CompatibleAmbientHeap.payloadModel checked context.registry functions
private def administrativeType : Ty := .function .unit frameLayout.type
private def administrativeValue : Value := .closure .unit frameLayout.type (.var 1) [SourceCoreCallableIndexedFrames.encode frameLayout .empty]
private theorem frameRegistered : frameLayout.Registered ambient.definitions := by
  constructor
  simp [ambient, AmbientDefinitions.append, frameLayout]
private theorem administrativeTyped : RuntimeValueHasType [] administrativeValue administrativeType ambient.definitions :=
  .closure (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty) .nil) (.var rfl)
private theorem initialHeap : GenericHeap.HeapRepresents model [] [administrativeType] ⟨[]⟩ [administrativeValue] :=
  GenericHeap.HeapRepresents.empty.allocate_administrative administrativeTyped
private def scope (type : Ty) : SourceCoreLocalCell.Scope := [((binder .bool).id, type)]
private theorem declarations (sourceType : TypeSystem.Ty) (type : Ty) :
    ScopeDeclarations (source sourceType) (scope type) (sourceContext sourceType) := by
  intro id declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst id
    have actual : SourceCoreDataPlaces.rootBinder (source sourceType) (binder .bool).id = .ok (binder sourceType) := by
      simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, source, binder, node, TypeSystem.Scheme.mono]
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected

private def boolCode : SourceCoreBasic.LoweredExpr := ⟨.bool, OptionalCell.read .bool (.var 0) reason⟩
private theorem boolAccepted : SourceCoreCompatibleDataExpressions.lowerRead 100 context (source .bool) (scope .bool) id reason = .ok boolCode.expression := by rfl
private theorem boolRead : SourceCoreCompatibleDataExpressions.readExpression checked (source .bool) id = .ok (node .bool, boolCode.type) := by rfl
private theorem boolCertificate : LoweredRead 100 context (source .bool) (sourceContext .bool) (fun _ => reason) (scope .bool) id boolCode :=
  loweredRead_of_accepted boolAccepted boolRead (unique _) (declarations _ _)
    (sourceTyped (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder .bool).id (binder .bool).scheme)))

/-- The actual read receipt discharges the child interfaces, including all
administrative environment insertions and arbitrary typed closure payloads. -/
theorem universal_forward : GenericExpressionMeaning.Preserves model program (sourceContext .bool) [] (source .bool)
    (LoweredRead 100 context (source .bool) (sourceContext .bool) (fun _ => reason)) faults :=
  loweredRead_preserves (context := context) (faults := faults) functions (.refl _) program _ [] _ (fun _ location => ⟨⟨location, rfl⟩, rfl⟩) (unique _)
theorem universal_reverse : GenericExpressionMeaning.Reflects model program (sourceContext .bool) [] (source .bool)
    (LoweredRead 100 context (source .bool) (sourceContext .bool) (fun _ => reason)) faults :=
  loweredRead_reflects (context := context) (faults := faults) functions (.refl _) program _ [] _ (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)

private def boolHeap (value : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨.bool, value, none⟩]⟩
private def world (type : Ty) : StoreTyping := [administrativeType, OptionalCell.cellType type]
private def environment (type : Ty) : Environment := [.cellRef (OptionalCell.cellType type) 1]
private theorem boolAgrees (value : Option Dynamic.Value) :
    Dynamic.EnvironmentAgrees (boolHeap value) (sourceContext .bool).locals (sourceEnvironment .bool) :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem visible {sourceType : TypeSystem.Ty} {nativeType : Ty} {sourceValue : Option Dynamic.Value} {native : Value}
    (cell : GenericHeap.CellRepresents model [] [administrativeType] ⟨sourceType, sourceValue, none⟩ native nativeType)
    (_projected : checked.catalog.project sourceType = .ok nativeType) :
    GenericHeap.HeapRepresents model [1] (world nativeType) ⟨[⟨sourceType, sourceValue, none⟩]⟩ [administrativeValue, native] ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [1] (world nativeType) [] (scope nativeType)
      (sourceEnvironment sourceType) (environment nativeType) ambient.definitions := by
  obtain ⟨heap, reference⟩ := initialHeap.allocate cell Dynamic.Heap.Allocates.append
  exact ⟨heap, .cons reference (.nil .nil)⟩

theorem initialized_read : ∃ value finalStore finalMap finalWorld,
    Evaluates [(.integer 99), .cellRef (OptionalCell.cellType .bool) 1]
      [administrativeValue, .inRight .unit (.bool true)] (boolCode.expression.weakenAt 0) value finalStore ∧
    FunctionCalls.ResultRepresents model finalMap finalWorld .bool .bool faults (.value (.bool true)) value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld (boolHeap (some (.bool true))) finalStore ∧
    LocationMap.Extends [1] finalMap ∧ WorldExtends (world .bool) finalWorld ∧
    AdministrativePreserved [1] [administrativeValue, .inRight .unit (.bool true)] finalMap finalStore ∧
    Dynamic.HeapMetadataExtend (boolHeap (some (.bool true))) (boolHeap (some (.bool true))) := by
  obtain ⟨heaps, environments⟩ := visible (.initialized (.bool true)) (show checked.catalog.project .bool = .ok .bool by cbv)
  have result := universal_forward boolCertificate (show (source .bool).lookupExpression? id = some (node .bool) by rfl)
    environments heaps (boolAgrees _) (GenericExpressionMeaning.agree_prefix (show EnvironmentsAgree Renaming.id (environment .bool) (environment .bool) from fun {_ _} found => found) (.integer 99))
    (Dynamic.ExpressionEvaluatesOutcome.value (.intro (contains _) (.local rfl .head (.intro .head) rfl rfl) .nil))
  have renamed : boolCode.expression.rename (Renaming.comp (Renaming.insertion 0) Renaming.id) = boolCode.expression.weakenAt 0 := by
    change boolCode.expression.rename (Renaming.insertion 0) = _
    exact Expr.rename_insertion _ _
  rw [renamed] at result
  exact result

theorem uninitialized_reflected : ∃ outcome after finalMap finalWorld,
    Dynamic.ExpressionEvaluatesOutcome program (sourceContext .bool) [] (source .bool) (sourceEnvironment .bool)
      (boolHeap none) id outcome after ∧
    FunctionCalls.ResultRepresents model finalMap finalWorld .bool .bool faults outcome (.inLeft .bool (.word reason)) ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after [administrativeValue, .inLeft .bool .unit] ∧
    LocationMap.Extends [1] finalMap ∧ WorldExtends (world .bool) finalWorld ∧
    AdministrativePreserved [1] [administrativeValue, .inLeft .bool .unit] finalMap [administrativeValue, .inLeft .bool .unit] ∧
    Dynamic.HeapMetadataExtend (boolHeap none) after := by
  obtain ⟨heaps, environments⟩ := visible (.uninitialized (show checked.catalog.project .bool = .ok .bool by rfl))
    (show checked.catalog.project .bool = .ok .bool by rfl)
  have evaluated : Evaluates (environment .bool) [administrativeValue, .inLeft .bool .unit]
      boolCode.expression (.inLeft .bool (.word reason)) [administrativeValue, .inLeft .bool .unit] :=
    OptionalCell.read_failure reason (.var rfl) rfl
  exact universal_reverse boolCertificate (show (source .bool).lookupExpression? id = some (node .bool) by rfl)
    environments heaps (boolAgrees _) (ξ := Renaming.id) (fun {_ _} found => found)
    (by simpa only [Expr.rename_id] using evaluated)

private def mappingType : TypeSystem.Ty := .mapping (.comptime .bool) .word
private theorem mappingProjectionExists : (checked.catalog.project mappingType).toOption.isSome = true := by rfl
private def mappingNative := (checked.catalog.project mappingType).toOption.get mappingProjectionExists
private theorem mappingProjection : checked.catalog.project mappingType = .ok mappingNative := except_get _ mappingProjectionExists
private theorem mappingRead : SourceCoreCompatibleDataExpressions.readExpression checked (source mappingType) id =
    .ok (node mappingType, mappingNative) := by rfl
private theorem mappingTyped : TypeAdmissible (sourceContext mappingType) mappingType :=
  .mapping (.comptime (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder mappingType).id (binder mappingType).scheme)))
    (.word ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder mappingType).id (binder mappingType).scheme))
private theorem mappingCertificate {code : Expr}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead 100 context (source mappingType) (scope mappingNative) id reason = .ok code) :
    LoweredRead 100 context (source mappingType) (sourceContext mappingType)
      (fun _ => reason) (scope mappingNative) id ⟨mappingNative, code⟩ :=
  loweredRead_of_accepted accepted mappingRead (unique _) (declarations _ _) (sourceTyped mappingTyped)
private def emptyMappingHeap : Dynamic.Heap := ⟨[⟨mappingType, none, none⟩]⟩
private def initializedMappingHeap : Dynamic.Heap := ⟨[⟨mappingType, some (.mapping (.comptime .bool) .word []), none⟩]⟩

/-- Lazy initialization preserves the raw staged key header and keeps the
administrative closure at Core index zero, outside the source location map. -/
theorem lazy_mapping_read {code : Expr}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead 100 context (source mappingType) (scope mappingNative) id reason = .ok code) :
    ∃ value finalStore finalMap finalWorld,
    Evaluates (environment mappingNative) [administrativeValue, .inLeft mappingNative .unit] code value finalStore ∧
    FunctionCalls.ResultRepresents model finalMap finalWorld mappingType mappingNative faults
      (.value (.mapping (.comptime .bool) .word [])) value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld initializedMappingHeap finalStore ∧
    LocationMap.Extends [1] finalMap ∧ WorldExtends (world mappingNative) finalWorld ∧
    AdministrativePreserved [1] [administrativeValue, .inLeft mappingNative .unit] finalMap finalStore ∧
    Dynamic.HeapMetadataExtend emptyMappingHeap initializedMappingHeap := by
  obtain ⟨heaps, environments⟩ := visible (.uninitialized mappingProjection) mappingProjection
  have sourceRun : Dynamic.ExpressionEvaluatesOutcome program (sourceContext mappingType) [] (source mappingType)
      (sourceEnvironment mappingType) emptyMappingHeap id (.value (.mapping (.comptime .bool) .word [])) initializedMappingHeap :=
    .value (.intro (contains _) (.localEmptyMapping rfl .head (.intro .head) rfl rfl rfl (.intro (.intro .head) .head)) .nil)
  have locals : Dynamic.EnvironmentAgrees emptyMappingHeap (sourceContext mappingType).locals (sourceEnvironment mappingType) :=
    .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
  have meaning : GenericExpressionMeaning.Preserves model program (sourceContext mappingType) [] (source mappingType)
      (LoweredRead 100 context (source mappingType) (sourceContext mappingType) (fun _ => reason)) faults :=
    loweredRead_preserves (context := context) (faults := faults) functions (.refl _) program
    (sourceContext mappingType) [] (fun _ => reason) (fun _ location => ⟨⟨location, rfl⟩, rfl⟩) (unique mappingType)
  have result := meaning (mappingCertificate accepted) (show (source mappingType).lookupExpression? id = some (node mappingType) by rfl)
    environments heaps locals (ξ := Renaming.id) (fun {_ _} found => found) sourceRun
  simpa only [Expr.rename_id, node, emptyMappingHeap] using result

/-- Mapping reflection consumes only the actual completed Core run. The source
lazy-initialization trace and final source heap are conclusions. -/
theorem lazy_mapping_reflected {code : Expr} {value : Value} {finalStore : Store}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead 100 context (source mappingType) (scope mappingNative) id reason = .ok code)
    (completed : Evaluates (environment mappingNative) [administrativeValue, .inLeft mappingNative .unit] code value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program (sourceContext mappingType) [] (source mappingType)
        (sourceEnvironment mappingType) emptyMappingHeap id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld mappingType mappingNative faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends [1] finalMap ∧ WorldExtends (world mappingNative) finalWorld ∧
      AdministrativePreserved [1] [administrativeValue, .inLeft mappingNative .unit] finalMap finalStore ∧
      Dynamic.HeapMetadataExtend emptyMappingHeap after := by
  obtain ⟨heaps, environments⟩ := visible (.uninitialized mappingProjection) mappingProjection
  have locals : Dynamic.EnvironmentAgrees emptyMappingHeap (sourceContext mappingType).locals (sourceEnvironment mappingType) :=
    .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
  have meaning : GenericExpressionMeaning.Reflects model program (sourceContext mappingType) [] (source mappingType)
      (LoweredRead 100 context (source mappingType) (sourceContext mappingType) (fun _ => reason)) faults :=
    loweredRead_reflects (context := context) (faults := faults) functions (.refl _) program
      (sourceContext mappingType) [] (fun _ => reason) (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)
  exact meaning (mappingCertificate accepted) (show (source mappingType).lookupExpression? id = some (node mappingType) by rfl)
    environments heaps locals (ξ := Renaming.id) (fun {_ _} found => found)
    (by simpa only [Expr.rename_id] using completed)

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def checkedSource (checkedProgram : CheckedProgram) (name : String) : IO TypedSource := do
  let signature ← match checkedProgram.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature | _ => throw (IO.userError "read fixture function missing")
  match SourceSpecializationWorklist.run checkedProgram [⟨signature.id, []⟩] 100 with
  | .ok (.complete plan) => match plan.specializations with
    | [specialized] => pure specialized.function.typedBody
    | _ => throw (IO.userError "read fixture specialization changed")
  | other => throw (IO.userError s!"read fixture specialization: {reprStr other}")

/-- Checked source uses the actual compatible callback; the erased certificate
is extracted from the same successful call used to build the native program. -/
def run : IO Unit := do
  let checkedProgram ← get "source checker" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "function initialized(value: Bool) returns (Bool) { return value; }",
      "function absent() returns (Bool) { let value: Bool; return value; }",
      "function lazy() returns (mapping(Word => Word)) { let value: mapping(Word => Word); return value; }"
    ]}] })
  for name in ["initialized", "absent", "lazy"] do
    let source ← checkedSource checkedProgram name
    let (readNode, selected) ← match source.nodes.filterMap (fun
      | .expression node => match node.form with
        | .reference _ (.local binder) => some (node, binder) | _ => none
      | _ => none) with
      | [found] => pure found | _ => throw (IO.userError "read fixture occurrence count changed")
    let declared ← get "source declaration" (SourceCoreDataPlaces.rootBinder source selected)
    let checked ← get "read catalog" (SourceCoreCompatibleCatalog.prepare checkedProgram.signatures 100 [declared.scheme.body])
    let context := SourceCoreCompatibleValues.Context.initial checked
    let type ← get "read projection" (checked.catalog.project declared.scheme.body)
    let scope := [(selected, type)]
    let expression ← match accepted : SourceCoreCompatibleDataExpressions.lowerRead 100 context source scope readNode.id reason with
      | .ok code =>
        have receipt : Nonempty (Certificate 100 context source scope readNode.id reason code) := of_accepted accepted
        let _receipt := receipt
        pure code
      | .error error => throw (IO.userError s!"actual compatible read: {reprStr error}")
    let initial := if name == "initialized" then OptionalCell.allocateInitialized type (.bool true) else OptionalCell.allocate type
    let native : Core.Program := ⟨LanguageResult.resultType type, .letE initial expression, checked.catalog.definitions⟩
    assertTrue native.check "native checker rejected actual read"
    let expected ← if name == "initialized" then pure (.inRight .word (.bool true))
      else if name == "absent" then pure (.inLeft type (.word reason))
      else do
        let encoded ← get "empty mapping encoder" (SourceCoreCompatibleValues.encode 100 context declared.scheme.body (.mapping .word .word []))
        pure (.inRight .word encoded.value)
    for fuel in [0, 1, 3, 1000] do
      let completed := match native.runStateful fuel with
        | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
        | other => other
      match completed with
      | .done value store =>
        assertTrue (value == expected) s!"{name} read outcome mismatch"
        assertTrue (store.length == 1) s!"{name} read allocated an extra source cell"
        if name == "lazy" then
          match value with
          | .inRight .word payload => assertTrue (store[0]? == some (.inRight .unit payload)) "lazy read did not initialize the original cell"
          | _ => throw (IO.userError "lazy read failed")
      | other => throw (IO.userError s!"{name} native completion: {reprStr other}")
  IO.println "compatible actual read receipts and native resume GREEN"

end Tests.SourceCoreCompatibleExpressionReads
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleExpressionRecursive
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Recursive constructor/member/control composition is checked against actual
lowering, independent source typing, and both finite execution directions.
Positional members are introduced in retained typed IR. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace Tests.SourceCoreCompatibleExpressionRecursive
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionRecursive CompatiblePayload GeneralHeap ReadOnly

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"recursive_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "recursive_meaning.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def sourceType : TypeSystem.Ty := .nominal owner []
private def firstSignature : ProgramDataConstructorSignature :=
  ⟨⟨owner, 0⟩, "First", [.bool, .bool], ⟨span, ⟨[], ⟨span, "First"⟩, none⟩⟩⟩
private def secondSignature : ProgramDataConstructorSignature :=
  ⟨⟨owner, 1⟩, "Second", [.bool, .bool], ⟨span, ⟨[], ⟨span, "Second"⟩, none⟩⟩⟩
private def signature : ProgramDataSignature := {
  id := owner, name := "Row", parameters := [], constructors := [firstSignature, secondSignature]
  source := ⟨span, ⟨none, ⟨span, "Row"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def instantiation : DataConstructorInstantiation := ⟨secondSignature.id, [], [.bool, .bool], sourceType⟩
private def boolean : ExpressionNode := { id := id 0, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def constructorNode : ExpressionNode := { id := id 1, span, type := sourceType, form := .constructor instantiation [id 0, id 0] }
private def memberNode : ExpressionNode := { id := id 2, span, type := .bool, form := .member (id 1) "1" 1 }
private def unaryNode : ExpressionNode := { id := id 3, span, type := .bool, form := .unary .logicalNot (id 2) }
private def wrappedNode : ExpressionNode := { id := id 4, span, type := sourceType, form := .constructor instantiation [id 3, id 2] }
private def selectedNode : ExpressionNode := { id := id 5, span, type := .bool, form := .member (id 4) "0" 0 }
private def conditionalNode : ExpressionNode := { id := id 6, span, type := sourceType, form := .conditional (id 5) (id 4) (id 1) }
private def pairedNode : ExpressionNode := { id := id 7, span, type := .product sourceType .bool, form := .tuple [id 6, id 5] }
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 7)], nodes := [.expression boolean, .expression constructorNode, .expression memberNode,
      .expression unaryNode, .expression wrappedNode, .expression selectedNode, .expression conditionalNode, .expression pairedNode] }
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private def faults : FunctionCalls.FaultRep := fun error token =>
  (∃ location, error = .uninitializedLocation location) ∧ token = reason
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index native selected; cases selected
private theorem instanceValid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation := by
  refine .intro signature secondSignature (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    (by simp [signature]) rfl rfl ⟨by simp [signature], by simp [ParameterSubstitution.domain, instantiation, signature]⟩ ?_ rfl rfl
  intro parameter replacement member; cases member
private theorem nominalAdmitted : TypeAdmissible context sourceType :=
  ⟨TypeParameterBindersWellFormed.ofSignatures signatures,
    .nominal signature [] (by simp [context, SourceSemantics.Context.ofSignatures, signatures]) rfl .nil⟩
private theorem boolAdmitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
private theorem boolTyped : ExpressionHasType source context (id 0) .bool := by
  apply ExpressionHasType.ofOrdinary (node := boolean) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem constructorTyped : ExpressionHasType source context (id 1) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := constructorNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.constructor instanceValid.toAdmissible (.cons boolTyped (.cons boolTyped (.nil _)))) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem projection (index : Nat) (inBounds : index = 0 ∨ index = 1) : UniformMemberProjection context sourceType index .bool := by
  refine .intro (dataType := signature) (substitution := []) (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    ⟨by simp [signature], by simp [ParameterSubstitution.domain, signature]⟩ rfl nominalAdmitted boolAdmitted (by simp [signature]) ?_ ?_
  · intro constructor member
    simp only [signature, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rcases inBounds with rfl | rfl <;> rfl
  · intro actual admissible resultType
    cases admissible with
    | intro dataType constructor dataMember constructorMember _ _ _ _ payloads _ =>
      have same : dataType = signature := by simpa [context, SourceSemantics.Context.ofSignatures, signatures] using dataMember
      subst dataType
      simp only [signature, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at constructorMember
      rcases constructorMember with rfl | rfl <;> rw [payloads] <;> rcases inBounds with rfl | rfl <;> rfl
private theorem memberTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := memberNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.member constructorTyped (projection 1 (.inr rfl))) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem unaryTyped : ExpressionHasType source context (id 3) .bool := by
  apply ExpressionHasType.ofOrdinary (node := unaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.unary memberTyped .logicalNot) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem wrappedTyped : ExpressionHasType source context (id 4) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := wrappedNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.constructor instanceValid.toAdmissible (.cons unaryTyped (.cons memberTyped (.nil _)))) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem selectedTyped : ExpressionHasType source context (id 5) .bool := by
  apply ExpressionHasType.ofOrdinary (node := selectedNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.member wrappedTyped (projection 0 (.inl rfl))) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem conditionalTyped : ExpressionHasType source context (id 6) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := conditionalNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.conditional selectedTyped wrappedTyped constructorTyped) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem pairedTyped : ExpressionHasType source context (id 7) (.product sourceType .bool) := by
  have admitted : TypeAdmissible context (.product sourceType .bool) := .product nominalAdmitted boolAdmitted
  apply ExpressionHasType.ofOrdinary (node := pairedNode) (rawType := .product sourceType .bool)
    (lookupExpression?_sound (by cbv)) (.tuple (.cons conditionalTyped (.cons selectedTyped (.nil _)))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem originalSyntax : Syntax source (id 1) := by
  refine .constructor (node := constructorNode) (by cbv) rfl ?_
  intro child member
  have same : child = id 0 := by simpa using member
  subst child
  exact .fragment (.fragment (.fragment (.primitive (.product (.literal (node := boolean) (by cbv) (.bool _ _))))))
private theorem memberSyntax : Syntax source (id 2) :=
  .member (node := memberNode) (by cbv) rfl originalSyntax
private theorem wrappedSyntax : Syntax source (id 4) := by
  refine .constructor (node := wrappedNode) (by cbv) rfl ?_
  intro child member
  have alternatives : child = id 3 ∨ child = id 2 := by simpa using member
  rcases alternatives with rfl | rfl
  · exact .unary (node := unaryNode) (by cbv) rfl memberSyntax
  · exact memberSyntax
private theorem selectedSyntax : Syntax source (id 5) :=
  .member (node := selectedNode) (by cbv) rfl wrappedSyntax
private theorem syntaxTree : Syntax source (id 7) :=
  .pair (node := pairedNode) (by cbv) rfl
    (.conditional (node := conditionalNode) (by cbv) rfl selectedSyntax wrappedSyntax originalSyntax)
    selectedSyntax
private theorem contextValid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures]
  · intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; simp [context, SourceSemantics.Context.ofSignatures] at member
variable {checked : SourceCoreCompatibleCatalog.Checked}
private abbrev values (checked : SourceCoreCompatibleCatalog.Checked) := SourceCoreCompatibleValues.Context.initial checked
private abbrev policy (checked : SourceCoreCompatibleCatalog.Checked) := SourceCoreCompatibleDataExpressions.functionPolicy 20 (values checked)
private theorem certified (catalogSignatures : checked.signatures = signatures) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 30 compilation source [] (id 7) (fun _ => reason) = .ok code) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 7) code :=
  tree_of_functions (values := values checked) unique declarations catalogSignatures.symm rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) pairedTyped accepted

theorem contextual_certificate
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {lowered : SourceCoreBasic.LoweredExpr}
    (catalogSignatures : checked.signatures = signatures)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead 20 (values checked))
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer (values checked))
    (generated : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures ⟨[]⟩ parents assignments
      diagnostics compilation native parent none 30 source [] (id 7) (fun _ => reason) = .ok lowered) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 7) lowered := by
  exact tree_of_contextual (values := values checked)
    ⟨fun _ _ _ found => (metadata found).1, fun _ _ _ found => (metadata found).2, by intros; rfl, by intros; rfl⟩
    unique rfl rfl declarations catalogSignatures.symm syntaxTree (by cbv) pairedTyped readPolicy lowerPolicy leafPolicy generated

theorem actual_preserves {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked (values checked).registry functions)
      program context [] source (Tree 20 (values checked) source context [] (fun _ => reason)) faults :=
  preserves (values := values checked) functions (.refl _) program [] contextValid unique (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)
theorem actual_reflects {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked (values checked).registry functions)
      program context [] source (Tree 20 (values checked) source context [] (fun _ => reason)) faults :=
  reflects (values := values checked) functions (.refl _) program [] contextValid (fun _ location => ⟨⟨location, rfl⟩, rfl⟩)

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Row { First(Bool, Bool), Second(Bool, Bool) }",
    "function nested() returns (Row) { return .Second(true, true); }",
    "function child_fault() returns (Row) { let missing: Bool; return .First(missing, true); }",
    "function parent(seed: Bool) returns (Row) { let f = lam(item) -> Row { return .Second(seed, true); }; return f(true); }"]}] }

private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | fuel + 1, source, expression => match source.lookupExpression? expression with
    | none => []
    | some node => node :: (match node.form with
      | .unary _ operand => reached fuel source operand
      | .binary left _ right => reached fuel source left ++ reached fuel source right
      | .conditional condition thenId elseId => reached fuel source condition ++ reached fuel source thenId ++ reached fuel source elseId
      | .member base _ _ => reached fuel source base
      | .group inner => reached fuel source inner
      | .tuple ids | .constructor _ ids => ids.flatMap (reached fuel source)
      | _ => [])

private def inspect {catalog : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (original : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (name : String) (expression : ExpressionId) : IO Unit := do
  let contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let representation := SourceCoreCompatibleFunctions.representation contextValues 150
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "recursive diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "recursive root diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let originalRoot ← match original.lookupExpression? expression with
    | some node => pure node | none => throw (IO.userError "recursive original root missing")
  let .constructor constructor _ := originalRoot.form | throw (IO.userError "recursive original constructor missing")
  let newId := fun index => (⟨⟨original.owner, 100000 + index⟩⟩ : ExpressionId)
  let member : ExpressionNode := {id := newId 0, span := originalRoot.span, type := .bool, form := .member expression "0" 0}
  let negated : ExpressionNode := {id := newId 1, span := originalRoot.span, type := .bool, form := .unary .logicalNot member.id}
  let wrapped : ExpressionNode := {id := newId 2, span := originalRoot.span, type := originalRoot.type, form := .constructor constructor [negated.id, member.id]}
  let selected : ExpressionNode := {id := newId 3, span := originalRoot.span, type := .bool, form := .member wrapped.id "0" 0}
  let selectedRow : ExpressionNode := {id := newId 4, span := originalRoot.span, type := originalRoot.type, form := .conditional selected.id wrapped.id originalRoot.id}
  let disjunction : ExpressionNode := {id := newId 5, span := originalRoot.span, type := .bool, form := .binary selected.id .logicalOr member.id}
  let paired : ExpressionNode := {id := newId 6, span := originalRoot.span, type := .product originalRoot.type .bool, form := .tuple [selectedRow.id, disjunction.id]}
  let grouped : ExpressionNode := {id := newId 7, span := originalRoot.span, type := paired.type, form := .group paired.id}
  let source := {original with roots := [.expression grouped.id], nodes := original.nodes ++
    [member, negated, wrapped, selected, selectedRow, disjunction, paired, grouped].map Node.expression}
  let ids := ((reached 100 source grouped.id).filterMap fun node =>
    match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let bindings ← ids.mapM fun binder => do
    let declared ← get "recursive binder" (SourceCoreDataPlaces.rootBinder source binder)
    let type ← get "recursive binder type" (catalog.catalog.project declared.scheme.body)
    assertTrue (type == .bool) "recursive fixture binder is not Boolean"
    let initializer := if declared.name == "missing" then OptionalCell.allocate type
      else OptionalCell.allocateInitialized type (.bool true)
    pure (binder, type, initializer)
  let scope := bindings.map fun (binder, type, _) => (binder, type)
  let lowered ← get s!"actual contextual recursive {name}" (SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram
    representation catalog.signatures prepared.locals prepared.contexts own.assignments diagnostics compilation prepared.callableContext
    parent none 150 source scope grouped.id reasonAt)
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"recursive {name} failed native checker"
  for fuel in [0, 3, 15, 1000] do
    let finished := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 10000 checkpoint
      | other => other
    match finished with
    | .done value store =>
      assertTrue (store.length == bindings.length + 1) "recursive composition allocated unexpected cells"
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "recursive composition changed administrative closure"
      if name == "child_fault" then
        let faultNode ← match original.nodes.findSome? fun
          | .expression node => match node.form with | .reference "missing" (.local _) => some node | _ => none
          | _ => none with
          | some node => pure node | none => throw (IO.userError "recursive fault occurrence missing")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt faultNode.id))) "recursive composition changed first fault"
      else
        let payload ← match value with
          | .inRight .word payload => pure payload
          | _ => throw (IO.userError s!"recursive {name} did not succeed: {reprStr value}")
        let decoded ← get "recursive decode" (SourceCoreCompatibleValues.decode 100 contextValues grouped.type payload)
        match decoded with
        | .product (.constructed retained [.bool true, .bool true]) (.bool true) =>
            assertTrue (retained == constructor) "recursive composition erased raw constructor metadata"
        | other => throw (IO.userError s!"recursive result changed: {reprStr other}")
    | other => throw (IO.userError s!"recursive {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let checkedProgram ← get "recursive checker" (checkProgram workspace)
  let roots := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram roots 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"recursive specialization: {reprStr other}")
  let automatic ← get "recursive factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let mut rootsSeen := 0
  for function in automatic.prepared.functions do
    let name := (checkedProgram.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" then
      let source := function.specialized.function.typedBody
      let expression ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some expression => pure expression | none => throw (IO.userError "recursive return missing")
      inspect automatic.prepared source function.signature.key none function.specialized.function.solvedRequirements name expression
      rootsSeen := rootsSeen + 1
  let mut parentsSeen := 0
  for parent in automatic.prepared.contexts do
    if !parent.substitution.isEmpty then
      for entry in parent.source.nodes do
        match entry with
        | .expression node => match node.form with
          | .constructor _ _ =>
            inspect automatic.prepared parent.source parent.caller.key (some parent) parent.caller.function.solvedRequirements "parent" node.id
            parentsSeen := parentsSeen + 1
          | _ => pure ()
        | _ => pure ()
  assertTrue (rootsSeen == 2) s!"recursive root cases missing: {rootsSeen}"
  assertTrue (parentsSeen > 0) "recursive full parent case missing"
  IO.println "recursive data/control composition: member inside constructor, outer member, nominal conditional, primitive, product, raw header, fault, ambient parent and resume GREEN"

end Tests.SourceCoreCompatibleExpressionRecursive
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleLiteralRuntime
/-! Actual atomic compiler receipts supply the selected numeric evidence.
Full runtime ledgers, including unrelated assumptions, stay unchanged. This
unit covers the ordinary function-policy leaf branch; contextual expressions
and larger expression trees are not certified here. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleLiteralRuntime
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly

section Accepted
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (found : source.lookupExpression? id = some node)
  (atomic : CompatibleExpressionLiterals.Atomic node.form)
  (unitType : node.form = .tuple [] → node.type = .unit)
  (special : ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
  (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
  (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
  (program : SourceSemantics.Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context) (faults : FunctionCalls.FaultRep)

include found atomic unitType special readPolicy leafPolicy accepted sameLedger runtime

/-- No whole-context ordinary validity or source execution callback is needed
for a receipt taken from the actual accepted atomic compilation. -/
theorem accepted_preserves (unique : NodeOccurrencesUnique source) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun s i code => s = scope ∧ i = id ∧ code = lowered) faults := by
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted
  intro s i code selected
  obtain ⟨rfl, rfl, rfl⟩ := selected
  exact CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtime unique faults receipt

/-- The same static receipt closes reflection from native completion alone. -/
theorem accepted_reflects :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun s i code => s = scope ∧ i = id ∧ code = lowered) faults := by
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted
  intro s i code selected
  obtain ⟨rfl, rfl, rfl⟩ := selected
  exact CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtime source faults receipt
end Accepted

section ActualFrame
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
  {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
  {types : List TypeSystem.Ty} {solved : List SolvedRequirement}
  (frame : NamedCalls.SourceFrame program instantiation body function)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved)
  (faults : FunctionCalls.FaultRep)

include frame extended programTyped sameLedger

/-- Initial frame validity supplies the complete runtime ledger without an
empty-template condition, Header.valid, or an ordinary-ledger callback. -/
theorem frame_preserves (unique : NodeOccurrencesUnique function.source) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context function.evidence function.source
      (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved function.source id lowered) faults :=
  CompatibleExpressionLiteralRuntime.preserves functions program context function.evidence
    ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped) unique faults

theorem frame_reflects :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context function.evidence function.source
      (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved function.source id lowered) faults :=
  CompatibleExpressionLiteralRuntime.reflects functions program context function.evidence
    ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped) function.source faults
end ActualFrame


section Boundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def resolution : IntegerLiteralResolution := ⟨37, .word, ⟨0⟩⟩
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"literal_runtime", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def node : ExpressionNode := {
  id := ⟨⟨owner, 0⟩⟩, span := ⟨⟨.main, "literal_runtime.solc"⟩, 0, 2⟩,
  type := .word, form := .integerLiteral (.decimal "37") resolution, requirements := [⟨0⟩] }

/-- The old literal metadata deliberately does not certify implementation
provenance. A runtime-valid assumption-only ledger cannot replace acceptance. -/
theorem metadata_not_acceptance :
    CompatibleExpressionLiterals.Literal [row] node .word
      (LanguageResult.success (.word (Word.ofNatModulo 37))) ∧
    RuntimeRequirementLedgerValid ((Context.ofSignatures signatures).withSolvedRequirements [row]) ∧
    ¬ CompatibleExpressionLiteralRuntime.NumericSelected [row] node := by
  refine ⟨?_, ?_, ?_⟩
  · apply CompatibleExpressionLiterals.Literal.resolvedWord (validated := ⟨Word.ofNatModulo 37, [⟨0⟩]⟩) rfl
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩
    · exact numericLiteralValue?_sound rfl
    · exact ⟨row, by simp, rfl, rfl⟩
  · refine ⟨?_, ?_⟩
    · change ([⟨0⟩] : List RequirementId).Nodup
      decide
    · intro item evidence member implementation
      have eq : item = row := by simpa [Context.withSolvedRequirements] using member
      subst item
      cases implementation
  · intro selected
    obtain ⟨item, singleton, _, implementation⟩ := selected (.decimal "37") resolution rfl
    have eq : item = row := by simpa [row, resolution] using singleton.symm
    subst item
    cases implementation
end Boundary

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def huge : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639937
private def content : String := String.intercalate "\n" [
  "function unitRoot() { return (); }",
  "function boolRoot() returns (Bool) { return true; }",
  "function wordRoot() returns (Word) { let first = 0x25; return first; }",
  s!"function wrapRoot() returns (Word) \{ return {huge}; }",
  s!"function integerRoot() returns (integer) \{ let full = {huge}; return full; }",
  "function faultRoot() returns (Word) { let prior = 41; let missing: Word; return missing + 43; }"
]

private def scalar? : Expr → Option Core.Value
  | .unit => some .unit | .bool b => some (.bool b) | .word w => some (.word w)
  | .integer n => some (.integer n) | _ => none

private def inspectNode (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (rows : List SolvedRequirement) (node : ExpressionNode)
    (atomic : CompatibleExpressionLiterals.Atomic node.form) : IO Ty := do
  let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
  let policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
  let context : SourceCoreFunctions.Context := {
    plan := compiled.indexed.base.plan, owner := named.signature.key,
    globals := compiled.indexed.base.globals, administrativePrefix := 1,
    solvedRequirements := rows, internalReason := Word.zero }
  let lowerBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ =>
    .error (.unsupportedExpression node.id node.form)
  if found : source.lookupExpression? node.id = some node then
    if unitType : node.form = .tuple [] → node.type = .unit then
      match accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody 100 context source [] node.id (fun _ => Word.zero) with
      | .error error => throw (IO.userError s!"actual atomic compiler rejected: {reprStr error}")
      | .ok lowered =>
        have receipt : CompatibleExpressionLiteralRuntime.Certificate rows source node.id lowered := CompatibleExpressionLiteralRuntime.of_functions
          found atomic unitType (by intros; rfl) rfl rfl accepted
        let _receipt := receipt
        let expected ← match lowered.expression with
          | .inRight .word payload => match scalar? payload with
            | some value => pure (.inRight .word value)
            | none => throw (IO.userError "atomic payload is not scalar")
          | _ => throw (IO.userError "atomic language result carrier changed")
        match node.form with
        | .integerLiteral _ resolution =>
          let selected ← match rows.filter (·.id == resolution.requirement) with
            | [selected] => pure selected
            | _ => throw (IO.userError "atomic selected row is not singleton")
          let implementation : ProgramImplId := .builtin (if node.type == .integer then .intInteger else .intWord)
          require (selected.predicate == resolution.predicate &&
            selected.evidence == .implementation (.byImpl resolution.predicate implementation []))
            "atomic full implementation receipt changed"
          let numeric := if node.type == .integer then Core.Value.integer (Int.ofNat resolution.rawValue)
            else .word (Word.ofNatModulo resolution.rawValue)
          require (expected == .inRight .word numeric) "atomic numeric target/payload changed"
        | _ => pure ()
        let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
          .letE (.newCell (.function .unit .unit) (.lambda .unit .unit .unit)) (lowered.expression.weakenAt 0),
          compiled.compatible.checked.catalog.definitions⟩
        require native.check "actual atomic emission failed Core typing"
        for fuel in [0, 1, 5, 1000] do
          let completed := match native.runStateful fuel with
            | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
            | other => other
          match completed with
          | .done value store =>
            require (value == expected && store == [.closure .unit .unit .unit []])
              "atomic leaf changed result/administrative store on resume"
          | other => throw (IO.userError s!"atomic native completion missing: {reprStr other}")
        pure lowered.type
    else throw (IO.userError "atomic unit has wrong raw type")
  else throw (IO.userError "atomic occurrence lookup changed")

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut types := []
  let mut numeric := 0
  let mut legacy := 0
  for named in compiled.indexed.base.functions do
    let actual ← get "atomic actual specialization"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (actual == named.specialized) "atomic full selected record changed"
    let source : TypedSource := actual.function.typedBody
    let ledger : List SolvedRequirement := actual.function.solvedRequirements
    for retained in source.nodes do
      match retained with
      | .expression node =>
        let atomic : Option (PLift (CompatibleExpressionLiterals.Atomic node.form)) := match form : node.form with
          | .tuple [] => some ⟨form ▸ CompatibleExpressionLiterals.Atomic.unit⟩
          | .reference name (.builtinBoolean value) => some ⟨form ▸ CompatibleExpressionLiterals.Atomic.bool name value⟩
          | .literal value => some ⟨form ▸ CompatibleExpressionLiterals.Atomic.word value⟩
          | .integerLiteral value resolution => some ⟨form ▸ CompatibleExpressionLiterals.Atomic.integer value resolution⟩
          | _ => none
        if let some boxed := atomic then
          let atomic := boxed.down
          types := types ++ [← inspectNode compiled named source ledger node atomic]
          match node.form with
          | .integerLiteral _ resolution =>
            numeric := numeric + 1
            let fresh : RequirementId := ⟨(ledger.map (·.id.index)).foldl max 0 + 1⟩
            let assumption : SolvedRequirement := ⟨fresh, resolution.predicate, .assumption resolution.predicate⟩
            -- Explicit test mutations retain every original row; they are not
            -- asserted to be produced by the independent checker.
            for rows in [assumption :: ledger, ledger ++ [assumption]] do
              let type ← inspectNode compiled named source rows node atomic
              require (types.contains type) "unrelated assumption changed native type"
            let malformed := ledger.map fun row => if row.id == resolution.requirement then
              {row with evidence := .assumption row.predicate} else row
            let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
            let context : SourceCoreFunctions.Context := {
              plan := compiled.indexed.base.plan, owner := named.signature.key,
              globals := compiled.indexed.base.globals, administrativePrefix := 1,
              solvedRequirements := malformed, internalReason := Word.zero }
            let rejected := SourceCoreFunctions.lowerExpressionWithPolicy
              (SourceCoreCompatibleDataExpressions.functionPolicy 100 values)
              (fun _ _ _ _ _ _ _ _ _ => .error (.unsupportedExpression node.id node.form))
              100 context source [] node.id (fun _ => Word.zero)
            require rejected.toOption.isNone "actual compiler accepted missing implementation provenance"
            if node.type == .word then
              let old := {node with form := .literal (.decimal "37"), requirements := [], coercions := []}
              let oldSource := {source with nodes := source.nodes.map fun
                | .expression entry => if entry.id == old.id then .expression old else .expression entry
                | .statement entry => .statement entry}
              let oldType ← inspectNode compiled named oldSource ledger old (.word _)
              require (oldType == .word) "retained legacy literal branch missing"
              legacy := legacy + 1
          | _ => pure ()
      | _ => pure ()
  for expected in [Ty.unit, .bool, .word, .integer] do
    require (types.contains expected) s!"actual atomic family missed {reprStr expected}"
  require (numeric ≥ 5 && legacy ≥ 4) "atomic numeric/legacy audit too small"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"atomic full source heap changed: {reprStr state.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "atomic runtime receipts" content
    ["unitRoot", "boolRoot", "wordRoot", "wrapRoot", "integerRoot", "faultRoot"]
  inspect compiled
  let missing ← match (compiled.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "atomic missing binder identity lost")
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("unitRoot", .unit, []), ("boolRoot", .bool true, []),
    ("wordRoot", .word (Word.ofNatModulo 37), [(.word, some (.word (Word.ofNatModulo 37)))]),
    ("wrapRoot", .word (Word.ofNatModulo 1), []),
    ("integerRoot", .integer (Int.ofNat huge), [(.integer, some (.integer (Int.ofNat huge)))])]
  for fuel in [0, 37, 151, 300000] do
    for (name, expected, heap) in successes do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel
      let finished ← get "atomic public resume" (started.resume 300000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr expected) "atomic public completed value changed"
        cells state heap
      | other => throw (IO.userError s!"atomic public success expected: {reprStr other}")
    let started ← SourceCoreUnifiedCorpusSupport.execute compiled "faultRoot" [] fuel
    let finished ← get "atomic public fault resume" (started.resume 300000)
    match finished.observation with
    | .fault (.uninitializedLocal actual) state =>
      require (actual == missing) "atomic first fault identity changed"
      cells state [(.word, some (.word (Word.ofNatModulo 41))), (.word, none)]
    | other => throw (IO.userError s!"atomic first fault expected: {reprStr other}")
  IO.println "atomic actual receipts / full runtime ledger / Unit Bool Word Integer / full heap / resume GREEN"

end Tests.SourceCoreCompatibleLiteralRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMemberNativeTyping
/-! Heterogeneous packed fields retain complete callable carriers. The public
contextual consumer requires actual catalog/compiler acceptance and independent
source typing, without native child or branch typing callbacks. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMemberNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open CompatibleExpressionMemberNativeTyping CompatibleExpressionScalarNativeTyping

theorem callable_field_stays_one_packed_field (definitions : DataEnvironment) :
    HasType [SourceCoreCompatibleCatalog.packTypes [.word,
        CallableContract.functionType .bool .bool, .namedData ⟨27⟩]]
      (SourceCoreDataExpressions.projectPacked 1 [.word, CallableContract.functionType .bool .bool, .namedData ⟨27⟩] (.var 0))
      (CallableContract.functionType .bool .bool) definitions :=
  projectPacked_native (by rfl) (.var rfl)

theorem tagged_callable_field_stays_one_packed_field (definitions : DataEnvironment) :
    HasType [SourceCoreCompatibleCatalog.packTypes [.unit,
        TaggedFunction.functionType .word .integer, .cell .bool]]
      (SourceCoreDataExpressions.projectPacked 1 [.unit, TaggedFunction.functionType .word .integer, .cell .bool] (.var 0))
      (TaggedFunction.functionType .word .integer) definitions :=
  projectPacked_native (by rfl) (.var rfl)

theorem actual_contextual_members_native
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {readFuel : Nat} {reasonAt : ExpressionId → Word}
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment} (administrative : Core.Context)
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (ordinary : CompatibleExpressionMembers.Ordinary source locals compilation.owner)
    (unique : SourceSemantics.NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionMembers.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : SourceSemantics.ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  contextual_native visibleTypes administrative registered ordinary unique closed residual declarations sourceSignatures
    syntaxTree found sourceTyped readPolicy lowerPolicy leafPolicy accepted extension

end Tests.SourceCoreCompatibleMemberNativeTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleReadNativeTyping
/-! Native typing is obtained from actual compatible read acceptance and
independent source typing. The fixtures include staged mapping metadata and
arbitrary administrative context extensions. Unused invalid sum annotations
demonstrate why raw runtime typing cannot replace checked projection. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleReadNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionReads

/-- An external consumer needs neither a native child typing assumption nor
a source or Core execution premise. -/
theorem actual_read_native {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id) = .ok lowered.expression)
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
    (unique : NodeOccurrencesUnique source) (declarations : ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id node.type) (administrative : Core.Context) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) values.checked.catalog.definitions :=
  loweredRead_native_hasType accepted read unique declarations typed administrative

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"read_native", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "read_native.solc"⟩, 0, 1⟩
private def id : ExpressionId := ⟨⟨owner, 1⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def binder (type : TypeSystem.Ty) : TypedBinder := ⟨⟨owner, 0⟩, "value", .mono type, [], false, none⟩
private def node (type : TypeSystem.Ty) : ExpressionNode :=
  { id, span, type, form := .reference "value" (.local (binder type).id) }
private def source (type : TypeSystem.Ty) : TypedSource :=
  { owner, inputs := [binder type], roots := [.expression id], nodes := [.expression (node type)] }
private def sourceContext (type : TypeSystem.Ty) :=
  (SourceSemantics.Context.ofSignatures signatures).withLocal (binder type).id (binder type).scheme
private def reason : Word := Word.ofNatModulo 17
private def scope (type : Ty) : SourceCoreLocalCell.Scope := [((binder .bool).id, type)]
private theorem unique (type : TypeSystem.Ty) : NodeOccurrencesUnique (source type) := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]

private theorem declarations (sourceType : TypeSystem.Ty) (type : Ty) :
    ScopeDeclarations (source sourceType) (scope type) (sourceContext sourceType) := by
  intro id declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst id
    have actual : SourceCoreDataPlaces.rootBinder (source sourceType) (binder .bool).id = .ok (binder sourceType) := by
      simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, source, binder, node, TypeSystem.Scheme.mono]
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected

private theorem sourceTyped {type : TypeSystem.Ty} (typed : TypeAdmissible (sourceContext type) type) :
    ExpressionHasType (source type) (sourceContext type) id type := by
  have contains : ContainsExpression (source type) id (node type) := lookupExpression?_sound (by rfl)
  have scheme : SchemeWellFormed (sourceContext type) (binder type).scheme := SchemeWellFormed.monoAdmissible typed
  apply ExpressionHasType.ofOrdinary (node := node type) (rawType := type) contains
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) scheme []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply type)
      (by simp) (by intro _ member; cases member) (.nil)))) typed typed
  · intro requirement member; cases member
  · exact .nil _
  · rfl

private def mappingType : TypeSystem.Ty := .mapping (.comptime .bool) .word
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, mappingType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, mappingType]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private def boolLowered : SourceCoreBasic.LoweredExpr := ⟨.bool, OptionalCell.read .bool (.var 0) reason⟩

theorem ordinary_checked_read (administrative : Core.Context) :
    HasType (SourceCoreLocalCell.coreContext (scope .bool) ++ administrative) boolLowered.expression
      (LanguageResult.resultType .bool) checked.catalog.definitions := by
  apply actual_read_native (source := source .bool) (sourceContext := sourceContext .bool)
    (reasonAt := fun _ => reason) (node := node .bool)
    (show SourceCoreCompatibleDataExpressions.lowerRead 100 values (source .bool) (scope .bool) id reason = .ok boolLowered.expression by rfl)
    (show SourceCoreCompatibleDataExpressions.readExpression checked (source .bool) id = .ok (node .bool, .bool) by rfl)
    (unique _) (declarations _ _)
  exact sourceTyped (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder .bool).id (binder .bool).scheme))

private theorem mappingProjected : (checked.catalog.project mappingType).toOption.isSome = true := by rfl
private def mappingNative := (checked.catalog.project mappingType).toOption.get mappingProjected
private def mappingAction := SourceCoreCompatibleDataExpressions.lowerRead 5 values (source mappingType) (scope mappingNative) id reason

theorem mapping_checked_read {code : Expr} (accepted : mappingAction = .ok code) (administrative : Core.Context) :
    HasType (SourceCoreLocalCell.coreContext (scope mappingNative) ++ administrative) code
      (LanguageResult.resultType mappingNative) checked.catalog.definitions := by
  apply actual_read_native (source := source mappingType) (sourceContext := sourceContext mappingType)
    (reasonAt := fun _ => reason) (lowered := ⟨mappingNative, code⟩) (node := node mappingType)
    accepted
    (show SourceCoreCompatibleDataExpressions.readExpression checked (source mappingType) id = .ok (node mappingType, mappingNative) by rfl)
    (unique _) (declarations _ _)
  exact sourceTyped (.mapping
    (.comptime (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder mappingType).id (binder mappingType).scheme)))
    (.word ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder mappingType).id (binder mappingType).scheme)))

private def missingData : Ty := .namedData ⟨0⟩
theorem unused_annotation_runtime_typed :
    RuntimeValueHasType [] (.inLeft missingData .unit) (.sum .unit missingData) [] := .inLeft .unit
theorem unused_annotation_quoted :
    SourceCoreCompatibleDataExpressions.quote (.inLeft missingData .unit) = some (.inLeft missingData .unit) := rfl
theorem unused_annotation_rejected (context : Core.Context) :
    ¬ HasType context (.inLeft missingData .unit) (.sum .unit missingData) [] := by
  intro typed
  cases typed with
  | inLeft wellFormed _ => cases wellFormed with | namedData found => cases found

def run : IO Unit := do
  let code ← match accepted : mappingAction with
    | .error error => throw (IO.userError s!"actual staged mapping read: {reprStr error}")
    | .ok code =>
      have derived : HasType (SourceCoreLocalCell.coreContext (scope mappingNative)) code
          (LanguageResult.resultType mappingNative) checked.catalog.definitions := by
        simpa only [List.append_nil] using mapping_checked_read accepted []
      let _derived := derived
      pure code
  let encoded ← match SourceCoreCompatibleValues.encode 5 values mappingType (.mapping (.comptime .bool) .word []) with
    | .error error => throw (IO.userError s!"staged empty mapping: {reprStr error}")
    | .ok encoded => pure encoded.value
  let initial : Store := [.integer 77, .inLeft mappingNative .unit]
  let expected : Value := .inRight .word encoded
  unless Core.infer? (SourceCoreLocalCell.coreContext (scope mappingNative)) code checked.catalog.definitions =
      some (LanguageResult.resultType mappingNative) do
    throw (IO.userError "actual mapping read native typing changed")
  for fuel in [0, 1, 3, 97, 2000] do
    let state := State.initial code [.cellRef (OptionalCell.cellType mappingNative) 1] initial
    let completed := match Core.runStateful fuel state with
      | .outOfFuel suspended => Core.runStateful 2000 suspended
      | other => other
    match completed with
    | .done actual store =>
      unless actual == expected && store == [.integer 77, .inRight .unit encoded] do
        throw (IO.userError "staged lazy mapping read lost metadata, prefix, write or resumed result")
    | other => throw (IO.userError s!"actual mapping read completion: {reprStr other}")
  IO.println "compatible native read typing: accepted ordinary/staged mapping reads, checked unused annotations, retained metadata/prefix and real resume GREEN"

end Tests.SourceCoreCompatibleReadNativeTyping
end
