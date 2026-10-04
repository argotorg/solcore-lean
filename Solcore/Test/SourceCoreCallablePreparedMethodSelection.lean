import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Test.SourceCoreUnifiedOperatorCorpus
import Solcore.Test.SourceCoreCallableCoercionSourceSelection

/-! Actual operator receipt tests. Static source judgments retain independent
formation and whole-program assumptions. Public runtime checks use the original
compiled source; marker callbacks below audit only the selected lowering shape. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreCallablePreparedMethodSelection
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallablePreparedMethodSelection
open CallableNamedMetadata (environment)
open CallableCoercionMethodInstantiation (Formation bodyInstance)
open SourceCompilerFeatureSupport

abbrev actual_unary := @CallablePreparedMethodSelection.unary_of_accepted
abbrev actual_binary := @CallablePreparedMethodSelection.binary_of_accepted
abbrev actual_lowering := @CallablePreparedMethodSelection.of_accepted

variable {program : CheckedProgram} {project : CallableCoercionExpressionCertificates.Projector}
  {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
  {child : SourceCoreEvidence.Child} {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Core.Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  {receipt : Operator program project caller compilation child fuel source scope id reasonAt policy node output}

/-- The same actual selector gives the source judgment and the existing method
body typing certificate, including runtime validity of its complete ledger. -/
theorem actual_source {loaded : LoadedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    (selected : SourceReceipt receipt)
    (formed : Formation selected.certificate.selected.implementation selected.certificate.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures program.signatures) receipt.selection.method.specialized.parameterSubstitution)
    {context : SourceSemantics.Context} (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller receipt.selection.method)
    (programTyped : ProgramWellFormed (Program.ofChecked program)) :
    Dynamic.OperatorMethodSelected (Program.ofChecked program) context (environment receipt.available)
      selected.traitName selected.methodName receipt.requirements (bodyInstance program receipt.selection.method)
      (environment receipt.dictionary) ∧
    ∃ types lexicalContext facts,
      Dynamic.BodyInstanceTypingCertificate (Program.ofChecked program) (bodyInstance program receipt.selection.method)
        types lexicalContext facts ∧
      CompatibleRuntimeContextValidity.Valid (bodyInstance program receipt.selection.method).context.solvedRequirements
        lexicalContext (environment receipt.dictionary) := by
  have sourceSelected := selected.selects loadedAccepted formed range signatures ledger assumptions covered
  exact ⟨sourceSelected, selected_typed sourceSelected programTyped⟩

abbrev actual_cache := @CallablePreparedMethodSelection.cached_row
abbrev actual_frame := @CallablePreparedMethodSelection.Cached.frame

theorem ordered_children (actual : Operator program project caller compilation child fuel source scope id reasonAt policy node output) :
    actual.arguments.mapM (fun id => child fuel source scope id reasonAt) = .ok actual.loweredArguments ∧
      SourceCoreEvidence.applyCoercions program project compilation caller actual.available scope node policy
        actual.operand node.coercions = .ok output :=
  ⟨actual.argumentsAccepted, actual.suffix.accepted⟩

theorem full_target (actual : Operator program project caller compilation child fuel source scope id reasonAt policy node output) :
    SourceCompilationPlan.exactSpecialization compilation.plan actual.key = .ok actual.target.specialized ∧
      compilation.globals.zipIdx.filter (fun row => decide (row.1.key = actual.key)) = [(actual.native.signature, actual.native.index)] :=
  ⟨actual.target.selected, actual.target.global⟩

/-- The actual staged guard allows marked methods under the enabled policy.
This static receipt does not assert that all methods are ordinary. -/
theorem staged_guard_allows (returnComptime : Bool) (parameters : List TypedBinder) :
    (!true && (returnComptime || parameters.any (·.comptime))) = false := rfl

theorem dictionary_order (first second : TypedTraitResolution.Evidence) (different : first ≠ second) :
    [first, second, first] ≠ [first, first, second] := by
  intro same
  exact different (List.cons.inj (List.cons.inj same).2).1.symm

abbrev range_stays_explicit := @SourceCoreCallableCoercionSourceSelection.ground_is_not_range
abbrev retained_parameter_order := @SourceCoreCallableCoercionSourceSelection.reversed_collector


/-- The actual preparation removes the former independent final-row premise.
Its staged boundary uses the emitter's exact argument order and full method. -/
theorem actual_prepared
    (actual : Operator program project caller compilation child fuel source scope id reasonAt policy node output)
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes) :
    actual.target.specialized = actual.selection.method.specialized ∧
      SourceCompilationPlan.validateStagedCallBoundary caller
        (CallableCoercionExpressionCertificates.rawNode node actual.requirements)
        actual.arguments actual.selection.method.specialized = .ok () := by
  obtain ⟨visit, requirements, selection, arguments, _, same⟩ := actual.prepared prepared callerMember nodeMember
  refine ⟨same, ?_⟩
  simpa only [CallableCoercionPreparationSteps.operatorOwnedNode, CallableCoercionExpressionCertificates.rawNode,
    requirements, selection, arguments] using visit.staged

abbrev actual_prepared_frame := @CallablePreparedMethodSelection.SourceReceipt.prepared_frame

private def content := String.intercalate "\n" [
  "trait Marker<T> {}", "trait Witness<T> {}",
  "impl<A, B> Marker<(A, B)> {}", "impl<A, B> Witness<(A, B)> {}",
  "trait Add<T> where T: Marker { function add(left: T, right: T) returns (T) where T: Witness; }",
  "trait BitNot<T> where T: Marker { function bnot(value: T) returns (T) where T: Witness; }",
  "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
  "impl<B, A> Add<(A, B)> where (A, B): Marker { function add(left: (A, B), right: (A, B)) returns ((A, B)) where (A, B): Witness { let unused: Word = 11; return right; } }",
  "impl<B, A> BitNot<(A, B)> where (A, B): Marker { function bnot(value: (A, B)) returns ((A, B)) where (A, B): Witness { let unused: Word = 13; return value; } }",
  "impl<B, A> Coerce<(A, B), Word> { function coerce(value: (A, B)) returns (Word) { return 19; } }",
  "function via<T>(left: T, right: T) returns (T) where T: Add, T: Marker, T: Witness, T: Marker { return left + right; }",
  "function binary(a: Word, b: Bool) returns ((Word, Bool)) { let left: (Word, Bool) = (a, b); let right: (Word, Bool) = (7, false); return via(left, right); }",
  "function unary(a: Word, b: Bool) returns ((Word, Bool)) { let value: (Word, Bool) = (a, b); return ~value; }",
  "function coerced(a: Word, b: Bool) returns (Word) { let value: (Word, Bool) = (a, b); return value + value; }",
  "function firstFault() returns ((Word, Bool)) { let left: (Word, Bool); let right: (Word, Bool) = (7, false); return left + right; }"
]

/-- Marker children audit the real lowering branch and its exact ordered call
code. Public execution below uses the original compiler callbacks and bodies. -/
private def inspect (cached : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let base := cached.indexed.base
  let program := cached.sourceProgram
  let representation := SourceCoreCompatibleFunctions.representation (.initial cached.compatible.checked) cached.compilationFuel
  let project := representation.expressions.projectType
  let policy : SourceCoreFunctions.CallablePolicy := {allowStaged := representation.allowStaged}
  let mut unaryCount := 0
  let mut binaryCount := 0
  let mut suffixCount := 0
  let mut coveredCount := 0
  let mut uncoveredCount := 0
  for named in base.functions do
    let caller := named.specialized
    let available ← get "actual operator caller" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
    for item in caller.function.typedBody.nodes do
      match item with
      | .expression node =>
        let ids? := match node.form with
          | .unary _ operand => some [operand]
          | .binary left _ right => some [left, right]
          | _ => none
        match ids?, SourceCompilationPlan.ordinaryOwnedRequirements? node with
        | some ids, some requirements =>
          if requirements.isEmpty then continue
          let owned := CallableCoercionExpressionCertificates.rawNode node requirements
          let selection ← get "actual operator selector" (match node.form with
            | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod program caller owned available operator
            | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod program caller owned available operator
            | _ => .error (.unsupportedRequirements requirements))
          if ids.length == 1 then unaryCount := unaryCount + 1 else binaryCount := binaryCount + 1
          let method := selection.method
          let dictionary ← get "actual ordered operator dictionary" (SourceCompilationPlan.operatorMethodRuntimeEvidence program caller owned selection)
          let headers ← get "actual method header roots" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program method.specialized.key method.traitPredicates)
          require (dictionary == headers ++ method.implementationPremises ++ method.methodPremises &&
            dictionary.length == 3 && dictionary[0]? == dictionary[1]? && dictionary[1]? != dictionary[2]?)
            "operator complete dictionary order changed"
          if method.traitPredicates.all caller.assumptions.contains then coveredCount := coveredCount + 1
          else uncoveredCount := uncoveredCount + 1
          let implementation ← match program.signatures.implementations.filter (·.id == method.id.implementation) with
            | [value] => pure value | _ => throw (IO.userError "operator impl singleton missing")
          let retained ← match program.methods.filter (·.id == method.id) with
            | [value] => pure value | _ => throw (IO.userError "operator retained checker body missing")
          require (TypedTraitResolution.ruleParameters implementation.implRule == implementation.parameters.reverse &&
            implementation.parameters != implementation.parameters.reverse &&
            method.specialized.parameterSubstitution.map Prod.fst == implementation.parameters)
            "operator raw substitution order became trivial"
          let selected ← get "operator full selected carrier" (SourceCompilationPlan.exactSpecialization base.plan method.specialized.key)
          require (selected == method.specialized &&
            selected.function.typedBody == StructuralSubstitution.applyTypedSource selected.parameterSubstitution retained.checked.typedBody &&
            selected.function.solvedRequirements == retained.checked.solvedRequirements.map
              (StructuralSubstitution.applySolvedRequirement selected.parameterSubstitution)) "operator full body/unused ledger changed"
          let namedRows := base.functions.zipIdx.filter (fun row => row.1.specialized == selected)
          let (actual, index) ← match namedRows with
            | [row] => pure row | _ => throw (IO.userError "operator full named cache row missing")
          require (actual.inputs.map Prod.fst == selected.function.typedBody.inputs &&
            (base.plan.specializations.reverse[index]?) == some selected &&
            (cached.indexed.secondPass.closures[index]?).isSome) "operator physical slot/raw binder/cache changed"
          let compilation : SourceCoreFunctions.Context := {
            plan := base.plan, owner := caller.key, globals := base.globals, administrativePrefix := 0,
            solvedRequirements := caller.function.solvedRequirements, internalReason := word 29 }
          let reasonAt := fun id : ExpressionId => word (1000 + id.occurrence.index)
          let child : SourceCoreEvidence.Child := fun remaining source _ childId _ => do
            if remaining != 37 then throw (.unsupportedExpression node.id node.form)
            let childNode ← match source.lookupExpression? childId with
              | some value => pure value | none => throw (.unsupportedExpression node.id node.form)
            let type ← project (.occurrence childId.occurrence) childNode.type
            pure ⟨type, .inLeft type (.word (reasonAt childId))⟩
          let codes ← ids.mapM (fun id => get "actual ordered marker child" (child 37 caller.function.typedBody [] id reasonAt))
          let signature := actual.signature
          let operand : SourceCoreBasic.LoweredExpr := ⟨signature.resultType,
            SourceCoreCalls.call signature index (SourceCoreCalls.packArguments codes).expression compilation.internalReason⟩
          let expected ← get "actual result coercion suffix" (SourceCoreEvidence.applyCoercions program project compilation caller available [] node policy operand node.coercions)
          let lowered ← get "actual operator lowering" (SourceCoreEvidence.lowerWithProjector program project caller compilation child
            37 caller.function.typedBody [] node.id reasonAt policy)
          require (lowered == some expected) "operator same ordered call/suffix/fuel changed"
          require (SourceCoreEvidence.lowerWithProjector program project caller compilation child 36
            caller.function.typedBody [] node.id reasonAt policy).toOption.isNone "operator child fuel was not preserved"
          suffixCount := suffixCount + node.coercions.length
          let ledger := caller.function.solvedRequirements
          let first ← match ledger with | first :: _ => pure first | _ => throw (IO.userError "operator ledger empty")
          let extra := {first with id := ⟨(ledger.map (fun (row : SolvedRequirement) => row.id.index)).foldl max 0 + 1⟩, evidence := .assumption first.predicate}
          for complete in [extra :: ledger, ledger ++ [extra]] do
            let retainedCaller := {caller with function := {caller.function with solvedRequirements := complete}}
            let same ← get "operator full unused row" (SourceCoreEvidence.lowerWithProjector program project retainedCaller
              {compilation with solvedRequirements := complete} child 37 caller.function.typedBody [] node.id reasonAt policy)
            require (same == lowered) "unused retained row changed actual operator materialization"
        | _, _ => pure ()
      | _ => pure ()
  require (unaryCount > 0 && binaryCount > 1 && suffixCount > 0 && coveredCount > 0 && uncoveredCount > 0)
    s!"operator actual inventory not exercised {unaryCount}/{binaryCount}/{suffixCount}/{coveredCount}/{uncoveredCount}"

private def full_native (cached : SourceCoreUnifiedCompilation.Compiled)
    (root : SourceSpecialization.SpecializationKey) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) : IO (String × String × Bool) := do
  let first ← get "operator native startup" (cached.run root arguments 1024 fuel)
  let final ← get "operator native resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution | none => throw (IO.userError "operator execution rejected")
  let failed ← match execution.completion.result.native.observation with
    | .succeeded _ _ => pure false | .failed _ _ => pure true
    | _ => throw (IO.userError "operator native did not complete")
  pure (reprStr final.observation, reprStr execution.completion.result.native.observation, failed)

def run : IO Unit := do
  let program ← get "actual operator source" (checkProgram {entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}]})
  let names := ["binary", "unary", "coerced", "firstFault"]
  let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
  let compiled ← get "actual public operator compile" (SourceCoreCompiler.compileChecked program
    (roots.map fun key => SourceCoreCompiler.Seed.declaration key.declaration []) {specializationBudget := 512, compilationFuel := 1000})
  let cached ← match compiled.artifact? with | some value => pure value | none => throw (IO.userError "operator actual cache absent")
  inspect cached
  for index in [0, 1, 2] do
    let entry ← SourceCompilerFeatureSupport.fromCompiled compiled index
    let expected : SourceCoreExecution.Value := if index == 0 then .product (scalar 7) (.bool false)
      else if index == 1 then .product (scalar 5) (.bool true) else scalar 19
    require ((← entry.run [scalar 5, .bool true]) == expected) "operator original public result changed"
    entry.checkResume [scalar 5, .bool true] expected 7
  for (name, root) in names.zip roots do
    let arguments : List SourceTypedRuntime.Value := if name == "firstFault" then [] else [.word (word 5), .bool true]
    let baseline ← full_native cached root arguments 300000
    require (baseline.2.2 == (name == "firstFault")) "operator public source/native fault boundary changed"
    for fuel in [0, 1, 31, 300000] do
      require ((← full_native cached root arguments fuel) == baseline) "operator full native/source heaps or resume changed"
  let faultKey ← SourceCoreUnifiedCorpusSupport.key program "firstFault"
  let faultCaller ← get "fault original source" (SourceCompilationPlan.exactSpecialization cached.indexed.base.plan faultKey)
  let missing ← match (SourceCoreDataPlaces.declaredBinders faultCaller.function.typedBody).filter (·.name == "left") with
    | [binder] => pure binder.id | _ => throw (IO.userError "operator first missing binder absent")
  let fault ← get "operator exact first fault" (cached.run faultKey [] 1024 300000)
  match fault.observation with
  | .fault (.uninitializedLocal actual) state =>
    let type := TypeSystem.Ty.product .word .bool
    let expected : List SourceTypedRuntime.Cell := [⟨type, none⟩, ⟨type, some (.product (.word (word 7)) (.bool false))⟩]
    require (actual == missing && reprStr state.heap == reprStr expected)
      "operator first missing binder/ordered source heap/suffix skip changed"
  | _ => throw (IO.userError "operator first fault kind changed")
  IO.println "prepared methods: actual unary/binary selection/full dictionaries/raw substitution order/unused rows/physical cache/suffix; original public full heap/resume GREEN"

end Tests.SourceCoreCallablePreparedMethodSelection
