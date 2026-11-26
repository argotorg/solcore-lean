import Solcore.Test.SourceSemantics.CoreLowering.Accepted.OneCall

/-!
# Indirect calls at the accepted-body public root

`viaLocal` binds `identity`, the program's first function, to a local `f` of type
`function(word) returns (word)` and returns `f(value)`, an indirect call of a named function value; `viaBuiltin`
binds `add`, the opcode that the program imports from `std.opcodes`, to a local `plus` of type
`function(word, word) returns (word)` and returns `plus(value, value)`, an indirect call of a builtin closure.
Every function of the program returns a `word`, so every instantiation the plan records has a runtime contract.

Runtime checks place every expression node of the three rows among the nested sites of the family that admits
every instantiation the plan records, given that admission, and each statement list in the supported shape.
With the complete inventory the rows make a family, and since every row the plan records is monomorphic and
without assumptions, every instantiation of the family is a row's retained instantiation, whose static receipts
the inventory gives. The original Source executions of `viaLocal`, whose call runs `identity`'s body instance,
and of `viaBuiltin`, whose call applies the opcode to the packed words, are lifted to staged traces, and the
call root's theorems apply at the first public call of each in both directions.

Main declarations: `Tests.SourceCoreAcceptedIndirect.Planned`,
`Tests.SourceCoreAcceptedIndirect.planned_retained`,
`Tests.SourceCoreAcceptedIndirect.planned_callees`,
`Tests.SourceCoreAcceptedIndirect.viaLocal_source`,
`Tests.SourceCoreAcceptedIndirect.viaBuiltin_source`,
`Tests.SourceCoreAcceptedIndirect.accepted_call`,
`Tests.SourceCoreAcceptedIndirect.accepted_reflection` and the runtime check
`Tests.SourceCoreAcceptedIndirect.AcceptedIndirectRuntime.run`.
-/

section
/-! The family of the planned instantiations: the instantiations the plan records, which it admits
(`Planned.covers`), and, in a plan whose rows are monomorphic and without assumptions, the retained
instantiations of the plan's rows (`planned_retained`). A cache row's checks given that admission accept its
uncoerced indirect calls, and the complete inventory gives the static receipts of the family's callees. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreAcceptedIndirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreAcceptedFixture

/-- The instantiations the plan records: those with an exact target key. -/
def Planned (plan : SourceCompilationPlan.Plan) (instantiation : DeclarationInstantiation) : Prop :=
  ∃ key, SourceCompilationPlan.exactInstantiationKey plan instantiation = .ok key

instance (plan : SourceCompilationPlan.Plan) : DecidablePred (Planned plan) := fun instantiation =>
  match target : SourceCompilationPlan.exactInstantiationKey plan instantiation with
  | .ok key => isTrue ⟨key, target⟩
  | .error _ => isFalse fun ⟨_, other⟩ => by rw [target] at other; cases other

/-- The family of the planned instantiations admits every instantiation the plan records. -/
theorem Planned.covers (plan : SourceCompilationPlan.Plan) :
    CellAwareInvocationAcceptedIndirectPremises.CoversPlan plan (Planned plan) :=
  fun _ key target => ⟨key, target⟩

/-- A planned instantiation of a plan whose rows are monomorphic and without assumptions is the retained
instantiation of the row it selects. -/
theorem planned_retained {plan : SourceCompilationPlan.Plan}
    (monomorphic : ∀ row ∈ plan.specializations, row.parameterSubstitution = [] ∧ row.assumptions = [])
    {instantiation : DeclarationInstantiation} (planned : Planned plan instantiation) :
    ∃ row ∈ plan.specializations, instantiation = CallableNamedCanonicalOrder.retainedInstantiation row := by
  obtain ⟨key, target⟩ := planned
  unfold SourceCompilationPlan.exactInstantiationKey at target
  split at target
  · cases target
  · rename_i row filtered
    have member : row ∈ [row] := .head _
    rw [← filtered] at member
    obtain ⟨rowMember, matching⟩ := List.mem_filter.mp member
    obtain ⟨substitution, assumptions⟩ := monomorphic row rowMember
    refine ⟨row, rowMember, ?_⟩
    simp only [SourceCompilationPlan.specializationMatchesInstantiation, Bool.and_eq_true, beq_iff_eq,
      substitution, assumptions] at matching
    obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, declaration⟩, equivalent⟩, type⟩, predicates⟩, comptime⟩, returnComptime⟩ := matching
    cases instantiation with
    | mk declared parameters instantiated required flags returned =>
      cases parameters with
      | cons _ _ => simp [SourceCompilationPlan.parameterSubstitutionsEquivalent] at equivalent
      | nil =>
        cases required with
        | cons _ _ => cases predicates
        | nil =>
          simp only at declaration type comptime returnComptime
          simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation,
            substitution, assumptions, declaration, type, comptime, returnComptime]
  · cases target

variable {workspace : Workspace.RawWorkspace} {options : SourceCoreCompiler.Options}

/-- The checks of one cache row, as `observeCallRow`'s, given that the family admits every instantiation the
plan records: they also accept the row's uncoerced indirect calls. -/
def observeCoveredCallRow (fixture : CompiledFixture workspace options) (called : DeclarationInstantiation → Prop)
    [DecidablePred called]
    (covers : CellAwareInvocationAcceptedIndirectPremises.CoversPlan fixture.recipe.compiled.indexed.base.plan called)
    (named : SourceCoreGeneralFunctions.Function) : IO (CallRow fixture called named) := do
  let source := CallableIndexedNamedGeneration.source named
  let some ⟨nodes⟩ := CellAwareInvocationAcceptedNestedCheck.nodes? fixture.recipe.compiled.indexed named source
      called (some ⟨covers⟩)
    | throw (IO.userError "accepted indirect row outside the nested sites")
  let statements := source.roots.filterMap fun root =>
    match root with
    | .statement id => some id
    | .expression _ => none
  let ⟨roots⟩ ← observed (source.roots = statements.map NodeId.statement) "accepted indirect statement roots"
  let some ⟨shape⟩ := CellAwareInvocationAcceptedBodyShape.shapeWith? source
      named.specialized.function.inferredBodyType _
      (fun id => CellAwareInvocationAcceptedNestedCheck.nested? fixture.recipe.compiled.indexed named source called
        (source.nodes.length + 1) id (some ⟨covers⟩))
      (source.nodes.length + 1) true statements
    | throw (IO.userError "accepted indirect statement shape")
  match assumptions : named.specialized.assumptions with
  | [] => return ⟨nodes, statements, roots, shape, assumptions⟩
  | _ :: _ => throw (IO.userError "accepted indirect row assumptions")

def observeCoveredCallRows (fixture : CompiledFixture workspace options) (called : DeclarationInstantiation → Prop)
    [DecidablePred called]
    (covers : CellAwareInvocationAcceptedIndirectPremises.CoversPlan fixture.recipe.compiled.indexed.base.plan called) :
    (functions : List SourceCoreGeneralFunctions.Function) → IO (CallRows fixture called functions)
  | [] => pure .nil
  | named :: rest =>
    return .cons (← observeCoveredCallRow fixture called covers named)
      (← observeCoveredCallRows fixture called covers rest)

private theorem statementRoots_functional {roots : List NodeId} {left right : List StatementId}
    (first : Dynamic.StatementRoots roots left) (second : Dynamic.StatementRoots roots right) : left = right := by
  induction first generalizing right with
  | nil =>
    cases second
    rfl
  | cons _ ih =>
    cases second with
    | cons tail => rw [ih tail]

/-- The static receipts of the admitted callees, when every instantiation the family admits is the retained
instantiation of a row the plan records and every cache row is checked, as `WholeInventory.callees`'s: the
plan's row is the specialization of a cache row, whose issued header the complete inventory retains. -/
theorem planned_callees {fixture : CompiledFixture workspace options} (whole : WholeInventory fixture)
    {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (admitted : ∀ {instantiation}, called instantiation →
      ∃ original ∈ fixture.recipe.compiled.indexed.base.plan.specializations,
        instantiation = CallableNamedCanonicalOrder.retainedInstantiation original) :
    CellAwareInvocationAcceptedCallLifting.Callees fixture.recipe.compiled.indexed
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) called := by
  intro instantiation bodyInstance roots admits instantiates rootsEq
  obtain ⟨original, member, same⟩ := admitted admits
  subst same
  obtain ⟨cached⟩ := CallablePreparedMethodSelection.cached_row fixture.recipe.compiled member
  obtain ⟨input, present, _slot, selectedNamed⟩ := whole.complete cached.selected
  obtain ⟨packet, retained⟩ := whole.rows.row_at input present
  have inputRow : input.row = original :=
    input.prepared.same.symm.trans ((congrArg (·.specialized) selectedNamed).trans cached.same)
  have frameInstantiated := packet.header.frame.instantiated
  rw [packet.aligned.metadata, inputRow] at frameInstantiated
  have bodySame := BuiltinNamedCalls.instantiation_unique_of_wellFormed wellFormed instantiates frameInstantiated
  subst bodySame
  have rootsSame := statementRoots_functional rootsEq packet.header.frame.roots
  subst rootsSame
  have view : Staging.Recursive.globalView packet.header.sourceBody [] packet.header.function.body =
      packet.header.function := by
    have same := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view packet.sourceAt
    rw [← packet.sourceAt.dictionary, calls.header_evidence packet] at same
    exact same
  obtain ⟨sidecar, _issued, closure⟩ := whole.invocation packet retained
  refine ⟨RecursiveStageRegistry.scope sidecar [] packet.header.function, input.prepared.named,
    packet.header.function.resultType, ?_, ?_, ?_⟩
  · rw [view]
    exact closure
  · rw [← packet.header.frame.source]
    exact packet.header.unique
  · rw [← packet.header.frame.source]
    exact calls.header_shape packet

end Tests.SourceCoreAcceptedIndirect
end

section
/-! The program and the declarative typing of its three functions, constructed from checked source
observations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreAcceptedIndirect
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceCoreAcceptedFixture (observed)
open Tests.SourceCoreOperatorCalls (functionType TypedNode)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{
    path := "main.solc", content := String.intercalate "\n" [
      "pragma solcore;",
      "import { add } from std.opcodes;",
      "function identity(value: word) returns (word) { return value; }",
      "function viaLocal(value: word) returns (word) { let f: function(word) returns (word) = identity; " ++
        "return f(value); }",
      "function viaBuiltin(value: word) returns (word) { let plus: function(word, word) returns (word) = add; " ++
        "return plus(value, value); }" ]}] }

def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}

/-- The type of the opcode `add` and of `viaBuiltin`'s local. -/
def adderType : TypeSystem.Ty := .function (.product .word .word) .word

/-- The opcode `add`'s catalogued type is `adderType`. -/
theorem adder_type : (BuiltinFunctionId.wordOpcode .add).type = adderType := rfl

private theorem statementRoots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]

private theorem parameter_nil (type : TypeSystem.Ty) :
    TypeSystem.ParameterSubstitution.apply [] type = type := by
  induction type <;> simp_all [TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?]

/-- A reference to a monomorphic declaration of type `function(word) returns (word)` as a value. -/
structure NamedValue (source : TypedSource) (signature : ProgramFunctionSignature) where
  value : TypedNode source functionType
  name : String
  instantiation : DeclarationInstantiation
  form : value.node.form = .reference name (.declaration instantiation)
  scheme : signature.scheme = ⟨[], [], functionType⟩
  exact : instantiation = ⟨signature.id, [], functionType, [], signature.parameterComptime, signature.returnComptime⟩

theorem NamedValue.typed {source : TypedSource} {signature : ProgramFunctionSignature}
    (named : NamedValue source signature) {context : SourceSemantics.Context}
    (member : signature ∈ context.signatures.functions) (admissible : TypeAdmissible context functionType) :
    ExpressionHasType source context named.value.node.id functionType := by
  have valid : SourceSemantics.DeclarationInstantiation.Admissible context named.instantiation := by
    rw [named.exact]
    refine .intro signature member rfl ?_ ?_ ?_ ?_ rfl rfl
    · simpa only [named.scheme] using ParameterSubstitution.exact_empty
    · intro parameter replacement contained
      cases contained
    · simp [named.scheme, parameter_nil]
    · simp [named.scheme]
  have proves : RequirementSequenceProves context [] named.instantiation.predicates := by
    rw [named.exact]
    exact .nil
  have typeEq : named.instantiation.type = functionType := by rw [named.exact]
  have reference : ReferenceUseValid context (.declaration named.instantiation) functionType [] := by
    rw [← typeEq]
    exact .declaration valid proves
  exact named.value.ordinary admissible (named.form ▸ ExpressionFormHasRawType.reference reference)

/-- The validity of a named value's instantiation at any context whose signatures have its declaration. -/
theorem NamedValue.valid {source : TypedSource} {signature : ProgramFunctionSignature}
    (named : NamedValue source signature) {context : SourceSemantics.Context}
    (member : signature ∈ context.signatures.functions) :
    SourceSemantics.DeclarationInstantiation.Valid context named.instantiation := by
  rw [named.exact]
  refine .intro signature member rfl ?_ ?_ ?_ ?_ rfl rfl
  · simpa only [named.scheme] using SourceSemantics.ParameterSubstitution.exact_empty
  · intro name value found
    cases found
  · simp [named.scheme, parameter_nil]
  · simp [named.scheme]

def observeNamedValue (source : TypedSource) (signature : ProgramFunctionSignature) (node : ExpressionNode) :
    IO (NamedValue source signature) := do
  let value ← Tests.SourceCoreOperatorCalls.observeNode source node functionType
  let .reference name (.declaration instantiation) := value.node.form
    | throw (IO.userError "named value form")
  let ⟨form⟩ ← observed (value.node.form = .reference name (.declaration instantiation)) "named value reference"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[], [], functionType⟩) "named value signature"
  let ⟨exact⟩ ← observed (instantiation =
    ⟨signature.id, [], functionType, [], signature.parameterComptime, signature.returnComptime⟩)
    "named value instantiation"
  return {value, name, instantiation, form, scheme, exact}

/-- An indirect call of a callee of type `function(word, word) returns (word)` with two arguments, without
coercions. -/
structure PairCall (source : TypedSource) (callee left right : ExpressionId) extends TypedNode source .word where
  metadata : IndirectCallResolution
  form : node.form = .call callee [left, right] (.indirect metadata)
  application : metadata = ⟨2, .product .word .word, .product .word .word, []⟩

theorem PairCall.typed {source : TypedSource} {callee left right : ExpressionId}
    (call : PairCall source callee left right) {context : SourceSemantics.Context}
    (word : TypeAdmissible context .word)
    (calleeTyped : ExpressionHasType source context callee adderType)
    (leftTyped : ExpressionHasType source context left .word)
    (rightTyped : ExpressionHasType source context right .word) :
    ExpressionHasType source context call.node.id .word := by
  have application : IndirectApplicationValid context call.metadata [.word, .word] (.product .word .word) := by
    rw [call.application]
    exact .intro rfl rfl rfl (.nil _)
  have typed : ExpressionHasType source context call.node.id call.node.type := by
    refine .intro (lookupExpression?_sound call.found)
      (call.form ▸ ExpressionFormHasRawType.indirectCall calleeTyped (.cons leftTyped (.cons rightTyped (.nil _)))
        application)
      call.raw word (call.type.symm ▸ word) ?_
    rw [call.requirements, call.coercions, call.type, call.application]
    exact .indirectCall (by intro id member; cases member) (.nil _) rfl
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.node.id type) call.type) typed

def observePairCall (source : TypedSource) (callee left right : ExpressionId) (node : ExpressionNode) :
    IO (PairCall source callee left right) := do
  let typed ← Tests.SourceCoreOperatorCalls.observeNode source node .word
  let .call _ _ (.indirect metadata) := typed.node.form | throw (IO.userError "pair call indirect")
  let ⟨form⟩ ← observed (typed.node.form = .call callee [left, right] (.indirect metadata)) "pair call form"
  let ⟨application⟩ ← observed (metadata = ⟨2, .product .word .word, .product .word .word, []⟩)
    "pair call metadata"
  return { toTypedNode := typed, metadata, form, application }

/-- The nodes of `viaLocal`'s body: the declaration of its local `f` from the named value of `identity`, and
the return of `f(value)`, the indirect call of a read of `f` with a read of the parameter, found by following
the statement graph. -/
structure ViaLocalParts (source : TypedSource) (identity : ProgramFunctionSignature) where
  binder : TypedBinder
  callable : TypedBinder
  named : NamedValue source identity
  calleeRead : Tests.SourceCoreNamedBranch.Read source callable functionType
  argumentRead : Tests.SourceCoreNamedBranch.Read source binder .word
  call : Tests.SourceCoreOperatorCalls.Call source calleeRead.node.id argumentRead.node.id
  declared : StatementNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement declared.id, .statement returned.id]
  declaredFound : source.lookupStatement? declared.id = some declared
  declaredForm : declared.form = .letDecl callable (some named.value.node.id)
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some call.node.id)

def observeViaLocalParts (source : TypedSource) (identity : ProgramFunctionSignature) :
    IO (ViaLocalParts source identity) := do
  let [binder] := source.inputs | throw (IO.userError "viaLocal input")
  let [.statement declaredId, .statement returnedId] := source.roots | throw (IO.userError "viaLocal roots")
  let some declared := source.lookupStatement? declaredId | throw (IO.userError "viaLocal let")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "viaLocal return")
  let .letDecl callable (some valueId) := declared.form | throw (IO.userError "viaLocal let form")
  let .returnStmt (some callId) := returned.form | throw (IO.userError "viaLocal return form")
  let some valueNode := source.lookupExpression? valueId | throw (IO.userError "viaLocal named value")
  let some callNode := source.lookupExpression? callId | throw (IO.userError "viaLocal call")
  let .call calleeId [argumentId] _ := callNode.form | throw (IO.userError "viaLocal call form")
  let some calleeNode := source.lookupExpression? calleeId | throw (IO.userError "viaLocal callee")
  let some argumentNode := source.lookupExpression? argumentId | throw (IO.userError "viaLocal argument")
  let named ← observeNamedValue source identity valueNode
  let calleeRead ← Tests.SourceCoreNamedBranch.observeRead source callable calleeNode functionType
  let argumentRead ← Tests.SourceCoreNamedBranch.observeRead source binder argumentNode .word
  let call ← Tests.SourceCoreOperatorCalls.observeCall source calleeRead.node.id argumentRead.node.id callNode
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "viaLocal inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement declared.id, .statement returned.id]) "viaLocal roots shape"
  let ⟨declaredFound⟩ ← observed (source.lookupStatement? declared.id = some declared) "viaLocal declaredFound"
  let ⟨declaredForm⟩ ← observed (declared.form = .letDecl callable (some named.value.node.id))
    "viaLocal declaredForm"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "viaLocal returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some call.node.id)) "viaLocal returnedForm"
  return ⟨binder, callable, named, calleeRead, argumentRead, call, declared, returned, inputs, roots, declaredFound,
    declaredForm, returnedFound, returnedForm⟩

/-- `viaLocal`'s body: `let f: function(word) returns (word) = identity` and the return of `f(value)`. -/
structure ViaLocalShape (function : CheckedFunction) (signature identity : ProgramFunctionSignature) where
  parts : ViaLocalParts function.typedBody identity
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderRequirements : parts.binder.schemeRequirements = []
  callableScheme : parts.callable.scheme = .mono functionType
  callableRequirements : parts.callable.schemeRequirements = []
  callableOwner : parts.callable.id.owner = function.typedBody.owner
  callableDistinct : parts.callable.id ≠ parts.binder.id
  declaredType : parts.declared.type = .unit
  returnedType : parts.returned.type = .word

theorem ViaLocalShape.statementTyping {function : CheckedFunction} {signature identity : ProgramFunctionSignature}
    (shape : ViaLocalShape function signature identity) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.declared.id, shape.parts.returned.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton facts), rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by
      rw [head.context_fields.1]
      rfl
    have callableType : TypeAdmissible lexical functionType := ⟨binders, .function (.builtin .word) (.builtin .word)⟩
    let locals := lexical.withLocal shape.parts.callable.id shape.parts.callable.scheme
      shape.parts.callable.schemeRequirements
    have callableExtended : BinderExtends function.typedBody.owner lexical shape.parts.callable locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.callableOwner
          scheme := shape.callableScheme.symm ▸ SchemeWellFormed.monoAdmissible callableType
          quantified_fresh := by rw [shape.callableScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.callableRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.callableDistinct]
    have namedTyped := shape.parts.named.typed (fields ▸ identityMember) callableType
    have declaredTyped : StatementHasType function.typedBody ⟨.word, 0⟩ lexical shape.parts.declared.id locals
        ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.parts.declaredFound)
        shape.parts.declaredForm
      · simpa only [shape.callableScheme, TypeSystem.Scheme.mono] using namedTyped
      · rw [shape.callableScheme]; rfl
      · rw [shape.callableScheme]; rfl
      · exact callableExtended
      · exact shape.declaredType
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have localCallable : TypeAdmissible locals functionType := ⟨binders, .function (.builtin .word) (.builtin .word)⟩
    have calleeTyped := shape.parts.calleeRead.typed shape.callableScheme shape.callableRequirements localCallable
      callableExtended.local_self callableExtended.local_scheme_requirements_self
    have parameterLookup : locals.LocalLookup shape.parts.binder.id shape.parts.binder.scheme :=
      .tail shape.callableDistinct head.local_self
    have parameterRequirements :
        locals.LocalSchemeRequirementsLookup shape.parts.binder.id shape.parts.binder.schemeRequirements :=
      .tail shape.callableDistinct head.local_scheme_requirements_self
    have argumentTyped := shape.parts.argumentRead.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have callTyped := shape.parts.call.typed localWord calleeTyped argumentTyped
    exact ⟨_, .cons declaredTyped (.singleton (.returnValue (lookupStatement?_sound shape.parts.returnedFound)
      shape.parts.returnedForm callTyped shape.returnedType))⟩

def observeViaLocal (function : CheckedFunction) (signature identity : ProgramFunctionSignature) :
    IO (ViaLocalShape function signature identity) := do
  let parts ← observeViaLocalParts function.typedBody identity
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "viaLocal parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "viaLocal inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "viaLocal returns"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "viaLocal binderRequirements"
  let ⟨callableScheme⟩ ← observed (parts.callable.scheme = .mono functionType) "viaLocal callableScheme"
  let ⟨callableRequirements⟩ ← observed (parts.callable.schemeRequirements = []) "viaLocal callableRequirements"
  let ⟨callableOwner⟩ ← observed (parts.callable.id.owner = function.typedBody.owner) "viaLocal callableOwner"
  let ⟨callableDistinct⟩ ← observed (parts.callable.id ≠ parts.binder.id) "viaLocal callableDistinct"
  let ⟨declaredType⟩ ← observed (parts.declared.type = .unit) "viaLocal declaredType"
  let ⟨returnedType⟩ ← observed (parts.returned.type = .word) "viaLocal returnedType"
  return ⟨parts, parameters, inputTypes, returns, binderRequirements, callableScheme, callableRequirements,
    callableOwner, callableDistinct, declaredType, returnedType⟩

/-- The nodes of `viaBuiltin`'s body: the declaration of its local `plus` from the reference to the opcode
`add`, and the return of `plus(value, value)`, the indirect call of a read of `plus` with two reads of the
parameter, found by following the statement graph. -/
structure ViaBuiltinParts (source : TypedSource) where
  binder : TypedBinder
  callable : TypedBinder
  builtin : TypedNode source adderType
  name : String
  builtinForm : builtin.node.form = .reference name (.builtinFunction (.wordOpcode .add))
  calleeRead : Tests.SourceCoreNamedBranch.Read source callable adderType
  leftRead : Tests.SourceCoreNamedBranch.Read source binder .word
  rightRead : Tests.SourceCoreNamedBranch.Read source binder .word
  call : PairCall source calleeRead.node.id leftRead.node.id rightRead.node.id
  declared : StatementNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  roots : source.roots = [.statement declared.id, .statement returned.id]
  declaredFound : source.lookupStatement? declared.id = some declared
  declaredForm : declared.form = .letDecl callable (some builtin.node.id)
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some call.node.id)

def observeViaBuiltinParts (source : TypedSource) : IO (ViaBuiltinParts source) := do
  let [binder] := source.inputs | throw (IO.userError "viaBuiltin input")
  let [.statement declaredId, .statement returnedId] := source.roots | throw (IO.userError "viaBuiltin roots")
  let some declared := source.lookupStatement? declaredId | throw (IO.userError "viaBuiltin let")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "viaBuiltin return")
  let .letDecl callable (some builtinId) := declared.form | throw (IO.userError "viaBuiltin let form")
  let .returnStmt (some callId) := returned.form | throw (IO.userError "viaBuiltin return form")
  let some builtinNode := source.lookupExpression? builtinId | throw (IO.userError "viaBuiltin opcode")
  let some callNode := source.lookupExpression? callId | throw (IO.userError "viaBuiltin call")
  let .call calleeId [leftId, rightId] _ := callNode.form | throw (IO.userError "viaBuiltin call form")
  let some calleeNode := source.lookupExpression? calleeId | throw (IO.userError "viaBuiltin callee")
  let some leftNode := source.lookupExpression? leftId | throw (IO.userError "viaBuiltin left")
  let some rightNode := source.lookupExpression? rightId | throw (IO.userError "viaBuiltin right")
  let builtin ← Tests.SourceCoreOperatorCalls.observeNode source builtinNode adderType
  let .reference name (.builtinFunction _) := builtin.node.form | throw (IO.userError "viaBuiltin opcode form")
  let ⟨builtinForm⟩ ← observed (builtin.node.form = .reference name (.builtinFunction (.wordOpcode .add)))
    "viaBuiltin opcode reference"
  let calleeRead ← Tests.SourceCoreNamedBranch.observeRead source callable calleeNode adderType
  let leftRead ← Tests.SourceCoreNamedBranch.observeRead source binder leftNode .word
  let rightRead ← Tests.SourceCoreNamedBranch.observeRead source binder rightNode .word
  let call ← observePairCall source calleeRead.node.id leftRead.node.id rightRead.node.id callNode
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "viaBuiltin inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement declared.id, .statement returned.id])
    "viaBuiltin roots shape"
  let ⟨declaredFound⟩ ← observed (source.lookupStatement? declared.id = some declared) "viaBuiltin declaredFound"
  let ⟨declaredForm⟩ ← observed (declared.form = .letDecl callable (some builtin.node.id)) "viaBuiltin declaredForm"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "viaBuiltin returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some call.node.id)) "viaBuiltin returnedForm"
  return ⟨binder, callable, builtin, name, builtinForm, calleeRead, leftRead, rightRead, call, declared, returned,
    inputs, roots, declaredFound, declaredForm, returnedFound, returnedForm⟩

/-- `viaBuiltin`'s body: `let plus: function(word, word) returns (word) = add` and the return of
`plus(value, value)`. -/
structure ViaBuiltinShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  parts : ViaBuiltinParts function.typedBody
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  binderRequirements : parts.binder.schemeRequirements = []
  callableScheme : parts.callable.scheme = .mono adderType
  callableRequirements : parts.callable.schemeRequirements = []
  callableOwner : parts.callable.id.owner = function.typedBody.owner
  callableDistinct : parts.callable.id ≠ parts.binder.id
  declaredType : parts.declared.type = .unit
  returnedType : parts.returned.type = .word

theorem ViaBuiltinShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : ViaBuiltinShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.parts.declared.id, shape.parts.returned.id] :=
    statementRoots_injective (roots.symm.trans shape.parts.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton facts), rfl, ?_⟩
  intro lexical extension
  rw [shape.parts.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have adder : TypeAdmissible lexical adderType :=
      ⟨binders, .function (.product (.builtin .word) (.builtin .word)) (.builtin .word)⟩
    let locals := lexical.withLocal shape.parts.callable.id shape.parts.callable.scheme
      shape.parts.callable.schemeRequirements
    have callableExtended : BinderExtends function.typedBody.owner lexical shape.parts.callable locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.callableOwner
          scheme := shape.callableScheme.symm ▸ SchemeWellFormed.monoAdmissible adder
          quantified_fresh := by rw [shape.callableScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.callableRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.callableDistinct]
    have reference : ExpressionFormHasRawType function.typedBody lexical shape.parts.builtin.node.form adderType
        (.ordinary []) := by
      rw [shape.parts.builtinForm, ← adder_type]
      exact .reference (.builtinFunction (.wordOpcode .add))
    have builtinTyped := shape.parts.builtin.ordinary adder reference
    have declaredTyped : StatementHasType function.typedBody ⟨.word, 0⟩ lexical shape.parts.declared.id locals
        ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.parts.declaredFound)
        shape.parts.declaredForm
      · simpa only [shape.callableScheme, TypeSystem.Scheme.mono] using builtinTyped
      · rw [shape.callableScheme]; rfl
      · rw [shape.callableScheme]; rfl
      · exact callableExtended
      · exact shape.declaredType
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have localAdder : TypeAdmissible locals adderType :=
      ⟨binders, .function (.product (.builtin .word) (.builtin .word)) (.builtin .word)⟩
    have calleeTyped := shape.parts.calleeRead.typed shape.callableScheme shape.callableRequirements localAdder
      callableExtended.local_self callableExtended.local_scheme_requirements_self
    have parameterLookup : locals.LocalLookup shape.parts.binder.id shape.parts.binder.scheme :=
      .tail shape.callableDistinct head.local_self
    have parameterRequirements :
        locals.LocalSchemeRequirementsLookup shape.parts.binder.id shape.parts.binder.schemeRequirements :=
      .tail shape.callableDistinct head.local_scheme_requirements_self
    have leftTyped := shape.parts.leftRead.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have rightTyped := shape.parts.rightRead.typed scheme shape.binderRequirements localWord parameterLookup
      parameterRequirements
    have callTyped := shape.parts.call.typed localWord calleeTyped leftTyped rightTyped
    exact ⟨_, .cons declaredTyped (.singleton (.returnValue (lookupStatement?_sound shape.parts.returnedFound)
      shape.parts.returnedForm callTyped shape.returnedType))⟩

def observeViaBuiltin (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (ViaBuiltinShape function signature) := do
  let parts ← observeViaBuiltinParts function.typedBody
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "viaBuiltin parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "viaBuiltin inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "viaBuiltin returns"
  let ⟨binderRequirements⟩ ← observed (parts.binder.schemeRequirements = []) "viaBuiltin binderRequirements"
  let ⟨callableScheme⟩ ← observed (parts.callable.scheme = .mono adderType) "viaBuiltin callableScheme"
  let ⟨callableRequirements⟩ ← observed (parts.callable.schemeRequirements = []) "viaBuiltin callableRequirements"
  let ⟨callableOwner⟩ ← observed (parts.callable.id.owner = function.typedBody.owner) "viaBuiltin callableOwner"
  let ⟨callableDistinct⟩ ← observed (parts.callable.id ≠ parts.binder.id) "viaBuiltin callableDistinct"
  let ⟨declaredType⟩ ← observed (parts.declared.type = .unit) "viaBuiltin declaredType"
  let ⟨returnedType⟩ ← observed (parts.returned.type = .word) "viaBuiltin returnedType"
  return ⟨parts, parameters, inputTypes, returns, binderRequirements, callableScheme, callableRequirements,
    callableOwner, callableDistinct, declaredType, returnedType⟩

/-- Two members of a list of signatures whose ids are distinct are equal when their ids are. -/
private theorem signature_of_id {signatures : List ProgramFunctionSignature}
    (distinct : (signatures.map (·.id)).Nodup) {first second : ProgramFunctionSignature}
    (firstMember : first ∈ signatures) (secondMember : second ∈ signatures) (same : first.id = second.id) :
    first = second := by
  induction signatures with
  | nil => cases firstMember
  | cons head rest ih =>
    obtain ⟨fresh, restDistinct⟩ := List.nodup_cons.mp distinct
    cases firstMember with
    | head =>
      cases secondMember with
      | head => rfl
      | tail _ secondRest => exact absurd (List.mem_map.mpr ⟨second, secondRest, same.symm⟩) fresh
    | tail _ firstRest =>
      cases secondMember with
      | head => exact absurd (List.mem_map.mpr ⟨first, firstRest, same⟩) fresh
      | tail _ secondRest => exact ih restDistinct firstRest secondRest

/-- The declarative typing of the complete checked program. -/
def observeWellFormed {program : CheckedProgram}
    (checked : checkProgram workspace options.checkingFuel = .ok program) :
    IO (PLift (ProgramWellFormed (Program.ofChecked program))) := do
  match functions : program.functions, signatures : program.signatures.functions with
  | [identityFunction, viaLocalFunction, viaBuiltinFunction],
    [identitySignature, viaLocalSignature, viaBuiltinSignature] =>
    let identityShape ← Tests.SourceCoreOperatorCalls.observeIdentity identityFunction identitySignature
    let viaLocalShape ← observeViaLocal viaLocalFunction viaLocalSignature identitySignature
    let viaBuiltinShape ← observeViaBuiltin viaBuiltinFunction viaBuiltinSignature
    let ⟨methods⟩ ← observed (program.methods = []) "indirect methods"
    let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id)
      "indirect identityDeclaration"
    let ⟨viaLocalDeclaration⟩ ← observed (viaLocalFunction.declaration = viaLocalSignature.id)
      "indirect viaLocalDeclaration"
    let ⟨viaBuiltinDeclaration⟩ ← observed (viaBuiltinFunction.declaration = viaBuiltinSignature.id)
      "indirect viaBuiltinDeclaration"
    let ⟨distinct⟩ ← observed ((program.signatures.functions.map (·.id)).Nodup) "indirect distinct signatures"
    let deep : CheckedProgramBodiesHaveStatementTyping program options.checkingFuel := {
      functions := by
        intro actual member candidate candidateMember accepted
        have declared := checkFunctionBody_success_declaration accepted
        have selects : ∀ {signature}, signature ∈ program.signatures.functions →
            actual.declaration = signature.id → candidate = signature := fun signatureMember same =>
          signature_of_id distinct candidateMember signatureMember (declared.symm.trans same)
        simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · obtain rfl := selects (by simp [signatures]) identityDeclaration
          exact identityShape.statementTyping program.signatures
        · obtain rfl := selects (by simp [signatures]) viaLocalDeclaration
          exact viaLocalShape.statementTyping program.signatures (by simp [signatures])
        · obtain rfl := selects (by simp [signatures]) viaBuiltinDeclaration
          exact viaBuiltinShape.statementTyping program.signatures
      methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
    return ⟨programWellFormed_ofCheckProgram_statements checked deep⟩
  | _, _ => throw (IO.userError "indirect declaration count")

end Tests.SourceCoreAcceptedIndirect
end

section
/-! The cache rows of `viaLocal` and `viaBuiltin` and their original Source executions: `viaLocal`'s local
`f` holds the named function value of `identity`, whose application by the indirect call is a given body
invocation, and `viaBuiltin`'s local `plus` holds the builtin closure of the opcode `add`, which the indirect
call applies to the packed pair of its parameter's word, returning the word's sum with itself. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreAcceptedIndirect
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceCoreAcceptedFixture (observed CompiledFixture)
open Tests.SourceCoreAcceptedOneCall (wordHeap wordEnvironment local_value)
open Tests.SourceCoreOperatorCalls (functionType)

/-- A heap with one more initialized cell of a function type. -/
def functionHeap (before : Dynamic.Heap) (type : TypeSystem.Ty) (value : Dynamic.Value) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := type, value := some value}]⟩

/-- `viaLocal`'s cache row: the nodes of its body, its `word` parameter and its local `f`, whose initializer
refers to `identity` at the instantiation `target`. -/
structure ViaLocalBody (fixture : CompiledFixture workspace options) (target : DeclarationInstantiation)
    (source : TypedSource) where
  identity : ProgramFunctionSignature
  member : identity ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  parts : ViaLocalParts source identity
  binderScheme : parts.binder.scheme = .mono .word
  callableScheme : parts.callable.scheme = .mono functionType
  callableDistinct : parts.callable.id ≠ parts.binder.id
  selects : parts.named.instantiation = target

private def identitySignature (fixture : CompiledFixture workspace options) :
    IO {identity : ProgramFunctionSignature //
      identity ∈ fixture.recipe.compiled.sourceProgram.signatures.functions} := do
  match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
      (fun signature => signature.name == "identity") with
  | none => throw (IO.userError "indirect callee signature")
  | some identity => return ⟨identity, List.mem_of_find?_eq_some found⟩

def observeViaLocalBody (fixture : CompiledFixture workspace options) (target : DeclarationInstantiation)
    (source : TypedSource) : IO (ViaLocalBody fixture target source) := do
  let ⟨identity, member⟩ ← identitySignature fixture
  let parts ← observeViaLocalParts source identity
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "viaLocal row binderScheme"
  let ⟨callableScheme⟩ ← observed (parts.callable.scheme = .mono functionType) "viaLocal row callableScheme"
  let ⟨callableDistinct⟩ ← observed (parts.callable.id ≠ parts.binder.id) "viaLocal row callableDistinct"
  let ⟨selects⟩ ← observed (parts.named.instantiation = target) "viaLocal row target"
  return ⟨identity, member, parts, binderScheme, callableScheme, callableDistinct, selects⟩

/-- `viaBuiltin`'s cache row: the nodes of its body, its `word` parameter and its local `plus`. -/
structure ViaBuiltinBody (source : TypedSource) where
  parts : ViaBuiltinParts source
  binderScheme : parts.binder.scheme = .mono .word
  callableScheme : parts.callable.scheme = .mono adderType
  callableDistinct : parts.callable.id ≠ parts.binder.id

def observeViaBuiltinBody (source : TypedSource) : IO (ViaBuiltinBody source) := do
  let parts ← observeViaBuiltinParts source
  let ⟨binderScheme⟩ ← observed (parts.binder.scheme = .mono .word) "viaBuiltin row binderScheme"
  let ⟨callableScheme⟩ ← observed (parts.callable.scheme = .mono adderType) "viaBuiltin row callableScheme"
  let ⟨callableDistinct⟩ ← observed (parts.callable.id ≠ parts.binder.id) "viaBuiltin row callableDistinct"
  return ⟨parts, binderScheme, callableScheme, callableDistinct⟩

/-- `viaLocal`'s body returns its parameter's word: its local `f` holds the named function value of
`identity`, and the indirect call applies it to the parameter's word, given the value's validity and its global
application. The local's context is a binder extension of the body's. -/
theorem ViaLocalBody.trace {fixture : CompiledFixture workspace options} {target : DeclarationInstantiation}
    {source : TypedSource} (body : ViaLocalBody fixture target source) {program : SourceSemantics.Program}
    {context localContext : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (extension : BinderExtends source.owner context body.parts.callable localContext)
    (word : Core.Word)
    (valid : SourceSemantics.DeclarationInstantiation.Valid context body.parts.named.instantiation)
    {after : Dynamic.Heap}
    (applies : Dynamic.CallableApplies program localContext evidence []
      (functionHeap (wordHeap before word) functionType (.global ⟨body.parts.named.instantiation, []⟩))
      (.global ⟨body.parts.named.instantiation, []⟩) [.word word] (.word word) after) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.declared.id, body.parts.returned.id] localContext (.returned (.word word))
      after := by
  let value : Dynamic.Value := .global ⟨body.parts.named.instantiation, []⟩
  let environment : Dynamic.Environment :=
    (body.parts.callable.id, ⟨(wordHeap before word).cells.length⟩) :: wordEnvironment body.parts.binder before
  have parameterAllocation : Dynamic.Heap.Allocates before .word (some (.word word)) ⟨before.cells.length⟩
      (wordHeap before word) := .append
  have allocation : Dynamic.Heap.Allocates (wordHeap before word) functionType (some value)
      ⟨(wordHeap before word).cells.length⟩ (functionHeap (wordHeap before word) functionType value) := .append
  have initial : Dynamic.ExpressionEvaluates program context evidence source
      (wordEnvironment body.parts.binder before) (wordHeap before word) body.parts.named.value.node.id value
      (wordHeap before word) := by
    have predicates : body.parts.named.instantiation.predicates = [] := by rw [body.parts.named.exact]
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.named.value.found)
    · rw [body.parts.named.form, body.parts.named.value.requirements, body.parts.named.value.coercions]
      exact .declaration (owned := []) rfl valid (by rw [predicates]; exact .nil)
    · rw [body.parts.named.value.coercions]
      exact .nil
  have declared : Dynamic.StatementExecutes program context evidence source
      (wordEnvironment body.parts.binder before) (wordHeap before word) body.parts.declared.id localContext
      (.fallthrough environment) (functionHeap (wordHeap before word) functionType value) :=
    .letInitialized (lookupStatement?_sound body.parts.declaredFound) body.parts.declaredForm initial
      (by rw [body.callableScheme]; rfl) extension (by rw [body.callableScheme]; exact allocation)
  have parameterLookup : Dynamic.Environment.LooksUp environment body.parts.binder.id ⟨before.cells.length⟩ :=
    .tail body.callableDistinct .head
  have called : Dynamic.ExpressionEvaluates program localContext evidence source environment
      (functionHeap (wordHeap before word) functionType value) body.parts.call.node.id (.word word) after := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.call.found)
    · rw [body.parts.call.form, body.parts.call.requirements, body.parts.call.coercions,
        body.parts.call.application]
      exact .indirectCall rfl (local_value body.parts.calleeRead evidence .head allocation.reads_new)
        (.cons (local_value body.parts.argumentRead evidence parameterLookup
          (allocation.preserves_read parameterAllocation.reads_new)) .nil)
        (.singleton _) .nil (.singleton _) rfl rfl applies
    · rw [body.parts.call.coercions]
      exact .nil
  exact .cons declared (.singleton (lookupStatement?_sound body.parts.returnedFound)
    (by rw [body.parts.returnedForm]; intro id impossible; cases impossible)
    (.returnValue (lookupStatement?_sound body.parts.returnedFound) body.parts.returnedForm called))

/-- `viaBuiltin`'s body returns its parameter's word added to itself: its local `plus` holds the builtin
closure of the opcode `add`, and the indirect call applies it to the packed pair of the parameter's word. The
local's context is a binder extension of the body's. -/
theorem ViaBuiltinBody.trace {source : TypedSource} (body : ViaBuiltinBody source)
    {program : SourceSemantics.Program} {context localContext : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (extension : BinderExtends source.owner context body.parts.callable localContext) (word : Core.Word) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.parts.binder before)
      (wordHeap before word) [body.parts.declared.id, body.parts.returned.id] localContext
      (.returned (.word (word.add word)))
      (functionHeap (wordHeap before word) adderType (.builtin ⟨.wordOpcode .add⟩)) := by
  let value : Dynamic.Value := .builtin ⟨.wordOpcode .add⟩
  let environment : Dynamic.Environment :=
    (body.parts.callable.id, ⟨(wordHeap before word).cells.length⟩) :: wordEnvironment body.parts.binder before
  have parameterAllocation : Dynamic.Heap.Allocates before .word (some (.word word)) ⟨before.cells.length⟩
      (wordHeap before word) := .append
  have allocation : Dynamic.Heap.Allocates (wordHeap before word) adderType (some value)
      ⟨(wordHeap before word).cells.length⟩ (functionHeap (wordHeap before word) adderType value) := .append
  have initial : Dynamic.ExpressionEvaluates program context evidence source
      (wordEnvironment body.parts.binder before) (wordHeap before word) body.parts.builtin.node.id value
      (wordHeap before word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.builtin.found)
    · rw [body.parts.builtinForm, body.parts.builtin.requirements, body.parts.builtin.coercions]
      exact .builtinFunction rfl
    · rw [body.parts.builtin.coercions]
      exact .nil
  have declared : Dynamic.StatementExecutes program context evidence source
      (wordEnvironment body.parts.binder before) (wordHeap before word) body.parts.declared.id localContext
      (.fallthrough environment) (functionHeap (wordHeap before word) adderType value) :=
    .letInitialized (lookupStatement?_sound body.parts.declaredFound) body.parts.declaredForm initial
      (by rw [body.callableScheme]; rfl) extension (by rw [body.callableScheme]; exact allocation)
  have parameterLookup : Dynamic.Environment.LooksUp environment body.parts.binder.id ⟨before.cells.length⟩ :=
    .tail body.callableDistinct .head
  have parameterRead := allocation.preserves_read parameterAllocation.reads_new
  have called : Dynamic.ExpressionEvaluates program localContext evidence source environment
      (functionHeap (wordHeap before word) adderType value) body.parts.call.node.id (.word (word.add word))
      (functionHeap (wordHeap before word) adderType value) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.parts.call.found)
    · rw [body.parts.call.form, body.parts.call.requirements, body.parts.call.coercions,
        body.parts.call.application]
      exact .indirectCall (invocationEvidence := []) rfl
        (local_value body.parts.calleeRead evidence .head allocation.reads_new)
        (.cons (local_value body.parts.leftRead evidence parameterLookup parameterRead)
          (.cons (local_value body.parts.rightRead evidence parameterLookup parameterRead) .nil))
        (.cons (.singleton _)) .nil (.cons (.singleton _)) rfl rfl (.builtin (.wordOpcode rfl))
    · rw [body.parts.call.coercions]
      exact .nil
  exact .cons declared (.singleton (lookupStatement?_sound body.parts.returnedFound)
    (by rw [body.parts.returnedForm]; intro id impossible; cases impossible)
    (.returnValue (lookupStatement?_sound body.parts.returnedFound) body.parts.returnedForm called))

end Tests.SourceCoreAcceptedIndirect
end

section
/-! The accepted-body public theorems at the call root, for the family of the planned instantiations.
Runtime checks place every expression node of the three rows among its nested sites, given that it admits
every planned instantiation, and each statement list in the supported shape; the complete inventory turns them
into the rows of a family, and gives the callees' static receipts, since every planned instantiation is the
retained instantiation of a row the plan records. The original Source executions of `viaLocal` and
`viaBuiltin`, which end in their local's context, are lifted through the checked shapes, and with the existing
start receipts the call root's theorems apply at the first public call of each in both directions
(`accepted_call`); the call root's reflection needs no Source execution (`accepted_reflection`). The fault
lifting does not cover a family with an indirect call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreAcceptedIndirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreAcceptedFixture
open Tests.SourceCoreAcceptedOneCall (wordHeap wordEnvironment IdentityBody observeIdentityBody)
open Tests.SourceCoreOperatorCalls (functionType)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : CompiledFixture workspace options} {whole : WholeInventory fixture} {row : Row fixture}

private theorem mono_signatures {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List TypeSystem.Ty}
    (extension : MonoBindersExtend owner context binders types final) : final.signatures = context.signatures := by
  induction extension with
  | nil => rfl
  | cons _ head _ ih => exact ih.trans head.context_fields.1

/-- A header's lexical context has the program's signatures. -/
theorem header_signatures
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)) :
    header.context.signatures = fixture.recipe.compiled.sourceProgram.signatures := by
  rw [mono_signatures header.extended, header.frame.context]
  cases header.frame.instantiated with
  | intro _ _ _ _ _ _ _ contextEq =>
    rw [contextEq]
    rfl

/-- A row whose only parameter is a `word` has the header parameter types `[.word]`, and its header allocates
that parameter in the next cell. -/
theorem word_parameter (selected : SelectedInventory whole row) {binder : TypedBinder}
    (inputs : row.original.function.typedBody.inputs = [binder]) (scheme : binder.scheme = .mono .word)
    (before : Dynamic.Heap) (word : Core.Word) :
    selected.packet.header.types = [.word] ∧
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.word word]
      (wordEnvironment binder before) (wordHeap before word) := by
  have sourceInputs : selected.packet.header.function.source.inputs = [binder] := by
    rw [selected.source_eq]
    exact inputs
  have parameters : selected.packet.header.function.parameters = [binder] :=
    selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans sourceInputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  have allocation : Dynamic.Heap.Allocates before .word (some (.word word)) ⟨before.cells.length⟩
      (wordHeap before word) := .append
  refine ⟨?_, ?_⟩
  · simpa only [parameters, List.map_cons, List.map_nil, scheme, TypeSystem.Scheme.mono] using types.symm
  · rw [parameters]
    exact .cons (by simpa only [scheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)

/-- `identity`'s global application at the empty dictionary, at any heap: its header's Source body runs on its
parameter in the next cell and returns it. -/
theorem identity_applies {identity : Row fixture} (identitySelected : SelectedInventory whole identity)
    {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (identityBody : IdentityBody identity.original.function.typedBody) {instantiation : DeclarationInstantiation}
    (selects : instantiation = CallableNamedCanonicalOrder.retainedInstantiation identity.original)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) :
    Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram) context evidence [] before
      (.global ⟨instantiation, []⟩) [.word word] (.word word) (wordHeap before word) := by
  have calleeSource : identitySelected.packet.header.sourceBody.source = identity.original.function.typedBody :=
    identitySelected.packet.header.frame.source.symm.trans identitySelected.source_eq
  have covers : Dynamic.EvidenceEnvironment.Covers identitySelected.packet.header.sourceBody.context [] := by
    have frameCovers := identitySelected.packet.header.frame.covers
    rw [calls.header_evidence identitySelected.packet] at frameCovers
    exact frameCovers
  have extended := identitySelected.packet.header.extended
  rw [identitySelected.packet.header.frame.parameters, identitySelected.packet.header.frame.source,
    identitySelected.packet.header.frame.context] at extended
  have rootsEq : Dynamic.StatementRoots identitySelected.packet.header.sourceBody.source.roots
      [identityBody.statement.id] := by
    rw [calleeSource, identityBody.roots]
    exact .cons .nil
  have allocation : Dynamic.Heap.Allocates before .word (some (.word word)) ⟨before.cells.length⟩
      (wordHeap before word) := .append
  have allocated : Dynamic.BindersAllocate [] before identitySelected.packet.header.sourceBody.source.inputs
      [.word word] (wordEnvironment identityBody.binder before) (wordHeap before word) := by
    rw [calleeSource, identityBody.inputs]
    exact .cons (by simpa only [identityBody.binderScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have execute : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      identitySelected.packet.header.context [] identitySelected.packet.header.sourceBody.source
      (wordEnvironment identityBody.binder before) (wordHeap before word) [identityBody.statement.id]
      identitySelected.packet.header.context (.returned (.word word)) (wordHeap before word) := by
    rw [calleeSource]
    exact identityBody.trace [] before word
  have instantiates := identitySelected.packet.header.frame.instantiated
  rw [identitySelected.packet.aligned.metadata, identitySelected.original, ← selects] at instantiates
  exact .global instantiates rfl covers (.returned covers rootsEq extended allocated execute rfl)

/-- The statement roots of a header whose row's body is two statements. -/
private theorem two_body (selected : SelectedInventory whole row) {first second : StatementId}
    (roots : row.original.function.typedBody.roots = [.statement first, .statement second]) :
    selected.packet.header.function.body = [first, second] := by
  have headerRoots : selected.packet.header.function.source.roots = [first, second].map NodeId.statement := by
    rw [selected.source_eq]
    exact roots
  exact statementRoots_injective (selected.packet.header.agreement.roots.symm.trans headerRoots)

/-- The original Source execution of `viaLocal`'s body at its header returns its parameter's word: the
indirect call's global application runs `identity`'s body instance, its header's Source body, at the empty
dictionary. The local's binder extension comes from the header's typing certificate. -/
theorem viaLocal_source (selected : SelectedInventory whole row) {identity : Row fixture}
    (identitySelected : SelectedInventory whole identity) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (identityBody : IdentityBody identity.original.function.typedBody)
    (viaLocalBody : ViaLocalBody fixture (CallableNamedCanonicalOrder.retainedInstantiation identity.original)
      row.original.function.typedBody)
    (certified : SelectedCompilationNamedSourceTyping.Certified selected.packet.header) (word : Core.Word) :
    ∃ finalContext, Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment viaLocalBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      finalContext (.returned (.word word))
      (wordHeap (functionHeap (wordHeap ⟨[]⟩ word) functionType
        (.global ⟨viaLocalBody.parts.named.instantiation, []⟩)) word) := by
  have body := two_body selected viaLocalBody.parts.roots
  have unique : NodeOccurrencesUnique row.original.function.typedBody :=
    selected.source_eq ▸ selected.packet.header.unique
  have member : viaLocalBody.identity ∈ selected.packet.header.context.signatures.functions := by
    rw [header_signatures selected.packet.header]
    exact viaLocalBody.member
  obtain ⟨_final, _facts, typed, _completes⟩ := certified.statements
  rw [body, selected.source_eq] at typed
  cases typed with
  | cons head _ =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans viaLocalBody.parts.declaredFound)
    rw [viaLocalBody.parts.declaredForm] at formTyped
    cases formTyped with
    | letInitialized _ _ extension =>
      rw [body, selected.source_eq]
      exact ⟨_, viaLocalBody.trace selected.packet.header.function.evidence ⟨[]⟩ extension word
        (viaLocalBody.parts.named.valid member)
        (identity_applies identitySelected calls identityBody viaLocalBody.selects _ _ _ word)⟩
    | letInitializedGeneralized polymorphic =>
      rw [viaLocalBody.callableScheme] at polymorphic
      exact absurd rfl polymorphic

/-- The original Source execution of `viaBuiltin`'s body at its header returns its parameter's word added to
itself. The local's binder extension comes from the header's typing certificate. -/
theorem viaBuiltin_source (selected : SelectedInventory whole row)
    (viaBuiltinBody : ViaBuiltinBody row.original.function.typedBody)
    (certified : SelectedCompilationNamedSourceTyping.Certified selected.packet.header) (word : Core.Word) :
    ∃ finalContext, Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment viaBuiltinBody.parts.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      finalContext (.returned (.word (word.add word)))
      (functionHeap (wordHeap ⟨[]⟩ word) adderType (.builtin ⟨.wordOpcode .add⟩)) := by
  have body := two_body selected viaBuiltinBody.parts.roots
  have unique : NodeOccurrencesUnique row.original.function.typedBody :=
    selected.source_eq ▸ selected.packet.header.unique
  obtain ⟨_final, _facts, typed, _completes⟩ := certified.statements
  rw [body, selected.source_eq] at typed
  cases typed with
  | cons head _ =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj
      ((lookupStatement?_complete unique contains).symm.trans viaBuiltinBody.parts.declaredFound)
    rw [viaBuiltinBody.parts.declaredForm] at formTyped
    cases formTyped with
    | letInitialized _ _ extension =>
      rw [body, selected.source_eq]
      exact ⟨_, viaBuiltinBody.trace selected.packet.header.function.evidence ⟨[]⟩ extension word⟩
    | letInitializedGeneralized polymorphic =>
      rw [viaBuiltinBody.callableScheme] at polymorphic
      exact absurd rfl polymorphic

/-- The first public call of a row, with the conclusions of the call root's output theorem, its checkpoint
sufficiency theorem and its checkpoint reflection theorem. -/
structure AcceptedCall (selected : SelectedInventory whole row) (word : Word)
    (started : Started fixture row.original.key [.word word]) where
  start : SelectedCompilationPublicSessionInitial.Started whole.rows fixture.ready selected.packet.header started.call
  output : ∃ requiredExecution requiredOutput, ∀ executionFuel outputFuel
      (outcome : SourceCoreExecution.Outcome started.artifact),
    requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
    started.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
    ∃ (returned : SourceCoreExecution.Completion started.artifact)
      (actual : SourceCoreIndexedSession.Completion start.artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store),
      outcome = .succeeded returned ∧
      start.checkpoint.SucceededResultAt executionFuel outputFuel generation value finalStore actual ∧
      returned.IndexedAt actual
  native : ∃ (value : Value) (finalStore : Store) (required : Nat),
    ∀ fuel, required ≤ fuel → start.checkpoint.NativeDone fuel value finalStore
  reflects : ∀ fuel (value : Value) (finalStore : Store), start.checkpoint.NativeDone fuel value finalStore →
    ∃ (sidecar : SourceCoreStageContracts.Sidecar) (size : Nat) (environment : Dynamic.Environment)
      (bound : Dynamic.Heap) (finalContext : SourceSemantics.Context) (outcome : Staging.Recursive.BodyOutcome)
      (after : Dynamic.Heap),
      Dynamic.BindersAllocate [] ⟨[]⟩ selected.packet.header.function.parameters [.word word] environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked fixture.recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) size
        (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) selected.packet.header.context
        environment bound selected.packet.header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult selected.packet.header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome)

/-- Every premise is an original checked or static observation, a runtime check of the program's rows, an
actual public start, or the row's original Source execution after the allocation of its `word` parameter, in
any final context. The body's accepted-expression meaning comes from the family of the checked rows, and the
staged Source trace is lifted from the original execution through the checked shape, with the admitted
callees' static receipts from the inventory, given that every admitted instantiation is the retained
instantiation of a row the plan records. -/
theorem accepted_call (selected : SelectedInventory whole row) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (admitted : ∀ {instantiation}, called instantiation →
      ∃ original ∈ fixture.recipe.compiled.indexed.base.plan.specializations,
        instantiation = CallableNamedCanonicalOrder.retainedInstantiation original)
    (word : Word)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (started : Started fixture row.original.key [.word word])
    (callableProfile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {binder : TypedBinder} (inputs : row.original.function.typedBody.inputs = [binder])
    (scheme : binder.scheme = .mono .word) {finalContext : SourceSemantics.Context} {result : Dynamic.Value}
    {after : Dynamic.Heap}
    (sourceTrace : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      finalContext (.returned result) after) :
    Nonempty (AcceptedCall selected word started) := by
  obtain ⟨types, allocated⟩ := word_parameter selected inputs scheme ⟨[]⟩ word
  have support := SelectedCompilationNamedSupport.Support.of_program wellFormed
  obtain ⟨start⟩ := CellAwarePublicInitialSelectedStart.from_selected_call
    (rows := whole.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.accepted fixture.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member key => selected.root_selection member key)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.word word] selected.packet.header.types := by
    rw [types]
    exact .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word word] [.word word] :=
    .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started whole.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    support.bodyTyping start inputTypes inputMeanings
  let prepared :=
    CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨sidecar, _sidecarIssued, bodySelected⟩ := whole.invocation selected.packet selected.retained
  obtain ⟨body, covered, closed, ports⟩ := whole.call_inputs calls selected.packet
  obtain ⟨_sourceCompiled, artifact, checked⟩ := CellAwarePublicAcceptedNamedRoot.compilation_receipts
    fixture.checked fixture.accepted fixture.selected
  obtain ⟨_entry, entryMember, _shape, _first⟩ := start.selected.2
  let rows : ∀ header, header ∈ headers whole.rows → called header.instantiation →
      CellAwareInvocationAcceptedCallFamily.Row (headers := headers whole.rows) called header :=
    fun _header member _ => Classical.choice (whole.family_row calls support entryMember member)
  obtain ⟨size, trace⟩ := CellAwareInvocationAcceptedCallLifting.body fixture.recipe.compiled.indexed
    (registry := SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled)
    ((SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled).source bodySelected)
    ((SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled).evidence bodySelected)
    selected.packet.header.unique (planned_callees whole calls wellFormed admitted)
    (fun _ => CellAwareInvocationAcceptedCallLifting.ClosuresFramed.stages fixture.recipe.compiled bodySelected)
    (fun _ => CellAwareInvocationAcceptedCallLifting.ClosuresFramed.stages fixture.recipe.compiled)
    (fun _ => CellAwareInvocationAcceptedCallLifting.Aligned.of_wellFormed wellFormed)
    (calls.header_shape selected.packet)
    (fun _ => CellAwareInvocationAcceptedStoredFunctions.Heap.empty.push fun _ same => by cases same; exact .word word)
    sourceTrace
  obtain ⟨_capture, _value, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput, _result, output⟩ :=
    CellAwarePublicAcceptedCallForward.first_value_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
      initial.heaps rfl start.started start.atCheckpoint
      (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated trace
      (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
        selected.packet.aligned diagnostic support artifact checked closed ports
        (fun _ => CellAwareNamedValuePorts.ports whole.rows whole.complete prepared.compilation) wellFormed rows size)
  obtain ⟨_capture, value, finalStore, _finalMap, _finalWorld, required, run, _result⟩ :=
    CellAwarePublicAcceptedCallRoot.checkpoint_has_sufficient_fuel_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
      initial.heaps rfl start.started allocated trace
      (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
        selected.packet.aligned diagnostic support artifact checked closed ports
        (fun _ => CellAwareNamedValuePorts.ports whole.rows whole.complete prepared.compilation) wellFormed rows size)
  refine ⟨⟨start, ⟨requiredExecution, requiredOutput, ?_⟩, ⟨value, finalStore, required, run⟩, ?_⟩⟩
  · intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    obtain ⟨returned, actual, generation, _reached, same, succeeded, indexed, _⟩ :=
      output executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    exact ⟨returned, actual, generation, _, _, same, succeeded, indexed⟩
  · intro fuel completedValue completedStore completed
    obtain ⟨_capture, size, environment, bound, finalContext, outcome, after, _finalMap, _finalWorld,
        allocated, staged, result, _named⟩ :=
      CellAwarePublicAcceptedCallRoot.checkpoint_reflects_selected callableProfile initial.issued prepared
        selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
        initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
        initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
        initial.heaps rfl start.started completed
        (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
          selected.packet.aligned diagnostic support artifact checked closed ports
          (fun _ => CellAwareNamedValuePorts.ports whole.rows whole.complete prepared.compilation) wellFormed rows)
    exact ⟨sidecar, size, environment, bound, finalContext, outcome, after, allocated, staged, result⟩

/-- The first public call of a row with the conclusion of the call root's checkpoint reflection theorem
alone. -/
structure AcceptedReflection (selected : SelectedInventory whole row) (word : Word)
    (started : Started fixture row.original.key [.word word]) where
  start : SelectedCompilationPublicSessionInitial.Started whole.rows fixture.ready selected.packet.header started.call
  reflects : ∀ fuel (value : Value) (finalStore : Store), start.checkpoint.NativeDone fuel value finalStore →
    ∃ (sidecar : SourceCoreStageContracts.Sidecar) (size : Nat) (environment : Dynamic.Environment)
      (bound : Dynamic.Heap) (finalContext : SourceSemantics.Context) (outcome : Staging.Recursive.BodyOutcome)
      (after : Dynamic.Heap),
      Dynamic.BindersAllocate [] ⟨[]⟩ selected.packet.header.function.parameters [.word word] environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked fixture.recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) size
        (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) selected.packet.header.context
        environment bound selected.packet.header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult selected.packet.header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome)

/-- The reflection part of `accepted_call`, which needs no Source execution and no callee receipts, so it
applies at every argument word. -/
theorem accepted_reflection (selected : SelectedInventory whole row) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions) (word : Word)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (started : Started fixture row.original.key [.word word])
    (callableProfile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {binder : TypedBinder} (inputs : row.original.function.typedBody.inputs = [binder])
    (scheme : binder.scheme = .mono .word) :
    Nonempty (AcceptedReflection selected word started) := by
  obtain ⟨types, _allocated⟩ := word_parameter selected inputs scheme ⟨[]⟩ word
  have support := SelectedCompilationNamedSupport.Support.of_program wellFormed
  obtain ⟨start⟩ := CellAwarePublicInitialSelectedStart.from_selected_call
    (rows := whole.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.accepted fixture.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member key => selected.root_selection member key)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.word word] selected.packet.header.types := by
    rw [types]
    exact .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word word] [.word word] :=
    .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started whole.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    support.bodyTyping start inputTypes inputMeanings
  let prepared :=
    CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨sidecar, _sidecarIssued, bodySelected⟩ := whole.invocation selected.packet selected.retained
  obtain ⟨body, covered, closed, ports⟩ := whole.call_inputs calls selected.packet
  obtain ⟨_sourceCompiled, artifact, checked⟩ := CellAwarePublicAcceptedNamedRoot.compilation_receipts
    fixture.checked fixture.accepted fixture.selected
  obtain ⟨_entry, entryMember, _shape, _first⟩ := start.selected.2
  let rows : ∀ header, header ∈ headers whole.rows → called header.instantiation →
      CellAwareInvocationAcceptedCallFamily.Row (headers := headers whole.rows) called header :=
    fun _header member _ => Classical.choice (whole.family_row calls support entryMember member)
  refine ⟨⟨start, ?_⟩⟩
  intro fuel completedValue completedStore completed
  obtain ⟨_capture, size, environment, bound, finalContext, outcome, after, _finalMap, _finalWorld,
      allocated, staged, result, _named⟩ :=
    CellAwarePublicAcceptedCallRoot.checkpoint_reflects_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
      initial.heaps rfl start.started completed
      (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
        selected.packet.aligned diagnostic support artifact checked closed ports
        (fun _ => CellAwareNamedValuePorts.ports whole.rows whole.complete prepared.compilation) wellFormed rows)
  exact ⟨sidecar, size, environment, bound, finalContext, outcome, after, allocated, staged, result⟩

/-- The receipts that the runtime checks observe: the compiled program, its cache, `identity`'s row and body,
the checked rows of the family of the planned instantiations, the plan's monomorphic rows without assumptions,
the program typing and the callable profile. -/
structure Observed where
  fixture : CompiledFixture workspace options
  cache : ObservedCache fixture fixture.recipe.compiled.indexed.base.functions
  identity : Row fixture
  identityBody : IdentityBody identity.original.function.typedBody
  calls : CallRows fixture (Planned fixture.recipe.compiled.indexed.base.plan)
    fixture.recipe.compiled.indexed.base.functions
  monomorphic : ∀ original ∈ fixture.recipe.compiled.indexed.base.plan.specializations,
    original.parameterSubstitution = [] ∧ original.assumptions = []
  wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  callableProfile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observe : IO Observed := do
  let fixture ← compileFixture workspace options
  let cache ← observeCache fixture fixture.recipe.compiled.indexed.base.functions
  let identity ← observeRow fixture "identity"
  let identityBody ← observeIdentityBody identity.original.function.typedBody
  let calls ← observeCoveredCallRows fixture (Planned fixture.recipe.compiled.indexed.base.plan)
    (Planned.covers fixture.recipe.compiled.indexed.base.plan) fixture.recipe.compiled.indexed.base.functions
  let ⟨monomorphic⟩ ← observed (∀ original ∈ fixture.recipe.compiled.indexed.base.plan.specializations,
    original.parameterSubstitution = [] ∧ original.assumptions = []) "indirect monomorphic plan"
  let ⟨wellFormed⟩ ← observeWellFormed fixture.checked
  let ⟨callableProfile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "indirect actual callable profile"
  return ⟨fixture, cache, identity, identityBody, calls, monomorphic, wellFormed, callableProfile⟩

namespace AcceptedIndirectRuntime

/-- The words at which the rows are called: zero, a small word and the largest word. -/
def words : List Word := [Word.zero, Word.ofNatModulo 7, Word.maximum]

/-- The actual resumption returned the word `expected`. -/
def expect {artifact : SourceCoreExecution.Artifact} (outcome : SourceCoreExecution.Outcome artifact)
    (expected : Word) (row : String) : IO Unit :=
  match outcome with
  | .succeeded returned =>
    unless returned.value == .word expected do throw (IO.userError s!"accepted indirect output of {row} changed")
  | _ => throw (IO.userError s!"accepted indirect call of {row} did not succeed")

/-- At `viaLocal`, `f(value)` with `f` bound to `identity`, which returns the parameter. Each call starts a
fresh actual session; the plan is kernel-checked against whatever the observed compile, check, row and start
receipts are, and the resume runs the real compiled code. -/
def runViaLocal (observed : Observed) : IO Unit := do
  let viaLocal ← observeRow observed.fixture "viaLocal"
  let viaLocalBody ← observeViaLocalBody observed.fixture
    (CallableNamedCanonicalOrder.retainedInstantiation observed.identity.original) viaLocal.original.function.typedBody
  for word in words do
    let started ← observeStarted observed.fixture viaLocal.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole viaLocal),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select viaLocal
      obtain ⟨identitySelected⟩ := whole.select observed.identity
      obtain ⟨_, sourceTrace⟩ := viaLocal_source selected identitySelected observed.calls observed.identityBody
        viaLocalBody ((SelectedCompilationNamedSupport.Support.of_program observed.wellFormed).certified
          selected.packet.header) word
      exact ⟨whole, selected, accepted_call selected observed.calls
        (fun planned => planned_retained observed.monomorphic planned) word observed.wellFormed started
        observed.callableProfile viaLocalBody.parts.inputs viaLocalBody.binderScheme sourceTrace⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    expect result.val word "viaLocal"

/-- At `viaBuiltin`, `plus(value, value)` with `plus` bound to the opcode `add`, which returns the parameter's
word added to itself, wrapped at the largest word. The call root's reflection applies as well. -/
def runViaBuiltin (observed : Observed) : IO Unit := do
  let viaBuiltin ← observeRow observed.fixture "viaBuiltin"
  let viaBuiltinBody ← observeViaBuiltinBody viaBuiltin.original.function.typedBody
  for word in words do
    let started ← observeStarted observed.fixture viaBuiltin.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole viaBuiltin),
        Nonempty (AcceptedCall selected word started) ∧ Nonempty (AcceptedReflection selected word started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.wellFormed
      obtain ⟨selected⟩ := whole.select viaBuiltin
      obtain ⟨_, sourceTrace⟩ := viaBuiltin_source selected viaBuiltinBody
        ((SelectedCompilationNamedSupport.Support.of_program observed.wellFormed).certified selected.packet.header)
        word
      exact ⟨whole, selected, accepted_call selected observed.calls
        (fun planned => planned_retained observed.monomorphic planned) word observed.wellFormed started
        observed.callableProfile viaBuiltinBody.parts.inputs viaBuiltinBody.binderScheme sourceTrace,
        accepted_reflection selected observed.calls word observed.wellFormed started observed.callableProfile
          viaBuiltinBody.parts.inputs viaBuiltinBody.binderScheme⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    expect result.val (word.add word) "viaBuiltin"

/-- The rows `viaLocal` and `viaBuiltin`. -/
def run : IO Unit := do
  let observed ← observe
  runViaLocal observed
  runViaBuiltin observed
  IO.println "ACCEPTED_INDIRECT_PUBLIC_PASS: viaLocal through identity and viaBuiltin through add at 0, 7 and 2^256-1"

end AcceptedIndirectRuntime

end Tests.SourceCoreAcceptedIndirect
end
