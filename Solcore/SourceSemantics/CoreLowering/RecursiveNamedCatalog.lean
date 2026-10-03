import Solcore.SourceSemantics.CoreLowering.BuiltinNamedCallMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity

/-! A finite named-call inventory contains source attribution, actual compiler
and cached hook receipts. Body profiles are kept separately, so recursive
catalog membership does not require recursive semantic evidence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedParameterCertificates
abbrev ValuesContext := SourceCoreCompatibleValues.Context

structure Header {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base) (values : ValuesContext)
    (definitions : DataEnvironment) (program : Program) where
  function : Dynamic.Closure
  instantiation : DeclarationInstantiation
  sourceBody : Dynamic.BodyInstance
  frame : NamedCalls.SourceFrame program instantiation sourceBody function
  named : SourceCoreGeneralFunctions.Function
  agreement : CompatibleNamedBody.NamedAgreement named function
  ordinaryReturn : named.specialized.function.returnComptime = false
  ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  bindings : List Binding
  parameters : function.parameters = bindings.map Prod.fst
  inputs : function.source.inputs = bindings.map Prod.fst
  extended : MonoBindersExtend function.source.owner function.context function.parameters types context
  solved : List SolvedRequirement
  reasonAt : ExpressionId → Word
  readFuel : Nat
  output : Ty
  policy : SourceCoreLoops.Policy
  fuel : Nat
  fellThrough : Word
  escaped : Word
  body : Expr
  parameterCode : Expr
  code : Expr
  layouts : SourceCoreAllocationLayouts.Prepared
  owner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  globals : Nat
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode
  hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code
  definitions_eq : layouts.definitions = definitions
  registered : prepared.layout.frame.Registered definitions
  valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence
  unique : NodeOccurrencesUnique function.source
  parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)
  resultType : named.signature.resultType = output
  representation : SourceCoreGeneralFunctions.Representation
  compiledFuel : Nat
  compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel
  slot : Nat
  selected : base.functions[slot]? = some named
  cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code)


abbrev Inventory {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base) (values : ValuesContext)
    (definitions : DataEnvironment) (program : Program) :=
  List (Header prepared values definitions program)

/-- Construct a header from the complete actual static receipts and the
runtime validity of its actual source context. -/
abbrev Header.of_dictionary_body {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (function : Dynamic.Closure)
    (instantiation : DeclarationInstantiation)
    (sourceBody : Dynamic.BodyInstance)
    (frame : NamedCalls.SourceFrame program instantiation sourceBody function)
    (named : SourceCoreGeneralFunctions.Function)
    (agreement : CompatibleNamedBody.NamedAgreement named function)
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key)
    (context : SourceSemantics.Context)
    (types : List TypeSystem.Ty)
    (bindings : List Binding)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word)
    (readFuel : Nat)
    (output : Ty)
    (policy : SourceCoreLoops.Policy)
    (fuel : Nat)
    (fellThrough : Word)
    (escaped : Word)
    (body : Expr)
    (parameterCode : Expr)
    (code : Expr)
    (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution)
    (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
    (definitions_eq : layouts.definitions = definitions)
    (registered : prepared.layout.frame.Registered definitions)
    (valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence)
    (unique : NodeOccurrencesUnique function.source)
    (parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
    (resultType : named.signature.resultType = output)
    (representation : SourceCoreGeneralFunctions.Representation)
    (compiledFuel : Nat)
    (compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel)
    (slot : Nat)
    (selected : base.functions[slot]? = some named)
    (cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code)) :
    Header prepared values definitions program :=
  { function := function
    instantiation := instantiation
    sourceBody := sourceBody
    frame := frame
    named := named
    agreement := agreement
    ordinaryReturn := ordinaryReturn
    ordinaryParameters := ordinaryParameters
    target := target
    context := context
    types := types
    bindings := bindings
    parameters := parameters
    inputs := inputs
    extended := extended
    solved := solved
    reasonAt := reasonAt
    readFuel := readFuel
    output := output
    policy := policy
    fuel := fuel
    fellThrough := fellThrough
    escaped := escaped
    body := body
    parameterCode := parameterCode
    code := code
    layouts := layouts
    owner := owner
    active := active
    globals := globals
    onError := onError
    acceptedPrefix := acceptedPrefix
    hook := hook
    definitions_eq := definitions_eq
    registered := registered
    valid := valid
    unique := unique
    parameterType := parameterType
    resultType := resultType
    representation := representation
    compiledFuel := compiledFuel
    compiled := compiled
    slot := slot
    selected := selected
    cached := cached }

abbrev Header.of_runtime_body {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (function : Dynamic.Closure)
    (instantiation : DeclarationInstantiation)
    (sourceBody : Dynamic.BodyInstance)
    (frame : NamedCalls.SourceFrame program instantiation sourceBody function)
    (named : SourceCoreGeneralFunctions.Function)
    (agreement : CompatibleNamedBody.NamedAgreement named function)
    (closed : named.specialized.assumptions = [])
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key)
    (context : SourceSemantics.Context)
    (types : List TypeSystem.Ty)
    (bindings : List Binding)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word)
    (readFuel : Nat)
    (output : Ty)
    (policy : SourceCoreLoops.Policy)
    (fuel : Nat)
    (fellThrough : Word)
    (escaped : Word)
    (body : Expr)
    (parameterCode : Expr)
    (code : Expr)
    (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution)
    (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
    (definitions_eq : layouts.definitions = definitions)
    (registered : prepared.layout.frame.Registered definitions)
    (valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence)
    (unique : NodeOccurrencesUnique function.source)
    (parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
    (resultType : named.signature.resultType = output)
    (representation : SourceCoreGeneralFunctions.Representation)
    (compiledFuel : Nat)
    (compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel)
    (slot : Nat)
    (selected : base.functions[slot]? = some named)
    (cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code)) :
    Header prepared values definitions program :=
  let _ := closed
  Header.of_dictionary_body
    (function := function)
    (instantiation := instantiation)
    (sourceBody := sourceBody)
    (frame := frame)
    (named := named)
    (agreement := agreement)
    (ordinaryReturn := ordinaryReturn)
    (ordinaryParameters := ordinaryParameters)
    (target := target)
    (context := context)
    (types := types)
    (bindings := bindings)
    (parameters := parameters)
    (inputs := inputs)
    (extended := extended)
    (solved := solved)
    (reasonAt := reasonAt)
    (readFuel := readFuel)
    (output := output)
    (policy := policy)
    (fuel := fuel)
    (fellThrough := fellThrough)
    (escaped := escaped)
    (body := body)
    (parameterCode := parameterCode)
    (code := code)
    (layouts := layouts)
    (owner := owner)
    (active := active)
    (globals := globals)
    (onError := onError)
    (acceptedPrefix := acceptedPrefix)
    (hook := hook)
    (definitions_eq := definitions_eq)
    (registered := registered)
    (valid := valid)
    (unique := unique)
    (parameterType := parameterType)
    (resultType := resultType)
    (representation := representation)
    (compiledFuel := compiledFuel)
    (compiled := compiled)
    (slot := slot)
    (selected := selected)
    (cached := cached)

/-- Independent source typing supplies runtime ledger validity and the
actual SourceFrame supplies coverage, including retained unused rows. -/
def Header.of_dictionary_frame {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (function : Dynamic.Closure)
    (instantiation : DeclarationInstantiation)
    (sourceBody : Dynamic.BodyInstance)
    (frame : NamedCalls.SourceFrame program instantiation sourceBody function)
    (named : SourceCoreGeneralFunctions.Function)
    (agreement : CompatibleNamedBody.NamedAgreement named function)
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key)
    (context : SourceSemantics.Context)
    (types : List TypeSystem.Ty)
    (bindings : List Binding)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word)
    (readFuel : Nat)
    (output : Ty)
    (policy : SourceCoreLoops.Policy)
    (fuel : Nat)
    (fellThrough : Word)
    (escaped : Word)
    (body : Expr)
    (parameterCode : Expr)
    (code : Expr)
    (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution)
    (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
    (definitions_eq : layouts.definitions = definitions)
    (registered : prepared.layout.frame.Registered definitions)
    (unique : NodeOccurrencesUnique function.source)
    (parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
    (resultType : named.signature.resultType = output)
    (representation : SourceCoreGeneralFunctions.Representation)
    (compiledFuel : Nat)
    (compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel)
    (slot : Nat)
    (selected : base.functions[slot]? = some named)
    (cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code))
    (programTyped : ProgramWellFormed program)
    (sameLedger : function.context.solvedRequirements = solved) :
    Header prepared values definitions program :=
  Header.of_dictionary_body
    (function := function)
    (instantiation := instantiation)
    (sourceBody := sourceBody)
    (frame := frame)
    (named := named)
    (agreement := agreement)
    (ordinaryReturn := ordinaryReturn)
    (ordinaryParameters := ordinaryParameters)
    (target := target)
    (context := context)
    (types := types)
    (bindings := bindings)
    (parameters := parameters)
    (inputs := inputs)
    (extended := extended)
    (solved := solved)
    (reasonAt := reasonAt)
    (readFuel := readFuel)
    (output := output)
    (policy := policy)
    (fuel := fuel)
    (fellThrough := fellThrough)
    (escaped := escaped)
    (body := body)
    (parameterCode := parameterCode)
    (code := code)
    (layouts := layouts)
    (owner := owner)
    (active := active)
    (globals := globals)
    (onError := onError)
    (acceptedPrefix := acceptedPrefix)
    (hook := hook)
    (definitions_eq := definitions_eq)
    (registered := registered)
    (unique := unique)
    (parameterType := parameterType)
    (resultType := resultType)
    (representation := representation)
    (compiledFuel := compiledFuel)
    (compiled := compiled)
    (slot := slot)
    (selected := selected)
    (cached := cached)
    (valid := CompatibleRuntimeContextValidity.of_frame frame extended programTyped sameLedger)

def Header.of_source_frame {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (function : Dynamic.Closure)
    (instantiation : DeclarationInstantiation)
    (sourceBody : Dynamic.BodyInstance)
    (frame : NamedCalls.SourceFrame program instantiation sourceBody function)
    (named : SourceCoreGeneralFunctions.Function)
    (agreement : CompatibleNamedBody.NamedAgreement named function)
    (closed : named.specialized.assumptions = [])
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key)
    (context : SourceSemantics.Context)
    (types : List TypeSystem.Ty)
    (bindings : List Binding)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word)
    (readFuel : Nat)
    (output : Ty)
    (policy : SourceCoreLoops.Policy)
    (fuel : Nat)
    (fellThrough : Word)
    (escaped : Word)
    (body : Expr)
    (parameterCode : Expr)
    (code : Expr)
    (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution)
    (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
    (definitions_eq : layouts.definitions = definitions)
    (registered : prepared.layout.frame.Registered definitions)
    (unique : NodeOccurrencesUnique function.source)
    (parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
    (resultType : named.signature.resultType = output)
    (representation : SourceCoreGeneralFunctions.Representation)
    (compiledFuel : Nat)
    (compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel)
    (slot : Nat)
    (selected : base.functions[slot]? = some named)
    (cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code))
    (programTyped : ProgramWellFormed program)
    (sameLedger : function.context.solvedRequirements = solved) :
    Header prepared values definitions program :=
  let _ := closed
  Header.of_dictionary_frame
    (function := function)
    (instantiation := instantiation)
    (sourceBody := sourceBody)
    (frame := frame)
    (named := named)
    (agreement := agreement)
    (ordinaryReturn := ordinaryReturn)
    (ordinaryParameters := ordinaryParameters)
    (target := target)
    (context := context)
    (types := types)
    (bindings := bindings)
    (parameters := parameters)
    (inputs := inputs)
    (extended := extended)
    (solved := solved)
    (reasonAt := reasonAt)
    (readFuel := readFuel)
    (output := output)
    (policy := policy)
    (fuel := fuel)
    (fellThrough := fellThrough)
    (escaped := escaped)
    (body := body)
    (parameterCode := parameterCode)
    (code := code)
    (layouts := layouts)
    (owner := owner)
    (active := active)
    (globals := globals)
    (onError := onError)
    (acceptedPrefix := acceptedPrefix)
    (hook := hook)
    (definitions_eq := definitions_eq)
    (registered := registered)
    (unique := unique)
    (parameterType := parameterType)
    (resultType := resultType)
    (representation := representation)
    (compiledFuel := compiledFuel)
    (compiled := compiled)
    (slot := slot)
    (selected := selected)
    (cached := cached)
    (programTyped := programTyped)
    (sameLedger := sameLedger)

/-- Forget the old body profile while retaining every actual compilation and
source selection receipt. -/
def Header.of_body {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (body : BuiltinNamedCalls.Body prepared values definitions program) :
    Header prepared values definitions program :=
  Header.of_runtime_body
    (function := body.function)
    (instantiation := body.instantiation)
    (sourceBody := body.sourceBody)
    (frame := body.frame)
    (named := body.named)
    (agreement := body.agreement)
    (closed := body.closed)
    (ordinaryReturn := body.ordinaryReturn)
    (ordinaryParameters := body.ordinaryParameters)
    (target := body.target)
    (context := body.context)
    (types := body.types)
    (bindings := body.bindings)
    (parameters := body.parameters)
    (inputs := body.inputs)
    (extended := body.extended)
    (solved := body.solved)
    (reasonAt := body.reasonAt)
    (readFuel := body.readFuel)
    (output := body.output)
    (policy := body.policy)
    (fuel := body.fuel)
    (fellThrough := body.fellThrough)
    (escaped := body.escaped)
    (body := body.body)
    (parameterCode := body.parameterCode)
    (code := body.code)
    (layouts := body.layouts)
    (owner := body.owner)
    (active := body.active)
    (globals := body.globals)
    (onError := body.onError)
    (acceptedPrefix := body.acceptedPrefix)
    (hook := body.hook)
    (definitions_eq := body.definitions_eq)
    (registered := body.registered)
    (unique := body.unique)
    (parameterType := body.parameterType)
    (resultType := body.resultType)
    (representation := body.representation)
    (compiledFuel := body.compiledFuel)
    (compiled := body.compiled)
    (slot := body.slot)
    (selected := body.selected)
    (cached := body.cached)
    (valid := CompatibleRuntimeContextValidity.of_ordinary body.valid)

theorem Header.of_body_slot {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (body : BuiltinNamedCalls.Body prepared values definitions program) :
    (Header.of_body body).slot = body.slot := rfl

/-- Empty legacy invocation evidence forces empty source predicates through the
actual SourceFrame coverage; general headers retain their full dictionary. -/
theorem Header.predicates_of_empty {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (header : Header prepared values definitions program)
    (empty : header.function.evidence = []) : header.instantiation.predicates = [] := by
  have assumptions : header.sourceBody.context.assumptions = header.instantiation.predicates := by
    cases header.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq => rw [contextEq]; rfl
  have supplies := header.frame.covers.2
  rw [empty] at supplies
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro predicate member
  obtain ⟨evidence, found⟩ := supplies predicate (assumptions.symm ▸ member)
  cases found

/-- A real cached row includes its signature, code and ordered slot. -/
theorem Header.cached_code {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (header : Header prepared values definitions program) :
    header.compiled.closures[header.slot]? = some (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code) := header.cached

/-- Owner uniqueness fixes independent source dispatch; it is not inferred
from a native signature or a selected slot. -/
theorem Header.source_unique {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (header : Header prepared values definitions program)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    {actual : Dynamic.BodyInstance} (instantiated : Dynamic.FunctionInstantiates program header.instantiation actual) :
    actual = header.sourceBody :=
  BuiltinNamedCalls.instantiation_unique owners instantiated header.frame.instantiated

/-- One actual cached closure ledger can certify every finite header. The
ordered slots and source owner uniqueness remain explicit static obligations. -/
structure Ledger {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (headers : Inventory prepared values definitions program) (closures : List Expr) : Prop where
  slots : (headers.map (·.slot)).Nodup
  owners : (program.functions.map (fun definition => definition.body.owner)).Nodup
  cached : ∀ header, header ∈ headers → closures[header.slot]? = some
    (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
