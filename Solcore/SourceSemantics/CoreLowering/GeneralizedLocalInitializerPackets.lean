import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfile
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerCompilation

/-! Every finite bundle row receives the lambda packet from its actual
candidate source. The scanner observes raw metadata and compatible reads;
accepted compilation supplies the child certificate and emitted code. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerPackets
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism DataPatternValues
open GeneralizedLocalInstanceCompilation (Inputs)

structure Observations (representation : SourceCoreGeneralFunctions.Representation)
    (callerKey : Key) (id : ExpressionId) (candidate : Instance) where
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  reported : Core.Ty
  caller : callerKey = candidate.origin.caller
  initializer : candidate.origin.initializer = id
  found : candidate.source.lookupExpression? id = some node
  form : node.form = .lambda parameters result body
  owner : id.occurrence.owner = candidate.source.owner
  requirements : node.requirements = []
  coercions : node.coercions = []
  read : representation.expressions.readExpression candidate.source id = .ok (node, reported)

abbrev Profile (inputs : Inputs) :=
  Observations inputs.representation inputs.current.owner inputs.initializer

def observations? (representation : SourceCoreGeneralFunctions.Representation)
    (callerKey : Key) (id : ExpressionId) (candidate : Instance) :
    Option (Observations representation callerKey id candidate) :=
  if caller : callerKey = candidate.origin.caller then
    if initializer : candidate.origin.initializer = id then
      if owner : id.occurrence.owner = candidate.source.owner then
        match found : candidate.source.lookupExpression? id with
        | none => none
        | some node =>
          match form : node.form with
          | .lambda parameters result body =>
            if requirements : node.requirements = [] then
              if coercions : node.coercions = [] then
                match read : representation.expressions.readExpression candidate.source id with
                | .error _ => none
                | .ok (actual, reported) =>
                  if same : actual = node then
                    some ⟨node, parameters, result, body, reported, caller, initializer, found, form,
                      owner, requirements, coercions, by simpa only [same] using read⟩
                  else none
              else none
            else none
          | _ => none
      else none
    else none
  else none

def profile? (inputs : Inputs) (candidate : Instance) : Option (Profile inputs candidate) :=
  observations? inputs.representation inputs.current.owner inputs.initializer candidate

def profiles? (inputs : Inputs) : (candidates : List Instance) →
    Option (PLift (∀ candidate ∈ candidates, Nonempty (Profile inputs candidate)))
  | [] => some ⟨by intro candidate member; cases member⟩
  | candidate :: rest => do
    let head ← profile? inputs candidate
    let ⟨tail⟩ ← profiles? inputs rest
    pure ⟨by
      intro selected member
      rcases List.mem_cons.mp member with same | member
      · subst selected; exact ⟨head⟩
      · exact tail selected member⟩

/-- Candidate source identity is checked against the exact stored binding,
separately from its cumulative native key and projected type. -/
structure BindingObservations (representation : SourceCoreGeneralFunctions.Representation)
    (callerKey : Key) (id : ExpressionId) (binding : Binding) (candidate : Instance)
    extends Observations representation callerKey id candidate where
  originalSource : candidate.origin.source = binding.source
  originalBinder : candidate.origin.binder.id = binding.binder.id

abbrev BindingProfile (inputs : Inputs) :=
  BindingObservations inputs.representation inputs.current.owner inputs.initializer

def bindingObservations? (representation : SourceCoreGeneralFunctions.Representation)
    (callerKey : Key) (id : ExpressionId) (binding : Binding) (candidate : Instance) :
    Option (BindingObservations representation callerKey id binding candidate) := do
  let profile ← observations? representation callerKey id candidate
  if originalSource : candidate.origin.source = binding.source then
    if originalBinder : candidate.origin.binder.id = binding.binder.id then
      pure ⟨profile, originalSource, originalBinder⟩
    else none
  else none

def bindingProfile? (inputs : Inputs) (binding : Binding) (candidate : Instance) :
    Option (BindingProfile inputs binding candidate) :=
  bindingObservations? inputs.representation inputs.current.owner inputs.initializer binding candidate

def bindingProfiles? (inputs : Inputs) (binding : Binding) : (candidates : List Instance) →
    Option (PLift (∀ candidate ∈ candidates, Nonempty (BindingProfile inputs binding candidate)))
  | [] => some ⟨by intro candidate member; cases member⟩
  | candidate :: rest => do
    let head ← bindingProfile? inputs binding candidate
    let ⟨tail⟩ ← bindingProfiles? inputs binding rest
    pure ⟨by
      intro selected member
      rcases List.mem_cons.mp member with same | member
      · subst selected; exact ⟨head⟩
      · exact tail selected member⟩

theorem Profile.packet {inputs : Inputs} {candidate : Instance} {raw : Core.Expr}
    (profile : Profile inputs candidate)
    (receipt : GeneralizedLocalInstanceCompilation.Receipt inputs candidate raw) :
    Nonempty (GeneralizedLocalLambdaCompilation.Packet inputs candidate raw) := by
  have sourceEq : receipt.emission.prepared.source = candidate.source :=
    GeneralizedLocalLambdaEmissionFacts.Emission.source receipt.emission
  exact GeneralizedLocalLambdaCompilation.of_receipt receipt
    (sourceEq ▸ profile.found) profile.form (sourceEq ▸ profile.owner) profile.requirements profile.coercions
    (sourceEq ▸ profile.read)

/-- The native rows remain paired in the exact original order, even when
several candidates project to the same native function type. -/
def IndexedRows {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (inputs : Inputs) (lexical : Substitution)
    (candidates : List Instance) (closures : List Core.Expr) : Prop :=
  ListRel (fun candidate raw => Nonempty (Sigma fun packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw =>
    { indexed : GeneralizedLocalLambdaGeneration.Indexed prepared packet // indexed.lexical = lexical } ×
      GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner packet.original.emission.prepared.source inputs.initializer)) candidates closures

theorem indexed_rows {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) {inputs : Inputs}
    {candidates : List Instance} {closures : List Core.Expr}
    (rows : ListRel (fun candidate raw => Nonempty (GeneralizedLocalInstanceCompilation.Receipt inputs candidate raw))
      candidates closures)
    (profiles : ∀ candidate ∈ candidates, Nonempty (Profile inputs candidate))
    (bodies : ∀ candidate ∈ candidates, Nonempty (GeneralizedLocalBodyProfile.Profile
      inputs.locals inputs.current.owner candidate.source inputs.initializer))
    (lexical : Substitution)
    (represented : inputs.representation =
      (CallableIndexedNamedGeneration.representation prepared).atContext inputs.current.owner lexical)
    (program : inputs.program = prepared.base.sourceProgram) (locals : inputs.locals = prepared.base.locals)
    (native : inputs.native = prepared.base.callableContext) (plan : inputs.current.plan = prepared.base.plan)
    (globals : inputs.current.globals = prepared.base.globals)
    (administrativePrefix : inputs.current.administrativePrefix = 1) :
    IndexedRows prepared inputs lexical candidates closures := by
  induction rows with
  | nil => exact .nil
  | @cons candidate raw rest remaining head tail ih =>
    obtain ⟨profile⟩ := profiles candidate (by simp)
    obtain ⟨receipt⟩ := head
    obtain ⟨packet⟩ := profile.packet receipt
    obtain ⟨indexed⟩ := GeneralizedLocalLambdaGeneration.of_packet prepared packet lexical
      represented program locals native plan profile.caller globals administrativePrefix
    let exactIndexed : GeneralizedLocalLambdaGeneration.Indexed prepared packet :=
      { indexed with lexical := lexical, represented := represented }
    obtain ⟨body⟩ := bodies candidate (by simp)
    have sourceEq := GeneralizedLocalLambdaEmissionFacts.Emission.source packet.original.emission
    have body : GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner
        packet.original.emission.prepared.source inputs.initializer := sourceEq.symm ▸ body
    exact .cons ⟨⟨packet, ⟨⟨exactIndexed, rfl⟩, body⟩⟩⟩
      (ih (fun child member => profiles child (List.mem_cons_of_mem _ member))
        (fun child member => bodies child (List.mem_cons_of_mem _ member)))

structure Receipt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (inputs : Inputs)
    (binding : Binding) (active : Substitution) (lowered : SourceCoreBasic.LoweredExpr) where
  original : GeneralizedLocalInitializerCompilation.Receipt inputs binding active lowered
  rows : IndexedRows prepared inputs active (binding.atContext active) original.closures
  sources : ∀ candidate ∈ binding.atContext active, candidate.origin.source = binding.source
  binders : ∀ candidate ∈ binding.atContext active, candidate.origin.binder.id = binding.binder.id

theorem of_receipt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) {inputs : Inputs}
    {binding : Binding} {active : Substitution} {lowered : SourceCoreBasic.LoweredExpr}
    (original : GeneralizedLocalInitializerCompilation.Receipt inputs binding active lowered)
    (profiles : ∀ candidate ∈ binding.atContext active, Nonempty (BindingProfile inputs binding candidate))
    (bodies : ∀ candidate ∈ binding.atContext active, Nonempty (GeneralizedLocalBodyProfile.Profile
      inputs.locals inputs.current.owner candidate.source inputs.initializer))
    (represented : inputs.representation =
      (CallableIndexedNamedGeneration.representation prepared).atContext inputs.current.owner active)
    (program : inputs.program = prepared.base.sourceProgram) (locals : inputs.locals = prepared.base.locals)
    (native : inputs.native = prepared.base.callableContext) (plan : inputs.current.plan = prepared.base.plan)
    (globals : inputs.current.globals = prepared.base.globals)
    (administrativePrefix : inputs.current.administrativePrefix = 1) :
    Nonempty (Receipt prepared inputs binding active lowered) :=
  ⟨⟨original, indexed_rows prepared original.rows (fun candidate member => by
      obtain ⟨profile⟩ := profiles candidate member
      exact ⟨profile.toObservations⟩) bodies active represented program locals native plan globals administrativePrefix,
    fun candidate member => by obtain ⟨profile⟩ := profiles candidate member; exact profile.originalSource,
    fun candidate member => by obtain ⟨profile⟩ := profiles candidate member; exact profile.originalBinder⟩⟩

private theorem indexed_type {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {candidate : Instance} {raw : Core.Expr}
    {packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw}
    (indexed : GeneralizedLocalLambdaGeneration.Indexed prepared packet)
    {context : Core.Context} {definitions : DataEnvironment} {type : Core.Ty}
    (typed : HasType context raw type definitions) : type = candidate.type := by
  rw [indexed.emitted] at typed
  cases typed with
  | pair tagged identifier =>
    cases identifier
    cases tagged with
    | pair marker function =>
      cases marker with
      | inLeft _ marker =>
        cases marker
        cases function with
        | letE snapshot closure =>
          cases closure
          exact indexed.nativeType.symm

private theorem rows_typed {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {lexical : Substitution} {candidates : List Instance} {closures : List Core.Expr}
    (rows : IndexedRows prepared inputs lexical candidates closures)
    {context : Core.Context} {definitions : DataEnvironment} {type : Core.Ty}
    (typed : HasType context (ProductBundle.expression closures) type definitions) :
    type = ProductBundle.type (candidates.map (·.type)) ∧
      ListRel (fun candidate raw => HasType context raw candidate.type definitions) candidates closures := by
  induction rows generalizing type with
  | nil => cases typed; exact ⟨rfl, .nil⟩
  | @cons candidate raw rest remaining head tail ih =>
    obtain ⟨⟨packet, ⟨indexed, _lexical⟩, _body⟩⟩ := head
    cases tail with
    | nil =>
      have same := indexed_type indexed typed
      exact ⟨same, .cons (same ▸ typed) .nil⟩
    | cons next restRows =>
      cases typed with
      | pair left right =>
        have first := indexed_type indexed left
        obtain ⟨remainingType, remainingTyped⟩ := ih right
        exact ⟨by simp only [List.map_cons, ProductBundle.type, first, remainingType],
          .cons (first ▸ left) remainingTyped⟩

/-- Static typing of the actual emitted bundle recovers every row's exact
native type from its authentic snapshot-lambda header. -/
theorem Receipt.raw_typed {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {binding : Binding} {active : Substitution} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt prepared inputs binding active lowered)
    {context : Core.Context} {definitions : DataEnvironment} {type : Core.Ty}
    (typed : HasType context lowered.expression type definitions) :
    type = LanguageResult.resultType lowered.type ∧
      ListRel (fun candidate raw => HasType context raw candidate.type definitions)
        (binding.atContext active) receipt.original.closures := by
  rw [receipt.original.emitted] at typed
  have loweredType : lowered.type = binding.bundleType active :=
    congrArg SourceCoreBasic.LoweredExpr.type receipt.original.emitted
  rw [loweredType]
  cases typed with
  | inRight _ bundle =>
    obtain ⟨same, rows⟩ := rows_typed receipt.rows bundle
    exact ⟨by simpa only [Binding.bundleType, LanguageResult.resultType] using congrArg (Core.Ty.sum .word) same, rows⟩

theorem Receipt.typed {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {binding : Binding} {active : Substitution} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt prepared inputs binding active lowered)
    {context : Core.Context} {definitions : DataEnvironment} {type : Core.Ty}
    (typed : HasType context lowered.expression type definitions) :
    HasType context lowered.expression (LanguageResult.resultType lowered.type) definitions :=
  (receipt.raw_typed typed).1 ▸ typed

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerPackets
