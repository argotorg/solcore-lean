import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReadBundles
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductTree
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.OrdinaryBodies
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.SourceSemantics.SubstitutionProperties
import Solcore.SourceSemantics.Dynamic.GeneralizedClosure
import Solcore.Frontend.SourceSpecializationWorklist
import Solcore.SourceSemantics.SourceInferenceSubtreeInverseClosure
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionExpressions
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates

/-!
# Generalized locals: lambda compilation

Compilation and generation of generalized lambdas, ordinary read sites and body profiles, instance values and the read view.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaEmissionFacts
/-! The checked local-instance factory fixes the complete candidate and the
source substitution. Its read parent remains the actual authenticated parent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaEmissionFacts
open Core Frontend SourceInference SourceCoreLocalPolymorphism

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem exactCaller_source {plan : SourceSpecializationWorklist.Plan} {binding : Binding}
    {caller : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCoreLocalEvidence.exactCaller plan binding = .ok caller) :
    caller.function.typedBody = binding.source := by
  unfold SourceCoreLocalEvidence.exactCaller at accepted
  obtain ⟨actual, _selected, accepted⟩ := bind_ok accepted
  try dsimp only at accepted
  split at accepted
  · cases accepted
  · next same =>
    try dsimp only at accepted
    split at accepted
    · cases accepted
      exact Classical.byContradiction same
    · cases accepted

/-- The one successful factory result retains the full candidate key and the
source graph selected by that same checked caller. -/
theorem prepare_facts {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared) :
    prepared.instance = candidate ∧
      prepared.substitution = candidate.origin.substitution ∧
      prepared.source = candidate.origin.source.applySubstitution candidate.origin.substitution := by
  unfold SourceCoreLocalEvidence.prepare at accepted
  obtain ⟨caller, selected, accepted⟩ := bind_ok accepted
  have source := exactCaller_source selected
  try dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨_discovered, _discovery, accepted⟩ := bind_ok accepted
    try dsimp only at accepted
    split at accepted
    · try dsimp only at accepted
      obtain ⟨⟨_active, _inherited⟩, _context, accepted⟩ := bind_ok accepted
      try dsimp only at accepted
      split at accepted
      · dsimp only [pure, Except.pure, bind, Except.bind] at accepted
        obtain ⟨_reference, _authenticated, accepted⟩ := bind_ok accepted
        try dsimp only at accepted
        split at accepted
        · cases accepted
        · try dsimp only at accepted
          obtain ⟨_checked, _validated, accepted⟩ := bind_ok accepted
          cases accepted
          exact ⟨rfl, rfl, congrArg (fun value => value.applySubstitution candidate.origin.substitution) source⟩
      · cases accepted
    · cases accepted

theorem Emission.instance {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    (emission : SourceCoreLocalEvidence.Emission program plan candidate parent) :
    emission.prepared.instance = candidate :=
  (prepare_facts emission.authentic).1

theorem Emission.substitution {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    (emission : SourceCoreLocalEvidence.Emission program plan candidate parent) :
    emission.prepared.substitution = candidate.origin.substitution :=
  (prepare_facts emission.authentic).2.1

theorem Emission.source {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    (emission : SourceCoreLocalEvidence.Emission program plan candidate parent) :
    emission.prepared.source = candidate.origin.source.applySubstitution candidate.origin.substitution :=
  (prepare_facts emission.authentic).2.2

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaEmissionFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaCompilation
/-! The literal contextual child of a generalized initializer retains its
actual lambda certificate. No source closure or read-site dictionary is
chosen while the native bundle is created. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaCompilation
open Core Frontend SourceInference SourceCoreLocalPolymorphism
open GeneralizedLocalInstanceCompilation (Inputs Receipt)

def context (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) : SourceCoreFunctions.Context :=
  { inputs.current with solvedRequirements := prepared.caller.function.solvedRequirements }

def representation (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) :
    SourceCoreGeneralFunctions.Representation :=
  inputs.representation.atContext inputs.current.owner prepared.substitution

def binder (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) :=
  SourceCoreGeneralFunctions.contextualBinder (representation inputs prepared)
    inputs.locals inputs.current.owner prepared.substitution

def lowerBody (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) :=
  SourceCoreGeneralFunctions.bodyLowererWithRepresentation (representation inputs prepared)
    prepared.caller.function.solvedRequirements inputs.assignments inputs.diagnostics inputs.current.owner
    (binder inputs prepared)

private def localError (id : ExpressionId) (node : ExpressionNode) : SourceCoreLocalPolymorphism.Error → SourceCoreBasic.Error
  | .metadata error => error
  | _ => .unsupportedExpression id node.form

def special (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) (fuel : Nat) :
    SourceCoreFunctions.Context → SourceCoreFunctions.ExpressionLowerer → Nat →
      TypedSource → SourceCoreBasic.Scope → ExpressionId → (ExpressionId → Word) →
      Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr) :=
  fun current child budget source scope id reasonAt => do
    let source ← SourceCoreGeneralFunctions.contextualSource inputs.program current.plan inputs.locals
      current.owner (some prepared) source id
    let node ← match source.lookupExpression? id with
      | some node => pure node
      | none => throw (.missingExpression id)
    let initialized := inputs.locals.bindings.find? fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)
    if let some initialized := initialized.filter (fun _ => some inputs.initializer ≠ some id) then
      let binding ← (inputs.locals.binding current.owner initialized.binder.id).mapError (localError id node)
      let lowered ← (SourceCoreLocalPolymorphism.lowerInitializer binding prepared.substitution
        (GeneralizedLocalInstanceCompilation.compile {
          inputs with representation := representation inputs prepared
                      current := current
                      parent := some prepared
                      budget := budget
                      fuel := fuel
                      initializer := id
                      scope := scope
                      reasonAt := reasonAt })).mapError (localError id node)
      return some lowered
    let evidence ← SourceCoreEvidence.lowerWithProjector inputs.program
      (representation inputs prepared).expressions.projectType prepared.caller current child budget
      source scope id reasonAt (SourceCoreGeneralFunctions.callablePolicy inputs.native prepared.substitution)
    if let some lowered := evidence then return some lowered
    match node.form with
    | .reference _ (.local identifier) =>
      if inputs.locals.bindings.any (fun binding =>
          decide (binding.caller = current.owner ∧ binding.binder.id = identifier)) then
        let lowered ← (SourceCoreLocalPolymorphism.lowerRead inputs.locals current.owner
          prepared.substitution source scope id (reasonAt id)).mapError (localError id node)
        let viewed ← (representation inputs prepared).localReadView current.owner prepared.substitution
          source scope id lowered
        SourceCoreBasic.ensureType (.occurrence id.occurrence) lowered.type viewed.type
        return some viewed
      else return none
    | _ => return none

def policy (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) (fuel : Nat) : SourceCoreFunctions.Policy :=
  { (representation inputs prepared).expressions with
    callables := SourceCoreGeneralFunctions.callablePolicy inputs.native prepared.substitution
    snapshotLambda := fun lambda => some inputs.initializer ≠ some lambda
    lowerBinder := binder inputs prepared
    readExpression := fun source id => do
      let source ← SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan
        inputs.locals inputs.current.owner (some prepared) source id
      (representation inputs prepared).expressions.readExpression source id
    lowerSpecial? := some (special inputs prepared fuel) }

/-- This equation unfolds the actual recursive contextual call, including its
original fuel cap and the exact initializer skipped by this one child. -/
theorem child_at_succ (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) {fuel : Nat}
    (budget : min inputs.budget inputs.fuel = fuel + 1) :
    inputs.child prepared = SourceCoreFunctions.lowerExpressionWithPolicy
      (policy inputs prepared fuel) (lowerBody inputs prepared) (fuel + 1) (context inputs prepared)
      prepared.source inputs.scope inputs.initializer inputs.reasonAt := by
  unfold Inputs.child
  rw [budget, SourceCoreGeneralFunctions.lowerContextualExpression.eq_def]
  rfl

private theorem evidence_lambda (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (compilation : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : SourceCoreBasic.Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result statements)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller compilation child fuel source scope id reasonAt callables = .ok none := by
  have owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, found, form, owned, requirements, coercions,
    bind, Except.bind, pure, Except.pure]

structure Packet (inputs : Inputs) (candidate : Instance) (raw : Expr) where
  original : Receipt inputs candidate raw
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  reported : Ty
  found : original.emission.prepared.source.lookupExpression? inputs.initializer = some node
  form : node.form = .lambda parameters result statements
  owner : inputs.initializer.occurrence.owner = original.emission.prepared.source.owner
  requirements : node.requirements = []
  coercions : node.coercions = []
  fuel : Nat
  budget : min inputs.budget inputs.fuel = fuel + 1
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy
    (policy inputs original.emission.prepared fuel) (lowerBody inputs original.emission.prepared)
    (fuel + 1) (context inputs original.emission.prepared) original.emission.prepared.source
    inputs.scope inputs.initializer inputs.reasonAt = .ok original.lowered
  certificate : CallableIndexedLambdaCertificates.Certificate
    (policy inputs original.emission.prepared fuel) (lowerBody inputs original.emission.prepared)
    fuel (context inputs original.emission.prepared) original.emission.prepared.source inputs.scope
    inputs.initializer node parameters result statements reported inputs.reasonAt original.lowered

/-- The factory result and its child certificate are retained together before
any particular source materialization supplies an evidence environment. -/
theorem of_receipt {inputs : Inputs} {candidate : Instance} {raw : Expr}
    (original : Receipt inputs candidate raw)
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId} {reported : Ty}
    (found : original.emission.prepared.source.lookupExpression? inputs.initializer = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : inputs.initializer.occurrence.owner = original.emission.prepared.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (read : inputs.representation.expressions.readExpression original.emission.prepared.source
      inputs.initializer = .ok (node, reported)) : Nonempty (Packet inputs candidate raw) := by
  have accepted := original.compiled
  cases budget : min inputs.budget inputs.fuel with
  | zero => simp [Inputs.child, budget, SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  | succ fuel =>
    rw [child_at_succ inputs original.emission.prepared budget] at accepted
    have unchanged : SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
        inputs.current.owner (some original.emission.prepared) original.emission.prepared.source
        inputs.initializer = .ok original.emission.prepared.source := by
      simp [SourceCoreGeneralFunctions.contextualSource, found, form]
    obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted
      (owner := owner) (found := found) (form := form) (accepted := accepted)
      (ordinary := by
        change special inputs original.emission.prepared fuel _ _ _ _ _ _ _ = .ok none
        unfold special
        change (do
          let source ← SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
            inputs.current.owner (some original.emission.prepared) original.emission.prepared.source inputs.initializer
          _) = .ok none
        rw [unchanged]
        simp only [bind, Except.bind, pure, Except.pure, found]
        rw [evidence_lambda _ _ _ _ _ _ _ _ _ found form requirements coercions]
        simp [form])
      (read := by
        change (do
          let source ← SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
            inputs.current.owner (some original.emission.prepared) original.emission.prepared.source inputs.initializer
          inputs.representation.expressions.readExpression source inputs.initializer) = .ok (node, reported)
        simpa only [unchanged, bind, Except.bind] using read)
    exact ⟨⟨original, node, parameters, result, statements, reported, found, form, owner,
      requirements, coercions, fuel, budget, accepted, certificate⟩⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaCompilation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaGeneration
/-! Generalized native instances retain the exact indexed lambda emitted by
 their contextual child. The creation receipt is independent of any source
 closure that will later be materialized by a local read. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaGeneration
open Core Frontend SourceInference
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet context policy lowerBody)

structure Indexed {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : Packet inputs candidate raw) where
  lexical : TypeSystem.Substitution
  represented : inputs.representation =
    (CallableIndexedNamedGeneration.representation prepared).atContext inputs.current.owner lexical
  program : inputs.program = prepared.base.sourceProgram
  locals : inputs.locals = prepared.base.locals
  native : inputs.native = prepared.base.callableContext
  plan : inputs.current.plan = prepared.base.plan
  owner : inputs.current.owner = candidate.origin.caller
  descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table
    (.lambda inputs.current.owner inputs.initializer packet.original.emission.prepared.substitution)
  nativeType : candidate.type =
    CallableContract.functionType packet.certificate.parameterCore packet.certificate.resultCore
  emitted : raw = descriptor.wrap (TaggedFunction.anonymous
    (SourceCoreCallableIndexedAncestry.snapshotLambda prepared.ancestry.graph.table
      prepared.ancestry.layout.frame descriptor.id
      (SourceCoreCallableIndexedAncestry.creationReferenceIndex
        (context inputs packet.original.emission.prepared) inputs.scope)
      packet.certificate.parameterCore packet.certificate.resultCore packet.certificate.rawBody))
  globals : inputs.current.globals = prepared.base.globals
  administrativePrefix : inputs.current.administrativePrefix = 1

private theorem descriptor_exists (table : SourceCoreStageCodebook.Table)
    {origin : SourceCoreStageCodebook.Origin} {id : Word} (selected : table.idAt? origin = some id) :
    Nonempty (SourceCoreCallableContracts.Descriptor table origin) := by
  cases accepted : SourceCoreCallableContracts.descriptor table origin with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at accepted
    split at accepted
    · rename_i absent
      rw [selected] at absent
      cases absent
    · cases accepted
  | ok descriptor => exact ⟨descriptor⟩

/-- Select the descriptor from the successful production hook, preserving the
full candidate substitution and the actual lexical capture index. -/
theorem of_packet {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : Packet inputs candidate raw) (lexical : TypeSystem.Substitution)
    (represented : inputs.representation =
      (CallableIndexedNamedGeneration.representation prepared).atContext inputs.current.owner lexical)
    (program : inputs.program = prepared.base.sourceProgram)
    (locals : inputs.locals = prepared.base.locals)
    (native : inputs.native = prepared.base.callableContext)
    (plan : inputs.current.plan = prepared.base.plan)
    (owner : inputs.current.owner = candidate.origin.caller)
    (globals : inputs.current.globals = prepared.base.globals)
    (administrativePrefix : inputs.current.administrativePrefix = 1) :
    Nonempty (Indexed prepared packet) := by
  have expressionProfile :
      (policy inputs packet.original.emission.prepared packet.fuel).rawLambdaExpression =
      SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry inputs.current.owner
        packet.original.emission.prepared.substitution := by
    unfold policy GeneralizedLocalLambdaCompilation.representation
    rw [represented]
    rfl
  have callables : (policy inputs packet.original.emission.prepared packet.fuel).callables =
      SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable)
        packet.original.emission.prepared.substitution := by
    change SourceCoreGeneralFunctions.callablePolicy inputs.native _ = _
    rw [native, prepared.ancestry.graph.inputs.callableSelected]
  have hook := packet.certificate.expressionHook
  rw [expressionProfile] at hook
  obtain ⟨origin, body, selected, rawShape, _, _, _, emitted⟩ :=
    CallableIndexedFormation.expressionHook_receipt prepared.ancestry hook
  have sameBody := Expr.lambda.inj rawShape
  rw [(lookupExpression?_sound packet.found).2] at selected
  obtain ⟨descriptor⟩ := descriptor_exists _ selected
  have sameOrigin : origin = descriptor.id := Option.some.inj (selected.symm.trans descriptor.found)
  have bodyEq : packet.certificate.rawBody = body := sameBody.2.2
  have decorated := packet.certificate.decoration
  rw [callables] at decorated
  have expected := ActualCallablePolicy.lambda_decoration prepared.ancestry.graph.inputs.callable
    packet.original.emission.prepared.substitution (context inputs packet.original.emission.prepared)
    packet.original.emission.prepared.source packet.node inputs.initializer
    packet.certificate.parameterCore packet.certificate.resultCore
    (TaggedFunction.anonymous packet.certificate.rawLambda) descriptor
  have decoration := Except.ok.inj (decorated.symm.trans expected)
  have exactExpression : packet.original.lowered.expression = LanguageResult.success
      (descriptor.wrap (TaggedFunction.anonymous
        (SourceCoreCallableIndexedAncestry.snapshotLambda prepared.ancestry.graph.table
          prepared.ancestry.layout.frame descriptor.id
          (SourceCoreCallableIndexedAncestry.creationReferenceIndex
            (context inputs packet.original.emission.prepared) inputs.scope)
          packet.certificate.parameterCore packet.certificate.resultCore packet.certificate.rawBody))) := by
    have unsnapshotted : packet.certificate.snapshotted = packet.certificate.expression := by
      have snapshot := packet.certificate.snapshot
      have off : (policy inputs packet.original.emission.prepared packet.fuel).snapshotLambda
          inputs.initializer = false := by
        simp [policy]
      simp only [off, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at snapshot
      exact snapshot.symm
    apply (congrArg SourceCoreBasic.LoweredExpr.expression packet.certificate.emitted).trans
    change packet.certificate.snapshotted = _
    rw [unsnapshotted, decoration, emitted, sameOrigin, ← bodyEq]
    rfl
  have rawEq := packet.original.extracted.symm.trans exactExpression
  have reportedType : packet.reported =
      CallableContract.functionType packet.certificate.parameterCore packet.certificate.resultCore := by
    have accepted := packet.certificate.checked
    rw [callables] at accepted
    unfold SourceCoreBasic.ensureType at accepted
    split at accepted
    · assumption
    · cases accepted
  have nativeType : candidate.type =
      CallableContract.functionType packet.certificate.parameterCore packet.certificate.resultCore :=
    packet.original.nativeType.trans
      ((congrArg SourceCoreBasic.LoweredExpr.type packet.certificate.emitted).trans reportedType)
  exact ⟨⟨lexical, represented, program, locals, native, plan, owner, descriptor,
    nativeType, (Expr.inRight.inj rawEq).2, globals, administrativePrefix⟩⟩

namespace Indexed
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked}
  {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
  {packet : Packet inputs candidate raw}

theorem allocationProfile (indexed : Indexed prepared packet) :
    (policy inputs packet.original.emission.prepared packet.fuel).sourceCells =
      some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame
        prepared.base.globals.length (prepared.layouts.allocatorAt inputs.current.owner
          packet.original.emission.prepared.substitution
          (fun error => .sourceAllocation (reprStr error)))) := by
  unfold policy GeneralizedLocalLambdaCompilation.representation
  rw [indexed.represented]
  rfl

theorem manifest (indexed : Indexed prepared packet) :
    (policy inputs packet.original.emission.prepared packet.fuel).rawLambdaBody =
      SourceCoreLambdaTemplates.hook prepared.ancestry.templates inputs.current.owner
        packet.original.emission.prepared.substitution := by
  unfold policy GeneralizedLocalLambdaCompilation.representation
  rw [indexed.represented]
  rfl

theorem expressionProfile (indexed : Indexed prepared packet) :
    (policy inputs packet.original.emission.prepared packet.fuel).rawLambdaExpression =
      SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry inputs.current.owner
        packet.original.emission.prepared.substitution := by
  unfold policy GeneralizedLocalLambdaCompilation.representation
  rw [indexed.represented]
  rfl

theorem callables (indexed : Indexed prepared packet) :
    (policy inputs packet.original.emission.prepared packet.fuel).callables =
      SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable)
        packet.original.emission.prepared.substitution := by
  change SourceCoreGeneralFunctions.callablePolicy inputs.native _ = _
  rw [indexed.native, prepared.ancestry.graph.inputs.callableSelected]

theorem projector (indexed : Indexed prepared packet) :
    (policy inputs packet.original.emission.prepared packet.fuel).projectType =
      SourceCoreCompatibleDataExpressions.projectType checked := by
  unfold policy GeneralizedLocalLambdaCompilation.representation
  rw [indexed.represented]
  rfl

/-- Only an actual read supplies the source closure and its metadata view.
The native code retains the original creation packet and full active key. -/
theorem code_at_read_with_view (indexed : Indexed prepared packet)
    (function : Dynamic.Closure) (administrative : Core.Context)
    (parameters : function.parameters = packet.parameters)
    (result : function.resultType = packet.result)
    (body : function.body = packet.statements)
    (profile : checked.catalog.callableContracts = true)
    {viewRelation : TypedSource → TypedSource → Prop}
    (viewOfSource : viewRelation function.source packet.original.emission.prepared.source)
    (sourceHeader : ∃ sourceNode, function.source.lookupExpression? inputs.initializer = some sourceNode ∧
      sourceNode.form = packet.node.form)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ administrative)
      packet.original.lowered.expression (LanguageResult.resultType packet.original.lowered.type)
      prepared.layouts.definitions) :
    ∃ code : CallableIndexedLambdaValues.Code prepared function inputs.scope administrative viewRelation,
      code.compilation = context inputs packet.original.emission.prepared ∧
      code.active = packet.original.emission.prepared.substitution ∧
      code.id = inputs.initializer ∧ code.lowered = packet.original.lowered ∧
      code.policy = policy inputs packet.original.emission.prepared packet.fuel ∧
      code.lowerBody = lowerBody inputs packet.original.emission.prepared ∧
      code.fuel = packet.fuel ∧ code.descriptor.id = indexed.descriptor.id ∧
      HEq code.receipt packet.certificate ∧
      code.view = packet.original.emission.prepared.source ∧ code.reasonAt = inputs.reasonAt := by
  cases function with
  | mk functionParameters functionResult functionBody source captured sourceContext evidence =>
    simp only at parameters result body viewOfSource sourceHeader
    subst functionParameters functionResult functionBody
    obtain ⟨sourceNode, sourceFound, sourceForm⟩ := sourceHeader
    have parameterProjected := packet.certificate.parameterProjected
    have resultProjected := packet.certificate.resultProjected
    rw [indexed.projector] at parameterProjected resultProjected
    have parameterProjected := CompatibleExpressionReads.projectType_of_accepted parameterProjected
    have resultProjected := CompatibleExpressionReads.projectType_of_accepted resultProjected
    have projection : checked.catalog.project
        (.function (TypeSystem.Ty.productMany (packet.parameters.map (·.scheme.body))) packet.result) =
        .ok (CallableContract.functionType packet.certificate.parameterCore packet.certificate.resultCore) := by
      rw [packet.certificate.parameterTypes]
      simp [SourceCoreCompatibleCatalog.Catalog.project, parameterProjected, resultProjected,
        SourceCoreCompatibleCatalog.Catalog.functionType, profile, bind, Except.bind, pure, Except.pure]
    have typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ administrative)
        packet.original.lowered.expression
        (LanguageResult.resultType
          (CallableContract.functionType packet.certificate.parameterCore packet.certificate.resultCore))
        prepared.layouts.definitions := by
      rw [← packet.original.nativeType, indexed.nativeType] at typed
      exact typed
    let code : CallableIndexedLambdaValues.Code prepared
        ⟨packet.parameters, packet.result, packet.statements, source, captured, sourceContext, evidence⟩
        inputs.scope administrative viewRelation := {
      policy := policy inputs packet.original.emission.prepared packet.fuel
      lowerBody := lowerBody inputs packet.original.emission.prepared
      fuel := packet.fuel
      compilation := context inputs packet.original.emission.prepared
      active := packet.original.emission.prepared.substitution
      view := packet.original.emission.prepared.source
      viewOfSource
      id := inputs.initializer
      sourceNode
      sourceFound
      sourceForm := sourceForm.trans packet.form
      node := packet.node
      found := packet.found
      form := sourceForm.symm
      reported := packet.reported
      reasonAt := inputs.reasonAt
      lowered := packet.original.lowered
      receipt := packet.certificate
      accepted := packet.accepted
      allocationError := fun error => .sourceAllocation (reprStr error)
      allocationProfile := indexed.allocationProfile
      manifest := indexed.manifest
      expressionProfile := indexed.expressionProfile
      callables := indexed.callables
      descriptor := indexed.descriptor
      projection
      typed }
    exact ⟨code, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.refl packet.certificate, rfl, rfl⟩

/-- The original global-view API is the specialization of the shared compiler constructor. -/
theorem code_at_read (indexed : Indexed prepared packet)
    (function : Dynamic.Closure) (administrative : Core.Context)
    (parameters : function.parameters = packet.parameters)
    (result : function.resultType = packet.result)
    (body : function.body = packet.statements)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView function.source packet.original.emission.prepared.source)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ administrative)
      packet.original.lowered.expression (LanguageResult.resultType packet.original.lowered.type)
      prepared.layouts.definitions) :
    ∃ code : CallableIndexedLambdaValues.Code prepared function inputs.scope administrative,
      code.compilation = context inputs packet.original.emission.prepared ∧
      code.active = packet.original.emission.prepared.substitution ∧
      code.id = inputs.initializer ∧ code.lowered = packet.original.lowered ∧
      code.policy = policy inputs packet.original.emission.prepared packet.fuel ∧
      code.lowerBody = lowerBody inputs packet.original.emission.prepared ∧
      code.fuel = packet.fuel ∧ code.descriptor.id = indexed.descriptor.id ∧
      HEq code.receipt packet.certificate ∧
      code.view = packet.original.emission.prepared.source ∧ code.reasonAt = inputs.reasonAt := by
  obtain ⟨sourceNode, sourceFound, _, sourceForm⟩ := viewOfSource.expression packet.found
  exact indexed.code_at_read_with_view function administrative parameters result body profile viewOfSource
    ⟨sourceNode, sourceFound, sourceForm⟩ typed

end Indexed

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaGeneration
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryReadSite
/-! Finite source observations for an ordinary local read in a generalized
instance body. The original catalog and full specialization key are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryReadSite
open Core Frontend SourceInference

structure Observations (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (id : ExpressionId) where
  node : ExpressionNode
  name : String
  binder : Resolved.LocalId
  found : source.lookupExpression? id = some node
  form : node.form = .reference name (.local binder)
  requirements : node.requirements = []
  coercions : node.coercions = []
  notInitializer : locals.bindings.find? (fun binding =>
    decide (binding.caller = owner ∧ binding.initializer = id)) = none
  ordinary : locals.bindings.any (fun binding =>
    decide (binding.caller = owner ∧ binding.binder.id = binder)) = false

def observations? (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (id : ExpressionId) : Option (Observations locals owner source id) :=
  match found : source.lookupExpression? id with
  | none => none
  | some node => match form : node.form with
    | .reference name (.local binder) =>
      if requirements : node.requirements = [] then
        if coercions : node.coercions = [] then
          if notInitializer : locals.bindings.find? (fun binding =>
              decide (binding.caller = owner ∧ binding.initializer = id)) = none then
            if ordinary : locals.bindings.any (fun binding =>
                decide (binding.caller = owner ∧ binding.binder.id = binder)) = false then
              some ⟨node, name, binder, found, form, requirements, coercions, notInitializer, ordinary⟩
            else none
          else none
        else none
      else none
    | _ => none

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryReadSite
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryExpressionProfile
/-! Finite ordinary expression profiles for the real materialized lambda view.
The tree contains only source metadata, never execution or compiler laws. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryExpressionProfile
open Core Frontend SourceInference

inductive Form : ExpressionForm → Prop where
  | literal {form} (atomic : CompatibleExpressionLiterals.Atomic form) : Form form
  | read (name : String) (binder : Resolved.LocalId) : Form (.reference name (.local binder))
  | group (inner : ExpressionId) : Form (.group inner)
  | pair (left right : ExpressionId) : Form (.tuple [left, right])

structure Site (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (id : ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : Form node.form
  coercions : node.coercions = []
  requirements : (match node.form with | .integerLiteral .. => True | _ => node.requirements = [])
  notInitializer : locals.bindings.find? (fun binding =>
    decide (binding.caller = owner ∧ binding.initializer = id)) = none
  ordinary : ∀ name binder, node.form = .reference name (.local binder) →
    locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false

private def form? (form : ExpressionForm) : Option (PLift (Form form)) :=
  match form with
  | .integerLiteral literal resolution => some ⟨.literal (.integer literal resolution)⟩
  | .reference name (.builtinBoolean value) => some ⟨.literal (.bool name value)⟩
  | .literal literal => some ⟨.literal (.word literal)⟩
  | .tuple [] => some ⟨.literal .unit⟩
  | .reference name (.local binder) => some ⟨.read name binder⟩
  | .group inner => some ⟨.group inner⟩
  | .tuple [left, right] => some ⟨.pair left right⟩
  | _ => none

private def ordinary? (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (node : ExpressionNode) :
    Option (PLift (∀ name binder, node.form = .reference name (.local binder) →
      locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false)) := by
  cases form : node.form
  case reference name resolution =>
    cases resolution
    case «local» binder =>
      exact if ordinary : locals.bindings.any (fun binding =>
          decide (binding.caller = owner ∧ binding.binder.id = binder)) = false then
        some ⟨by
          intro actual actualBinder same
          obtain ⟨rfl, resolution⟩ := ExpressionForm.reference.inj same
          cases resolution
          exact ordinary⟩
      else none
    all_goals exact some ⟨by intro name binder same; simp at same⟩
  all_goals exact some ⟨by intro name binder same; simp at same⟩

private def requirements? (node : ExpressionNode) :
    Option (PLift (match node.form with | .integerLiteral .. => True | _ => node.requirements = [])) :=
  if empty : node.requirements = [] then some ⟨by split <;> simp_all⟩
  else match node.form with | .integerLiteral .. => some ⟨True.intro⟩ | _ => none

def site? (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (id : ExpressionId) :
    Option (Site locals owner source id) := do
  match found : source.lookupExpression? id with
  | none => none
  | some node => do
    let ⟨form⟩ ← form? node.form
    if coercions : node.coercions = [] then do
      let ⟨requirements⟩ ← requirements? node
      if notInitializer : locals.bindings.find? (fun binding =>
          decide (binding.caller = owner ∧ binding.initializer = id)) = none then do
        let ⟨ordinary⟩ ← ordinary? locals owner node
        pure ⟨node, found, form, coercions, requirements, notInitializer, ordinary⟩
      else none
    else none

inductive Tree (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) : ExpressionId → Prop where
  | literal {id} (site : Site locals owner source id)
      (atomic : CompatibleExpressionLiterals.Atomic site.node.form) : Tree locals owner source id
  | read {id name binder} (site : Site locals owner source id)
      (form : site.node.form = .reference name (.local binder)) : Tree locals owner source id
  | group {id inner} (site : Site locals owner source id) (form : site.node.form = .group inner)
      (child : Tree locals owner source inner) : Tree locals owner source id
  | pair {id left right} (site : Site locals owner source id) (form : site.node.form = .tuple [left, right])
      (first : Tree locals owner source left) (second : Tree locals owner source right) : Tree locals owner source id

variable {locals : SourceCoreLocalPolymorphism.Catalog} {owner : SourceCoreLocalPolymorphism.Key}
  {source : TypedSource} {id : ExpressionId}

theorem Tree.site (tree : Tree locals owner source id) : Nonempty (Site locals owner source id) := by
  cases tree <;> exact ⟨‹_›⟩

theorem Tree.syntax (tree : Tree locals owner source id) : CompatibleExpressionProducts.Syntax source id := by
  induction tree with
  | literal site atomic => exact .literal site.found atomic
  | read site form => exact .read site.found form
  | group site form _ ih => exact .group site.found form ih
  | pair site form _ _ left right => exact .pair site.found form left right

theorem Tree.children (tree : Tree locals owner source id) {node : ExpressionNode} {child : ExpressionId}
    (found : source.lookupExpression? id = some node)
    (member : (.expression child : NodeId) ∈ node.form.references) : Tree locals owner source child := by
  cases tree with
  | literal site atomic =>
    cases Option.some.inj (site.found.symm.trans found)
    generalize shape : site.node.form = form at atomic
    cases atomic <;> simp [shape, ExpressionForm.references] at member
  | read site form =>
    cases Option.some.inj (site.found.symm.trans found)
    simp [form, ExpressionForm.references] at member
  | group site form subtree =>
    cases Option.some.inj (site.found.symm.trans found)
    simp only [form, ExpressionForm.references, List.mem_singleton, NodeId.expression.injEq] at member
    exact member ▸ subtree
  | pair site form first second =>
    cases Option.some.inj (site.found.symm.trans found)
    simp [form, ExpressionForm.references] at member
    rcases member with rfl | rfl
    · exact first
    · exact second

def tree? (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (Tree locals owner source id))
  | 0, _ => none
  | fuel + 1, id => do
    let site ← site? locals owner source id
    match form : site.node.form with
    | .integerLiteral literal resolution => pure ⟨.literal site (form ▸ .integer literal resolution)⟩
    | .reference name (.builtinBoolean value) => pure ⟨.literal site (form ▸ .bool name value)⟩
    | .literal literal => pure ⟨.literal site (form ▸ .word literal)⟩
    | .tuple [] => pure ⟨.literal site (form ▸ .unit)⟩
    | .reference _ (.local _) => pure ⟨.read site form⟩
    | .group inner => do
      let ⟨child⟩ ← tree? locals owner source fuel inner
      pure ⟨.group site form child⟩
    | .tuple [left, right] => do
      let ⟨first⟩ ← tree? locals owner source fuel left
      let ⟨second⟩ ← tree? locals owner source fuel right
      pure ⟨.pair site form first second⟩
    | _ => none

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryExpressionProfile
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyProfile
/-! Materialized ordinary bodies reuse the common finite statement scanner.
The profile retains the original lambda and every expression-tree receipt.
Ordinary declarations, scoped blocks and conditionals are scanned structurally;
assignments, nested generalized declarations and loops are outside this finite lexical grammar. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyProfile
open Core Frontend SourceInference

abbrev Approved (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceCoreLocalPolymorphism.Key)
    (source : TypedSource) (id : ExpressionId) : Prop :=
  GeneralizedLocalOrdinaryExpressionProfile.Tree locals owner source id

structure Profile (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (initializer : ExpressionId) where
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  found : source.lookupExpression? initializer = some node
  form : node.form = .lambda parameters result body
  scan : ScopedSourceBodyAdmission.Scan source (Approved locals owner source) result true body
  lexical : CellAwareOrdinaryBodySyntax.lexicalOnly source (source.nodes.length + 1) body = true

def profile? (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (initializer : ExpressionId) :
    Option (Profile locals owner source initializer) :=
  match found : source.lookupExpression? initializer with
  | none => none
  | some node => match form : node.form with
    | .lambda parameters result body => do
      let ⟨scan⟩ ← ScopedSourceBodyAdmission.scan? source
        (fun id => GeneralizedLocalOrdinaryExpressionProfile.tree? locals owner source (source.nodes.length + 1) id)
        result (source.nodes.length + 1) true body
      if lexical : CellAwareOrdinaryBodySyntax.lexicalOnly source (source.nodes.length + 1) body = true then
        pure ⟨node,parameters,result,body,found,form,scan,lexical⟩
      else none
    | _ => none

theorem Profile.packet_body {inputs : GeneralizedLocalInstanceCompilation.Inputs}
    {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw)
    (profile : Profile inputs.locals inputs.current.owner packet.original.emission.prepared.source inputs.initializer) :
    profile.parameters = packet.parameters ∧ profile.result = packet.result ∧ profile.body = packet.statements := by
  have same := Option.some.inj (profile.found.symm.trans packet.found)
  exact ExpressionForm.lambda.inj (profile.form.symm.trans ((congrArg ExpressionNode.form same).trans packet.form))

theorem Profile.packet_scan {inputs : GeneralizedLocalInstanceCompilation.Inputs}
    {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw)
    (profile : Profile inputs.locals inputs.current.owner packet.original.emission.prepared.source inputs.initializer) :
    ScopedSourceBodyAdmission.Scan packet.original.emission.prepared.source
      (Approved inputs.locals inputs.current.owner packet.original.emission.prepared.source)
      packet.result true packet.statements := by
  obtain ⟨_,result,body⟩ := profile.packet_body packet
  simpa only [result,body] using profile.scan

theorem Profile.packet_lexical {inputs : GeneralizedLocalInstanceCompilation.Inputs}
    {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw)
    (profile : Profile inputs.locals inputs.current.owner packet.original.emission.prepared.source inputs.initializer) :
    CellAwareOrdinaryBodySyntax.lexicalOnly packet.original.emission.prepared.source
      (packet.original.emission.prepared.source.nodes.length + 1) packet.statements = true := by
  obtain ⟨_,_,body⟩ := profile.packet_body packet
  simpa only [body] using profile.lexical

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyProfile
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfile
/-! Bounded instances retain the original lambda and its finite lexical body.
The common scanner carries each original expression and declaration receipt;
no body execution law is part of the profile. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfile
abbrev Profile := GeneralizedLocalOrdinaryBodyProfile.Profile
abbrev profile? := GeneralizedLocalOrdinaryBodyProfile.profile?
end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfile
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalScopeDeclarations
/-! Genuine captured declarations survive the same flexible substitution as
the materialized Source closure. Binder identities and declaration order stay
fixed; source schemes and the lexical context are substituted together. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalScopeDeclarations
open Core Frontend SourceInference TypeSystem
open SourceCoreDataPlaces

private theorem instructions (substitution : Substitution) (items : List MatchPatternInstruction) :
    instructionBinders (items.map (MatchPatternInstruction.applySubstitution substitution)) =
      (instructionBinders items).map (TypedBinder.applySubstitution substitution) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simpa [instructionBinders, MatchPatternInstruction.applySubstitution] using ih

private theorem pattern (substitution : Substitution) (item : TypedMatchPattern) :
    patternBinders (item.applySubstitution substitution) =
      (patternBinders item).map (TypedBinder.applySubstitution substitution) := by
  cases form : item.resolution <;>
    simp [patternBinders, TypedMatchPattern.applySubstitution, MatchPatternResolution.applySubstitution, form, instructions]

private theorem for_items (substitution : Substitution) (items : List ForItemForm) :
    (items.map (ForItemForm.applySubstitution substitution)).filterMap (fun | .letDecl binder _ => some binder | _ => none) =
      (items.filterMap (fun | .letDecl binder _ => some binder | _ => none)).map (TypedBinder.applySubstitution substitution) := by
  induction items with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [ForItemForm.applySubstitution, ih]

theorem declared (substitution : Substitution) (source : TypedSource) :
    declaredBinders (source.applySubstitution substitution) =
      (declaredBinders source).map (TypedBinder.applySubstitution substitution) := by
  simp only [declaredBinders, TypedSource.applySubstitution, List.map_append, List.flatMap_map, List.map_flatMap]
  congr 1
  apply congrArg (fun f : Node → List TypedBinder => source.nodes.flatMap f)
  funext node
  cases node with
  | expression node =>
    cases form : node.form <;> simp [Node.applySubstitution, ExpressionNode.applySubstitution, ExpressionForm.applySubstitution, form]
  | statement node =>
    cases form : node.form <;>
      simp [Node.applySubstitution, StatementNode.applySubstitution, StatementForm.applySubstitution, form,
        List.filterMap_append, MatchResolution.applySubstitution, List.flatMap_map,
        List.map_flatMap, TypedMatchCase.applySubstitution, pattern]
    rename_i initial condition post body
    have first := for_items substitution initial
    have second := for_items substitution post
    simp only [List.filterMap_map] at first second
    exact congr (congrArg List.append first) second

theorem root (substitution : Substitution) (source : TypedSource) (id : Resolved.LocalId) :
    rootBinder (source.applySubstitution substitution) id =
      (rootBinder source id).map (TypedBinder.applySubstitution substitution) := by
  unfold rootBinder
  rw [declared]
  simp only [TypedSource.applySubstitution]
  by_cases owner : id.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte]
    have selected : ((declaredBinders source).map (TypedBinder.applySubstitution substitution)).filter
        (fun binder => decide (binder.id = id)) =
        ((declaredBinders source).filter (fun binder => decide (binder.id = id))).map
          (TypedBinder.applySubstitution substitution) := by
      simp only [List.filter_map, Function.comp_def, TypedBinder.applySubstitution_id]
    rw [selected]
    cases entries : (declaredBinders source).filter (fun binder => decide (binder.id = id)) with
    | nil => rfl
    | cons binder rest =>
      cases rest with
      | nil =>
        simp only [List.map_cons, List.map_nil, FlexibleSubstitution.applyTypedBinder_scheme_quantified,
          FlexibleSubstitution.applyTypedBinder_schemeRequirements, List.isEmpty_map]
        split <;> split <;> rfl
      | cons next remaining => rfl
  · simp [owner, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.map]

private theorem lookup (substitution : Substitution)
    {locals : Resolved.LocalScope Scheme} {id : Resolved.LocalId} {scheme : Scheme}
    (found : Resolved.LocalScope.Lookup locals id scheme) :
    Resolved.LocalScope.Lookup (FlexibleSubstitution.applyLocals substitution locals) id (scheme.apply substitution) := by
  induction found with
  | head => exact .head
  | tail different tail ih => exact .tail different ih

theorem scope {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context) (substitution : Substitution) :
    CompatibleExpressionReads.ScopeDeclarations (source.applySubstitution substitution) scope
      (FlexibleSubstitution.closeContext substitution context) := by
  intro id declared index type selected authentic
  rw [root] at authentic
  cases original : rootBinder source id with
  | error error => simp only [original, Except.map] at authentic; cases authentic
  | ok binder =>
    simp only [original, Except.map] at authentic
    cases authentic
    simpa only [FlexibleSubstitution.applyTypedBinder_scheme, FlexibleSubstitution.closeContext, FlexibleSubstitution.applyContext] using lookup substitution (declarations _ _ _ _ selected original)

theorem materialized {function : Dynamic.GeneralizedClosure} {scope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source scope function.definitionContext)
    (substitution : Substitution) (evidence : Dynamic.EvidenceEnvironment) :
    CompatibleExpressionReads.ScopeDeclarations (function.instantiate substitution evidence).source scope
      (function.instantiate substitution evidence).context := by
  exact GeneralizedLocalScopeDeclarations.scope (context := localSchemeInitializerContext function.definitionContext function.binder) declarations substitution

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalScopeDeclarations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDiagnosticIssuer
/-! Generalized allocation retains the exact compiler diagnostic issuer and
callback. Later body failures use the actual receiving table to decode it. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDiagnosticIssuer
open Core Frontend SourceInference

/-- The original accepted named callback retains its own diagnostic inventory. -/
def Receipt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (inputs : GeneralizedLocalInstanceCompilation.Inputs) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    prepared.base.diagnostics = some issued ∧
    inputs.reasonAt = issued.program.reasonAt inputs.current.owner ∧
    ∃ own : SourceCoreProgramFaultSites.Function,
      issued.program.base.find? inputs.current.owner = some own

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDiagnosticIssuer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues
/-! Stored generalized instances retain their literal compiler packet, mapped
captures and actual lexical snapshot. They become ordinary Source closures
only when a read supplies its real substitution and evidence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalDescriptorOrigin (Origin)
open CallableIndexedHistory

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
  {packet : Packet inputs candidate raw}

def referenceIndex (_indexed : Indexed prepared packet) : Nat :=
  SourceCoreCallableIndexedAncestry.creationReferenceIndex
    (GeneralizedLocalLambdaCompilation.context inputs packet.original.emission.prepared) inputs.scope

def body (indexed : Indexed prepared packet) : Core.Expr :=
  SourceCoreCallableIndexedFrames.withFrame (.var (referenceIndex indexed + 2))
    (SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table prepared.ancestry.layout.frame
      indexed.descriptor.id (.var 1) (.loadCell (.var (referenceIndex indexed + 2))))
    (packet.certificate.rawBody.weakenAt 1)

def value (indexed : Indexed prepared packet) (embedding : Renaming)
    (native : NativeFrame) (actual : Core.Environment) : Core.Value :=
  .pair (.pair (.inLeft .word .unit)
    (.closure packet.certificate.parameterCore (LanguageResult.resultType packet.certificate.resultCore)
      ((body indexed).rename embedding.lift.lift)
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame native :: actual)))
    (.word indexed.descriptor.id)

/-- Creation retains a static native typing derivation and its actual capture
representation. There is no Source body execution or future read dictionary. -/
inductive Represents (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) : Dynamic.GeneralizedClosure →
      SourceCoreLocalPolymorphism.Binding → Substitution → SourceCoreLocalPolymorphism.Instance → Core.Value → Prop where
  | retained {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
      {lexical : Substitution} {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
      {raw : Core.Expr} {actual : Core.Environment}
      (packet : Packet inputs candidate raw) (indexed : Indexed prepared packet)
      (bodyProfile : GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner
        packet.original.emission.prepared.source inputs.initializer)
      (sameLexical : indexed.lexical = lexical)
      (owner : inputs.current.owner = binding.caller)
      (initializer : inputs.initializer = binding.initializer)
      (candidateSource : candidate.origin.source = binding.source)
      (candidateBinder : candidate.origin.binder.id = binding.binder.id)
      (descriptorSource : function.source = binding.source)
      (origin : Origin prepared function binding lexical)
      (namedLexical : lexical = [])
      (namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩)
      (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
      (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
      (ownership : LocalIdentityOwnership function.source)
      (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
      (frameLocation : Core.Location)
      (frameReference : captured.canonical[referenceIndex indexed]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
      (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
        raw candidate.type prepared.layouts.definitions)
      (runtimeTyped : RuntimeValueHasType world (value indexed captured.embedding origin.native actual)
        candidate.type prepared.layouts.definitions) :
      Represents prepared mapping world function binding lexical candidate
        (value indexed captured.embedding origin.native actual)

def model (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    GeneralizedLocalDescriptorHeap.InstanceModel prepared.layouts.definitions where
  locals := prepared.base.locals
  Origin := fun function binding lexical => Nonempty (Origin prepared function binding lexical)
  Represents := Represents prepared
  runtime_hasType := by
    intro mapping world function binding lexical candidate native represented
    cases represented with
    | retained _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ typed => exact typed
  extend := by
    intro mapping futureMapping world futureWorld function binding lexical candidate native represented maps worlds
    cases represented with
    | retained packet indexed bodyProfile lexical owner initializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer frameLocation frameReference typed runtimeTyped =>
        exact .retained packet indexed bodyProfile lexical owner initializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata (captured.extend maps worlds) declarations ownership issuer frameLocation frameReference typed
          (runtimeTyped.weaken worlds)

/-- The literal snapshot lambda reads the actual lexical reference and leaves
the whole native store unchanged. -/
theorem formation_evaluates (indexed : Indexed prepared packet)
    {mapping : LocationMap} {world : StoreTyping} {source : Dynamic.Environment} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope source actual)
    {native : NativeFrame} {store : Store} {location : Core.Location}
    (reference : captured.canonical[referenceIndex indexed]? =
      some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame native)) :
    Evaluates actual store (raw.rename captured.embedding) (value indexed captured.embedding native actual) store := by
  conv => arg 3; rw [indexed.emitted]
  exact .pair (.pair (.inLeft .unit) (.letE (.loadCell (.var (captured.agrees reference)) read) .lambda)) .word

/-- Runtime typing is derived from the accepted raw expression and its actual
execution in this same store. It does not assume an instance body law. -/
theorem formation (indexed : Indexed prepared packet)
    (bodyProfile : GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner
      packet.original.emission.prepared.source inputs.initializer)
    {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {actual : Core.Environment}
    (sameLexical : indexed.lexical = lexical) (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (candidateSource : candidate.origin.source = binding.source)
    (candidateBinder : candidate.origin.binder.id = binding.binder.id)
    (descriptorSource : function.source = binding.source)
    (origin : Origin prepared function binding lexical)
    (namedLexical : lexical = [])
    (namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩)
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
      (ownership : LocalIdentityOwnership function.source)
      (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[referenceIndex indexed]? =
      some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding) (value indexed captured.embedding origin.native actual) store ∧
    Represents prepared mapping world function binding lexical candidate
      (value indexed captured.embedding origin.native actual) := by
  have evaluated := formation_evaluates indexed captured reference read
  obtain ⟨future, _, finalStored, outputTyped⟩ :=
    evaluation_preserves_type evaluated (typed.rename captured.respects) captured.typed stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  exact ⟨evaluated, .retained packet indexed bodyProfile sameLexical owner initializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer location reference typed outputTyped⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadView
/-! The emitted read wrapper saves the caller at the read occurrence. Later
application installs that saved view before invoking the original carrier and
restores the actual application caller, including on language failure. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadView
open Core Frontend ReadOnly
open SourceCoreCallableIndexedFrames SourceCoreCallableIndexedAncestry
open CallableIndexedHistory

def value (layout : SourceCoreCallableIndexedFrames.Layout) (parameter result : Ty) (id target : Word)
    (referenceIndex : Nat) (embedding : Renaming) (caller : NativeFrame)
    (identity payload : Value) (environment : Environment) : Value :=
  .pair (.pair identity
    (.closure parameter (LanguageResult.resultType result)
      ((viewBody layout id target referenceIndex).rename embedding.lift.lift.lift)
      (encode layout caller :: .pair (.pair identity payload) (.word target) :: environment))) (.word target)

theorem formation {layout : SourceCoreCallableIndexedFrames.Layout} {parameter result : Ty} {id target : Word}
    {referenceIndex location : Nat} {embedding : Renaming} {caller : NativeFrame}
    {identity payload : Value} {environment : Environment} {before after : Store} {readCode : Expr}
    (read : Evaluates environment before (readCode.rename embedding)
      (.inRight .word (.pair (.pair identity payload) (.word target))) after)
    (reference : environment[embedding referenceIndex]? = some (.cellRef layout.type location))
    (snapshot : after.read? location = some (encode layout caller)) :
    Evaluates environment before
      ((viewLower layout parameter result id target referenceIndex readCode).rename embedding)
      (.inRight .word (value layout parameter result id target referenceIndex embedding caller identity payload environment)) after := by
  apply Evaluates.caseRight read
  apply Evaluates.letE (.loadCell (.var (by simpa [Renaming.lift] using reference)) snapshot)
  exact .inRight (.pair (.pair (.first (.first (.var rfl))) .lambda) (.second (.var rfl)))

private theorem body_rename (layout : SourceCoreCallableIndexedFrames.Layout) (id target : Word) (referenceIndex : Nat) (embedding : Renaming) :
    (viewBody layout id target referenceIndex).rename embedding.lift.lift.lift =
      viewBody layout id target (embedding referenceIndex) := by
  simp only [viewBody, NamedCalls.withFrame_rename, CallableIndexedRenaming.readView, Expr.rename, Renaming.lift]

/-- The returned wrapper is typed from the actual stored carrier and the
read-time environment. No typing relation for an arbitrary embedding is assumed. -/
theorem runtime_hasType {definitions : DataEnvironment} {world : StoreTyping}
    {layout : SourceCoreCallableIndexedFrames.Layout} {parameter result : Ty} {id target : Word}
    {referenceIndex location : Nat} {embedding : Renaming} {caller : NativeFrame}
    {identity payload : Value} {environment : Environment} {context : Core.Context}
    (registered : layout.Registered definitions)
    (carrier : RuntimeValueHasType world (.pair (.pair identity payload) (.word target))
      (CallableContract.functionType parameter result) definitions)
    (environments : RuntimeEnvironmentHasTypes world environment context definitions)
    (reference : environment[embedding referenceIndex]? = some (.cellRef layout.type location)) :
    RuntimeValueHasType world
      (value layout parameter result id target referenceIndex embedding caller identity payload environment)
      (CallableContract.functionType parameter result) definitions := by
  have typedReference : context[embedding referenceIndex]? = some (.cell layout.type) := by
    rw [← environments.type_tags]
    simp only [List.getElem?_map, reference, Option.map_some, Value.type]
  have frameTyped : RuntimeValueHasType world (encode layout caller) layout.type definitions := by
    exact SourceCoreCallableIndexedFrames.encode_runtime_typed world registered caller
  have original := carrier
  cases carrier with
  | pair tagged contract =>
    cases tagged with
    | pair identityTyped _ =>
      refine .pair (.pair identityTyped (.closure (.cons frameTyped (.cons original environments)) ?_)) contract
      rw [body_rename]
      unfold viewBody
      apply SourceCoreCallableContextFrames.withFrame_hasType
      · exact .var (by simpa only [List.getElem?_cons_succ] using typedReference)
      · exact SourceCoreCallableIndexedDispatch.readView_hasType registered id target (.var rfl)
      · exact .apply (.second (.first (.var rfl))) (.var rfl)

/-- The wrapper exposes one call to the retained inner lambda. Its saved
read-time frame and the current caller are different values throughout. -/
theorem agreement {layout : SourceCoreCallableIndexedFrames.Layout} {parameter result : Ty} {id target : Word}
    {referenceIndex location : Nat} {embedding : Renaming} {caller : NativeFrame}
    {identity : Value} {innerBody : Expr} {innerEnvironment environment : Environment}
    {argument saved : Value} {store : Store}
    (reference : environment[embedding referenceIndex]? = some (.cellRef layout.type location))
    (current : store.read? location = some saved) :
    let payload := Value.closure parameter (LanguageResult.resultType result) innerBody innerEnvironment
    let original := Value.pair (.pair identity payload) (.word target)
    let entry := argument :: encode layout caller :: original :: environment
    let next := encode layout (SourceCoreCallableIndexedDispatch.readFrame id target caller)
    (∀ {output finalStore}, Evaluates (argument :: innerEnvironment) (store.set location next)
      innerBody output finalStore →
      Evaluates entry store ((viewBody layout id target referenceIndex).rename embedding.lift.lift.lift)
        output (finalStore.set location saved)) ∧
    (∀ {output finalStore},
      Evaluates entry store ((viewBody layout id target referenceIndex).rename embedding.lift.lift.lift)
        output finalStore →
      ∃ bodyStore, Evaluates (argument :: innerEnvironment) (store.set location next) innerBody output bodyStore ∧
        finalStore = bodyStore.set location saved) := by
  let payload := Value.closure parameter (LanguageResult.resultType result) innerBody innerEnvironment
  let original := Value.pair (.pair identity payload) (.word target)
  let entry := argument :: encode layout caller :: original :: environment
  let next := encode layout (SourceCoreCallableIndexedDispatch.readFrame id target caller)
  have selected : DataEquality.Selects entry (.var (embedding referenceIndex + 3)) (.cellRef layout.type location) :=
    .var (by simpa [entry] using reference)
  have nextEval : Evaluates (saved :: entry) store
      ((SourceCoreCallableIndexedDispatch.readView layout id target (.var 1)).weakenAt 0) next store := by
    rw [CallableIndexedRenaming.readView_weaken]
    simpa only [Expr.weakenAt, Nat.zero_le, ↓reduceIte] using CallableIndexedContextFrames.readView_evaluates id target
      (show DataEquality.Selects (saved :: entry) (.var 2) (encode layout caller) from .var rfl) store
  rw [body_rename]
  constructor
  · intro output finalStore evaluated
    apply CallableContextFrames.withFrame_evaluates selected current nextEval
    simp only [Expr.weakenAt, Nat.zero_le, ↓reduceIte]
    exact .apply (.second (.first (.var rfl))) (.var rfl) evaluated
  · intro output finalStore evaluated
    obtain ⟨installed, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
      CallableContextFrames.withFrame_reflects selected current evaluated
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEval nextEvaluation
    simp only [Expr.weakenAt, Nat.zero_le, ↓reduceIte] at bodyEvaluation
    cases bodyEvaluation with
    | apply callee arg body =>
      obtain ⟨sameClosure, rfl⟩ := evaluation_deterministic callee
        (show Evaluates (.unit :: saved :: entry) (store.set location next)
          (.second (.first (.var 4))) payload (store.set location next) from .second (.first (.var rfl)))
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj sameClosure
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic arg (Evaluates.var (show
        (.unit :: saved :: entry)[2]? = some argument from rfl))
      exact ⟨bodyStore, body, finalEq⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadView
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalSubtree
/-! Real lexical discovery stays inside the initializer's actual occurrence
subtree. A closed preserved earlier subtree then recovers complete records. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalSubtree
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceInferenceSoundness

private theorem lexical_edge {source : TypedSource} {parent child : NodeId}
    (unique : NodeOccurrencesUnique source) (present : parent ∈ nodeIds source)
    (member : child ∈ localLambdaLexicalChildren source parent) :
    DirectChild source parent child := by
  obtain ⟨original, originalMember, originalId⟩ := List.mem_map.mp present
  obtain ⟨node, found, reference⟩ := localLambdaLexicalChildren_origin member
  have originalFound := lookupNode?_complete unique originalMember
    (congrArg NodeId.occurrenceId originalId)
  have same := Option.some.inj (found.symm.trans originalFound)
  subst node
  exact ⟨original, ⟨originalMember, originalId⟩, reference⟩

/-- The pruned lexical traversal uses actual source edges, including every
structured statement body that it visits. -/
theorem path_descends {source : TypedSource} {root node : NodeId} {roots : List NodeId}
    (unique : NodeOccurrencesUnique source) (closed : ChildEdgesExist source)
    (rootEdges : ∀ child ∈ roots, DirectChild source root child)
    (path : LocalLambdaLexicalPath source roots node) :
    Descends source root node ∧ node ∈ nodeIds source := by
  induction path with
  | root member =>
      have edge := rootEdges _ member
      obtain ⟨parent, contains, reference⟩ := edge
      exact ⟨.direct ⟨parent, contains, reference⟩, closed parent contains.1 _ reference⟩
  | child previous member ih =>
      have edge := lexical_edge unique ih.2 member
      obtain ⟨parent, contains, reference⟩ := edge
      exact ⟨ih.1.trans (.direct ⟨parent, contains, reference⟩),
        closed parent contains.1 _ reference⟩

/-- A complete record selected from this actual lambda body lies below the
same initializer identity used by the discovered instance. -/
theorem body_node_descends {source : TypedSource} {localInstance : LocalLambdaInstance}
    {nodes : List Node} {node : Node}
    (unique : NodeOccurrencesUnique source) (closed : ChildEdgesExist source)
    (accepted : localLambdaBodyNodes source localInstance = .ok nodes)
    (member : node ∈ nodes) :
    Descends source (.expression localInstance.binding.initializer) node.id := by
  obtain ⟨initializer, parameters, resultType, body, found, form, path⟩ :=
    localLambdaBodyNodes_path accepted member
  have contains := lookupExpression?_sound found
  apply (path_descends unique closed ?_ path).1
  intro child childMember
  refine ⟨.expression initializer, ⟨contains.1, congrArg NodeId.expression contains.2⟩, ?_⟩
  simpa only [nodeChildIds, Node.references, form, ExpressionForm.references] using childMember

/-- Earlier closure and genuine subtree preservation recover the complete
record, including a local read's exact binder target. -/
theorem body_node_before {before source : TypedSource} {localInstance : LocalLambdaInstance}
    {nodes : List Node} {node : Node}
    (unique : NodeOccurrencesUnique source) (sourceClosed : ChildEdgesExist source)
    (preserved : RawSubtreePreserved before source (.expression localInstance.binding.initializer))
    (beforeClosed : ChildEdgesExist before)
    (present : NodeId.expression localInstance.binding.initializer ∈ nodeIds before)
    (accepted : localLambdaBodyNodes source localInstance = .ok nodes) (member : node ∈ nodes) :
    node ∈ before.nodes :=
  preserved.node_inverse beforeClosed present unique (localLambdaBodyNodes_members accepted member)
    (.inr (body_node_descends unique sourceClosed accepted member))

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalSubtree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaMetadata
/-! A successful native generalized initializer cannot retain evidence on its
lambda header. The actual coercion spine and the compiler's decreasing fuel
supply this fact before the existing lambda packet is constructed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaMetadata
open Core Frontend SourceInference SourceCoreLocalPolymorphism
open GeneralizedLocalInstanceCompilation (Inputs Receipt)
open GeneralizedLocalLambdaCompilation

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem emit_inRight {reason : Word} {input raw : Expr}
    {calls : List CallableCoercionSpine.Call}
    (shape : CallableCoercionSpine.emit reason input calls = .inRight .word raw) :
    calls = [] := by
  induction calls generalizing input with
  | nil => rfl
  | cons head tail ih =>
    have empty := ih shape
    subst empty
    simp [CallableCoercionSpine.emit, SourceCoreCalls.call, LanguageResult.bind] at shape

/-- Actual successful output coercions cannot produce an unwrapped successful
closure expression unless the original ordered coercion list is empty. -/
theorem coercions_empty {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {context : SourceCoreFunctions.Context} {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceCompilationPlan.EvidenceEnvironment} {scope : SourceCoreBasic.Scope}
    {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : SourceCoreBasic.LoweredExpr} {steps : List CoercionStep} {raw : Expr}
    (accepted : SourceCoreEvidence.applyCoercions program project context caller available scope node policy
      input steps = .ok output)
    (shape : output.expression = .inRight .word raw) : steps = [] := by
  obtain ⟨calls, spine⟩ := CallableCoercionSpine.of_accepted accepted
  have empty := emit_inRight (spine.code.symm.trans shape)
  have length := spine.length
  rw [empty] at length
  cases steps <;> simp_all

/-- Replacing the expression found by the actual first-match lookup preserves
that lookup. Occurrence uniqueness is not needed for this local operation. -/
theorem replaced_lookup {source : TypedSource} {id : ExpressionId} {node replacement : ExpressionNode}
    (found : source.lookupExpression? id = some node) (same : replacement.id = node.id) :
    (SourceCoreEvidence.withNode source replacement).lookupExpression? id = some replacement := by
  have nodeId : node.id = id := (lookupExpression?_sound found).2
  have replacementId : replacement.id = id := same.trans nodeId
  rcases source with ⟨owner, inputs, roots, nodes⟩
  unfold SourceCoreEvidence.withNode TypedSource.lookupExpression? TypedSource.lookupNode? at *
  dsimp only at *
  induction nodes with
  | nil => cases found
  | cons current rest ih =>
    cases current with
    | statement statement =>
      cases hit : decide ((Node.statement statement).occurrenceId = id.occurrence)
      · simp only [List.find?_cons, hit] at found
        simpa only [List.map_cons, List.find?_cons, hit] using ih found
      · simp only [List.find?_cons, hit] at found
        cases found
    | expression expression =>
      by_cases hit : expression.id = id
      · subst hit
        simp [List.map_cons, replacementId, Node.occurrenceId, Node.id,
          NodeId.occurrenceId]
      · have occurrence : expression.id.occurrence ≠ id.occurrence := by
          intro equal
          exact hit (congrArg ExpressionId.mk equal)
        have different : expression.id ≠ replacement.id := by simpa only [replacementId] using hit
        simp only [List.find?_cons, Node.occurrenceId, Node.id, NodeId.occurrenceId,
          occurrence, decide_false] at found
        simpa only [List.map_cons, different, ↓reduceIte, List.find?_cons, Node.occurrenceId,
          Node.id, NodeId.occurrenceId, occurrence, decide_false] using ih found

private theorem special_lambda (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared)
    (policyFuel budget : Nat) (child : SourceCoreFunctions.ExpressionLowerer)
    {source : TypedSource} {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {reasonAt : ExpressionId → Word}
    (found : source.lookupExpression? inputs.initializer = some node)
    (form : node.form = .lambda parameters result body) :
    special inputs prepared policyFuel (context inputs prepared) child budget source scope
      inputs.initializer reasonAt =
    SourceCoreEvidence.lowerWithProjector inputs.program
      (representation inputs prepared).expressions.projectType prepared.caller (context inputs prepared)
      child budget source scope inputs.initializer reasonAt
      (SourceCoreGeneralFunctions.callablePolicy inputs.native prepared.substitution) := by
  have skipped : (inputs.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context inputs prepared).owner ∧ binding.initializer = inputs.initializer))).filter
      (fun _ => decide (some inputs.initializer ≠ some inputs.initializer)) = none := by simp
  simp only [special, SourceCoreGeneralFunctions.contextualSource, found, form,
    bind, Except.bind, pure, Except.pure, skipped]
  cases SourceCoreEvidence.lowerWithProjector inputs.program
    (representation inputs prepared).expressions.projectType prepared.caller (context inputs prepared)
    child budget source scope inputs.initializer reasonAt
    (SourceCoreGeneralFunctions.callablePolicy inputs.native prepared.substitution) with
  | error error => rfl
  | ok value => cases value <;> rfl

private theorem evidence_none {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {caller : SourceSpecialization.SpecializedFunction} {context : SourceCoreFunctions.Context}
    {child : SourceCoreFunctions.ExpressionLowerer} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreBasic.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (accepted : SourceCoreEvidence.lowerWithProjector program project caller context child fuel source scope
      id reasonAt policy = .ok none) : node.requirements = [] ∧ node.coercions = [] := by
  unfold SourceCoreEvidence.lowerWithProjector at accepted
  simp only [found, form, bind, Except.bind, pure, Except.pure] at accepted
  cases ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node with
  | none => simp [ordinary] at accepted
  | some requirements =>
    simp only [ordinary, Bool.not_false,
      Bool.and_true, Bool.or_false] at accepted
    split at accepted
    · rename_i empty
      have e : node.coercions = [] ∧ node.requirements = [] := by simpa using empty
      exact e.symm
    · by_cases valid : node.hasValidCoercionPath = true
      · by_cases owner : caller.key = context.owner
        · simp only [valid, owner, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
          split at accepted
          · cases accepted
          · split at accepted
            · cases accepted
            · split at accepted
              · cases accepted
              · split at accepted
                · cases accepted
                · split at accepted
                  · cases accepted
                  · split at accepted
                    · cases accepted
                    · split at accepted <;> cases accepted

        · simp [valid, owner] at accepted
      · simp [valid] at accepted


/-- The same actual contextual policy is fixed while its remaining expression
fuel decreases. Only the lambda currently being emitted is examined. -/
theorem lowered_metadata (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared)
    (policyFuel fuel : Nat) {source : TypedSource} {scope : SourceCoreBasic.Scope}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {raw : Expr}
    (found : source.lookupExpression? inputs.initializer = some node)
    (form : node.form = .lambda parameters result body)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy
      (policy inputs prepared policyFuel) (lowerBody inputs prepared) fuel (context inputs prepared)
      source scope inputs.initializer reasonAt = .ok lowered)
    (shape : lowered.expression = .inRight .word raw) :
    node.requirements = [] ∧ node.coercions = [] := by
  induction fuel generalizing source node lowered with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy.eq_def] at accepted
  | succ fuel ih =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy.eq_def] at accepted
    dsimp only at accepted
    by_cases owner : inputs.initializer.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
        bind, Except.bind, pure, Except.pure] at accepted
      change (do
        let special ← special inputs prepared policyFuel (context inputs prepared)
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy (policy inputs prepared policyFuel)
              (lowerBody inputs prepared) (min budget fuel) (context inputs prepared)
              childSource childScope childId childReasonAt)
          (fuel + 1) source scope inputs.initializer reasonAt
        if let some result := special then pure result else _) = .ok lowered at accepted
      rw [special_lambda inputs prepared policyFuel (fuel + 1) _ found form] at accepted
      obtain ⟨evidence, evidenceAccepted, accepted⟩ := bind_ok accepted
      cases evidence with
      | none => exact evidence_none found form evidenceAccepted
      | some value =>
        have same : value = lowered := Except.ok.inj accepted
        subst value
        cases ordinaryEq : SourceCompilationPlan.ordinaryOwnedRequirements? node with
        | none =>
          simp only [SourceCoreEvidence.lowerWithProjector, found, form, ordinaryEq,
            bind, Except.bind, pure, Except.pure] at evidenceAccepted
          cases evidenceAccepted
        | some ordinary =>
          obtain ⟨delegated⟩ := CallableCoercionExpressionCertificates.delegated_of_accepted found
            ordinaryEq (by simp [CallableCoercionExpressionCertificates.Delegates, form]) evidenceAccepted
          have empty := coercions_empty delegated.suffix.accepted shape
          have normal : SourceCompilationPlan.ordinaryOwnedRequirements? node = some node.requirements := by
            unfold SourceCompilationPlan.ordinaryOwnedRequirements?
            rw [empty]
            change (if node.requirements.length < 0 then none else
              let owned := node.requirements.take (node.requirements.length - 0)
              if node.requirements = owned ++ [] then some owned else none) = some node.requirements
            simp
          have ordinarySame : delegated.ordinary = node.requirements :=
            Option.some.inj (delegated.ordinaryAccepted.symm.trans normal)
          have childFound := replaced_lookup (replacement := CallableCoercionExpressionCertificates.rawNode node delegated.ordinary)
            found rfl
          have childShape : delegated.operand.expression = .inRight .word raw := by
            have sameOutput := delegated.suffix.accepted
            simp only [empty, SourceCoreEvidence.applyCoercions, pure, Except.pure, Except.ok.injEq] at sameOutput
            exact congrArg SourceCoreBasic.LoweredExpr.expression sameOutput |>.trans shape
          have childAccepted := delegated.childAccepted
          simp only [Nat.min_eq_right (Nat.le_succ fuel)] at childAccepted
          have metadata := ih childFound (by simpa [CallableCoercionExpressionCertificates.rawNode] using form)
            childAccepted childShape
          exact ⟨by simpa only [CallableCoercionExpressionCertificates.rawNode, ordinarySame] using metadata.1, empty⟩
    · simp [owner, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted

/-- Metadata emptiness follows from the compiler result retained by the actual
instance receipt, independently of the source closure's runtime metadata. -/
theorem receipt_metadata {inputs : Inputs} {candidate : Instance} {raw : Expr}
    (receipt : Receipt inputs candidate raw)
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId}
    (found : receipt.emission.prepared.source.lookupExpression? inputs.initializer = some node)
    (form : node.form = .lambda parameters result body) :
    node.requirements = [] ∧ node.coercions = [] := by
  have accepted := receipt.compiled
  cases budget : min inputs.budget inputs.fuel with
  | zero => simp [Inputs.child, budget, SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  | succ fuel =>
    rw [child_at_succ inputs receipt.emission.prepared budget] at accepted
    exact lowered_metadata inputs receipt.emission.prepared fuel (fuel + 1) found form accepted receipt.extracted

/-- Once the actual special callback is excluded, the compiler's ordinary
lambda branch contains this representation read, with the same source and ID. -/
theorem receipt_read {inputs : Inputs} {candidate : Instance} {raw : Expr}
    (receipt : Receipt inputs candidate raw)
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId}
    (found : receipt.emission.prepared.source.lookupExpression? inputs.initializer = some node)
    (form : node.form = .lambda parameters result body) :
    inputs.initializer.occurrence.owner = receipt.emission.prepared.source.owner ∧
    ∃ actual reported, inputs.representation.expressions.readExpression receipt.emission.prepared.source
      inputs.initializer = .ok (actual, reported) := by
  obtain ⟨requirements, coercions⟩ := receipt_metadata receipt found form
  have accepted := receipt.compiled
  cases budget : min inputs.budget inputs.fuel with
  | zero => simp [Inputs.child, budget, SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  | succ fuel =>
    rw [child_at_succ inputs receipt.emission.prepared budget,
      SourceCoreFunctions.lowerExpressionWithPolicy.eq_def] at accepted
    dsimp only at accepted
    by_cases owner : inputs.initializer.occurrence.owner = receipt.emission.prepared.source.owner
    · refine ⟨owner, ?_⟩
      simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
        bind, Except.bind, pure, Except.pure] at accepted
      change (do
        let special ← special inputs receipt.emission.prepared fuel (context inputs receipt.emission.prepared)
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy (policy inputs receipt.emission.prepared fuel)
              (lowerBody inputs receipt.emission.prepared) (min budget fuel) (context inputs receipt.emission.prepared)
              childSource childScope childId childReasonAt)
          (fuel + 1) receipt.emission.prepared.source inputs.scope inputs.initializer inputs.reasonAt
        if let some result := special then pure result else _) = .ok receipt.lowered at accepted
      rw [special_lambda inputs receipt.emission.prepared fuel (fuel + 1) _ found form] at accepted
      have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
        unfold SourceCompilationPlan.ordinaryOwnedRequirements?
        rw [requirements, coercions]
        rfl
      have evidence : SourceCoreEvidence.lowerWithProjector inputs.program
          (representation inputs receipt.emission.prepared).expressions.projectType receipt.emission.prepared.caller
          (context inputs receipt.emission.prepared)
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy (policy inputs receipt.emission.prepared fuel)
              (lowerBody inputs receipt.emission.prepared) (min budget fuel) (context inputs receipt.emission.prepared)
              childSource childScope childId childReasonAt)
          (fuel + 1) receipt.emission.prepared.source inputs.scope inputs.initializer inputs.reasonAt
          (SourceCoreGeneralFunctions.callablePolicy inputs.native receipt.emission.prepared.substitution) = .ok none := by
        simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
          bind, Except.bind, pure, Except.pure]
      rw [evidence] at accepted
      simp only [bind, Except.bind, form] at accepted
      change (do
        let read ← (policy inputs receipt.emission.prepared fuel).readExpression
          receipt.emission.prepared.source inputs.initializer
        _) = .ok receipt.lowered at accepted
      obtain ⟨pair, read, _⟩ := bind_ok accepted
      rcases pair with ⟨actual, reported⟩
      refine ⟨actual, reported, ?_⟩
      simpa [policy, SourceCoreGeneralFunctions.contextualSource, found, form,
        representation, SourceCoreGeneralFunctions.Representation.atContext] using read
    · simp [owner, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted

/-- For the actual compatible reader, its retained lookup identifies the same
lambda node. The original packet constructor then needs no assumed metadata. -/
theorem packet_of_compatible {inputs : Inputs} {candidate : Instance} {raw : Expr}
    (receipt : Receipt inputs candidate raw)
    {checked : SourceCoreCompatibleCatalog.Checked}
    (reader : inputs.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression checked)
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId}
    (found : receipt.emission.prepared.source.lookupExpression? inputs.initializer = some node)
    (form : node.form = .lambda parameters result body) : Nonempty (Packet inputs candidate raw) := by
  obtain ⟨owner, actual, reported, read⟩ := receipt_read receipt found form
  have metadata := CompatibleExpressionReads.metadata_of_read (reader ▸ read)
  have same : actual = node := Option.some.inj (metadata.found.symm.trans found)
  subst actual
  exact of_receipt receipt found form owner metadata.requirements metadata.coercions read

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaMetadata
end
