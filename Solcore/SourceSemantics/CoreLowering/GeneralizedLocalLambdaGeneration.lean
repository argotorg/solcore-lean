import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaCompilation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration

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
    apply (congrArg SourceCoreBasic.LoweredExpr.expression packet.certificate.emitted).trans
    change packet.certificate.expression = _
    rw [decoration, emitted, sameOrigin, ← bodyEq]
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
  cases function with
  | mk functionParameters functionResult functionBody source captured sourceContext evidence =>
    simp only at parameters result body viewOfSource
    subst functionParameters functionResult functionBody
    obtain ⟨sourceNode, sourceFound, _, sourceForm⟩ := viewOfSource.expression packet.found
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
        inputs.scope administrative := {
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

end Indexed

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaGeneration
