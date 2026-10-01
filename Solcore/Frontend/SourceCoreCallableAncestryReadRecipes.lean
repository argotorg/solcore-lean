import Solcore.Frontend.SourceCoreCallableAncestryPreparation

/-! Read-time evidence and lexical source transport for generalized callables.
The caller supplies the occurrence's requirements; the stored principal
supplies the source graph to which its own substitution and witnesses apply.
Native compilation context and source substitution are separate fields.

These factories run during preparation. Their sealed receipts retain exact
owned view/template selection and the actual local-witness factory equation.
Runtime consumers select cached receipts and never invoke these factories.
Reachability, cache closure, native read snapshots, and heap provenance remain
obligations of the enclosing artifact. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryReadRecipes
open SourceInference TypeSystem
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Inputs := @SourceCoreCallableAncestryPreparation.Inputs
abbrev Metadata := SourceCoreCallableAncestryCache.State
abbrev Witness := SourceCoreLocalEvidence.Witness
abbrev View {checked : Checked} (base : Base checked) :=
  SourceCoreCallableViews.Entry base.sourceProgram base.plan

structure State where
  metadata : Metadata
  nativeActive : Substitution
  deriving DecidableEq, Repr

inductive Error where
  | unknownView (id : Core.Word)
  | unknownTarget (id : Core.Word)
  | invalidDescriptor (id : Core.Word)
  | monomorphicView (id : Core.Word)
  | wrongCaller (id : Core.Word)
  | missingRead (id : ExpressionId)
  | invalidRead (id : ExpressionId)
  | missingBinder (id : Resolved.LocalId)
  | invalidBinder (id : Resolved.LocalId)
  | unsupportedRequirements (id : ExpressionId)
  | plan (error : SourceCompilationPlan.Error)
  | substitutionMismatch (id : Core.Word)
  | wrongPrincipal (id : Core.Word)
  | missingLambda (id : ExpressionId)
  | invalidLambda (id : ExpressionId)
  | nativeHeaderMismatch (id : Core.Word)
  deriving Repr

/-- This receipt describes one read, independent of when or where the
resulting callable is applied. Its witnesses come from this exact caller. -/
structure Read {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (caller : State) (id target : Core.Word) where private mk ::
  entry : View base
  selected : inputs.views.entryAt? id = some entry
  generalized : entry.view.wrapsPrincipal = true
  template : SourceCoreLambdaTemplates.Lambda
  targetSelected : inputs.templates.lambdaAt? target = some template
  descriptor : SourceCoreStageCodebook.Entry
  descriptorSelected : inputs.callable.table.entryAt? target = some descriptor
  templateOrigin : descriptor.origin = .lambda template.owner template.id template.active
  viewOrigin : descriptor.origin = .lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative
  owner : caller.metadata.owner = entry.view.owner
  nativeParent : caller.nativeActive = entry.view.parentActive
  specialized : SourceSpecialization.SpecializedFunction
  specializedFound : SourceCompilationPlan.exactSpecialization base.plan caller.metadata.owner = .ok specialized
  available : SourceCompilationPlan.EvidenceEnvironment
  availableResolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram specialized.key
    specialized.assumptions = .ok available
  node : ExpressionNode
  found : caller.metadata.source.lookupExpression? entry.view.read = some node
  name : String
  reference : node.form = .reference name (.local entry.view.binding.binder.id)
  binder : TypedBinder
  detected : SourceCompilationPlan.directLambdaLetBinder? caller.metadata.source entry.view.binding.binder.id = some binder
  binderExact : binder = entry.view.binding.binder.applySubstitution caller.metadata.active
  requirements : List RequirementId
  requirementsSelected : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements
  substitution : Substitution
  witnesses : List Witness
  factory : SourceCompilationPlan.localRequirementWitnesses specialized available binder
    {node with type := node.rawType, requirements, coercions := []} = .ok (substitution, witnesses)
  substitutionExact : substitution = entry.view.ownSubstitution

def prepareRead {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (caller : State) (id target : Core.Word) : Except Error (Read inputs caller id target) := do
  match selected : inputs.views.entryAt? id with
  | none => throw (.unknownView id)
  | some entry =>
    if generalized : entry.view.wrapsPrincipal = true then
      match targetSelected : inputs.templates.lambdaAt? target with
      | none => throw (.unknownTarget target)
      | some template =>
        match descriptorSelected : inputs.callable.table.entryAt? target with
        | none => throw (.unknownTarget target)
        | some descriptor =>
          if templateOrigin : descriptor.origin = .lambda template.owner template.id template.active then
            if viewOrigin : descriptor.origin = .lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative then
              if owner : caller.metadata.owner = entry.view.owner then
                if nativeParent : caller.nativeActive = entry.view.parentActive then
                  match specializedFound : SourceCompilationPlan.exactSpecialization base.plan caller.metadata.owner with
                  | .error error => throw (.plan error)
                  | .ok specialized =>
                    match availableResolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram specialized.key specialized.assumptions with
                    | .error error => throw (.plan error)
                    | .ok available =>
                    match found : caller.metadata.source.lookupExpression? entry.view.read with
                    | none => throw (.missingRead entry.view.read)
                    | some node =>
                      match reference : node.form with
                      | .reference name (.local binderId) =>
                        if same : binderId = entry.view.binding.binder.id then
                          match detected : SourceCompilationPlan.directLambdaLetBinder? caller.metadata.source entry.view.binding.binder.id with
                          | none => throw (.missingBinder entry.view.binding.binder.id)
                          | some binder =>
                            if binderExact : binder = entry.view.binding.binder.applySubstitution caller.metadata.active then
                              match requirementsSelected : SourceCompilationPlan.ordinaryOwnedRequirements? node with
                              | none => throw (.unsupportedRequirements node.id)
                              | some requirements =>
                                match factory : SourceCompilationPlan.localRequirementWitnesses specialized available binder
                                    {node with type := node.rawType, requirements, coercions := []} with
                                | .error error => throw (.plan error)
                                | .ok (substitution, witnesses) =>
                                  if substitutionExact : substitution = entry.view.ownSubstitution then
                                    pure ⟨entry, selected, generalized, template, targetSelected, descriptor, descriptorSelected,
                                      templateOrigin, viewOrigin, owner, nativeParent, specialized, specializedFound,
                                      available, availableResolved,
                                      node, found, name, by simpa only [same] using reference, binder, detected, binderExact,
                                      requirements, requirementsSelected, substitution, witnesses, factory, substitutionExact⟩
                                  else throw (.substitutionMismatch id)
                            else throw (.invalidBinder entry.view.binding.binder.id)
                        else throw (.invalidRead entry.view.read)
                      | _ => throw (.invalidRead entry.view.read)
                else throw (.wrongCaller id)
              else throw (.wrongCaller id)
            else throw (.invalidDescriptor target)
          else throw (.invalidDescriptor target)
    else throw (.monomorphicView id)

/-- Application transports the lexical source. The read caller is retained
in `read` and is never used as the replacement principal source. -/
def Read.after {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} (read : Read inputs caller id target) (lexical : State) : State :=
  ⟨⟨lexical.metadata.owner, read.substitution.compose lexical.metadata.active,
    SourceTypedRuntime.rewriteLocalRequirements read.witnesses
      (lexical.metadata.source.applySubstitution read.substitution)⟩, read.entry.view.cumulative⟩

structure Applied {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} (read : Read inputs caller id target) (lexical : State) where private mk ::
  owner : lexical.metadata.owner = read.entry.view.owner
  node : ExpressionNode
  found : lexical.metadata.source.lookupExpression? read.entry.view.principal.initializer = some node
  parameters : List TypedBinder
  resultType : Ty
  body : List StatementId
  shape : node.form = .lambda parameters resultType body
  nativeHeader : (ExpressionForm.lambda (parameters.map (TypedBinder.applySubstitution read.substitution))
    (read.substitution.apply resultType) body) = read.template.node.form

def applyRead {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} (read : Read inputs caller id target) (lexical : State) :
    Except Error (Applied read lexical) := do
  if owner : lexical.metadata.owner = read.entry.view.owner then
    match found : lexical.metadata.source.lookupExpression? read.entry.view.principal.initializer with
    | none => throw (.missingLambda read.entry.view.principal.initializer)
    | some node =>
      match shape : node.form with
      | .lambda parameters resultType body =>
        if nativeHeader : ExpressionForm.lambda (parameters.map (TypedBinder.applySubstitution read.substitution))
            (read.substitution.apply resultType) body = read.template.node.form then
          pure ⟨owner, node, found, parameters, resultType, body, shape, nativeHeader⟩
        else throw (.nativeHeaderMismatch target)
      | _ => throw (.invalidLambda read.entry.view.principal.initializer)
  else throw (.wrongPrincipal id)

/-- Keep the observable instantiated constructor and the original lexical
header. Capture ownership must be supplied by the allocation/callable join. -/
def Applied.sourceValue {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} {read : Read inputs caller id target} {lexical : State}
    (applied : Applied read lexical) (captured : SourceTypedRuntime.Environment)
    (evidence : SourceCompilationPlan.EvidenceEnvironment) : SourceTypedRuntime.Value :=
  .instantiated read.substitution read.witnesses
    (.closure applied.parameters applied.resultType applied.body lexical.metadata.source lexical.metadata.owner
      captured evidence)

theorem Read.after_native {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} (read : Read inputs caller id target) (lexical : State) :
    (read.after lexical).nativeActive = read.entry.view.cumulative := rfl

theorem Read.after_source {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} (read : Read inputs caller id target) (lexical : State) :
    (read.after lexical).metadata.source = SourceTypedRuntime.rewriteLocalRequirements read.witnesses
      (lexical.metadata.source.applySubstitution read.substitution) := rfl

theorem Applied.capture_order {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} {read : Read inputs caller id target} {lexical : State}
    (applied : Applied read lexical) (captured : SourceTypedRuntime.Environment)
    (evidence : SourceCompilationPlan.EvidenceEnvironment) :
    applied.sourceValue captured evidence = .instantiated read.substitution read.witnesses
      (.closure applied.parameters applied.resultType applied.body lexical.metadata.source lexical.metadata.owner
        captured evidence) := rfl

end Solcore.Frontend.SourceCoreCallableAncestryReadRecipes
