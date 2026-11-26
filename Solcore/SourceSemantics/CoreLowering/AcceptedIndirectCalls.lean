import Solcore.SourceSemantics.CoreLowering.AcceptedNamedValues

/-!
# Accepted bodies: indirect calls

An uncoerced indirect call `.call callee ids (.indirect metadata)` of a
named-row body. The compiler lowers it through its prepared call site
(`SourceCoreCallableContracts.Callsite.lower`): the callee's carrier, the
site's first gate, the packed arguments, the second gate on the physical
arity, then the application of the carrier's closure to the packed payloads.

Applying the callee's value is an explicit input below the grade, quantified
over the callee's Source value and its Core carrier related by the payload
model at the callee's function type. The heads prove everything else on the
accepted `CellAwareInvocationExpressionBounds` protocol: the callee and the
arguments through the children's bounds, both gates through the site's
boundary, and the restoration of the caller carrier. At the root function
model the input holds for a family that admits every instantiation the plan
records (`CoversPlan`), in a program whose callable table records no lambda
(`NoLambdas`): a builtin applies as a packed builtin, a named function as the
direct-call application of its header, and no closure is a function value.

Main declarations: `CellAwareInvocationAcceptedIndirectSites.IndirectSite`, the
site; `CellAwareInvocationAcceptedIndirectPremises.CoversPlan` and `NoLambdas`,
the two whole-program premises; `PreservesAt`, `ReflectsAt`, `PreservesBelow`
and `ReflectsBelow` of `CellAwareInvocationAcceptedIndirectApplication`, the input;
`CellAwareInvocationAcceptedIndirectCalls.preserves` and `reflects`, the heads;
`CellAwareInvocationAcceptedIndirectRows.boundary_row`, `arity_fault` and
`arity_mismatch`, the second gate's Source side;
`CellAwareInvocationAcceptedIndirectReceipts`, the heads' fault and origin
inputs at the public receiving table and the root function model; and
`CellAwareInvocationAcceptedIndirectLeaves.preserves_application` and
`reflects_application`, the input at the root model.
-/

section
/-! Indirect calls of named-row bodies as compiler sites. An indirect site has
no coercions or requirements, no argument coercions, is not a generalized
initializer and lies in a row without evidence assumptions, so the named
policy's special callback declines it and its read policy is the compatible
reader, as for the direct sites of `CellAwareInvocationAcceptedDirectSites`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectSites
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

/-- An uncoerced indirect call of a named-row body. -/
structure IndirectSite {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) (callee : ExpressionId) (arguments : List ExpressionId)
    (metadata : IndirectCallResolution) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : node.form = .call callee arguments (.indirect metadata)
  coercions : node.coercions = []
  requirements : node.requirements = []
  uncoerced : metadata.argumentCoercions = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  assumptions : named.specialized.assumptions = []

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id callee : ExpressionId}
  {arguments : List ExpressionId} {metadata : IndirectCallResolution}

theorem contextual (site : IndirectSite prepared named source id callee arguments metadata) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, site.found, site.form]

private theorem evidence_none (site : IndirectSite prepared named source id callee arguments metadata)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  simp [SourceCoreEvidence.lowerWithProjector, site.found, site.form, site.requirements, site.coercions,
    site.assumptions, site.uncoerced, SourceCompilationPlan.ordinaryOwnedRequirements?] <;> rfl

variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- The named policy's special callback declines an indirect site. -/
theorem special (site : IndirectSite prepared named source id callee arguments metadata) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq, contextual site, bind, Except.bind, pure, Except.pure, site.found,
    site.notInitializer, Option.filter_none]
  rw [evidence_none site child budget scope reasonAt]
  simp [site.form]

theorem read (site : IndirectSite prepared named source id callee arguments metadata) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual site, bind, Except.bind]
  rfl

/-- Proof-producing recognition of an indirect site. -/
def indirectSite? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) :
    Option ((callee : ExpressionId) × (arguments : List ExpressionId) × (metadata : IndirectCallResolution) ×
      PLift (Nonempty (IndirectSite prepared named source id callee arguments metadata))) :=
  match found : source.lookupExpression? id with
  | none => none
  | some node =>
    match form : node.form with
    | .call callee arguments (.indirect metadata) =>
      if coercions : node.coercions = [] then
        if requirements : node.requirements = [] then
          if uncoerced : metadata.argumentCoercions = [] then
            match notInitializer : prepared.base.locals.bindings.find? (fun binding =>
                decide (binding.caller = named.signature.key ∧ binding.initializer = id)) with
            | some _ => none
            | none =>
              if assumptions : named.specialized.assumptions = [] then
                some ⟨callee, arguments, metadata, ⟨⟨⟨node, found, form, coercions, requirements, uncoerced,
                  notInitializer, assumptions⟩⟩⟩⟩
              else none
          else none
        else none
      else none
    | _ => none

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectSites
end

section
/-! The two whole-program premises of an indirect site. `CoversPlan` states
that the family admits every instantiation the plan records, so a named
function read from a local is an admitted callee; `NoLambdas` states that the
callable table records no lambda, which holds when no planned source has one,
so no closure is a function value of the program. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectPremises
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)

/-- Every instantiation the plan records is one the family admits. -/
def CoversPlan (plan : SourceCompilationPlan.Plan) (called : DeclarationInstantiation → Prop) : Prop :=
  ∀ instantiation key, SourceCompilationPlan.exactInstantiationKey plan instantiation = .ok key →
    called instantiation

/-- The callable table records no lambda. -/
def NoLambdas (table : SourceCoreStageCodebook.Table) : Prop :=
  ∀ entry ∈ table.entries, ∀ owner id substitution, entry.origin ≠ .lambda owner id substitution

private def isLambda : SourceCoreStageCodebook.Origin → Bool
  | .lambda _ _ _ => true
  | _ => false

private theorem noLambdas_iff (table : SourceCoreStageCodebook.Table) :
    NoLambdas table ↔ table.entries.all (fun entry => !isLambda entry.origin) = true := by
  simp only [NoLambdas, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · intro none entry member
    cases origin : entry.origin with
    | lambda owner id substitution => exact absurd origin (none entry member owner id substitution)
    | named => rfl
    | builtin => rfl
  · intro none entry member owner id substitution same
    have answer := none entry member
    rw [same] at answer
    cases answer

instance (table : SourceCoreStageCodebook.Table) : Decidable (NoLambdas table) :=
  decidable_of_iff _ (noLambdas_iff table).symm

/-- No closure has a stage origin in a table without lambdas. -/
theorem closure_absurd {plan : SourceCompilationPlan.Plan} {table : SourceCoreStageCodebook.Table}
    (none : NoLambdas table) {function : Dynamic.Closure} {native : Value}
    (origin : CallableLedger.OriginRep plan table (.closure function) native) : False := by
  cases origin with
  | closure member entryOrigin _ _ => exact none _ member _ _ _ entryOrigin

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectPremises
end

section
/-! Applying an indirect callee's value: the Core application of its carrier
to the packed argument payloads, after the call site's second gate accepted
the physical arity, agrees with the staged Source application of its value,
from a reached caller pool with its physical cache. The Source arity of the
value is the argument count, as the accepted gate leaves it. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectApplication
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header Key)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (faults : RecursiveStageMeaning.FaultRep)

/-- Applying a callee's carrier to packed payloads at the Source grade of the
application: the result, the accepted cells and the restoration of the same
pool. This is the cross-body input of an indirect call site. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {scope mapping world before store canonical}
    (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩),
    CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store → StableRows caller →
  ∀ {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope},
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source →
    invocation.evidence.Covers context → Dynamic.HeapWellTyped context before →
  ∀ {sourceValue carrier parameter result parameterCore resultCore},
    Dynamic.ValueHasType context before sourceValue (.function parameter result) →
    model.Represents mapping world (.function parameter result) sourceValue carrier
      (CallableContract.functionType parameterCore resultCore) →
  ∀ {sourceTypes nativeTypes sources payloads},
    TypeSystem.Ty.productMany sourceTypes = parameter →
    SourceCoreCompatibleCatalog.packTypes nativeTypes = parameterCore →
    Dynamic.ValuesHaveTypes context before sources sourceTypes →
    DataExpressionSequence.Values model mapping world sourceTypes nativeTypes sources payloads →
    RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) sourceValue sources.length →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
  ∀ {outcome after},
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) registry size invocation context
      before sourceValue sources outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates [carrier, DataPatternValues.packValues payloads] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld result resultCore faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned

/-- Native completion of the same application from the same caller pool
reconstructs an independent staged Source application and the restored pool. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope mapping world before store canonical}
    (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩),
    CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store → StableRows caller →
  ∀ {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope},
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source →
    invocation.evidence.Covers context → Dynamic.HeapWellTyped context before →
  ∀ {sourceValue carrier parameter result parameterCore resultCore},
    Dynamic.ValueHasType context before sourceValue (.function parameter result) →
    model.Represents mapping world (.function parameter result) sourceValue carrier
      (CallableContract.functionType parameterCore resultCore) →
  ∀ {sourceTypes nativeTypes sources payloads},
    TypeSystem.Ty.productMany sourceTypes = parameter →
    SourceCoreCompatibleCatalog.packTypes nativeTypes = parameterCore →
    Dynamic.ValuesHaveTypes context before sources sourceTypes →
    DataExpressionSequence.Values model mapping world sourceTypes nativeTypes sources payloads →
    RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) sourceValue sources.length →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
  ∀ {value finalStore},
    EvaluationSize size [carrier, DataPatternValues.packValues payloads] store
      CallableIndexedLambdaCalls.applyPayload value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) registry sourceSize invocation
        context before sourceValue sources outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld result resultCore faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget →
    PreservesAt (attachment := attachment) (headers := headers) (keys := keys) model registry faults size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget →
    ReflectsAt (attachment := attachment) (headers := headers) (keys := keys) model registry faults size

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectApplication
end

section
/-! Static facts of an accepted indirect call: the original parent's Source
rows, the staged rules that can run it, the boundary row of its callee's
carrier with the callee's Source arity at the row's physical count, and the
staged application at a different count. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open RecursivePublicCallableArity (Arity)

/-- The lowered type of an accepted indirect call is its projected result. -/
theorem lowered_type {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered) :
    lowered.type = compiler.resultType :=
  (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm

/-- Original parent typing fixes the callee's node and function type, its
typing, the argument row and the raw result, as
`CallableIndexedOwnedIndirectSourceTypeRows.original_rows` does for a given
callee node. -/
theorem source_rows {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (parent : SourceParent compiler) {context : SourceSemantics.Context}
    {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type) :
    ∃ calleeNode parameter result,
      source.lookupExpression? callee = some calleeNode ∧
      calleeNode.type = .function parameter result ∧
      ExpressionHasType source context callee calleeNode.type ∧
      ExpressionsHaveTypes source context ids sourceTypes ∧
      TypeSystem.Ty.productMany sourceTypes = parameter ∧
      compiler.original.type = result := by
  generalize reportedEq : compiler.original.type = reported at parentTyped
  cases parentTyped with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans compiler.found)
    subst actualNode
    rw [compiler.originalForm] at raw
    cases raw with
    | indirectCall calleeTyping argumentsTyping application =>
      obtain ⟨calleeNode, calleeContains, calleeType⟩ := calleeTyping.stored_type
      have row := CallableIndexedOwnedContextualInitializedClosureReceipts.source_types_at_tree
        unique tree argumentsTyping
      have bundle := CallableIndexedOwnedStoredClosureArgumentReceipts.empty_bundle
        application compiler.argumentCoercions
      have result := requirements.outputPath.foldl_target
      rw [parent.coercions, List.foldl_nil] at result
      refine ⟨calleeNode, _, _, lookupExpression?_complete unique calleeContains, calleeType, ?_,
        row ▸ argumentsTyping, by simpa only [← row] using bundle, ?_⟩
      · rw [calleeType]
        exact calleeTyping
      · exact reportedEq.trans result.symm

/-- The staged rules that can run an indirect parent, with their grades. -/
private inductive SourcePrefix (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (call callee : ExpressionId) (ids : List ExpressionId) (metadata : IndirectCallResolution) :
    Nat → Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | calleeFault {childSize failure after}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.fault failure) after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault failure) after
  | notCallable {childSize value after}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) after)
      (invalid : ¬ Dynamic.CallableValue value) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault (.semantic .notCallable)) after
  | rejected {childSize value after reason}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) after)
      (rejected : Staging.CallBoundary.GuardRejects invocation.guards call ids value reason) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault (.stage invocation call reason)) after
  | argumentsFault {childSize argumentsSize value middle after failure}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) middle)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment middle ids (.fault failure) after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize]) (.fault failure) after
  | sourceArity {childSize argumentsSize value middle after values}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) middle)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment middle ids (.values values) after)
      (mismatch : ids.length ≠ metadata.argumentCount) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize])
        (.fault (.semantic (.argumentArityMismatch metadata.argumentCount ids.length))) after
  | applied {childSize argumentsSize applicationSize value calleeHeap argumentsHeap after values outcome}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) calleeHeap)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment calleeHeap ids (.values values) argumentsHeap)
      (called : Staging.Recursive.Size.Applies program stages applicationSize invocation context
        argumentsHeap value values outcome after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize, applicationSize]) outcome after

/-- A staged trace at an uncoerced indirect parent is one of its own rules. -/
private theorem source_prefix
    {program : Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {size : Nat} {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (trace : Staging.Recursive.Size.Expression program stages size invocation context
      environment before id outcome after) :
    SourcePrefix program stages invocation context environment before id callee ids metadata size outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm requirements},
      Staging.Recursive.Occurrence invocation id actualForm requirements →
      actualForm = .call callee ids (.indirect metadata) := by
    intro actualForm requirements occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | arrayFault occurrence shape _ | arrayResult occurrence shape _ _ =>
    cases occurrence_form occurrence
    cases shape
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
    rw [same, form] at shape
    rcases shape with atomic | ⟨_, _, _, impossible⟩
    · cases atomic
    · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
    have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
    rw [actualForm] at atomic
    cases atomic
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
    have actual := (congrArg ExpressionNode.form (same_node contains)).trans form
    rw [actual] at actualForm
    cases actualForm
  | calleeFault occurrence child =>
    cases occurrence_form occurrence
    exact .calleeFault child
  | notCallable occurrence child invalid =>
    cases occurrence_form occurrence
    exact .notCallable child invalid
  | rejected occurrence child rejected =>
    cases occurrence_form occurrence
    exact .rejected child rejected
  | argumentsFault occurrence child accepted arguments =>
    cases occurrence_form occurrence
    exact .argumentsFault child accepted arguments
  | sourceArity occurrence child accepted arguments mismatch =>
    cases occurrence_form occurrence
    exact .sourceArity child accepted arguments mismatch
  | applied occurrence _uncoerced child accepted arguments _arity called =>
    cases occurrence_form occurrence
    exact .applied child accepted arguments called
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _
  | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _
  | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | constructorMetadataFault occurrence _
  | tupleValue occurrence _ _ | tupleFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _ | binaryPanic occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _ => cases occurrence_form occurrence

/-- A function value is callable. -/
theorem callable_of_function {value : Dynamic.Value} (shape : IsFunction value) : Dynamic.CallableValue value := by
  cases shape <;> trivial

/-- The boundary row of a callee's carrier: the carrier's tag selects the
row, whose physical parameter count is the Source arity of the callee's value
(a closure's parameters, a named row's inputs, a builtin's parameter types). -/
theorem boundary_row {compiled : SourceCoreUnifiedCompilation.Compiled}
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {sourceValue : Dynamic.Value} {carrier : Value}
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (boundary : BoundaryAt sidecar site callee ids metadata node sourceValue carrier)
    (named : CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.NamedOrigin compiled sourceValue) :
    ∃ raw tag row, carrier = .pair raw (.word tag) ∧ Selected sidecar site callee ids metadata node row ∧
      site.rowAt? tag = some row ∧
      Arity (Program.ofChecked compiled.sourceProgram) sourceValue row.entry.parameterCount := by
  cases boundary with
  | user dispatch selected =>
    cases (CallableLedger.frame sidecar).userCallable dispatch.bound with
    | closure function =>
      refine ⟨dispatch.function, dispatch.contract, dispatch.row, dispatch.shape, selected, dispatch.found, ?_⟩
      rw [CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected]
      exact .closure function
    | global function =>
      obtain ⟨header, rawD, sourceAt⟩ := named function rfl
      refine ⟨dispatch.function, dispatch.contract, dispatch.row, dispatch.shape, selected, dispatch.found, ?_⟩
      rw [CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count sourceAt caller dispatch selected,
        sourceAt.frame.parameters]
      exact .global sourceAt.frame.instantiated
  | builtin receipt =>
    rename_i function row
    obtain ⟨raw, shape⟩ := receipt.shape
    refine ⟨raw, _, _, shape, receipt.selected, receipt.selected.found, ?_⟩
    rw [receipt.parameter_count]
    exact .builtin function

/-- At a different argument count, the staged application of a value is its
Source arity fault, which leaves the heap unchanged. -/
theorem arity_fault {program : Program} {registry : Staging.Recursive.Registry}
    {scope : Staging.Recursive.Scope} {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {function : Dynamic.Value} {arguments : List Dynamic.Value} {count : Nat}
    (arity : Arity program function count) (different : count ≠ arguments.length) :
    Staging.Recursive.Size.Applies program registry (Staging.Recursive.Size.stepSize []) scope context heap
      function arguments (.fault (.semantic (.argumentArityMismatch count arguments.length))) heap := by
  cases arity with
  | closure function => exact .closureArity different
  | global instantiates => exact .globalArity instantiates different
  | builtin function => exact .builtinArity different

/-- Every staged application at a different argument count is that fault. -/
theorem arity_mismatch {program : Program} {registry : Staging.Recursive.Registry} {size : Nat}
    {scope : Staging.Recursive.Scope} {context : SourceSemantics.Context} {before after : Dynamic.Heap}
    {function : Dynamic.Value} {arguments : List Dynamic.Value} {count : Nat}
    {outcome : Staging.Recursive.Outcome}
    (wellFormed : ProgramWellFormed program)
    (arity : Arity program function count) (different : count ≠ arguments.length)
    (trace : Staging.Recursive.Size.Applies program registry size scope context before function arguments
      outcome after) :
    outcome = .fault (.semantic (.argumentArityMismatch count arguments.length)) ∧ after = before := by
  cases arity with
  | closure function =>
    cases trace with
    | closureArity _ => exact ⟨rfl, rfl⟩
    | closure _ _ _ _ allocate _ _ =>
      have length := allocate.length_eq
      exact False.elim (different (by omega))
  | global instantiates =>
    cases trace with
    | globalArity actual _ =>
      cases BuiltinNamedCalls.instantiation_unique_of_wellFormed wellFormed instantiates actual
      exact ⟨rfl, rfl⟩
    | global actual _ _ _ _ allocate _ _ =>
      cases BuiltinNamedCalls.instantiation_unique_of_wellFormed wellFormed instantiates actual
      have length := allocate.length_eq
      exact False.elim (different (by omega))
  | builtin function =>
    cases trace with
    | builtin applied =>
      have length := (applied.preserves (context := context) (heap := before)).1.length_eq
      exact False.elim (different (by omega))
    | builtinArity _ => exact ⟨rfl, rfl⟩
    | builtinType same _ => exact False.elim (different (by omega))
    | builtinFault fault =>
      have length := fault.argument_count
      exact False.elim (different (by omega))

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectRows
end

section
/-! Uncoerced indirect calls at accepted cell-aware sites. The callee and the
ordered arguments run through the children's bounds at their reached caller
states, which carry the scope authority and the physical frame. The site's
first gate is decided by the callee's boundary row: a rejection is the staged
stage fault, a builtin always passes. The second gate is decided by the row's
physical count: a different count is the Source arity fault of the callee's
value, an equal count supplies its Source arity to the application input,
which runs from the reached argument pool; the caller carrier is restored
around it. Faults of a staged guard rejection and of an application arity are
represented by explicit inputs, as the receiving codebook interprets them. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds (Point)
open CallableIndexedOwnedIndirectSourceAdapters (Prepared SourceParent)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView boundary_at_source_view)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds (NamedOrigin)
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CellAwareInvocationAcceptedIndirectRows
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (cache : ∀ {current}, callerProtocol.State current →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled current.mapping current.store)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation} (index : ActualBodyInvocation.Index compiled bodyRelation)
  (registry : Staging.Recursive.Registry) (faults : RecursiveStageMeaning.FaultRep)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (sourceParent : SourceParent compiler)
  (functionType : policy.callables.functionType = CallableContract.functionType)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : SourceView sidecar.source invocation.source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (origins : ∀ {mapping world sourceType sourceValue carrier type},
    model.Represents mapping world sourceType sourceValue carrier type → IsFunction sourceValue →
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      sourceValue carrier)
  (namedOrigins : ∀ {mapping world sourceType sourceValue carrier type},
    model.Represents mapping world sourceType sourceValue carrier type → NamedOrigin compiled sourceValue)
  (stageFaults : ∀ {sourceValue carrier originalNode originalMetadata reason}
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
      sourceValue carrier),
    CallView originalNode compiler.original originalMetadata metadata →
    Selected sidecar prepared.site callee ids originalMetadata originalNode dispatch.row →
    Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason →
    faults (.stage invocation id reason) (dispatch.reason reason))
  (arityFaults : ∀ {originalNode originalMetadata row},
    Selected sidecar prepared.site callee ids originalMetadata originalNode row →
    row.entry.parameterCount ≠ ids.length →
    faults (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length))
      (prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount ids.length)))
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)

include bridge cache compiler prepared sourceParent functionType caller view originalUnique guardFrame origins
  namedOrigins stageFaults arityFaults unique wellFormed runtime covers in
/-- An uncoerced indirect call at an accepted site preserves its staged
execution when the callee's value application does below the same Source
grade. A callee fault stops before both gates, a stage rejection and an
argument fault stop before the second gate, and a different physical count
stops at it. `notCallable` contradicts the callee's function type and
`sourceArity` the parent's metadata. -/
theorem preserves {children : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
    (size : Nat)
    (calleeCertified : children scope callee compiler.calleeCode)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids sourceTypes compiler.codes)
    (childMeaning : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation children faults size)
    (application : CellAwareInvocationAcceptedIndirectApplication.PreservesBelow (attachment := attachment)
      (headers := headers) (keys := keys) model registry faults size) :
    CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) bridge context model
      index registry invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace
  obtain ⟨sameScope, sameId, sameCode⟩ := point
  subst current child code
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨calleeNode, parameter, result, calleeFound, calleeType, calleeTyped, argumentsTyped, bundle, resultEq⟩ :=
    source_rows compiler sourceParent sequence unique typed
  have loweredType := lowered_type compiler
  have rename := prepared.lowered_rename compiler ξ
  have selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram) registry := .of_program wellFormed
  have originalTrace := trace
  cases source_prefix unique compiler.found compiler.originalForm trace with
  | calleeFault child =>
    obtain ⟨_value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
      childMeaning _ (Staging.Recursive.Size.child_lt_stepSize (by simp)) calleeCertified calleeFound calleeTyped
        environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame child
    cases represented with
    | fault matched =>
      have whole := CallableContract.call_callee_failure (result := compiler.resultType)
        (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
        prepared.site.gates compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown evaluated
      rw [← rename, ← loweredType] at whole
      exact ⟨_, finalStore, finalMap, finalWorld, whole, .fault matched, finalHeaps, maps, worlds, frame,
        heapMetadata, effect, reached, related, post.at_fault_type⟩
  | notCallable child invalid =>
    obtain ⟨_value, _finalStore, _finalMap, _finalWorld, _evaluated, _represented, _finalHeaps,
        _maps, _worlds, _frame, _heapMetadata, _effect, _reached, _related, post⟩ :=
      childMeaning _ (Staging.Recursive.Size.child_lt_stepSize (by simp)) calleeCertified calleeFound calleeTyped
        environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame child
    have valueTyped := post.at_value.1
    rw [calleeType] at valueTyped
    exact False.elim (invalid (callable_of_function (CellAwareIndirectArgumentPrefix.callable_shape valueTyped)))
  | @rejected childSize sourceValue calleeHeap reason child rejected =>
    obtain ⟨_value, calleeStore, calleeMap, calleeWorld, evaluated, represented, calleeHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
      childMeaning _ (Staging.Recursive.Size.child_lt_stepSize (by simp)) calleeCertified calleeFound calleeTyped
        environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame child
    cases represented with
    | @value _ carrier payload =>
      have valueTyped := post.at_value.1
      rw [calleeType] at valueTyped
      obtain ⟨_originalNode, _originalMetadata, _contains, _form, callView, boundary⟩ :=
        boundary_at_source_view compiler prepared caller view originalUnique
          (origins payload (CellAwareIndirectArgumentPrefix.callable_shape valueTyped))
      cases boundary with
      | user dispatch selected =>
        have actualRejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar)
            prepared.site.call ids sourceValue reason := by
          simpa only [guardFrame, prepared.call] using rejected
        have shaped := evaluated
        rw [dispatch.shape] at shaped
        have whole := prepared.site.lower_stage_failure (result := compiler.resultType)
          (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.row
          (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner
            reason)
          dispatch.found (dispatch.rejected actualRejected) shaped
        have evaluatedWhole : Evaluates actual store (lowered.expression.rename ξ)
            (.inLeft lowered.type (.word (dispatch.reason reason))) calleeStore := by
          simpa only [SourceCoreCallableContracts.Callsite.lower, CallStageBoundary.Dispatch.reason, rename,
            loweredType] using whole
        exact ⟨_, calleeStore, calleeMap, calleeWorld, evaluatedWhole,
          .fault (stageFaults dispatch callView selected rejected), calleeHeaps, maps, worlds, frame,
          heapMetadata, effect, reached, related, post.at_value.2.rows⟩
      | builtin receipt =>
        exact False.elim (Staging.CallBoundary.GuardAccepts.not_rejects (.builtin _) rejected)
  | @argumentsFault childSize argumentsSize sourceValue calleeHeap after failure child accepted arguments =>
    obtain ⟨_value, calleeStore, calleeMap, calleeWorld, calleeEvaluated, represented, calleeHeaps,
        calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeEffect, calleeState, calleeRelated,
        calleePost⟩ :=
      childMeaning _ (Staging.Recursive.Size.child_lt_stepSize (by simp)) calleeCertified calleeFound calleeTyped
        environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame child
    cases represented with
    | @value _ carrier payload =>
      have valueTyped := calleePost.at_value.1
      rw [calleeType] at valueTyped
      obtain ⟨_originalNode, _originalMetadata, _contains, _form, _callView, boundary⟩ :=
        boundary_at_source_view compiler prepared caller view originalUnique
          (origins payload (CellAwareIndirectArgumentPrefix.callable_shape valueTyped))
      have gate := CellAwareIndirectArgumentFaultBounds.first_gate (actual := actual) compiler prepared guardFrame
        boundary accepted calleeStore
      have argumentLayout : EnvironmentsAgree
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
          canonical (.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
      have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
        (RuntimeEnvironmentHasTypes.cons (model.runtime_hasType payload) (actualTyped.weaken calleeWorlds))
      obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
          maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
        CellAwareInvocationExpressionSequence.preserves_fault bridge _ sequence unique argumentsTyped childMeaning
          (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
          argumentTyped calleeState calleePost.at_value.2 (authority.transport calleeEffect)
          (physical.transport calleeEffect calleeFrame) frameOwner ownerFrame arguments
          (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp)))
      have whole : Evaluates actual store
          (CallableContract.call prepared.site.gates
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
            (compiler.calleeCode.expression.rename ξ)
            ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ))
          (.inLeft compiler.resultType (.word token)) finalStore := by
        apply LanguageResult.bind_success compiler.resultType calleeEvaluated
        apply LanguageResult.bind_success compiler.resultType gate
        apply LanguageResult.bind_failure compiler.resultType
        simpa only [← rename_prefix, ← rename_prefix] using argumentsEvaluated
      rw [← rename, ← loweredType] at whole
      exact ⟨_, finalStore, finalMap, finalWorld, whole, .fault matched, finalHeaps, calleeMaps.trans maps,
        calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans heapMetadata,
        calleeEffect.trans effect, reached, callerProtocol.trans calleeRelated related,
        SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers
          locals typed originalTrace (calleeFrame.trans frame)⟩
  | sourceArity _ _ _ mismatch => exact False.elim (mismatch sourceParent.arity)
  | @applied childSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap after sources outcome
      child accepted arguments called =>
    obtain ⟨_value, calleeStore, calleeMap, calleeWorld, calleeEvaluated, represented, calleeHeaps,
        calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeEffect, calleeState, calleeRelated,
        calleePost⟩ :=
      childMeaning _ (Staging.Recursive.Size.child_lt_stepSize (by simp)) calleeCertified calleeFound calleeTyped
        environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame child
    cases represented with
    | @value _ carrier payload =>
      have valueTyped := calleePost.at_value.1
      rw [calleeType] at valueTyped
      obtain ⟨_originalNode, _originalMetadata, _contains, _form, _callView, boundary⟩ :=
        boundary_at_source_view compiler prepared caller view originalUnique
          (origins payload (CellAwareIndirectArgumentPrefix.callable_shape valueTyped))
      obtain ⟨_raw, tag, row, carrierShape, selected, rowFound, rowArity⟩ :=
        boundary_row caller boundary (namedOrigins payload)
      have gate := CellAwareIndirectArgumentFaultBounds.first_gate (actual := actual) compiler prepared guardFrame
        boundary accepted calleeStore
      have argumentLayout : EnvironmentsAgree
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
          canonical (.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
      have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
        (RuntimeEnvironmentHasTypes.cons (model.runtime_hasType payload) (actualTyped.weaken calleeWorlds))
      obtain ⟨values, argumentsStore, argumentMap, argumentWorld, argumentsEvaluated, representedValues,
          argumentHeaps, argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentEffect,
          argumentState, argumentRelated, argumentPost⟩ :=
        CellAwareInvocationExpressionSequence.preserves_values bridge _ sequence unique argumentsTyped childMeaning
          (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
          argumentTyped calleeState calleePost.at_value.2 (authority.transport calleeEffect)
          (physical.transport calleeEffect calleeFrame) frameOwner ownerFrame arguments
          (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp)))
      have argumentsNative : Evaluates (.unit :: carrier :: actual) calleeStore
          ((((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0).weakenAt 0)
          (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
        simpa only [← rename_prefix, ← rename_prefix] using argumentsEvaluated
      have count := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count arguments
      by_cases accepts : row.entry.parameterCount = ids.length
      · have arity : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram)
            sourceValue sources.length := by
          rw [count, ← accepts]
          exact rowArity
        obtain ⟨sourcesTyped, argumentHeapTyped, argumentTypes⟩ :=
          SelectedStagedArgumentTyping.values_at selectedBodies runtime covers (locals.mono calleeMetadata)
            calleePost.at_value.2.heap argumentsTyped arguments
        have related : model.Represents argumentMap argumentWorld (.function parameter result) sourceValue carrier
            (CallableContract.functionType compiler.parameterType compiler.resultType) := by
          have extended := model.extend payload argumentMaps argumentWorlds
          rw [calleeType, ← compiler.callableType, functionType] at extended
          exact extended
        have nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
            compiler.parameterType :=
          (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
            compiler.packedType.symm
        obtain ⟨value, finalStore, finalMap, finalWorld, applied, appliedResult, finalHeaps,
            appliedMaps, appliedWorlds, appliedFrame, appliedMetadata, appliedEffect, returned, appliedRelated⟩ :=
          application _ (Staging.Recursive.Size.child_lt_stepSize (by simp)) (bridge.pool argumentState)
            (cache argumentState) argumentPost.rows runtime covers argumentHeapTyped
            (valueTyped.mono argumentTypes) related bundle nativeBundle sourcesTyped representedValues arity
            argumentHeaps called
        have suffix := CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.preserves_suffix
          (actual := actual) (result := compiler.resultType)
          (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
          carrierShape selected rowFound accepts applied
        have whole : Evaluates actual store
            (CallableContract.call prepared.site.gates
              compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
              (compiler.calleeCode.expression.rename ξ)
              ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore := by
          apply LanguageResult.bind_success compiler.resultType calleeEvaluated
          apply LanguageResult.bind_success compiler.resultType gate
          apply LanguageResult.bind_success compiler.resultType argumentsNative
          exact suffix
        rw [← rename] at whole
        obtain ⟨returnedCaller, _samePool, returnedRelated⟩ := bridge.restore initial returned
          ((calleeMaps.trans argumentMaps).trans appliedMaps) ((calleeWorlds.trans argumentWorlds).trans appliedWorlds)
          ((calleeFrame.trans argumentFrame).trans appliedFrame)
          ((calleeMetadata.trans argumentMetadata).trans appliedMetadata)
          ((bridge.related (callerProtocol.trans calleeRelated argumentRelated)).trans appliedRelated)
        refine ⟨value, finalStore, finalMap, finalWorld, whole, ?_, finalHeaps,
          (calleeMaps.trans argumentMaps).trans appliedMaps, (calleeWorlds.trans argumentWorlds).trans appliedWorlds,
          (calleeFrame.trans argumentFrame).trans appliedFrame,
          (calleeMetadata.trans argumentMetadata).trans appliedMetadata,
          (calleeEffect.trans argumentEffect).trans appliedEffect, returnedCaller, returnedRelated,
          SelectedStagedPostAdmission.after_expression_sized initial returnedCaller admitted selectedBodies runtime
            covers locals typed originalTrace ((calleeFrame.trans argumentFrame).trans appliedFrame)⟩
        rw [resultEq, loweredType]
        exact appliedResult
      · have different : row.entry.parameterCount ≠ sources.length := by
          rw [count]
          exact accepts
        obtain ⟨sameOutcome, sameHeap⟩ := arity_mismatch wellFormed rowArity different called
        subst sameOutcome sameHeap
        have read : Evaluates (DataPatternValues.packValues values :: .unit :: carrier :: actual) argumentsStore
            (.second (.var 2)) (.word tag) argumentsStore := by
          rw [carrierShape]
          exact .second (.var rfl)
        have secondGate := CallableContract.dispatch_evaluates prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown tag read
        rw [CallableIndexedOwnedPreparedSecondCallGateRejection.rejected_gate selected rowFound accepts,
          CallableContract.resultValue] at secondGate
        have whole : Evaluates actual store
            (CallableContract.call prepared.site.gates
              compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
              (compiler.calleeCode.expression.rename ξ)
              ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ))
            (.inLeft compiler.resultType (.word (prepared.site.reasonAt row.caller row.call row.entry.id
              .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length)))) argumentsStore := by
          apply LanguageResult.bind_success compiler.resultType calleeEvaluated
          apply LanguageResult.bind_success compiler.resultType gate
          apply LanguageResult.bind_success compiler.resultType argumentsNative
          exact LanguageResult.bind_failure compiler.resultType secondGate
        rw [← rename, ← loweredType] at whole
        refine ⟨_, argumentsStore, argumentMap, argumentWorld, whole, ?_, argumentHeaps,
          calleeMaps.trans argumentMaps, calleeWorlds.trans argumentWorlds, calleeFrame.trans argumentFrame,
          calleeMetadata.trans argumentMetadata, calleeEffect.trans argumentEffect, argumentState,
          callerProtocol.trans calleeRelated argumentRelated,
          SelectedStagedPostAdmission.after_expression_sized initial argumentState admitted selectedBodies runtime
            covers locals typed originalTrace (calleeFrame.trans argumentFrame)⟩
        rw [count]
        exact .fault (arityFaults selected accepts)

include bridge cache compiler prepared sourceParent functionType caller view originalUnique guardFrame origins
  namedOrigins stageFaults arityFaults unique wellFormed runtime covers in
/-- Native completion of an uncoerced indirect call at an accepted site
reconstructs its staged execution when the callee's value application does
below the native grade of the call. Each native stop, at the callee, at
either gate or in the arguments, is the staged rule that stops there. -/
theorem reflects {children : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
    (size : Nat)
    (calleeCertified : children scope callee compiler.calleeCode)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids sourceTypes compiler.codes)
    (childMeaning : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model index registry invocation children faults size)
    (application : CellAwareInvocationAcceptedIndirectApplication.ReflectsBelow (attachment := attachment)
      (headers := headers) (keys := keys) model registry faults size) :
    CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) bridge context model
      index registry invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed
  obtain ⟨sameScope, sameId, sameCode⟩ := point
  subst current child code
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨calleeNode, parameter, result, calleeFound, calleeType, calleeTyped, argumentsTyped, bundle, resultEq⟩ :=
    source_rows compiler sourceParent sequence unique typed
  have loweredType := lowered_type compiler
  have selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram) registry := .of_program wellFormed
  have occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm, sourceParent.requirements,
      sourceParent.coercions⟩
  have full := completed
  rw [prepared.lowered_rename compiler ξ] at full
  cases CallableIndirectCallBounds.bind_completed full (Nat.le_refl size) with
  | failed calleeNative calleeStrict =>
    obtain ⟨_calleeSize, _calleeOutcome, after, finalMap, finalWorld, calleeTrace, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
      childMeaning _ calleeStrict calleeCertified calleeFound calleeTyped environments heaps locals agrees
        actualTyped initial admitted authority physical frameOwner ownerFrame calleeNative
    cases represented with
    | fault matched =>
      refine ⟨_, _, after, finalMap, finalWorld, .calleeFault occurrence calleeTrace, ?_, finalHeaps, maps, worlds,
        frame, heapMetadata, effect, reached, related, post.at_fault_type⟩
      rw [loweredType]
      exact .fault matched
  | @continued _ _ _ carrier calleeStore _ _ calleeNative remaining calleeStrict remainingStrict =>
    obtain ⟨_calleeSize, _calleeOutcome, calleeHeap, calleeMap, calleeWorld, calleeTrace, represented, calleeHeaps,
        calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeEffect, calleeState, calleeRelated,
        calleePost⟩ :=
      childMeaning _ calleeStrict calleeCertified calleeFound calleeTyped environments heaps locals agrees
        actualTyped initial admitted authority physical frameOwner ownerFrame calleeNative
    cases represented with
    | @value sourceValue _ payload =>
      have valueTyped := calleePost.at_value.1
      rw [calleeType] at valueTyped
      obtain ⟨originalNode, originalMetadata, _contains, _form, callView, boundary⟩ :=
        boundary_at_source_view compiler prepared caller view originalUnique
          (origins payload (CellAwareIndirectArgumentPrefix.callable_shape valueTyped))
      obtain ⟨_raw, _tag, row, carrierShape, selected, rowFound, rowArity⟩ :=
        boundary_row caller boundary (namedOrigins payload)
      have gatePrefix : CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix size prepared.site
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
          ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier
          value finalStore := by
        cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
        | failed gate gateStrict => exact .failed gate gateStrict
        | continued gate suffixTrace gateStrict suffixStrict =>
          exact .passed gate suffixTrace gateStrict suffixStrict
      have gateResult :
          (∃ reason, Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason ∧
            ∃ dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call
                ids sourceValue carrier,
              Selected sidecar prepared.site callee ids originalMetadata originalNode dispatch.row ∧
              value = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧ finalStore = calleeStore) ∨
          (Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
            ∃ suffixSize, EvaluationSize suffixSize (.unit :: carrier :: actual) calleeStore
              (CallableIndexedOwnedStoredIndirectNativePrefix.suffix prepared.site
                compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
                ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore ∧
              suffixSize < size) := by
        cases boundary with
        | user dispatch dispatchSelected =>
          cases gatePrefix.resolve dispatch with
          | inl rejectedGate =>
            obtain ⟨reason, rejectedFrame, valueEq, storeEq, _represents⟩ := rejectedGate
            exact .inl ⟨reason, by simpa only [guardFrame, prepared.call] using rejectedFrame, dispatch,
              dispatchSelected, valueEq, storeEq⟩
          | inr acceptedGate =>
            exact .inr (by simpa only [guardFrame, prepared.call] using acceptedGate)
        | builtin receipt =>
          exact .inr (by simpa only [guardFrame, prepared.call] using receipt.resolve_prefix gatePrefix)
      cases gateResult with
      | inl rejectedGate =>
        obtain ⟨reason, rejected, dispatch, dispatchSelected, valueEq, storeEq⟩ := rejectedGate
        subst valueEq storeEq
        refine ⟨_, _, calleeHeap, calleeMap, calleeWorld, .rejected occurrence calleeTrace rejected, ?_,
          calleeHeaps, calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeEffect, calleeState,
          calleeRelated, calleePost.at_value.2.rows⟩
        rw [loweredType]
        exact .fault (stageFaults dispatch callView dispatchSelected rejected)
      | inr acceptedGate =>
        obtain ⟨accepted, _suffixSize, suffixTrace, suffixStrict⟩ := acceptedGate
        have argumentLayout : EnvironmentsAgree
            (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
            canonical (.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
        have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
          (RuntimeEnvironmentHasTypes.cons (model.runtime_hasType payload) (actualTyped.weaken calleeWorlds))
        cases CallableIndirectCallBounds.bind_completed suffixTrace (Nat.le_of_lt suffixStrict) with
        | failed argumentsNative argumentsStrict =>
          have argumentNative := argumentsNative
          rw [← rename_prefix, ← rename_prefix] at argumentNative
          obtain ⟨_argumentsSize, _argumentsOutcome, after, finalMap, finalWorld, argumentsTrace, represented,
              finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
            CellAwareInvocationExpressionSequence.reflects bridge size sequence unique argumentsTyped childMeaning
              (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
              argumentTyped calleeState calleePost.at_value.2 (authority.transport calleeEffect)
              (physical.transport calleeEffect calleeFrame) frameOwner ownerFrame argumentNative argumentsStrict
          cases represented with
          | fault matched =>
            have trace := Staging.Recursive.Size.Expression.argumentsFault occurrence calleeTrace accepted
              argumentsTrace
            refine ⟨_, _, after, finalMap, finalWorld, trace, ?_, finalHeaps, calleeMaps.trans maps,
              calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans heapMetadata,
              calleeEffect.trans effect, reached, callerProtocol.trans calleeRelated related,
              SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime
                covers locals typed trace (calleeFrame.trans frame)⟩
            rw [loweredType]
            exact .fault matched
        | continued argumentsNative remaining argumentsStrict remainingStrict =>
          have argumentNative := argumentsNative
          rw [← rename_prefix, ← rename_prefix] at argumentNative
          obtain ⟨_argumentsSize, _argumentsOutcome, argumentsHeap, argumentMap, argumentWorld, argumentsTrace,
              represented, argumentHeaps, argumentMaps, argumentWorlds, argumentFrame, argumentMetadata,
              argumentEffect, argumentState, argumentRelated, argumentPost⟩ :=
            CellAwareInvocationExpressionSequence.reflects bridge size sequence unique argumentsTyped childMeaning
              (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
              argumentTyped calleeState calleePost.at_value.2 (authority.transport calleeEffect)
              (physical.transport calleeEffect calleeFrame) frameOwner ownerFrame argumentNative argumentsStrict
          cases represented with
          | @values sources values representedValues =>
            have count := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
            by_cases accepts : row.entry.parameterCount = ids.length
            · obtain ⟨_applicationSize, applicationStrict, applicationNative⟩ :=
                CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.reflects_suffix carrierShape selected
                  rowFound accepts remaining (Nat.le_of_lt remainingStrict)
              have arity : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram)
                  sourceValue sources.length := by
                rw [count, ← accepts]
                exact rowArity
              obtain ⟨sourcesTyped, argumentHeapTyped, argumentTypes⟩ :=
                SelectedStagedArgumentTyping.values_at selectedBodies runtime covers (locals.mono calleeMetadata)
                  calleePost.at_value.2.heap argumentsTyped argumentsTrace
              have related : model.Represents argumentMap argumentWorld (.function parameter result) sourceValue
                  carrier (CallableContract.functionType compiler.parameterType compiler.resultType) := by
                have extended := model.extend payload argumentMaps argumentWorlds
                rw [calleeType, ← compiler.callableType, functionType] at extended
                exact extended
              have nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
                  compiler.parameterType :=
                (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
                  compiler.packedType.symm
              obtain ⟨_applicationSourceSize, outcome, after, finalMap, finalWorld, called, appliedResult,
                  finalHeaps, appliedMaps, appliedWorlds, appliedFrame, appliedMetadata, appliedEffect, returned,
                  appliedRelated⟩ :=
                application _ applicationStrict (bridge.pool argumentState) (cache argumentState) argumentPost.rows
                  runtime covers argumentHeapTyped (valueTyped.mono argumentTypes) related bundle nativeBundle
                  sourcesTyped representedValues arity argumentHeaps applicationNative
              have trace := Staging.Recursive.Size.Expression.applied occurrence compiler.argumentCoercions
                calleeTrace accepted argumentsTrace sourceParent.arity called
              obtain ⟨returnedCaller, _samePool, returnedRelated⟩ := bridge.restore initial returned
                ((calleeMaps.trans argumentMaps).trans appliedMaps)
                ((calleeWorlds.trans argumentWorlds).trans appliedWorlds)
                ((calleeFrame.trans argumentFrame).trans appliedFrame)
                ((calleeMetadata.trans argumentMetadata).trans appliedMetadata)
                ((bridge.related (callerProtocol.trans calleeRelated argumentRelated)).trans appliedRelated)
              refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps,
                (calleeMaps.trans argumentMaps).trans appliedMaps,
                (calleeWorlds.trans argumentWorlds).trans appliedWorlds,
                (calleeFrame.trans argumentFrame).trans appliedFrame,
                (calleeMetadata.trans argumentMetadata).trans appliedMetadata,
                (calleeEffect.trans argumentEffect).trans appliedEffect, returnedCaller, returnedRelated,
                SelectedStagedPostAdmission.after_expression_sized initial returnedCaller admitted selectedBodies
                  runtime covers locals typed trace ((calleeFrame.trans argumentFrame).trans appliedFrame)⟩
              rw [resultEq, loweredType]
              exact appliedResult
            · obtain ⟨valueEq, storeEq⟩ :=
                CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix carrierShape selected
                  rowFound accepts remaining
              subst valueEq storeEq
              have different : row.entry.parameterCount ≠ sources.length := by
                rw [count]
                exact accepts
              have trace := Staging.Recursive.Size.Expression.applied occurrence compiler.argumentCoercions
                calleeTrace accepted argumentsTrace sourceParent.arity
                (arity_fault (registry := registry) (scope := invocation) (context := context)
                  (heap := argumentsHeap) rowArity different)
              refine ⟨_, _, argumentsHeap, argumentMap, argumentWorld, trace, ?_, argumentHeaps,
                calleeMaps.trans argumentMaps, calleeWorlds.trans argumentWorlds, calleeFrame.trans argumentFrame,
                calleeMetadata.trans argumentMetadata, calleeEffect.trans argumentEffect, argumentState,
                callerProtocol.trans calleeRelated argumentRelated,
                SelectedStagedPostAdmission.after_expression_sized initial argumentState admitted selectedBodies
                  runtime covers locals typed trace (calleeFrame.trans argumentFrame)⟩
              rw [loweredType, count]
              exact .fault (arityFaults selected accepts)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectCalls
end

section
/-! Receipts for the fault and origin inputs of the indirect heads, at the
public receiving table and the root function model of the accepted family. A
staged guard rejection and an application arity fault are decoded at their
original selected rows, as `CellAwareScopeIndirectFirstGateBounds` and
`CellAwareScopeIndirectSecondGateBounds` decode them; the root model supplies a
callable origin for every function value and the named Source authority of
every positive named handle. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds (NamedOrigin)

section Faults
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source invocation.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include receiver stagePrepared view guardFrame in
/-- The first-gate word of a staged guard rejection represents its stage
fault at the public receiving table (the heads' `stageFaults`). -/
theorem stage_faults {sourceValue : Dynamic.Value} {carrier : Value} {originalNode : ExpressionNode}
    {originalMetadata : IndirectCallResolution} {reason : Staging.CallGuard.Fault}
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
      sourceValue carrier)
    (callView : CallView originalNode compiler.original originalMetadata metadata)
    (selected : Selected sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
    (rejected : Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason) :
    callFaults (.stage invocation id reason) (dispatch.reason reason) := by
  have actualRejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar)
      prepared.site.call ids sourceValue reason := by
    simpa only [guardFrame, prepared.call] using rejected
  obtain ⟨diagnostic, decoded, error⟩ :=
    CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.receiving_diagnostic
      compiler prepared stagePrepared dispatch selected receiver actualRejected
  have actualContains : ContainsExpression invocation.source prepared.site.call compiler.original := by
    rw [prepared.call]
    exact lookupExpression?_sound compiler.found
  have errorView : CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.StageErrorView
      invocation prepared.site.call reason diagnostic.error := by
    rw [error]
    exact .selected view actualContains compiler.originalForm callView guardFrame dispatch selected
      (by simpa only [prepared.call] using rejected)
  have received : CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.stagedFaults
      completion.result.diagnostics (.stage invocation prepared.site.call reason) (dispatch.reason reason) :=
    ⟨diagnostic, decoded, errorView⟩
  have common := CallableIndexedOwnedPublicDecodedStagedCallFaults.of_first_gate received
  simpa only [prepared.call] using common

include receiver stagePrepared in
/-- The second-gate word of a different physical count represents the Source
arity fault at the public receiving table (the heads' `arityFaults`). -/
theorem arity_faults {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
    {row : SourceCoreStageCodebook.Decision}
    (selected : Selected sidecar prepared.site callee ids originalMetadata originalNode row)
    (different : row.entry.parameterCount ≠ ids.length) :
    callFaults (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length))
      (prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount ids.length)) := by
  obtain ⟨diagnostic, decoded, error⟩ :=
    CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiving_diagnostic
      compiler prepared stagePrepared selected receiver different
  exact CallableIndexedOwnedPublicDecodedStagedCallFaults.of_arity
    ⟨row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩

end Faults

section Origins
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

/-- The root model gives every function value its callable origin (the heads'
`origins`). -/
theorem origins {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {carrier : Value} {type : Ty}
    (represented : (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile)).Represents
        mapping world sourceType sourceValue carrier type)
    (shape : IsFunction sourceValue) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      sourceValue carrier :=
  CellAwarePhysicalFunctionOrigins.stage_origin profile represented shape

/-- A global value of the root model is a positive named handle, which keeps
its named Source authority (the heads' `namedOrigins`). -/
theorem named_origins {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {carrier : Value} {type : Ty}
    (represented : (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile)).Represents
        mapping world sourceType sourceValue carrier type) :
    NamedOrigin compiled sourceValue := by
  change ValueRep compiled.compatible.checked registry
    (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world sourceType sourceValue carrier type at represented
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    intro function same
    cases same
    cases related with
    | ordinary retained =>
      cases retained with
      | global member =>
        obtain ⟨association⟩ := member
        exact ⟨association.header, association.rawD, association.sourceAt⟩
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | fixed | product | proxy | constructed | mappingValue | arrayRef | arraySlice
  | memref =>
    intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

end Origins
end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectReceipts
end

section
/-! The application input at the root function model of the accepted family,
for programs whose callable table records no lambda. A closure value has a
stage origin, which such a table excludes. A builtin value applies its
primitive at the unchanged pool, as `CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds`
applies it. A named value is the positive handle of a header of the
inventory: its installed cell, read from the physical cache, gives a capture
for the caller's physical owner, the header's instantiation is admitted by
`CoversPlan`, and the direct-call application input runs the header's code. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectLeaves
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedCapture NamedInstalledCode)
open CellAwareInvocationAcceptedIndirectPremises (CoversPlan NoLambdas closure_absurd)

/-- Renaming keeps an expression's head: a renamed lambda is a lambda. -/
private theorem rename_lambda {expression : Expr} {ξ : Renaming} {parameter result : Ty} {body : Expr}
    (renamed : expression.rename ξ = .lambda parameter result body) :
    ∃ original, expression = .lambda parameter result original ∧ original.rename ξ.lift = body := by
  cases expression <;> simp [Expr.rename] at renamed
  case lambda =>
    obtain ⟨rfl, rfl, rfl⟩ := renamed
    exact ⟨_, rfl, rfl⟩

/-- An installed named closure is read from its physical cache cell. -/
private theorem installed_read {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (Header compiled program)} {key : Key compiled program} {header : Header compiled program}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    {capture : NamedCapture headers key header mapping world}
    (installed : NamedInstalledCode capture)
    (embedding : capture.embedding = RecursiveGlobalInitializationMeaning.shift header.slot)
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store) :
    store.read? (CallableIndexedOwnedPhysicalGlobals.location compiled header.slot) = some (.inRight .unit
      (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename (RecursiveGlobalInitializationMeaning.shift header.slot).lift)
        (List.replicate header.slot .unit ++ CallableIndexedOwnedPhysicalGlobals.environment compiled))) := by
  obtain ⟨template, found, shape⟩ := installed
  change SourceCoreLambdaTemplates.installedTemplate header.slot template = _ at shape
  rw [RecursiveGlobalInitializationMeaning.installed_template, RecursiveGlobalInitializationMeaning.shifted,
    embedding] at shape
  obtain ⟨original, sameTemplate, sameBody⟩ := rename_lambda shape
  subst sameTemplate
  have read := (physical.cached found).2
  rw [sameBody] at read
  exact read

/-- The applied closure of a carrier in a packed application. -/
private theorem payload_body {size : Nat} {parameter result : Ty} {body : Expr} {captured : Environment}
    {identity contract packed value : Value} {store finalStore : Store}
    (completed : EvaluationSize size [.pair (.pair identity (.closure parameter result body captured)) contract,
      packed] store CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ bodySize, bodySize < size ∧ EvaluationSize bodySize (packed :: captured) store body value finalStore := by
  cases completed with
  | apply selected argument evaluated =>
    cases selected with
    | second tagged =>
      cases tagged with
      | first lookup =>
        cases lookup with
        | var found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Value.pair.injEq, Value.closure.injEq] at found
          obtain ⟨⟨_, rfl, rfl, rfl, rfl⟩, _⟩ := found
          cases argument with
          | var read =>
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at read
            subst read
            exact ⟨_, by omega, evaluated⟩

private theorem values_rep {checked : SourceCoreCompatibleCatalog.Checked}
    {receiving : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {types : List TypeSystem.Ty} {natives : List Ty} {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel checked receiving functions)
      mapping world types natives sources payloads) :
    ValuesRep checked receiving functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry receiving : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

/-- A global value of the root model is a positive named handle. -/
theorem named_member {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {carrier : Value} {type : Ty}
    (represented : ValueRep compiled.compatible.checked receiving
      (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile)
      mapping world sourceType sourceValue carrier type) :
    ∀ function, sourceValue = .global function → ∃ actualType,
      CallableIndexedOwnedPhysicalNamedAssociation.StaticMember headers keys mapping world actualType function
        carrier type := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    intro function same
    cases same
    cases related with
    | ordinary retained =>
      cases retained with
      | global member => exact ⟨_, member⟩
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | fixed | product | proxy | constructed | mappingValue | arrayRef | arraySlice
  | memref =>
    intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

variable (registry : Staging.Recursive.Registry) (faults : RecursiveStageMeaning.FaultRep)
  (owner : OwnedKey keys) (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (noLambdas : NoLambdas compiled.indexed.ancestry.graph.inputs.callable.table)
  {called : DeclarationInstantiation → Prop}
  (covers : CoversPlan compiled.indexed.base.plan called)
  (sizes : ∀ header, header ∈ headers → called header.instantiation →
    header.globals = compiled.indexed.base.globals.length)

local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving
  (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile)

include keyPhysical wellFormed noLambdas covers sizes in
/-- The application input holds at the root model when every admitted
header's application does below the same Source grade. -/
theorem preserves_application {size : Nat}
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True)
        (headers := headers) (keys := keys) rootModel registry faults header size) :
    CellAwareInvocationAcceptedIndirectApplication.PreservesBelow (attachment := fun _ _ _ => True)
      (headers := headers) (keys := keys) rootModel registry faults size := by
  intro applicationSize smaller scope mapping world before store canonical caller cacheAuth stable context
    invocation runtime evidenceCovers heapTyped sourceValue carrier parameter result parameterCore resultCore
    calleeTyped related sourceTypes nativeTypes sources payloads bundle nativeBundle sourcesTyped values arity
    heaps outcome after trace
  cases CellAwareIndirectArgumentPrefix.callable_shape calleeTyped with
  | closure function =>
    exact False.elim (closure_absurd noLambdas
      (CellAwarePhysicalFunctionOrigins.stage_origin profile related (.closure function)))
  | builtin function =>
    cases function with
    | mk function =>
    have builtin := CallableIndexedOwnedPreparedStagedBuiltinArgumentRows.builtin_member
      (CellAwarePhysicalFunctionOrigins.builtin profile related ⟨function⟩ rfl) ⟨function⟩ rfl
    have nativeType : CallableContract.functionType parameterCore resultCore =
        CallableContract.functionType (SourceCoreInteger.builtinParameter function)
          (SourceCoreInteger.builtinResult function) := by
      generalize sourceTypeEq : function.type = sourceType at builtin
      cases builtin
      rfl
    have nativeSignature := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
    have signature : parameter = TypeSystem.Ty.productMany function.parameterTypes ∧
        result = function.returnType := by
      rcases calleeTyped.builtin_inv with ordinary | staged
      · exact TypeSystem.Ty.function.inj ordinary
      · obtain ⟨inner, impossible, _typed⟩ := staged
        cases impossible
    have count : function.parameterTypes.length = sources.length := arity.builtin_count
    have expectedLength :
        function.parameterTypes.length = (CompatibleBuiltinMeaning.argumentTypes function).length := by
      cases function <;> first | rfl | (rename_i op; cases op <;> rfl)
    have sourceRow : sourceTypes = function.parameterTypes := by
      have sourceLength := CallableIndexedOwnedStoredArgumentAlignment.source_length values
      exact TypeSystem.Ty.productMany_inj (by omega) (bundle.trans signature.1)
    have nativeRow : nativeTypes = CompatibleBuiltinMeaning.argumentTypes function := by
      have nativeLength := values.length.1
      exact CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle (by omega)
        (nativeBundle.trans (nativeSignature.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function).symm))
    have rows := values_rep values
    rw [sourceRow, nativeRow] at rows
    obtain ⟨_nativeSize, value, evaluated, represented, sameHeap, _sourceGrade⟩ :=
      CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.preserves _
        (CellAwarePhysicalFunctionOrigins.observations profile) builtin rows trace
    subst sameHeap
    refine ⟨value, store, mapping, world, evaluated.sound, ?_, heaps, .refl _, .refl _, .refl _ _, .refl _,
      CellAwareScopeAuthority.Effect.refl _ _ _ _, caller, (protocol headers keys).refl caller⟩
    rw [signature.2, nativeSignature.2]
    exact represented
  | global function =>
    obtain ⟨_actualType, ⟨association⟩⟩ := named_member profile related function rfl
    rcases association with ⟨_associationOwner, header, rawD, _identity, named, _descriptor, member, sourceAt,
      installed, _number, _projection, _typed, _canonical, captured, embedding, _sourceType, nativeEq, typeEq⟩
    have admitted : called header.instantiation := covers _ _ header.target
    obtain ⟨globalType, _valid, _evidence⟩ :
        (TypeSystem.Ty.function parameter result) = function.instantiation.type ∧ _ ∧ _ := by
      rcases Dynamic.ValueHasType.global_inv calleeTyped with ordinary | ⟨_inner, impossible, _typed⟩
      · exact ordinary
      · cases impossible
    have actualType : function.instantiation.type = header.named.specialized.function.type := by
      rw [sourceAt.retained]
      rfl
    have signature := TypeSystem.Ty.function.inj (globalType.trans (actualType.trans
      (RecursiveNamedPublicHistorySourceInputs.source_function_type wellFormed sourceAt)))
    have types : header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
      have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
      rw [header.parameters] at bodyTypes
      simpa only [List.map_map, Function.comp_def] using bodyTypes.symm
    have inputs := arity.global_count wellFormed sourceAt.frame.instantiated
    have parameterCount := congrArg List.length sourceAt.frame.parameters
    rw [header.parameters, List.length_map] at parameterCount
    have binderCount : sources.length = header.bindings.length := by omega
    have sourceRow : sourceTypes = header.types := by
      apply TypeSystem.Ty.productMany_inj _ (bundle.trans signature.1)
      rw [types, List.length_map, CallableIndexedOwnedStoredArgumentAlignment.source_length values]
      exact binderCount
    have argumentsTyped : Dynamic.ValuesHaveTypes context before sources
        (header.bindings.map (fun binding => binding.1.scheme.body)) := by
      rw [← types, ← sourceRow]
      exact sourcesTyped
    obtain ⟨bodyHeap, bodyArguments, supports⟩ := SelectedCompilationNamedAdmission.arguments
      ((SelectedCompilationNamedSupport.Support.of_program wellFormed).certified header) runtime heapTyped
      argumentsTyped
    have nativeSignature := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters typeEq
    have parameters := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles header.bindings values
      binderCount (by rw [sourceRow, types]) (nativeBundle.trans (nativeSignature.1.trans header.parameterType))
    obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_read (mapping := mapping) member
      keyPhysical.frame keyPhysical.prefixZero keyPhysical.locations (sizes header member admitted)
      (installed_read installed embedding cacheAuth) heaps.runtime_hasTypes
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluated, applied, finalHeaps, maps, worlds, frame,
        metadata, effect, returned, relatedPool⟩ :=
      applications header member admitted applicationSize smaller owner caller capture cacheAuth member stable
        supports bodyHeap bodyArguments parameters heaps sourceAt trace
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, metadata, effect,
      returned, relatedPool⟩
    · have body : Evaluates (DataPatternValues.packValues payloads :: named.captured) store
          (header.code.rename named.embedding.lift) value finalStore := by
        rw [captured, embedding, ← capture.captured_eq, ← capture.embedding_eq]
        exact bodyEvaluated
      rw [nativeEq]
      exact .apply (.second (.first (.var rfl))) (.var rfl) body
    · rw [signature.2, nativeSignature.2, header.resultType]
      exact applied

include keyPhysical wellFormed noLambdas covers sizes in
/-- Native completion of the application input holds at the root model when
every admitted header's native completion does below the same native grade. -/
theorem reflects_application {size : Nat}
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True)
        (headers := headers) (keys := keys) rootModel registry faults header size) :
    CellAwareInvocationAcceptedIndirectApplication.ReflectsBelow (attachment := fun _ _ _ => True)
      (headers := headers) (keys := keys) rootModel registry faults size := by
  intro applicationSize smaller scope mapping world before store canonical caller cacheAuth stable context
    invocation runtime evidenceCovers heapTyped sourceValue carrier parameter result parameterCore resultCore
    calleeTyped related sourceTypes nativeTypes sources payloads bundle nativeBundle sourcesTyped values arity
    heaps value finalStore completed
  cases CellAwareIndirectArgumentPrefix.callable_shape calleeTyped with
  | closure function =>
    exact False.elim (closure_absurd noLambdas
      (CellAwarePhysicalFunctionOrigins.stage_origin profile related (.closure function)))
  | builtin function =>
    cases function with
    | mk function =>
    have builtin := CallableIndexedOwnedPreparedStagedBuiltinArgumentRows.builtin_member
      (CellAwarePhysicalFunctionOrigins.builtin profile related ⟨function⟩ rfl) ⟨function⟩ rfl
    have nativeType : CallableContract.functionType parameterCore resultCore =
        CallableContract.functionType (SourceCoreInteger.builtinParameter function)
          (SourceCoreInteger.builtinResult function) := by
      generalize sourceTypeEq : function.type = sourceType at builtin
      cases builtin
      rfl
    have nativeSignature := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
    have signature : parameter = TypeSystem.Ty.productMany function.parameterTypes ∧
        result = function.returnType := by
      rcases calleeTyped.builtin_inv with ordinary | staged
      · exact TypeSystem.Ty.function.inj ordinary
      · obtain ⟨inner, impossible, _typed⟩ := staged
        cases impossible
    have count : function.parameterTypes.length = sources.length := arity.builtin_count
    have expectedLength :
        function.parameterTypes.length = (CompatibleBuiltinMeaning.argumentTypes function).length := by
      cases function <;> first | rfl | (rename_i op; cases op <;> rfl)
    have sourceRow : sourceTypes = function.parameterTypes := by
      have sourceLength := CallableIndexedOwnedStoredArgumentAlignment.source_length values
      exact TypeSystem.Ty.productMany_inj (by omega) (bundle.trans signature.1)
    have nativeRow : nativeTypes = CompatibleBuiltinMeaning.argumentTypes function := by
      have nativeLength := values.length.1
      exact CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle (by omega)
        (nativeBundle.trans (nativeSignature.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function).symm))
    have rows := values_rep values
    rw [sourceRow, nativeRow] at rows
    obtain ⟨_sourceResult, called, represented, _applied, sameStore⟩ :=
      CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.reflects _
        (CellAwarePhysicalFunctionOrigins.observations profile) builtin rows
        (program := Program.ofChecked compiled.sourceProgram) (stages := registry) (invocation := invocation)
        (context := context) (before := before) completed
    subst sameStore
    refine ⟨_, _, before, mapping, world, called, ?_, heaps, .refl _, .refl _, .refl _ _, .refl _,
      CellAwareScopeAuthority.Effect.refl _ _ _ _, caller, (protocol headers keys).refl caller⟩
    rw [signature.2, nativeSignature.2]
    exact represented
  | global function =>
    obtain ⟨_actualType, ⟨association⟩⟩ := named_member profile related function rfl
    rcases association with ⟨_associationOwner, header, rawD, _identity, named, _descriptor, member, sourceAt,
      installed, _number, _projection, _typed, _canonical, captured, embedding, _sourceType, nativeEq, typeEq⟩
    have admitted : called header.instantiation := covers _ _ header.target
    obtain ⟨globalType, _valid, _evidence⟩ :
        (TypeSystem.Ty.function parameter result) = function.instantiation.type ∧ _ ∧ _ := by
      rcases Dynamic.ValueHasType.global_inv calleeTyped with ordinary | ⟨_inner, impossible, _typed⟩
      · exact ordinary
      · cases impossible
    have actualType : function.instantiation.type = header.named.specialized.function.type := by
      rw [sourceAt.retained]
      rfl
    have signature := TypeSystem.Ty.function.inj (globalType.trans (actualType.trans
      (RecursiveNamedPublicHistorySourceInputs.source_function_type wellFormed sourceAt)))
    have types : header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
      have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
      rw [header.parameters] at bodyTypes
      simpa only [List.map_map, Function.comp_def] using bodyTypes.symm
    have inputs := arity.global_count wellFormed sourceAt.frame.instantiated
    have parameterCount := congrArg List.length sourceAt.frame.parameters
    rw [header.parameters, List.length_map] at parameterCount
    have binderCount : sources.length = header.bindings.length := by omega
    have sourceRow : sourceTypes = header.types := by
      apply TypeSystem.Ty.productMany_inj _ (bundle.trans signature.1)
      rw [types, List.length_map, CallableIndexedOwnedStoredArgumentAlignment.source_length values]
      exact binderCount
    have argumentsTyped : Dynamic.ValuesHaveTypes context before sources
        (header.bindings.map (fun binding => binding.1.scheme.body)) := by
      rw [← types, ← sourceRow]
      exact sourcesTyped
    obtain ⟨bodyHeap, bodyArguments, supports⟩ := SelectedCompilationNamedAdmission.arguments
      ((SelectedCompilationNamedSupport.Support.of_program wellFormed).certified header) runtime heapTyped
      argumentsTyped
    have nativeSignature := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters typeEq
    have parameters := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles header.bindings values
      binderCount (by rw [sourceRow, types]) (nativeBundle.trans (nativeSignature.1.trans header.parameterType))
    obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_read (mapping := mapping) member
      keyPhysical.frame keyPhysical.prefixZero keyPhysical.locations (sizes header member admitted)
      (installed_read installed embedding cacheAuth) heaps.runtime_hasTypes
    have completedBody := completed
    rw [nativeEq] at completedBody
    obtain ⟨bodySize, bodySmaller, bodyEvaluation⟩ := payload_body completedBody
    have bodyCapture : EvaluationSize bodySize (DataPatternValues.packValues payloads :: capture.named.captured)
        store (header.code.rename capture.named.embedding.lift) value finalStore := by
      rw [capture.captured_eq, capture.embedding_eq, ← captured, ← embedding]
      exact bodyEvaluation
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, called, applied, finalHeaps, maps, worlds, frame,
        metadata, effect, returned, relatedPool⟩ :=
      applications header member admitted bodySize (by omega) owner caller capture cacheAuth member stable
        supports bodyHeap bodyArguments parameters heaps sourceAt bodyCapture
    refine ⟨sourceSize, outcome, after, finalMap, finalWorld, called, ?_, finalHeaps, maps, worlds, frame, metadata,
      effect, returned, relatedPool⟩
    rw [signature.2, nativeSignature.2, header.resultType]
    exact applied

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedIndirectLeaves
end
