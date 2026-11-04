import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.LambdaCompilation
import Solcore.SourceSemantics.CoreLowering.AcceptedTrees
import Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientStageOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReadBundles
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping

/-!
# Generalized locals: accepted bodies

Materialized generalized locals with an accepted body: instances, materialization, the body compiler, calls and catalog formation.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBody
/-! A contextual instance packet already contains its successful body compiler
call. Recover the complete body tree from that call without a lexical scanner
or a restriction on nested declarations, assignments or loops. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBody
open Core Frontend SourceInference
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet context representation binder policy lowerBody)

def bodyPolicy (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) (fuel : Nat) :
    SourceCoreLoops.Policy :=
  let repr := representation inputs prepared
  { repr.loopsWithSourceCells repr.expressions.sourceCells
      prepared.caller.function.solvedRequirements inputs.assignments inputs.diagnostics
      inputs.current.owner
      (FunctionCode.children (policy inputs prepared fuel) (lowerBody inputs prepared)
        fuel (context inputs prepared)) with
    sourceCells := repr.expressions.sourceCells
    lowerBinder := binder inputs prepared }

abbrev Receipt {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : Packet inputs candidate raw) :=
  AcceptedNamedBodyFlow.Body (bodyPolicy inputs packet.original.emission.prepared packet.fuel)
    packet.fuel packet.original.emission.prepared.source packet.certificate.bodyScope
    packet.statements packet.certificate.resultCore inputs.reasonAt
    (context inputs packet.original.emission.prepared).internalReason
    (context inputs packet.original.emission.prepared).internalReason packet.certificate.body

/-- The body belongs to the same contextual candidate, lexical substitution,
parameter scope and exact output stored by its original packet. -/
theorem of_packet {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : Packet inputs candidate raw) : Nonempty (Receipt packet) := by
  have accepted := packet.certificate.bodyCompiled
  change SourceCoreLoops.lowerStatementsWithPolicy
    (bodyPolicy inputs packet.original.emission.prepared packet.fuel)
    packet.fuel packet.original.emission.prepared.source packet.certificate.bodyScope
    packet.statements packet.certificate.resultCore inputs.reasonAt
    (context inputs packet.original.emission.prepared).internalReason
    (context inputs packet.original.emission.prepared).internalReason = .ok packet.certificate.body at accepted
  exact AcceptedNamedBodyFlow.body_of_accepted accepted

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInstances
/-! Creation retains the actual instance packet and accepted body instead of a
finite body profile. The original capture mapping and snapshot location remain
explicit through heap extension. No later body execution is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInstances
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalDescriptorOrigin (Origin)
open GeneralizedLocalInstanceValues (referenceIndex value)
open CallableIndexedHistory

variable {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}

/-- All rows of one initializer can retain the same genuine snapshot location.
The body receipt is derived from this packet's own contextual compiler call. -/
inductive Snapshot (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) (location : Core.Location) (attachment : Prop) :
    SourceCoreLocalPolymorphism.Instance → Core.Value → Prop where
  | retained {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
      {raw : Core.Expr} {actual : Core.Environment}
      (packet : Packet inputs candidate raw) (indexed : Indexed prepared packet)
      (body : Nonempty (GeneralizedLocalAcceptedBody.Receipt packet))
      (sameLexical : indexed.lexical = lexical)
      (owner : inputs.current.owner = binding.caller)
      (initializer : inputs.initializer = binding.initializer)
      (candidateSource : candidate.origin.source = binding.source)
      (candidateBinder : candidate.origin.binder.id = binding.binder.id)
      (attached : attachment)
      (origin : Origin prepared function binding lexical)
      (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
      (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
      (ownership : LocalIdentityOwnership function.source)
      (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
      (reference : captured.canonical[referenceIndex indexed]? =
        some (.cellRef prepared.ancestry.layout.frame.type location))
      (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
        raw candidate.type prepared.layouts.definitions)
      (runtimeTyped : RuntimeValueHasType world (value indexed captured.embedding origin.native actual)
        candidate.type prepared.layouts.definitions) :
      Snapshot prepared mapping world function binding lexical location attachment candidate
        (value indexed captured.embedding origin.native actual)

/-- The original API retains its exact source attachment. General creation
uses the same snapshot representation with its authentic paired history. -/
abbrev Framed (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) (location : Core.Location) :=
  Snapshot prepared mapping world function binding lexical location (function.source = binding.source)

variable {attachment : Prop}

theorem Snapshot.runtime_hasType {location : Core.Location}
    (framed : Snapshot prepared mapping world function binding lexical location attachment candidate native) :
    RuntimeValueHasType world native candidate.type prepared.layouts.definitions := by
  cases framed
  assumption

theorem Snapshot.extend {location : Core.Location}
    (framed : Snapshot prepared mapping world function binding lexical location attachment candidate native)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Snapshot prepared futureMapping futureWorld function binding lexical location attachment candidate native := by
  cases framed with
  | retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      attached origin captured declarations ownership issuer reference typed runtimeTyped =>
    exact .retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      attached origin (captured.extend maps worlds) declarations ownership issuer reference
      typed (runtimeTyped.weaken worlds)

abbrev Framed.runtime_hasType := @Snapshot.runtime_hasType
abbrev Framed.extend := @Snapshot.extend

def RepresentsWith (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) (attachment : Prop)
    (candidate : SourceCoreLocalPolymorphism.Instance) (native : Core.Value) : Prop :=
  ∃ location, Snapshot prepared mapping world function binding lexical location attachment candidate native

def Represents (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution)
    (candidate : SourceCoreLocalPolymorphism.Instance) (native : Core.Value) : Prop :=
  RepresentsWith prepared mapping world function binding lexical (function.source = binding.source) candidate native

/-- Both the original and general attachment use this one instance model.
Every snapshot independently retains the actual origin, code and captures. -/
def modelWith (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (attachment : Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → Substitution → Prop) :
    GeneralizedLocalDescriptorHeap.InstanceModel prepared.layouts.definitions where
  locals := prepared.base.locals
  Origin := fun function binding lexical => Nonempty (Origin prepared function binding lexical)
  Represents := fun mapping world function binding lexical =>
    RepresentsWith prepared mapping world function binding lexical (attachment function binding lexical)
  runtime_hasType := by
    intro mapping world function binding lexical candidate native represented
    obtain ⟨_, framed⟩ := represented
    exact framed.runtime_hasType
  extend := by
    intro mapping futureMapping world futureWorld function binding lexical candidate native represented maps worlds
    obtain ⟨location, framed⟩ := represented
    exact ⟨location, framed.extend maps worlds⟩

def model (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    GeneralizedLocalDescriptorHeap.InstanceModel prepared.layouts.definitions :=
  modelWith prepared (fun function binding _ => function.source = binding.source)

/-- The actual Origin.Pair, rather than equality with a canonical table,
attaches independently substituted Source to every stored snapshot. -/
def trackedModel (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    GeneralizedLocalDescriptorHeap.InstanceModel prepared.layouts.definitions :=
  modelWith prepared (fun _ _ _ => True)

theorem Snapshot.forget_attachment {location : Core.Location}
    (framed : Snapshot prepared mapping world function binding lexical location attachment candidate native) :
    Snapshot prepared mapping world function binding lexical location True candidate native := by
  cases framed with
  | retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      _ origin captured declarations ownership issuer reference typed runtimeTyped =>
    exact .retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      True.intro origin captured declarations ownership issuer reference typed runtimeTyped

/-- Creation evaluates the literal snapshot closure in the same store and
derives runtime typing from the accepted native type and capture environment.
It does not execute or restrict the instance body. -/
theorem formation_at_frame_with {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed prepared packet)
    {actual : Core.Environment}
    (sameLexical : indexed.lexical = lexical) (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (candidateSource : candidate.origin.source = binding.source)
    (candidateBinder : candidate.origin.binder.id = binding.binder.id)
    (attachment : Prop) (attached : attachment)
    (origin : Origin prepared function binding lexical)
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
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (value indexed captured.embedding origin.native actual) store ∧
    Snapshot prepared mapping world function binding lexical location attachment candidate
      (value indexed captured.embedding origin.native actual) := by
  have evaluated := GeneralizedLocalInstanceValues.formation_evaluates indexed captured reference read
  obtain ⟨future, _, finalStored, outputTyped⟩ :=
    evaluation_preserves_type evaluated (typed.rename captured.respects) captured.typed stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  exact ⟨evaluated, .retained packet indexed (GeneralizedLocalAcceptedBody.of_packet packet)
    sameLexical owner initializer candidateSource candidateBinder attached origin captured
    declarations ownership issuer reference typed outputTyped⟩

theorem formation_at_frame {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed prepared packet)
    {actual : Core.Environment}
    (sameLexical : indexed.lexical = lexical) (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (candidateSource : candidate.origin.source = binding.source)
    (candidateBinder : candidate.origin.binder.id = binding.binder.id)
    (descriptorSource : function.source = binding.source)
    (origin : Origin prepared function binding lexical)
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
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (value indexed captured.embedding origin.native actual) store ∧
    Framed prepared mapping world function binding lexical location candidate
      (value indexed captured.embedding origin.native actual) := by
  exact formation_at_frame_with indexed sameLexical owner initializer candidateSource candidateBinder
    (function.source = binding.source) descriptorSource origin captured declarations ownership issuer
    typed stored reference read

/-- Previously profiled instances embed with their same packet and actual body,
without changing the value, captured environment or native world. -/
theorem of_profiled
    (represented : GeneralizedLocalInstanceValues.Represents prepared mapping world
      function binding lexical candidate native) :
    Represents prepared mapping world function binding lexical candidate native := by
  cases represented with
  | retained packet indexed _ sameLexical owner initializer candidateSource candidateBinder descriptorSource
      origin _ _ captured declarations ownership issuer location reference typed runtimeTyped =>
    exact ⟨location, .retained packet indexed (GeneralizedLocalAcceptedBody.of_packet packet)
      sameLexical owner initializer candidateSource candidateBinder descriptorSource origin captured
      declarations ownership issuer reference typed runtimeTyped⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInstances
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedCode
/-! The materialized Source closure uses the exact native value stored at
declaration time. Equality follows from the accepted emitted expression, not
from running the creation code again in a changed store. A generalized
initializer is not snapshotted at creation; its `let` copies the captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedCode
open Core Frontend SourceInference
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open CallableIndexedHistory

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
  {packet : Packet inputs candidate raw}

theorem value_eq (indexed : Indexed prepared packet)
    {function : Dynamic.Closure} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : CallableIndexedLambdaValues.Code prepared function inputs.scope administrative viewRelation)
    (lowered : code.lowered = packet.original.lowered)
    (policy : code.policy = GeneralizedLocalLambdaCompilation.policy inputs packet.original.emission.prepared packet.fuel)
    (codeId : code.id = inputs.initializer)
    (embedding : Renaming) (native : NativeFrame) (actual : Core.Environment) :
    CallableIndexedLambdaValues.value code embedding native actual =
      GeneralizedLocalInstanceValues.value indexed embedding native actual := by
  have shared : code.policy.snapshotLambda code.id = false := by
    rw [policy, codeId]
    simp [GeneralizedLocalLambdaCompilation.policy]
  have emitted := code.emitted_shared shared
  conv at emitted => lhs; rw [lowered, packet.original.extracted, indexed.emitted]
  change Expr.inRight .word
      (.pair (.pair (.inLeft .word .unit)
        (.letE (.loadCell (.var (GeneralizedLocalInstanceValues.referenceIndex indexed)))
          (.lambda packet.certificate.parameterCore (LanguageResult.resultType packet.certificate.resultCore)
            (GeneralizedLocalInstanceValues.body indexed)))) (.word indexed.descriptor.id)) =
    Expr.inRight .word
      (.pair (.pair (.inLeft .word .unit)
        (.letE (.loadCell (.var code.referenceIndex))
          (.lambda code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore) code.body)))
        (.word code.descriptor.id)) at emitted
  have outer := Expr.pair.inj (Expr.inRight.inj emitted).2
  have lambda := Expr.lambda.inj (Expr.letE.inj (Expr.pair.inj outer.1).2).2
  have descriptor := Expr.word.inj outer.2
  unfold CallableIndexedLambdaValues.value GeneralizedLocalInstanceValues.value
  rw [← lambda.1, ← lambda.2.1, ← lambda.2.2, ← descriptor]

/-- The original emission's checked preparation supplies canonical stage
provenance for the actual materialized source and its full child key. -/
theorem source_receipt (indexed : Indexed prepared packet)
    {function : Dynamic.Closure} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : CallableIndexedLambdaValues.Code prepared function inputs.scope administrative viewRelation)
    (compilation : code.compilation = GeneralizedLocalLambdaCompilation.context inputs packet.original.emission.prepared)
    (active : code.active = packet.original.emission.prepared.substitution)
    (sourceEq : function.source = packet.original.emission.prepared.source) :
    LambdaSourceAlignment.SourceReceipt prepared.base.sourceProgram prepared.base.plan
      code.compilation.owner code.active function.source := by
  have authentic : LambdaSourceAlignment.SourceReceipt inputs.program inputs.current.plan
      candidate.origin.caller packet.original.emission.prepared.substitution packet.original.emission.prepared.source :=
    .contextual packet.original.emission.authentic
  simpa only [indexed.program, indexed.plan, ← indexed.owner, compilation, active, sourceEq,
    GeneralizedLocalLambdaCompilation.context] using authentic

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedCode
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedMaterialization
/-! In a named lexical context, the actual local read matcher identifies the
complete candidate substitution. The checked candidate's original source and
the allocation's descriptor source then determine the materialized body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedMaterialization
open Core Frontend SourceInference TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)

variable {catalog : SourceCoreLocalPolymorphism.Catalog} {caller : SourceCoreLocalPolymorphism.Key}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Core.Word}
  {lowered : SourceCoreBasic.LoweredExpr}

theorem lookup_eq
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller [] source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actual : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actual = receipt.node.rawType) :
    ∀ metavariable, semantic.lookup? metavariable = receipt.candidate.origin.substitution.lookup? metavariable := by
  have matched := receipt.matched
  simp only [EmptySourceSubstitution.scheme, EmptySourceSubstitution.type] at matched
  have originalType : receipt.original.rawType = receipt.node.rawType := by
    simpa only [EmptySourceSubstitution.type] using receipt.rawType
  have actualMatch : SourceSpecialization.matchClosedSchemeInstance? function.binder.scheme actual =
      some receipt.child := by
    simpa only [sameScheme, sameType, originalType] using matched
  have key : receipt.candidate.origin.substitution = receipt.child := by
    have identity : receipt.child.compose [] = receipt.child := by
      simp [Substitution.compose, List.filter_eq_self]
    exact receipt.candidate_key.trans identity
  intro metavariable
  rw [key]
  exact CallableClosedSchemeSubstitutionAgreement.runtime_instantiation_lookup_eq actualMatch instantiation metavariable

/-- These source identities are supplied by the actual declaration site and
the statically checked catalog row, while the substitution comes from Source. -/
theorem source_eq
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller [] source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actual : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actual = receipt.node.rawType)
    (descriptorSource : function.source = receipt.binding.source)
    (candidateSource : receipt.candidate.origin.source = receipt.binding.source)
    {inputs : Inputs} {raw : Core.Expr}
    (packet : Packet inputs receipt.candidate raw) :
    (function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source =
      packet.original.emission.prepared.source := by
  change function.source.applySubstitution semantic = _
  rw [GeneralizedLocalLambdaEmissionFacts.Emission.source]
  have same := CallableFlexibleSubstitutionAgreement.typedSource_congr
    (lookup_eq receipt instantiation sameScheme sameType) function.source
  simpa only [descriptorSource, candidateSource] using same

/-- The Source capture occurrence and the accepted emitted lambda determine
the exact parameter, result and statement header of the materialized closure. -/
theorem header
    {function : Dynamic.GeneralizedClosure} {semantic : Substitution} {evidence : Dynamic.EvidenceEnvironment}
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
    (packet : Packet inputs candidate raw)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = inputs.initializer)
    (sourceEq : (function.instantiate semantic evidence).source = packet.original.emission.prepared.source) :
    (function.instantiate semantic evidence).parameters = packet.parameters ∧
    (function.instantiate semantic evidence).resultType = packet.result ∧
    (function.instantiate semantic evidence).body = packet.statements := by
  obtain ⟨node, occurrence, form, _⟩ := captures.occurrence
  have found := lookupExpression?_complete unique occurrence
  have substituted := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution
    function.source semantic function.initializer node found
  change (function.instantiate semantic evidence).source.lookupExpression? function.initializer = _ at substituted
  simp only [sourceEq, initializer] at substituted
  have sameNode := Option.some.inj (substituted.symm.trans packet.found)
  have sameForm := (congrArg ExpressionNode.form sameNode).trans packet.form
  simp only [ExpressionNode.applySubstitution, form, ExpressionForm.applySubstitution] at sameForm
  exact ExpressionForm.lambda.inj sameForm

/-- The actual named read, its retained capture row and accepted compiler
packet construct ordinary raw Code for the exact materialized Source closure. -/
theorem code_at_read
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller [] source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actualType : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actualType requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actualType = receipt.node.rawType)
    (descriptorSource : function.source = receipt.binding.source)
    (candidateSource : receipt.candidate.origin.source = receipt.binding.source)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {inputs : Inputs} {raw : Core.Expr}
    (packet : Packet inputs receipt.candidate raw)
    (indexed : GeneralizedLocalLambdaGeneration.Indexed prepared packet)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = inputs.initializer)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw receipt.candidate.type prepared.layouts.definitions)
    (profile : checked.catalog.callableContracts = true)
    (native : CallableIndexedHistory.NativeFrame) :
    let instantiated := function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ code : CallableIndexedLambdaValues.Code prepared instantiated inputs.scope captured.administrative,
      code.compilation = GeneralizedLocalLambdaCompilation.context inputs packet.original.emission.prepared ∧
      code.active = packet.original.emission.prepared.substitution ∧
      code.id = inputs.initializer ∧ code.lowered = packet.original.lowered ∧
      code.policy = GeneralizedLocalLambdaCompilation.policy inputs packet.original.emission.prepared packet.fuel ∧
      code.lowerBody = GeneralizedLocalLambdaCompilation.lowerBody inputs packet.original.emission.prepared ∧
      code.fuel = packet.fuel ∧ code.descriptor.id = indexed.descriptor.id ∧
      HEq code.receipt packet.certificate ∧
      code.view = packet.original.emission.prepared.source ∧
      code.reasonAt = inputs.reasonAt ∧
      CallableIndexedLambdaValues.value code captured.embedding native actual =
        GeneralizedLocalInstanceValues.value indexed captured.embedding native actual := by
  have sourceEq := source_eq receipt instantiation sameScheme sameType descriptorSource candidateSource packet
  obtain ⟨parameters, result, body⟩ := header packet captures unique initializer sourceEq
  have view : LambdaMetadataViews.MetadataView
      (function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source
      packet.original.emission.prepared.source := by
    rw [sourceEq]
    exact .refl _
  have typedLowered : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      packet.original.lowered.expression (LanguageResult.resultType packet.original.lowered.type)
      prepared.layouts.definitions := by
    rw [packet.original.extracted, ← packet.original.nativeType]
    exact LanguageResult.success_hasType typed
  obtain ⟨code, compilation, active, id, lowered, policy, lowerBody, fuel, descriptor, certificate, codeView, reasons⟩ :=
    indexed.code_at_read _ captured.administrative parameters result body profile view typedLowered
  exact ⟨code, compilation, active, id, lowered, policy, lowerBody, fuel, descriptor, certificate, codeView, reasons,
    GeneralizedLocalMaterializedCode.value_eq indexed code lowered policy id captured.embedding native actual⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedMaterialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
/-! Materialized local functions retain their real compiler row, Source
instantiation, lexical capture and read-time view. The relation records no
execution law for the body and does not identify the two native contexts.
The body evidence is the actual accepted tree, without a finite lexical profile. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalDescriptorOrigin (Origin)

structure Materialization (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure)
    (viewRelation : TypedSource → TypedSource → Prop := LambdaMetadataViews.MetadataView) where
  descriptor : Dynamic.GeneralizedClosure
  binding : SourceCoreLocalPolymorphism.Binding
  lexical : TypeSystem.Substitution
  inputs : Inputs
  candidate : SourceCoreLocalPolymorphism.Instance
  raw : Expr
  packet : Packet inputs candidate raw
  indexed : Indexed compiled.indexed packet
  body : Nonempty (GeneralizedLocalAcceptedBody.Receipt packet)
  sameLexical : indexed.lexical = lexical
  owner : inputs.current.owner = binding.caller
  initializer : inputs.initializer = binding.initializer
  candidateSource : candidate.origin.source = binding.source
  candidateBinder : candidate.origin.binder.id = binding.binder.id
  descriptorInitializer : descriptor.initializer = binding.initializer
  origin : Origin compiled.indexed descriptor binding lexical
  descriptorUnique : NodeOccurrencesUnique descriptor.source
  sourceCaptures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source
    descriptor.captured descriptor.binder descriptor.initializer descriptor
  context : Solcore.SourceSemantics.Context
  callerEvidence : Dynamic.EvidenceEnvironment
  produced : Dynamic.EvidenceEnvironment
  actualType : TypeSystem.Ty
  requirements : List RequirementId
  semantic : TypeSystem.Substitution
  instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
    actualType requirements semantic produced
  materialized : function = descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
  actual : Environment
  captured : Captures compiled.indexed mapping world inputs.scope function.captured actual
  capturedDeclarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.context
  frameLocation : Core.Location
  frameReference : captured.canonical[GeneralizedLocalInstanceValues.referenceIndex indexed]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation)
  code : Code compiled.indexed function inputs.scope captured.administrative viewRelation
  compilation : code.compilation = GeneralizedLocalLambdaCompilation.context inputs packet.original.emission.prepared
  active : code.active = packet.original.emission.prepared.substitution
  lowered : code.lowered = packet.original.lowered
  codeId : code.id = inputs.initializer
  policy : code.policy = GeneralizedLocalLambdaCompilation.policy inputs packet.original.emission.prepared packet.fuel
  lowerBody : code.lowerBody = GeneralizedLocalLambdaCompilation.lowerBody inputs packet.original.emission.prepared
  fuel : code.fuel = packet.fuel
  descriptorId : code.descriptor.id = indexed.descriptor.id
  certificate : HEq code.receipt packet.certificate
  view : code.view = packet.original.emission.prepared.source
  reasons : code.reasonAt = inputs.reasonAt
  rawTyped : RuntimeValueHasType world (CallableIndexedLambdaValues.value code captured.embedding origin.native actual)
    candidate.type compiled.indexed.layouts.definitions
  ownership : LocalIdentityOwnership function.source
  issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs
  unique : NodeOccurrencesUnique function.source

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure}
  {viewRelation : TypedSource → TypedSource → Prop}

def Materialization.extend (material : Materialization compiled mapping world function viewRelation)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Materialization compiled futureMapping futureWorld function viewRelation :=
  { material with captured := material.captured.extend maps worlds
                  rawTyped := material.rawTyped.weaken worlds }

/-- Weakening view evidence retains the same stored packet and every capture. -/
def Materialization.weaken_view {after : TypedSource → TypedSource → Prop}
    (material : Materialization compiled mapping world function viewRelation)
    (weaken : ∀ source view, viewRelation source view → after source view) :
    Materialization compiled mapping world function after :=
  { material with code := material.code.weaken_view weaken }

theorem Materialization.frame_reference (material : Materialization compiled mapping world function viewRelation) :
    material.captured.canonical[material.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type material.frameLocation) := by
  simpa only [Code.referenceIndex, material.compilation, GeneralizedLocalInstanceValues.referenceIndex]
    using material.frameReference

/-- Canonical provenance belongs to the compiler view. The independently
substituted runtime Source is carried by the actual paired history. -/
theorem Materialization.compiler_source_receipt (material : Materialization compiled mapping world function viewRelation) :
    LambdaSourceAlignment.SourceReceipt compiled.indexed.base.sourceProgram compiled.indexed.base.plan
      material.code.compilation.owner material.code.active material.code.view := by
  have authentic : LambdaSourceAlignment.SourceReceipt material.inputs.program material.inputs.current.plan
      material.candidate.origin.caller material.packet.original.emission.prepared.substitution
      material.packet.original.emission.prepared.source :=
    .contextual material.packet.original.emission.authentic
  simpa only [material.indexed.program, material.indexed.plan, ← material.indexed.owner,
    material.compilation, material.active, material.view, GeneralizedLocalLambdaCompilation.context] using authentic

/-- Compatibility for clients whose actual source is the canonical compiler
view. General applied origins use the independent paired-source producer. -/
theorem Materialization.source_receipt_of_eq (material : Materialization compiled mapping world function viewRelation)
    (same : function.source = material.code.view) :
    LambdaSourceAlignment.SourceReceipt compiled.indexed.base.sourceProgram compiled.indexed.base.plan
      material.code.compilation.owner material.code.active function.source := by
  rw [same]
  exact material.compiler_source_receipt

abbrev Materialization.source_receipt := @Materialization.source_receipt_of_eq

theorem Materialization.native_type (material : Materialization compiled mapping world function viewRelation) :
    material.candidate.type = CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore := by
  have same := GeneralizedLocalMaterializedCode.value_eq material.indexed material.code material.lowered
    material.policy material.codeId
    material.captured.embedding material.origin.native material.actual
  have shape := Value.closure.inj (Value.pair.inj (Value.pair.inj same).1).2
  have result := (Ty.sum.inj shape.2.1).2
  rw [shape.1, result]
  exact material.indexed.nativeType

/-- The compiler-selected read wrapper and the captured reference remain
available after the read has returned and the caller has changed. -/
structure View (material : Materialization compiled mapping world function viewRelation) where
  owner : SourceCoreLocalPolymorphism.Key
  active : TypeSystem.Substitution
  source : TypedSource
  scope : SourceCoreLocalCell.Scope
  expression : ExpressionId
  original : SourceCoreBasic.LoweredExpr
  lowered : SourceCoreBasic.LoweredExpr
  accepted : SourceCoreCallableIndexedAncestry.lowerView compiled.indexed.ancestry owner active source scope
    expression original = .ok lowered
  id : Word
  referenceIndex : Nat
  emitted : lowered.expression = SourceCoreCallableIndexedAncestry.viewLower compiled.indexed.ancestry.layout.frame
    material.code.receipt.parameterCore material.code.receipt.resultCore id material.code.descriptor.id
    referenceIndex original.expression
  callerNative : NativeFrame
  callerGhost : GhostFrame
  caller : MetadataState
  carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    callerNative callerGhost (some caller)
  recipe : CallableAppliedViewProvenance.Recipe compiled.indexed.ancestry.graph.inputs callerGhost
    material.origin.ghost caller material.origin.metadata id material.code.descriptor.id
  initializer : material.descriptor.initializer = recipe.read.entry.view.principal.initializer
  scheme : material.descriptor.binder.scheme = recipe.read.binder.scheme
  actualType : material.actualType = recipe.read.node.rawType
  embedding : Renaming
  environment : Environment
  location : Core.Location
  reference : environment[embedding referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type location)
  lexicalReference : material.captured.canonical[material.code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type location)

theorem View.materialized_pair {material : Materialization compiled mapping world function viewRelation} (view : View material) :
    CallableAppliedDynamicSourceMaterialization.Pair compiled.indexed.ancestry.graph.inputs
      (.appliedView view.id material.code.descriptor.id view.callerGhost material.origin.ghost)
      (view.recipe.read.after material.origin.metadata) function.source := by
  have captures : Dynamic.GeneralizedClosureCaptures material.descriptor.definitionContext material.descriptor.source
      material.descriptor.captured material.descriptor.binder view.recipe.read.entry.view.principal.initializer
      material.descriptor := by
    rw [← view.initializer]
    exact material.sourceCaptures
  have result := material.origin.materialize view.recipe captures material.descriptorUnique
    material.instantiation view.scheme view.actualType
  simpa only [← material.materialized] using result.1

def View.native {material : Materialization compiled mapping world function viewRelation} (view : View material) : Value :=
  GeneralizedLocalReadView.value compiled.indexed.ancestry.layout.frame
    material.code.receipt.parameterCore material.code.receipt.resultCore view.id material.code.descriptor.id
    view.referenceIndex view.embedding view.callerNative (.inLeft .word .unit)
    (.closure material.code.receipt.parameterCore (LanguageResult.resultType material.code.receipt.resultCore)
      (material.code.body.rename material.captured.embedding.lift.lift)
      (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual))
    view.environment

def View.extend {material : Materialization compiled mapping world function viewRelation} (view : View material)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    View (material.extend maps worlds) :=
  { view with }

def View.weaken_view {after : TypedSource → TypedSource → Prop}
    {material : Materialization compiled mapping world function viewRelation} (view : View material)
    (weaken : ∀ source target, viewRelation source target → after source target) :
    View (material.weaken_view weaken) := { view with }

theorem View.weaken_view_native {after : TypedSource → TypedSource → Prop}
    {material : Materialization compiled mapping world function viewRelation} (view : View material)
    (weaken : ∀ source target, viewRelation source target → after source target) :
    (view.weaken_view weaken).native = view.native := rfl

inductive Association (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping)
    {viewRelation : optParam (TypedSource → TypedSource → Prop) LambdaMetadataViews.MetadataView} :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | viewed {function : Dynamic.Closure} (material : Materialization compiled mapping world function viewRelation)
      (view : View material)
      (typed : RuntimeValueHasType world view.native
        (CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore)
        compiled.indexed.layouts.definitions) :
      Association compiled mapping world (viewRelation := viewRelation) function view.native material.code.receipt.loweredParameters
        material.code.receipt.parameterCore material.code.receipt.resultCore

variable {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

def Association.AtFrame
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result)
    (location : Core.Location) : Prop :=
  match member with
  | .viewed _ view _ => view.location = location

theorem Association.projection
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result) :
    compiled.compatible.checked.catalog.project (FunctionValues.sourceType function) =
      .ok (CallableContract.functionType parameter result) := by
  cases member with
  | viewed material _ _ => exact material.code.projection

theorem Association.runtime_hasType
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result) :
    RuntimeValueHasType world native (CallableContract.functionType parameter result) compiled.indexed.layouts.definitions := by
  cases member with
  | viewed _ _ typed => exact typed

def Association.extend
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association compiled futureMapping futureWorld (viewRelation := viewRelation) function native bindings parameter result := by
  cases member with
  | viewed material view typed =>
    exact .viewed (material.extend maps worlds) (view.extend maps worlds) (typed.weaken worlds)

def Association.weaken_view {after : TypedSource → TypedSource → Prop}
    (member : Association compiled mapping world (viewRelation := viewRelation)
      function native bindings parameter result)
    (weaken : ∀ source view, viewRelation source view → after source view) :
    Association compiled mapping world (viewRelation := after) function native bindings parameter result := by
  cases member with
  | viewed material view typed =>
    exact .viewed (material.weaken_view weaken) (view.weaken_view weaken) typed

theorem Association.stage_origin
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  cases member with
  | viewed material view _ =>
    have captures : Dynamic.GeneralizedClosureCaptures material.descriptor.definitionContext
        material.descriptor.source material.descriptor.captured material.descriptor.binder
        view.recipe.read.entry.view.principal.initializer material.descriptor := by
      rw [← view.initializer]
      exact material.sourceCaptures
    let payload : Value := match view.native with
      | .pair payload _ => payload
      | _ => .unit
    have result := GeneralizedLocalAppliedSourceOrigins.materialized material.origin view.recipe
      captures material.descriptorUnique material.instantiation view.scheme view.actualType payload
    simpa only [← material.materialized, payload, View.native, GeneralizedLocalReadView.value] using result.2


theorem Association.observation
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    CompatibleEquality.Observation compiled.compatible.checked.catalog registry identities
      (CallableContract.functionType parameter result) (.closure function) native := by
  cases member with
  | viewed _ _ _ => exact .contractedAnonymous _ _ _ _ _ profile

theorem Association.source_binders
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body) := by
  cases member with
  | viewed material _ _ =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) material.code)).symm

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBodyCompiler
/-! Materialization enters the same complete accepted lambda body. Its actual
Source frame supplies the parameter context without a finite body profile. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBodyCompiler
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalAcceptedMaterialization
open GeneralizedLocalLambdaCompilation (representation binder)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {viewRelation : TypedSource → TypedSource → Prop}
  (material : Materialization compiled mapping world function viewRelation)

def policy : SourceCoreLoops.Policy :=
  let actual := representation material.inputs material.packet.original.emission.prepared
  { actual.loopsWithSourceCells actual.expressions.sourceCells
      material.packet.original.emission.prepared.caller.function.solvedRequirements
      material.inputs.assignments material.inputs.diagnostics material.inputs.current.owner
      (FunctionCode.children material.code.policy material.code.lowerBody material.code.fuel material.code.compilation) with
    sourceCells := actual.expressions.sourceCells
    lowerBinder := binder material.inputs material.packet.original.emission.prepared }

theorem callback : material.code.lowerBody
    (FunctionCode.children material.code.policy material.code.lowerBody material.code.fuel material.code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy (policy material) := by
  rw (occs := .pos [1]) [material.lowerBody]
  rfl

theorem expression_reader : (policy material).lowerExpression =
    FunctionCode.children material.code.policy material.code.lowerBody material.code.fuel material.code.compilation := by
  unfold policy representation
  rw [material.indexed.represented]
  rfl

theorem statement_reader : (policy material).readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := by
  unfold policy representation
  rw [material.indexed.represented]
  rfl

/-- The same source closure and compiled view use the complete original body. -/
theorem lambda_fields : material.packet.parameters = function.parameters ∧
    material.packet.result = function.resultType ∧ material.packet.statements = function.body := by
  have found := material.code.found
  rw [material.codeId, material.view] at found
  have same := Option.some.inj (material.packet.found.symm.trans found)
  have form := material.code.form.trans material.code.sourceForm
  exact ExpressionForm.lambda.inj (material.packet.form.symm.trans
    ((congrArg ExpressionNode.form same).trans form))

/-- Readout materialization retains the same actual whole-body compiler call,
with its parameter scope and full unfiltered statement list. -/
theorem body_receipt : Nonempty (AcceptedNamedBodyFlow.Body (policy material)
    material.code.fuel material.code.view
    (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
    function.body material.code.receipt.resultCore material.code.reasonAt
    material.code.compilation.internalReason material.code.compilation.internalReason material.code.receipt.body) := by
  exact AcceptedNamedBodyFlow.body_of_accepted
    (CallableIndexedLambdaSemanticInvocation.loops_accepted
      (values := .initial compiled.compatible.checked) material.code (policy material) (callback material))

/-- Complete Source lambda typing supplies the actual parameter context.
The real global layout fixes the native reference slot independently of types. -/
theorem entry_context {program : Program} (frame : Dynamic.ClosureFrame program function)
    (ownership : LocalIdentityOwnership function.source)
:
    Nonempty (CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code) := by
  obtain ⟨id, node, contains, form, raw, typing⟩ := frame.code.occurrence
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) material.code ownership contains form
  have reference : material.code.referenceIndex =
      material.inputs.scope.length + 1 + compiled.indexed.base.globals.length := by
    unfold CallableIndexedLambdaValues.Code.referenceIndex
    rw [material.compilation]
    change material.inputs.scope.length + material.inputs.current.administrativePrefix + material.inputs.current.globals.length = _
    rw [material.indexed.administrativePrefix, material.indexed.globals]
  rw [form] at typing
  generalize rawEq : TypeSystem.Ty.function
    (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) function.resultType = rawType at typing
  generalize planEq : ExpressionRequirementPlan.ordinary [] = plan at typing
  cases typing with
  | lambda unique extended bodyTyped completes =>
    exact ⟨⟨_, _, extended, kinds, reference⟩⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBodyCompiler
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedCall
/-! The outer read wrapper and inner lexical wrapper compose around the same
real frame cell. A completed body retains all other writes and allocations,
while both successful and failed calls restore the current caller's frame. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues
open GeneralizedLocalAcceptedMaterialization

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {viewRelation : TypedSource → TypedSource → Prop}
  {material : Materialization compiled mapping world function viewRelation}

def View.transient (view : View material) : NativeFrame :=
  SourceCoreCallableIndexedDispatch.readFrame view.id material.code.descriptor.id view.callerNative

def View.selected (view : View material) : NativeFrame :=
  SourceCoreCallableIndexedDispatch.selectedFrame compiled.indexed.ancestry.graph.table
    material.code.descriptor.id material.origin.native view.transient

def View.bodyEnvironment (view : View material) (argument : Value) : Environment :=
  .unit :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.transient :: argument ::
    SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual

def View.entry (view : View material) (argument : Value) : Environment :=
  argument :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.callerNative ::
    CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual :: view.environment

def View.body (view : View material) : Expr :=
  (SourceCoreCallableIndexedAncestry.viewBody compiled.indexed.ancestry.layout.frame view.id material.code.descriptor.id
    view.referenceIndex).rename view.embedding.lift.lift.lift

theorem View.agreement (view : View material) {argument saved : Value} {store : Store}
    (current : store.read? view.location = some saved) :
    let selected := SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.selected
    (∀ {output finalStore},
      Evaluates (view.bodyEnvironment argument) (store.set view.location selected)
        (material.code.receipt.rawBody.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding material.captured.embedding))
        output finalStore →
      Evaluates (view.entry argument) store view.body output (finalStore.set view.location saved)) ∧
    (∀ {output finalStore}, Evaluates (view.entry argument) store view.body output finalStore →
      ∃ bodyStore,
        Evaluates (view.bodyEnvironment argument) (store.set view.location selected)
          (material.code.receipt.rawBody.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding material.captured.embedding))
          output bodyStore ∧ finalStore = bodyStore.set view.location saved) := by
  let transient := SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.transient
  have bound : view.location < store.length := (List.getElem?_eq_some_iff.mp current).choose
  have installed : Store.read? (store.set view.location transient) view.location = some transient :=
    Store.write?_reads_written (Store.write?_eq_some_iff.mpr ⟨bound, rfl⟩)
  have inner := GeneralizedLocalCallFrame.agreement material.origin material.captured material.code
    view.carried view.recipe view.lexicalReference installed (argument := argument)
  have outer := GeneralizedLocalReadView.agreement view.reference current
    (parameter := material.code.receipt.parameterCore) (result := material.code.receipt.resultCore)
    (id := view.id) (target := material.code.descriptor.id) (caller := view.callerNative)
    (identity := .inLeft .word .unit)
    (innerBody := material.code.body.rename material.captured.embedding.lift.lift)
    (innerEnvironment := SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual)
    (argument := argument)
  constructor
  · intro output finalStore evaluated
    have bodyEvaluation := inner.1 (by simpa only [List.set_set, View.bodyEnvironment, View.selected, View.transient, View.entry, View.body, CallableIndexedLambdaValues.value] using evaluated)
    simpa only [List.set_set, View.bodyEnvironment, View.selected, View.transient, View.entry, View.body, CallableIndexedLambdaValues.value] using outer.1 bodyEvaluation
  · intro output finalStore evaluated
    obtain ⟨innerStore, innerEvaluation, outerEq⟩ := outer.2 evaluated
    obtain ⟨bodyStore, bodyEvaluation, innerEq⟩ := inner.2 innerEvaluation
    refine ⟨bodyStore, ?_, ?_⟩
    · simpa only [List.set_set, View.bodyEnvironment, View.selected, View.transient, View.entry, View.body, CallableIndexedLambdaValues.value] using bodyEvaluation
    · simpa only [innerEq, List.set_set] using outerEq

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedCatalogFormation
/-! The actual compiler catalog supplies candidate origins at creation and at
a later read. Snapshot formation uses the same Packet, captured environment
and stored frame; no independent candidate Source or binder equality is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedCatalogFormation
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalDescriptorOrigin (Origin)
open GeneralizedLocalInstanceValues (referenceIndex value)
open GeneralizedLocalAcceptedInstances (Snapshot)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

theorem read_origins {caller : SourceCoreLocalPolymorphism.Key} {active : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals
      caller active source scope id reason lowered) :
    receipt.candidate.origin.caller = caller ∧
      receipt.candidate.origin.source = receipt.binding.source ∧
      receipt.candidate.origin.binder = receipt.binding.binder ∧
      receipt.candidate.origin.initializer = receipt.binding.initializer :=
  SelectedCompilationLocalOrigins.at_context compiled receipt.bindingFound
    (List.mem_of_getElem? receipt.candidate_at)

theorem formation_at_frame {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {candidate : SourceCoreLocalPolymorphism.Instance}
    {inputs : Inputs} {raw : Core.Expr} {packet : Packet inputs candidate raw}
    (indexed : Indexed compiled.indexed packet) {actual : Core.Environment}
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext lexical)
    (sameLexical : indexed.lexical = lexical)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin compiled.indexed function binding lexical)
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world
      inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type compiled.indexed.layouts.definitions)
    {store : Store} {location : Location}
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (reference : captured.canonical[referenceIndex indexed]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (value indexed captured.embedding origin.native actual) store ∧
    Snapshot compiled.indexed mapping world function binding lexical location True candidate
      (value indexed captured.embedding origin.native actual) := by
  obtain ⟨_, source, binder, _⟩ := SelectedCompilationLocalOrigins.at_context compiled located member
  exact GeneralizedLocalAcceptedInstances.formation_at_frame_with indexed sameLexical owner initializer
    source (congrArg TypedBinder.id binder) True True.intro origin captured declarations ownership issuer
    typed stored reference read

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedCatalogFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedAssociationFormation
/-! The selected row of an actual generalized allocation supplies the complete
materialized association. The Source substitution and dictionary are supplied
by the actual read rule; all compiler ancestry is recovered from that row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedAssociationFormation
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalAcceptedMaterialization

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping : LocationMap} {world : StoreTyping}
  {caller : SourceCoreLocalPolymorphism.Key} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem materialize_framed
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller [] source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {lexical : TypeSystem.Substitution} {native : Value}
    {frameLocation : Core.Location}
    (row : GeneralizedLocalAcceptedInstances.Framed compiled.indexed mapping world descriptor
      receipt.binding lexical frameLocation receipt.candidate native)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source descriptor.captured
      descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actualType = receipt.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      material.frameLocation = frameLocation ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual := by
  cases row with
  | retained packet indexed acceptedBody sameLexical owner instanceInitializer candidateSource candidateBinder descriptorSource origin captured declarations ownership issuer frameReference typed runtimeTyped =>
    have initializerEq := initializer.trans instanceInitializer.symm
    obtain ⟨code, compilation, active, _id, loweredEq, _policy, _lowerBody, _fuel, _descriptor, _certificate, codeView, reasons, valueEq⟩ :=
      GeneralizedLocalNamedMaterialization.code_at_read receipt instantiation sameScheme sameType
        descriptorSource candidateSource packet indexed captures unique initializerEq captured typed profile origin.native
    have materializedUnique : NodeOccurrencesUnique
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source := by
      change ((descriptor.source.applySubstitution semantic).nodes.map Node.occurrenceId).Nodup
      change (descriptor.source.nodes.map Node.occurrenceId).Nodup at unique
      simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique
    let material : Materialization compiled mapping world
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)) :=
      { descriptor := descriptor, binding := receipt.binding, lexical := lexical
        inputs := _, candidate := receipt.candidate, raw := _, packet := packet, indexed := indexed, body := acceptedBody
        sameLexical := sameLexical, owner := owner, initializer := instanceInitializer
        candidateSource := candidateSource, candidateBinder := candidateBinder, descriptorInitializer := initializer
        origin := origin, descriptorUnique := unique, sourceCaptures := captures, context := context, callerEvidence := callerEvidence
        produced := produced, actualType := actualType, requirements := requirements, semantic := semantic
        instantiation := instantiation, materialized := rfl, actual := _, captured := captured
        capturedDeclarations := GeneralizedLocalScopeDeclarations.materialized declarations semantic (produced ++ callerEvidence.applySubstitution semantic)
        frameLocation := frameLocation, frameReference := frameReference, code := code
        compilation := compilation, active := active, lowered := loweredEq, codeId := _id, policy := _policy, lowerBody := _lowerBody,
        fuel := _fuel, descriptorId := _descriptor, certificate := _certificate, view := codeView, reasons := reasons,
        rawTyped := valueEq.symm ▸ runtimeTyped,
        ownership := FlexibleSubstitution.LocalIdentityOwnership.applySubstitution semantic ownership,
        issuer := issuer, unique := materializedUnique }
    exact ⟨material, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, valueEq.symm⟩


theorem materialize
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller [] source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {lexical : TypeSystem.Substitution} {native : Value}
    (row : GeneralizedLocalAcceptedInstances.Represents compiled.indexed mapping world descriptor
      receipt.binding lexical receipt.candidate native)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source descriptor.captured
      descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actualType = receipt.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual := by
  obtain ⟨location, framed⟩ := row
  obtain ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, actualEq, semanticEq,
    contextEq, callerEq, producedEq, requirementsEq, _frameEq, nativeEq⟩ :=
    materialize_framed receipt framed captures unique initializer instantiation sameScheme sameType profile
  exact ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, actualEq, semanticEq,
    contextEq, callerEq, producedEq, requirementsEq, nativeEq⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedAssociationFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedReadApplication
/-! The saved descriptor and the actual emitted lambda discharge application
metadata checks. Read preparation remains a separate, occurrence-specific
ledger obligation; this proof does not assume a prepared application edge. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedReadApplication
open Core Frontend SourceInference TypeSystem
open GeneralizedLocalAcceptedMaterialization
open SourceCoreCallableAncestryReadRecipes
open CallableAncestryMetadata (eraseRequirements eraseNodeRequirements)

private theorem erased_lookup (source : TypedSource) (id : ExpressionId) :
    (eraseRequirements source).lookupExpression? id =
      (source.lookupExpression? id).map (fun node => {node with requirements := []}) := by
  unfold TypedSource.lookupExpression? TypedSource.lookupNode?
  simp only [eraseRequirements, List.find?_map]
  have predicate : ((fun candidate : Node => decide (candidate.occurrenceId = id.occurrence)) ∘
      eraseNodeRequirements) = (fun candidate => decide (candidate.occurrenceId = id.occurrence)) := by
    funext candidate
    cases candidate <;> rfl
  rw [predicate]
  cases found : source.nodes.find? (fun candidate => decide (candidate.occurrenceId = id.occurrence)) with
  | none => rfl
  | some node => cases node <;> rfl

private theorem pair_lambda
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame} {metadata : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame metadata source)
    {id : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    ∃ original : ExpressionNode, metadata.metadata.source.lookupExpression? id = some original ∧ original.form = node.form := by
  have same := congrArg (fun source : TypedSource => source.lookupExpression? id)
    (CallableAppliedDynamicSourceMaterialization.erase_source paired)
  rw [erased_lookup, erased_lookup, found] at same
  cases actual : metadata.metadata.source.lookupExpression? id with
  | none => simp [actual] at same
  | some original =>
    rw [actual] at same
    have erased : ({original with requirements := []} : ExpressionNode) = {node with requirements := []} :=
      Option.some.inj same
    have forms := congrArg ExpressionNode.form erased
    exact ⟨original, rfl, forms⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : GeneralHeap.LocationMap}
  {world : StoreTyping} {function : Dynamic.Closure}
  {viewRelation : TypedSource → TypedSource → Prop}

/-- The actual code selects the initializer and lexical owner checked by the
same real read. The header check follows from its real Source instantiation. -/
theorem apply_read (material : Materialization compiled mapping world function viewRelation)
    {caller : SourceCoreCallableAncestryReadRecipes.State} {id : Word}
    (read : Read compiled.indexed.ancestry.graph.inputs caller id material.code.descriptor.id)
    (scheme : material.descriptor.binder.scheme = read.binder.scheme)
    (actualType : material.actualType = read.node.rawType) :
    material.descriptor.initializer = read.entry.view.principal.initializer ∧
    ∃ applied, applyRead read material.origin.metadata = .ok applied := by
  obtain ⟨template, selected, _authentic, owner, initial, _active, header⟩ :=
    CallableIndexedLambdaTemplatePermission.selected material.code
  have templateEq : read.template = template := Option.some.inj (read.targetSelected.symm.trans selected)
  have origins := SourceCoreStageCodebook.Origin.lambda.inj
    (read.templateOrigin.symm.trans read.viewOrigin)
  have initializer : material.descriptor.initializer = read.entry.view.principal.initializer := by
    calc
      material.descriptor.initializer = material.binding.initializer := material.descriptorInitializer
      _ = material.inputs.initializer := material.initializer.symm
      _ = material.code.id := material.codeId.symm
      _ = template.id := initial.symm
      _ = read.template.id := congrArg SourceCoreLambdaTemplates.Lambda.id templateEq.symm
      _ = read.entry.view.principal.initializer := origins.2.1
  have lexicalOwner : material.origin.metadata.metadata.owner = read.entry.view.owner := by
    calc
      material.origin.metadata.metadata.owner = material.binding.caller := material.origin.owner
      _ = material.inputs.current.owner := material.owner.symm
      _ = material.code.compilation.owner := by rw [material.compilation]; rfl
      _ = template.owner := owner.symm
      _ = read.template.owner := congrArg SourceCoreLambdaTemplates.Lambda.owner templateEq.symm
      _ = read.entry.view.owner := origins.1
  obtain ⟨node, member, form, _raw, _type, _requirements, _coercions⟩ := material.sourceCaptures.occurrence
  have found : material.descriptor.source.lookupExpression? material.descriptor.initializer = some node :=
    lookupExpression?_complete material.descriptorUnique member
  obtain ⟨original, originalFound, originalForm⟩ := pair_lambda material.origin.paired found
  rw [initializer] at originalFound
  have shape : original.form = .lambda material.descriptor.parameters material.descriptor.resultType
      material.descriptor.body := originalForm.trans form
  have instantiated : function = material.descriptor.instantiate read.substitution
      (material.produced ++ material.callerEvidence.applySubstitution material.semantic) :=
    material.materialized.trans (CallableAppliedRuntimeMaterialization.instantiated_closure_eq read
      material.descriptor material.instantiation scheme actualType)
  have nativeHeader : ExpressionForm.lambda
      (material.descriptor.parameters.map (TypedBinder.applySubstitution read.substitution))
      (read.substitution.apply material.descriptor.resultType) material.descriptor.body = read.template.node.form := by
    rw [instantiated] at header
    simpa only [Dynamic.GeneralizedClosure.instantiate, templateEq] using header.symm
  refine ⟨initializer, ?_⟩
  unfold applyRead
  split
  · split
    · next rejected => rw [originalFound] at rejected; cases rejected
    · next actual actualFound =>
      have same : actual = original := Option.some.inj (actualFound.symm.trans originalFound)
      subst actual
      split
      · next parameters resultType body actualShape =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.lambda.inj (actualShape.symm.trans shape)
        split
        · exact ⟨_, rfl⟩
        · contradiction
      all_goals rename_i rejected; exact False.elim (rejected _ _ _ shape)
  · contradiction

/-- Once the actual read factory succeeds, its saved lexical descriptor
produces the genuine paired-table edge. No application factory, edge coverage,
initializer equality or native-header condition is supplied by the caller. -/
theorem prepared_edge (material : Materialization compiled mapping world function viewRelation)
    {caller : SourceCoreCallableAncestryReadRecipes.State}
    {callerNative : CallableIndexedHistory.NativeFrame}
    {callerGhost : CallableIndexedHistory.GhostFrame} {id : Word}
    (carried : CallableIndexedHistory.Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table callerNative callerGhost (some caller))
    (read : Read compiled.indexed.ancestry.graph.inputs caller id material.code.descriptor.id)
    (accepted : prepareRead compiled.indexed.ancestry.graph.inputs caller id
      material.code.descriptor.id = .ok read)
    (scheme : material.descriptor.binder.scheme = read.binder.scheme)
    (actualType : material.actualType = read.node.rawType) :
    ∃ recipe : CallableAppliedViewProvenance.Recipe compiled.indexed.ancestry.graph.inputs
        callerGhost material.origin.ghost caller material.origin.metadata id material.code.descriptor.id,
      material.descriptor.initializer = recipe.read.entry.view.principal.initializer ∧
      recipe.read = read ∧
      ∃ callerIndex lexicalIndex destination,
        callerNative = .state (Int.ofNat callerIndex) ∧
        material.origin.native = .state (Int.ofNat lexicalIndex) ∧
        compiled.indexed.ancestry.graph.table.viewAt? callerIndex lexicalIndex id
          material.code.descriptor.id = some destination ∧
        compiled.indexed.ancestry.graph.table.stateAt? destination = some (read.after material.origin.metadata) := by
  obtain ⟨initializer, applied, application⟩ := apply_read material read scheme actualType
  let recipe : CallableAppliedViewProvenance.Recipe compiled.indexed.ancestry.graph.inputs
      callerGhost material.origin.ghost caller material.origin.metadata id material.code.descriptor.id :=
    ⟨carried.authenticates, material.origin.carried.authenticates, read, accepted, applied, application⟩
  obtain ⟨callerIndex, callerShape, callerStored⟩ := carried.state_shape
  obtain ⟨lexicalIndex, lexicalShape, lexicalStored⟩ := material.origin.carried.state_shape
  obtain ⟨destination, edge, stored⟩ :=
    (CallableAncestryPairedValidation.valid_closed compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.validated).view callerStored lexicalStored recipe.view_accepted
  exact ⟨recipe, initializer, rfl, callerIndex, lexicalIndex, destination,
    callerShape, lexicalShape, edge, stored⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedReadApplication
end
