import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning

/-! Pointwise finite-trace contracts. Source preservation uses an independent
source size; reflection consumes the original Core size and constructs a source
trace with its own size. Below only restricts an existing pointwise family.
Administrative authority and runtime environment typing stay separate inputs.
These contracts do not add meaning fields to a static catalog or profile. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open GenericExpressionMeaning (Certificate FaultRep ResultRepresents)
open ProtectedExpressionMeaning (Entry)

/-- A strict outer bound selects only the smaller pointwise obligations. -/
def Below (budget : Nat) (contract : Nat → Prop) : Prop :=
  ∀ size, size < budget → contract size

theorem Below.restrict {contract : Nat → Prop} {small large : Nat}
    (meaning : Below large contract) (bounded : small ≤ large) : Below small contract := by
  intro size smaller
  exact meaning size (Nat.lt_of_lt_of_le smaller bounded)

theorem Below.child {contract : Nat → Prop} {budget child : Nat}
    (meaning : Below budget contract) (smaller : child < budget) : contract child :=
  meaning child smaller

def PreservesAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) (entry : Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after
def ReflectsAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) (entry : Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-! Body contracts have the same independent source statement typing boundary
as the existing body interface, with an additional actual typed environment and
protected entry. A source body trace is never an input to reflection. -/
def BodyPreservesAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (function : Dynamic.Closure) (certificate : FunctionCode.BodyCertificate)
    (faults : FaultRep) (entry : Entry) : Prop :=
  ∀ {scope type body}, certificate function.source scope function.body type body →
  ∀ {context staticFinal facts}, StatementsHaveType function.source
    {returnType := function.resultType, loopDepth := 0} context function.body staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (body.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld function.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after
def BodyReflectsAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (function : Dynamic.Closure) (certificate : FunctionCode.BodyCertificate)
    (faults : FaultRep) (entry : Entry) : Prop :=
  ∀ {scope type body}, certificate function.source scope function.body type body →
  ∀ {context staticFinal facts}, StatementsHaveType function.source
    {returnType := function.resultType, loopDepth := 0} context function.body staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    EvaluationSize size actual store (body.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld function.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : Certificate} {faults : FaultRep} {entry : Entry}
  {function : Dynamic.Closure} {bodyCertificate : FunctionCode.BodyCertificate}

/-- Restriction of a proved unrestricted expression theorem. -/
theorem preserves_at_of_unbounded
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    (size : Nat) : PreservesAt size model program context evidence source certificate faults entry := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed installed trace
  exact meaning certified found environments heaps locals agrees typed installed trace.sound

theorem reflects_at_of_unbounded
    (meaning : ProtectedExpressionMeaning.Reflects model program context evidence source certificate faults entry)
    (size : Nat) : ReflectsAt size model program context evidence source certificate faults entry := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed installed evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed installed evaluated.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves_below_of_unbounded
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    (budget : Nat) : Below budget (fun size => PreservesAt size model program context evidence source certificate faults entry) := by
  intro size _
  exact preserves_at_of_unbounded meaning size

theorem reflects_below_of_unbounded
    (meaning : ProtectedExpressionMeaning.Reflects model program context evidence source certificate faults entry)
    (budget : Nat) : Below budget (fun size => ReflectsAt size model program context evidence source certificate faults entry) := by
  intro size _
  exact reflects_at_of_unbounded meaning size

/-- Existing unrestricted body meaning can be restricted without changing the
source/static code or any canonical/actual environment relationship. -/
theorem body_preserves_at_of_unbounded
    (meaning : FunctionCalls.BodyPreserves model program function bodyCertificate faults)
    (entry : Entry) (size : Nat) : BodyPreservesAt size model program function bodyCertificate faults entry := by
  intro scope type body certified context staticFinal facts typed mapping world administrative environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees _ _ trace
  exact meaning certified typed environments heaps locals agrees trace.sound

theorem body_reflects_at_of_unbounded
    (meaning : FunctionCalls.BodyReflects model program function bodyCertificate faults)
    (entry : Entry) (size : Nat) : BodyReflectsAt size model program function bodyCertificate faults entry := by
  intro scope type body certified context staticFinal facts typed mapping world administrative environment canonical actual
    actualContext before store ξ value finalStore environments heaps locals agrees _ _ evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified typed environments heaps locals agrees evaluated.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.BodyTrace.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem body_preserves_below_of_unbounded
    (meaning : FunctionCalls.BodyPreserves model program function bodyCertificate faults)
    (entry : Entry) (budget : Nat) :
    Below budget (fun size => BodyPreservesAt size model program function bodyCertificate faults entry) := by
  intro size _
  exact body_preserves_at_of_unbounded meaning entry size

theorem body_reflects_below_of_unbounded
    (meaning : FunctionCalls.BodyReflects model program function bodyCertificate faults)
    (entry : Entry) (budget : Nat) :
    Below budget (fun size => BodyReflectsAt size model program function bodyCertificate faults entry) := by
  intro size _
  exact body_reflects_at_of_unbounded meaning entry size

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts
