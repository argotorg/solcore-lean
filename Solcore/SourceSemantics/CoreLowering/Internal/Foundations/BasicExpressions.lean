import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FunctionCalls
import Solcore.Frontend.SourceCoreBasic
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.Heaps
import Solcore.Frontend.SourceCoreControl
import Solcore.Frontend.SourceCoreGeneralFunctions
import Solcore.SourceSemantics.Staging.CallBoundary
import Solcore.Frontend.SourceCoreCallableContracts

/-!
# Basic expressions and call contracts

Basic and control expressions and their certificates, typed generic expression meaning, expression fault contracts, and the certificates of call contracts and call entries.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning
/-! Expression induction for code that allocates administrative closures.
Every actual slot, including inserted temporary values, has runtime typing in
the actual definition environment. This is needed when a generated closure
captures the whole environment. Existing allocation-free meanings embed here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open GenericExpressionMeaning (Certificate FaultRep ResultRepresents)

def Preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def Reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {certificate : Certificate} {faults : FaultRep}

theorem preserves_of_unrestricted
    (meaning : GenericExpressionMeaning.Preserves model program context evidence source certificate faults) :
    Preserves model program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees _ trace
  exact meaning certified found environments heaps locals agrees trace

theorem reflects_of_unrestricted
    (meaning : GenericExpressionMeaning.Reflects model program context evidence source certificate faults) :
    Reflects model program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees _ trace
  exact meaning certified found environments heaps locals agrees trace

end Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts
/-! An interface for retaining an actual fault origin beside the
original result. Finite joins consume existing child posts and Source traces.
They do not produce evaluations or choose a primitive witness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly

abbrev ExpressionFaultPost := Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
  TypedSource → Dynamic.Environment → Dynamic.Heap → ExpressionId → Dynamic.SemanticFault →
  Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop

abbrev ExpressionsFaultPost := Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
  TypedSource → Dynamic.Environment → Dynamic.Heap → List ExpressionId → Dynamic.SemanticFault →
  Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop

/-- Only an actual fault outcome requires a provenance post. -/
def OutcomePost (post : ExpressionFaultPost) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : ExpressionId) (type : Core.Ty)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) : Prop :=
  match outcome with
  | .value _ => True
  | .fault reason => ∃ token, result = .inLeft type (.word token) ∧
      post program context evidence source environment before id reason after token mapping world store

/-- This shape is independent of DataExpressionSequence and avoids an import cycle. -/
def ListOutcomePost (post : ExpressionsFaultPost) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (ids : List ExpressionId) (type : Core.Ty)
    (outcome : Except Dynamic.SemanticFault (List Dynamic.Value)) (after : Dynamic.Heap) (result : Value)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) : Prop :=
  match outcome with
  | .ok _ => True
  | .error reason => ∃ token, result = .inLeft type (.word token) ∧
      post program context evidence source environment before ids reason after token mapping world store

/-- These are only the two original ordered Source fault joins. -/
structure SequenceJoins (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) : Prop where
  head : ∀ {environment before id ids reason after token mapping world store},
    Dynamic.ExpressionFaults program context evidence source environment before id reason after →
    expressionPost program context evidence source environment before id reason after token mapping world store →
    listPost program context evidence source environment before (id :: ids) reason after token mapping world store
  tail : ∀ {environment before middle id ids value reason after token mapping world store},
    Dynamic.ExpressionEvaluates program context evidence source environment before id value middle →
    Dynamic.ExpressionsFault program context evidence source environment middle ids reason after →
    listPost program context evidence source environment middle ids reason after token mapping world store →
    listPost program context evidence source environment before (id :: ids) reason after token mapping world store

/-- A genuine parent-to-selected-child Source join. The parent contains its
actual form and layout, and selected right/branch joins keep the actual prefix. -/
inductive ExpressionLink (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment) :
    Dynamic.Heap → ExpressionId → Dynamic.Heap → ExpressionId → Prop where
  | group {before : Dynamic.Heap} {id inner : ExpressionId} {node : ExpressionNode}
      (contains : ContainsExpression source id node) (form : node.form = .group inner)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions []) :
      ExpressionLink program context evidence source environment before id before inner
  | unary {before : Dynamic.Heap} {id operand : ExpressionId} {node : ExpressionNode}
      {operator : Syntax.UnaryOp} {owned : List RequirementId}
      (contains : ContainsExpression source id node) (form : node.form = .unary operator operand)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned) :
      ExpressionLink program context evidence source environment before id before operand
  | binaryLeft {before : Dynamic.Heap} {id left right : ExpressionId} {node : ExpressionNode}
      {operator : Syntax.BinaryOp} {owned : List RequirementId}
      (contains : ContainsExpression source id node) (form : node.form = .binary left operator right)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned) :
      ExpressionLink program context evidence source environment before id before left
  | binaryRight {before middle : Dynamic.Heap} {id left right : ExpressionId} {node : ExpressionNode}
      {operator : Syntax.BinaryOp} {owned : List RequirementId} {value : Dynamic.Value}
      (contains : ContainsExpression source id node) (form : node.form = .binary left operator right)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned)
      (firstSource : Dynamic.ExpressionEvaluates program context evidence source environment before left value middle)
      (selected : Dynamic.EvaluatesRightOperand operator value) :
      ExpressionLink program context evidence source environment before id middle right
  | conditionalCondition {before : Dynamic.Heap} {id condition yes no : ExpressionId} {node : ExpressionNode}
      (contains : ContainsExpression source id node) (form : node.form = .conditional condition yes no)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions []) :
      ExpressionLink program context evidence source environment before id before condition
  | conditionalTrue {before middle : Dynamic.Heap} {id condition yes no : ExpressionId} {node : ExpressionNode}
      (contains : ContainsExpression source id node) (form : node.form = .conditional condition yes no)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
      (firstSource : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool true) middle) :
      ExpressionLink program context evidence source environment before id middle yes
  | conditionalFalse {before middle : Dynamic.Heap} {id condition yes no : ExpressionId} {node : ExpressionNode}
      (contains : ContainsExpression source id node) (form : node.form = .conditional condition yes no)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
      (firstSource : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool false) middle) :
      ExpressionLink program context evidence source environment before id middle no

inductive ExpressionsLink (source : TypedSource) : ExpressionId → List ExpressionId → Prop where
  | tuple {id : ExpressionId} {ids : List ExpressionId} {node : ExpressionNode}
      (contains : ContainsExpression source id node) (form : node.form = .tuple ids)
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions []) :
      ExpressionsLink source id ids

/-- Only finite post transport along those exact joins is requested. -/
structure CompositionJoins (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) : Prop where
  expression : ∀ {environment before id middle child reason after token mapping world store},
    ExpressionLink program context evidence source environment before id middle child →
    Dynamic.ExpressionFaults program context evidence source environment middle child reason after →
    expressionPost program context evidence source environment middle child reason after token mapping world store →
    expressionPost program context evidence source environment before id reason after token mapping world store
  expressions : ∀ {environment before id ids reason after token mapping world store},
    ExpressionsLink source id ids →
    Dynamic.ExpressionsFault program context evidence source environment before ids reason after →
    listPost program context evidence source environment before ids reason after token mapping world store →
    expressionPost program context evidence source environment before id reason after token mapping world store

/-- The original untyped child contract with a fault-only post appended. -/
def Preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate)
    (faults : FunctionCalls.FaultRep) (post : ExpressionFaultPost) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      OutcomePost post program context evidence source environment before id lowered.type outcome after value finalMap finalWorld finalStore

/-- The original untyped completed-child contract, with the same appended post. -/
def Reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate)
    (faults : FunctionCalls.FaultRep) (post : ExpressionFaultPost) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      OutcomePost post program context evidence source environment before id lowered.type outcome after value finalMap finalWorld finalStore

/-- Inserted slots retain their original native runtime typing premise. -/
def TypedPreserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate)
    (faults : FunctionCalls.FaultRep) (post : ExpressionFaultPost) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      OutcomePost post program context evidence source environment before id lowered.type outcome after value finalMap finalWorld finalStore

/-- The typed completed-child contract retains the actual inserted-slot context. -/
def TypedReflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate)
    (faults : FunctionCalls.FaultRep) (post : ExpressionFaultPost) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      OutcomePost post program context evidence source environment before id lowered.type outcome after value finalMap finalWorld finalStore

abbrev TrivialExpressionPost : ExpressionFaultPost := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => True
abbrev TrivialExpressionsPost : ExpressionsFaultPost := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => True

theorem trivial_sequence_joins (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    SequenceJoins TrivialExpressionPost TrivialExpressionsPost program context evidence source where
  head := by intros; trivial
  tail := by intros; trivial

theorem trivial_composition_joins (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    CompositionJoins TrivialExpressionPost TrivialExpressionsPost program context evidence source where
  expression := by intros; trivial
  expressions := by intros; trivial

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {faults : FunctionCalls.FaultRep} {post : ExpressionFaultPost}

theorem OutcomePost.of_trivial {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {sourceType : TypeSystem.Ty} {type : Core.Ty} {outcome : Dynamic.ExpressionOutcome}
    {value : Value} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (represented : FunctionCalls.ResultRepresents model mapping world sourceType type faults outcome value) :
    OutcomePost TrivialExpressionPost program context evidence source environment before id type
      outcome after value mapping world store := by
  cases represented with
  | value _ => trivial
  | fault _ => exact ⟨_, rfl, trivial⟩

theorem OutcomePost.fault {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {type : Core.Ty} {reason : Dynamic.SemanticFault} {token : Word}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (retained : OutcomePost post program context evidence source environment before id type
      (.fault reason) after (.inLeft type (.word token)) mapping world store) :
    post program context evidence source environment before id reason after token mapping world store := by
  obtain ⟨actual, same, retained⟩ := retained
  have tokens : token = actual := by simpa only [Value.inLeft.injEq, Value.word.injEq, true_and] using same
  exact tokens.symm ▸ retained

/-- Finite transport of the actual selected child outcome through its owning Source form. -/
theorem OutcomePost.expression {listPost : ExpressionsFaultPost}
    (joins : CompositionJoins post listPost program context evidence source)
    {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id child : ExpressionId} {type : Core.Ty} {outcome : Dynamic.ExpressionOutcome}
    {value : Value} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (link : ExpressionLink program context evidence source environment before id middle child)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment middle child outcome after)
    (retained : OutcomePost post program context evidence source environment middle child type
      outcome after value mapping world store) :
    OutcomePost post program context evidence source environment before id type
      outcome after value mapping world store := by
  cases trace with
  | value _ => trivial
  | fault failed =>
    obtain ⟨token, same, retained⟩ := retained
    exact ⟨token, same, joins.expression link failed retained⟩

theorem ListOutcomePost.fault {listPost : ExpressionsFaultPost}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {ids : List ExpressionId}
    {type : Core.Ty} {reason : Dynamic.SemanticFault} {token : Word}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (retained : ListOutcomePost listPost program context evidence source environment before ids type
      (.error reason) after (.inLeft type (.word token)) mapping world store) :
    listPost program context evidence source environment before ids reason after token mapping world store := by
  obtain ⟨actual, same, retained⟩ := retained
  have tokens : token = actual := by simpa only [Value.inLeft.injEq, Value.word.injEq, true_and] using same
  exact tokens.symm ▸ retained

theorem Preserves.forget (meaning : Preserves model program context evidence source certificate faults post) :
    GenericExpressionMeaning.Preserves model program context evidence source certificate faults := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ outcome after environments heaps locals layout trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := meaning generated found environments heaps locals layout trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem Reflects.forget (meaning : Reflects model program context evidence source certificate faults post) :
    GenericExpressionMeaning.Reflects model program context evidence source certificate faults := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ value finalStore environments heaps locals layout evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := meaning generated found environments heaps locals layout evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem TypedPreserves.forget (meaning : TypedPreserves model program context evidence source certificate faults post) :
    TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals layout actualTyped trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := meaning generated found environments heaps locals layout actualTyped trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem TypedReflects.forget (meaning : TypedReflects model program context evidence source certificate faults post) :
    TypedGenericExpressionMeaning.Reflects model program context evidence source certificate faults := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals layout actualTyped evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := meaning generated found environments heaps locals layout actualTyped evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem Preserves.of_trivial
    (meaning : GenericExpressionMeaning.Preserves model program context evidence source certificate faults) :
    Preserves model program context evidence source certificate faults TrivialExpressionPost := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ outcome after environments heaps locals layout trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, OutcomePost.of_trivial represented⟩

theorem Reflects.of_trivial
    (meaning : GenericExpressionMeaning.Reflects model program context evidence source certificate faults) :
    Reflects model program context evidence source certificate faults TrivialExpressionPost := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ value finalStore environments heaps locals layout evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, OutcomePost.of_trivial represented⟩

theorem TypedPreserves.of_trivial
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults) :
    TypedPreserves model program context evidence source certificate faults TrivialExpressionPost := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals layout actualTyped trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout actualTyped trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, OutcomePost.of_trivial represented⟩

theorem TypedReflects.of_trivial
    (meaning : TypedGenericExpressionMeaning.Reflects model program context evidence source certificate faults) :
    TypedReflects model program context evidence source certificate faults TrivialExpressionPost := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals layout actualTyped evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout actualTyped evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, OutcomePost.of_trivial represented⟩

end Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BasicExpressions
/-!
Meaning preservation for the ordinary scalar/product expression compiler.

The certificate records source occurrences and metadata, not a successful
compiler call. It includes local reads, grouping and binary tuples with
left-to-right failure propagation. Corresponding heaps contain ordinary
optional cells only. The reason word is the compiler's supplied failure token;
a complete source fault-site table is outside this fragment.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.BasicExpressions

open Frontend Frontend.SourceInference TypeSystem
open LocalCell

structure Metadata (source : TypedSource) (id : ExpressionId)
    (node : ExpressionNode) (type : Core.Ty) : Prop where
  contains : ContainsExpression source id node
  owned : id.occurrence.owner = source.owner
  types : TypeRepresents node.type type
  requirements : node.requirements = []
  coercions : node.coercions = []

theorem Metadata.read {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {type : Core.Ty}
    (metadata : Metadata source id node type) (unique : NodeOccurrencesUnique source) :
    SourceCoreBasic.readExpression source id = .ok (node, type) := by
  simp [SourceCoreBasic.readExpression, metadata.owned,
    lookupExpression?_complete unique metadata.contains,
    metadata.requirements, metadata.coercions, SourceCoreBasic.projectType,
    metadata.types.lower _, Except.mapError, bind, Except.bind, pure, Pure.pure, Except.pure]

inductive Tree (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (reason : Core.Word) :
    ExpressionId → Core.Ty → Core.Expr → Nat → Prop where
  | unit {id : ExpressionId} {node : ExpressionNode}
      (metadata : Metadata source id node .unit) (form : node.form = .tuple []) :
      Tree source scope reason id .unit (Core.LanguageResult.success .unit) 1
  | bool {id : ExpressionId} {node : ExpressionNode} {name : String} (value : Bool)
      (metadata : Metadata source id node .bool)
      (form : node.form = .reference name (.builtinBoolean value)) :
      Tree source scope reason id .bool (Core.LanguageResult.success (.bool value)) 1
  | word {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue}
      (value : Core.Word) (metadata : Metadata source id node .word)
      (form : node.form = .literal literal)
      (meaning : WordLiteralDenotes ⟨node.span, literal⟩ value) :
      Tree source scope reason id .word (Core.LanguageResult.success (.word value)) 1
  | localRead {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
      {binder : Resolved.LocalId} {name : String} {index : Nat}
      (metadata : Metadata source id node type)
      (form : node.form = .reference name (.local binder))
      (owned : binder.owner = source.owner)
      (slot : SourceCoreLocalCell.lookup? scope binder = some (index, type)) :
      Tree source scope reason id type (Core.OptionalCell.read type (.var index) reason) 1
  | group {id inner : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
      {expression : Core.Expr} {depth : Nat}
      (metadata : Metadata source id node type) (form : node.form = .group inner)
      (child : Tree source scope reason inner type expression depth) :
      Tree source scope reason id type expression (depth + 1)
  | pair {id left right : ExpressionId} {node : ExpressionNode}
      {leftType rightType : Core.Ty} {leftCode rightCode : Core.Expr} {leftDepth rightDepth : Nat}
      (metadata : Metadata source id node (.product leftType rightType))
      (form : node.form = .tuple [left, right])
      (leftTree : Tree source scope reason left leftType leftCode leftDepth)
      (rightTree : Tree source scope reason right rightType rightCode rightDepth) :
      Tree source scope reason id (.product leftType rightType)
        (Core.LocalSequence.pair leftType rightType leftCode rightCode)
        (max leftDepth rightDepth + 1)

theorem Tree.wellFormed {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reason : Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reason id type expression depth) : Core.Ty.WellFormed [] type := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ => exact metadata.types.wellFormed []

theorem Tree.cellPayload {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reason : Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reason id type expression depth) : Core.CellPayload type := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ => exact metadata.types.cellPayload

theorem Tree.hasType {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reason : Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reason id type expression depth) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) expression
      (Core.LanguageResult.resultType type) := by
  induction tree with
  | unit => exact Core.LanguageResult.success_hasType .unit
  | bool => exact Core.LanguageResult.success_hasType .bool
  | word => exact Core.LanguageResult.success_hasType .word
  | localRead metadata _ _ slot =>
      exact Core.OptionalCell.read_hasType _ (metadata.types.wellFormed [])
        (.var (SourceCoreLocalCell.lookup?_context slot))
  | group _ _ _ child => exact child
  | pair _ _ leftTree rightTree left right =>
      exact Core.LocalSequence.pair_hasType leftTree.wellFormed rightTree.wellFormed left right

inductive OutcomeRepresents (type : Core.Ty) (reason : Core.Word) :
    Dynamic.ExpressionOutcome → Core.Value → Prop where
  | value (value : SourceStagedValue.Value)
      (typed : SourceStagedValue.coreType value = type) :
      OutcomeRepresents type reason (.value (StagedValue.toSource value))
        (.inRight .word (SourceStagedValue.toCore value))
  | uninitialized (location : Dynamic.Location) :
      OutcomeRepresents type reason (.fault (.uninitializedLocation location))
        (.inLeft type (.word reason))

/-- Every sufficient traversal budget produces the certificate's expression.
The certificate contains no compiler-success or source-evaluation premise. -/
theorem Tree.lower {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reason : Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reason id type expression depth)
    (unique : NodeOccurrencesUnique source) (fuel : Nat) (enough : depth ≤ fuel) :
    SourceCoreBasic.lowerExpression fuel source scope id reason = .ok ⟨type, expression⟩ := by
  induction tree generalizing fuel with
  | unit metadata form =>
      cases fuel with
      | zero => omega
      | succ fuel => exact SourceCoreBasic.lowerExpression_unit (metadata.read unique) form
  | bool value metadata form =>
      cases fuel with
      | zero => omega
      | succ fuel => exact SourceCoreBasic.lowerExpression_bool (metadata.read unique) form
  | word value metadata form meaning =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerExpression_word (metadata.read unique) form
            (interpretWordLiteral?_complete meaning)
  | localRead metadata form owned slot =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerExpression_local (metadata.read unique) form
            (SourceCoreLocalCell.lowerRead_eq
              (lookupExpression?_complete unique metadata.contains) form owned
              metadata.requirements metadata.coercions slot (metadata.types.lower _) reason)
  | group metadata form child inductionHypothesis =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerExpression_group (metadata.read unique) form
            (inductionHypothesis fuel (by omega))
  | pair metadata form leftTree rightTree leftInduction rightInduction =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerExpression_pair (metadata.read unique) form
            (leftInduction fuel (by omega)) (rightInduction fuel (by omega))

private theorem word_constructs {span : Syntax.SourceSpan}
    {literal : Syntax.CoreLiteralValue} {value : Core.Word}
    (meaning : WordLiteralDenotes ⟨span, literal⟩ value) :
    Dynamic.LiteralConstructs literal (.word value) := by
  have modulo : Core.Word.ofNatModulo value.val = value := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.isLt
  rw [← modulo]
  exact .word meaning

/-- The certificate supplies both independent source and Core derivations.
Neither heap changes, including when a child read fails. -/
theorem Tree.preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reason : Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reason id type expression depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents type reason sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store expression coreValue store := by
  induction tree with
  | unit metadata form =>
      refine ⟨.value .unit, .inRight .word .unit, .value ?_, .value .unit rfl, .inRight .unit⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]
        exact .tuple rfl .nil .nil
      · rw [metadata.coercions]; exact .nil
  | bool value metadata form =>
      refine ⟨.value (.bool value), .inRight .word (.bool value), .value ?_,
        .value (.bool value) rfl, .inRight .bool⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]; exact .builtinBoolean rfl
      · rw [metadata.coercions]; exact .nil
  | word value metadata form meaning =>
      refine ⟨.value (.word value), .inRight .word (.word value), .value ?_,
        .value (.word value) rfl, .inRight .word⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]
        exact .literal rfl (word_constructs meaning)
      · rw [metadata.coercions]; exact .nil
  | @localRead id node type binder name index metadata form owned slot =>
      obtain ⟨location, cell, stored, lookup, coreLookup, _, read, coreRead, related⟩ :=
        environments.lookup_heap heaps slot
      have cellType := related.types.source_unique metadata.types
      let site : ReadSite source scope id type := {
        node, binder, name, index, contains := metadata.contains, form, owner := owned
        requirements := metadata.requirements, coercions := metadata.coercions
        slot, types := metadata.types
      }
      cases related with
      | uninitialized types =>
          obtain ⟨fault, evaluated⟩ := site.uninitialized program context evidence environment heap
            coreEnvironment store location _ lookup read cellType rfl rfl coreLookup coreRead reason
          exact ⟨_, _, .fault fault, .uninitialized location, evaluated⟩
      | initialized value =>
          obtain ⟨evaluated, coreEvaluated⟩ := site.initialized program context evidence environment heap
            coreEnvironment store location _ value lookup read rfl rfl coreLookup coreRead reason
          exact ⟨_, _, .value evaluated, .value value rfl, coreEvaluated⟩
  | group metadata form child inductionHypothesis =>
      obtain ⟨outcome, coreValue, evaluated, related, coreEvaluated⟩ := inductionHypothesis
      refine ⟨outcome, coreValue, ?_, related, coreEvaluated⟩
      cases evaluated with
      | value evaluated =>
          apply Dynamic.ExpressionEvaluatesOutcome.value
          apply Dynamic.ExpressionEvaluates.intro metadata.contains
          · rw [form, metadata.requirements, metadata.coercions]; exact .group rfl evaluated
          · rw [metadata.coercions]; exact .nil
      | fault fault =>
          apply Dynamic.ExpressionEvaluatesOutcome.fault
          apply Dynamic.ExpressionFaults.form metadata.contains
          rw [form, metadata.requirements, metadata.coercions]
          exact .group rfl fault
  | @pair id left right node leftType rightType leftCode rightCode leftDepth rightDepth
      metadata form leftTree rightTree leftInduction rightInduction =>
      obtain ⟨leftOutcome, leftValue, leftSource, leftRelated, leftCore⟩ := leftInduction
      cases leftRelated with
      | uninitialized location =>
          cases leftSource with
          | fault fault =>
              refine ⟨_, _, .fault ?_, .uninitialized location,
                Core.LocalSequence.pair_left_failure leftType rightType leftCore⟩
              apply Dynamic.ExpressionFaults.form metadata.contains
              rw [form, metadata.requirements, metadata.coercions]
              exact .tuple rfl (.head fault)
      | value leftValue leftTypeEq =>
          cases leftSource with
          | value leftSource =>
              obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightInduction
              have weakened := rightCore.weakenAt_zero_cellPayload rightTree.hasType
                (.sum .word rightTree.cellPayload) (environments.runtime_hasTypes [])
                (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes
                (SourceStagedValue.toCore leftValue)
              cases rightRelated with
              | uninitialized location =>
                  cases rightSource with
                  | fault fault =>
                      refine ⟨_, _, .fault ?_, .uninitialized location,
                        Core.LocalSequence.pair_right_failure leftType rightType leftCore weakened⟩
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .tuple rfl (.tail leftSource (.head fault))
              | value rightValue rightTypeEq =>
                  cases rightSource with
                  | value rightSource =>
                      refine ⟨.value (StagedValue.toSource (.product leftValue rightValue)),
                        .inRight .word (SourceStagedValue.toCore (.product leftValue rightValue)),
                        .value ?_, .value (.product leftValue rightValue) ?_,
                        Core.LocalSequence.pair_success leftType rightType leftCore weakened⟩
                      · apply Dynamic.ExpressionEvaluates.intro metadata.contains
                        · rw [form, metadata.requirements, metadata.coercions]
                          exact .tuple rfl (.cons leftSource (.cons rightSource .nil))
                            (.cons (.singleton _))
                        · rw [metadata.coercions]; exact .nil
                      · simp [SourceStagedValue.coreType, leftTypeEq, rightTypeEq]

/-- Actual compilation, Core checking and finite execution agree with an
independent source outcome. Completed runs reflect that same result/store;
smaller runtime fuel may retain a checkpoint. -/
theorem Tree.lower_run_preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reason : Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reason id type expression depth)
    (unique : NodeOccurrencesUnique source) (compilationFuel : Nat) (enough : depth ≤ compilationFuel)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    SourceCoreBasic.lowerExpression compilationFuel source scope id reason = .ok ⟨type, expression⟩ ∧
    Core.infer? (SourceCoreLocalCell.coreContext scope) expression =
      some (Core.LanguageResult.resultType type) ∧
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents type reason sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel
        (.initial expression coreEnvironment store) = .done coreValue store) ∧
      (∀ fuel result finalStore, Core.runStateful fuel
        (.initial expression coreEnvironment store) = .done result finalStore →
          result = coreValue ∧ finalStore = store) := by
  obtain ⟨sourceOutcome, coreValue, sourceEvaluation, outcome, coreEvaluation⟩ :=
    tree.preserves program context evidence environments heaps
  obtain ⟨required, completes⟩ :=
    Core.evaluation_runStateful_complete_with_sufficient_fuel coreEvaluation
  refine ⟨tree.lower unique compilationFuel enough, Core.infer_complete tree.hasType,
    sourceOutcome, coreValue, required, sourceEvaluation, outcome, completes, ?_⟩
  intro fuel result finalStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreEvaluation

end Solcore.SourceSemantics.CoreLowering.BasicExpressions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BasicExpressionCertificates
/-! Recover the structural expression certificate from the actual basic
lowerer's success. Extraction inspects compiler checks and finite traversal
only; it has no source-evaluation or Core-evaluation premise. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.BasicExpressions

open Frontend Frontend.SourceInference TypeSystem LocalCell

theorem typeRepresents_of_lowerType
    {site : SourceCoreElaboration.ErrorSite} {sourceType : Ty} {type : Core.Ty}
    (lowered : SourceCoreElaboration.lowerType site sourceType = .ok type) :
    TypeRepresents sourceType type := by
  induction sourceType generalizing type with
  | «variable» | parameter | function | mapping | proxy | comptime | error => cases lowered
  | constructor constructor =>
      cases constructor with
      | declaration => cases lowered
      | builtin builtin =>
          cases builtin with
          | unit => cases lowered; exact .unit
          | bool => cases lowered; exact .bool
          | word => cases lowered; exact .word
          | integer => cases lowered
  | application function argument =>
      simp only [SourceCoreElaboration.lowerType] at lowered
      split at lowered <;> cases lowered
  | product left right leftIH rightIH =>
      simp only [SourceCoreElaboration.lowerType] at lowered
      cases leftResult : SourceCoreElaboration.lowerType site left with
      | error error => simp [leftResult, bind, Except.bind] at lowered
      | ok leftType =>
          cases rightResult : SourceCoreElaboration.lowerType site right with
          | error error => simp [leftResult, rightResult, bind, Except.bind] at lowered
          | ok rightType =>
              simp only [leftResult, rightResult, bind, Except.bind, pure, Pure.pure,
                Except.pure, Except.ok.injEq] at lowered
              subst type
              exact .product (leftIH leftResult) (rightIH rightResult)

private theorem projectType_ok
    {site : SourceCoreElaboration.ErrorSite} {sourceType : Ty} {type : Core.Ty}
    (projected : SourceCoreBasic.projectType site sourceType = .ok type) :
    SourceCoreElaboration.lowerType site sourceType = .ok type := by
  unfold SourceCoreBasic.projectType at projected
  cases result : SourceCoreElaboration.lowerType site sourceType with
  | error error => simp [result, Except.mapError] at projected
  | ok lowered =>
      simp only [result, Except.mapError, Except.ok.injEq] at projected
      subst lowered
      rfl

/-- Successful metadata checks establish declarative occurrence membership,
ownership, an exact scalar/product type, and absence of runtime obligations. -/
theorem readExpression_certificate
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    (read : SourceCoreBasic.readExpression source id = .ok (node, type)) :
    source.lookupExpression? id = some node ∧ Metadata source id node type := by
  by_cases owned : id.occurrence.owner = source.owner
  · cases found : source.lookupExpression? id with
    | none => simp [SourceCoreBasic.readExpression, owned, found, bind, Except.bind] at read
    | some selected =>
        by_cases requirements : selected.requirements = []
        · by_cases coercions : selected.coercions = []
          · cases projected : SourceCoreBasic.projectType (.occurrence id.occurrence) selected.type with
            | error error =>
                simp [SourceCoreBasic.readExpression, owned, found, requirements, coercions,
                  projected, bind, Except.bind, pure, Pure.pure, Except.pure] at read
            | ok projectedType =>
                simp [SourceCoreBasic.readExpression, owned, found, requirements, coercions,
                  projected, bind, Except.bind, pure, Pure.pure, Except.pure] at read
                rcases read with ⟨rfl, rfl⟩
                exact ⟨rfl, lookupExpression?_sound found, owned,
                  typeRepresents_of_lowerType (projectType_ok projected), requirements, coercions⟩
          · simp [SourceCoreBasic.readExpression, owned, found, requirements, coercions,
              bind, Except.bind, pure, Pure.pure, Except.pure] at read
        · simp [SourceCoreBasic.readExpression, owned, found, requirements,
            bind, Except.bind, pure, Pure.pure, Except.pure] at read
  · simp [SourceCoreBasic.readExpression, owned, bind, Except.bind] at read

theorem metadata_of_readExpression
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    (read : SourceCoreBasic.readExpression source id = .ok (node, type)) :
    Metadata source id node type :=
  (readExpression_certificate read).2

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem localRead_of_lowerRead
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {type : Core.Ty} {name : String} {binder : Resolved.LocalId}
    {reason : Core.Word} {expression : Core.Expr}
    (metadata : Metadata source id node type)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (lowered : SourceCoreLocalCell.lowerRead source scope id reason = .ok expression) :
    ∃ index, binder.owner = source.owner ∧
      SourceCoreLocalCell.lookup? scope binder = some (index, type) ∧
      expression = Core.OptionalCell.read type (.var index) reason := by
  by_cases owned : binder.owner = source.owner
  · cases slot : SourceCoreLocalCell.lookup? scope binder with
    | none =>
        simp [SourceCoreLocalCell.lowerRead, found, form, owned,
          metadata.requirements, metadata.coercions, slot, bind, Except.bind,
          pure, Pure.pure, Except.pure] at lowered
    | some pair =>
        rcases pair with ⟨index, payloadType⟩
        by_cases same : type = payloadType
        · subst payloadType
          simp [SourceCoreLocalCell.lowerRead, found, form, owned,
            metadata.requirements, metadata.coercions, slot, metadata.types.lower _,
            Except.mapError, bind, Except.bind, pure, Pure.pure, Except.pure] at lowered
          exact ⟨index, owned, rfl, lowered.symm⟩
        · simp [SourceCoreLocalCell.lowerRead, found, form, owned,
            metadata.requirements, metadata.coercions, slot, metadata.types.lower _, same,
            Except.mapError, bind, Except.bind, pure, Pure.pure, Except.pure] at lowered
  · simp [SourceCoreLocalCell.lowerRead, found, form, owned,
      bind, Except.bind, pure, Pure.pure, Except.pure] at lowered

/-- Every successful expression compilation has a structural certificate whose
depth fits that exact traversal budget. Rejection branches cannot supply one. -/
theorem tree_of_lowerExpression
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreBasic.lowerExpression fuel source scope id reason = .ok lowered) :
    ∃ depth, depth ≤ fuel ∧ Tree source scope reason id lowered.type lowered.expression depth := by
  induction fuel generalizing id lowered with
  | zero => simp [SourceCoreBasic.lowerExpression] at accepted
  | succ fuel ih =>
      cases read : SourceCoreBasic.readExpression source id with
      | error error => simp [SourceCoreBasic.lowerExpression, read, bind, Except.bind] at accepted
      | ok pair =>
          rcases pair with ⟨node, type⟩
          obtain ⟨found, metadata⟩ := readExpression_certificate read
          simp only [SourceCoreBasic.lowerExpression, read, bind, Except.bind] at accepted
          cases form : node.form with
          | literal literal =>
              simp only [form] at accepted
              cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) .word type with
              | error error => simp [checked] at accepted
              | ok checkedUnit =>
                  cases checkedUnit
                  have same := ensureType_ok checked
                  subst type
                  cases decoded : interpretWordLiteral? ⟨node.span, literal⟩ with
                  | none => simp [checked, decoded] at accepted
                  | some value =>
                      simp only [checked, decoded, pure, Pure.pure,
                        Except.pure, Except.ok.injEq] at accepted
                      subst lowered
                      exact ⟨1, by omega, .word value metadata form (interpretWordLiteral?_sound decoded)⟩
          | reference name resolution =>
              cases resolution with
              | declaration | builtinFunction => simp [form] at accepted
              | builtinBoolean value =>
                  simp only [form] at accepted
                  cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool type with
                  | error error => simp [checked] at accepted
                  | ok checkedUnit =>
                      cases checkedUnit
                      have same := ensureType_ok checked
                      subst type
                      simp only [checked, pure, Pure.pure,
                        Except.pure, Except.ok.injEq] at accepted
                      subst lowered
                      exact ⟨1, by omega, .bool value metadata form⟩
              | «local» binder =>
                  simp only [form] at accepted
                  cases localRead : SourceCoreLocalCell.lowerRead source scope id reason with
                  | error error => simp [localRead, Except.mapError] at accepted
                  | ok expression =>
                      simp only [localRead, Except.mapError, pure, Pure.pure,
                        Except.pure, Except.ok.injEq] at accepted
                      subst lowered
                      obtain ⟨index, owned, slot, rfl⟩ :=
                        localRead_of_lowerRead metadata found form localRead
                      exact ⟨1, by omega, .localRead metadata form owned slot⟩
          | group inner =>
              simp only [form] at accepted
              cases child : SourceCoreBasic.lowerExpression fuel source scope inner reason with
              | error error => simp [child] at accepted
              | ok result =>
                  simp only [child] at accepted
                  cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) type result.type with
                  | error error => simp [checked] at accepted
                  | ok checkedUnit =>
                      cases checkedUnit
                      have same := ensureType_ok checked
                      simp only [checked, pure, Pure.pure,
                        Except.pure, Except.ok.injEq] at accepted
                      subst lowered
                      obtain ⟨depth, bound, tree⟩ := ih child
                      exact ⟨depth + 1, by omega, .group (same ▸ metadata) form tree⟩
          | tuple elements =>
              cases elements with
              | nil =>
                  simp only [form] at accepted
                  cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit type with
                  | error error => simp [checked] at accepted
                  | ok checkedUnit =>
                      cases checkedUnit
                      have same := ensureType_ok checked
                      subst type
                      simp only [checked, pure, Pure.pure,
                        Except.pure, Except.ok.injEq] at accepted
                      subst lowered
                      exact ⟨1, by omega, .unit metadata form⟩
              | cons left rest =>
                  cases rest with
                  | nil => simp [form] at accepted
                  | cons right rest =>
                      cases rest with
                      | cons => simp [form] at accepted
                      | nil =>
                          simp only [form] at accepted
                          cases leftResult : SourceCoreBasic.lowerExpression fuel source scope left reason with
                          | error error => simp [leftResult] at accepted
                          | ok leftLowered =>
                              cases rightResult : SourceCoreBasic.lowerExpression fuel source scope right reason with
                              | error error => simp [leftResult, rightResult] at accepted
                              | ok rightLowered =>
                                  simp only [leftResult, rightResult] at accepted
                                  cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) type
                                      (.product leftLowered.type rightLowered.type) with
                                  | error error => simp [checked] at accepted
                                  | ok checkedUnit =>
                                      cases checkedUnit
                                      have same := ensureType_ok checked
                                      subst type
                                      simp only [checked, pure, Pure.pure,
                                        Except.pure, Except.ok.injEq] at accepted
                                      subst lowered
                                      obtain ⟨leftDepth, leftBound, leftTree⟩ := ih leftResult
                                      obtain ⟨rightDepth, rightBound, rightTree⟩ := ih rightResult
                                      exact ⟨max leftDepth rightDepth + 1, by omega,
                                        .pair metadata form leftTree rightTree⟩
          | integerLiteral | unary | binary | conditional | lambda | call | constructor | member | proxy | index =>
              simp [form] at accepted

theorem lowerExpression_hasType
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreBasic.lowerExpression fuel source scope id reason = .ok lowered) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) lowered.expression
      (Core.LanguageResult.resultType lowered.type) := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression accepted
  exact tree.hasType

/-- Accepted compiler output can use meaning preservation directly. The
remaining premises are occurrence uniqueness and the initial environment/heap
representation, not a manually supplied tree or an evaluation result. -/
theorem lowerExpression_run_preserves
    {compilationFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreBasic.lowerExpression compilationFuel source scope id reason = .ok lowered)
    (unique : NodeOccurrencesUnique source)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    Core.infer? (SourceCoreLocalCell.coreContext scope) lowered.expression =
      some (Core.LanguageResult.resultType lowered.type) ∧
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents lowered.type reason sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel
        (.initial lowered.expression coreEnvironment store) = .done coreValue store) ∧
      (∀ fuel result finalStore, Core.runStateful fuel
        (.initial lowered.expression coreEnvironment store) = .done result finalStore →
          result = coreValue ∧ finalStore = store) := by
  obtain ⟨depth, bound, tree⟩ := tree_of_lowerExpression accepted
  exact (tree.lower_run_preserves unique compilationFuel bound program context evidence
    environments heaps).2

end Solcore.SourceSemantics.CoreLowering.BasicExpressions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ControlExpressions
/-! Conditional expressions preserve their actual evaluated read occurrence.
The provider supplies a reason word per occurrence, and fault provenance follows
left-to-right tuple evaluation and the selected conditional branch. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ControlExpressions

open Frontend Frontend.SourceInference TypeSystem LocalCell

abbrev Metadata := BasicExpressions.Metadata

inductive Tree (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Core.Word) :
    ExpressionId → Core.Ty → Core.Expr → Nat → Prop where
  | unit {id : ExpressionId} {node : ExpressionNode}
      (metadata : Metadata source id node .unit) (form : node.form = .tuple []) :
      Tree source scope reasonAt id .unit (Core.LanguageResult.success .unit) 1
  | bool {id : ExpressionId} {node : ExpressionNode} {name : String} (value : Bool)
      (metadata : Metadata source id node .bool)
      (form : node.form = .reference name (.builtinBoolean value)) :
      Tree source scope reasonAt id .bool (Core.LanguageResult.success (.bool value)) 1
  | word {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue}
      (value : Core.Word) (metadata : Metadata source id node .word)
      (form : node.form = .literal literal)
      (meaning : WordLiteralDenotes ⟨node.span, literal⟩ value) :
      Tree source scope reasonAt id .word (Core.LanguageResult.success (.word value)) 1
  | localRead {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
      {binder : Resolved.LocalId} {name : String} {index : Nat}
      (metadata : Metadata source id node type)
      (form : node.form = .reference name (.local binder))
      (owned : binder.owner = source.owner)
      (slot : SourceCoreLocalCell.lookup? scope binder = some (index, type)) :
      Tree source scope reasonAt id type (Core.OptionalCell.read type (.var index) (reasonAt id)) 1
  | group {id inner : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
      {expression : Core.Expr} {depth : Nat}
      (metadata : Metadata source id node type) (form : node.form = .group inner)
      (child : Tree source scope reasonAt inner type expression depth) :
      Tree source scope reasonAt id type expression (depth + 1)
  | pair {id left right : ExpressionId} {node : ExpressionNode}
      {leftType rightType : Core.Ty} {leftCode rightCode : Core.Expr} {leftDepth rightDepth : Nat}
      (metadata : Metadata source id node (.product leftType rightType))
      (form : node.form = .tuple [left, right])
      (leftTree : Tree source scope reasonAt left leftType leftCode leftDepth)
      (rightTree : Tree source scope reasonAt right rightType rightCode rightDepth) :
      Tree source scope reasonAt id (.product leftType rightType)
        (Core.LocalSequence.pair leftType rightType leftCode rightCode)
        (max leftDepth rightDepth + 1)

  | conditional {id condition thenId elseId : ExpressionId} {node : ExpressionNode}
      {type : Core.Ty} {conditionCode thenCode elseCode : Core.Expr}
      {conditionDepth thenDepth elseDepth : Nat}
      (metadata : Metadata source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionTree : Tree source scope reasonAt condition .bool conditionCode conditionDepth)
      (thenTree : Tree source scope reasonAt thenId type thenCode thenDepth)
      (elseTree : Tree source scope reasonAt elseId type elseCode elseDepth) :
      Tree source scope reasonAt id type (Core.LocalControl.choose type conditionCode thenCode elseCode)
        (max conditionDepth (max thenDepth elseDepth) + 1)

theorem Tree.wellFormed {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type expression depth) : Core.Ty.WellFormed [] type := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ | conditional metadata _ _ _ _ => exact metadata.types.wellFormed []

theorem Tree.cellPayload {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type expression depth) : Core.CellPayload type := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ | conditional metadata _ _ _ _ => exact metadata.types.cellPayload

theorem Tree.hasType {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type expression depth) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) expression
      (Core.LanguageResult.resultType type) := by
  induction tree with
  | unit => exact Core.LanguageResult.success_hasType .unit
  | bool => exact Core.LanguageResult.success_hasType .bool
  | word => exact Core.LanguageResult.success_hasType .word
  | localRead metadata _ _ slot =>
      exact Core.OptionalCell.read_hasType _ (metadata.types.wellFormed [])
        (.var (SourceCoreLocalCell.lookup?_context slot))
  | group _ _ _ child => exact child
  | pair _ _ leftTree rightTree left right =>
      exact Core.LocalSequence.pair_hasType leftTree.wellFormed rightTree.wellFormed left right

  | conditional metadata _ _ _ _ condition thenBranch elseBranch =>
      exact Core.LocalControl.choose_hasType (metadata.types.wellFormed []) condition thenBranch elseBranch

/-- Occurrence provenance follows the evaluated source path. In particular,
right tuple elements require a successful left prefix, and conditional branches
require the matching Boolean condition. -/
inductive UninitializedAt (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    ExpressionId → ExpressionId → Dynamic.Location → Prop where
  | localRead {id : ExpressionId} {scope : SourceCoreLocalCell.Scope} {type : Core.Ty}
      {location : Dynamic.Location} {cell : Dynamic.Cell}
      (site : ReadSite source scope id type)
      (lookup : Dynamic.Environment.LooksUp environment site.binder location)
      (read : Dynamic.Heap.Reads heap location cell)
      (cellType : cell.type = site.node.type) (ordinary : cell.generalized = none)
      (empty : cell.value = none) : UninitializedAt program context evidence source environment heap id id location
  | group {id inner site : ExpressionId} {location : Dynamic.Location} {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .group inner)
      (child : UninitializedAt program context evidence source environment heap inner site location) :
      UninitializedAt program context evidence source environment heap id site location
  | pairLeft {id left right site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .tuple [left, right])
      (child : UninitializedAt program context evidence source environment heap left site location) :
      UninitializedAt program context evidence source environment heap id site location
  | pairRight {id left right site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty} {leftValue : Dynamic.Value}
      (metadata : Metadata source id node type) (form : node.form = .tuple [left, right])
      (evaluatedPrefix : Dynamic.ExpressionEvaluates program context evidence source environment heap left leftValue heap)
      (child : UninitializedAt program context evidence source environment heap right site location) :
      UninitializedAt program context evidence source environment heap id site location
  | condition {id condition thenId elseId site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .conditional condition thenId elseId)
      (child : UninitializedAt program context evidence source environment heap condition site location) :
      UninitializedAt program context evidence source environment heap id site location
  | thenBranch {id condition thenId elseId site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .conditional condition thenId elseId)
      (evaluatedPrefix : Dynamic.ExpressionEvaluates program context evidence source environment heap condition (.bool true) heap)
      (child : UninitializedAt program context evidence source environment heap thenId site location) :
      UninitializedAt program context evidence source environment heap id site location
  | elseBranch {id condition thenId elseId site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .conditional condition thenId elseId)
      (evaluatedPrefix : Dynamic.ExpressionEvaluates program context evidence source environment heap condition (.bool false) heap)
      (child : UninitializedAt program context evidence source environment heap elseId site location) :
      UninitializedAt program context evidence source environment heap id site location

theorem UninitializedAt.faults
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {root site : ExpressionId} {location : Dynamic.Location}
    (provenance : UninitializedAt program context evidence source environment heap root site location) :
    Dynamic.ExpressionFaults program context evidence source environment heap root
      (.uninitializedLocation location) heap := by
  induction provenance with
  | localRead site lookup read cellType ordinary empty =>
      apply Dynamic.ExpressionFaults.form site.contains
      rw [site.form, site.requirements, site.coercions]
      exact .localUninitialized (owned := []) rfl lookup read ordinary empty
        (cellType ▸ site.types.not_mapping)
  | group metadata form _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .group rfl ih
  | pairLeft metadata form _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .tuple rfl (.head ih)
  | pairRight metadata form evaluatedPrefix _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .tuple rfl (.tail evaluatedPrefix (.head ih))
  | condition metadata form _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .conditionalCondition rfl ih
  | thenBranch metadata form evaluatedPrefix _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .conditionalTrueBranch rfl evaluatedPrefix ih
  | elseBranch metadata form evaluatedPrefix _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .conditionalFalseBranch rfl evaluatedPrefix ih

/-- The propagated occurrence names an actual absent ordinary local cell.
No injectivity assumption is imposed on the caller's reason provider. -/
theorem UninitializedAt.read_site
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {root site : ExpressionId} {location : Dynamic.Location}
    (provenance : UninitializedAt program context evidence source environment heap root site location) :
    ∃ (scope : SourceCoreLocalCell.Scope) (type : Core.Ty)
      (readSite : ReadSite source scope site type) (cell : Dynamic.Cell),
      Dynamic.Environment.LooksUp environment readSite.binder location ∧
      Dynamic.Heap.Reads heap location cell ∧ cell.type = readSite.node.type ∧
      cell.generalized = none ∧ cell.value = none := by
  induction provenance with
  | localRead site lookup read cellType ordinary empty =>
      exact ⟨_, _, site, _, lookup, read, cellType, ordinary, empty⟩
  | group _ _ _ ih | pairLeft _ _ _ ih | pairRight _ _ _ _ ih
  | condition _ _ _ ih | thenBranch _ _ _ _ ih | elseBranch _ _ _ _ ih => exact ih

inductive OutcomeRepresents (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (reasonAt : ExpressionId → Core.Word) (root : ExpressionId) (type : Core.Ty) :
    Dynamic.ExpressionOutcome → Core.Value → Prop where
  | value (value : SourceStagedValue.Value) (typed : SourceStagedValue.coreType value = type) :
      OutcomeRepresents program context evidence source environment heap reasonAt root type
        (.value (StagedValue.toSource value)) (.inRight .word (SourceStagedValue.toCore value))
  | uninitialized (site : ExpressionId) (location : Dynamic.Location)
      (provenance : UninitializedAt program context evidence source environment heap root site location) :
      OutcomeRepresents program context evidence source environment heap reasonAt root type
        (.fault (.uninitializedLocation location)) (.inLeft type (.word (reasonAt site)))


private theorem OutcomeRepresents.mapRoot
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {reasonAt : ExpressionId → Core.Word} {root parent : ExpressionId} {type : Core.Ty}
    {sourceOutcome : Dynamic.ExpressionOutcome} {coreValue : Core.Value}
    (related : OutcomeRepresents program context evidence source environment heap reasonAt root type sourceOutcome coreValue)
    (lift : ∀ site location, UninitializedAt program context evidence source environment heap root site location →
      UninitializedAt program context evidence source environment heap parent site location) :
    OutcomeRepresents program context evidence source environment heap reasonAt parent type sourceOutcome coreValue := by
  cases related with
  | value staged typed => exact .value staged typed
  | uninitialized site location provenance => exact .uninitialized site location (lift site location provenance)

private theorem word_constructs {span : Syntax.SourceSpan}
    {literal : Syntax.CoreLiteralValue} {value : Core.Word}
    (meaning : WordLiteralDenotes ⟨span, literal⟩ value) :
    Dynamic.LiteralConstructs literal (.word value) := by
  have modulo : Core.Word.ofNatModulo value.val = value := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.isLt
  rw [← modulo]
  exact .word meaning

/-- The certificate supplies both independent source and Core derivations.
Neither heap changes, including when a child read fails. -/
theorem Tree.preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type expression depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store expression coreValue store := by
  induction tree with
  | unit metadata form =>
      refine ⟨.value .unit, .inRight .word .unit, .value ?_, .value .unit rfl, .inRight .unit⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]
        exact .tuple rfl .nil .nil
      · rw [metadata.coercions]; exact .nil
  | bool value metadata form =>
      refine ⟨.value (.bool value), .inRight .word (.bool value), .value ?_,
        .value (.bool value) rfl, .inRight .bool⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]; exact .builtinBoolean rfl
      · rw [metadata.coercions]; exact .nil
  | word value metadata form meaning =>
      refine ⟨.value (.word value), .inRight .word (.word value), .value ?_,
        .value (.word value) rfl, .inRight .word⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]
        exact .literal rfl (word_constructs meaning)
      · rw [metadata.coercions]; exact .nil
  | @localRead id node type binder name index metadata form owned slot =>
      obtain ⟨location, cell, stored, lookup, coreLookup, _, read, coreRead, related⟩ :=
        environments.lookup_heap heaps slot
      have cellType := related.types.source_unique metadata.types
      let site : ReadSite source scope id type := {
        node, binder, name, index, contains := metadata.contains, form, owner := owned
        requirements := metadata.requirements, coercions := metadata.coercions
        slot, types := metadata.types
      }
      cases related with
      | uninitialized types =>
          obtain ⟨fault, evaluated⟩ := site.uninitialized program context evidence environment heap
            coreEnvironment store location _ lookup read cellType rfl rfl coreLookup coreRead (reasonAt id)
          exact ⟨_, _, .fault fault, .uninitialized id location (.localRead site lookup read cellType rfl rfl), evaluated⟩
      | initialized value =>
          obtain ⟨evaluated, coreEvaluated⟩ := site.initialized program context evidence environment heap
            coreEnvironment store location _ value lookup read rfl rfl coreLookup coreRead (reasonAt id)
          exact ⟨_, _, .value evaluated, .value value rfl, coreEvaluated⟩
  | group metadata form child inductionHypothesis =>
      obtain ⟨outcome, coreValue, evaluated, related, coreEvaluated⟩ := inductionHypothesis
      refine ⟨outcome, coreValue, ?_, related.mapRoot (fun _ _ trace => .group metadata form trace), coreEvaluated⟩
      cases evaluated with
      | value evaluated =>
          apply Dynamic.ExpressionEvaluatesOutcome.value
          apply Dynamic.ExpressionEvaluates.intro metadata.contains
          · rw [form, metadata.requirements, metadata.coercions]; exact .group rfl evaluated
          · rw [metadata.coercions]; exact .nil
      | fault fault =>
          apply Dynamic.ExpressionEvaluatesOutcome.fault
          apply Dynamic.ExpressionFaults.form metadata.contains
          rw [form, metadata.requirements, metadata.coercions]
          exact .group rfl fault
  | @pair id left right node leftType rightType leftCode rightCode leftDepth rightDepth
      metadata form leftTree rightTree leftInduction rightInduction =>
      obtain ⟨leftOutcome, leftValue, leftSource, leftRelated, leftCore⟩ := leftInduction
      cases leftRelated with
      | uninitialized faultSite location provenance =>
          cases leftSource with
          | fault fault =>
              refine ⟨_, _, .fault ?_, .uninitialized faultSite location (.pairLeft metadata form provenance),
                Core.LocalSequence.pair_left_failure leftType rightType leftCore⟩
              apply Dynamic.ExpressionFaults.form metadata.contains
              rw [form, metadata.requirements, metadata.coercions]
              exact .tuple rfl (.head fault)
      | value leftValue leftTypeEq =>
          cases leftSource with
          | value leftSource =>
              obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightInduction
              have weakened := rightCore.weakenAt_zero_cellPayload rightTree.hasType
                (.sum .word rightTree.cellPayload) (environments.runtime_hasTypes [])
                (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes
                (SourceStagedValue.toCore leftValue)
              cases rightRelated with
              | uninitialized faultSite location provenance =>
                  cases rightSource with
                  | fault fault =>
                      refine ⟨_, _, .fault ?_, .uninitialized faultSite location (.pairRight metadata form leftSource provenance),
                        Core.LocalSequence.pair_right_failure leftType rightType leftCore weakened⟩
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .tuple rfl (.tail leftSource (.head fault))
              | value rightValue rightTypeEq =>
                  cases rightSource with
                  | value rightSource =>
                      refine ⟨.value (StagedValue.toSource (.product leftValue rightValue)),
                        .inRight .word (SourceStagedValue.toCore (.product leftValue rightValue)),
                        .value ?_, .value (.product leftValue rightValue) ?_,
                        Core.LocalSequence.pair_success leftType rightType leftCore weakened⟩
                      · apply Dynamic.ExpressionEvaluates.intro metadata.contains
                        · rw [form, metadata.requirements, metadata.coercions]
                          exact .tuple rfl (.cons leftSource (.cons rightSource .nil))
                            (.cons (.singleton _))
                        · rw [metadata.coercions]; exact .nil
                      · simp [SourceStagedValue.coreType, leftTypeEq, rightTypeEq]
  | @conditional id condition thenId elseId node type conditionCode thenCode elseCode
      conditionDepth thenDepth elseDepth metadata form conditionTree thenTree elseTree
      conditionIH thenIH elseIH =>
      obtain ⟨conditionOutcome, conditionValue, conditionSource, conditionRelated, conditionCore⟩ := conditionIH
      cases conditionRelated with
      | uninitialized site location provenance =>
          have propagated := UninitializedAt.condition metadata form provenance
          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
            Core.LocalControl.choose_failure type conditionCore⟩
      | value staged typed =>
          have boolean : ∃ value, staged = .bool value := by
            cases staged <;> simp_all [SourceStagedValue.coreType]
          obtain ⟨boolean, rfl⟩ := boolean
          cases conditionSource with
          | value conditionSource =>
              cases boolean with
              | true =>
                  obtain ⟨outcome, coreValue, branchSource, branchRelated, branchCore⟩ := thenIH
                  have shifted := branchCore.weakenAt_zero_cellPayload thenTree.hasType
                    (.sum .word thenTree.cellPayload) (environments.runtime_hasTypes [])
                    (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes (.bool true)
                  refine ⟨outcome, coreValue, ?_,
                    branchRelated.mapRoot (fun _ _ trace => .thenBranch metadata form conditionSource trace),
                    Core.LocalControl.choose_true type conditionCore shifted⟩
                  cases branchSource with
                  | value evaluated =>
                      apply Dynamic.ExpressionEvaluatesOutcome.value
                      apply Dynamic.ExpressionEvaluates.intro metadata.contains
                      · rw [form, metadata.requirements, metadata.coercions]
                        exact .conditionalTrue rfl conditionSource evaluated
                      · rw [metadata.coercions]; exact .nil
                  | fault fault =>
                      apply Dynamic.ExpressionEvaluatesOutcome.fault
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .conditionalTrueBranch rfl conditionSource fault
              | false =>
                  obtain ⟨outcome, coreValue, branchSource, branchRelated, branchCore⟩ := elseIH
                  have shifted := branchCore.weakenAt_zero_cellPayload elseTree.hasType
                    (.sum .word elseTree.cellPayload) (environments.runtime_hasTypes [])
                    (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes (.bool false)
                  refine ⟨outcome, coreValue, ?_,
                    branchRelated.mapRoot (fun _ _ trace => .elseBranch metadata form conditionSource trace),
                    Core.LocalControl.choose_false type conditionCore shifted⟩
                  cases branchSource with
                  | value evaluated =>
                      apply Dynamic.ExpressionEvaluatesOutcome.value
                      apply Dynamic.ExpressionEvaluates.intro metadata.contains
                      · rw [form, metadata.requirements, metadata.coercions]
                        exact .conditionalFalse rfl conditionSource evaluated
                      · rw [metadata.coercions]; exact .nil
                  | fault fault =>
                      apply Dynamic.ExpressionEvaluatesOutcome.fault
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .conditionalFalseBranch rfl conditionSource fault


private theorem bind_ok {α β : Type} {computation : Except SourceCoreBasic.Error α}
    {next : α → Except SourceCoreBasic.Error β} {result : β}
    (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem fromBasicLeaf
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (notGroup : ∀ inner, node.form ≠ .group inner)
    (notPair : ∀ left right, node.form ≠ .tuple [left, right])
    (tree : BasicExpressions.Tree source scope (reasonAt id) id type code depth) :
    Tree source scope reasonAt id type code depth := by
  cases tree with
  | unit metadata form => exact .unit metadata form
  | bool value metadata form => exact .bool value metadata form
  | word value metadata form meaning => exact .word value metadata form meaning
  | localRead metadata form owned slot => exact .localRead metadata form owned slot
  | group metadata form child =>
      have same := Option.some.inj (found.symm.trans (lookupExpression?_complete unique metadata.contains))
      cases same
      exact False.elim (notGroup _ form)
  | pair metadata form left right =>
      have same := Option.some.inj (found.symm.trans (lookupExpression?_complete unique metadata.contains))
      cases same
      exact False.elim (notPair _ _ form)

private theorem tree_of_basicLeaf
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (notGroup : ∀ inner, node.form ≠ .group inner)
    (notPair : ∀ left right, node.form ≠ .tuple [left, right])
    (accepted : SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id) = .ok lowered) :
    ∃ depth, depth ≤ fuel ∧ Tree source scope reasonAt id lowered.type lowered.expression depth := by
  obtain ⟨depth, bound, tree⟩ := BasicExpressions.tree_of_lowerExpression accepted
  exact ⟨depth, bound, fromBasicLeaf unique found notGroup notPair tree⟩

/-- Extraction checks the executable conditional compiler, including its
fallback leaf checks. Uniqueness identifies the same occurrence across the
control and basic metadata lookups. No semantic premise is required. -/
theorem tree_of_lowerExpression
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered) :
    ∃ depth, depth ≤ fuel ∧ Tree source scope reasonAt id lowered.type lowered.expression depth := by
  induction fuel generalizing id lowered with
  | zero => cases accepted
  | succ fuel ih =>
      simp only [SourceCoreControl.lowerExpressionWithReasons] at accepted
      obtain ⟨⟨node, type⟩, read, accepted⟩ := bind_ok accepted
      obtain ⟨found, metadata⟩ := BasicExpressions.readExpression_certificate read
      cases form : node.form with
      | conditional condition thenId elseId =>
          simp only [form] at accepted
          obtain ⟨condition, conditionAccepted, accepted⟩ := bind_ok accepted
          obtain ⟨checkedUnit, conditionChecked, accepted⟩ := bind_ok accepted
          cases checkedUnit
          obtain ⟨thenBranch, thenAccepted, accepted⟩ := bind_ok accepted
          obtain ⟨elseBranch, elseAccepted, accepted⟩ := bind_ok accepted
          obtain ⟨checkedUnit, thenChecked, accepted⟩ := bind_ok accepted
          cases checkedUnit
          obtain ⟨checkedUnit, elseChecked, accepted⟩ := bind_ok accepted
          cases checkedUnit
          cases accepted
          obtain ⟨conditionDepth, conditionBound, conditionTree⟩ := ih conditionAccepted
          obtain ⟨thenDepth, thenBound, thenTree⟩ := ih thenAccepted
          obtain ⟨elseDepth, elseBound, elseTree⟩ := ih elseAccepted
          rw [← ensureType_ok conditionChecked] at conditionTree
          rw [← ensureType_ok thenChecked] at thenTree
          rw [← ensureType_ok elseChecked] at elseTree
          exact ⟨max conditionDepth (max thenDepth elseDepth) + 1, by omega,
            .conditional metadata form conditionTree thenTree elseTree⟩
      | group inner =>
          simp only [form] at accepted
          obtain ⟨child, childAccepted, accepted⟩ := bind_ok accepted
          obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
          cases checkedUnit
          cases accepted
          obtain ⟨depth, bound, childTree⟩ := ih childAccepted
          exact ⟨depth + 1, by omega, .group (ensureType_ok checked ▸ metadata) form childTree⟩
      | tuple elements =>
          cases elements with
          | nil =>
              simp only [form] at accepted
              exact tree_of_basicLeaf unique found
                (by intro inner impossible; rw [form] at impossible; cases impossible)
                (by intro left right impossible; rw [form] at impossible; cases impossible) accepted
          | cons left rest =>
              cases rest with
              | nil =>
                  simp only [form] at accepted
                  exact tree_of_basicLeaf unique found
                    (by intro inner impossible; rw [form] at impossible; cases impossible)
                    (by intro left right impossible; rw [form] at impossible; cases impossible) accepted
              | cons right rest =>
                  cases rest with
                  | cons =>
                      simp only [form] at accepted
                      exact tree_of_basicLeaf unique found
                        (by intro inner impossible; rw [form] at impossible; cases impossible)
                        (by intro left right impossible; rw [form] at impossible; cases impossible) accepted
                  | nil =>
                      simp only [form] at accepted
                      obtain ⟨leftResult, leftAccepted, accepted⟩ := bind_ok accepted
                      obtain ⟨rightResult, rightAccepted, accepted⟩ := bind_ok accepted
                      obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                      cases checkedUnit
                      cases accepted
                      obtain ⟨leftDepth, leftBound, leftTree⟩ := ih leftAccepted
                      obtain ⟨rightDepth, rightBound, rightTree⟩ := ih rightAccepted
                      have same := ensureType_ok checked
                      rw [same]
                      exact ⟨max leftDepth rightDepth + 1, by omega,
                        .pair (same ▸ metadata) form leftTree rightTree⟩
      | literal | reference | integerLiteral | unary | binary | lambda | call | constructor | member | proxy | index =>
          simp only [form] at accepted
          exact tree_of_basicLeaf unique found
            (by intro inner impossible; rw [form] at impossible; cases impossible)
            (by intro left right impossible; rw [form] at impossible; cases impossible) accepted

theorem Tree.lower
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source) (fuel : Nat) (enough : depth ≤ fuel) :
    SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok ⟨type, code⟩ := by
  induction tree generalizing fuel with
  | unit metadata form =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [SourceCoreControl.lowerExpressionWithReasons, metadata.read unique, bind, Except.bind, form]
          exact SourceCoreBasic.lowerExpression_unit (metadata.read unique) form
  | bool value metadata form =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [SourceCoreControl.lowerExpressionWithReasons, metadata.read unique, bind, Except.bind, form]
          exact SourceCoreBasic.lowerExpression_bool (metadata.read unique) form
  | word value metadata form meaning =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [SourceCoreControl.lowerExpressionWithReasons, metadata.read unique, bind, Except.bind, form]
          exact SourceCoreBasic.lowerExpression_word (metadata.read unique) form (interpretWordLiteral?_complete meaning)
  | localRead metadata form owned slot =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [SourceCoreControl.lowerExpressionWithReasons, metadata.read unique, bind, Except.bind, form]
          apply SourceCoreBasic.lowerExpression_local (metadata.read unique) form
          exact SourceCoreLocalCell.lowerRead_eq (lookupExpression?_complete unique metadata.contains)
            form owned metadata.requirements metadata.coercions slot (metadata.types.lower _) _
  | group metadata form child ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [SourceCoreControl.lowerExpressionWithReasons, metadata.read unique, form,
            ih fuel (by omega), SourceCoreBasic.ensureType, bind, Except.bind, pure, Pure.pure, Except.pure]
  | pair metadata form left right leftIH rightIH =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [SourceCoreControl.lowerExpressionWithReasons, metadata.read unique, form,
            leftIH fuel (by omega), rightIH fuel (by omega), SourceCoreBasic.ensureType,
            bind, Except.bind, pure, Pure.pure, Except.pure]
  | conditional metadata form condition thenBranch elseBranch conditionIH thenIH elseIH =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreControl.lowerExpression_conditional (metadata.read unique) form
            (conditionIH fuel (by omega)) (thenIH fuel (by omega)) (elseIH fuel (by omega))

theorem lowerExpression_hasType
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) lowered.expression
      (Core.LanguageResult.resultType lowered.type) := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  exact tree.hasType

theorem Tree.metadata
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type code depth) :
    ∃ node, Metadata source id node type := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ | conditional metadata _ _ _ _ => exact ⟨_, metadata⟩

theorem lowerExpression_metadata
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered) :
    ∃ node, SourceCoreBasic.readExpression source id = .ok (node, lowered.type) ∧
      Metadata source id node lowered.type := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  obtain ⟨node, metadata⟩ := tree.metadata
  exact ⟨node, metadata.read unique, metadata⟩

/-- Actual accepted output has a finite independent source and Core evaluation.
Fault correspondence records the executed read occurrence, not just its location. -/
theorem lowerExpression_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store lowered.expression coreValue store := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  exact tree.preserves program context evidence environments heaps

/-- Every completed machine run agrees with the derived source result and
unchanged store. The finite grammar supplies sufficient runtime fuel; this is
not an unrestricted normalization or source-fault completeness statement. -/
theorem lowerExpression_run_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    Core.infer? (SourceCoreLocalCell.coreContext scope) lowered.expression =
      some (Core.LanguageResult.resultType lowered.type) ∧
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial lowered.expression coreEnvironment store) =
        .done coreValue store) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial lowered.expression coreEnvironment store) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store) := by
  obtain ⟨sourceOutcome, coreValue, sourceEvaluation, related, coreEvaluation⟩ :=
    lowerExpression_preserves unique accepted program context evidence environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreEvaluation
  refine ⟨Core.infer_complete (lowerExpression_hasType unique accepted),
    sourceOutcome, coreValue, required, sourceEvaluation, related, completes, ?_⟩
  intro fuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreEvaluation

end Solcore.SourceSemantics.CoreLowering.ControlExpressions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualCallablePolicy
/-! Authenticate the callable hooks used by the actual general compiler.
These are static code equations. Source code/capture typing and the body
meaning theorem remain separate obligations. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ActualCallablePolicy

open Frontend Frontend.SourceInference

private theorem descriptor_reconstructs
    {table : SourceCoreStageCodebook.Table} {origin : SourceCoreStageCodebook.Origin}
    (descriptor : SourceCoreCallableContracts.Descriptor table origin) :
    SourceCoreCallableContracts.descriptor table origin = .ok descriptor := by
  cases descriptor
  rename_i id found
  unfold SourceCoreCallableContracts.descriptor
  split
  · rename_i missing
    rw [found] at missing
    contradiction
  · rename_i selected actual
    have same := Option.some.inj (actual.symm.trans found)
    subst selected
    rfl

/-- Lambda decoration in the production policy uses the exact full
instantiation context recorded in the artifact's sealed codebook. -/
theorem lambda_decoration
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (context : SourceCoreFunctions.Context) (source : TypedSource) (node : ExpressionNode)
    (id : ExpressionId) (parameter result : Core.Ty) (value : Core.Expr)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.lambda context.owner id active)) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).decorateCallable
      context source node (.lambda id) parameter result (Core.LanguageResult.success value) =
      .ok (Core.LanguageResult.success (descriptor.wrap value)) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, descriptor_reconstructs descriptor,
    Core.LanguageResult.success, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem named_decoration
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (context : SourceCoreFunctions.Context) (source : TypedSource) (node : ExpressionNode)
    (key : SourceCoreStageCodebook.Key) (parameter result : Core.Ty) (value : Core.Expr)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named key)) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).decorateCallable
      context source node (.named key) parameter result (Core.LanguageResult.success value) =
      .ok (Core.LanguageResult.success (descriptor.wrap value)) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, descriptor_reconstructs descriptor,
    Core.LanguageResult.success, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem builtin_decoration
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (context : SourceCoreFunctions.Context) (source : TypedSource) (node : ExpressionNode)
    (function : BuiltinFunctionId) (parameter result : Core.Ty) (value : Core.Expr)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin function)) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).decorateCallable
      context source node (.builtin function) parameter result (Core.LanguageResult.success value) =
      .ok (Core.LanguageResult.success (descriptor.wrap value)) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, descriptor_reconstructs descriptor,
    Core.LanguageResult.success, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem indirect_call
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (context : SourceCoreFunctions.Context) (source : TypedSource) (node : ExpressionNode)
    (callee : ExpressionId) (arguments : List ExpressionId) (function : IndirectCallResolution)
    (result : Core.Ty) (calleeCode argumentsCode : Core.Expr)
    (site : SourceCoreCallableContracts.Callsite)
    (form : node.form = .call callee arguments (.indirect function))
    (accepted : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).callCallable
      context source node result calleeCode argumentsCode =
      .ok (site.lower native.diagnostics.unknown result calleeCode argumentsCode) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, form, accepted,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- The real policy supplies the decoration obligation of the generic
contracted closure certificate. No source or Core execution is assumed. -/
def closureCode
    {catalog : SourceCoreDataCatalog.Catalog} {program : Program}
    {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {active : TypeSystem.Substitution}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrativeContext : Core.Context} {id : ExpressionId} {node : ExpressionNode}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (native : SourceCoreGeneralFunctions.CallableContext)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (artifact : DecoratedFunctionCode.LambdaCertificate bodyCertificate policy compilation function.source
      scope id node function.parameters function.resultType function.body reportedType lowered)
    (owner : compilation.owner.declaration = function.source.owner)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.lambda compilation.owner id active))
    (frame : Dynamic.ClosureFrame program function)
    (projection : catalog.project (FunctionValues.sourceType function) = .ok
      (Core.CallableContract.functionType artifact.raw.parameterCore artifact.raw.resultCore))
    (typed : Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext)
      lowered.expression (Core.LanguageResult.resultType
        (Core.CallableContract.functionType artifact.raw.parameterCore artifact.raw.resultCore)) catalog.definitions) :
    ContractedFunctionValues.Code catalog program bodyCertificate policy compilation native.table active
      function scope administrativeContext where
  id := id
  node := node
  reportedType := reportedType
  lowered := lowered
  artifact := artifact
  owner := owner
  descriptor := descriptor
  decoration := by
    intro value
    rw [profile]
    exact lambda_decoration native active compilation function.source node id
      artifact.raw.parameterCore artifact.raw.resultCore value descriptor
  frame := frame
  projection := projection
  outputTyped := typed

end Solcore.SourceSemantics.CoreLowering.ActualCallablePolicy
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallStageBoundary
/-! A stage-rejected indirect-call boundary preserves the exact callee prefix.
The child theorem is universal over related states; no child Core evaluation is
assumed. Static dispatch coverage relates artifact descriptors to the explicit
source contract ledger and original retained guard receipts. It is a separate
obligation of the enclosing compiler profile, not inferred from Core typing.

The result is for the staged CallBoundary extension. Plain Dynamic and recursive
stage-frame propagation are deliberately outside this theorem. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallStageBoundary
open Core Frontend Frontend.SourceInference GeneralHeap ReadOnly

/-- All fields concern static provenance and value representation. In
particular this certificate does not contain a guard verdict or an evaluation. -/
structure Dispatch (frame : Staging.CallBoundary.Frame) (site : SourceCoreCallableContracts.Callsite)
    (call : ExpressionId) (arguments : List ExpressionId) (source : Dynamic.Value) (carrier : Value) where
  function : Value
  contract : Word
  row : SourceCoreStageCodebook.Decision
  guard : SourceCoreStageContracts.Guard
  shape : carrier = .pair function (.word contract)
  found : site.rowAt? contract = some row
  attached : row.guard = some guard
  call_eq : guard.node.id = call
  arguments_eq : guard.arguments = arguments
  stages : frame.stages = CallStageGuard.frame guard.sidecar.caller
  bound : frame.Binds source ⟨guard.contract.parameters, guard.contract.stagedResult⟩

def Dispatch.reason {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Value}
    (dispatch : Dispatch frame site call arguments source carrier) (reason : Staging.CallGuard.Fault) : Word :=
  site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeArguments
    (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason)

theorem Dispatch.rejected {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Value}
    (dispatch : Dispatch frame site call arguments source carrier) {reason : Staging.CallGuard.Fault}
    (rejected : Staging.CallBoundary.GuardRejects frame call arguments source reason) :
    dispatch.row.beforeArguments = .error
      (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason) := by
  cases rejected with
  | contract bound rejected =>
    cases frame.unique bound dispatch.bound
    have guarded : Staging.CallGuard.Rejects (CallStageGuard.frame dispatch.guard.sidecar.caller)
        ⟨dispatch.guard.contract.parameters, dispatch.guard.contract.stagedResult⟩
        dispatch.guard.node.id dispatch.guard.arguments reason := by
      simpa only [dispatch.call_eq, dispatch.arguments_eq, ← dispatch.stages] using rejected
    have failed := (CallStageGuard.guard_rejects_iff dispatch.guard _).mpr ⟨reason, guarded, rfl⟩
    simpa only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer,
      dispatch.attached] using failed

/-- Accepted source guards select the exact success branch of the sealed row. -/
theorem Dispatch.accepted {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Value}
    (dispatch : Dispatch frame site call arguments source carrier)
    (accepted : Staging.CallBoundary.GuardAccepts frame call arguments source) :
    dispatch.row.beforeArguments = .ok () := by
  cases accepted with
  | builtin => cases frame.userCallable dispatch.bound
  | contract bound accepted =>
    cases frame.unique bound dispatch.bound
    have guarded : Staging.CallGuard.Accepts (CallStageGuard.frame dispatch.guard.sidecar.caller)
        ⟨dispatch.guard.contract.parameters, dispatch.guard.contract.stagedResult⟩
        dispatch.guard.node.id dispatch.guard.arguments := by
      simpa only [dispatch.call_eq, dispatch.arguments_eq, ← dispatch.stages] using accepted
    have passed := (CallStageGuard.guard_accepts_iff dispatch.guard).mpr guarded
    simpa only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer,
      dispatch.attached] using passed

/-- Gate acceptance reconstructs the source guard from its original metadata;
it is not assumed merely because the erased function carrier has a type. -/
theorem Dispatch.accepted_iff {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Value}
    (dispatch : Dispatch frame site call arguments source carrier) :
    dispatch.row.beforeArguments = .ok () ↔ Staging.CallBoundary.GuardAccepts frame call arguments source := by
  constructor
  · intro passed
    have guarded : dispatch.guard.decision = .ok () := by
      simpa only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer,
        dispatch.attached] using passed
    apply Staging.CallBoundary.GuardAccepts.contract dispatch.bound
    have accepted := (CallStageGuard.guard_accepts_iff dispatch.guard).mp guarded
    simpa only [dispatch.call_eq, dispatch.arguments_eq, ← dispatch.stages] using accepted
  · exact dispatch.accepted

/-- A retained gate error reconstructs the exact independent stage failure,
including original occurrence/index coordinates before word assignment. -/
theorem Dispatch.rejected_of_error {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Value}
    (dispatch : Dispatch frame site call arguments source carrier) (diagnostic : SourceCompilationPlan.Error)
    (failed : dispatch.row.beforeArguments = .error diagnostic) :
    ∃ reason, Staging.CallBoundary.GuardRejects frame call arguments source reason ∧
      diagnostic = CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason := by
  have guarded : dispatch.guard.decision = .error diagnostic := by
    simpa only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer,
      dispatch.attached] using failed
  obtain ⟨reason, rejected, exactError⟩ := (CallStageGuard.guard_rejects_iff dispatch.guard diagnostic).mp guarded
  refine ⟨reason, Staging.CallBoundary.GuardRejects.contract dispatch.bound ?_, exactError⟩
  simpa only [dispatch.call_eq, dispatch.arguments_eq, ← dispatch.stages] using rejected

/-- Stage words retain the exact source failure under the selected sealed row. -/
def ReasonRepresents (site : SourceCoreCallableContracts.Callsite) (reason : Staging.CallGuard.Fault) (token : Word) : Prop :=
  ∃ row guard, row ∈ site.rows ∧ row.guard = some guard ∧
    token = site.reasonAt row.caller row.call row.entry.id .beforeArguments
      (CallStageGuard.error guard.sidecar.caller guard.node guard.contract.owner reason)

theorem Dispatch.reason_represents {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Value}
    (dispatch : Dispatch frame site call arguments source carrier) (reason : Staging.CallGuard.Fault) :
    ReasonRepresents site reason (dispatch.reason reason) :=
  ⟨dispatch.row, dispatch.guard, List.mem_of_find?_eq_some dispatch.found, dispatch.attached, rfl⟩

/-- Coverage is a property of the artifact's function-value relation and source
contract ledger. It does not assume the current call or any child completes. -/
def CoversFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (frame : Staging.CallBoundary.Frame) (site : SourceCoreCallableContracts.Callsite)
    (call : ExpressionId) (arguments : List ExpressionId) (sourceType : TypeSystem.Ty) (type : Ty) : Prop :=
  ∀ {mapping world source carrier contract}, model.Represents mapping world sourceType source carrier type →
    frame.Binds source contract → Nonempty (Dispatch frame site call arguments source carrier)

def Covers {catalog : SourceCoreDataCatalog.Catalog} (model : GenericHeap.PayloadModel catalog)
    (frame : Staging.CallBoundary.Frame) (site : SourceCoreCallableContracts.Callsite)
    (call : ExpressionId) (arguments : List ExpressionId) (sourceType : TypeSystem.Ty) (type : Ty) : Prop :=
  CoversFor model frame site call arguments sourceType type

/-- A finite staged-source rejection derives its Core callee computation from
the universal child theorem, then emits the exact language failure without
executing arguments. The post-callee heap, map/world and administrative frame
are retained, including any writes or allocations performed by the callee. -/
theorem preserves_rejection_for {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
    {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite} {call callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution} {scope : SourceCoreLocalCell.Scope}
    {lowered : SourceCoreBasic.LoweredExpr} {calleeNode : ExpressionNode}
    (certified : certificate scope callee lowered) (found : source.lookupExpression? callee = some calleeNode)
    (childMeaning : GenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    (coverage : CoversFor model frame site call arguments calleeNode.type lowered.type)
    (unknown : Word) (result : Ty) (argumentCode : Expr)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Staging.CallGuard.Fault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.CallBoundary.Executes program frame context evidence source environment before call callee arguments metadata
      (.stageFault reason) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown result (lowered.expression.rename ξ) argumentCode)
        (.inLeft result (.word token)) finalStore ∧
      ReasonRepresents site reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨callable, calleeEvaluation, rejected⟩ := Staging.CallBoundary.Executes.stageFault_iff.mp execution
  obtain ⟨carrier, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, framePreserved, metadataPreserved⟩ :=
    childMeaning certified found environments heaps locals layout (.value calleeEvaluation)
  cases represented with
  | value represented =>
    have binding : ∃ contract, frame.Binds callable contract := by cases rejected with | contract bound _ => exact ⟨_, bound⟩
    obtain ⟨contract, bound⟩ := binding
    obtain ⟨dispatch⟩ := coverage represented bound
    have failed := dispatch.rejected rejected
    rw [dispatch.shape] at evaluated
    exact ⟨dispatch.reason reason, finalStore, finalMap, finalWorld,
      site.lower_stage_failure unknown dispatch.row _ dispatch.found failed evaluated,
      dispatch.reason_represents reason, finalHeaps, maps, worlds, framePreserved, metadataPreserved⟩

theorem preserves_rejection {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
    {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite} {call callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution} {scope : SourceCoreLocalCell.Scope}
    {lowered : SourceCoreBasic.LoweredExpr} {calleeNode : ExpressionNode}
    (certified : certificate scope callee lowered) (found : source.lookupExpression? callee = some calleeNode)
    (childMeaning : GenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    (coverage : Covers model frame site call arguments calleeNode.type lowered.type)
    (unknown : Word) (result : Ty) (argumentCode : Expr)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Staging.CallGuard.Fault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.CallBoundary.Executes program frame context evidence source environment before call callee arguments metadata
      (.stageFault reason) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown result (lowered.expression.rename ξ) argumentCode)
        (.inLeft result (.word token)) finalStore ∧
      ReasonRepresents site reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves_rejection_for certified found childMeaning coverage unknown result argumentCode
    environments heaps locals layout execution

end Solcore.SourceSemantics.CoreLowering.CallStageBoundary
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallContractCertificates
/-! Static provenance of retained callable contracts and call guards. These
lemmas inspect the actual metadata factories. They do not evaluate source/Core
code or infer source staging flags from projected Core function types.
Contextual lambda receipts retain the entire authenticated substitution. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallContractCertificates
open Frontend Frontend.SourceInference SourceCoreStageContracts

abbrev SourceContract := Staging.CallGuard.Contract

def semanticContract (contract : Contract) : SourceContract :=
  ⟨contract.parameters, contract.stagedResult⟩

theorem expression_sound {sidecar : Sidecar} {id : ExpressionId} {node : ExpressionNode}
    (accepted : expression sidecar id = .ok node) : ContainsExpression sidecar.source id node := by
  unfold expression at accepted
  simp only [bind, Except.bind] at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · next selected found =>
      cases accepted
      have member : node ∈ [node] := List.mem_singleton_self _
      rw [← found] at member
      obtain ⟨candidate, member, selected⟩ := List.mem_filterMap.mp member
      cases candidate with
      | statement => cases selected
      | expression candidate =>
        by_cases same : candidate.id = id
        · simp only [same, ↓reduceIte, Option.some.injEq] at selected
          subst candidate
          exact ⟨member, same⟩
        · simp only [same, ↓reduceIte] at selected
          cases selected
    · cases accepted

/-- The factory's singleton check authenticates every matching occurrence,
not just the first-match lookup used by other frontend traversals. -/
theorem expression_unique {sidecar : Sidecar} {id : ExpressionId} {node other : ExpressionNode}
    (accepted : expression sidecar id = .ok node) (contains : ContainsExpression sidecar.source id other) :
    other = node := by
  unfold expression at accepted
  simp only [bind, Except.bind] at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · next selected found =>
      cases accepted
      have member : other ∈ sidecar.source.nodes.filterMap (fun
          | .expression candidate => if candidate.id = id then some candidate else none
          | .statement _ => none) := by
        apply List.mem_filterMap.mpr
        exact ⟨.expression other, contains.1, by simp only [contains.2, ↓reduceIte]⟩
      have sameFilter : (sidecar.source.nodes.filterMap (fun
          | .expression candidate => if candidate.id = id then some candidate else none
          | .statement _ => none)) = [node] := by
        refine Eq.trans ?_ found
        apply congrArg (fun (select : Node → Option ExpressionNode) => sidecar.source.nodes.filterMap select)
        funext item
        cases item with
        | expression candidate => by_cases same : candidate.id = id <;> simp [same]
        | statement => rfl
      rw [sameFilter] at member
      exact List.mem_singleton.mp member
    · cases accepted

private theorem exactSpecialization_key {plan : Plan} {key : Key} {caller : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok caller) : caller.key = key := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · next selected found =>
    cases accepted
    have member : caller ∈ [caller] := List.mem_singleton_self _
    rw [← found] at member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · cases accepted

theorem sidecar_of_accepted {plan : Plan} {key : Key} {sidecar : Sidecar}
    (accepted : prepareSidecar plan key = .ok sidecar) : sidecar.plan = plan ∧ sidecar.caller.key = key := by
  unfold prepareSidecar at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan key with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    cases valid : SourceCompilationPlan.validateSpecializationMetadataWith true caller with
    | error error => simp [valid, Functor.discard, Functor.mapConst, Except.map] at accepted
    | ok value =>
      simp only [valid] at accepted
      dsimp [Functor.discard, Functor.mapConst, Except.map] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted; exact ⟨rfl, exactSpecialization_key selected⟩
        · cases accepted

structure NamedReceipt (plan : Plan) (key : Key) (contract : Contract) where
  sidecar : Sidecar
  prepared : prepareSidecar plan key = .ok sidecar
  parameters : contract.parameters = sidecar.source.inputs
  stagedResult : contract.stagedResult =
    (sidecar.caller.function.returnComptime || SourceCompilationPlan.sourceTypeIsComptimeOnly sidecar.caller.function.inferredBodyType)
  owner : contract.owner = sidecar.caller.key
  plan_eq : contract.plan = sidecar.plan

theorem named_of_accepted {plan : Plan} {key : Key} {contract : Contract}
    (accepted : Contract.named plan key = .ok contract) : Nonempty (NamedReceipt plan key contract) := by
  unfold Contract.named at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · cases accepted
  · next sidecar prepared => cases accepted; exact ⟨⟨sidecar, prepared, rfl, rfl, rfl, rfl⟩⟩

structure LambdaReceipt (sidecar : Sidecar) (id : ExpressionId) (contract : Contract) where
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  selected : expression sidecar id = .ok node
  form : node.form = .lambda parameters result body
  parameters_eq : contract.parameters = parameters
  stagedResult : contract.stagedResult = SourceCompilationPlan.sourceTypeIsComptimeOnly result
  owner : contract.owner = sidecar.caller.key
  plan_eq : contract.plan = sidecar.plan

theorem lambda_of_accepted {sidecar : Sidecar} {id : ExpressionId} {contract : Contract}
    (accepted : Contract.lambda sidecar id = .ok contract) : Nonempty (LambdaReceipt sidecar id contract) := by
  unfold Contract.lambda at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · cases accepted
  · next node selected =>
    split at accepted
    · next parameters result body form =>
      split at accepted
      · cases accepted
      · cases accepted; exact ⟨⟨node, parameters, result, body, selected, form, rfl, rfl, rfl, rfl⟩⟩
    · cases accepted

structure ContextualLambdaReceipt (sidecar : Sidecar) (prepared : SourceCoreLocalEvidence.Prepared)
    (id : ExpressionId) (contract : Contract) where
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  selected : expression sidecar id = .ok node
  form : node.form = .lambda parameters result body
  parameters_eq : contract.parameters = parameters.map (TypedBinder.applySubstitution prepared.substitution)
  stagedResult : contract.stagedResult = SourceCompilationPlan.sourceTypeIsComptimeOnly (prepared.substitution.apply result)
  owner : contract.owner = sidecar.caller.key
  plan_eq : contract.plan = sidecar.plan
  caller_checked : (prepared.caller == { sidecar.caller with function := { sidecar.caller.function with
    typedBody := sidecar.source.applySubstitution prepared.substitution
    solvedRequirements := SourceCoreLocalEvidence.rewriteLedger prepared.substitution
      prepared.witnesses sidecar.caller.function.solvedRequirements } }) = true

theorem contextualLambda_of_accepted {sidecar : Sidecar} {prepared : SourceCoreLocalEvidence.Prepared}
    {id : ExpressionId} {contract : Contract}
    (accepted : Contract.contextualLambda sidecar prepared id = .ok contract) :
    Nonempty (ContextualLambdaReceipt sidecar prepared id contract) := by
  unfold Contract.contextualLambda at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · next caller =>
    split at accepted
    · cases accepted
    · next node selected =>
      split at accepted
      · next parameters result body form =>
        split at accepted
        · cases accepted
        · cases accepted
          refine ⟨⟨node, parameters, result, body, selected, form, rfl, rfl, rfl, rfl, ?_⟩⟩
          exact caller
      · cases accepted
  · cases accepted

structure GuardReceipt (sidecar : Sidecar) (call : ExpressionId) (contract : Contract) (guard : Guard) where
  sidecar_eq : guard.sidecar = sidecar
  contract_eq : guard.contract = contract
  selected : expression sidecar call = .ok guard.node
  callee : ExpressionId
  metadata : IndirectCallResolution
  form : guard.node.form = .call callee guard.arguments (.indirect metadata)

theorem guard_of_accepted {sidecar : Sidecar} {call : ExpressionId} {contract : Contract} {guard : Guard}
    (accepted : prepareGuard sidecar call contract = .ok guard) :
    Nonempty (GuardReceipt sidecar call contract guard) := by
  unfold prepareGuard at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · split at accepted
    · cases accepted
    · next node selected =>
      split at accepted
      · next callee arguments metadata form =>
        cases accepted; exact ⟨⟨rfl, rfl, selected, callee, metadata, form⟩⟩
      · cases accepted
  · cases accepted

theorem GuardReceipt.call {sidecar : Sidecar} {call : ExpressionId} {contract : Contract} {guard : Guard}
    (receipt : GuardReceipt sidecar call contract guard) : guard.node.id = call :=
  (expression_sound receipt.selected).2

theorem guard_arguments {sidecar : Sidecar} {call : ExpressionId} {contract : Contract} {guard : Guard}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (accepted : prepareGuard sidecar call contract = .ok guard)
    (contains : ContainsExpression sidecar.source call node)
    (form : node.form = .call callee arguments (.indirect metadata)) : guard.arguments = arguments := by
  obtain ⟨receipt⟩ := guard_of_accepted accepted
  have same := expression_unique receipt.selected contains
  have forms := receipt.form.symm.trans (same ▸ form)
  cases forms
  rfl

end Solcore.SourceSemantics.CoreLowering.CallContractCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallEntryCertificates
/-! Origin certificates from the actual codebook entry builders. Each retained
contract points to its original metadata factory, including the full cumulative
substitution for contextual lambdas. Duplicate origins preserve the earlier
authenticated entry. This proves metadata provenance, not callable execution. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallEntryCertificates
open Frontend Frontend.SourceInference SourceCoreStageCodebook CallContractCertificates

inductive OriginContract (plan : Plan) : Origin → Nat → Option Contract → Prop where
  | named {key : Key} {contract : Contract}
      (prepared : SourceCoreStageContracts.Contract.named plan key = .ok contract) :
      OriginContract plan (.named key) contract.parameters.length (some contract)
  | originalLambda {sidecar : Sidecar} {id : ExpressionId} {contract : Contract}
      (original : SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar)
      (prepared : SourceCoreStageContracts.Contract.lambda sidecar id = .ok contract) :
      OriginContract plan (.lambda sidecar.caller.key id []) contract.parameters.length (some contract)
  | contextualLambda {sidecar : Sidecar} {prepared : SourceCoreLocalEvidence.Prepared} {id : ExpressionId} {contract : Contract}
      (original : SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar)
      (checked : SourceCoreStageContracts.Contract.contextualLambda sidecar prepared id = .ok contract) :
      OriginContract plan (.lambda sidecar.caller.key id prepared.substitution) contract.parameters.length (some contract)
  | builtin (function : BuiltinFunctionId) : OriginContract plan (.builtin function) function.parameterTypes.length none

def Authenticated (plan : Plan) (entry : Entry) : Prop := OriginContract plan entry.origin entry.parameterCount entry.contract

def AllAuthenticated (plan : Plan) (entries : List Entry) : Prop := ∀ entry, entry ∈ entries → Authenticated plan entry

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {result : Except ε α} {value : α} {f : ε → δ}
    (accepted : result.mapError f = .ok value) : result = .ok value := by
  cases result with
  | error => cases accepted
  | ok selected => cases accepted; rfl

private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item, item ∈ items → ∀ state outcome, invariant state → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ invariant updated) : invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item items ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

theorem insert_preserves {plan : Plan} {limits : Limits} {firstId count : Nat}
    {entries final : List Entry} {origin : Origin} {contract : Option Contract}
    (old : AllAuthenticated plan entries) (new : OriginContract plan origin count contract)
    (accepted : insert limits firstId entries origin count contract = .ok final) : AllAuthenticated plan final := by
  unfold SourceCoreStageCodebook.insert at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · cases accepted; exact old
  · split at accepted
    · cases accepted
    · split at accepted
      · next selected found =>
        cases accepted
        intro entry member
        rcases List.mem_append.mp member with previous | fresh
        · exact old entry previous
        · have same := List.mem_singleton.mp fresh
          subst entry
          exact new
      · cases accepted

theorem collectLambdas_preserves {plan : Plan} {limits : Limits} {firstId : Nat} {sidecar : Sidecar}
    {prepared : Option SourceCoreLocalEvidence.Prepared} {entries final : List Entry}
    (original : SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar) (old : AllAuthenticated plan entries)
    (accepted : collectLambdas limits firstId sidecar prepared entries = .ok final) : AllAuthenticated plan final := by
  unfold collectLambdas at accepted
  obtain ⟨updated, loop, accepted⟩ := bind_ok accepted
  cases accepted
  apply forIn_invariant loop old
  intro id _ state outcome previous iteration
  dsimp only at iteration
  cases prepared with
  | none =>
    cases prepared : SourceCoreStageContracts.Contract.lambda sidecar id with
    | error error =>
      cases error <;> simp only [prepared] at iteration <;> try cases iteration
      exact ⟨state, rfl, previous⟩
    | ok contract =>
      simp only [prepared] at iteration
      obtain ⟨updated, inserted, iteration⟩ := bind_ok iteration
      cases iteration
      exact ⟨updated, rfl, insert_preserves previous (.originalLambda original prepared) inserted⟩
  | some contextual =>
    cases prepared : SourceCoreStageContracts.Contract.contextualLambda sidecar contextual id with
    | error error =>
      cases error <;> simp only [prepared] at iteration <;> try cases iteration
      exact ⟨state, rfl, previous⟩
    | ok contract =>
      simp only [prepared] at iteration
      obtain ⟨updated, inserted, iteration⟩ := bind_ok iteration
      cases iteration
      exact ⟨updated, rfl, insert_preserves previous (.contextualLambda original prepared) inserted⟩

/-- Public codebook preparation authenticates every retained entry. Contextual
instances keep their actual sealed local-evidence receipt; no runtime closure
or arbitrary type erasure is used to reconstruct its flags. -/
theorem prepareWithProjection_authenticates {program : CheckedProgram} {plan : Plan} {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {table : Table}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok table) : AllAuthenticated plan table.entries := by
  unfold prepareWithProjection at accepted
  split at accepted
  · cases accepted
  · obtain ⟨state, originals, accepted⟩ := bind_ok accepted
    have initial : AllAuthenticated plan state.1 := by
      apply forIn_invariant (invariant := fun current : List Entry × List Sidecar => AllAuthenticated plan current.1) originals
      · intro entry member; cases member
      · intro specialized _ state outcome previous iteration
        dsimp only at iteration
        obtain ⟨sidecar, selected, iteration⟩ := bind_ok iteration
        have selected := mapError_ok selected
        obtain ⟨contract, prepared, iteration⟩ := bind_ok iteration
        have prepared := mapError_ok prepared
        obtain ⟨entries, inserted, iteration⟩ := bind_ok iteration
        obtain ⟨entries, collected, iteration⟩ := bind_ok iteration
        cases iteration
        exact ⟨_, rfl, collectLambdas_preserves (by rw [(sidecar_of_accepted selected).2]; exact selected)
          (insert_preserves previous (.named prepared) inserted) collected⟩
    obtain ⟨entries, builtins, accepted⟩ := bind_ok accepted
    have builtinEntries : AllAuthenticated plan entries := by
      apply forIn_invariant builtins initial
      intro function _ state outcome previous iteration
      dsimp only at iteration
      obtain ⟨updated, inserted, iteration⟩ := bind_ok iteration
      cases iteration
      exact ⟨updated, rfl, insert_preserves previous (.builtin function) inserted⟩
    obtain ⟨locals, _, accepted⟩ := bind_ok accepted
    dsimp only at accepted
    split at accepted
    · cases accepted
    · obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, contextual, accepted⟩ := bind_ok accepted
      have final : AllAuthenticated plan entries := by
        apply forIn_invariant contextual builtinEntries
        intro contextual _ state outcome previous iteration
        obtain ⟨sidecar, selected, iteration⟩ := bind_ok iteration
        obtain ⟨updated, collected, iteration⟩ := bind_ok iteration
        cases iteration
        exact ⟨updated, rfl, collectLambdas_preserves (by
          have prepared := mapError_ok selected
          rw [(sidecar_of_accepted prepared).2]
          exact prepared) previous collected⟩
      obtain ⟨rows, _, accepted⟩ := bind_ok accepted
      split at accepted
      · split at accepted
        · split at accepted
          · cases accepted; exact final
          · cases accepted
        · cases accepted
      · cases accepted

/-- The strict wrapper retains the same artifact authentication guarantee. -/
theorem prepare_authenticates {program : CheckedProgram} {plan : Plan} {checked : SourceCoreDataCatalog.Checked}
    {limits : Limits} {firstId : Nat} {table : Table}
    (accepted : prepare program plan checked limits firstId = .ok table) : AllAuthenticated plan table.entries :=
  prepareWithProjection_authenticates accepted

/-- A descriptor's selected entry retains the full original origin. -/
theorem descriptor_entry {table : Table} {origin : Origin}
    (descriptor : SourceCoreCallableContracts.Descriptor table origin) :
    ∃ entry, entry ∈ table.entries ∧ entry.origin = origin ∧ entry.id = descriptor.id := by
  have found := descriptor.found
  unfold Table.idAt? at found
  cases selected : table.entries.find? (fun entry => decide (entry.origin = origin)) with
  | none => simp [selected] at found
  | some entry =>
    simp only [selected, Option.map_some, Option.some.injEq] at found
    exact ⟨entry, List.mem_of_find?_eq_some selected,
      of_decide_eq_true (List.find?_some (p := fun candidate : Entry => decide (candidate.origin = origin)) selected), found⟩

end Solcore.SourceSemantics.CoreLowering.CallEntryCertificates
end
