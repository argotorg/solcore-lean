import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding
import Solcore.SourceSemantics.CoreLowering.GenericForHeaderContinuationMap
import Solcore.SourceSemantics.CoreLowering.ProtectedForGenericEndpoint
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeControl
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogGoals
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderReady

/-! Ready catalog positions retain the actual statement post. An initializer
keeps the original ordered header Tree and requires genuine pending loop facts
before its actual loop continuation. Source and native grades stay independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedImperativeFor (Position)
open TypedLexicalWhile (Scope ValuesContext)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} (validity : SourceSemantics.Context → Prop) (budget : Nat)

abbrev PreservingHeaderWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  initializerFacts context items condition post statements expected →
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => loopFacts context condition post statements expected ∧ AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor protocol readiness conditionGate (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev ReflectingHeaderWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  initializerFacts context items condition post statements expected →
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => loopFacts context condition post statements expected ∧ AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor protocol readiness conditionGate (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev PreservesAtWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => AtMost budget (fun size => Control.Stateful.WithReady.PreservesAtWith protocol readiness conditionGate facts (validity := validity) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => PreservingHeaderWith protocol readiness conditionGate loopFacts initializerFacts (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Below budget (fun size => Control.Stateful.WithReady.ReflectsAtWith protocol readiness conditionGate facts (validity := validity) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => ReflectingHeaderWith protocol readiness conditionGate loopFacts initializerFacts (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Stateful.WithReady

/-! Pointwise assignment prefixes keep the real seven-slot continuation and
its exact successful or fault state. Source facts stay independent of native
projection; high producers establish them from the actual parent statement. -/
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady.Assignment
abbrev ResultAt := @ProtectedForHeader.Stateful.WithReady.AssignmentResultAt
abbrev AssignmentPrefixPreservesAt := @ProtectedForHeader.Stateful.WithReady.AssignmentPrefixPreservesAt
abbrev AssignmentFaultPreservesAt := @ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesAt
abbrev AssignmentReflectsAt := @ProtectedForHeader.Stateful.WithReady.AssignmentReflectsAt
end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady.Assignment

namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateTransition
universe u v

/-- Authentic initializer facts follow the original static item contexts.
The done field supplies the pending loop facts at the actual nil site. -/
structure InitializerSites
    (initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
    (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
    (source : TypedSource) : Prop where
  done : ∀ {context condition post statements expected},
    initializerFacts context [] condition post statements expected → loopFacts context condition post statements expected
  absent : ∀ {context next binder rest condition post statements expected},
    initializerFacts context (.letDecl binder none :: rest) condition post statements expected →
    BinderExtends source.owner context binder next →
    initializerFacts next rest condition post statements expected
  initialized : ∀ {context next binder expression rest condition post statements expected},
    initializerFacts context (.letDecl binder (some expression) :: rest) condition post statements expected →
    BinderExtends source.owner context binder next →
    initializerFacts next rest condition post statements expected
  discard : ∀ {context expression rest condition post statements expected},
    initializerFacts context (.expression expression :: rest) condition post statements expected →
    initializerFacts context rest condition post statements expected
  assignment : ∀ {context resolution operator rhs rest condition post statements expected},
    initializerFacts context (.assignValue resolution operator rhs :: rest) condition post statements expected →
    initializerFacts context rest condition post statements expected
  snapshot : ∀ {context resolution rest condition post statements expected},
    initializerFacts context (.assignBitNot resolution :: rest) condition post statements expected →
    initializerFacts context rest condition post statements expected

/-- The exact Source assignment and snapshot site are projected from the
actual typed parent, independently of its compiler/native representation. -/
structure AssignmentSites
    (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
    (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
    (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
    (source : TypedSource) : Prop where
  assignment : ∀ {context id expected node resolution operator rhs}, headFacts context id expected →
    source.lookupStatement? id = some node → node.form = .assignValue resolution operator rhs →
    assignmentFacts context resolution operator rhs
  snapshot : ∀ {context id expected node resolution}, headFacts context id expected →
    source.lookupStatement? id = some node → node.form = .assignBitNot resolution →
    snapshotFacts context resolution

/-- Successful bit-not transfer uses the real Source snapshot update and the
actual written state. Fault rows use the shared actual administrative rule. -/
abbrev SnapshotTransfers := @ProtectedForHeader.Stateful.WithReady.SnapshotTransfers

namespace Lexical
variable {Records : Type v} (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  {values : TypedLexicalWhile.ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {administrative : Core.Context}
  {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {size : Nat}

theorem preserves (validity : SourceSemantics.Context → Prop)
    (meaning : PreservesAtFor protocol readiness condition facts functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (scope := scope) mode statements expected type code) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness condition facts
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope) mode statements expected type code := by
  intro valid static mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped initial gate ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ :=
    meaning valid static environments heaps locals agrees typed reference read unmapped initial gate ready trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, TypedLexicalWhile.FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, frame, metadata, lexical, post⟩

theorem reflects (validity : SourceSemantics.Context → Prop)
    (meaning : ReflectsAtFor protocol readiness condition facts functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (scope := scope) mode statements expected type code) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness condition facts
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope) mode statements expected type code := by
  intro valid static mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial gate ready evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ :=
    meaning valid static environments heaps locals agrees typed reference read unmapped initial gate ready evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, TypedLexicalWhile.FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, frame, metadata, lexical, post⟩
end Lexical
end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady


namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Position)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateTransition
universe u v
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The three catalog-specific heads retain their authentic compiler receipts
and only their recursive child goals. A recipe contains no completed head or
body execution proof. The Source parent facts and actual input state are
consumed separately by its pointwise producer. -/
inductive HeadRecipe (goal : SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop) :
    SourceSemantics.Context → Scope → StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | whileLoop {context scope id node condition conditionNode statements expected type conditionCode loopCode selfReason}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
        context scope (.statements false statements) expected type loopCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) ambient.definitions)
      (child : goal context scope (.statements false statements) expected type loopCode) :
      HeadRecipe goal context scope id expected type (LocalLoop.whileLoop type conditionCode loopCode selfReason)
  | forLoop {context scope id node initializer condition post statements expected type initialCode}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initializer condition post statements)
      (child : goal context scope (.initializers initializer condition post statements) expected type initialCode) :
      HeadRecipe goal context scope id expected type initialCode
  | matchWith {context scope id node resolution scrutineeNode expected type matched selfReason control caseFacts}
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
      (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
      (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
      (compilation : SourceCoreCompatibleDataMatches.Context)
      (sameValues : compilation.values = values) (sameDefinitions : compilation.definitions = ambient.definitions)
      (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError)))
      (requests : List GenericMatchChildren.Request)
      (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched)
      (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
      (children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code)
      (catalog : SignatureCatalogWellFormed values.checked.signatures)
      (patternContext : GenericImperativeMatch.Tree.MatchContextFields compilation context)
      (child : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        goal childContext request.scope (.statements false request.statements) expected type request.code) :
      HeadRecipe goal context scope id expected type matched

/-- A completed initializer keeps the original condition, body, and ordered
post-header compiler receipts. Its body premise is the strict recursive goal;
the pending loop Source facts are supplied at its actual normalized context. -/
inductive LoopRecipe (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (goal : SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop) :
    SourceSemantics.Context → Scope → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | mk {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
        context scope (.statements false statements) expected type bodyCode)
      (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
      (postErrors : GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults postTree)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
      (child : goal context scope (.statements false statements) expected type bodyCode) :
      LoopRecipe diagnosticPolicy goal context scope condition post statements expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason)
end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady


namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Position)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} (validity : SourceSemantics.Context → Prop) (budget : Nat)
  (goal : SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop)

def PreservingHeads : Prop :=
  ∀ {context scope id expected type code},
    HeadRecipe (administrative := administrative) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) goal context scope id expected type code →
    AtMost budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadPreservesAtWith protocol readiness conditionGate headFacts
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals)
      size (scope := scope) id expected type code)

def ReflectingHeads : Prop :=
  ∀ {context scope id expected type code},
    HeadRecipe (administrative := administrative) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) goal context scope id expected type code →
    Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadReflectsAtWith protocol readiness conditionGate headFacts
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals)
      size (scope := scope) id expected type code)

def PreservingLoops (diagnosticPolicy : AssignmentDiagnosticPolicy) : Prop :=
  ∀ {context scope condition post statements expected type code},
    LoopRecipe (administrative := administrative) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults)
      diagnosticPolicy goal context scope condition post statements expected type code →
    loopFacts context condition post statements expected →
    AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor protocol readiness conditionGate (validity := validity)
      functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals)
      size (scope := scope) condition post statements expected type code)

def ReflectingLoops (diagnosticPolicy : AssignmentDiagnosticPolicy) : Prop :=
  ∀ {context scope condition post statements expected type code},
    LoopRecipe (administrative := administrative) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults)
      diagnosticPolicy goal context scope condition post statements expected type code →
    loopFacts context condition post statements expected →
    AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor protocol readiness conditionGate (validity := validity)
      functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals)
      size (scope := scope) condition post statements expected type code)
end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady


namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope}
  {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

theorem loop_preserves_of_true (meaning : ProtectedFor.Body.Stateful.LoopPreservesAtFor protocol conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code) :
    ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor protocol (Readiness.trivial protocol) conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees typed reference read unmapped initial guarded _ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial guarded trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, Reached.of_trivial reached⟩

theorem loop_preserves_forget_true (meaning : ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor protocol (Readiness.trivial protocol) conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code) :
    ProtectedFor.Body.Stateful.LoopPreservesAtFor protocol conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees typed reference read unmapped initial guarded trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial guarded True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached.forget⟩

theorem loop_reflects_of_true (meaning : ProtectedFor.Body.Stateful.LoopReflectsAtFor protocol conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code) :
    ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor protocol (Readiness.trivial protocol) conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial guarded _ready evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial guarded evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, Reached.of_trivial reached⟩

theorem loop_reflects_forget_true (meaning : ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor protocol (Readiness.trivial protocol) conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code) :
    ProtectedFor.Body.Stateful.LoopReflectsAtFor protocol conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial guarded evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial guarded True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached.forget⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady

namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Position)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} {validity : SourceSemantics.Context → Prop} {budget : Nat}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {context : SourceSemantics.Context} {scope : Scope}
  {position : Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

theorem preserves_goal_forget_true (meaning : RecursiveNamedImperativeFor.Stateful.WithReady.PreservesAtWith protocol (Readiness.trivial protocol) conditionGate
      (fun _ _ _ _ => True) (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget context scope position expected type code) :
    RecursiveNamedImperativeFor.Stateful.PreservesAtWith protocol conditionGate
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget context scope position expected type code := by
  cases position with
  | statements mode statements =>
    intro size within
    exact RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith.forget_true (protocol := protocol) (condition := conditionGate)
      (functions := functions) (program := program) (evidence := evidence) (meaning size within)
  | initializers items condition post statements =>
    obtain ⟨tree, errors⟩ := meaning True.intro
    let convert := fun {nextContext nextScope nextCode} (certificate : True ∧ RecursiveNamedHeaderContracts.AtMost budget
      (fun size => ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor protocol (Readiness.trivial protocol) conditionGate
        (validity := validity) functions program evidence size (source := source) (context := nextContext)
        (scope := nextScope) (registry := registry) (faults := faults) (frameLayout := frame)
        (globals := globals) (administrative := administrative) condition post statements expected type nextCode)) =>
      fun size within => loop_preserves_forget_true (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (program := program) (evidence := evidence)
        (certificate.2 size within)
    exact ⟨tree.mapContinuation convert, errors.mapContinuation convert⟩

theorem reflects_goal_forget_true (meaning : RecursiveNamedImperativeFor.Stateful.WithReady.ReflectsAtWith protocol (Readiness.trivial protocol) conditionGate
      (fun _ _ _ _ => True) (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget context scope position expected type code) :
    RecursiveNamedImperativeFor.Stateful.ReflectsAtWith protocol conditionGate
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget context scope position expected type code := by
  cases position with
  | statements mode statements =>
    intro size within
    exact RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith.forget_true (protocol := protocol) (condition := conditionGate)
      (functions := functions) (program := program) (evidence := evidence) (meaning size within)
  | initializers items condition post statements =>
    obtain ⟨tree, errors⟩ := meaning True.intro
    let convert := fun {nextContext nextScope nextCode} (certificate : True ∧ RecursiveNamedHeaderContracts.AtMost budget
      (fun size => ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor protocol (Readiness.trivial protocol) conditionGate
        (validity := validity) functions program evidence size (source := source) (context := nextContext)
        (scope := nextScope) (registry := registry) (faults := faults) (frameLayout := frame)
        (globals := globals) (administrative := administrative) condition post statements expected type nextCode)) =>
      fun size within => loop_reflects_forget_true (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (program := program) (evidence := evidence)
        (certificate.2 size within)
    exact ⟨tree.mapContinuation convert, errors.mapContinuation convert⟩

theorem InitializerSites.trivial (source : TypedSource) :
    InitializerSites (fun _ _ _ _ _ _ => True) (fun _ _ _ _ _ => True) source :=
  ⟨fun _ => True.intro, fun _ _ => True.intro, fun _ _ => True.intro,
    fun _ => True.intro, fun _ => True.intro, fun _ => True.intro⟩

theorem AssignmentSites.trivial (source : TypedSource) :
    AssignmentSites (fun _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ => True) source :=
  ⟨fun _ _ _ => True.intro, fun _ _ _ => True.intro⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
