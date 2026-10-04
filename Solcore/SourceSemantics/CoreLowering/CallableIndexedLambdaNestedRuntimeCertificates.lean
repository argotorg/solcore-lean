import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewNamedRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads

/-! Literal lambda leaves retain their actual Code and a smaller static body.
The compiler view is observed by a full node lookup; the accepted body and its
original view remain inside the receipt. Named calls impose no rank decrease.
Transport changes only reached node and child certificates, preserving every
ordered child, same dictionary and emitted code. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeCertificates
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaViewEdits CallableLambdaBodyReachability
open RecursiveNamedCatalog RecursiveNamedLambdaFormationHeads
variable {values : SourceCoreCompatibleValues.Context} {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
  {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {compilation : SourceCoreFunctions.Context} {source view : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}

abbrev RankedSupport := Nat → CallableIndexedLambdaRuntimeValues.SupportFamily indexed

/-- The source index is an actual node observation, not equality of the entire
view with the closure source. Code already retains its original body callback. -/
structure Lambda (support : RankedSupport (indexed := indexed)) (rank : Nat)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (source : TypedSource) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  code : Code indexed (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
    scope (nativePrefix caller)
  childRank : Nat
  smaller : childRank < rank
  body : support childRank code
  compilation : code.compilation = CallableIndexedNamedGeneration.context indexed caller.named
  active : code.active = []
  identifier : code.id = id
  emitted : code.lowered = lowered
  found : source.lookupExpression? id = some code.sourceNode
  sourceType : code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
  nativeType : lowered.type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore
  requirements : code.sourceNode.requirements = []
  coercions : code.sourceNode.coercions = []

theorem Lambda.of_site {support : RankedSupport (indexed := indexed)} {rank childRank : Nat}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {scope : SourceCoreLocalCell.Scope}
    (site : CallableIndexedLambdaGeneration.Site indexed caller.named parameters result statements
      context evidence [] scope (nativePrefix caller))
    (smaller : childRank < rank) (body : support childRank site.code)
    (found : source.lookupExpression? site.code.id = some site.code.sourceNode)
    (sourceType : site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence []))
    (requirements : site.code.sourceNode.requirements = []) (coercions : site.code.sourceNode.coercions = []) :
    Nonempty (Lambda support rank caller source context evidence scope site.code.id site.code.lowered) :=
  ⟨{parameters := parameters, result := result, statements := statements, code := site.code,
    childRank := childRank, smaller := smaller, body := body, compilation := site.compilation,
    active := site.active, identifier := rfl, emitted := rfl, found := found, sourceType := sourceType,
    nativeType := site_native_type site, requirements := requirements, coercions := coercions}⟩

inductive Head (support : RankedSupport (indexed := indexed)) (rank : Nat)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | existing {scope id lowered}
      (head : CallableLambdaViewNamedRuntimeCertificates.Head (ambient := CallableIndexedAmbient.ambientDefinitions indexed)
        headers compilation source context evidence children scope id lowered) :
      Head support rank caller headers compilation source context evidence children scope id lowered
  | lambda {scope id lowered}
      (head : Lambda support rank caller source context evidence scope id lowered) :
      Head support rank caller headers compilation source context evidence children scope id lowered

abbrev Certificates (support : RankedSupport (indexed := indexed)) (rank : Nat)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :=
  RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
    (Head support rank caller headers compilation source context evidence) fuel values source context solved reasonAt

/-- Lexical syntax is only an actual full node receipt; the concrete Tree
separately supplies every supported expression and nested literal body. -/
def Nodes (source : TypedSource) (id : ExpressionId) : Prop :=
  ∃ node, source.lookupExpression? id = some node

structure BodyReceipt (support : RankedSupport (indexed := indexed)) (rank : Nat)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code indexed function scope administrative)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  source : function.source = CallableIndexedNamedGeneration.source caller.named
  compilation : code.compilation = CallableIndexedNamedGeneration.context indexed caller.named
  active : code.active = []
  administrative : administrative = nativePrefix caller
  body : CallableIndexedLambdaStaticBodySupport.BodyWith Nodes
    (fun fuel source context => Certificates support rank caller headers code.compilation fuel source context
      function.evidence code.compilation.solvedRequirements code.reasonAt)
    code program registry faults

/-- The recursion orders only static nested literals. Named calls in each body
retain the complete existing family and do not contain a rank condition. -/
def BodyAt
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (rank : Nat) : CallableIndexedLambdaRuntimeValues.SupportFamily indexed :=
  fun {_ _ _} code => BodyReceipt
    (fun childRank {_ _ _} childCode =>
      if _smaller : childRank < rank then BodyAt headers caller registry faults childRank childCode else Empty)
    rank caller headers code registry faults
termination_by rank


def BodyAt.receipt {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code indexed function scope administrative} {rank : Nat}
    (body : BodyAt headers caller registry faults rank code) :
    BodyReceipt (fun childRank {_ _ _} childCode => if _smaller : childRank < rank then
      BodyAt headers caller registry faults childRank childCode else Empty)
      rank caller headers code registry faults := by
  rw [BodyAt] at body
  exact body

def BodyAt.recapture {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code indexed function scope administrative} {rank : Nat}
    (body : BodyAt headers caller registry faults rank code) (environment : Dynamic.Environment) :
    BodyAt headers caller registry faults rank (recaptureCode code environment) := by
  rw [BodyAt]
  have actual := body.receipt
  exact {
    source := actual.source
    compilation := actual.compilation
    active := actual.active
    administrative := actual.administrative
    body := recaptureBodyWith code actual.body environment }

/-- The existential rank is stored in the same Code's static support. -/
abbrev Support (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    CallableIndexedLambdaRuntimeValues.SupportFamily indexed :=
  fun {_ _ _} code => Σ caller : Header indexed.ancestry values indexed.layouts.definitions program,
    Σ rank : Nat, BodyAt headers caller registry faults rank code

/-- Captured globals and the full actual carried source metadata are separate
from call-time catalog authority. Both remain unchanged under heap extension. -/
def Condition
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (locations : Locations (prepared := indexed.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)) :
    CallableIndexedLambdaRuntimeValues.SupportCondition indexed (Support headers registry faults) :=
  fun {_ _ _ scope _} captured _ history body =>
    history.metadata = CallableIndexedNamedGeneration.state body.1.named ∧ ∃ location,
      CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 scope captured.canonical location

theorem condition_stable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
    (captured : Captures indexed mapping world scope function.captured actual)
    (code : Code indexed function scope captured.administrative) (history : History code)
    (body : Support headers registry faults code)
    {locations : Locations (prepared := indexed.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)}
    (supported : Condition (registry := registry) (faults := faults) headers locations captured code history body)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Condition (registry := registry) (faults := faults) headers locations (captured.extend maps worlds) code history body := supported

def model
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (locations : Locations (prepared := indexed.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : values.checked.catalog.callableContracts = true) :
    FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions indexed) :=
  CallableIndexedLambdaRuntimeValues.modelWith indexed (Support headers registry faults)
    (Condition headers locations) (condition_stable (headers := headers) (locations := locations)
      (registry := registry) (faults := faults)) profile


section View
variable {support : RankedSupport (indexed := indexed)} {rank : Nat}
  {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)

def Lambda.transport {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Lambda support rank caller source context evidence scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    Lambda support rank caller view context evidence scope id lowered :=
  {head with found := (expression_lookup edited avoids reached).symm.trans head.found}

theorem found {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Head support rank caller headers compilation source context evidence children scope id lowered) :
    ∃ node, source.lookupExpression? id = some node := by
  cases head with
  | existing head => exact CallableLambdaViewNamedRuntimeCertificates.canonical_call_found head
  | lambda head => exact ⟨_, head.found⟩

include edited avoids in
theorem transport {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificates support rank caller headers compilation fuel source context evidence solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    Certificates support rank caller headers compilation fuel view context evidence solved reasonAt scope id lowered := by
  exact CallableLambdaViewNamedRuntimeCertificates.transport_generic
    (target := Head support rank caller headers compilation view context evidence) edited avoids
    (fun head => found head)
    (fun found head reached children => by
      cases head with
      | lambda leaf => exact .lambda (leaf.transport edited avoids reached)
      | existing head =>
        cases head with
        | ordinary receipt =>
          have same := Option.some.inj (found.symm.trans receipt.metadata.found)
          cases same
          exact .existing (.ordinary (CallableLambdaViewNamedRuntimeCertificates.ordinary_transport edited avoids receipt reached children))
        | authenticated receipt => exact .existing (CallableLambdaViewNamedRuntimeCertificates.call_transport edited avoids found receipt reached children))
    receipt reached

end View
end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeCertificates
