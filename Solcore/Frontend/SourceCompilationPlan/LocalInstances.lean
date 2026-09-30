import Solcore.Frontend.SourceCompilationPlan.Types

/-!
# Local lambda instances for compilation

This catalog exposes existing worklist contexts without evaluating typed
source. It retains source identities and metadata for later Core generation;
it does not allocate closures or cells, resolve evidence, or certify lowering.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCompilationPlan

open SourceInference TypeSystem

/-- A local instance belongs to one enclosing declaration specialization.
Rigid declaration parameters and cumulative flexible local substitutions are
kept separately. `source` retains all original reference/use metadata, while
`bodyNodes` selects this lambda's direct lexical body before local substitution.
The solved requirements are the caller's unchanged ledger, not newly resolved
evidence for this local instance. -/
structure LocalLambdaCatalogEntry where
  caller : SourceSpecialization.SpecializationKey
  parameterSubstitution : ParameterSubstitution
  localInstance : SourceSpecializationWorklist.LocalLambdaInstance
  source : TypedSource
  bodyNodes : List Node
  solvedRequirements : List SolvedRequirement
  deriving Repr, BEq

namespace LocalLambdaCatalogEntry

def initializer (entry : LocalLambdaCatalogEntry) : ExpressionId :=
  entry.localInstance.binding.initializer

def binder (entry : LocalLambdaCatalogEntry) : TypedBinder :=
  entry.localInstance.binding.binder

def substitution (entry : LocalLambdaCatalogEntry) : Substitution :=
  entry.localInstance.substitution

/-- Apply the exact worklist context to body metadata. Quantified nested
binders retain their own schemes under the existing scoped substitution. -/
def instantiatedBodyNodes (entry : LocalLambdaCatalogEntry) : List Node :=
  entry.bodyNodes.map (Node.applySubstitution entry.substitution)

end LocalLambdaCatalogEntry

/-- Enumerate plan specializations in their retained order, then local
instances in the worklist's FIFO discovery order. Repeated use sites share one
binding/substitution entry. Different cumulative contexts remain distinct,
even when they produce the same local function type.

This accepts an already prepared plan and checks duplicate keys and the
worklist's local-context policy. It does not replace canonical plan or evidence
validation. A diagnostic fuel override is passed directly to the same bounded
compile-time closure used by the worklist. -/
def localLambdaCatalog (plan : SourceSpecializationWorklist.Plan)
    (contextFuel : Option Nat := none) :
    Except SourceSpecializationWorklist.Error (List LocalLambdaCatalogEntry) := do
  SourceSpecializationWorklist.validatePlanSpecializationsUnique plan
  let mut entries := []
  for specialized in plan.specializations do
    let source := specialized.function.typedBody
    let instances ← SourceSpecializationWorklist.localLambdaInstances source contextFuel
    for localInstance in instances do
      let bodyNodes ← SourceSpecializationWorklist.localLambdaBodyNodes source localInstance
      entries := entries ++ [{
        caller := specialized.key
        parameterSubstitution := specialized.parameterSubstitution
        localInstance
        source
        bodyNodes
        solvedRequirements := specialized.function.solvedRequirements
      }]
  pure entries

end Solcore.Frontend.SourceCompilationPlan
