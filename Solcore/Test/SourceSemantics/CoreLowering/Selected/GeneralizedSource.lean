import Solcore.Test.SourceSemantics.CoreLowering.Named.Branches
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.SourceSemantics.StaticValidation
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime

/-!
# Generalized local source tests

The source of generalized local selection, and its typing validation.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalSource
/-! One unchanged original function captures an identity lambda as a generalized
local, then materializes it at Word and Bool in left-to-right order. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function local(flag: Bool) returns (Word, Bool) { let f = lam(value) { return value; }; return (f(11), f(flag)); }"}] }
def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 300000, outputValidationFuel := 1000}

structure WordNode (source : TypedSource) where
  node : ExpressionNode
  literal : Syntax.CoreLiteralValue
  resolution : IntegerLiteralResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .integerLiteral literal resolution
  target : resolution.targetType = .word
  requirements : node.requirements = [resolution.requirement]
  coercions : node.coercions = []

theorem WordNode.evaluates {source : TypedSource} (node : WordNode source)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context node.node.id type) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id
      (.word (Word.ofNatModulo node.resolution.rawValue)) heap := by
  have valid : IntegerLiteralValid context node.literal node.resolution := by
    cases typed with
    | intro contains raw _ _ _ _ =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans node.found)
      rw [node.form] at raw
      cases raw with | integerLiteral valid => exact valid
  have constructs : Dynamic.ResolvedIntegerLiteralConstructs context node.literal node.resolution
      (.word (Word.ofNatModulo node.resolution.rawValue)) := by
    cases valid with
    | word meaning target evidence =>
      generalize resolutionEq : node.resolution = resolution at *
      cases resolution with
      | mk value type requirement =>
        dsimp only at target
        subst type
        exact .word meaning evidence
    | integer _ target _ => rw [node.target] at target; cases target
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]; exact .integerLiteral (by rw [node.requirements,node.coercions]; rfl) constructs
  · rw [node.coercions]; exact .nil

structure CallShape (source : TypedSource) (binder : TypedBinder)
    (argument : ExpressionId) (type : TypeSystem.Ty) where
  callee : Tests.SourceCoreNamedBranch.Read source binder (.function type type)
  node : ExpressionNode
  metadata : IndirectCallResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .call callee.node.id [argument] (.indirect metadata)
  arity : metadata.argumentCount = 1
  argumentCoercions : metadata.argumentCoercions = []
  requirements : node.requirements = []
  coercions : node.coercions = []

structure Shape (source : TypedSource) where
  flag : TypedBinder
  binder : TypedBinder
  parameter : TypedBinder
  typeVariable : TypeSystem.TypeVarId
  initialized : StatementNode
  lambda : ExpressionNode
  identityReturn : StatementNode
  parameterRead : Tests.SourceCoreNamedBranch.Read source parameter (.variable typeVariable)
  literal : WordNode source
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  wordCall : CallShape source binder literal.node.id .word
  boolCall : CallShape source binder flagRead.node.id .bool
  tuple : ExpressionNode
  returned : StatementNode
  inputs : source.inputs = [flag]
  flagScheme : flag.scheme = .mono .bool
  scheme : binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) (.variable typeVariable)⟩
  schemeRequirements : binder.schemeRequirements = []
  parameterScheme : parameter.scheme = .mono (.variable typeVariable)
  parameterRequirements : parameter.schemeRequirements = []
  roots : source.roots = [.statement initialized.id, .statement returned.id]
  initializedFound : source.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl binder (some lambda.id)
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [parameter] (.variable typeVariable) [identityReturn.id]
  lambdaRaw : lambda.rawType = binder.scheme.body
  lambdaType : lambda.type = binder.scheme.body
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  identityFound : source.lookupStatement? identityReturn.id = some identityReturn
  identityForm : identityReturn.form = .returnStmt (some parameterRead.node.id)
  literalValue : literal.resolution.rawValue = 11
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [wordCall.node.id, boolCall.node.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some tuple.id)

def Shape.descriptor {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) : Dynamic.GeneralizedClosure :=
  Dynamic.GeneralizedClosure.ofDirectLambda context source environment shape.binder shape.lambda.id
    [shape.parameter] (.variable shape.typeVariable) [shape.identityReturn.id]

def Shape.allocatedHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨before.cells ++ [{ type := shape.binder.scheme.body, value := none, generalized := some (shape.descriptor context environment) }]⟩

theorem Shape.captures {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) :
    Dynamic.GeneralizedClosureCaptures context source environment shape.binder shape.lambda.id
      (shape.descriptor context environment) :=
  .directLambda (lookupExpression?_sound shape.lambdaFound) shape.lambdaForm
    shape.lambdaRaw shape.lambdaType shape.lambdaRequirements shape.lambdaCoercions

/-- The original let copies its environment once and stores one principal
descriptor over the copies. It performs no lambda body call and selects
neither the Word nor Bool instance at allocation. -/
theorem Shape.initializes {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context nextContext : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) {environment captured : Dynamic.Environment}
    {before middle : Dynamic.Heap}
    (snapshot : Dynamic.EnvironmentCopies source environment before captured middle)
    (extended : BinderExtends source.owner context shape.binder nextContext) :
    Dynamic.StatementExecutes program context evidence source environment before shape.initialized.id
      nextContext (.fallthrough ((shape.binder.id, ⟨middle.cells.length⟩) :: environment))
      (shape.allocatedHeap context captured middle) := by
  apply Dynamic.StatementExecutes.letInitializedGeneralized
    (lookupStatement?_sound shape.initializedFound) shape.initializedForm snapshot
    (shape.captures context captured) (by rw [shape.scheme]; simp) extended
  exact .append

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalTypingValidation
/-! Proof-producing observations for the original generalized-local fixture.
Every accepted fact is checked against its complete source and lexical context;
native execution is not an input to these declarative typing proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation
open Solcore Core Frontend SourceInference SourceSemantics

def observe (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if proof : p then pure ⟨proof⟩ else throw (IO.userError message)

def admissible (context : SourceSemantics.Context) (type : TypeSystem.Ty) :
    IO (PLift (TypeAdmissible context type)) := do
  match accepted : validateTypeAdmissible context type with
  | .error _ => throw (IO.userError "generalized source type formation")
  | .ok () => return ⟨validateTypeAdmissible_success accepted⟩

def scheme (context : SourceSemantics.Context) (value : TypeSystem.Scheme) :
    IO (PLift (SchemeWellFormed context value)) := do
  match accepted : validateSchemeWellFormed context value with
  | .error _ => throw (IO.userError "generalized source scheme formation")
  | .ok () => return ⟨validateSchemeWellFormed_success accepted⟩

def generalizes (context : SourceSemantics.Context) (binder : TypedBinder) :
    IO (PLift (SchemeGeneralizesExcept context (localSchemeTemplateIds binder) binder.scheme)) := do
  match accepted : validateSchemeGeneralizesExcept context (localSchemeTemplateIds binder) binder.scheme with
  | .error _ => throw (IO.userError "generalized source exact generalization")
  | .ok () => return ⟨validateSchemeGeneralizesExcept_success accepted⟩

def binder (context : SourceSemantics.Context) (owner : Resolved.DeclarationId) (value : TypedBinder) :
    IO (PLift (BinderExtends owner context value
      (context.withLocal value.id value.scheme value.schemeRequirements))) := do
  let ⟨owned⟩ ← observe (value.id.owner = owner) "generalized source binder owner"
  let ⟨formed⟩ ← scheme context value.scheme
  let ⟨fresh⟩ ← observe (value.id ∉ context.locals.map Prod.fst ∧
    value.id ∉ context.localSchemeRequirements.map Prod.fst) "generalized source binder freshness"
  let ⟨quantifiers⟩ ← observe (value.scheme.quantified.all (fun metavariable =>
    decide (metavariable ∉ context.typeVariables) && context.locals.all (fun entry =>
      decide (metavariable ∉ entry.2.quantified))) = true) "generalized source quantifier freshness"
  let ⟨empty⟩ ← observe (value.scheme.quantified = [] → value.schemeRequirements = [])
    "generalized source monomorphic requirements"
  have isolated : SchemeQuantifiersFresh context value.scheme := by
    intro metavariable member
    have selected := List.all_eq_true.mp quantifiers metavariable member
    simp only [Bool.and_eq_true] at selected
    exact ⟨of_decide_eq_true selected.1, fun entry found =>
      of_decide_eq_true (List.all_eq_true.mp selected.2 entry found)⟩
  return ⟨.intro ⟨owned, formed, isolated, empty⟩ fresh⟩

def range (context : SourceSemantics.Context) : (substitution : TypeSystem.Substitution) →
    IO (PLift (SubstitutionRangeAdmissible context substitution))
  | [] => pure ⟨by intro metavariable replacement member; cases member⟩
  | (metavariable, replacement) :: rest => do
    let ⟨head⟩ ← admissible context replacement
    let ⟨tail⟩ ← range context rest
    return ⟨by
      intro other value member
      obtain same | member := List.mem_cons.mp member
      · cases same; exact head
      · exact tail other value member⟩

def read {source : TypedSource} {value : TypedBinder} {type : TypeSystem.Ty}
    (node : Tests.SourceCoreNamedBranch.Read source value type) (context : SourceSemantics.Context)
    (lookup : context.LocalLookup value.id value.scheme)
    (requirements : context.LocalSchemeRequirementsLookup value.id value.schemeRequirements) :
    IO (PLift (ExpressionHasType source context node.node.id type)) := do
  let ⟨empty⟩ ← observe (value.schemeRequirements = []) "generalized unqualified read"
  let ⟨formed⟩ ← scheme context value.scheme
  let ⟨typeFormed⟩ ← admissible context type
  let some matched := value.scheme.matchInstanceCertificate? type
    | throw (IO.userError "generalized exact local instance")
  let ⟨replacements⟩ ← range context matched.substitution
  have instanceValid : LocalSchemeInstantiationValid context value type [] :=
    .intro (LocalSchemeRequirementsWellFormed.empty _ _ empty) formed matched.substitution
      ⟨matched.quantifiedUnique, matched.domainExact ▸ List.Perm.refl _⟩ replacements matched.applies
      (by simp) (by intro id member; cases member)
      (by rw [instantiateLocalSchemePredicates, empty]; exact .nil)
  have typed : ExpressionHasType source context node.node.id node.node.type := by
    refine .intro (lookupExpression?_sound node.found)
      (node.form ▸ ExpressionFormHasRawType.reference (.local lookup requirements instanceValid))
      node.raw typeFormed (node.type.symm ▸ typeFormed) ?_
    rw [node.requirements, node.coercions, node.type]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  return ⟨Eq.mp (congrArg (fun target => ExpressionHasType source context node.node.id target) node.type) typed⟩

def uncoerced {source : TypedSource} (context : SourceSemantics.Context)
    (node : ExpressionNode) (type : TypeSystem.Ty)
    (found : source.lookupExpression? node.id = some node)
    (form : ExpressionFormHasRawType source context node.form type (.ordinary [])) :
    IO (PLift (ExpressionHasType source context node.id type)) := do
  let ⟨raw⟩ ← observe (node.rawType = type) "generalized source raw type"
  let ⟨result⟩ ← observe (node.type = type) "generalized source result type"
  let ⟨requirements⟩ ← observe (node.requirements = []) "generalized source empty requirements"
  let ⟨coercions⟩ ← observe (node.coercions = []) "generalized source empty coercions"
  let ⟨formed⟩ ← admissible context type
  have typed : ExpressionHasType source context node.id node.type := by
    refine .intro (lookupExpression?_sound found) form raw formed (result.symm ▸ formed) ?_
    rw [requirements, coercions, result]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  return ⟨by simpa only [result] using typed⟩

def call {source : TypedSource} {binder : TypedBinder} {argument : ExpressionId} {type : TypeSystem.Ty}
    (shape : CallShape source binder argument type) (context : SourceSemantics.Context)
    (callee : ExpressionHasType source context shape.callee.node.id (.function type type))
    (argumentTyped : ExpressionHasType source context argument type) :
    IO (PLift (ExpressionHasType source context shape.node.id type)) := do
  let ⟨before⟩ ← observe (shape.metadata.argumentTypeBeforeCoercion = type) "generalized call argument before"
  let ⟨after⟩ ← observe (shape.metadata.argumentTypeAfterCoercion = type) "generalized call argument after"
  let ⟨raw⟩ ← observe (shape.node.rawType = type) "generalized call raw type"
  let ⟨result⟩ ← observe (shape.node.type = type) "generalized call result type"
  let ⟨formed⟩ ← admissible context type
  have application : IndirectApplicationValid context shape.metadata [type] type := by
    refine .intro shape.arity before after ?_
    rw [before, shape.argumentCoercions]
    exact .nil _
  have typed : ExpressionHasType source context shape.node.id shape.node.type := by
    refine .intro (lookupExpression?_sound shape.found)
      (shape.form ▸ ExpressionFormHasRawType.indirectCall callee (.cons argumentTyped (.nil _)) application)
      raw formed (result.symm ▸ formed) ?_
    rw [shape.requirements, shape.coercions, shape.argumentCoercions, result]
    exact .indirectCall (by intro step member; cases member) (.nil _) rfl
  return ⟨by simpa only [result] using typed⟩

private theorem builtin_word (context : SourceSemantics.Context) :
    RetainedEvidenceValid context.assumptions context.signatures.resolutionRules
      (ProgramSignatures.builtinIntPredicate .word)
      (.implementation (.byImpl (ProgramSignatures.builtinIntPredicate .word) (.builtin .intWord) [])) := by
  apply RetainedEvidenceValid.intro (.implementation (.byImpl .nil))
  exact .implementation (rule := ProgramSignatures.builtinIntWordRule)
    (by simp [ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]) rfl
    (.intro ⟨[], []⟩ ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩ rfl rfl) .nil

def word {source : TypedSource} (shape : WordNode source) (context : SourceSemantics.Context) :
    IO (PLift (ExpressionHasType source context shape.node.id .word)) := do
  match accepted : SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements
      shape.node shape.literal shape.resolution with
  | .error _ => throw (IO.userError "generalized original Word evidence")
  | .ok validated =>
    let ⟨formed⟩ ← admissible context .word
    let ⟨raw⟩ ← observe (shape.node.rawType = .word) "generalized original Word raw type"
    have metadata := SourceCoreElaboration.validateWordIntegerLiteral_sound accepted
    have proves : RequirementProves context shape.resolution.requirement
        (ProgramSignatures.builtinIntPredicate shape.resolution.targetType) := by
      obtain ⟨row, selected, predicate, evidence⟩ := CoreLowering.NumericLiteralEvidenceReceipts.word accepted
      have member : row ∈ context.solvedRequirements.filter (fun row => decide (row.id = shape.resolution.requirement)) := by
        rw [selected]; simp
      obtain ⟨member, identity⟩ := List.mem_filter.mp member
      refine ⟨row, ⟨member, of_decide_eq_true identity⟩, predicate, .intro ?_⟩
      rw [evidence, predicate]
      simpa only [IntegerLiteralResolution.predicate, metadata.targetType] using builtin_word context
    have valid : IntegerLiteralValid context shape.literal shape.resolution :=
      .word metadata.meaning metadata.targetType proves
    have typed : ExpressionHasType source context shape.node.id shape.node.type := by
      refine .intro (lookupExpression?_sound shape.found)
        (shape.form ▸ ExpressionFormHasRawType.integerLiteral valid)
        (raw.trans metadata.targetType.symm) (metadata.targetType.symm ▸ formed)
        (metadata.nodeType.symm ▸ formed) ?_
      rw [metadata.requirements, metadata.coercions, metadata.targetType, metadata.nodeType]
      exact .ordinary (by intro id member; exact List.mem_singleton.mp member ▸ valid.requirement_valid) (.nil _) rfl
    return ⟨by simpa only [metadata.nodeType] using typed⟩

end Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation
end
