import Solcore.SourceSemantics.CoreLowering.CallableCoercionBodyProvenance

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationSpecializationBinders
open Frontend SourceInference TypeSystem

private def instructionBinders : MatchPatternInstruction → List TypedBinder
  | .binder binder => [binder]
  | _ => []

private def patternBinders : MatchPatternResolution → List TypedBinder
  | .binder binder => [binder]
  | .constructor _ instructions | .tuple instructions => instructions.flatMap instructionBinders
  | _ => []

private def allowed (source : TypedSource) (binder : TypedBinder)
    (initializer : Option ExpressionId) : Bool :=
  !binder.scheme.quantified.isEmpty && initializer.any (SourceSpecialization.isDirectLambdaInitializer source)

private def rejectedBinders (source : TypedSource) : Node → List TypedBinder
  | .expression node => match node.form with
    | .lambda parameters _ _ => parameters.filter fun binder => !binder.scheme.quantified.isEmpty
    | _ => []
  | .statement node => match node.form with
    | .letDecl binder initializer =>
      if binder.scheme.quantified.isEmpty || allowed source binder initializer then [] else [binder]
    | .forLoop initializer _ post _ => (initializer ++ post).filterMap fun
      | .letDecl binder _ => if binder.scheme.quantified.isEmpty then none else some binder
      | _ => none
    | .matchWith resolution => resolution.cases.flatMap fun arm =>
      (patternBinders arm.pattern.resolution).filter fun binder => !binder.scheme.quantified.isEmpty
    | _ => []

private def positionCheck (source : TypedSource) : Except SourceSpecialization.Error Unit :=
  match ((source.inputs.filter fun binder => !binder.scheme.quantified.isEmpty) ++
      source.nodes.flatMap (rejectedBinders source)).head? with
  | some binder => .error (.polymorphicBinder binder.id binder.scheme.quantified)
  | none => .ok ()

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) : action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

private theorem positions_of_specialization {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    positionCheck specialized.function.typedBody = .ok () := by
  unfold SourceSpecialization.specializeFunction at accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, residuals, accepted⟩ := bind_ok accepted
  obtain ⟨position, positions, _⟩ := bind_ok residuals
  change positionCheck (SourceSpecialization.applyCheckedFunction canonical generic).typedBody = .ok position at positions
  cases position
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction (SourceSpecialization.applyCheckedFunction canonical generic) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
    simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
    subst specialized
    exact positions

private theorem no_rejected {source : TypedSource} (accepted : positionCheck source = .ok ()) :
    source.nodes.flatMap (rejectedBinders source) = [] := by
  unfold positionCheck at accepted
  split at accepted
  next binder found => cases accepted
  next absent =>
    have empty := List.head?_eq_none_iff.mp absent
    exact (List.append_eq_nil_iff.mp empty).2

/-- The successful original specialization checks every stored let, including
statements after a return. A quantified binder must name a direct lambda. -/
theorem initialized_direct_lambda {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    {node : StatementNode} {binder : TypedBinder} {initializer : Option ExpressionId}
    (member : Node.statement node ∈ specialized.function.typedBody.nodes)
    (form : node.form = .letDecl binder initializer)
    (polymorphic : binder.scheme.quantified ≠ []) :
    ∃ expression, initializer = some expression ∧
      SourceSpecialization.isDirectLambdaInitializer specialized.function.typedBody expression = true := by
  have empty := no_rejected (positions_of_specialization accepted)
  have localEmpty : rejectedBinders specialized.function.typedBody (.statement node) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro actual present
    have all : actual ∈ specialized.function.typedBody.nodes.flatMap
        (rejectedBinders specialized.function.typedBody) := List.mem_flatMap.mpr ⟨_, member, present⟩
    rw [empty] at all
    cases all
  have nonempty : binder.scheme.quantified.isEmpty = false := by
    cases same : binder.scheme.quantified with
    | nil => exact False.elim (polymorphic same)
    | cons => rfl
  simp only [rejectedBinders, form, nonempty, Bool.false_or, allowed, Bool.not_false, Bool.true_and] at localEmpty
  split at localEmpty
  next accepted =>
    cases initializer with
    | none => simp at accepted
    | some expression => exact ⟨expression, rfl, accepted⟩
  next => cases localEmpty

/-- This source-wide endpoint also accounts for initialized `for` header
binders, which the original specialization requires to be monomorphic. -/
theorem initialized_position {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    {binder : TypedBinder} (member : binder ∈ specialized.function.typedBody.initializedLetBinders)
    (polymorphic : binder.scheme.quantified ≠ []) :
    ∃ node initializer, Node.statement node ∈ specialized.function.typedBody.nodes ∧
      node.form = .letDecl binder (some initializer) ∧
      SourceSpecialization.isDirectLambdaInitializer specialized.function.typedBody initializer = true := by
  obtain ⟨node, present, binderMember⟩ := List.mem_flatMap.mp member
  cases node with
  | expression node => cases binderMember
  | statement node =>
    change binder ∈ node.form.initializedLetBinders at binderMember
    cases form : node.form <;> simp only [form, StatementForm.initializedLetBinders] at binderMember
    case letDecl actual initializer =>
      cases initializer with
      | none => cases binderMember
      | some initializer =>
        have same : binder = actual := by simpa using binderMember
        subst actual
        obtain ⟨expression, same, direct⟩ := initialized_direct_lambda accepted present form polymorphic
        cases Option.some.inj same
        exact ⟨node, initializer, present, form, direct⟩
    case forLoop initializer condition post body =>
      have inItems : binder ∈ (initializer ++ post).flatMap ForItemForm.initializedLetBinders := by
        simpa only [List.flatMap_append] using binderMember
      obtain ⟨item, itemMember, localMember⟩ := List.mem_flatMap.mp inItems
      have nonempty : binder.scheme.quantified.isEmpty = false := by
        cases same : binder.scheme.quantified with
        | nil => exact False.elim (polymorphic same)
        | cons => rfl
      have rejected : binder ∈ rejectedBinders specialized.function.typedBody (.statement node) := by
        simp only [rejectedBinders, form]
        apply List.mem_filterMap.mpr
        refine ⟨item, itemMember, ?_⟩
        cases item <;> simp only [ForItemForm.initializedLetBinders] at localMember
        case letDecl actual initializer =>
          cases initializer with
          | none => cases localMember
          | some initializer =>
            have same : binder = actual := by simpa using localMember
            subst actual
            simp only [nonempty, Bool.false_eq_true, ↓reduceIte]
        all_goals cases localMember
      have all : binder ∈ specialized.function.typedBody.nodes.flatMap
          (rejectedBinders specialized.function.typedBody) := List.mem_flatMap.mpr ⟨_, present, rejected⟩
      rw [no_rejected (positions_of_specialization accepted)] at all
      cases all
    all_goals cases binderMember

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationSpecializationBinders
