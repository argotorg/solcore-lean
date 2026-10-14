import Solcore.SourceSemantics.SourceInferenceSelectedOrdinaryRecorder
import Solcore.SourceSemantics.SourceInferenceSelectedDeclaration
import Solcore.SourceSemantics.SourceInferenceSelectedOperatorInterfaces

/-! Operator inference is interpreted in the actual final lexical context.
Profile substitution uses the unchanged signature catalog; no substitution
certificate for an unrelated whole lexical context is required. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open FlexibleSubstitution

theorem operatorProfile_applySubstitution_signatures
    {substitution : Substitution}
    {source target : Context} {traitName methodName : String}
    {operand : Ty} {parameterTypes returnTypes : List Ty}
    {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed source.signatures)
    (signatures : target.signatures = source.signatures)
    (profile : OperatorProfileInstantiates source traitName methodName operand
      parameterTypes returnTypes predicates) :
    OperatorProfileInstantiates target traitName methodName
      (substitution.apply operand) (parameterTypes.map substitution.apply)
      (returnTypes.map substitution.apply)
      (predicates.map
        (TypedTraitResolution.applySubstitution substitution)) := by
  cases profile with
  | @intro signature method parameter signatureMem traitNameEq parametersEq
      methodUnique parameterTypesEq returnTypesEq =>
      have signatureWellFormed := catalog.traits_semantic signature signatureMem
      have methodFiltered : method ∈
          signature.methods.filter
            (fun candidate => candidate.name == methodName) := by
        rw [methodUnique]
        simp
      have methodMem : method ∈ signature.methods :=
        (List.mem_filter.mp methodFiltered).1
      have methodWellFormed := signatureWellFormed.methods method methodMem
      have innerExact : SourceSemantics.ParameterSubstitution.Exact
          [(parameter, operand)] signature.parameters := by
        constructor
        · exact signatureWellFormed.parameters_nodup
        · rw [parametersEq]
          simp [SourceSemantics.ParameterSubstitution.domain]
      have parameterCompose :=
        TypesWellScoped.applyFlexible_composeParameters
          (context := signatureContext source.signatures signature.id
            signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          substitution [(parameter, operand)] innerExact
          (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
            methodWellFormed.parameter_types)
      have returnCompose :=
        TypesWellScoped.applyFlexible_composeParameters
          (context := signatureContext source.signatures signature.id
            signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          substitution [(parameter, operand)] innerExact
          (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
            methodWellFormed.return_types)
      have predicateCompose :=
        PredicatesWellFormed.applyFlexible_composeParameters
          (context := signatureContext source.signatures signature.id
            signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          substitution [(parameter, operand)] innerExact
          methodWellFormed.predicates
      change OperatorProfileInstantiates target traitName methodName
        (substitution.apply operand) (parameterTypes.map substitution.apply)
        (returnTypes.map substitution.apply)
        ({ trait := .declaration signature.id
           subject := substitution.apply operand
           arguments := [] } ::
          (method.wherePredicates.map
            (ProgramPredicate.applyParameters [(parameter, operand)])).map
              (TypedTraitResolution.applySubstitution substitution))
      rw [predicateCompose]
      exact .intro
        (by
          rw [signatures]
          exact signatureMem)
        traitNameEq parametersEq methodUnique
        (by
          change method.parameterTypes.map
              (ParameterSubstitution.mapRange substitution
                [(parameter, operand)]).apply =
            parameterTypes.map substitution.apply
          rw [← parameterCompose, parameterTypesEq])
        (by
          change method.returnTypes.map
              (ParameterSubstitution.mapRange substitution
                [(parameter, operand)]).apply =
            returnTypes.map substitution.apply
          rw [← returnCompose, returnTypesEq])

private theorem emptyLedger_sequence_false {context : SourceSemantics.Context}
    (empty : context.solvedRequirements = []) {ids : List RequirementId}
    {head : ProgramPredicate} {tail : List ProgramPredicate}
    (sequence : RequirementSequenceProves context ids (head :: tail)) : False := by
  cases sequence with
  | cons evidence rest =>
    obtain ⟨row, ⟨member, _⟩, _⟩ := evidence
    rw [empty] at member
    cases member

private theorem unary_primitive_substitution {context target : SourceSemantics.Context}
    (empty : context.solvedRequirements = []) {substitution : Substitution}
    {operator : Syntax.UnaryOp} {operand result : Ty} {requirements : List RequirementId}
    (typed : UnaryOperatorHasType context operator operand result requirements) :
    UnaryOperatorHasType target operator (substitution.apply operand)
      (substitution.apply result) requirements := by
  cases typed with
  | logicalNot => exact .logicalNot
  | wordBitNot => exact .wordBitNot
  | integerBitNot => exact .integerBitNot
  | trait dispatch profile evidence =>
    cases profile
    exact False.elim (emptyLedger_sequence_false empty evidence)

private theorem binary_primitive_substitution {context target : SourceSemantics.Context}
    (empty : context.solvedRequirements = []) {substitution : Substitution}
    {operator : Syntax.BinaryOp} {left right result : Ty} {requirements : List RequirementId}
    (typed : BinaryOperatorHasType context operator left right result requirements) :
    BinaryOperatorHasType target operator (substitution.apply left)
      (substitution.apply right) (substitution.apply result) requirements := by
  cases typed with
  | wordArithmetic kind => exact .wordArithmetic kind
  | integerArithmetic kind => exact .integerArithmetic kind
  | wordComparison kind => exact .wordComparison kind
  | integerComparison kind => exact .integerComparison kind
  | booleanAnd => exact .booleanAnd
  | booleanOr => exact .booleanOr
  | trait dispatch profile evidence =>
    cases profile
    exact False.elim (emptyLedger_sequence_false empty evidence)

theorem unaryOperatorInferenceCase_hasType_in_active
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {base active : SourceSemantics.Context}
    {initial later : Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {ledgerSource : TypedSource} {occurrence : NodeId}
    {operator : Syntax.UnaryOp} {operandType : TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {result : Detail.OperatorInferenceResult}
    (inferenceCase : UnaryOperatorInferenceCase inferenceContext (Context.ofSignatures inferenceContext.signatures)
      initial operator operandType integerLiterals result)
    (progress : initial.InferenceProgress result.state)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (requirementsSubset : result.state.requirements ⊆ later.requirements)
    (integerLiteralTargetsSupported : ∀ origin,
      origin ∈ integerLiterals →
        later.inference.substitution.apply
            (.variable origin.metavariable) = .word ∨
          later.inference.substitution.apply
            (.variable origin.metavariable) = .integer)
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (operatorNames : OperatorNamesAt inferenceContext.signatures solved result.requirements
      (fun name => ∃ method, UnaryTraitDispatch operator name method))
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered ledgerSource active occurrence)
    (occurs : ∀ requirement, requirement ∈ result.requirements →
      PrimaryRequirementOccursAt ledgerSource occurrence requirement) :
    UnaryOperatorHasType active operator
      (later.inference.substitution.apply operandType)
      (later.inference.substitution.apply result.type)
      result.requirements := by
  have laterExtendsInitial :
      later.inference.substitution.SemanticallyExtends
        initial.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      progress.substitution_extends
  have resolvedOperandEq :
      later.inference.substitution.apply
          (result.state.resolve operandType) =
        later.inference.substitution.apply operandType :=
    TypeSystem.InferState.apply_resolve_eq_apply substitutionExtends
      operandType
  cases inferenceCase with
  | primitive typing =>
      have mapped :=
        unary_primitive_substitution (target := active) (substitution := later.inference.substitution) rfl typing
      simpa only [resolvedOperandEq] using mapped
  | deferredBitNot operatorEq requirementsEq typeEq deferred =>
      have openTarget : Detail.isOpenIntegerLiteralTarget initial
          integerLiterals operandType = true := by
        unfold Detail.isDeferredBuiltinOperatorTarget at deferred
        split at deferred <;> simp_all
      obtain ⟨_, origin, _, originMember, originResolveEq⟩ :=
        Detail.isOpenIntegerLiteralTarget_true_witness openTarget
      have originTargetEq :
          later.inference.substitution.apply
              (.variable origin.metavariable) =
            later.inference.substitution.apply operandType := by
        calc
          later.inference.substitution.apply
                (.variable origin.metavariable) =
              later.inference.substitution.apply
                (initial.resolve (.variable origin.metavariable)) :=
            (TypeSystem.InferState.apply_resolve_eq_apply
              laterExtendsInitial (.variable origin.metavariable)).symm
          _ = later.inference.substitution.apply
                (initial.resolve operandType) :=
            congrArg later.inference.substitution.apply originResolveEq
          _ = later.inference.substitution.apply operandType :=
            TypeSystem.InferState.apply_resolve_eq_apply laterExtendsInitial
              operandType
      have resultTargetEq : later.inference.substitution.apply result.type =
          later.inference.substitution.apply operandType := by
        rw [typeEq]
        exact resolvedOperandEq
      have supported := integerLiteralTargetsSupported origin
        originMember
      rcases supported with originWord | originInteger
      · have operandWord : later.inference.substitution.apply operandType =
            .word := originTargetEq.symm.trans originWord
        have resultWord : later.inference.substitution.apply result.type =
            .word := resultTargetEq.trans operandWord
        simpa only [operatorEq, operandWord, resultWord, requirementsEq] using
          (UnaryOperatorHasType.wordBitNot (context := active))
      · have operandInteger : later.inference.substitution.apply operandType =
            .integer := originTargetEq.symm.trans originInteger
        have resultInteger : later.inference.substitution.apply result.type =
            .integer := resultTargetEq.trans operandInteger
        simpa only [operatorEq, operandInteger, resultInteger,
          requirementsEq] using
            (UnaryOperatorHasType.integerBitNot (context := active))
  | @trait trait traitName methodName predicates dispatch selected profile
      corresponds =>
      obtain ⟨companions, predicateEq⟩ := operatorTraitPredicates_primary profile
      have traitNameEq := operatorNames.traitName solveSuccess
        (by simpa only [predicateEq] using corresponds.mono requirementsSubset) ⟨methodName, dispatch⟩
      apply UnaryOperatorHasType.trait dispatch
      · have instantiated :=
          operatorProfile_applySubstitution_signatures (substitution := later.inference.substitution) catalog rfl
            (operatorTraitPredicates_instantiates signaturesEq traitNameEq profile)
        simpa only [List.map_cons, List.map_nil, resolvedOperandEq] using
          instantiated
      · have laterCorresponds :=
          corresponds.mono requirementsSubset
        have sequence := solveRequirements_correspondingSequenceProvesAt
          laterCorresponds solveSuccess solvedEq ledger ownership
          activeSignaturesEq activeRequirementsEq assumptionsMono covered
          occurs
        change RequirementSequenceProves active result.requirements
          (predicates.map (TypedTraitResolution.applySubstitution
            later.inference.substitution)) at sequence
        exact sequence


theorem binaryOperatorInferenceCase_hasType_in_active
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {base active : SourceSemantics.Context}
    {initial later : Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {ledgerSource : TypedSource} {occurrence : NodeId}
    {operator : Syntax.BinaryOp} {left right : TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {result : Detail.OperatorInferenceResult}
    (inferenceCase : BinaryOperatorInferenceCase inferenceContext (Context.ofSignatures inferenceContext.signatures)
      initial operator left right integerLiterals result)
    (progress : initial.InferenceProgress result.state)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (requirementsSubset : result.state.requirements ⊆ later.requirements)
    (integerLiteralTargetsSupported : ∀ origin,
      origin ∈ integerLiterals →
        later.inference.substitution.apply
            (.variable origin.metavariable) = .word ∨
          later.inference.substitution.apply
            (.variable origin.metavariable) = .integer)
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (operatorNames : OperatorNamesAt inferenceContext.signatures solved result.requirements
      (fun name => ∃ method, BinaryTraitDispatch operator name method))
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered ledgerSource active occurrence)
    (occurs : ∀ requirement, requirement ∈ result.requirements →
      PrimaryRequirementOccursAt ledgerSource occurrence requirement) :
    BinaryOperatorHasType active operator
      (later.inference.substitution.apply left)
      (later.inference.substitution.apply right)
      (later.inference.substitution.apply result.type)
      result.requirements := by
  have laterExtendsInitial :
      later.inference.substitution.SemanticallyExtends
        initial.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      progress.substitution_extends
  have resolvedLeftEq :
      later.inference.substitution.apply (result.state.resolve left) =
        later.inference.substitution.apply left :=
    TypeSystem.InferState.apply_resolve_eq_apply substitutionExtends left
  have resolvedRightEq :
      later.inference.substitution.apply (result.state.resolve right) =
        later.inference.substitution.apply right :=
    TypeSystem.InferState.apply_resolve_eq_apply substitutionExtends right
  cases inferenceCase with
  | primitive typing =>
      have mapped :=
        binary_primitive_substitution (target := active) (substitution := later.inference.substitution) rfl typing
      simpa only [resolvedLeftEq, resolvedRightEq] using mapped
  | literalFallback requirementsEq operandsEq typeEq fallback =>
      have finalOperandsEq :
          later.inference.substitution.apply left =
            later.inference.substitution.apply right := by
        calc
          later.inference.substitution.apply left =
              later.inference.substitution.apply
                (result.state.resolve left) := resolvedLeftEq.symm
          _ = later.inference.substitution.apply
                (result.state.resolve right) :=
            congrArg later.inference.substitution.apply operandsEq
          _ = later.inference.substitution.apply right := resolvedRightEq
      have resultTypeEq :
          later.inference.substitution.apply result.type =
            if Detail.binaryResultIsBool operator then .bool
            else later.inference.substitution.apply left := by
        rw [typeEq]
        by_cases returnsBool : Detail.binaryResultIsBool operator = true
        · simp [returnsBool, TypeSystem.Ty.bool]
        · simp [returnsBool, resolvedLeftEq]
      rcases fallback with deferred | staged
      · have deferredFacts :
            Detail.binaryBuiltinType operator = .word ∧
              (Detail.isOpenIntegerLiteralTarget initial integerLiterals left ||
                Detail.isOpenIntegerLiteralTarget initial integerLiterals
                  right) = true := by
          unfold Detail.isDeferredBuiltinOperatorTarget at deferred
          split at deferred <;> simp_all
        have openEither := Bool.or_eq_true_iff.mp deferredFacts.2
        obtain ⟨origin, originMember, originResolveEq⟩ :
            ∃ origin, origin ∈ integerLiterals ∧
              (initial.resolve (.variable origin.metavariable) =
                  initial.resolve left ∨
                initial.resolve (.variable origin.metavariable) =
                  initial.resolve right) := by
          rcases openEither with leftOpen | rightOpen
          · obtain ⟨_, origin, _, member, equal⟩ :=
              Detail.isOpenIntegerLiteralTarget_true_witness leftOpen
            exact ⟨origin, member, .inl equal⟩
          · obtain ⟨_, origin, _, member, equal⟩ :=
              Detail.isOpenIntegerLiteralTarget_true_witness rightOpen
            exact ⟨origin, member, .inr equal⟩
        have originOperandEq :
            later.inference.substitution.apply
                (.variable origin.metavariable) =
              later.inference.substitution.apply left := by
          rcases originResolveEq with leftEq | rightEq
          · calc
              later.inference.substitution.apply
                    (.variable origin.metavariable) =
                  later.inference.substitution.apply
                    (initial.resolve (.variable origin.metavariable)) :=
                (TypeSystem.InferState.apply_resolve_eq_apply
                  laterExtendsInitial (.variable origin.metavariable)).symm
              _ = later.inference.substitution.apply
                    (initial.resolve left) :=
                congrArg later.inference.substitution.apply leftEq
              _ = later.inference.substitution.apply left :=
                TypeSystem.InferState.apply_resolve_eq_apply
                  laterExtendsInitial left
          · calc
              later.inference.substitution.apply
                    (.variable origin.metavariable) =
                  later.inference.substitution.apply
                    (initial.resolve (.variable origin.metavariable)) :=
                (TypeSystem.InferState.apply_resolve_eq_apply
                  laterExtendsInitial (.variable origin.metavariable)).symm
              _ = later.inference.substitution.apply
                    (initial.resolve right) :=
                congrArg later.inference.substitution.apply rightEq
              _ = later.inference.substitution.apply right :=
                TypeSystem.InferState.apply_resolve_eq_apply
                  laterExtendsInitial right
              _ = later.inference.substitution.apply left :=
                finalOperandsEq.symm
        have supported := integerLiteralTargetsSupported origin
          originMember
        rcases supported with originWord | originInteger
        · have leftWord : later.inference.substitution.apply left = .word :=
            originOperandEq.symm.trans originWord
          have rightWord : later.inference.substitution.apply right = .word :=
            finalOperandsEq.symm.trans leftWord
          have resultWord : later.inference.substitution.apply result.type =
              if Detail.binaryResultIsBool operator then .bool
              else .word := by
            rw [resultTypeEq, leftWord]
          have typing := binaryBuiltin_hasType active operator
          rw [deferredFacts.1] at typing
          simpa only [leftWord, rightWord, resultWord, requirementsEq] using
            typing
        · have leftInteger : later.inference.substitution.apply left =
              .integer := originOperandEq.symm.trans originInteger
          have rightInteger : later.inference.substitution.apply right =
              .integer := finalOperandsEq.symm.trans leftInteger
          have resultInteger : later.inference.substitution.apply result.type =
              if Detail.binaryResultIsBool operator then .bool
              else .integer := by
            rw [resultTypeEq, leftInteger]
          have typing := binaryInteger_hasType active operator deferredFacts.1
          simpa only [leftInteger, rightInteger, resultInteger,
            requirementsEq] using typing
      · have stagedFacts :
            Detail.binaryBuiltinType operator = .word ∧
              result.state.resolve (result.state.resolve left) = .integer := by
          unfold Detail.isStagedIntegerOperatorTarget at staged
          simp_all
        have resolvedLeftInteger :
            later.inference.substitution.apply
                (result.state.resolve left) = .integer := by
          calc
            later.inference.substitution.apply
                  (result.state.resolve left) =
                later.inference.substitution.apply
                  (result.state.resolve (result.state.resolve left)) :=
              (TypeSystem.InferState.apply_resolve_eq_apply
                substitutionExtends (result.state.resolve left)).symm
            _ = later.inference.substitution.apply (.integer) :=
              congrArg later.inference.substitution.apply stagedFacts.2
            _ = .integer := by rfl
        have leftInteger : later.inference.substitution.apply left =
            .integer := resolvedLeftEq.symm.trans resolvedLeftInteger
        have rightInteger : later.inference.substitution.apply right =
            .integer := finalOperandsEq.symm.trans leftInteger
        have resultInteger : later.inference.substitution.apply result.type =
            if Detail.binaryResultIsBool operator then .bool
            else .integer := by
          rw [resultTypeEq, leftInteger]
        have typing := binaryInteger_hasType active operator stagedFacts.1
        simpa only [leftInteger, rightInteger, resultInteger,
          requirementsEq] using typing
  | @trait trait traitName methodName predicates operandsEq dispatch selected
      profile corresponds =>
      obtain ⟨companions, predicateEq⟩ := operatorTraitPredicates_primary profile
      have traitNameEq := operatorNames.traitName solveSuccess
        (by simpa only [predicateEq] using corresponds.mono requirementsSubset) ⟨methodName, dispatch⟩
      have finalOperandsEq :
          later.inference.substitution.apply left =
            later.inference.substitution.apply right := by
        calc
          later.inference.substitution.apply left =
              later.inference.substitution.apply
                (result.state.resolve left) := resolvedLeftEq.symm
          _ = later.inference.substitution.apply
                (result.state.resolve right) :=
            congrArg later.inference.substitution.apply operandsEq
          _ = later.inference.substitution.apply right := resolvedRightEq
      have instantiated :=
        operatorProfile_applySubstitution_signatures (substitution := later.inference.substitution) catalog rfl
          (operatorTraitPredicates_instantiates signaturesEq traitNameEq profile)
      have finalProfile : OperatorProfileInstantiates active traitName
          methodName (later.inference.substitution.apply left)
          [later.inference.substitution.apply left,
            later.inference.substitution.apply left]
          [later.inference.substitution.apply result.type]
          (predicates.map (TypedTraitResolution.applySubstitution
            later.inference.substitution)) := by
        simpa only [List.map_cons, List.map_nil, resolvedLeftEq] using
          instantiated
      have laterCorresponds := corresponds.mono requirementsSubset
      have sequence := solveRequirements_correspondingSequenceProvesAt
        laterCorresponds solveSuccess solvedEq ledger ownership
        activeSignaturesEq activeRequirementsEq assumptionsMono covered occurs
      change RequirementSequenceProves active result.requirements
        (predicates.map (TypedTraitResolution.applySubstitution
          later.inference.substitution)) at sequence
      have common : BinaryOperatorHasType active operator
          (later.inference.substitution.apply left)
          (later.inference.substitution.apply left)
          (later.inference.substitution.apply result.type)
          result.requirements :=
        .trait dispatch finalProfile sequence
      simpa only [finalOperandsEq] using common


end Solcore.SourceSemantics.SourceInferenceSoundness
