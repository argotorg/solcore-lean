import Solcore.Syntax.Parser.Trivia
import Solcore.Syntax.FileValidity

/-! Source-validity preservation for canonical comment attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Selected leading comments inherit validity from the complete comment stream. -/
theorem commentsDirectlyBefore_validFor (file : SourceFile)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (declarationStart : Nat) :
    ∀ comment ∈ commentsDirectlyBefore file.content comments
      declarationStart, comment.span.ValidFor file := by
  intro comment member
  exact commentsValid comment
    (commentsDirectlyBefore_mem file.content comments declarationStart member)

namespace TriviaInternals

/-- Attaching selected comments preserves a valid enum constructor. -/
theorem attachEnumConstructorComments_validFor (file : SourceFile)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (introducer : SourceSpan) (constructor : EnumConstructor)
    (constructorValid : EnumConstructor.ValidFor file constructor) :
    EnumConstructor.ValidFor file
      (attachEnumConstructorComments file comments introducer constructor) := by
  rcases constructorValid with
    ⟨spanValid, _oldCommentsValid, nameValid, fieldsSpanValid, fieldsValid⟩
  refine ⟨spanValid, ?_, nameValid, fieldsSpanValid, fieldsValid⟩
  intro comment member
  exact commentsValid comment
    (attachEnumConstructorComments_mem file comments introducer constructor
      member)

/-- Constructor attachment preserves validity throughout the enum body. -/
theorem attachEnumConstructors_validFor (file : SourceFile)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (bodySpan : SourceSpan) : ∀ constructors previous,
    List.ValidFor EnumConstructor.ValidFor file constructors →
    List.ValidFor EnumConstructor.ValidFor file
      (attachEnumConstructors file comments bodySpan constructors previous) := by
  intro constructors
  induction constructors with
  | nil =>
      intro previous _constructorValid attached member
      simp [attachEnumConstructors] at member
  | cons constructor rest inductionHypothesis =>
      intro previous constructorsValid attached member
      have constructorValid := constructorsValid constructor (by simp)
      have restValid : List.ValidFor EnumConstructor.ValidFor file rest := by
        intro retained retainedMember
        exact constructorsValid retained (List.mem_cons_of_mem constructor
          retainedMember)
      cases previous with
      | none =>
          simp only [attachEnumConstructors, List.mem_cons] at member
          rcases member with rfl | retainedMember
          · exact attachEnumConstructorComments_validFor file comments
              commentsValid _ constructor constructorValid
          · exact inductionHypothesis (some constructor.span) restValid
              attached retainedMember
      | some prior =>
          simp only [attachEnumConstructors] at member
          split at member
          · simp only [List.mem_cons] at member
            rcases member with rfl | retainedMember
            · exact attachEnumConstructorComments_validFor file comments
                commentsValid _ constructor constructorValid
            · exact inductionHypothesis (some constructor.span) restValid
                attached retainedMember
          · simp only [List.mem_cons] at member
            rcases member with rfl | retainedMember
            · exact constructorValid
            · exact inductionHypothesis (some constructor.span) restValid
                attached retainedMember

/-- Enum attachment preserves every declaration and constructor range. -/
theorem attachEnumComments_validFor (file : SourceFile)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (declaration : EnumDecl)
    (declarationValid : EnumDecl.ValidFor file declaration) :
    EnumDecl.ValidFor file (attachEnumComments file comments declaration) := by
  rcases declarationValid with
    ⟨spanValid, deriveValid, nameValid, parametersSpanValid,
      parametersValid, bodyValid, constructorsValid⟩
  refine ⟨spanValid, deriveValid, nameValid, parametersSpanValid,
    parametersValid, bodyValid, ?_⟩
  exact attachEnumConstructors_validFor file comments commentsValid
    declaration.value.bodySpan declaration.value.constructors none
    constructorsValid

/-- Attaching selected comments preserves a valid trait method. -/
theorem attachTraitMethodComments_validFor (file : SourceFile)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (method : TraitMethod) (methodValid : TraitMethod.ValidFor file method) :
    TraitMethod.ValidFor file
      (attachTraitMethodComments file comments method) := by
  rcases methodValid with
    ⟨spanValid, _oldCommentsValid, signatureValid, semicolonValid⟩
  refine ⟨spanValid, ?_, signatureValid, semicolonValid⟩
  exact commentsDirectlyBefore_validFor file comments commentsValid
    method.value.signature.span.startByte

/-- Mapping trait-method comments leaves every declaration range valid. -/
theorem attachTraitComments_validFor (file : SourceFile)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (declaration : TraitDecl)
    (declarationValid : TraitDecl.ValidFor file declaration) :
    TraitDecl.ValidFor file
      (attachTraitComments file comments declaration) := by
  rcases declarationValid with
    ⟨spanValid, nameValid, parametersSpanValid, parametersValid,
      whereValid, bodyValid, methodsValid⟩
  refine ⟨spanValid, nameValid, parametersSpanValid, parametersValid,
    whereValid, bodyValid, ?_⟩
  intro attached attachedMember
  rcases List.mem_map.mp attachedMember with
    ⟨method, methodMember, rfl⟩
  exact attachTraitMethodComments_validFor file comments commentsValid method
    (methodsValid method methodMember)

/-- Attaching selected comments preserves a valid implementation method. -/
theorem attachImplMethodComments_validFor
    (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (method : ImplMethod)
    (methodValid : ImplMethod.ValidFor statementValid file method) :
    ImplMethod.ValidFor statementValid file
      (attachImplMethodComments file comments method) := by
  rcases methodValid with
    ⟨spanValid, _oldCommentsValid, declarationValid⟩
  refine ⟨spanValid, ?_, declarationValid⟩
  exact commentsDirectlyBefore_validFor file comments commentsValid
    method.span.startByte

/-- Mapping implementation-method comments preserves declaration validity. -/
theorem attachImplComments_validFor
    (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (declaration : ImplDecl)
    (declarationValid : ImplDecl.ValidFor statementValid file declaration) :
    ImplDecl.ValidFor statementValid file
      (attachImplComments file comments declaration) := by
  rcases declarationValid with
    ⟨spanValid, defaultValid, parameterSpanValid, parametersValid,
      traitNameValid, headSpanValid, headArgumentsValid, whereValid,
      bodyValid, methodsValid⟩
  refine ⟨spanValid, defaultValid, parameterSpanValid, parametersValid,
    traitNameValid, headSpanValid, headArgumentsValid, whereValid,
    bodyValid, ?_⟩
  intro attached attachedMember
  rcases List.mem_map.mp attachedMember with
    ⟨method, methodMember, rfl⟩
  exact attachImplMethodComments_validFor statementValid file comments
    commentsValid method (methodsValid method methodMember)

/-- Contract-member attachment preserves all branches, including nested enums. -/
theorem attachContractMemberComments_validFor
    (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (member : ContractMember)
    (memberValid : ContractMember.ValidFor statementValid expressionValid
      file member) :
    ContractMember.ValidFor statementValid expressionValid file
      (attachContractMemberComments file comments member) := by
  cases memberValid with
  | @field span leadingComments declaration spanValid _ declarationValid =>
      exact ContractMember.ValidFor.field spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid
          span.startByte) declarationValid
  | @function span leadingComments declaration spanValid _ declarationValid =>
      exact ContractMember.ValidFor.function spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid
          span.startByte) declarationValid
  | @constructor span leadingComments declaration spanValid _ declarationValid =>
      exact ContractMember.ValidFor.constructor spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid
          span.startByte) declarationValid
  | @fallback span leadingComments declaration spanValid _ declarationValid =>
      exact ContractMember.ValidFor.fallback spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid
          span.startByte) declarationValid
  | @typeAlias span leadingComments declaration spanValid _ declarationValid =>
      exact ContractMember.ValidFor.typeAlias spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid
          span.startByte) declarationValid
  | @enum span leadingComments declaration spanValid _ declarationValid =>
      exact ContractMember.ValidFor.enum spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid
          span.startByte)
        (attachEnumComments_validFor file comments commentsValid _
          declarationValid)
  | @error span leadingComments spanValid _ =>
      exact ContractMember.ValidFor.error spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid
          span.startByte)

/-- Contract attachment preserves member order and nested declaration validity. -/
theorem attachContractComments_validFor
    (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (declaration : ContractDecl)
    (declarationValid : ContractDecl.ValidFor statementValid expressionValid
      file declaration) :
    ContractDecl.ValidFor statementValid expressionValid file
      (attachContractComments file comments declaration) := by
  rcases declarationValid with
    ⟨spanValid, nameValid, parametersSpanValid, parametersValid,
      bodyValid, membersValid⟩
  refine ⟨spanValid, nameValid, parametersSpanValid, parametersValid,
    bodyValid, ?_⟩
  intro attached attachedMember
  rcases List.mem_map.mp attachedMember with
    ⟨member, memberMember, rfl⟩
  exact attachContractMemberComments_validFor statementValid expressionValid
    file comments commentsValid member (membersValid member memberMember)

end TriviaInternals

/-- Public top-level attachment selects only source-valid leading comments. -/
theorem attachTopItemComments_leading_validFor (file : SourceFile)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (item : TopItem) :
    ∀ comment ∈ (attachTopItemComments file comments item).leadingComments,
      comment.span.ValidFor file := by
  exact commentsDirectlyBefore_validFor file comments commentsValid
    item.span.startByte

/-- The public top-level trait branch preserves its nested declaration contract. -/
theorem attachTopItemComments_trait_validFor (file : SourceFile)
    (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (span : SourceSpan) (leadingComments : List Comment)
    (spanValid : span.ValidFor file)
    (declaration : TraitDecl)
    (declarationValid : TraitDecl.ValidFor file declaration) :
    TopItem.ValidFor statementValid expressionValid file
      (attachTopItemComments file comments {
        span, leadingComments, value := .trait declaration
      }) := by
  apply TopItem.ValidFor.trait
  · exact spanValid
  · exact commentsDirectlyBefore_validFor file comments commentsValid
      span.startByte
  · exact TriviaInternals.attachTraitComments_validFor file comments
      commentsValid declaration declarationValid

/-- The public top-level impl branch preserves its nested declaration contract. -/
theorem attachTopItemComments_impl_validFor
    (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (span : SourceSpan) (leadingComments : List Comment)
    (spanValid : span.ValidFor file)
    (declaration : ImplDecl)
    (declarationValid : ImplDecl.ValidFor statementValid file declaration) :
    TopItem.ValidFor statementValid expressionValid file
      (attachTopItemComments file comments {
        span, leadingComments, value := .impl declaration
      }) := by
  apply TopItem.ValidFor.impl
  · exact spanValid
  · exact commentsDirectlyBefore_validFor file comments commentsValid
      span.startByte
  · exact TriviaInternals.attachImplComments_validFor statementValid file
      comments commentsValid declaration declarationValid

/-- Comment attachment preserves source validity for every top-level branch. -/
theorem attachTopItemComments_validFor
    (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (item : TopItem)
    (itemValid : TopItem.ValidFor statementValid expressionValid file item) :
    TopItem.ValidFor statementValid expressionValid file
      (attachTopItemComments file comments item) := by
  cases itemValid with
  | @importDecl span leadingComments declaration spanValid _ declarationValid =>
      exact TopItem.ValidFor.importDecl spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid span.startByte)
        declarationValid
  | @exportDecl span leadingComments declaration spanValid _ declarationValid =>
      exact TopItem.ValidFor.exportDecl spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid span.startByte)
        declarationValid
  | @pragmaDecl span leadingComments declaration spanValid _ declarationValid =>
      exact TopItem.ValidFor.pragmaDecl spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid span.startByte)
        declarationValid
  | @typeAlias span leadingComments declaration spanValid _ declarationValid =>
      exact TopItem.ValidFor.typeAlias spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid span.startByte)
        declarationValid
  | @enum span leadingComments declaration spanValid _ declarationValid =>
      exact TopItem.ValidFor.enum spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid span.startByte)
        (TriviaInternals.attachEnumComments_validFor file comments commentsValid
          _ declarationValid)
  | @trait span leadingComments declaration spanValid _ declarationValid =>
      exact TopItem.ValidFor.trait spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid span.startByte)
        (TriviaInternals.attachTraitComments_validFor file comments commentsValid
          _ declarationValid)
  | @impl span leadingComments declaration spanValid _ declarationValid =>
      exact TopItem.ValidFor.impl spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid span.startByte)
        (TriviaInternals.attachImplComments_validFor statementValid file comments
          commentsValid _ declarationValid)
  | @contract span leadingComments declaration spanValid _ declarationValid =>
      exact TopItem.ValidFor.contract spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid span.startByte)
        (TriviaInternals.attachContractComments_validFor statementValid
          expressionValid file comments commentsValid _ declarationValid)
  | @function span leadingComments declaration spanValid _ declarationValid =>
      exact TopItem.ValidFor.function spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid span.startByte)
        declarationValid
  | @error span leadingComments spanValid _ =>
      exact TopItem.ValidFor.error spanValid
        (commentsDirectlyBefore_validFor file comments commentsValid span.startByte)

end Solcore.Syntax.Parser
