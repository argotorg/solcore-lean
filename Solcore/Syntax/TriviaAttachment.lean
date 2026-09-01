import Solcore.Syntax.Declaration
import Solcore.Syntax.Trivia

/-! Pure comment attachment for canonical declarations and top-level items. -/

set_option autoImplicit false

namespace Solcore.Syntax.Trivia

namespace Internals

def attachEnumConstructorComments (file : SourceFile)
    (comments : List Comment) (introducer : SourceSpan)
    (constructor : EnumConstructor) : EnumConstructor :=
  let trailing := commentsDirectlyAfterIntroducer file.content comments
    introducer constructor.span.startByte
  let nextStart := trailing.head?.map (fun comment => comment.span.startByte)
    |>.getD constructor.span.startByte
  let gapIsDirect := match utf8Slice? file.content introducer.endByte nextStart with
    | some gap => allRustWhitespace gap && lineBreakCount gap ≤ 1
    | none => false
  let leading :=
    (if gapIsDirect then
      commentsDirectlyBefore file.content comments introducer.startByte
    else
      []) ++ trailing
  { constructor with value := {
      constructor.value with leadingComments := leading
    }
  }

def attachEnumConstructors (file : SourceFile)
    (comments : List Comment) (bodySpan : SourceSpan) :
    List EnumConstructor → Option SourceSpan → List EnumConstructor
  | [], _ => []
  | constructor :: rest, previous =>
      let introducer := match previous with
        | none => some {
            source := bodySpan.source
            startByte := bodySpan.startByte
            endByte := bodySpan.startByte + 1
          }
        | some prior =>
            findSeparatorComma file.content comments bodySpan.source
              prior.endByte constructor.span.startByte
      let updated := match introducer with
        | some span =>
            attachEnumConstructorComments file comments span constructor
        | none => constructor
      updated :: attachEnumConstructors file comments bodySpan rest
        (some constructor.span)

def attachEnumComments (file : SourceFile) (comments : List Comment)
    (declaration : EnumDecl) : EnumDecl :=
  { declaration with value := {
      declaration.value with
      constructors := attachEnumConstructors file comments
        declaration.value.bodySpan declaration.value.constructors none
    }
  }

def attachTraitMethodComments (file : SourceFile)
    (comments : List Comment) (method : TraitMethod) : TraitMethod :=
  { method with value := {
      method.value with
      leadingComments := commentsDirectlyBefore file.content comments
        method.value.signature.span.startByte
    }
  }

def attachTraitComments (file : SourceFile) (comments : List Comment)
    (declaration : TraitDecl) : TraitDecl :=
  { declaration with value := {
      declaration.value with
      methods := declaration.value.methods.map
        (attachTraitMethodComments file comments)
    }
  }

def attachImplMethodComments (file : SourceFile)
    (comments : List Comment) (method : ImplMethod) : ImplMethod :=
  { method with value := {
      method.value with
      leadingComments := commentsDirectlyBefore file.content comments
        method.span.startByte
    }
  }

def attachImplComments (file : SourceFile) (comments : List Comment)
    (declaration : ImplDecl) : ImplDecl :=
  { declaration with value := {
      declaration.value with
      methods := declaration.value.methods.map
        (attachImplMethodComments file comments)
    }
  }

def attachContractMemberComments (file : SourceFile)
    (comments : List Comment) (member : ContractMember) : ContractMember :=
  let value := match member.value with
    | .enum declaration => .enum (attachEnumComments file comments declaration)
    | other => other
  { member with
    leadingComments := commentsDirectlyBefore file.content comments
      member.span.startByte
    value
  }

def attachContractComments (file : SourceFile)
    (comments : List Comment) (declaration : ContractDecl) : ContractDecl :=
  { declaration with value := {
      declaration.value with
      members := declaration.value.members.map
        (attachContractMemberComments file comments)
    }
  }

end Internals

/-- Attach top-level and nested declaration comments without changing spans. -/
def attachTopItemComments (file : SourceFile) (comments : List Comment)
    (item : TopItem) : TopItem :=
  let value := match item.value with
    | .enum declaration =>
        .enum (Internals.attachEnumComments file comments declaration)
    | .trait declaration =>
        .trait (Internals.attachTraitComments file comments declaration)
    | .impl declaration =>
        .impl (Internals.attachImplComments file comments declaration)
    | .contract declaration =>
        .contract (Internals.attachContractComments file comments declaration)
    | other => other
  { item with
    leadingComments := commentsDirectlyBefore file.content comments
      item.span.startByte
    value
  }

theorem Internals.attachEnumConstructorComments_mem
    (file : SourceFile) (comments : List Comment)
    (introducer : SourceSpan) (constructor : EnumConstructor)
    {comment : Comment}
    (member : comment ∈
      (attachEnumConstructorComments file comments introducer
        constructor).value.leadingComments) :
    comment ∈ comments := by
  unfold attachEnumConstructorComments at member
  dsimp only at member
  split at member
  · split at member
    · rcases List.mem_append.mp member with before | after
      · exact commentsDirectlyBefore_mem file.content comments
          introducer.startByte before
      · exact commentsDirectlyAfterIntroducer_mem file.content comments
          introducer constructor.span.startByte after
    · exact commentsDirectlyAfterIntroducer_mem file.content comments
        introducer constructor.span.startByte (by simpa using member)
  · exact commentsDirectlyAfterIntroducer_mem file.content comments
      introducer constructor.span.startByte (by simpa using member)

end Solcore.Syntax.Trivia
