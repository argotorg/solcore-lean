import Solcore.Syntax.Source
import Solcore.Syntax.Declaration

/-! Pure source-trivia selection, independent of parser state and replies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Trivia

/-- Rust 1.97.0 `char::is_whitespace`, used by comment attachment. -/
def isRustWhitespace (character : Char) : Bool :=
  let value := character.val.toNat
  (0x09 ≤ value && value ≤ 0x0D) || value == 0x20 ||
    value == 0x85 || value == 0xA0 || value == 0x1680 ||
    (0x2000 ≤ value && value ≤ 0x200A) ||
    value == 0x2028 || value == 0x2029 || value == 0x202F ||
    value == 0x205F || value == 0x3000

/-- Validated UTF-8 byte slicing equivalent to Rust `str::get`. -/
def utf8Slice? (source : String) (startByte endByte : Nat) : Option String :=
  if startByte ≤ endByte && endByte ≤ source.utf8ByteSize &&
      isUtf8Boundary source startByte && isUtf8Boundary source endByte then
    String.fromUTF8?
      (source.toByteArray.extract startByte endByte)
  else
    none

namespace Internals

def allRustWhitespace (text : String) : Bool :=
  text.toList.all isRustWhitespace

def lineBreakCountChars : List Char → Nat
  | [] => 0
  | '\r' :: '\n' :: rest => lineBreakCountChars rest + 1
  | '\r' :: rest | '\n' :: rest => lineBreakCountChars rest + 1
  | _ :: rest => lineBreakCountChars rest

end Internals

/-- Count CRLF as one break and lone CR/LF as one, exactly as upstream. -/
def lineBreakCount (text : String) : Nat :=
  Internals.lineBreakCountChars text.toList

namespace Internals

def lineStartByteAux :
    Nat → Nat → Nat → List Char → Nat
  | _, _, lastStart, [] => lastStart
  | limit, cursor, lastStart, character :: rest =>
      if cursor ≥ limit then
        lastStart
      else
        let next := cursor + character.utf8Size
        let updated :=
          if character == '\r' || character == '\n' then next else lastStart
        lineStartByteAux limit next updated rest

def lineStartByte (source : String) (limit : Nat) : Nat :=
  lineStartByteAux limit 0 0 source.toList

def gapHasCode (source : String)
    (startByte endByte : Nat) : Bool :=
  match utf8Slice? source startByte endByte with
  | some gap => !allRustWhitespace gap
  | none => true

def codeBeforeCommentAux (source : String)
    (lineStart targetStart : Nat) : List Comment → Nat → Bool
  | [], cursor => gapHasCode source cursor targetStart
  | previous :: rest, cursor =>
      if previous.span.startByte ≥ targetStart then
        gapHasCode source cursor targetStart
      else if previous.span.endByte ≤ cursor then
        codeBeforeCommentAux source lineStart targetStart rest cursor
      else if previous.span.startByte < lineStart ||
          previous.span.endByte > targetStart then
        codeBeforeCommentAux source lineStart targetStart rest cursor
      else if gapHasCode source cursor previous.span.startByte then
        true
      else
        codeBeforeCommentAux source lineStart targetStart rest
          previous.span.endByte

def commentHasCodeBeforeItOnLine (source : String)
    (comments : List Comment) (comment : Comment)
    (allowedLinePrefixEnd : Option Nat := none) : Bool :=
  let lineStart := lineStartByte source comment.span.startByte
  let cursor := match allowedLinePrefixEnd with
    | some endByte =>
        if lineStart ≤ endByte && endByte ≤ comment.span.startByte then
          endByte
        else
          lineStart
    | none => lineStart
  codeBeforeCommentAux source lineStart comment.span.startByte
    comments cursor

def attachBeforeAux (source : String) (allComments : List Comment)
    (allowedLinePrefixEnd : Option Nat) :
    Nat → List Comment → List Comment → List Comment
  | _, [], attached => attached
  | cursor, comment :: rest, attached =>
      match utf8Slice? source comment.span.endByte cursor with
      | none => attached
      | some gap =>
          if !allRustWhitespace gap || lineBreakCount gap > 1 ||
              commentHasCodeBeforeItOnLine source allComments comment
                allowedLinePrefixEnd then
            attached
          else
            attachBeforeAux source allComments allowedLinePrefixEnd
              comment.span.startByte rest (comment :: attached)

def commentsDirectlyBeforeSince (source : String)
    (comments : List Comment) (declarationStart minimumStart : Nat)
    (allowedLinePrefixEnd : Option Nat) : List Comment :=
  let candidates := (comments.filter fun comment =>
    minimumStart ≤ comment.span.startByte &&
      comment.span.endByte ≤ declarationStart).reverse
  attachBeforeAux source comments allowedLinePrefixEnd declarationStart
    candidates []

end Internals

/-- Consecutive source comments directly documenting a declaration. -/
def commentsDirectlyBefore (source : String) (comments : List Comment)
    (declarationStart : Nat) : List Comment :=
  Internals.commentsDirectlyBeforeSince source comments declarationStart 0 none

namespace Internals

def commentsDirectlyAfterIntroducer (source : String)
    (comments : List Comment) (introducer : SourceSpan)
    (declarationStart : Nat) : List Comment :=
  commentsDirectlyBeforeSince source comments declarationStart
    introducer.endByte (some introducer.endByte)

def commentCoversByte (comments : List Comment)
    (offset : Nat) : Bool :=
  comments.any fun comment =>
    comment.span.startByte ≤ offset && offset < comment.span.endByte

def findSeparatorComma (source : String) (comments : List Comment)
    (sourceId : SourceId) (startByte endByte : Nat) : Option SourceSpan :=
  if startByte ≤ endByte then
    (List.range (endByte - startByte)).find? (fun delta =>
      let offset := startByte + delta
      source.toByteArray.data[offset]? == some (0x2c : UInt8) &&
        !commentCoversByte comments offset)
    |>.map fun delta => {
      source := sourceId
      startByte := startByte + delta
      endByte := startByte + delta + 1
    }
  else
    none

theorem attachBeforeAux_mem_of_mem
    (source : String) (allComments : List Comment)
    (allowedLinePrefixEnd : Option Nat) :
    ∀ candidates cursor attached,
      (∀ comment ∈ candidates, comment ∈ allComments) →
      (∀ comment ∈ attached, comment ∈ allComments) →
      ∀ comment ∈ attachBeforeAux source allComments allowedLinePrefixEnd
        cursor candidates attached,
        comment ∈ allComments := by
  intro candidates
  induction candidates with
  | nil =>
      intro cursor attached candidatesSubset attachedSubset comment member
      exact attachedSubset comment (by simpa [attachBeforeAux] using member)
  | cons head rest inductionHypothesis =>
      intro cursor attached candidatesSubset attachedSubset comment member
      unfold attachBeforeAux at member
      cases slice : utf8Slice? source head.span.endByte cursor with
      | none =>
          exact attachedSubset comment (by simpa [slice] using member)
      | some gap =>
          simp only [slice] at member
          split at member
          · exact attachedSubset comment member
          · apply inductionHypothesis head.span.startByte (head :: attached)
            · intro retained retainedMember
              exact candidatesSubset retained (List.mem_cons_of_mem head
                retainedMember)
            · intro retained retainedMember
              rcases List.mem_cons.mp retainedMember with retainedEq | priorMember
              · exact candidatesSubset retained (by simp [retainedEq])
              · exact attachedSubset retained priorMember
            · exact member

theorem commentsDirectlyBeforeSince_mem (source : String)
    (comments : List Comment) (declarationStart minimumStart : Nat)
    (allowedLinePrefixEnd : Option Nat)
    {comment : Comment}
    (member : comment ∈ commentsDirectlyBeforeSince source comments
      declarationStart minimumStart allowedLinePrefixEnd) :
    comment ∈ comments := by
  unfold commentsDirectlyBeforeSince at member
  apply attachBeforeAux_mem_of_mem source comments allowedLinePrefixEnd
    ((comments.filter fun retained =>
      minimumStart ≤ retained.span.startByte &&
        retained.span.endByte ≤ declarationStart).reverse)
    declarationStart []
  · intro retained retainedMember
    have filteredMember : retained ∈ comments.filter fun candidate =>
        minimumStart ≤ candidate.span.startByte &&
          candidate.span.endByte ≤ declarationStart := by
      simpa using retainedMember
    exact (List.mem_filter.mp filteredMember).1
  · simp
  · exact member

end Internals

/-- Every comment selected for a declaration comes from the supplied stream. -/
theorem commentsDirectlyBefore_mem (source : String)
    (comments : List Comment) (declarationStart : Nat)
    {comment : Comment}
    (member : comment ∈ commentsDirectlyBefore source comments
      declarationStart) :
    comment ∈ comments := by
  exact Internals.commentsDirectlyBeforeSince_mem source comments
    declarationStart 0 none member

namespace Internals

theorem commentsDirectlyAfterIntroducer_mem (source : String)
    (comments : List Comment) (introducer : SourceSpan)
    (declarationStart : Nat) {comment : Comment}
    (member : comment ∈ commentsDirectlyAfterIntroducer source comments
      introducer declarationStart) :
    comment ∈ comments := by
  exact commentsDirectlyBeforeSince_mem source comments declarationStart
    introducer.endByte (some introducer.endByte) member

end Internals

end Solcore.Syntax.Trivia

/-!
## Consolidated module: `Solcore.Syntax.TriviaAttachment`
-/

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
