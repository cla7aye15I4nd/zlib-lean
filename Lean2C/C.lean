import Lean

/-! Source-level C for the fixed LP64 model. Values carry their C type.
Memory operations and sequencing are explicit. -/
namespace Lean2C.CSource

inductive Ty where
  | void | bool | u8 | u16 | u32 | u64 | i32 | i64
  | named (spelling : String)
  | ptr (to : Ty)
  deriving BEq, Inhabited, Repr

def Ty.render : Ty → String
  | .void => "void" | .bool => "_Bool"
  | .u8 => "unsigned char" | .u16 => "unsigned short" | .u32 => "unsigned" | .u64 => "unsigned long"
  | .i32 => "int" | .i64 => "long"
  | .named spelling => spelling
  | .ptr t => t.render ++ " *"

inductive Value where
  | var (type : Ty) (name : String)
  | num (type : Ty) (value : Nat)
  | op (type : Ty) (operator : String) (left right : Value)
  | cast (type : Ty) (arg : Value)
  | record (type : Ty) (fields : List Value)
  | choose (condition yes no : Value)
  | load (type : Ty) (pointer : Value)
  | index (type : Ty) (pointer offset : Value)
  | field (type : Ty) (record : Value) (name : String)
  | postDec (place : Value)
  | preDec (place : Value)
  | addr (place : Value)
  | call (type : Ty) (name : String) (args : List Value)
  deriving Inhabited, BEq

def Value.type : Value → Ty
  | .var t _ | .num t _ | .op t .. | .cast t _ | .load t _ | .index t .. | .field t .. | .record t .. | .call t .. => t
  | .choose _ yes _ => yes.type
  | .postDec x | .preDec x => x.type
  | .addr x => .ptr x.type

partial def Value.render : Value → String
  | .var _ n => n
  | .num t n =>
    let suffix := if t == .u64 then "UL" else if t == .u32 then "U" else if t == .i64 then "L" else ""
    toString n ++ suffix
  | .op _ symbol a b => "(" ++ a.render ++ " " ++ symbol ++ " " ++ b.render ++ ")"
  | .cast t a => "((" ++ t.render ++ ")" ++ a.render ++ ")"
  | .record t xs => "((" ++ t.render ++ "){" ++ String.intercalate ", " (xs.map Value.render) ++ "})"
  | .choose c a b => "(" ++ c.render ++ " ? " ++ a.render ++ " : " ++ b.render ++ ")"
  | .load _ p => "(*" ++ p.render ++ ")"
  | .index _ p i => p.render ++ "[" ++ i.render ++ "]"
  | .field _ x name => "(" ++ x.render ++ ")." ++ name
  | .postDec x => "(" ++ x.render ++ "--)"
  | .preDec x => "(--" ++ x.render ++ ")"
  | .addr x => "(&" ++ x.render ++ ")"
  | .call _ n args => n ++ "(" ++ String.intercalate ", " (args.map Value.render) ++ ")"

private def condition (v : Value) : String :=
  match v with
  | .op .. | .choose .. | .load .. | .cast .. | .addr .. => v.render
  | _ => "(" ++ v.render ++ ")"

inductive Stmt where
  | decl (type : Ty) (name : String) (init : Option Value)
  | assign (place value : Value)
  | eval (value : Value)
  | ret (value : Value)
  | branch (cond : Value) (yes no : List Stmt)
  | doLoop (body : List Stmt) (cond : Value)
  | stop
  | loop (cond : Value) (body : List Stmt)
  deriving Inhabited

partial def renderStmts (ss : List Stmt) (depth : Nat) : String := Id.run do
  let indent := String.ofList (List.replicate (depth * 4) ' ')
  let mut out := ""
  for s in ss do
    let line := match s with
      | .decl t n init => t.render ++ " " ++ n ++ (init.map (" = " ++ ·.render)).getD "" ++ ";"
      | .assign p v => p.render ++ " = " ++ v.render ++ ";"
      | .eval v => v.render ++ ";"
      | .ret v => "return " ++ v.render ++ ";"
      | .branch c yes no =>
        let alt := if no.isEmpty then "" else " else {\n" ++ renderStmts no (depth + 1) ++ indent ++ "}"
        "if " ++ condition c ++ " {\n" ++ renderStmts yes (depth + 1) ++ indent ++ "}" ++ alt
      | .doLoop body c => "do {\n" ++ renderStmts body (depth + 1) ++ indent ++ "} while " ++ condition c ++ ";"
      | .stop => "break;"
      | .loop c body => "while " ++ condition c ++ " {\n" ++ renderStmts body (depth + 1) ++ indent ++ "}"
    out := out ++ indent ++ line ++ "\n"
  return out

def renderBody (ss : List Stmt) : String := "{\n" ++ renderStmts ss 1 ++ "}"

end Lean2C.CSource
