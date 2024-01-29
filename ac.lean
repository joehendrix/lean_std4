import Std.Tactic.Omega
import Lean

namespace Option

def getWith (x : Option α) (some : α -> β) (none : Unit → β) : β :=
  match x with
  | .some x => some x
  | .none => none ()

end Option

inductive POption (P : Prop) : Prop where
  | some : P → POption P
  | none : POption P


def Const := String

def Var := String

#print Lean.Expr

inductive Expr
| app : Expr → Expr → Expr
| const : Const → Expr
| fvar : Var → Expr
| bvar : Nat → Expr

structure ConstInfo where
  -- Arguments to const before binary operator.
  patterns : List Expr := []
  assoc : Bool := .false
  comm  : Bool := .false
  idem  : Bool := .false
  left_ident : Option Expr := .none
  right_ident : Option Expr := .none
  comm_ident : comm → left_ident = right_ident := by simp

--instance : EmptyCollection ConstInfo where
--  emptyCollection := {}


structure Sig where
  eqs : Const → Option ConstInfo

/-
namespace Sig
def info (s:Sig) (f : Expr) : Option ConstInfo :=
  match f with
  | .const c => s.eqs c
  | _ => .none


def is_assoc (s:Sig) (f : Expr) : Bool := s.info f |> .getWith (·.assoc) (fun () => .false)
def is_comm (s:Sig) (f : Expr) : Bool := (s.info f).comm
def is_idem (s:Sig) (f : Expr) : Bool := (s.info f).idem
def left_ident (s:Sig) (f : Expr) : Option Expr := (s.info f).left_ident
def right_ident (s:Sig) (f : Expr) : Option Expr := (s.info f).right_ident

end Sig
-/

namespace Expr

instance : CoeFun Expr (fun _ => Expr → Expr) where
  coe := .app

@[reducible] def Subst := Array Expr

def apply (e : Expr) (s : Subst) : Expr :=
  match e with
  | .bvar idx =>
    if p : idx < s.size then
      have _ : Array.size s - 1 - idx < Array.size s := by omega
      s[s.size - 1 - idx]
    else
      .bvar (idx - s.size)
  | .const c => .const c
  | .fvar v => .fvar v
  | .app f x => .app (apply f s) (apply x s)

def appN (e : Expr) (args : List Expr) : Expr := List.foldl .app e args

@[reducible] def MatchConstInfo (s:Sig) (f : Expr) (cinfo : ConstInfo) :=
  ∃(c : Const) (params : List Expr) (subst : Subst),
    f = appN (.const c) params
    ∧ s.eqs c = .some cinfo
    ∧ cinfo.patterns.map (apply · subst) = params

inductive Eq (s:Sig) : Expr → Expr → Prop
| rfl (x : Expr) : Eq s x x
| symm {x y : Expr} : Eq s y x → Eq s x y
| trans {x y z : Expr} : Eq s x y → Eq s y z → Eq s x z
| congr {f x g y : Expr} : Eq s f g → Eq s x y → Eq s (f x) (g y)
| assoc {f x y z : Expr} (cinfo : ConstInfo) : MatchConstInfo s f cinfo → cinfo.assoc → Eq s (f (f x y) z) (f x (f y z))
| comm  {f x y : Expr} (cinfo : ConstInfo) : MatchConstInfo s f cinfo → cinfo.comm →  Eq s (f y x) (f x y)
| idem  {f x : Expr} (cinfo : ConstInfo) : MatchConstInfo s f cinfo → cinfo.idem →  Eq s (f x x) x
| left_ident  {f x o : Expr} (cinfo : ConstInfo) : MatchConstInfo s f cinfo → cinfo.left_ident  = .some o → Eq s (f o x) x
| right_ident {f x o : Expr} (cinfo : ConstInfo) : MatchConstInfo s f cinfo → cinfo.right_ident = .some o → Eq s (f x o) x

end Expr


inductive FlatExpr where
| free_app : FlatExpr → FlatExpr → FlatExpr
-- `bin_app c params args` denotes an a binary operator.
-- There should be at least two arguments and the parameters are fixed
-- for all applications.
| bin_app : Const → Array FlatExpr → Array FlatExpr → FlatExpr
| const : Const → FlatExpr
| fvar : Var → FlatExpr


def flatten (s : Sig) (e : Expr) : FlatExpr :=
  match e with
  | .app (.app f x) y =>
    let finfo := s.info f
    sorry
  | _ => .free e



def check (sig : Sig) (x y : Expr) : POption (Eq sig x y) := by
  match x, y with
  | .app (.app f x0) x1, .app (.app g y0) y1 =>

  admit

#print Eq.rfl

end Expr

inductive PreExpr (op : Expr) ()

private inductive PreExpr
| op (op : Op) (lhs rhs : PreExpr)
| var (e : Expr)

private inductive PreExpr
| op (lhs rhs : PreExpr)
| var (e : Expr)
