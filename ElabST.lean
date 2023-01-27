import Lean
import Init.Data.Nat
import Init.Data.String
import Init.Data.Fin

namespace CoC open CoC

set_option pp.proofs true
set_option linter.unusedVariables false

abbrev Name := String
abbrev Level := Nat
notation " let " x " := " a " in " e => let x := a ; e
infix : 50 " ⊔ " => Nat.max

inductive Term : Type where
  | type (l : Level) 
  | var (x : Name)
  | app (f: Term) (a: Term)
  | pi (v : Name) (vty : Term) (pty : Term) 
  | lam (v : Name) (vty : Term) (e : Term)

open Term
notation "(" a " : " A ")'" " -> " e => pi a A e
notation "λ' " a " : " A " => " e => lam a A e

open Lean

#reduce (λ x : Nat => (λ (y : Nat) (x : Bool) => y) x)

def freev : Term -> Name -> Bool
  | type _ , _ => false
  | var x , n => x == n
  | app f a , n => freev f n || freev a n 
  | pi x t e , n => freev t n || (x != n && freev e n)
  | lam x t e , n => freev t n || (x != n && freev e n)

notation e "[" a "]ₜ?" => freev e a

def boundv (t : Term)(n : Name) : Bool :=
  match t with
  | (a : A)' -> B => a == n || boundv A n || boundv B n
  | λ' a : A => B => a == n || boundv A n || boundv B n
  | app f a => boundv f n || boundv a n
  | _ => false

notation e "[" a "]'?"  => boundv e a

theorem bool_or_efalse : (a || b) = false -> a = false /\ b = false := by
  intro p 
  cases a ; all_goals cases b
  constructor; rfl; rfl
  all_goals simp at p

theorem boundv_th₁ : ((a : A)' -> B)[n]'? = false -> A[n]'? = false /\ B[n]'? = false := by
  intro p 
  unfold boundv at p
  have f := bool_or_efalse p ; cases f ; case intro z x => {
  have g := bool_or_efalse z ;
  cases g ;
  case intro z y => {
    apply And.intro ;
    exact y ; 
    exact x
  }
  } 

-- #print boundv_th₁

theorem boundv_th₂ : (lam a A B)[n]'? = false -> A[n]'? = false /\ B[n]'? = false := by
  intro p 
  unfold boundv at p
  have f := bool_or_efalse p ; cases f ; case intro z x => {
  have g := bool_or_efalse z ;
  cases g ;
  case intro z y => {
    apply And.intro ;
    exact y ; 
    exact x
  }
  }

theorem boundv_th₃ : (app f a)[n]'? = false -> f[n]'? = false /\ a[n]'? = false := by
  intro p 
  unfold boundv at p 
  exact bool_or_efalse p 

def substn (t : Term)(n m : Name){p : boundv t m = false} :=
  match t with
  | type _ => t
  | var x => bif x == n then var m else t
  | app f a => app (@substn f n m (boundv_th₃ p).1) (@substn a n m (boundv_th₃ p).2)
  | pi a A B => pi a (@substn A n m (boundv_th₁ p).1) (bif a == n then B else @substn B n m (boundv_th₁ p).2)
  | lam a A B => lam a (@substn A n m (boundv_th₁ p).1) (bif a == n then B else @substn B n m (boundv_th₁ p).2)


def depth : Term -> Nat -- rec depth
  | type _ => 0
  | var _ => 0
  | app f a => (depth f ⊔ depth a) + 1
  | pi _ A e => (depth A ⊔ depth e) + 1
  | lam _ A e => (depth A ⊔ depth e) + 1

def deplt : Term -> Term -> Prop := InvImage Nat.lt depth

def depacc : Acc deplt t := InvImage.accessible depth (Nat.lt_wfRel.wf.apply (depth t))

def depwf : WellFounded deplt := ⟨ @depacc ⟩

def dep_wfRel : WellFoundedRelation Term where
  rel := deplt
  wf  := depwf

def depsn {p} : depth (@substn t n m p) = depth t := by
  cases t 
  any_goals (unfold depth ; unfold substn ; simp)
  case var x => (
    generalize h : (x == n) = a
    cases a
    all_goals simp
  )
  case app f a => (
    have g₁ := depsn (t := f) (n := n) (m := m) (p := (boundv_th₃ p).1)
    have g₂ := depsn (t := a) (n := n) (m := m) (p := (boundv_th₃ p).2)
    rw [g₁ , g₂]
  )
  case pi a A e => (
    have g₁ := depsn (t := A) (n := n) (m := m) (p := (boundv_th₁ p).1)
    rw [g₁]
    generalize h : (a == n) = b
    cases b 
    case true => simp 
    case false => (
      simp
      have g₁ := depsn (t := e) (n := n) (m := m) (p := (boundv_th₁ p).2)
      rw [g₁]
    )
  )
  case lam a A e => (
    have g₁ := depsn (t := A) (n := n) (m := m) (p := (boundv_th₁ p).1)
    rw [g₁]
    generalize h : (a == n) = b
    cases b 
    case true => simp 
    case false => (
      simp
      have g₁ := depsn (t := e) (n := n) (m := m) (p := (boundv_th₁ p).2)
      rw [g₁]
    )
  )

notation t "[" n " => " m "]'" => substn t n m 

-- #eval (pi "c" (type 1) (var "b"))["b" => "c"]'
#reduce (("c" : type 1)' -> var "b")["c"]'?

def freshb (e : Term) : Name :=
  match e with 
  | type _ => "x"
  | var _ => "x"
  | app f a => freshb f ++ freshb a
  | pi a A e => a ++ freshb A ++ freshb e
  | lam a A e => a ++ freshb A ++ freshb e

theorem freshb_th₁ : t[freshb t]'? = false := by
  cases t
--  any_goals 
  case type _ => rfl 
  case var _ => rfl
  case app f a => sorry
  admit
  admit

def freshst (m e : Term) : Name := by sorry

theorem freshst_th₁ : m[freshst m e]ₜ? = false := by sorry

theorem freshst_th₂ : e[freshst m e]'? = false := by sorry

theorem maxlt : a < ((a ⊔ b) + 1) := by sorry

theorem deplt_th₁₁ : deplt f (app f a) := by sorry

theorem deplt_th₁₂ : deplt a (app f a) := by sorry

theorem deplt_th₂₁ : deplt A (pi a A e) := by sorry

theorem deplt_th₂₂ : deplt (@substn e a z p) ((a : A)' -> e) := by sorry

theorem deplt_th₂₃ :   deplt e ((a : A)' -> e) := by sorry

theorem deplt_th₃₁ : deplt A (lam a A e) := by sorry

theorem deplt_th₃₂ : deplt (@substn e a z p) (lam a A e) := by sorry

theorem deplt_th₃₃ :   deplt e (lam a A e) := by sorry

-- set_option pp.instances false

def subst (t : Term)(n : Name)(m : Term) : Term :=
  match t with
  | type _ => t
  | var x => bif x == n then m else t
  | app f a => app (subst f n m) (subst a n m)
  | pi a A e => bif a == n then pi a (subst A n m) e 
    else bif e[n]ₜ? && m[a]ₜ? 
      then let z := freshst m e 
        in pi z (subst A n m) (subst (@substn e a z freshst_th₂) n m)
      else pi a (subst A n m) (subst e n m)
  | lam a A e => bif a == n then lam a (subst A n m) e 
    else bif e[n]ₜ? && m[a]ₜ? 
      then let z := freshst m e 
        in lam z (subst A n m) (subst (@substn e a z freshst_th₂) n m)
      else lam a (subst A n m) (subst e n m)
termination_by subst t _ _ => depth t 
decreasing_by {
  try apply deplt_th₁₁
  try apply deplt_th₁₂
  try apply deplt_th₂₂
}
notation e "[" a " => " m "]" => subst e a m

theorem subst_def : t[n => m] = match t with
  | type _ => t
  | var x => bif x == n then m else t
  | app f a => app (subst f n m) (subst a n m)
  | pi a A e => bif a == n then pi a (subst A n m) e 
    else bif e[n]ₜ? && m[a]ₜ? 
      then let z := freshst m e 
        in pi z (subst A n m) (subst (@substn e a z freshst_th₂) n m)
      else pi a (subst A n m) (subst e n m)
  | lam a A e => bif a == n then lam a (subst A n m) e 
    else bif e[n]ₜ? && m[a]ₜ? 
      then let z := freshst m e 
        in lam z (subst A n m) (subst (@substn e a z freshst_th₂) n m)
      else lam a (subst A n m) (subst e n m)
  := by
  cases t
  case type => simp ; rfl
  case var => simp ; rfl
  case app => simp ; rfl
  case pi => simp ; rfl
  case lam => simp ; rfl

theorem subst_th₁ : (type l)[n => m] = type l := rfl
theorem subst_th₂ : (var x)[n => m] = bif x == n then m else var x := rfl
theorem subst_th₃ : (app f a)[n => m] = app (f[n => m]) (a[n => m]) := rfl
theorem subst_th₄ : (pi a A e)[a => m] = pi a (A[a => m]) e := by 
  rw [subst_def]
  simp

-- #print subst #print subst._unary

def redcbl : Term -> Bool 
  | app (lam _ _ _) _ => true
  | app t@(app _ _) _ => redcbl t
  | _ => false

def betan1 : Term -> Term 
  | app (lam x t e) a => e[x => a]
  | app (app f b) a => app (betan1 (app f b)) a
  | t => t

set_option quotPrecheck false

notation a " ▹ " b => (betan1 a = b)

theorem beta_th₀ : (app (lam a A e) x) ▹ e[a => x] := by
  simp [betan1]

instance funpow : Pow (α -> α) Nat :=
⟨
  fun f => let rec ch (n : Nat) : α -> α :=
    match n with
    | 0  => id
    | i+1 => f ∘ (ch i)
  ch 
⟩ 

def funpow_add {f : A -> A}{m n : Nat} : (f ^ (m + n)) x = ((f ^ n) ((f ^ m) x)):= by
  induction n ; any_goals simp [HPow.hPow, Pow.pow, funpow.ch] at *
  case succ a p => rw [p]

def Betaeq (t₁ : Term)(t₂ : Term) : Type := 
  (m n : Nat) ×' ((betan1 ^ m) t₁) = ((betan1 ^ n) t₂)

notation t₁ " =ᵦ " t₂ => Betaeq t₁ t₂

notation a " :' " A => Prod.mk (α := Name) (β := Term) a A
notation : 67 xs ",, " x => List.cons x xs 

-- 
def ntin (n : Name) : List (Name × Term) -> Bool
  | [] => true
  | (x , _) :: xs => n != x && ntin n xs 

def TTrip := (List (Name × Term)) × Term × Term

inductive Typing : TTrip -> Type :=
  | rweak  : Typing (Γ, e, T)
          -> Typing (Γ, A, (type l))  
          -> {_ : ntin a Γ = true} 
          -> Typing (Γ,, a :' A, e, T)
  
  | rtype  : Typing ([], type l, type (l+1))
  
  | rvar   : Typing (Γ, A, type l) 
          -> {_ : ntin a Γ}
          -> Typing (Γ,, a :' A, var a, A)
  
  | rapp   : Typing (Γ, f, (x : A)' -> B) 
          -> Typing (Γ, a, A) 
          -> Typing (Γ, app f a, B[x => a])
  
  | rpi  : Typing (Γ, A, type l₁) 
          -> Typing (Γ,, a :' A, B, type l₂) 
          -> Typing (Γ, pi a A B, type (l₁ ⊔ l₂))
  
  | rlam   : Typing (Γ,, a :' A, b, B)
          -> Typing (Γ, pi a A B, type l)
          -> Typing (Γ, lam a A b, pi a A B)

  | rcnv   : Typing (Γ, a, A) 
          -> Typing (Γ, B, type l)
          -> {p : A =ᵦ B}
          -> Typing (Γ, a, B)

open Typing
notation Γ " ⊢ " e " : " T => Typing (Γ, e, T) 
-- 后面不能有"(...)"才能print
#print Term
#print Typing

inductive Vect (A : Type ℓ) : Nat -> Type _
  | nil : Vect A 0
  | cons (x : A)(xs : Vect A n) : Vect A (n + 1) 

def Targs (n : Nat)(A : Type)(T : Type ℓ) : Type _ :=
  match n with
  | 0 => T
  | n + 1 => A -> Targs n A T

def Dargs (n : Nat)(A : Type)(T : Targs n A (Type ℓ)) : Type (_) :=
  match n with
  | 0 => T 
  | m+1 => (a : A) -> (Dargs m A (T a))

variable (A : Type)(T : Targs 4 A Type) in
#reduce Dargs 4 A T 

structure ElabD :=
  ncgoal : Nat
  cgoals : Vect (Σ(n : Nat)(_ : Vect (Fin n) n), (Targs n Term TTrip)) ncgoal
  fngoal : Targs ncgoal Term TTrip
-- List.rec (Typing fngoal) (λ x xs tx => Typing x -> tx) cgoals

def Tcterm : ElabD -> Type _
  | ⟨ 0, Vect.nil, Tt⟩  => Typing Tt
  | ⟨ m+1, Vect.cons x xs, fg⟩  => 
  (h0 : Term) -> Typing (x h0) 

structure ElabST (dt : ElabD) :=
  cterm : Tcterm dt 

abbrev ElabM := StateT ElabST Option #reduce ElabM

def tintro (n : Name) : ElabM Unit := do 
  let st <- get
  match st with
  | ElabST.mk fgs cgl ctm => match cgl[0]? with 
  | none => failure
  | some ⟨ ctx , tm , ty ⟩ => _

#exit
  | none => pure
  | some (ElabST.mk fgs cgl ctm) => {}