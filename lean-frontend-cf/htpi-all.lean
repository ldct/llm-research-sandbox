-- How to Prove It with Lean — Exercise Files
-- All 258 exercises from Chapters 3-8, with custom HTPILib library included
-- Source: https://github.com/djvelleman/HTPILeanPackage
-- Author: Daniel J. Velleman
-- Lean toolchain: leanprover/lean4:v4.26.0, Mathlib v4.26.0

set_option warningAsError false
set_option linter.style.longFile 0
set_option linter.unusedVariables false
set_option linter.unusedTactic false

-- ════════════════════════════════════════════════════════════════
-- HTPILib: Custom Library (prerequisite for exercises)
-- ════════════════════════════════════════════════════════════════

-- ──── HTPIDefs ────
/- Copyright 2023-2025 Daniel J. Velleman -/

--Make sure ring tactic doesn't give annoying warning about ring_nf
@[inherit_doc Mathlib.Tactic.RingNF.ring]
macro "ring" : tactic =>
  `(tactic| first | ring1 | ring_nf)

def Iff.ltr {p q : Prop} (h : p ↔ q) := h.mp
def Iff.rtl {p q : Prop} (h : p ↔ q) := h.mpr

--Make sure Lean understands {x} and ∅ as Sets, not Finsets
attribute [default_instance] Set.instSingletonSet
attribute [default_instance] Set.instEmptyCollection

-- Used in one exercise in Chapter 3.
notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)

--Note:  Mathlib.Order.SymmDiff.lean defines this, but it is scoped[symmDiff] there.
-- Use in one exercise in Chapter 3.
infixl:100 " ∆ " => symmDiff

namespace HTPI
--Some theorems not in library
theorem not_not_and_distrib {p q : Prop} : ¬(¬ p ∧ q) ↔ (p ∨ ¬ q) := by
  rw [not_and_or, Classical.not_not]

theorem not_and_not_distrib {p q : Prop} : ¬(p ∧ ¬ q) ↔ (¬ p ∨ q) := by
  rw [not_and_or, Classical.not_not]

theorem not_not_or_distrib {p q : Prop} : ¬(¬ p ∨ q) ↔ (p ∧ ¬ q) := by
  rw [not_or, Classical.not_not]

theorem not_or_not_distrib {p q : Prop} : ¬(p ∨ ¬ q) ↔ (¬ p ∧ q) := by
  rw [not_or, Classical.not_not]

theorem not_imp_not_iff_and {p q : Prop} : ¬ (p → ¬ q) ↔ p ∧ q := by
  rw [Classical.not_imp, Classical.not_not]

theorem not_imp_iff_not_and {p q : Prop} : ¬ (q → p) ↔ ¬ p ∧ q := by
  rw [Classical.not_imp]
  exact And.comm

theorem not_not_iff {p q : Prop} : ¬(¬p ↔ q) ↔ (p ↔ q) := by
  rw [not_iff, Classical.not_not]

def Pred (U : Type) : Type := U → Prop
def BinRel (U : Type) : Type := Rel U U

--Definitions of tactics
section tactic_defs
open Lean Elab Tactic Expr MVarId

--Syntax for arguments to tactics
syntax oneLoc := " at " ident
syntax colonTerm := " : " term
syntax withId := " with " ident
syntax with2Ids := " with " ident (", " ident)?
syntax idOrTerm := ident <|> ("(" term ")")
syntax idOrTerm?Type := ident <|> ("(" term (" : " term)? ")")

abbrev OneLoc := TSyntax ``oneLoc
abbrev ColonTerm := TSyntax ``colonTerm
abbrev WithId := TSyntax ``withId
abbrev With2Ids := TSyntax ``with2Ids
abbrev IdOrTerm := TSyntax ``idOrTerm
abbrev IdOrTerm?Type := TSyntax ``idOrTerm?Type

--Get formula from identifier
def formFromIdent (h : Syntax) : TacticM Expr := do
  instantiateMVars (← Meta.getLocalDeclFromUserName h.getId).type

--Get formula from optional location.  Note both formFromIdent and getMainTarget call instantiateMVars
def formFromLoc (l : Option OneLoc) : TacticM Expr := do
  match l with
    | some h => formFromIdent h.raw[1]
    | none => getMainTarget

--For debugging:
def myTrace (msg : String) : TacticM Unit := do
  let m := Syntax.mkStrLit msg
  evalTactic (← `(tactic| trace $m))

partial def SyntaxToString (s : Syntax) : String :=
match s with
  | .missing => "(missing)"
  | .node _ k as => "(node " ++ toString k ++ (SyntaxListToString as.toList) ++ ")"
  | .atom _ v => "(atom " ++ toString v ++ ")"
  | .ident _ rv v _ => "(ident " ++ (toString rv) ++ " " ++ (toString v) ++ ")"
where SyntaxListToString (ss : List Syntax) : String :=
  match ss with
    | (s :: rest) => " " ++ (SyntaxToString s) ++ (SyntaxListToString rest)
    | [] => ""

def traceThisSyntax (s : Syntax) : TacticM Unit := myTrace (SyntaxToString s)

def binderString (bi : BinderInfo) : String :=
  match bi with
    | .default => "default"
    | _ => "not default"

def ExprToString (e : Expr) : String :=
match e with
  | .bvar n => "(bvar " ++ (toString n) ++ ")" -- bound variables
  | .fvar f => "(fvar " ++ (toString f.name) ++ ")"  -- free variables
  | .mvar m => "(mvar " ++ (toString m.name) ++ ")"   -- meta variables
  | .sort l => "(sort " ++ (toString l) ++ ")"   -- Sort
  | .const n ls => "(const " ++ (toString n) ++ " " ++ (toString ls) ++ ")"   -- constants
  | .app a b => "(app " ++ (ExprToString a) ++ " " ++ (ExprToString b) ++ ")" -- application
  | .lam n t b bi => "(lam " ++ (toString n) ++ " " ++ (ExprToString t) ++ " " ++ (ExprToString b) ++ " " ++ (binderString bi) ++ ")"    -- lambda abstraction
  | .forallE n t b bi => "(forallE " ++ (toString n) ++ " " ++ (ExprToString t) ++ " " ++ (ExprToString b) ++ " " ++ (binderString bi) ++ ")"  -- (dependent) arrow
  | .letE n t v b _ => "(let " ++ (toString n) ++ " " ++ (ExprToString t) ++ " "
        ++ (ExprToString v) ++ " " ++ (ExprToString b) ++ ")" -- let expressions
  | .lit _ => "(lit)"  -- literals
  | .mdata m e => "(mdata " ++ (toString m) ++ " " ++ (ExprToString e) ++ ")"   -- metadata
  | .proj t i c => "(proj " ++ (toString t) ++ " " ++ (toString i) ++ " " ++ (ExprToString c) ++ ")" -- projection

def traceThisExpr (e : Expr) : TacticM Unit := myTrace (ExprToString e)

elab "traceExpr" t:(colonTerm)? l:(oneLoc)? : tactic =>
  withMainContext do
    match t with
      | some tstx => do
        traceThisSyntax tstx.raw[1]
        let e ← elabTerm tstx.raw[1] none
        traceThisExpr e
      | none =>
        let e ← formFromLoc l
        traceThisExpr e

-- This is stronger than e1 == e2: names of bound variables must match.
def identical (e1 e2 : Expr) : Bool :=
  let e2c := consumeMData e2
  match e1 with
    | .app a1 b1 => match e2c with
      | .app a2 b2 => (identical a1 a2) && (identical b1 b2)
      | _ => false
    | .lam n1 t1 b1 bi1 => match e2c with
      | .lam n2 t2 b2 bi2 => (n1 == n2) && (identical t1 t2) && (identical b1 b2) && (bi1 == bi2)
      | _ => false
    | .forallE n1 t1 b1 bi1 => match e2c with
      | .forallE n2 t2 b2 bi2 => (n1 == n2) && (identical t1 t2) && (identical b1 b2) && (bi1 == bi2)
      | _ => false
    | .letE n1 t1 v1 b1 nd1 => match e2c with
      | .letE n2 t2 v2 b2 nd2 => (n1 == n2) && (identical t1 t2) && (identical v1 v2) && (identical b1 b2) && (nd1 == nd2)
      | _ => false
    | .proj t1 i1 c1 => match e2c with
      | .proj t2 i2 c2 => (t1 == t2) && (i1 == i2) && (identical c1 c2)
      | _ => false
    | .mdata _ e => identical e e2c
    | _ => e1 == e2c

-- Get head and arg list
def getHeadData (e : Expr) : Expr × List Expr :=
  match e with
    | app f a =>
      let (h, as) := getHeadData f
      (h, a :: as)
    | mdata _ e' => getHeadData e'
    | _ => (e, [])

-- Recover expression from head and arg list
def mkAppList (h : Expr) (args : List Expr) : Expr :=
  match args with
    | a :: rest => mkApp (mkAppList h rest) a
    | [] => h

--Determine if e is a proposition, in current local context
def exprIsProp (e : Expr) : TacticM Bool :=
  return (← instantiateMVars (← Meta.inferType e)).isProp

--Logical form of a proposition.
inductive PropForm where
  | not     : Expr → PropForm
  | and     : Expr → Expr → PropForm
  | or      : Expr → Expr → PropForm
  | implies : Expr → Expr → PropForm
  | iff     : Expr → Expr → PropForm
  | all     : Name → Expr → Expr → BinderInfo → PropForm
  | ex      : Level → Name → Expr → Expr → BinderInfo → PropForm
  | exun    : Level → Name → Expr → Expr → BinderInfo → PropForm
  | f       : PropForm
  | t       : PropForm
  | none    : PropForm

/- Try to unfold definition, and if result is negative, return PropForm.not
Note:  Uses constants but not fvars with let declarations.  Also, only unfolds once.
This might be best--only detect expressions immediately recognized as negative by def.
-/
def findNegPropAll (e : Expr) : TacticM PropForm := do
  match (← Meta.unfoldDefinition? (consumeMData e)) with
    | some e' =>
      match getHeadData e' with
        | (const ``Not _, [l]) => return PropForm.not l
        | _ => return PropForm.none
    | none => return PropForm.none

--Apply a function to data for an existential.  Existentials usually apply to a
--lambda expression, but allow for others
def applyToExData {α : Type} (f : Level → Name → Expr → Expr → BinderInfo → α)
  (lev : Level) (l r : Expr) : α :=
  let r' := consumeMData r
  match r' with
    | lam v t b bi => f lev v t b bi
    | _ => f lev `x l (mkApp r' (bvar 0)) BinderInfo.default

-- Get logical form of a proposition.
-- Recognizes negative predicates by findNegPropAll.
def getPropForm (e : Expr) : TacticM PropForm := do
  if !(← exprIsProp e) then return PropForm.none
  let (h, args) := getHeadData e
  match h with
    | const c levs =>
      match (c, levs, args) with
        | (``False, _, _) => return PropForm.f
        | (``True, _, _) => return PropForm.t
        | (``Not, _, [l]) => return PropForm.not l
        | (``And, _, [r, l]) => return PropForm.and l r
        | (``Or, _, [r, l]) => return PropForm.or l r
        | (``Iff, _, [r, l]) => return PropForm.iff l r
        | (``Exists, [lev], [r, l]) => return applyToExData PropForm.ex lev l r
        | (``ExistsUnique, [lev], [r, l]) => return applyToExData PropForm.exun lev l r
        | _ => findNegPropAll e
    | forallE v t b bi =>
      if (b.hasLooseBVars || !(← exprIsProp t)) then
        return PropForm.all v t b bi
      else
        return PropForm.implies t b
    | _ => return PropForm.none

--mkNot, mkAnd, mkOr, and mkForall are already defined.  Also mkArrow and Meta.mkEq
def mkIff (l r : Expr) : Expr :=
  mkApp2 (mkConst ``Iff) l r

--Need to supply level--I always have it, so easiest to use it.
def mkExists (l : Level) (x : Name) (bi : BinderInfo) (t b : Expr) : Expr :=
  mkApp2 (mkConst ``Exists [l]) t (mkLambda x bi t b)

def myFail {α} (tac : Name) (msg : String) : TacticM α := do
  Meta.throwTacticEx tac (← getMainGoal) msg

/- Functions for unfolding head -/

--Unfold ExistsUnique; default version doesn't do a good job of naming variables
def unfoldExUn (lev : Level) (v : Name) (t b : Expr) (_ : BinderInfo) : Expr :=
  let v1 := Name.appendIndexAfter v 1
  let eqn := mkApp3 (mkConst ``Eq [lev]) t (bvar 1) (bvar 2)
  let body := mkAnd b (mkForall v1 BinderInfo.default t (mkForall `x BinderInfo.default b eqn))
  mkExists lev v BinderInfo.default t body

-- Constants not to unfold except if explicitly asked to
def dontUnfold : List Name := [``ite, ``dite]
def dontUnfoldNum : List Name := [``LT.lt, ``LE.le, ``GT.gt, ``GE.ge]
def numNames : List Name := [``Nat, ``Int, ``_root_.Rat, ``Real]

/- Unfold head in current context--must set local context before call.
If first = true, then unfold ExistsUnique using my def; else don't unfold it.
Also, if first = true, then unfold constants in list dontUnfold; otherwise don't.
If rep = true, unfold repeatedly.
Let whnfCore handle everything except unfolding of constants.
Do all normalization up to first unfolding of a definition; on next call do that unfolding
-/
def fixElt (e : Expr) (doFix : Bool) : TacticM Expr := do
  if doFix then
    match e with  --if e is "set elt", change to "elt ∈ set"
      | app st elt =>
        let tp ← instantiateMVars (← Meta.inferType st)
        match tp with
          | app (const ``Set [lev]) t =>
            let ststx ← st.toSyntax
            let eltstx ← elt.toSyntax
            let tm ← `(term| $eltstx ∈ $ststx)
            return (← elabTerm tm (mkSort levelZero))
/-  Previous version, depends on underlying rep. of membership expression
            return (mkApp5 (mkConst ``Membership.mem [lev, lev])
              t
              (mkApp (mkConst ``Set [lev]) t)
              (mkApp (mkConst ``Set.instMembership [lev]) t)
              st
              elt)
-/
          | _ => return e
      | _ => return e
  else
    return e

--Unfold if possible, else return input.  Input should have no MData.
partial def unfoldHeadCore (e : Expr) (first rep : Bool) : TacticM Expr := do
  match e with  --Don't unfold {x | p} if not applied to anything
    | (app (app (const ``setOf _) _) _) => return e
    | _ => pure ()
  let (h, args) := getHeadData e
  -- First let e1 = result of one unfolding, or handle negation, or return e
  let e1 ← match h with
    | const c levs =>
      match (c, levs, args) with
        | (``Not, _, [l]) => return mkNot (← unfoldHeadCore (consumeMData l) first rep)
        | (``ExistsUnique, [lev], [r, l]) =>
          if first then
            pure (applyToExData unfoldExUn lev l r)
          else
            return e
        | _ =>
          if !first then
            if c ∈ dontUnfold then
              return e
            if c ∈ dontUnfoldNum then
              match args[3]! with
                | const nc _ => if nc ∈ numNames then return e
                | _ => pure ()
          let edo ← Meta.unfoldDefinition? e
          match edo with
            | some ed => pure ed
            | none => return (← fixElt e rep)
    | _ =>
      let ew ← Meta.whnfCore e
      if ew == e then
        return (← fixElt e rep)
      else
        pure ew
  if rep then
    return (← unfoldHeadCore (consumeMData e1) false true)
  else
    return e1

def unfoldHead (e : Expr) (tac : Name) (first rep : Bool) : TacticM Expr := do
  let e1 := consumeMData e
  let e2 ← unfoldHeadCore e1 first rep
  if e2 == e1 then
    myFail tac "failed to unfold definition"
  else
    return e2

-- whnf, but don't unfold ``ExistsUnique
def whnfNotExUn (e : Expr) : TacticM Expr :=
  Meta.whnfHeadPred e (fun x => return !(x.isAppOf ``ExistsUnique))

-- w = 0 : no whnf, w = 1 : whnfNotExun, w = 2 : full whnf
def exprFromPf (t : Term) (w : Nat) : TacticM Expr := do
  let p ← elabTerm t none
  let e ← instantiateMVars (← Meta.inferType p)
  match w with
    | 0 => return e
    | 1 => whnfNotExUn e
    | _ => Meta.whnf e

--Add new hypothesis with name n, asserting form, proven by pfstx.
def doHave (n : Name) (form : Expr) (pfstx : Syntax) : TacticM Unit := do
  let goal ← getMainGoal
  let oldtar ← getType goal
  let pf ← elabTermEnsuringType pfstx form
  let mvarIdNew ← assert goal n form pf
  let (_, newGoal) ← intro1P mvarIdNew    --blank is FVarId of new hyp.
  let newtar ← getType newGoal
  if (oldtar != newtar) && (← Meta.isExprDefEq oldtar newtar) then
    --intro1P sometimes changes target to something def. equal.  Put it back to original
    replaceMainGoal [← newGoal.replaceTargetDefEq oldtar]
  else
    replaceMainGoal [newGoal]

--Set goal to be form; pfstx is proof that it suffices.
def doSuffices (form : Expr) (pfstx : Syntax) : TacticM Unit := do
  let goal ← getMainGoal
  let tag ← getTag goal
  let target ← getType goal
  let imp ← mkArrow form target
  let pf ← elabTermEnsuringType pfstx imp
  let newTarget ← Meta.mkFreshExprSyntheticOpaqueMVar form tag
  assign goal (mkApp pf newTarget)
  replaceMainGoal [newTarget.mvarId!]

--Do rewrite; symm says whether to reverse direction, rule is Term for rule, l is optional location
def doRewrite (symm : Bool) (rule : Term) (l : Option OneLoc) : TacticM Unit := do
  match l with
    | some id =>
        let idstx : Ident := ⟨id.raw[1]⟩
        if symm then
          evalTactic (← `(tactic| rewrite [← $rule:term] at $idstx:ident))
        else
          evalTactic (← `(tactic| rewrite [$rule:term] at $idstx:ident))
    | none =>
        if symm then
          evalTactic (← `(tactic| rewrite [← $rule:term]))
        else
          evalTactic (← `(tactic| rewrite [$rule:term]))

--Swap first two goals, if there are at least two
def doSwap : TacticM Unit := do
  let g ← getGoals
  let ng := match g with
    | g1 :: (g2 :: rest) => g2 :: (g1 :: rest)
    | _ => g
  setGoals ng

/- Functions for all equivalence tactics: contrapos, demorgan, quant_neg, conditional, double_neg -/
def ruleType := Name × Expr

def equivMakeRule (f : Expr)
  (ruleFunc : Expr → TacticM ruleType) : TacticM ruleType := do
  let (rule, res) ← ruleFunc f
  return (rule, mkIff f res)

def equivRuleFromForm (p : Expr)
  (ruleFunc : Expr → TacticM ruleType) : TacticM ruleType := do
    try
      equivMakeRule p ruleFunc
    catch ex =>
      match (← getPropForm p) with
        | PropForm.iff l r =>
          try
            equivMakeRule l ruleFunc
          catch _ =>
            equivMakeRule r ruleFunc
        | _ => throw ex

def equivRule (f : Option ColonTerm) (l : Option OneLoc)
  (ruleFunc : Expr → TacticM ruleType) : TacticM ruleType := do
  match f with
    | some fs => equivMakeRule (← elabTerm fs.raw[1] none) ruleFunc
    | none => equivRuleFromForm (← formFromLoc l) ruleFunc

def doReplace (tac : Name) (l : Option OneLoc) (res : Expr) (pf : Syntax) : TacticM Unit := do
    let hn ← mkFreshUserName `h
    doHave hn res pf
    let h := mkIdent hn
    let ht : Term := ⟨h.raw⟩
    try
      doRewrite false ht l
      evalTactic (← `(tactic| clear $h:ident)) -- Could also do: (try apply Iff.refl); try assumption
    catch _ =>
      evalTactic (← `(tactic| clear $h:ident))
      myFail tac  "target expression not found"

def doEquivTac (f : Option ColonTerm) (l : Option OneLoc)
  (tac : Name) (ruleFunc : Expr → TacticM ruleType) : TacticM Unit :=
  withMainContext do
    let (rule, res) ← equivRule f l ruleFunc
    doReplace tac l res (mkIdent rule)

/- contrapos tactic -/
def cpRule (form : Expr) : TacticM ruleType := do
  match (← getPropForm form) with
    | PropForm.implies l r => match (← getPropForm l) with
      | PropForm.not nl => match (← getPropForm r) with
        | PropForm.not nr =>
          return (`not_imp_not, (← mkArrow nr nl))
        | _ =>
          return (`not_imp_comm, (← mkArrow (mkNot r) nl))
      | _ => match (← getPropForm r) with
        | PropForm.not nr =>
          return (`imp_not_comm, (← mkArrow nr (mkNot l)))
        | _ =>
          return (`not_imp_not.symm, (← mkArrow (mkNot r) (mkNot l)))
    | _ => myFail `contrapos "contrapositive law doesn't apply"

elab "contrapos" f:(colonTerm)? l:(oneLoc)? : tactic => doEquivTac f l `contrapos cpRule

/- demorgan tactic -/
def dmRuleFromInfoNoNeg (l r : Expr) (conn : Expr → Expr → Expr) (rs : Array Name) : TacticM ruleType := do
  match (← getPropForm l) with
  | PropForm.not nl =>
      match (← getPropForm r) with
        | PropForm.not nr => return (rs[0]!, conn nl nr)
        | _ => return (rs[1]!, conn nl (mkNot r))
  | _ =>
      match (← getPropForm r) with
        | PropForm.not nr => return (rs[2]!, conn (mkNot l) nr)
        | _ => return (rs[3]!, conn (mkNot l) (mkNot r))

def dmRuleFromInfo (l r : Expr) (conn : Expr → Expr → Expr) (n : Bool) (rs : Array Name) : TacticM ruleType := do
  let p ← dmRuleFromInfoNoNeg l r conn rs
  if n then
    return (p.1, mkNot p.2)
  else
    return p

def dmRule (form : Expr) : TacticM ruleType := do
  match (← getPropForm form) with
    | PropForm.not a => match (← getPropForm a) with
      | PropForm.and l r =>
        dmRuleFromInfo l r mkOr false
          #[`or_iff_not_and_not.symm, `HTPI.not_not_and_distrib, `HTPI.not_and_not_distrib, `not_and_or]
      | PropForm.or l r =>
        dmRuleFromInfo l r mkAnd false
          #[`and_iff_not_or_not.symm, `HTPI.not_not_or_distrib, `HTPI.not_or_not_distrib, `not_or]
      | _ => myFail `demorgan "De Morgan's laws don't apply"
    | PropForm.and l r =>
        dmRuleFromInfo l r mkOr true
          #[`not_or.symm, `HTPI.not_or_not_distrib.symm, `HTPI.not_not_or_distrib.symm, `and_iff_not_or_not]
    | PropForm.or l r =>
      dmRuleFromInfo l r mkAnd true
        #[`not_and_or.symm, `HTPI.not_and_not_distrib.symm, `HTPI.not_not_and_distrib.symm, `or_iff_not_and_not]
    | _ => myFail `demorgan "De Morgan's laws don't apply"

elab "demorgan" f:(colonTerm)? l:(oneLoc)? : tactic => doEquivTac f l `demorgan dmRule

/- quant_neg tactic -/
def qnRuleFromInfoNoNeg (v : Name) (t b : Expr) (qf : Name → BinderInfo → Expr → Expr → Expr)
  (rs : Name × Name) : TacticM ruleType := do
  let f := mkLambda `x BinderInfo.default t b
  let negres ← Meta.lambdaTelescope f fun fvs e => do
    match (← getPropForm e) with
      | PropForm.not ne => return some (← Meta.mkLambdaFVars fvs ne)
      | _ => return none
  match negres with
    | some ne => match ne with
      | lam _ _ nb _ => return (rs.1, qf v BinderInfo.default t nb)
      | _ => return (rs.2, qf v BinderInfo.default t (mkNot b))
    | none => return (rs.2, qf v BinderInfo.default t (mkNot b))

def qnRuleFromInfo (v : Name) (t b : Expr) (qf : Name → BinderInfo → Expr → Expr → Expr)
  (n : Bool) (rs : Name × Name) : TacticM ruleType := do
  let p ← qnRuleFromInfoNoNeg v t b qf rs
  if n then
    return (p.1, mkNot p.2)
  else
    return p

def qnRule (form : Expr) : TacticM ruleType := do
  match (← getPropForm form) with
    | PropForm.not p => match (← getPropForm p) with
      | PropForm.all v t b _ =>
        qnRuleFromInfo v t b (mkExists (← Meta.getLevel t)) false
          (`not_forall_not, `not_forall)
      | PropForm.ex _ v t b _ =>
        qnRuleFromInfo v t b mkForall false
          (`not_exists_not, `not_exists)
      | _ => myFail `quant_neg "quantifier negation laws don't apply"
    | PropForm.all v t b _ =>
      qnRuleFromInfo v t b (mkExists (← Meta.getLevel t)) true
        (`not_exists.symm, `not_exists_not.symm)
    | PropForm.ex _ v t b _ =>
      qnRuleFromInfo v t b mkForall true
        (`not_forall.symm, `not_forall_not.symm)
    | _ => myFail `quant_neg "quantifier negation laws don't apply"

elab "quant_neg" f:(colonTerm)? l:(oneLoc)? : tactic => doEquivTac f l `quant_neg qnRule

/- conditional tactic -/
def cdlRule (form : Expr) : TacticM ruleType := do
  match (← getPropForm form) with
    | PropForm.not p => match (← getPropForm p) with
      | PropForm.implies l r => match (← getPropForm r) with
        | PropForm.not nr => return (`HTPI.not_imp_not_iff_and, mkAnd l nr)
        | _ => return (`Classical.not_imp, mkAnd l (mkNot r))
      | _ => myFail `conditional "conditional laws don't apply"
    | PropForm.implies l r => match (← getPropForm l) with
      | PropForm.not nl => return (`or_iff_not_imp_left.symm, mkOr nl r)
      | _ => return (`imp_iff_not_or, mkOr (mkNot l) r)
    | PropForm.and l r => match (← getPropForm r) with
      | PropForm.not nr => return (`Classical.not_imp.symm, mkNot (← mkArrow l nr))
      | _ => match (← getPropForm l) with
        | PropForm.not nl => return (`HTPI.not_imp_iff_not_and.symm, mkNot (← mkArrow r nl))
        | _ => return (`HTPI.not_imp_not_iff_and.symm, mkNot (← mkArrow l (mkNot r)))
    | PropForm.or l r => match (← getPropForm l) with
      | PropForm.not nl => return (`imp_iff_not_or.symm, (← mkArrow nl r))
      | _ => match (← getPropForm r) with
        | PropForm.not nr => return (`imp_iff_or_not.symm, (← mkArrow nr l))
        | _ => return (`or_iff_not_imp_left, (← mkArrow (mkNot l) r))
    | _ => myFail `conditional "conditional laws don't apply"

elab "conditional" f:(colonTerm)? l:(oneLoc)? : tactic => doEquivTac f l `conditional cdlRule

/- double_neg tactic -/
def dnRule (form : Expr) : TacticM ruleType := do
  match (← getPropForm form) with
    | PropForm.not p1 => match (← getPropForm p1) with
      | PropForm.not p2 => return (`Classical.not_not, p2)
      | _ => myFail `double_neg "double negation law doesn't apply"
    | _ => myFail `double_neg "double negation law doesn't apply"

elab "double_neg" f:(colonTerm)? l:(oneLoc)? : tactic => doEquivTac f l `double_neg dnRule

/- bicond_neg tactic
Note converts P ↔ Q to ¬(¬P ↔ Q).
So to convert only one side of ↔, must use : [term to convert] -/
def binegRule (form : Expr) : TacticM ruleType := do
  match (← getPropForm form) with
    | PropForm.not p => match (← getPropForm p) with
      | PropForm.iff l r => match (← getPropForm l) with
        | PropForm.not nl => return (`HTPI.not_not_iff, mkIff nl r)
        | _ => return (`Classical.not_iff, mkIff (mkNot l) r)
      | _ => myFail `bicond_neg "biconditional negation law doesn't apply"
    | PropForm.iff l r => match (← getPropForm l) with
      | PropForm.not nl => return (`Classical.not_iff.symm, mkNot (mkIff nl r))
      | _ => return (`HTPI.not_not_iff.symm, mkNot (mkIff (mkNot l) r))
    | _ => myFail `bicond_neg "biconditional negation law doesn't apply"

elab "bicond_neg" f:(colonTerm)? l:(oneLoc)? : tactic => doEquivTac f l `bicond_neg binegRule

-- Give error if any ident in i is already in use.  Is this right thing to do in all cases?
partial def checkIdUsed (tac : Name) (i : Syntax) : TacticM Unit := do
  match i with
    | .missing => return ()
    | .node _ _ as => for a in as do checkIdUsed tac a
    | .atom _ _ => return ()
    | .ident _ _ v _ =>
        if ((← getLCtx).usesUserName v) then
          myFail tac ("identifier " ++ (toString v) ++ " already in use")
        else
          return ()

-- Get label from "with" clause, or default label.  Used by several tactics
def getLabel (tac : Name) (w : Option WithId) (dflt : Ident := mkIdent `this) : TacticM Ident := do
  match w with
    | some h =>
      let i := h.raw[1]
      checkIdUsed tac i
      return ⟨i⟩
    | none => return dflt

def isLocalVar (s : Syntax) : TacticM Bool := do
  match s with
    | .ident _ _ v _ => return (← getLCtx).usesUserName v
    | _ => return False

/- or_left and or_right tactics -/
def negData (e : Expr) : TacticM (Expr × Bool) := do
  match (← getPropForm e) with
    | PropForm.not ne => return (ne, true)
    | _ => return (e, false)

def orstrat (tac : Name) (w : Option WithId) (left : Bool) : TacticM Unit :=
  withMainContext do
    let label ← getLabel tac w
    let d ← getMainDecl
    let t ← Meta.whnf (← instantiateMVars d.type)
    match (← getPropForm t) with
      | PropForm.or l r => do
          let (form, neg) ← negData (if left then r else l)
          let goalName := d.userName
          let emn ← mkFreshUserName `h
          let emi := mkIdent emn
          doHave emn (mkOr form (mkNot form)) (← `(em _))
          evalTactic (← `(tactic|refine Or.elim $emi:ident ?_ ?_))
          if neg then doSwap
          let (rule1, rule2) :=
            if left then
              (mkIdent ``Or.inr, mkIdent ``Or.inl)
            else
              (mkIdent ``Or.inl, mkIdent ``Or.inr)
          evalTactic (← `(tactic| exact fun x => $rule1:ident x))
          evalTactic (← `(tactic| intro $label:ident; refine $rule2:ident ?_; clear $emi:ident))
          let newGoal ← getMainGoal
          setUserName newGoal goalName
      | _ => myFail tac "goal is not a disjunction"

elab "or_left" w:(withId)? : tactic => orstrat `or_left w true
elab "or_right" w:(withId)? : tactic => orstrat `or_right w false

/- disj_syll tactic -/
def matchFirstNeg (e1 e2 : Expr) : TacticM Bool := do
  match (← getPropForm e1) with
    | PropForm.not ne1 => Meta.isExprDefEq ne1 e2
    | _ => return false

--1st coord:  does one match neg of other?  2nd coord:  does first match neg of second?
def matchNeg (e1 e2 : Expr) : TacticM (Bool × Bool) := do
  if (← matchFirstNeg e1 e2) then
    return (true, true)
  else
    return ((← matchFirstNeg e2 e1), false)

--1st coord:  Does neg contradict right side of disj?  (else left side)
--2nd coord:  Is disjunct negation of neg?  (else neg is negation of disj)
def DisjSyllData (disj neg : Expr) : TacticM (Bool × Bool) := do
  match (← getPropForm disj) with
    | PropForm.or l r =>
      let (isneg, disjneg) ← matchNeg l neg
      if isneg then
        return (false, disjneg)
      else
        let (isneg, disjneg) ← matchNeg r neg
        if isneg then
          return (true, disjneg)
        else
          myFail `disj_syll "disjunctive syllogism rule doesn't apply"
    | _ => myFail `disj_syll "disjunctive syllogism rule doesn't apply"

def parseIdOrTerm (it : IdOrTerm) : Term :=
  let s := it.raw[0]
  match s with
    | .ident .. => ⟨s⟩
    | _ => ⟨s[1]⟩

elab "disj_syll" dIOrT:idOrTerm nIOrT:idOrTerm w:(withId)? : tactic =>
  withMainContext do
    let d := parseIdOrTerm dIOrT
    let n := parseIdOrTerm nIOrT
    let disj ← exprFromPf d 2
    let neg ← exprFromPf n 0
    let (dId, deflabel) :=
      if (← isLocalVar d.raw) then
        (true, ⟨d.raw⟩)
      else
        (false, mkIdent `this)
    let label ← getLabel `disj_syll w deflabel
    let (conright, disjneg) ← DisjSyllData disj neg
    let goalName := (← getMainDecl).userName
    evalTactic (← `(tactic| refine Or.elim $d ?_ ?_))
    if conright then doSwap
    if disjneg then
      evalTactic (← `(tactic| exact fun x => absurd $n x))
    else
      evalTactic (← `(tactic| exact fun x => absurd x $n))
    if (dId && (w == none)) then evalTactic (← `(tactic| clear $label:ident))
    evalTactic (← `(tactic| intro $label:ident))
    let newGoal ← getMainGoal
    setUserName newGoal goalName

/- contradict tactic -/
def ensureContra (w : Option WithId) : TacticM Unit :=
  withMainContext do
    let label ← getLabel `contradict w
    let t ← getMainTarget
    match (← getPropForm t) with
      | PropForm.f => return ()
      | _ => evalTactic (← `(tactic| by_contra $label:ident))

elab "contradict" h:term w:(withId)? : tactic => do
  ensureContra w
  withMainContext do
    --let tocon ← formFromIdent h.raw
    let tocon ← exprFromPf h 0
    match (← getPropForm tocon) with
      | PropForm.not p =>
        doSuffices p (← `(fun x => $h x))
      | _ =>
        doSuffices (mkNot tocon) (← `(fun x => x $h))

/- define, def_step, and whnf tactics -/
def unfoldOrWhnf (tac: Name) (e : Expr) (w rep : Bool) : TacticM Expr := do
  if w then
    match (← getPropForm e) with
      | PropForm.exun lev v t b bi => return unfoldExUn lev v t b bi
      | _ => whnfNotExUn e
  else
    unfoldHead e tac true rep

def doDefine (tac : Name) (f : Option ColonTerm) (l : Option OneLoc) (w rep : Bool) : TacticM Unit :=
  withMainContext do
    let e ← match f with
      | some fs => elabTerm fs.raw[1] none
      | none => formFromLoc l
    let e' ← unfoldOrWhnf tac e w rep
    doReplace tac l (← Meta.mkEq e e') (← `(Eq.refl _))

elab "define" f:(colonTerm)? l:(oneLoc)? : tactic => doDefine `define f l false true
elab "whnf" f:(colonTerm)? l:(oneLoc)? : tactic => doDefine `whnf f l true true
elab "def_step" f:(colonTerm)? l:(oneLoc)? : tactic => doDefine `def_step f l false false

/- definition and definition! tactics -/
--Context set in doDefinition, which calls these functions
def getDefineFormLabel (f : Option ColonTerm) (l : Option OneLoc) : TacticM (Expr × Name) := do
  match f with
    | some t => return (← elabTerm t.raw[1] none, `this)
    | none => match l with
      | some h => do
        let hs := h.raw[1]
        return (← formFromIdent hs, Name.mkStr hs.getId "def")
      | none => return (← getMainTarget, `goal.def)

-- use Iff for propositions, = for other types
def mkRel (e1 e2 : Expr) (prop : Bool) : TacticM Expr :=
  if prop then
    return mkIff e1 e2
  else
    Meta.mkEq e1 e2

-- repeatedly assert definition equivalences or equations, numbering steps
partial def doDefinitionRep (label : Name) (e e1 : Expr) (prop : Bool) (rule : Ident) (firstNum : Nat) : TacticM Unit := do
  let e' ← unfoldHead e1 `definition (firstNum == 1) false
  let res ← mkRel e e' prop
  doHave (Name.appendIndexAfter label firstNum) res (← `($rule _))
  try
    withMainContext (doDefinitionRep label e e' prop rule (firstNum + 1))  -- Context changes each time through
  catch _ =>
    return ()

def doDefinition (all : Bool) (f : Option ColonTerm) (l : Option OneLoc) (wid : Option WithId) : TacticM Unit :=
  withMainContext do
    let (e, deflabel) ← getDefineFormLabel f l
    let label ← getLabel `definition wid (mkIdent deflabel)
    let labeln := label.getId
    let (prop, rule) := if (← exprIsProp e) then
        (true, mkIdent ``Iff.refl)
      else
        (false, mkIdent ``Eq.refl)
    if all then
      doDefinitionRep labeln e e prop rule 1
    else
      let e' ← unfoldHead e `definition true true
      let res ← mkRel e e' prop
      doHave labeln res (← `($rule _))

elab "definition" f:(colonTerm) wid:(withId)? : tactic => doDefinition false (some f) none wid
elab "definition" l:(oneLoc)? wid:(withId)? : tactic => doDefinition false none l wid
elab "definition!" f:(colonTerm) wid:(withId)? : tactic => doDefinition true (some f) none wid
elab "definition!" l:(oneLoc)? wid:(withId)? : tactic => doDefinition true none l wid

def addToName (n : Name) (s : String) : Name :=
  Name.modifyBase n (fun x => Name.mkStr x s)

--Bool is whether or not to clear "or" given; Idents for two cases
def setUpCases (t : Term) (wids : Option With2Ids) : TacticM (Bool × Ident × Ident) := do
  match wids with
    | some ids =>
      let id1s := ids.raw[1]
      checkIdUsed `by_cases id1s
      let id1 : Ident := ⟨id1s⟩
      match ids.raw[2].getArgs[1]? with
        | some id2 =>
          checkIdUsed `by_cases id2
          return (false, id1, ⟨id2⟩)
        | none => return (false, id1, id1)
    | none =>
      if (← isLocalVar t.raw) then
        let tid : Ident := ⟨t.raw⟩
        return (true, tid, tid)
      else
        let thisId := mkIdent `this
        return (false, thisId, thisId)

def fixCase (clear : Bool) (label : Ident) (g : Name) (c : String) : TacticM Unit := do
  if clear then
    evalTactic (← `(tactic| clear $label))
  evalTactic (← `(tactic| intro $label:ident))
  setUserName (← getMainGoal) (addToName g c)
  doSwap

elab "by_cases" "on" t:term wids:(with2Ids)? : tactic =>
  withMainContext do
    let e ← exprFromPf t 2
    match (← getPropForm e) with
      | PropForm.or _ _ =>
        let (clear, label1, label2) ← setUpCases t wids
        let goalname :=  (← getMainDecl).userName
        evalTactic (← `(tactic| refine Or.elim $t ?_ ?_))
        fixCase clear label1 goalname "Case_1"
        fixCase clear label2 goalname "Case_2"
      | _ => myFail `by_cases "hypothesis is not a disjunction"

/- exists_unique tactic -/
def mkUn (lev: Level) (v : Name) (t b : Expr) : TacticM Expr := do
  let v1 := Name.appendIndexAfter v 1
  let v2 := Name.appendIndexAfter v 2
  let f1 := mkLambda v1 BinderInfo.default t b
  let f2 := mkLambda v2 BinderInfo.default t b
  Meta.lambdaTelescope f1 fun fv1 e1 =>
    Meta.lambdaTelescope f2 fun fv2 e2 => do
      let body ← mkArrow e1 (← mkArrow e2
        (mkApp3 (const ``Eq [lev]) t fv1[0]! fv2[0]!))
      Meta.mkForallFVars (fv1.push fv2[0]!) body

elab "exists_unique" : tactic => do
  let goal ← getMainGoal
  withContext goal do
    let d ← getDecl goal
    let goalname := d.userName
    let tar ← instantiateMVars d.type
    match (← getPropForm tar) with
      | PropForm.exun lev v t b _ =>
        let un ← mkUn lev v t b
        let ex := mkExists lev v BinderInfo.default t b
        let h ← mkFreshUserName `h
        let hid := mkIdent h
        let hex := (mkForall `a BinderInfo.default ex
          (mkForall `b BinderInfo.default un tar))
        doHave h hex (← `(existsUnique_of_exists_of_unique))
        evalTactic (← `(tactic| refine $hid ?_ ?_; clear $hid))
        setUserName (← getMainGoal) (addToName goalname "Existence")
        doSwap
        evalTactic (← `(tactic| clear $hid))
        setUserName (← getMainGoal) (addToName goalname "Uniqueness")
        doSwap
      | _ => myFail `exists_unique "goal is not a unique existence statement"

/- obtain tactic -/
def parseIdOrTerm?Type (tac : Name) (it : IdOrTerm?Type) : TacticM (Term × (Option Term)) := do
  let s := it.raw[0]
  let res := match s with
    | .ident .. => (⟨s⟩, none)
    | _ => match s[2].getArgs[1]? with
      | some t => (⟨s[1]⟩, some ⟨t⟩)
      | none => (⟨s[1]⟩, none)
  checkIdUsed tac res.1.raw
  return res

/- Old version
def doIntroOption (i : Term) (t : Option Term) : TacticM Unit := do
  match t with
    | some tt => --evalTactic (← `(tactic| intro ($i : $tt)))
      --Above fails in Chap8Part1 line 572.  Problem seems to be that
      --{a} is not understood as a Set despite default instance declarations above.
      evalTactic (← `(tactic| intro h; match @h with | ($i : $tt) => ?_; try clear h))
    | none => evalTactic (← `(tactic| intro $i:term))
-/

--Imitating mkHasTypeButIsExpectedMsg
def mkDeclaredTypeButIsExpectedMsg (decType expectedType : Expr) : MetaM MessageData := do
  try
    let decTypeType ← Meta.inferType decType
    let expectedTypeType ← Meta.inferType expectedType
    let (decType, expectedType) ← Meta.addPPExplicitToExposeDiff decType expectedType
    let (decTypeType, expectedTypeType) ← Meta.addPPExplicitToExposeDiff decTypeType expectedTypeType
    return m!"is declared to have type{indentD m!"{decType} : {decTypeType}"}\nbut is expected to have type{indentD m!"{expectedType} : {expectedTypeType}"}"
  catch _ =>
    let (decType, expectedType) ← Meta.addPPExplicitToExposeDiff decType expectedType
    return m!"is declared to have type{indentExpr decType}\nbut is expected to have type{indentExpr expectedType}"

def doIntroOption (tac : Name) (i : Term) (t : Option Term) (isProp : Bool) : TacticM Unit := withMainContext do
  match t with
    | some tt =>
      let et ← if isProp then
                  let ett ← elabTerm tt (mkSort levelZero)
                  withRef tt <| Term.ensureType ett
                else
                  Term.elabType tt
      let goal ← getMainGoal
      let h ← mkFreshUserName `h
      let hid := mkIdent h
      let (fvid, goal2) ← goal.intro h
      replaceMainGoal [goal2]
      withMainContext do
        let fv := mkFVar fvid
        let fvt ← Meta.inferType fv
        if (← Meta.isDefEq et fvt) then
          -- Was: replaceMainGoal [← goal2.replaceLocalDeclDefEq fvid et]
          -- But it didn't do replacement in cases where it thought difference wasn't significant.
          -- Copied code from replaceMainGoal to make it do replacement if terms not identical.
          if !(identical et fvt) then
            let mvarDecl ← goal2.getDecl
            let lctxNew := (← getLCtx).modifyLocalDecl fvid (·.setType et)
            let mvarNew ← Meta.mkFreshExprMVarAt lctxNew (← Meta.getLocalInstances) mvarDecl.type mvarDecl.kind mvarDecl.userName
            goal2.assign mvarNew
            replaceMainGoal [mvarNew.mvarId!]
          evalTactic (← `(tactic| match @$hid with | ($i : _) => ?_; try clear $hid))
        else
          Meta.throwTacticEx tac goal m!"type mismatch: {i} {← mkDeclaredTypeButIsExpectedMsg et fvt}"
    | none => evalTactic (← `(tactic| intro $i:term))

def doObtain (itw ith : IdOrTerm?Type) (tm : Term) : TacticM Unit :=
  withMainContext do
    let e ← exprFromPf tm 1
    match (← getPropForm e) with
      | PropForm.ex _ _ _ _ _ =>
        let (wi, wt) ← parseIdOrTerm?Type `obtain itw
        let (hi, ht) ← parseIdOrTerm?Type `obtain ith
        evalTactic (← `(tactic| refine Exists.elim $tm ?_))
        doIntroOption `obtain wi wt false
        doIntroOption `obtain hi ht true
      | _ => myFail `obtain "hypothesis is not an existence statement"

theorem exun_elim {α : Sort u} {p : α → Prop} {b : Prop}
    (h2 : ∃! x, p x) (h1 : ∀ x, p x → (∀ y z, p y → p z → y = z) → b) : b := by
      apply ExistsUnique.elim h2
      intro x h3 h4
      apply h1 x h3
      intro y z h5 h6
      have h7 := h4 y h5
      have h8 := h4 z h6
      rw [h7,h8]

def doObtainExUn (itw ith1 ith2 : IdOrTerm?Type) (tm : Term) : TacticM Unit :=
  withMainContext do
    let e ← exprFromPf tm 1
    match (← getPropForm e) with
      | PropForm.exun lev v t b _ =>
        let (wi, wt) ← parseIdOrTerm?Type `obtain itw
        let (h1i, h1t) ← parseIdOrTerm?Type `obtain ith1
        let (h2i, h2t) ← parseIdOrTerm?Type `obtain ith2
        let tar ← getMainTarget
        let un ← mkUn lev v t b
        let exun := mkForall v BinderInfo.default t (← mkArrow b (← mkArrow un tar))
        let h ← mkFreshUserName `h
        let hid := mkIdent h
        doHave h (← mkArrow exun tar) (← `(HTPI.exun_elim $tm))
        evalTactic (← `(tactic| refine $hid ?_; clear $hid))
        doIntroOption `obtain wi wt false
        doIntroOption `obtain h1i h1t true
        doIntroOption `obtain h2i h2t true
      | _ => myFail `obtain "hypothesis is not a unique existence statement"

--Make 1 assertion for existential, 2 for unique existential
elab "obtain" itw:idOrTerm?Type ith:idOrTerm?Type " from " t:term : tactic =>
  doObtain itw ith t
elab "obtain" itw:idOrTerm?Type ith1:idOrTerm?Type ith2:idOrTerm?Type " from " t:term : tactic =>
  doObtainExUn itw ith1 ith2 t

/- assume and fix tactics -/
def doAssume (w : Term) (t : Option Term) : TacticM Unit :=
  withMainContext do
    checkIdUsed `assume w
    match (← getPropForm (← Meta.whnf (← getMainTarget))) with
      | PropForm.implies _ _ => doIntroOption `assume w t true
      --| PropForm.not _ => doIntroOption w t  --Not necessary--whnf will have changed to implies
      | _ => myFail `assume "goal is not a conditional statement"

def doFix (w : Term) (t : Option Term) : TacticM Unit :=
  withMainContext do
    checkIdUsed `fix w
    match (← getPropForm (← Meta.whnf (← getMainTarget))) with
      | PropForm.all _ _ _ _ => doIntroOption `fix w t false
      | _ => myFail `fix "goal is not a universally quantified statement"

elab "assume" w:term : tactic => doAssume w none
elab "assume" w:term " : " t:term : tactic => doAssume w (some t)
elab "fix" w:term : tactic => doFix w none
elab "fix" w:term " : " t:term : tactic => doFix w (some t)

/- show tactic: allow either "from" or ":="  Probably best to stick to "from" -/
macro "show " c:term " from " p:term : tactic => `(tactic| {show $c; exact $p})
macro "show " c:term " := " p:term : tactic => `(tactic| {show $c; exact $p})
macro "show " c:term " by " p:tactic : tactic => `(tactic| {show $c; $p})

theorem induc_from (P : Nat → Prop) (k : Nat) (h1 : P k) (h2 : (∀ n ≥ k, P n → P (n+1))) :
    ∀ n ≥ k, P n := by
  apply @Nat.rec
  assume h3
  have h4 : k = 0 := Nat.eq_zero_of_le_zero h3
  rewrite [h4] at h1
  exact h1
  fix n
  assume h3
  assume h4
  have h5 : k < n + 1 ∨ k = n + 1 := LE.le.lt_or_eq_dec h4
  by_cases on h5
  have h6 : k ≤ n := Nat.le_of_lt_succ h5
  have h7 := h3 h6
  exact h2 n h6 h7
  rewrite [h5] at h1
  exact h1

-- For ordinary induction, uses a different base if appropriate
def doInduc (strong : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  withContext goal do
    let d ← getDecl goal
    let tag := d.userName
    let target ← instantiateMVars d.type
    match (← getPropForm target) with
      | PropForm.all v t b _ =>
        match t with
          | (.const ``Nat _) =>
            let m := Expr.lam v t b BinderInfo.default  --motive
            let vid := mkIdent v
            if strong then
              let v1 := Name.appendIndexAfter v 1
              let v1id := mkIdent v1
              let m1 := Expr.lam v1 t m BinderInfo.default
              let newtar ← Meta.lambdaTelescope m1 fun fvs Pv => do
                let fv1 := fvs[0]!
                let fv := fvs[1]!
                let Pv1 := replaceFVar Pv fv fv1
                let v1lv ← elabTerm (← `($v1id < $vid)) none
                let ih ← Meta.mkForallFVars #[fv1] (← mkArrow v1lv Pv1)
                Meta.mkForallFVars #[fv] (← mkArrow ih Pv)
              let newgoal ← Meta.mkFreshExprSyntheticOpaqueMVar newtar tag
              assign goal (mkApp2 (Expr.const ``Nat.strongRec' [Level.zero]) m newgoal)
              replaceMainGoal [newgoal.mvarId!]
            else
              let (base, ind, rule) ← Meta.lambdaTelescope m fun fvs Pv => do
                -- fvs.size should be 1.
                let fv := fvs[0]!
                let PFPv ← getPropForm Pv
                let (fr, Qv) := match PFPv with
                  | PropForm.implies l r => match (consumeMData l) with
                    | (app (app (app (app (const ``GE.ge _) (const ``Nat _)) _) a) min) =>
                      if (a == fv) && !(containsFVar min (fvarId! fv)) then
                        (some (min, l), r)
                      else
                        (none, Pv)
                    | (app (app (app (app (const ``LE.le _) (const ``Nat _)) _) min) a) =>
                      if (a == fv) && !(containsFVar min (fvarId! fv)) then
                        (some (min, l), r)
                      else
                        (none, Pv)
                    | _ => (none, Pv)
                  | _ => (none, Pv)
                let fvp1 ← elabTerm (← `($vid:ident + 1)) none
                let Qimp ← mkArrow Qv (replaceFVar Qv fv fvp1)
                match fr with
                  | some (min, cond) =>
                    let base := replaceFVar Qv fv min
                    let ind ← Meta.mkForallFVars fvs (← mkArrow cond Qimp)
                    let m' ← Meta.mkLambdaFVars fvs Qv
                    pure (base, ind, mkApp2 (const ``HTPI.induc_from []) m' min)
                  | none =>
                    let base := replaceFVar Qv fv (Expr.lit (.natVal 0))
                    let ind ← Meta.mkForallFVars fvs Qimp
                    pure (base, ind, app (const ``Nat.rec [Level.zero]) m)
              let baseGoal ← Meta.mkFreshExprSyntheticOpaqueMVar base (addToName tag "Base_Case")
              let indGoal ← Meta.mkFreshExprSyntheticOpaqueMVar ind (addToName tag "Induction_Step")
              assign goal (mkApp2 rule baseGoal indGoal)
              replaceMainGoal [baseGoal.mvarId!, indGoal.mvarId!]
          | _ => myFail `by_induc "mathematical induction doesn't apply"
      | _ => myFail `by_induc "mathematical induction doesn't apply"

elab "by_induc" : tactic => doInduc false
elab "by_strong_induc" : tactic => doInduc true
end tactic_defs

--Sum of m terms of the form f i, starting with i = k
def sum_seq {A : Type} [AddZeroClass A] (m k : Nat) (f : Nat → A) : A :=
  match m with
    | 0 => 0
    | n + 1 => sum_seq n k f + f (k + n)

def sum_from_to {A : Type} [AddZeroClass A] (k n : Nat) (f : Nat → A) : A :=
  sum_seq (n + 1 - k) k f

syntax (name := sumFromTo) "Sum " ident " from " term " to " term ", " term:51 : term
macro_rules (kind := sumFromTo)
  | `(Sum $i from $k to $n, $p) => `(sum_from_to $k $n (fun $i => $p))

@[app_unexpander sum_from_to] def unexpandSumFromTo : Lean.PrettyPrinter.Unexpander
  | `($_ $k:term $n:term fun $i:ident => $b) => `(Sum $i from $k to $n, $b)
  | `($_ $k:term $n:term fun ($i:ident : $_) => $b) => `(Sum $i from $k to $n, $b)
  | _ => throw ()

theorem sum_base {A : Type} [AddZeroClass A] {k : Nat} {f : Nat → A} :
    Sum i from k to k, f i = f k := by
  define : Sum i from k to k, f i
  rewrite [Nat.add_sub_cancel_left]
  rewrite [sum_seq, sum_seq]
  rewrite [zero_add, add_zero]
  rfl
  done

theorem sum_step {A : Type} [AddZeroClass A] {k n : Nat} {f : Nat → A}
    (h : k ≤ n) : Sum i from k to (n + 1), f i = (Sum i from k to n, f i) + f (n + 1) := by
  define : Sum i from k to (n + 1), f i
  obtain j h1 from Nat.le.dest h
  have h2 : n + 1 + 1 - k = n + 1 - k + 1 := by
    rewrite [←h1, add_assoc, add_assoc, Nat.add_sub_cancel_left,
      add_assoc, Nat.add_sub_cancel_left, add_assoc]
    rfl
  have h3 : f (n + 1) = f (k + (n + 1 - k)) := by
    rewrite [←h1, add_assoc, Nat.add_sub_cancel_left]
    rfl
  rewrite [h2, h3]
  rfl
  done

theorem sum_from_zero_step {A : Type} [AddZeroClass A] {n : Nat} {f : Nat → A} :
    Sum i from 0 to (n + 1), f i = (Sum i from 0 to n, f i) + f (n + 1) :=
  sum_step (Nat.zero_le n)

theorem sum_empty {A : Type} [AddZeroClass A] {k n : Nat} {f : Nat → A}
    (h : n < k) : Sum i from k to n, f i = 0 := by
  define : Sum i from k to n, f i
  have h2 : n + 1 - k = 0 := Nat.sub_eq_zero_of_le h
  rewrite [h2]
  rfl
  done

-- ──── IntroLean ────
/- Copyright 2023-2025 Daniel J. Velleman -/


theorem Example_3_2_4
    (P Q R : Prop) (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  have h4 : Q → R := h h3
  contrapos at h4            --Now h4 : ¬R → ¬Q
  show ¬Q from h4 h2
  done

theorem extremely_easy (P : Prop) (h : P) : P := h

theorem very_easy
    (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := h1 h2

theorem easy (P Q R : Prop) (h1 : P → Q)
    (h2 : Q → R) (h3 : P) : R := h2 (h1 h3)

theorem two_imp (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P := by
  contrapos         --Goal is now P → ¬R
  assume h3 : P
  have h4 : Q := h1 h3
  show ¬R from h2 h4
  done

theorem Example_3_2_5_simple
    (B C : Set Nat) (a : Nat)
    (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C := by
  define at h2       --Now h2 : ¬(a ∈ B ∧ a ∉ C)
  demorgan at h2; conditional at h2
                     --Now h2 : a ∈ B → a ∈ C
  show a ∈ C from h2 h1
  done

theorem Example_3_2_5_simple_general
    (U : Type) (B C : Set U) (a : U)
    (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C := by
  define at h2
  demorgan at h2; conditional at h2
  show a ∈ C from h2 h1
  done

-- ──── Chap3 ────
/- Copyright 2023-2025 Daniel J. Velleman -/


/- Definitions -/
def even (n : Int) : Prop := ∃ (k : Int), n = 2 * k

def odd (n : Int) : Prop := ∃ (k : Int), n = 2 * k + 1

/- Sections 3.1 and 3.2 -/
theorem Example_3_2_4_v2 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  by_contra h4
  have h5 : Q → R := h h3
  have h6 : R := h5 h4
  show False from h2 h6
  done

theorem Example_3_2_4_v3 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  by_contra h4
  contradict h2
  show R from h h3 h4
  done

theorem Like_Example_3_2_5
    (U : Type) (A B C : Set U) (a : U)
    (h1 : a ∈ A) (h2 : a ∉ A \ B)
    (h3 : a ∈ B → a ∈ C) : a ∈ C := by
  apply h3 _
  define at h2
  demorgan at h2; conditional at h2
  show a ∈ B from h2 h1
  done

/- Section 3.3 -/
example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), P x → ¬Q x)
    (h2 : ∀ (x : U), Q x) :
    ¬∃ (x : U), P x := by
  quant_neg     --Goal is now ∀ (x : U), ¬P x
  fix y : U
  have h3 : P y → ¬Q y := h1 y
  have h4 : Q y := h2 y
  contrapos at h3  --Now h3 : Q y → ¬P y
  show ¬P y from h3 h4
  done

example (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ∀ (x : U), x ∈ A → x ∉ B) : A ⊆ C := by
  define  --Goal : ∀ ⦃a : U⦄, a ∈ A → a ∈ C
  fix y : U
  assume h3 : y ∈ A
  have h4 : y ∉ B := h2 y h3
  define at h1  --h1 : ∀ ⦃a : U⦄, a ∈ A → a ∈ B ∪ C
  have h5 : y ∈ B ∪ C := h1 h3
  define at h5  --h5 : y ∈ B ∨ y ∈ C
  conditional at h5  --h5 : ¬y ∈ B → y ∈ C
  show y ∈ C from h5 h4
  done

example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), ∃ (y : U), P x → ¬ Q y)
    (h2 : ∃ (x : U), ∀ (y : U), P x → Q y) :
    ∃ (x : U), ¬P x := by
  obtain (a : U)
    (h3 : ∀ (y : U), P a → Q y) from h2
  have h4 : ∃ (y : U), P a → ¬ Q y := h1 a
  obtain (b : U) (h5 : P a → ¬ Q b) from h4
  have h6 : P a → Q b := h3 b
  apply Exists.intro a _
  by_contra h7
  show False from h5 h7 (h6 h7)
  done

theorem Example_3_3_5 (U : Type) (B : Set U)
    (F : Set (Set U)) : ⋃₀ F ⊆ B → F ⊆ 𝒫 B := by
  assume h1 : ⋃₀ F ⊆ B
  define
  fix x : Set U
  assume h2 : x ∈ F
  define
  fix y : U
  assume h3 : y ∈ x
  define at h1
  apply h1 _
  define
  apply Exists.intro x _
  show x ∈ F ∧ y ∈ x from And.intro h2 h3
  done

/- Section 3.4 -/
theorem Like_Example_3_4_1 (U : Type)
    (A B C D : Set U) (h1 : A ⊆ B)
    (h2 : ¬∃ (c : U), c ∈ C ∩ D) :
    A ∩ C ⊆ B \ D := by
  define
  fix x : U
  assume h3 : x ∈ A ∩ C
  define at h3; define
  apply And.intro
  · -- Proof that x ∈ B.
    show x ∈ B from h1 h3.left
    done
  · -- Proof that x ∉ D.
    contradict h2 with h4
    apply Exists.intro x
    show x ∈ C ∩ D from And.intro h3.right h4
    done
  done

example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), P x ↔ Q x) :
    (∃ (x : U), P x) ↔ ∃ (x : U), Q x := by
  apply Iff.intro
  · -- (→)
    assume h2 : ∃ (x : U), P x
    obtain (u : U) (h3 : P u) from h2
    have h4 : P u ↔ Q u := h1 u
    apply Exists.intro u
    show Q u from h4.ltr h3
    done
  · -- (←)
    assume h2 : ∃ (x : U), Q x
    obtain (u : U) (h3 : Q u) from h2
    show ∃ (x : U), P x from Exists.intro u ((h1 u).rtl h3)
    done
  done

theorem Example_3_4_5 (U : Type)
    (A B C : Set U) : A ∩ (B \ C) = (A ∩ B) \ C := by
  apply Set.ext
  fix x : U
  show x ∈ A ∩ (B \ C) ↔ x ∈ (A ∩ B) \ C from
    calc x ∈ A ∩ (B \ C)
      _ ↔ x ∈ A ∧ (x ∈ B ∧ x ∉ C) := Iff.refl _
      _ ↔ (x ∈ A ∧ x ∈ B) ∧ x ∉ C := and_assoc.symm
      _ ↔ x ∈ (A ∩ B) \ C := Iff.refl _
  done

/- Section 3.5 -/
theorem Example_3_5_2
    (U : Type) (A B C : Set U) :
    A \ (B \ C) ⊆ (A \ B) ∪ C := by
  fix x : U
  assume h1 : x ∈ A \ (B \ C)
  define; define at h1
  have h2 : x ∉ B \ C := h1.right
  define at h2; demorgan at h2
            --h2 : x ∉ B ∨ x ∈ C
  by_cases on h2
  · -- Case 1. h2 : x ∉ B
    apply Or.inl
    show x ∈ A \ B from And.intro h1.left h2
    done
  · -- Case 2. h2 : x ∈ C
    apply Or.inr
    show x ∈ C from h2
    done
  done

example (U : Type) (A B C : Set U)
    (h1 : A \ B ⊆ C) : A ⊆ B ∪ C := by
  fix x : U
  assume h2 : x ∈ A
  define
  or_right with h3
  show x ∈ C from h1 (And.intro h2 h3)
  done

example
    (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ¬∃ (x : U), x ∈ A ∩ B) : A ⊆ C := by
  fix a : U
  assume h3 : a ∈ A
  quant_neg at h2
  have h4 : a ∈ B ∪ C := h1 h3
  have h5 : a ∉ A ∩ B := h2 a
  define at h4
  define at h5; demorgan at h5
  disj_syll h5 h3  --h5 : ¬a ∈ B
  disj_syll h4 h5  --h4 : a ∈ C
  show a ∈ C from h4
  done

example
    (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ¬∃ (x : U), x ∈ A ∩ B) : A ⊆ C := by
  fix a : U
  assume h3 : a ∈ A
  have h4 : a ∈ B ∪ C := h1 h3
  define at h4
  have h5 : a ∉ B := by
    contradict h2 with h6
    show ∃ (x : U), x ∈ A ∩ B from
      Exists.intro a (And.intro h3 h6)
    done
  disj_syll h4 h5  --h4 : a ∈ C
  show a ∈ C from h4
  done

/- Section 3.6 -/
theorem empty_union {U : Type} (B : Set U) :
    ∅ ∪ B = B := by
  apply Set.ext
  fix x : U
  apply Iff.intro
  · -- (→)
    assume h1 : x ∈ ∅ ∪ B
    define at h1
    have h2 : x ∉ ∅ := by
      by_contra h3
      define at h3  --h3 : False
      show False from h3
      done
    disj_syll h1 h2  --h1 : x ∈ B
    show x ∈ B from h1
    done
  · -- (←)
    assume h1 : x ∈ B
    show x ∈ ∅ ∪ B from Or.inr h1
    done
  done

theorem union_comm {U : Type} (X Y : Set U) :
    X ∪ Y = Y ∪ X := by
  apply Set.ext
  fix x : U
  define : x ∈ X ∪ Y
  define : x ∈ Y ∪ X
  show x ∈ X ∨ x ∈ Y ↔ x ∈ Y ∨ x ∈ X from or_comm
  done

theorem Example_3_6_2 (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U),
    A ∪ B = B := by
  exists_unique
  · -- Existence
    apply Exists.intro ∅
    show ∀ (B : Set U), ∅ ∪ B = B from empty_union
    done
  · -- Uniqueness
    fix C : Set U; fix D : Set U
    assume h1 : ∀ (B : Set U), C ∪ B = B
    assume h2 : ∀ (B : Set U), D ∪ B = B
    have h3 : C ∪ D = D := h1 D
    have h4 : D ∪ C = C := h2 C
    show C = D from
      calc C
        _ = D ∪ C := h4.symm
        _ = C ∪ D := union_comm D C
        _ = D := h3
    done
  done

theorem Example_3_6_4 (U : Type) (A B C : Set U)
    (h1 : ∃ (x : U), x ∈ A ∩ B)
    (h2 : ∃ (x : U), x ∈ A ∩ C)
    (h3 : ∃! (x : U), x ∈ A) :
    ∃ (x : U), x ∈ B ∩ C := by
  obtain (b : U) (h4 : b ∈ A ∩ B) from h1
  obtain (c : U) (h5 : c ∈ A ∩ C) from h2
  obtain (a : U) (h6 : a ∈ A) (h7 : ∀ (y z : U),
    y ∈ A → z ∈ A → y = z)  from h3
  define at h4; define at h5
  have h8 : b = c := h7 b c h4.left h5.left
  rewrite [h8] at h4
  show ∃ (x : U), x ∈ B ∩ C from
    Exists.intro c (And.intro h4.right h5.right)
  done

/- Section 3.7 -/
theorem Theorem_3_3_7 :
    ∀ (a b c : Int), a ∣ b → b ∣ c → a ∣ c := by
  fix a : Int; fix b : Int; fix c : Int
  assume h1 : a ∣ b; assume h2 : b ∣ c
  define at h1; define at h2; define
  obtain (m : Int) (h3 : b = a * m) from h1
  obtain (n : Int) (h4 : c = b * n) from h2
  rewrite [h3] at h4   --h4 : c = a * m * n
  apply Exists.intro (m * n)
  rewrite [mul_assoc a m n] at h4
  show c = a * (m * n) from h4
  done

theorem Theorem_3_4_7 :
    ∀ (n : Int), 6 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n := by
  fix n : Int
  apply Iff.intro
  · -- (→)
    assume h1 : 6 ∣ n; define at h1
    obtain (k : Int) (h2 : n = 6 * k) from h1
    apply And.intro
    · -- Proof that 2 ∣ n
      define
      apply Exists.intro (3 * k)
      rewrite [←mul_assoc 2 3 k]
      show n = 2 * 3 * k from h2
      done
    · -- Proof that 3 ∣ n
      define
      apply Exists.intro (2 * k)
      rewrite [←mul_assoc 3 2 k]
      show n = 3 * 2 * k from h2
      done
    done
  · -- (←)
    assume h1 : 2 ∣ n ∧ 3 ∣ n
    have h2 : 2 ∣ n := h1.left
    have h3 : 3 ∣ n := h1.right
    define at h2; define at h3; define
    obtain (j : Int) (h4 : n = 2 * j) from h2
    obtain (k : Int) (h5 : n = 3 * k) from h3
    have h6 : 6 * (j - k) = n :=
      calc 6 * (j - k)
        _ = 3 * (2 * j) - 2 * (3 * k) := by ring
        _ = 3 * n - 2 * n := by rw [←h4, ←h5]
        _ = n := by ring
    show ∃ (c : Int), n = 6 * c from
      Exists.intro (j - k) h6.symm
    done
  done

theorem Example_3_5_4 (x : Real) (h1 : x ≤ x ^ 2) : x ≤ 0 ∨ 1 ≤ x := by
  or_right with h2     --h2 : ¬x ≤ 0;  Goal : 1 ≤ x
  have h3 : 0 < x := lt_of_not_ge h2
  have h4 : 1 * x ≤ x * x :=
    calc 1 * x
      _ = x := one_mul x
      _ ≤ x ^ 2 := h1
      _ = x * x := by ring
  show 1 ≤ x from le_of_mul_le_mul_right h4 h3
  done

-- ──── Chap4 ────
/- Copyright 2023-2025 Daniel J. Velleman -/


/- Definitions -/
def Dom {A B : Type} (R : Set (A × B)) : Set A :=
  {a : A | ∃ (b : B), (a, b) ∈ R}

def Ran {A B : Type} (R : Set (A × B)) : Set B :=
  {b : B | ∃ (a : A), (a, b) ∈ R}

def inv {A B : Type} (R : Set (A × B)) : Set (B × A) :=
  {(b, a) : B × A | (a, b) ∈ R}

def comp {A B C : Type}
    (S : Set (B × C)) (R : Set (A × B)) : Set (A × C) :=
  {(a, c) : A × C | ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S}

def extension {A B : Type} (R : Rel A B) : Set (A × B) :=
  {(a, b) : A × B | R a b}

def reflexive {A : Type} (R : BinRel A) : Prop :=
  ∀ (x : A), R x x

def symmetric {A : Type} (R : BinRel A) : Prop :=
  ∀ (x y : A), R x y → R y x

def transitive {A : Type} (R : BinRel A) : Prop :=
  ∀ (x y z : A), R x y → R y z → R x z

def elementhood (A : Type) (a : A) (X : Set A) : Prop := a ∈ X

def RelFromExt {A B : Type}
  (R : Set (A × B)) (a : A) (b : B) : Prop := (a, b) ∈ R

def antisymmetric {A : Type} (R : BinRel A) : Prop :=
  ∀ (x y : A), R x y → R y x → x = y

def partial_order {A : Type} (R : BinRel A) : Prop :=
  reflexive R ∧ transitive R ∧ antisymmetric R

def total_order {A : Type} (R : BinRel A) : Prop :=
  partial_order R ∧ ∀ (x y : A), R x y ∨ R y x

def sub (A : Type) (X Y : Set A) : Prop := X ⊆ Y

def smallestElt {A : Type} (R : BinRel A) (b : A) (B : Set A) : Prop :=
  b ∈ B ∧ ∀ x ∈ B, R b x

def minimalElt {A : Type} (R : BinRel A) (b : A) (B : Set A) : Prop :=
  b ∈ B ∧ ¬∃ x ∈ B, R x b ∧ x ≠ b

def upperBd {A : Type} (R : BinRel A) (a : A) (B : Set A) : Prop :=
  ∀ x ∈ B, R x a

def lub {A : Type} (R : BinRel A) (a : A) (B : Set A) : Prop :=
  smallestElt R a {c : A | upperBd R c B}

def equiv_rel {A : Type} (R : BinRel A) : Prop :=
  reflexive R ∧ symmetric R ∧ transitive R

def equivClass {A : Type} (R : BinRel A) (x : A) : Set A :=
  {y : A | R y x}

def mod (A : Type) (R : BinRel A) : Set (Set A) :=
  {equivClass R x | x : A}

def empty {A : Type} (X : Set A) : Prop := ¬∃ (x : A), x ∈ X

def pairwise_disjoint {A : Type} (F : Set (Set A)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → empty (X ∩ Y)

def partition {A : Type} (F : Set (Set A)) : Prop :=
  (∀ (x : A), x ∈ ⋃₀ F) ∧ pairwise_disjoint F ∧ ∀ X ∈ F, ¬empty X

def EqRelFromPart {A : Type} (F : Set (Set A)) (x y : A) : Prop :=
  ∃ X ∈ F, x ∈ X ∧ y ∈ X

/- Section 4.2 -/
theorem Theorem_4_2_5_1 {A B : Type}
    (R : Set (A × B)) : inv (inv R) = R := by rfl

theorem Theorem_4_2_5_2 {A B : Type}
    (R : Set (A × B)) : Dom (inv R) = Ran R := by rfl

theorem Theorem_4_2_5_3 {A B : Type}
    (R : Set (A × B)) : Ran (inv R) = Dom R := by rfl

theorem Theorem_4_2_5_4 {A B C D : Type}
    (R : Set (A × B)) (S : Set (B × C)) (T : Set (C × D)) :
    comp T (comp S R) = comp (comp T S) R := by
  apply Set.ext
  fix (a, d) : A × D
  apply Iff.intro
  · -- (→)
    assume h1 : (a, d) ∈ comp T (comp S R)
                     --Goal : (a, d) ∈ comp (comp T S) R
    define           --Goal : ∃ (x : B), (a, x) ∈ R ∧ (x, d) ∈ comp T S
    define at h1     --h1 : ∃ (x : C), (a, x) ∈ comp S R ∧ (x, d) ∈ T
    obtain (c : C) (h2 : (a, c) ∈ comp S R ∧ (c, d) ∈ T) from h1
    have h3 : (a, c) ∈ comp S R := h2.left
    define at h3     --h3 : ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S
    obtain (b : B) (h4 : (a, b) ∈ R ∧ (b, c) ∈ S) from h3
    apply Exists.intro b    --Goal : (a, b) ∈ R ∧ (b, d) ∈ comp T S
    apply And.intro h4.left --Goal : (b, d) ∈ comp T S
    define                  --Goal : ∃ (x : C), (b, x) ∈ S ∧ (x, d) ∈ T
    show ∃ (x : C), (b, x) ∈ S ∧ (x, d) ∈ T from
      Exists.intro c (And.intro h4.right h2.right)
    done
  · -- (←)
    assume h1 : (a, d) ∈ comp (comp T S) R
    define; define at h1
    obtain (b : B) (h2 : (a, b) ∈ R ∧ (b, d) ∈ comp T S) from h1
    have h3 : (b, d) ∈ comp T S := h2.right
    define at h3
    obtain (c : C) (h4 : (b, c) ∈ S ∧ (c, d) ∈ T) from h3
    apply Exists.intro c
    apply And.intro _ h4.right
    define
    show ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S from
      Exists.intro b (And.intro h2.left h4.left)
    done
  done

theorem inv_def {A B : Type} (R : Set (A × B)) (a : A) (b : B) :
    (b, a) ∈ inv R ↔ (a, b) ∈ R := by rfl

theorem Theorem_4_2_5_5 {A B C : Type}
    (R : Set (A × B)) (S : Set (B × C)) :
    inv (comp S R) = comp (inv R) (inv S) := by
  apply Set.ext
  fix (c, a) : C × A
  apply Iff.intro
  · -- (→)
    assume h1 : (c, a) ∈ inv (comp S R)
                      --Goal : (c, a) ∈ comp (inv R) (inv S)
    define at h1      --h1 : ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S
    define            --Goal : ∃ (x : B), (c, x) ∈ inv S ∧ (x, a) ∈ inv R
    obtain (b : B) (h2 : (a, b) ∈ R ∧ (b, c) ∈ S) from h1
    apply Exists.intro b         --Goal : (c, b) ∈ inv S ∧ (b, a) ∈ inv R
    rewrite [inv_def, inv_def] --Goal : (b, c) ∈ S ∧ (a, b) ∈ R
    show (b, c) ∈ S ∧ (a, b) ∈ R from And.intro h2.right h2.left
    done
  · -- (←)
    assume h1 : (c, a) ∈ comp (inv R) (inv S)
    define at h1
    define
    obtain (b : B) (h2 : (c, b) ∈ inv S ∧ (b, a) ∈ inv R) from h1
    apply Exists.intro b
    rewrite [inv_def, inv_def] at h2
    show (a, b) ∈ R ∧ (b, c) ∈ S from And.intro h2.right h2.left
    done
  done

/- Section 4.3 -/
theorem ext_def {A B : Type} (R : Rel A B) (a : A) (b : B) :
    (a, b) ∈ extension R ↔ R a b := by rfl

theorem Theorem_4_3_4_2 {A : Type} (R : BinRel A) :
    symmetric R ↔ extension R = inv (extension R) := by
  apply Iff.intro
  · -- (→)
    assume h1 : symmetric R
    define at h1             --h1 : ∀ (x y : A), R x y → R y x
    apply Set.ext
    fix (a, b) : A × A
    show (a, b) ∈ extension R ↔ (a, b) ∈ inv (extension R) from
      calc (a, b) ∈ extension R
        _ ↔ R a b := by rfl
        _ ↔ R b a := Iff.intro (h1 a b) (h1 b a)
        _ ↔ (a, b) ∈ inv (extension R) := by rfl
    done
  · -- (←)
    assume h1 : extension R = inv (extension R)
    define                   --Goal : ∀ (x y : A), R x y → R y x
    fix a : A; fix b : A
    assume h2 : R a b        --Goal : R b a
    rewrite [←ext_def R, h1, inv_def, ext_def] at h2
    show R b a from h2
    done
  done

theorem RelFromExt_def {A B : Type}
    (R : Set (A × B)) (a : A) (b : B) :
    RelFromExt R a b ↔ (a, b) ∈ R := by rfl

example {A B : Type} (R : Rel A B) :
    RelFromExt (extension R) = R := by rfl

example {A B : Type} (R : Set (A × B)) :
    extension (RelFromExt R) = R := by rfl

/- Section 4.4 -/
theorem Theorem_4_4_6_2 {A : Type} (R : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R) (h2 : smallestElt R b B) :
    minimalElt R b B ∧ ∀ (c : A), minimalElt R c B → b = c := by
  define at h1     --h1 : reflexive R ∧ transitive R ∧ antisymmetric R
  define at h2     --h2 : b ∈ B ∧ ∀ (x : A), x ∈ B → R b x
  apply And.intro
  · -- Proof that b is minimal
    define           --Goal : b ∈ B ∧ ¬∃ (x : A), x ∈ B ∧ R x b ∧ x ≠ b
    apply And.intro h2.left
    quant_neg        --Goal : ∀ (x : A), ¬(x ∈ B ∧ R x b ∧ x ≠ b)
    fix x : A
    demorgan         --Goal : ¬x ∈ B ∨ ¬(R x b ∧ x ≠ b)
    or_right with h3 --h3 : x ∈ B; Goal : ¬(R x b ∧ x ≠ b)
    demorgan         --Goal : ¬R x b ∨ x = b
    or_right with h4 --h4 : R x b; Goal : x = b
    have h5 : R b x := h2.right x h3
    have h6 : antisymmetric R := h1.right.right
    define at h6     --h6 : ∀ (x y : A), R x y → R y x → x = y
    show x = b from h6 x b h4 h5
    done
  · -- Proof that b is only minimal element
    fix c : A
    assume h3 : minimalElt R c B
    define at h3    --h3 : c ∈ B ∧ ¬∃ (x : A), x ∈ B ∧ R x c ∧ x ≠ c
    contradict h3.right with h4
                  --h4 : ¬b = c; Goal : ∃ (x : A), x ∈ B ∧ R x c ∧ x ≠ c
    have h5 : R b c := h2.right c h3.left
    show ∃ (x : A), x ∈ B ∧ R x c ∧ x ≠ c from
      Exists.intro b (And.intro h2.left (And.intro h5 h4))
    done
  done

theorem Theorem_4_4_6_3 {A : Type} (R : BinRel A) (B : Set A) (b : A)
    (h1 : total_order R) (h2 : minimalElt R b B) : smallestElt R b B := by
  define at h1         --h1 : partial_order R ∧ ∀ (x y : A), R x y ∨ R y x
  define at h2         --h2 : b ∈ B ∧ ¬∃ (x : A), x ∈ B ∧ R x b ∧ x ≠ b
  define               --Goal : b ∈ B ∧ ∀ (x : A), x ∈ B → R b x
  apply And.intro h2.left  --Goal : ∀ (x : A), x ∈ B → R b x
  fix x : A
  assume h3 : x ∈ B        --Goal : R b x
  by_cases h4 : x = b
  · -- Case 1. h4 : x = b
    rewrite [h4]           --Goal : R b b
    have h5 : partial_order R := h1.left
    define at h5
    have h6 : reflexive R := h5.left
    define at h6
    show R b b from h6 b
    done
  · -- Case 2. h4 : x ≠ b
    have h5 : ∀ (x y : A), R x y ∨ R y x := h1.right
    have h6 : R x b ∨ R b x := h5 x b
    have h7 : ¬R x b := by
      contradict h2.right with h8
      show ∃ (x : A), x ∈ B ∧ R x b ∧ x ≠ b from
        Exists.intro x (And.intro h3 (And.intro h8 h4))
      done
    disj_syll h6 h7
    show R b x from h6
    done
  done

/- Section 4.5 -/
lemma Lemma_4_5_5_1 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ (x : A), x ∈ equivClass R x := by
  fix x : A
  define           --Goal : R x x
  define at h      --h : reflexive R ∧ symmetric R ∧ transitive R
  have Rref : reflexive R := h.left
  show R x x from Rref x
  done

lemma Lemma_4_5_5_2 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ (x y : A), y ∈ equivClass R x ↔
      equivClass R y = equivClass R x := by
  have Rsymm : symmetric R := h.right.left
  have Rtrans : transitive R := h.right.right
  fix x : A; fix y : A
  apply Iff.intro
  · -- (→)
    assume h2 :
      y ∈ equivClass R x    --Goal : equivClass R y = equivClass R x
    define at h2                        --h2 : R y x
    apply Set.ext
    fix z : A
    apply Iff.intro
    · -- Proof that z ∈ equivClass R y → z ∈ equivClass R x
      assume h3 : z ∈ equivClass R y
      define                            --Goal : R z x
      define at h3                      --h3 : R z y
      show R z x from Rtrans z y x h3 h2
      done
    · -- Proof that z ∈ equivClass R x → z ∈ equivClass R y
      assume h3 : z ∈ equivClass R x
      define                            --Goal : R z y
      define at h3                      --h3 : R z x
      have h4 : R x y := Rsymm y x h2
      show R z y from Rtrans z x y h3 h4
      done
    done
  · -- (←)
    assume h2 :
      equivClass R y = equivClass R x   --Goal : y ∈ equivClass R x
    rewrite [←h2]                       --Goal : y ∈ equivClass R y
    show y ∈ equivClass R y from Lemma_4_5_5_1 R h y
    done
  done

lemma Theorem_4_5_4_part_1 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ (x : A), x ∈ ⋃₀ (mod A R) := by
  fix x : A
  define        --Goal : ∃ (t : Set A), t ∈ mod A R ∧ x ∈ t
  apply Exists.intro (equivClass R x)
  apply And.intro _ (Lemma_4_5_5_1 R h x)
                --Goal : equivClass R x ∈ mod A R
  define        --Goal : ∃ (x_1 : A), equivClass R x_1 = equivClass R x
  apply Exists.intro x
  rfl
  done

lemma Theorem_4_5_4_part_2 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    pairwise_disjoint (mod A R) := by
  define
  fix X : Set A
  assume h2 : X ∈ mod A R
  fix Y : Set A
  assume h3 : Y ∈ mod A R           --Goal : X ≠ Y → empty (X ∩ Y)
  define at h2; define at h3
  obtain (x : A) (h4 : equivClass R x = X) from h2
  obtain (y : A) (h5 : equivClass R y = Y) from h3
  contrapos
  assume h6 : ∃ (x : A), x ∈ X ∩ Y  --Goal : X = Y
  obtain (z : A) (h7 : z ∈ X ∩ Y) from h6
  define at h7
  rewrite [←h4, ←h5] at h7 --h7 : z ∈ equivClass R x ∧ z ∈ equivClass R y
  have h8 : equivClass R z = equivClass R x :=
    (Lemma_4_5_5_2 R h x z).ltr h7.left
  have h9 : equivClass R z = equivClass R y :=
    (Lemma_4_5_5_2 R h y z).ltr h7.right
  show X = Y from
    calc X
      _ = equivClass R x := h4.symm
      _ = equivClass R z := h8.symm
      _ = equivClass R y := h9
      _ = Y              := h5
  done

lemma Theorem_4_5_4_part_3 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ X ∈ mod A R, ¬empty X := by
  fix X : Set A
  assume h2 : X ∈ mod A R  --Goal : ¬empty X
  define; double_neg       --Goal : ∃ (x : A), x ∈ X
  define at h2             --h2 : ∃ (x : A), equivClass R x = X
  obtain (x : A) (h3 : equivClass R x = X) from h2
  rewrite [←h3]
  show ∃ (x_1 : A), x_1 ∈ equivClass R x from
    Exists.intro x (Lemma_4_5_5_1 R h x)
  done

theorem Theorem_4_5_4 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    partition (mod A R) := And.intro (Theorem_4_5_4_part_1 R h)
      (And.intro (Theorem_4_5_4_part_2 R h) (Theorem_4_5_4_part_3 R h))

lemma overlap_implies_equal {A : Type}
    (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ Y ∈ F, ∀ (x : A), x ∈ X → x ∈ Y → X = Y := sorry

lemma Lemma_4_5_7_ref {A : Type} (F : Set (Set A)) (h : partition F):
    reflexive (EqRelFromPart F) := sorry

lemma Lemma_4_5_7_symm {A : Type} (F : Set (Set A)) (h : partition F):
    symmetric (EqRelFromPart F) := sorry

lemma Lemma_4_5_7_trans {A : Type} (F : Set (Set A)) (h : partition F):
    transitive (EqRelFromPart F) := sorry

lemma Lemma_4_5_7 {A : Type} (F : Set (Set A)) (h : partition F) :
    equiv_rel (EqRelFromPart F) := And.intro (Lemma_4_5_7_ref F h)
      (And.intro (Lemma_4_5_7_symm F h) (Lemma_4_5_7_trans F h))

lemma Lemma_4_5_8 {A : Type} (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ x ∈ X, equivClass (EqRelFromPart F) x = X := sorry

theorem Theorem_4_5_6 {A : Type} (F : Set (Set A)) (h: partition F) :
    ∃ (R : BinRel A), equiv_rel R ∧ mod A R = F := by
  set R : BinRel A := EqRelFromPart F
  apply Exists.intro R               --Goal : equiv_rel R ∧ mod A R = F
  apply And.intro (Lemma_4_5_7 F h)  --Goal : mod A R = F
  apply Set.ext
  fix X : Set A                      --Goal :  X ∈ mod A R ↔ X ∈ F
  apply Iff.intro
  · -- (→)
    assume h2 : X ∈ mod A R          --Goal : X ∈ F
    define at h2                     --h2 : ∃ (x : A), equivClass R x = X
    obtain (x : A) (h3 : equivClass R x = X) from h2
    have h4 : x ∈ ⋃₀ F := h.left x
    define at h4
    obtain (Y : Set A) (h5 : Y ∈ F ∧ x ∈ Y) from h4
    have h6 : equivClass R x = Y :=
      Lemma_4_5_8 F h Y h5.left x h5.right
    rewrite [←h3, h6]
    show Y ∈ F from h5.left
    done
  · -- (←)
    assume h2 : X ∈ F                --Goal : X ∈ mod A R
    have h3 : ¬empty X := h.right.right X h2
    define at h3; double_neg at h3   --h3 : ∃ (x : A), x ∈ X
    obtain (x : A) (h4 : x ∈ X) from h3
    define                       --Goal : ∃ (x : A), equivClass R x = X
    show ∃ (x : A), equivClass R x = X from
      Exists.intro x (Lemma_4_5_8 F h X h2 x h4)
    done
  done

-- ──── Chap5 ────
/- Copyright 2023-2025 Daniel J. Velleman -/


/- Definitions -/
def graph {A B : Type} (f : A → B) : Set (A × B) :=
    {(a, b) : A × B | f a = b}

def is_func_graph {A B : Type} (G : Set (A × B)) : Prop :=
    ∀ (x : A), ∃! (y : B), (x, y) ∈ G

def onto {A B : Type} (f : A → B) : Prop :=
  ∀ (y : B), ∃ (x : A), f x = y

def one_to_one {A B : Type} (f : A → B) : Prop :=
  ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2

def closed {A : Type} (f : A → A) (C : Set A) : Prop := ∀ x ∈ C, f x ∈ C

def closure {A : Type} (f : A → A) (B C : Set A) : Prop :=
  smallestElt (sub A) C {D : Set A | B ⊆ D ∧ closed f D}

def closed2 {A : Type} (f : A → A → A) (C : Set A) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, f x y ∈ C

def closure2 {A : Type} (f : A → A → A) (B C : Set A) : Prop :=
  smallestElt (sub A) C {D : Set A | B ⊆ D ∧ closed2 f D}

def closed_family {A : Type} (F : Set (A → A)) (C : Set A) : Prop :=
  ∀ f ∈ F, closed f C

def closure_family {A : Type} (F : Set (A → A)) (B C : Set A) : Prop :=
  smallestElt (sub A) C {D : Set A | B ⊆ D ∧ closed_family F D}

def image {A B : Type} (f : A → B) (X : Set A) : Set B :=
  {f x | x ∈ X}

def inverse_image {A B : Type} (f : A → B) (Y : Set B) : Set A :=
  {a : A | f a ∈ Y}

/- Section 5.1 -/
theorem graph_def {A B : Type} (f : A → B) (a : A) (b : B) :
    (a, b) ∈ graph f ↔ f a = b := by rfl

theorem func_from_graph_ltr {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) → is_func_graph F := sorry

--This proof is explained in Section 8.2
theorem func_from_graph_rtl {A B : Type} (F : Set (A × B)) :
    is_func_graph F → (∃ (f : A → B), graph f = F) := by
  assume h1 : is_func_graph F
  define at h1    --h1 : ∀ (x : A), ∃! (y : B), (x, y) ∈ F
  have h2 : ∀ (x : A), ∃ (y : B), (x, y) ∈ F := by
    fix x : A
    obtain (y : B) (h3 : (x, y) ∈ F)
      (h4 : ∀ (y1 y2 : B), (x, y1) ∈ F → (x, y2) ∈ F → y1 = y2) from h1 x
    show ∃ (y : B), (x, y) ∈ F from Exists.intro y h3
    done
  set f : A → B := fun (x : A) => Classical.choose (h2 x)
  apply Exists.intro f
  apply Set.ext
  fix (x, y) : A × B
  have h3 : (x, f x) ∈ F := Classical.choose_spec (h2 x)
  apply Iff.intro
  · -- (→)
    assume h4 : (x, y) ∈ graph f
    define at h4        --h4 : f x = y
    rewrite [h4] at h3
    show (x, y) ∈ F from h3
    done
  · -- (←)
    assume h4 : (x, y) ∈ F
    define              --Goal : f x = y
    obtain (z : B) (h5 : (x, z) ∈ F)
      (h6 : ∀ (y1 y2 : B), (x, y1) ∈ F → (x, y2) ∈ F → y1 = y2) from h1 x
    show f x = y from h6 (f x) y h3 h4
    done
  done

theorem func_from_graph {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) ↔ is_func_graph F :=
  Iff.intro (func_from_graph_ltr F) (func_from_graph_rtl F)

theorem Theorem_5_1_4 {A B : Type} (f g : A → B) :
    (∀ (a : A), f a = g a) → f = g := funext

example {A B : Type} (f g : A → B) :
    graph f = graph g → f = g := by
  assume h1 : graph f = graph g  --Goal : f = g
  apply funext                   --Goal : ∀ (x : A), f x = g x
  fix x : A
  have h2 : (x, f x) ∈ graph f := by
    define                       --Goal : f x = f x
    rfl
    done
  rewrite [h1] at h2             --h2 : (x, f x) ∈ graph g
  define at h2                   --h2 : g x = f x
  show f x = g x from h2.symm
  done

def square1 (n : Nat) : Nat := n ^ 2

def square2 : Nat → Nat := fun (n : Nat) => n ^ 2

example : square1 = square2 := by rfl

#eval square1 7     --Answer: 49

theorem Theorem_5_1_5 {A B C : Type} (f : A → B) (g : B → C) :
    ∃ (h : A → C), graph h = comp (graph g) (graph f) := by
  set h : A → C := fun (x : A) => g (f x)
  apply Exists.intro h
  apply Set.ext
  fix (a, c) : A × C
  apply Iff.intro
  · -- Proof that (a, c) ∈ graph h → (a, c) ∈ comp (graph g) (graph f)
    assume h1 : (a, c) ∈ graph h
    define at h1  --h1 : h a = c
    define        --Goal : ∃ (x : B), (a, x) ∈ graph f ∧ (x, c) ∈ graph g
    apply Exists.intro (f a)
    apply And.intro
    · -- Proof that (a, f a) ∈ graph f
      define
      rfl
      done
    · -- Proof that (f a, c) ∈ graph g
      define
      show g (f a) = c from h1
      done
    done
  · -- Proof that (a, c) ∈ comp (graph g) (graph f) → (a, c) ∈ graph h
    assume h1 : (a, c) ∈ comp (graph g) (graph f)
    define        --Goal : h a = c
    define at h1  --h1 : ∃ (x : B), (a, x) ∈ graph f ∧ (x, c) ∈ graph g
    obtain (b : B) (h2 : (a, b) ∈ graph f ∧ (b, c) ∈ graph g) from h1
    have h3 : (a, b) ∈ graph f := h2.left
    have h4 : (b, c) ∈ graph g := h2.right
    define at h3          --h3 : f a = b
    define at h4          --h4 : g b = c
    rewrite [←h3] at h4   --h4 : g (f a) = c
    show h a = c from h4
    done
  done

example {A B C D : Type} (f : A → B) (g : B → C) (h : C → D) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := by rfl

example {A B : Type} (f : A → B) : f ∘ id = f := by rfl

example {A B : Type} (f : A → B) : id ∘ f = f := by rfl

/- Section 5.2 -/
theorem Theorem_5_2_5_1 {A B C : Type} (f : A → B) (g : B → C) :
    one_to_one f → one_to_one g → one_to_one (g ∘ f) := by
  assume h1 : one_to_one f
  assume h2 : one_to_one g
  define at h1  --h1 : ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
  define at h2  --h2 : ∀ (x1 x2 : B), g x1 = g x2 → x1 = x2
  define        --Goal : ∀ (x1 x2 : A), (g ∘ f) x1 = (g ∘ f) x2 → x1 = x2
  fix a1 : A
  fix a2 : A    --Goal : (g ∘ f) a1 = (g ∘ f) a2 → a1 = a2
  define : (g ∘ f) a1; define : (g ∘ f) a2
                --Goal : g (f a1) = g (f a2) → a1 = a2
  assume h3 : g (f a1) = g (f a2)
  have h4 : f a1 = f a2 := h2 (f a1) (f a2) h3
  show a1 = a2 from h1 a1 a2 h4
  done

lemma comp_def {A B C : Type} (g : B → C) (f : A → B) (x : A) :
    (g ∘ f) x = g (f x) := by rfl

theorem Theorem_5_2_5_2 {A B C : Type} (f : A → B) (g : B → C) :
    onto f → onto g → onto (g ∘ f) := by
  assume h1 : onto f
  assume h2 : onto g
  define at h1           --h1 : ∀ (y : B), ∃ (x : A), f x = y
  define at h2           --h2 : ∀ (y : C), ∃ (x : B), g x = y
  define                 --Goal : ∀ (y : C), ∃ (x : A), (g ∘ f) x = y
  fix c : C
  obtain (b : B) (h3 : g b = c) from h2 c
  obtain (a : A) (h4 : f a = b) from h1 b
  apply Exists.intro a   --Goal : (g ∘ f) a = c
  rewrite [comp_def]     --Goal : g (f a) = c
  rewrite [←h4] at h3
  show g (f a) = c from h3
  done

/- Section 5.3 -/
theorem Theorem_5_3_1 {A B : Type}
    (f : A → B) (h1 : one_to_one f) (h2 : onto f) :
    ∃ (g : B → A), graph g = inv (graph f) := by
  rewrite [func_from_graph]   --Goal : is_func_graph (inv (graph f))
  define        --Goal : ∀ (x : B), ∃! (y : A), (x, y) ∈ inv (graph f)
  fix b : B
  exists_unique
  · -- Existence
    define at h2          --h2 : ∀ (y : B), ∃ (x : A), f x = y
    obtain (a : A) (h4 : f a = b) from h2 b
    apply Exists.intro a  --Goal : (b, a) ∈ inv (graph f)
    define                --Goal : f a = b
    show f a = b from h4
    done
  · -- Uniqueness
    fix a1 : A; fix a2 : A
    assume h3 : (b, a1) ∈ inv (graph f)
    assume h4 : (b, a2) ∈ inv (graph f) --Goal : a1 = a2
    define at h3          --h3 : f a1 = b
    define at h4          --h4 : f a2 = b
    rewrite [←h4] at h3   --h3 : f a1 = f a2
    define at h1          --h1 : ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
    show a1 = a2 from h1 a1 a2 h3
    done
  done

theorem Theorem_5_3_2_1 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : g ∘ f = id := by
  apply funext           --Goal : ∀ (x : A), (g ∘ f) x = id x
  fix a : A              --Goal : (g ∘ f) a = id a
  have h2 : (f a, a) ∈ graph g := by
    rewrite [h1]         --Goal : (f a, a) ∈ inv (graph f)
    define               --Goal : f a = f a
    rfl
    done
  define at h2           --h2 : g (f a) = a
  show (g ∘ f) a = id a from h2
  done

theorem Theorem_5_3_2_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : f ∘ g = id := sorry

theorem Theorem_5_3_3_1 {A B : Type} (f : A → B) (g : B → A)
    (h1 : g ∘ f = id) : one_to_one f := by
  define              --Goal : ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
  fix a1 : A; fix a2 : A
  assume h2 : f a1 = f a2
  show a1 = a2 from
    calc a1
      _ = id a1 := by rfl
      _ = (g ∘ f) a1 := by rw [h1]
      _ = g (f a1) := by rfl
      _ = g (f a2) := by rw [h2]
      _ = (g ∘ f) a2 := by rfl
      _ = id a2 := by rw [h1]
      _ = a2 := by rfl
  done

theorem Theorem_5_3_3_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : f ∘ g = id) : onto f := sorry

theorem Theorem_5_3_5 {A B : Type} (f : A → B) (g : B → A)
    (h1 : g ∘ f = id) (h2 : f ∘ g = id) : graph g = inv (graph f) := by
  have h3 : one_to_one f := Theorem_5_3_3_1 f g h1
  have h4 : onto f := Theorem_5_3_3_2 f g h2
  obtain (g' : B → A) (h5 : graph g' = inv (graph f))
    from Theorem_5_3_1 f h3 h4
  have h6 : g' ∘ f = id := Theorem_5_3_2_1 f g' h5
  have h7 : g = g' :=
    calc g
      _ = id ∘ g := by rfl
      _ = (g' ∘ f) ∘ g := by rw [h6]
      _ = g' ∘ (f ∘ g) := by rfl
      _ = g' ∘ id := by rw [h2]
      _ = g' := by rfl
  rewrite [←h7] at h5
  show graph g = inv (graph f) from h5
  done

/- Section 5.4 -/
theorem Theorem_5_4_5 {A : Type} (f : A → A) (B : Set A) :
    ∃ (C : Set A), closure f B C := by
  set F : Set (Set A) := {D : Set A | B ⊆ D ∧ closed f D}
  set C : Set A := ⋂₀ F
  apply Exists.intro C    --Goal : closure f B C
  define                  --Goal : C ∈ F ∧ ∀ x ∈ F, C ⊆ x
  apply And.intro
  · -- Proof that C ∈ F
    define                  --Goal : B ⊆ C ∧ closed f C
    apply And.intro
    · -- Proof that B ⊆ C
      fix a : A
      assume h1 : a ∈ B       --Goal : a ∈ C
      define                  --Goal : ∀ t ∈ F, a ∈ t
      fix D : Set A
      assume h2 : D ∈ F
      define at h2            --h2 : B ⊆ D ∧ closed f D
      show a ∈ D from h2.left h1
      done
    · -- Proof that C is closed under f
      define                  --Goal : ∀ x ∈ C, f x ∈ C
      fix a : A
      assume h1 : a ∈ C       --Goal : f a ∈ C
      define                  --Goal : ∀ t ∈ F, f a ∈ t
      fix D : Set A
      assume h2 : D ∈ F       --Goal : f a ∈ D
      define at h1            --h1 : ∀ t ∈ F, a ∈ t
      have h3 : a ∈ D := h1 D h2
      define at h2            --h2 : B ⊆ D ∧ closed f D
      have h4 : closed f D := h2.right
      define at h4            --h4 : ∀ x ∈ D, f x ∈ D
      show f a ∈ D from h4 a h3
      done
    done
  · -- Proof that C is smallest
    fix D : Set A
    assume h1 : D ∈ F      --Goal : sub A C D
    define
    fix a : A
    assume h2 : a ∈ C       --Goal : a ∈ D
    define at h2            --h2 : ∀ t ∈ F, a ∈ t
    show a ∈ D from h2 D h1
    done
  done

def plus (m n : Int) : Int := m + n

def plus' : Int → Int → Int := fun (m n : Int) => m + n

def plus'' : Int → Int → Int := fun (m : Int) => (fun (n : Int) => m + n)

example : plus = plus'' := by rfl

example : plus' = plus'' := by rfl

#eval plus 3 2     --Answer: 5

theorem Theorem_5_4_9 {A : Type} (f : A → A → A) (B : Set A) :
    ∃ (C : Set A), closure2 f B C := sorry

/- Section 5.5 -/
theorem image_def {A B : Type} (f : A → B) (X : Set A) (b : B) :
    b ∈ image f X ↔ ∃ x ∈ X, f x = b := by rfl

theorem inverse_image_def {A B : Type} (f : A → B) (Y : Set B) (a : A) :
    a ∈ inverse_image f Y ↔ f a ∈ Y := by rfl

theorem Theorem_5_5_2_1 {A B : Type} (f : A → B) (W X : Set A) :
    image f (W ∩ X) ⊆ image f W ∩ image f X := by
  fix y : B
  assume h1 : y ∈ image f (W ∩ X)  --Goal : y ∈ image f W ∩ image f X
  define at h1                     --h1 : ∃ x ∈ W ∩ X, f x = y
  obtain (x : A) (h2 : x ∈ W ∩ X ∧ f x = y) from h1
  define : x ∈ W ∩ X at h2         --h2 : (x ∈ W ∧ x ∈ X) ∧ f x = y
  apply And.intro
  · -- Proof that y ∈ image f W
    define                         --Goal : ∃ x ∈ W, f x = y
    show ∃ (x : A), x ∈ W ∧ f x = y from
      Exists.intro x (And.intro h2.left.left h2.right)
    done
  · -- Proof that y ∈ image f X
    show y ∈ image f X from
      Exists.intro x (And.intro h2.left.right h2.right)
    done
  done

theorem Theorem_5_5_2_2 {A B : Type} (f : A → B) (W X : Set A)
    (h1 : one_to_one f) : image f (W ∩ X) = image f W ∩ image f X := by
  apply Set.ext
  fix y : B      --Goal : y ∈ image f (W ∩ X) ↔ y ∈ image f W ∩ image f X
  apply Iff.intro
  · -- (→)
    assume h2 : y ∈ image f (W ∩ X)
    show y ∈ image f W ∩ image f X from Theorem_5_5_2_1 f W X h2
    done
  · -- (←)
    assume h2 : y ∈ image f W ∩ image f X  --Goal : y ∈ image f (W ∩ X)
    define at h2                  --h2 : y ∈ image f W ∧ y ∈ image f X
    rewrite [image_def, image_def] at h2
          --h2 : (∃ x ∈ W, f x = y) ∧ ∃ x ∈ X, f x = y
    obtain (x1 : A) (h3 : x1 ∈ W ∧ f x1 = y) from h2.left
    obtain (x2 : A) (h4 : x2 ∈ X ∧ f x2 = y) from h2.right
    have h5 : f x2 = y := h4.right
    rewrite [←h3.right] at h5  --h5 : f x2 = f x1
    define at h1               --h1 : ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
    have h6 : x2 = x1 := h1 x2 x1 h5
    rewrite [h6] at h4           --h4 : x1 ∈ X ∧ f x1 = y
    show y ∈ image f (W ∩ X) from
      Exists.intro x1 (And.intro (And.intro h3.left h4.left) h3.right)
    done
  done

-- ──── Chap8Part1 ────
/- Copyright 2023-2025 Daniel J. Velleman -/


open Classical

/- Definitions -/
def equinum (U V : Type) : Prop :=
  ∃ (f : U → V), one_to_one f ∧ onto f

notation:50  U:50 " ∼ " V:50 => equinum U V

def Subtype_elt {U : Type} {A : Set U} {x : U} (h : x ∈ A) : ↑A :=
  Subtype.mk x h

def I (n : Nat) : Set Nat := {k : Nat | k < n}

def finite (U : Type) : Prop := ∃ (n : Nat), I n ∼ U

def denum (U : Type) : Prop := Nat ∼ U

def ctble (U : Type) : Prop := finite U ∨ denum U

def range {U V : Type} (f : U → V) : Set V := {y : V | ∃ (x : U), f x = y}

lemma elt_range {U V : Type} (f : U → V) (x : U) : f x ∈ range f := by
  define                 --Goal : ∃ (x_1 : U), f x_1 = f x
  apply Exists.intro x
  rfl
  done

def func_to_range {U V : Type} (f : U → V) (x : U) : range f :=
  Subtype_elt (elt_range f x)

def func_restrict {U V : Type}
  (f : U → V) (A : Set U) (x : A) : V := f x.val

def one_one_on {U V : Type} (f : U → V) (A : Set U) : Prop :=
  ∀ ⦃x1 x2 : U⦄, x1 ∈ A → x2 ∈ A → f x1 = f x2 → x1 = x2

def func_to_type {U V : Type} {B : Set V}
  (f : U → B) (x : U) : V := (f x).val

noncomputable def func_extend {U V : Type} {A : Set U}
  (f : A → V) (v : V) (u : U) : V :=
  if test : u ∈ A then f (Subtype_elt test) else v

def constant_func (U : Type) {V : Type} (v : V) (x : U) : V := v

def numElts {U : Type} (A : Set U) (n : Nat) : Prop := I n ∼ A

/- Section 8.1 -/
lemma id_one_one (U : Type) : one_to_one (@id U) := by
  fix x1 : U; fix x2 : U
  assume h : id x1 = id x2
  show x1 = x2 from h
  done

lemma id_onto (U : Type) : onto (@id U) := by
  fix y : U              --Goal : ∃ (x : U), id x = y
  apply Exists.intro y   --Goal : id y = y
  rfl
  done

theorem Theorem_8_1_3_1 (U : Type) : U ∼ U := by
  apply Exists.intro id
  show one_to_one id ∧ onto id from And.intro (id_one_one U) (id_onto U)
  done

theorem Theorem_8_1_3_2 {U V : Type}
    (h : U ∼ V) : V ∼ U := by
  obtain (f : U → V) (h1 : one_to_one f ∧ onto f) from h
  obtain (finv : V → U) (h2 : graph finv = inv (graph f)) from
    Theorem_5_3_1 f h1.left h1.right
  apply Exists.intro finv
  have h3 : finv ∘ f = id := Theorem_5_3_2_1 f finv h2
  have h4 : f ∘ finv = id := Theorem_5_3_2_2 f finv h2
  show one_to_one finv ∧ onto finv from
    And.intro (Theorem_5_3_3_1 finv f h4) (Theorem_5_3_3_2 finv f h3)
  done

theorem Theorem_8_1_3_3 {U V W : Type}
    (h1 : U ∼ V) (h2 : V ∼ W) : U ∼ W := by
  obtain (f : U → V) (h3 : one_to_one f ∧ onto f) from h1
  obtain (g : V → W) (h4 : one_to_one g ∧ onto g) from h2
  apply Exists.intro (g ∘ f)
  show one_to_one (g ∘ f) ∧ onto (g ∘ f) from
    And.intro (Theorem_5_2_5_1 f g h3.left h4.left)
    (Theorem_5_2_5_2 f g h3.right h4.right)
  done

theorem wishful_thinking?
    {U : Type} (A : Set U) : A ∼ A := Theorem_8_1_3_1 A

#check @wishful_thinking?   --∀ {U : Type} (A : Set U), ↑A ∼ ↑A

lemma I_def (k n : Nat) : k ∈ I n ↔ k < n := by rfl

lemma denum_def (U : Type) : denum U ↔ Nat ∼ U := by rfl

lemma ftr_def {U V : Type} (f : U → V) (x : U) :
    (func_to_range f x).val = f x := by rfl

lemma ftr_onto {U V : Type} (f : U → V) : onto (func_to_range f) := by
  fix y : range f              --y has type ↑(range f)
  have h1 : y.val ∈ range f := y.property
  define at h1                 --h1 : ∃ (x : U), f x = y.val
  obtain (x : U) (h2 : f x = y.val) from h1
  apply Exists.intro x         --Goal : func_to_range f x = y
  apply Subtype.ext            --Goal : (func_to_range f x).val = y.val
  rewrite [ftr_def, h2]
  rfl
  done

lemma ftr_one_one_of_one_one {U V : Type} {f : U → V}
    (h : one_to_one f) : one_to_one (func_to_range f) := by
  fix x1 : U; fix x2 : U
  assume h1 : func_to_range f x1 = func_to_range f x2
  have h2 : f x1 = f x2 :=
    calc f x1
      _ = (func_to_range f x1).val := (ftr_def f x1).symm
      _ = (func_to_range f x2).val := by rw [h1]
      _ = f x2 := ftr_def f x2
  show x1 = x2 from h x1 x2 h2
  done

theorem equinum_range {U V : Type} {f : U → V}
    (h : one_to_one f) : U ∼ range f := by
  apply Exists.intro (func_to_range f)
  show one_to_one (func_to_range f) ∧ onto (func_to_range f) from
    And.intro (ftr_one_one_of_one_one h) (ftr_onto f)
  done

lemma fr_def {U V : Type} (f : U → V) (A : Set U) (x : A) :
    func_restrict f A x = f x.val := by rfl

lemma fr_one_one_of_one_one_on {U V : Type} {f : U → V} {A : Set U}
    (h : one_one_on f A) : one_to_one (func_restrict f A) := by
  fix x1 : A; fix x2 : A                    --x1 and x2 have type ↑A
  assume h1 : func_restrict f A x1 = func_restrict f A x2
  rewrite [fr_def, fr_def] at h1            --h1 : f x1.val = f x2.val
  apply Subtype.ext                         --Goal : x1.val = x2.val
  show x1.val = x2.val from h x1.property x2.property h1
  done

lemma elt_image {U V : Type} {A : Set U} {x : U}
    (f : U → V) (h : x ∈ A) : f x ∈ image f A := by
  define                   --Goal : ∃ x_1 ∈ A, f x_1 = f x
  apply Exists.intro x     --Goal : x ∈ A ∧ f x = f x
  apply And.intro h
  rfl
  done

lemma fr_range {U V : Type} (f : U → V) (A : Set U) :
    range (func_restrict f A) = image f A := by
  apply Set.ext
  fix y : V
  apply Iff.intro
  · -- (→)
    assume h1 : y ∈ range (func_restrict f A) --Goal : y ∈ image f A
    define at h1
    obtain (a : A) (h2 : func_restrict f A a = y) from h1
    rewrite [←h2, fr_def]                     --Goal : f a.val ∈ image f A
    show f a.val ∈ image f A from elt_image f a.property
    done
  · -- (←)
    assume h1 : y ∈ image f A         --Goal : y ∈ range (func_restrict f A)
    define at h1
    obtain (a : U) (h2 : a ∈ A ∧ f a = y) from h1
    set aA : A := Subtype_elt h2.left
    have h3 : func_restrict f A aA = f a := fr_def f A aA
    rewrite [←h2.right, ←h3]
    show func_restrict f A aA ∈ range (func_restrict f A) from
      elt_range (func_restrict f A) aA
    done
  done

theorem equinum_image {U V : Type} {A : Set U} {f : U → V}
    (h : one_one_on f A) : A ∼ image f A := by
  rewrite [←fr_range f A]          --Goal : A ∼ range (func_restrict f A)
  have h1 : one_to_one (func_restrict f A) :=
    fr_one_one_of_one_one_on h
  show A ∼ range (func_restrict f A) from equinum_range h1
  done

lemma ftt_def {U V : Type} {B : Set V} (f : U → B) (x : U) :
    func_to_type f x = (f x).val := by rfl

lemma fe_elt {U V : Type} {A : Set U} (f : A → V) (v : V) (a : A) :
    func_extend f v a.val = f a := dif_pos a.property

example (U V : Type) (f : U → V) :
    func_to_type (func_to_range f) = f := by rfl

example (U V : Type) (A : Set U) (f : A → V) (v : V) :
    func_restrict (func_extend f v) A = f := sorry

lemma ftt_range_of_onto {U V : Type} {B : Set V} {f : U → B}
    (h : onto f) : range (func_to_type f) = B := by
  apply Set.ext
  fix y : V
  apply Iff.intro
  · -- (→)
    assume h1 : y ∈ range (func_to_type f)
    obtain (x : U) (h2 : func_to_type f x = y) from h1
    rewrite [←h2, ftt_def]
    show (f x).val ∈ B from (f x).property
    done
  · -- (←)
    assume h1 : y ∈ B
    set yB : B := Subtype_elt h1
    obtain (x : U) (h2 : f x = yB) from h yB
    apply Exists.intro x
    show func_to_type f x = y from
      calc func_to_type f x
        _ = (f x).val := ftt_def f x
        _ = yB.val := by rw [h2]
        _ = y := by rfl
    done
  done

lemma ftt_one_one_of_one_one {U V : Type} {B : Set V} {f : U → B}
    (h : one_to_one f) : one_to_one (func_to_type f) := by
  fix x1 : U; fix x2 : U
  assume h1 : func_to_type f x1 = func_to_type f x2
  have h2 : f x1 = f x2 := by
    apply Subtype.ext
    rewrite [ftt_def, ftt_def] at h1
    show (f x1).val = (f x2).val from h1
    done
  show x1 = x2 from h x1 x2 h2
  done

lemma fe_image {U V : Type} {A : Set U}
    (f : A → V) (v : V) : image (func_extend f v) A = range f := by
  apply Set.ext
  fix y : V
  apply Iff.intro
  · --
    assume h1 : y ∈ image (func_extend f v) A
    define at h1
    obtain (x : U) (h2 : x ∈ A ∧ func_extend f v x = y) from h1
    set xA : A := Subtype_elt h2.left
    have h3 : func_extend f v x = f xA := fe_elt f v xA
    rewrite [←h2.right, h3]
    show f xA ∈ range f from elt_range f xA
    done
  · --
    assume h1 : y ∈ range f
    define at h1
    obtain (xA : A) (h2 : f xA = y) from h1
    rewrite [←h2, ←fe_elt f v]
    show func_extend f v xA.val ∈ image (func_extend f v) A from
      elt_image (func_extend f v) xA.property
    done
  done

lemma fe_one_one_on_of_one_one {U V : Type} {A : Set U} {f : A → V}
    (h : one_to_one f) (v : V) : one_one_on (func_extend f v) A := by
  set F : U → V := func_extend f v
  define
  fix x1 : U; fix x2 : U
  assume h1 : x1 ∈ A
  assume h2 : x2 ∈ A
  assume h3 : F x1 = F x2
  set x1A : A := Subtype_elt h1
  set x2A : A := Subtype_elt h2
  have h4 : F x1 = f x1A := fe_elt f v x1A
  have h5 : F x2 = f x2A := fe_elt f v x2A
  rewrite [h4, h5] at h3       --h3 : f x1A = f x2A
  have h6 : x1A = x2A := h x1A x2A h3
  show x1 = x2 from
    calc x1
      _ = x1A.val := by rfl
      _ = x2A.val := by rw [h6]
      _ = x2 := by rfl
  done

theorem type_to_type_of_equinum {U V : Type} {A : Set U} {B : Set V}
    (h : A ∼ B) (v : V) :
    ∃ (f : U → V), one_one_on f A ∧ image f A = B := by
  obtain (g : A → B) (h1 : one_to_one g ∧ onto g) from h
  set gtt : A → V := func_to_type g
  set f : U → V := func_extend gtt v
  apply Exists.intro f
  apply And.intro
  · -- Proof of one_to_one_on f A
    have h2 : one_to_one gtt := ftt_one_one_of_one_one h1.left
    show one_one_on f A from fe_one_one_on_of_one_one h2 v
    done
  · -- Proof of image f A = B
    have h2 : range gtt = B := ftt_range_of_onto h1.right
    have h3 : image f A = range gtt := fe_image gtt v
    rewrite [h3, h2]
    rfl
    done
  done

/- Section 8.1½ -/
lemma numElts_def {U : Type} (A : Set U) (n : Nat) :
    numElts A n ↔ I n ∼ A := by rfl

lemma finite_def {U : Type} (A : Set U) :
    finite A ↔ ∃ (n : Nat), numElts A n := by rfl

lemma not_empty_iff_exists_elt {U : Type} {A : Set U} :
    ¬empty A ↔ ∃ (x : U), x ∈ A := by
  define : empty A
  double_neg
  rfl
  done

lemma elt_empty_implies {U : Type} {A : Set U} {x : U} {P : Prop}
    (h : empty A) : x ∈ A → P := by
  assume h1 : x ∈ A
  contradict h
  show ∃ (x : U), x ∈ A from Exists.intro x h1
  done

lemma one_one_on_empty {U : Type} {A : Set U}
    (f : U → Nat) (h : empty A) : one_one_on f A := by
  fix x1 : U; fix x2 : U
  show x1 ∈ A → x2 ∈ A → f x1 = f x2 → x1 = x2 from
    elt_empty_implies h
  done

lemma image_empty {U : Type} {A : Set U}
    (f : U → Nat) (h : empty A) : image f A = I 0 := sorry

theorem zero_elts_iff_empty {U : Type} (A : Set U) :
    numElts A 0 ↔ empty A := by
  apply Iff.intro
  · -- (→)
    assume h1 : numElts A 0
    define at h1
    obtain (f : I 0 → A) (h2 : one_to_one f ∧ onto f) from h1
    by_contra h3
    rewrite [not_empty_iff_exists_elt] at h3
    obtain (x : U) (h4 : x ∈ A) from h3
    set xA : A := Subtype_elt h4
    obtain (n : I 0) (h5 : f n = xA) from h2.right xA
    have h6 : n.val < 0 := n.property
    linarith
    done
  · -- (←)
    assume h1 : empty A
    rewrite [numElts_def]
    set f : U → Nat := constant_func U 0
    have h2 : one_one_on f A := one_one_on_empty f h1
    have h3 : image f A = I 0 := image_empty f h1
    have h4 : A ∼ image f A := equinum_image h2
    rewrite [h3] at h4
    show I 0 ∼ A from Theorem_8_1_3_2 h4
    done
  done

theorem nonempty_of_pos_numElts {U : Type} {A : Set U} {n : Nat}
    (h1 : numElts A n) (h2 : n > 0) : ∃ (x : U), x ∈ A := by
  define at h1
  obtain (f : I n → A) (h3 : one_to_one f ∧ onto f) from h1
  have h4 : 0 ∈ I n := h2
  set x : A := f (Subtype_elt h4)
  show ∃ (x : U), x ∈ A from Exists.intro x.val x.property
  done

def incr_from (k n : Nat) : Nat := if n < k then n else n + 1

lemma incr_from_lt {k n : Nat} (h : n < k) :
    incr_from k n = n := if_pos h

lemma incr_from_nlt {k n : Nat} (h : ¬n < k) :
    incr_from k n = n + 1 := if_neg h

lemma incr_from_iff (k n : Nat) : incr_from k n < k ↔ n < k := by
  apply Iff.intro
  · -- (→)
    assume h1 : incr_from k n < k
    by_contra h2
    rewrite [incr_from_nlt h2] at h1
    linarith  --h1 : n + 1 < k contradicts h2 : ¬n < k
    done
  · -- (←)
    assume h1 : n < k
    rewrite [incr_from_lt h1]
    show n < k from h1
    done
  done

lemma incr_from_one_one (k : Nat) :
    one_to_one (incr_from k) := by
  fix n1 : Nat; fix n2 : Nat
  assume h1 : incr_from k n1 = incr_from k n2
  have h2 : n1 < k ↔ n2 < k :=
    calc n1 < k
      _ ↔ incr_from k n1 < k := (incr_from_iff k n1).symm
      _ ↔ incr_from k n2 < k := by rw [h1]
      _ ↔ n2 < k := incr_from_iff k n2
  by_cases h3 : n1 < k
  · -- Case 1. h3 : n1 < k
    have h4 : n2 < k := h2.ltr h3
    rewrite [incr_from_lt h3, incr_from_lt h4] at h1
    show n1 = n2 from h1
    done
  · -- Case 2. h3 : ¬n1 < k
    have h4 : ¬n2 < k := by
      contradict h3 with h4
      show n1 < k from h2.rtl h4
      done
    rewrite [incr_from_nlt h3, incr_from_nlt h4] at h1
    linarith
    done
  done

lemma incr_from_image {k n : Nat} (h : k < n + 1) :
    image (incr_from k) (I n) = I (n + 1) \ {k} := by
  apply Set.ext
  fix m : Nat
  have h1 : m ∈ I (n + 1) \ {k} ↔ m < n + 1 ∧ m ≠ k := by rfl
  rewrite [h1]
  apply Iff.intro
  · -- (→)
    assume h2 : m ∈ image (incr_from k) (I n)
    obtain (t : Nat) (h3 : t ∈ I n ∧ incr_from k t = m) from h2
    rewrite [I_def] at h3
    by_cases h4 : t < k
    · -- Case 1. h4 : t < k
      rewrite [incr_from_lt h4] at h3
      have h5 : m < n + 1 := by linarith --m = t < n < n + 1
      have h6 : m ≠ k := by linarith     --m = t < k
      show m < n + 1 ∧ m ≠ k from And.intro h5 h6
      done
    · -- Case 2. h4 : ¬t < k
      rewrite [incr_from_nlt h4] at h3
      have h5 : m < n + 1 := by linarith --m = t + 1 and t < n
      have h6 : m ≠ k := by linarith     --m = t + 1 and ¬t < k
      show m < n + 1 ∧ m ≠ k from And.intro h5 h6
      done
    done
  · -- (→)
    assume h2 : m < n + 1 ∧ m ≠ k
    by_cases h3 : m < k
    · -- Case 1. h3 : m < k
      apply Exists.intro m
      rewrite [I_def]
      apply And.intro _ (incr_from_lt h3)
      linarith                        --m < k < n + 1
      done
    · -- Case 2. h3 : ¬m < k
      have h4 : m = k ∨ k < m := Nat.eq_or_lt_of_not_lt h3
      disj_syll h4 h2.right           --h4 : k < m
      have h5 : 1 ≤ m := by linarith
      obtain (t : Nat) (h6 : m = t + 1) from
        Nat.exists_eq_add_of_le' h5
      apply Exists.intro t
      rewrite [I_def, h6]
      have h7 : ¬t < k := by linarith --k < m = t + 1
      apply And.intro _ (incr_from_nlt h7)
      linarith                        --t + 1 = m < n + 1
    done
  done

lemma one_one_on_of_one_one {U V : Type} {f : U → V}
    (h : one_to_one f) (A : Set U) : one_one_on f A := by
  define
  fix x1 : U; fix x2 : U
  assume h1 : x1 ∈ A
  assume h2 : x2 ∈ A
  show f x1 = f x2 → x1 = x2 from h x1 x2
  done

lemma I_equinum_I_remove_one {k n : Nat}
    (h : k < n + 1) : I n ∼ ↑(I (n + 1) \ {k}) := by
  rewrite [←incr_from_image h]
  show I n ∼ image (incr_from k) (I n) from
    equinum_image (one_one_on_of_one_one (incr_from_one_one k) (I n))
  done

lemma remove_one_equinum
    {U V : Type} {A : Set U} {B : Set V} {a : U} {b : V} {f : U → V}
    (h1 : one_one_on f A) (h2 : image f A = B)
    (h3 : a ∈ A) (h4 : f a = b) : ↑(A \ {a}) ∼ ↑(B \ {b}) := sorry

theorem remove_one_numElts {U : Type} {A : Set U} {n : Nat} {a : U}
    (h1 : numElts A (n + 1)) (h2 : a ∈ A) : numElts (A \ {a}) n := by
  rewrite [numElts_def] at h1; rewrite [numElts_def]
    --h1 : I (n + 1) ∼ A;  Goal : I n ∼ ↑(A \ {a})
  obtain (f : Nat → U) (h3 : one_one_on f (I (n + 1)) ∧
    image f (I (n + 1)) = A) from type_to_type_of_equinum h1 a
  rewrite [←h3.right] at h2
  obtain (k : Nat) (h4 : k ∈ I (n + 1) ∧ f k = a) from h2
  have h5 : ↑(I (n + 1) \ {k}) ∼ ↑(A \ {a}) :=
    remove_one_equinum h3.left h3.right h4.left h4.right
  have h6 : k < n + 1 := h4.left
  have h7 : I n ∼ ↑(I (n + 1) \ {k}) := I_equinum_I_remove_one h6
  show I n ∼ ↑(A \ {a}) from Theorem_8_1_3_3 h7 h5
  done

lemma singleton_of_diff_empty {U : Type} {A : Set U} {a : U}
    (h1 : a ∈ A) (h2 : empty (A \ {a})) : A = {a} := sorry

lemma one_one_on_I_1 {U : Type} (f : Nat → U) : one_one_on f (I 1) := by
  fix x1 : Nat; fix x2 : Nat
  assume h1 : x1 ∈ I 1
  assume h2 : x2 ∈ I 1
  assume h3 : f x1 = f x2
  define at h1; define at h2   --h1 : x1 < 1; h2 : x2 < 1
  linarith
  done

lemma image_I_1 {U : Type} (f : Nat → U) : image f (I 1) = {f 0} := by
  apply Set.ext
  fix y
  apply Iff.intro
  · -- (→)
    assume h1 : y ∈ image f (I 1)
    define at h1; define
    obtain (x : Nat) (h2 : x ∈ I 1 ∧ f x = y) from h1
    have h3 : x < 1 := h2.left
    have h4 : x = 0 := by linarith
    rewrite [←h2.right, h4]
    rfl
    done
  · -- (←)
    assume h1 : y ∈ {f 0}
    define at h1; define
    apply Exists.intro 0
    apply And.intro _ h1.symm
    define
    linarith
    done
  done

lemma singleton_one_elt {U : Type} (u : U) : numElts {u} 1 := by
  rewrite [numElts_def]  --Goal : I 1 ∼ {u}
  set f : Nat → U := constant_func Nat u
  have h1 : one_one_on f (I 1) := one_one_on_I_1 f
  have h2 : image f (I 1) = {f 0} := image_I_1 f
  have h3 : f 0 = u := by rfl
  rewrite [←h3, ←h2]
  show I 1 ∼ image f (I 1) from equinum_image h1
  done

theorem one_elt_iff_singleton {U : Type} (A : Set U) :
    numElts A 1 ↔ ∃ (x : U), A = {x} := by
  apply Iff.intro
  · -- (→)
    assume h1 : numElts A 1  --Goal : ∃ (x : U), A = {x}
    have h2 : 1 > 0 := by linarith
    obtain (x : U) (h3 : x ∈ A) from nonempty_of_pos_numElts h1 h2
    have h4 : numElts (A \ {x}) 0 := remove_one_numElts h1 h3
    rewrite [zero_elts_iff_empty] at h4
    show ∃ (x : U), A = {x} from
      Exists.intro x (singleton_of_diff_empty h3 h4)
    done
  · -- (←)
    assume h1 : ∃ (x : U), A = {x}
    obtain (x : U) (h2 : A = {x}) from h1
    rewrite [h2]
    show numElts {x} 1 from singleton_one_elt x
    done
  done

-- ──── Chap6 ────
/- Copyright 2023-2025 Daniel J. Velleman -/


/- Definitions and theorems in Chap8Part1 and HTPIDefs

theorem zero_elts_iff_empty {A : Type} (X : Set A) :
    numElts X 0 ↔ empty X

theorem one_elt_iff_singleton {A : Type} (X : Set A) :
    numElts X 1 ↔ ∃ (x : A), X = {x}

theorem nonempty_of_pos_numElts {A : Type} {X : Set A} {n : Nat}
    (h1 : numElts X n) (h2 : n > 0) : ∃ (x : A), x ∈ X

theorem remove_one_numElts {A : Type} {X : Set A} {n : Nat} {x : A}
    (h1 : numElts X (n + 1)) (h2 : x ∈ X) : numElts (X \ {x}) n

def sum_seq {A : Type} [AddZeroClass A] (m k : Nat) (f : Nat → A) : A :=
  match m with
    | 0 => 0
    | n + 1 => sum_seq n k f + f (k + n)

theorem sum_base {A : Type} [AddZeroClass A] {k : Nat} {f : Nat → A} :
    Sum i from k to k, f i = f k

theorem sum_step {A : Type} [AddZeroClass A] {k n : Nat} {f : Nat → A}
    (h : k ≤ n) : Sum i from k to (n + 1), f i = (Sum i from k to n, f i) + f (n + 1)

theorem sum_from_zero_step {A : Type} [AddZeroClass A] {n : Nat} {f : Nat → A} :
    Sum i from 0 to (n + 1), f i = (Sum i from 0 to n, f i) + f (n + 1)
-/

/- Definitions -/
def nat_even (n : Nat) : Prop := ∃ (k : Nat), n = 2 * k

def nat_odd (n : Nat) : Prop := ∃ (k : Nat), n = 2 * k + 1

def extendPO {A : Type} (R : BinRel A) (b : A) (x y : A) : Prop :=
  R x y ∨ (R x b ∧ ¬R y b)

def fact (k : Nat) : Nat :=
  match k with
    | 0 => 1
    | n + 1 => (n + 1) * fact n

def Fib (n : Nat) : Nat :=
  match n with
    | 0 => 0
    | 1 => 1
    | k + 2 => Fib k + Fib (k + 1)

def rep_image {A : Type} (f : A → A) (n : Nat) (B : Set A) : Set A :=
  match n with
    | 0 => B
    | k + 1 => image f (rep_image f k B)

def cumul_image {A : Type} (f : A → A) (B : Set A) : Set A :=
  {x : A | ∃ (n : Nat), x ∈ rep_image f n B}

/- Section 6.1 -/
theorem Like_Example_6_1_2 :
    ∀ (n : Nat), 3 ∣ n ^ 3 + 2 * n := by
  by_induc
  · -- Base Case
    define         --Goal : ∃ (c : Nat), 0 ^ 3 + 2 * 0 = 3 * c
    apply Exists.intro 0
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : 3 ∣ n ^ 3 + 2 * n
    define at ih   --ih : ∃ (c : Nat), n ^ 3 + 2 * n = 3 * c
    obtain (k : Nat) (h1 : n ^ 3 + 2 * n = 3 * k) from ih
    define         --Goal : ∃ (c : Nat), (n + 1) ^ 3 + 2 * (n + 1) = 3 * c
    apply Exists.intro (k + n ^ 2 + n + 1)
    show (n + 1) ^ 3 + 2 * (n + 1) = 3 * (k + n ^ 2 + n + 1) from
      calc (n + 1) ^ 3 + 2 * (n + 1)
        _ = n ^ 3 + 2 * n + 3 * n ^ 2 + 3 * n + 3 := by ring
        _ = 3 * k + 3 * n ^ 2 + 3 * n + 3 := by rw [h1]
        _ = 3 * (k + n ^ 2 + n + 1) := by ring
    done
  done

theorem Like_Example_6_1_1 :
    ∀ (n : Nat), (Sum i from 0 to n, 2 ^ i) + 1 = 2 ^ (n + 1) := by
  by_induc
  · -- Base Case
    rewrite [sum_base]
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : (Sum i from 0 to n, 2 ^ i) + 1 = 2 ^ (n + 1)
    show (Sum i from 0 to n + 1, 2 ^ i) + 1 = 2 ^ (n + 1 + 1) from
      calc (Sum i from 0 to n + 1, 2 ^ i) + 1
        _ = (Sum i from 0 to n, 2 ^ i) + 2 ^ (n + 1) + 1 := by
              rw [sum_from_zero_step]
        _ = (Sum i from 0 to n, 2 ^ i) + 1 + 2 ^ (n + 1) := by ring
        _ = 2 ^ (n + 1) + 2 ^ (n + 1) := by rw [ih]
        _ = 2 ^ (n + 1 + 1) := by ring
    done
  done

theorem Example_6_1_3 : ∀ n ≥ 5, 2 ^ n > n ^ 2 := by
  by_induc
  · -- Base Case
    decide
    done
  · -- Induction Step
    fix n : Nat
    assume h1 : n ≥ 5
    assume ih : 2 ^ n > n ^ 2
    have h2 : n * n ≥ 5 * n := Nat.mul_le_mul_right n h1
    show 2 ^ (n + 1) > (n + 1) ^ 2 from
      calc 2 ^ (n + 1)
        _ = 2 * 2 ^ n := by ring
        _ > 2 * n ^ 2 := by linarith
        _ ≥ n ^ 2 + 5 * n := by linarith
        _ > n ^ 2 + 2 * n + 1 := by linarith
        _ = (n + 1) ^ 2 := by ring
    done
  done

#eval 2 - 3       --Answer: 0

theorem Example_6_1_1 :
    ∀ (n : Nat), Sum i from 0 to n, (2 : Int) ^ i =
    (2 : Int) ^ (n + 1) - (1 : Int) := by
  by_induc
  · -- Base Case
    rewrite [sum_base]
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : Sum i from 0 to n, (2 : Int) ^ i =
        (2 : Int) ^ (n + 1) - (1 : Int)
    show Sum i from 0 to n + 1, (2 : Int) ^ i =
        (2 : Int) ^ (n + 1 + 1) - (1 : Int) from
      calc Sum i from 0 to n + 1, (2 : Int) ^ i
        _ = (Sum i from 0 to n, (2 : Int) ^ i)
            + (2 : Int) ^ (n + 1) := by rw [sum_from_zero_step]
        _ = (2 : Int) ^ (n + 1) - (1 : Int)
            + (2 : Int) ^ (n + 1) := by rw [ih]
        _ = (2 : Int) ^ (n + 1 + 1) - (1 : Int) := by ring
    done
  done

/- Section 6.2 -/
lemma Lemma_6_2_1_1 {A : Type} {R : BinRel A} {B : Set A} {b c : A}
    (h1 : partial_order R) (h2 : b ∈ B) (h3 : minimalElt R c (B \ {b}))
    (h4 : R b c) : minimalElt R b B := by
  define at h3
    --h3 : c ∈ B \ {b} ∧ ¬∃ x ∈ B \ {b}, R x c ∧ x ≠ c
  define  --Goal : b ∈ B ∧ ¬∃ x ∈ B, R x b ∧ x ≠ b
  apply And.intro h2    --Goal : ¬∃ x ∈ B, R x b ∧ x ≠ b
  contradict h3.right with h5
  obtain (x : A) (h6 : x ∈ B ∧ R x b ∧ x ≠ b) from h5
  apply Exists.intro x  --Goal : x ∈ B \ {b} ∧ R x c ∧ x ≠ c
  apply And.intro
  · -- Proof that x ∈ B \ {b}
    show x ∈ B \ {b} from And.intro h6.left h6.right.right
    done
  · -- Proof that R x c ∧ x ≠ c
    have Rtrans : transitive R := h1.right.left
    have h7 : R x c := Rtrans x b c h6.right.left h4
    apply And.intro h7
    by_contra h8
    rewrite [h8] at h6  --h6 : c ∈ B ∧ R c b ∧ c ≠ b
    have Rantisymm : antisymmetric R := h1.right.right
    have h9 : c = b := Rantisymm c b h6.right.left h4
    show False from h6.right.right h9
    done
  done

lemma Lemma_6_2_1_2 {A : Type} {R : BinRel A} {B : Set A} {b c : A}
    (h1 : partial_order R) (h2 : b ∈ B) (h3 : minimalElt R c (B \ {b}))
    (h4 : ¬R b c) : minimalElt R c B := sorry

theorem Example_6_2_1 {A : Type} (R : BinRel A) (h : partial_order R) :
    ∀ n ≥ 1, ∀ (B : Set A), numElts B n →
      ∃ (x : A), minimalElt R x B := by
  by_induc
  · -- Base Case
    fix B : Set A
    assume h2 : numElts B 1
    rewrite [one_elt_iff_singleton] at h2
    obtain (b : A) (h3 : B = {b}) from h2
    apply Exists.intro b
    define         --Goal : b ∈ B ∧ ¬∃ x ∈ B, R x b ∧ x ≠ b
    apply And.intro
    · -- Proof that b ∈ B
      rewrite [h3]    --Goal : b ∈ {b}
      define          --Goal : b = b
      rfl
      done
    · -- Proof that nothing in B is smaller than b
      by_contra h4
      obtain (x : A) (h5 : x ∈ B ∧ R x b ∧ x ≠ b) from h4
      have h6 : x ∈ B := h5.left
      rewrite [h3] at h6   --h6 : x ∈ {b}
      define at h6         --h6 : x = b
      show False from h5.right.right h6
      done
    done
  · -- Induction Step
    fix n : Nat
    assume h2 : n ≥ 1
    assume ih : ∀ (B : Set A), numElts B n → ∃ (x : A), minimalElt R x B
    fix B : Set A
    assume h3 : numElts B (n + 1)
    have h4 : n + 1 > 0 := by linarith
    obtain (b : A) (h5 : b ∈ B) from nonempty_of_pos_numElts h3 h4
    set B' : Set A := B \ {b}
    have h6 : numElts B' n := remove_one_numElts h3 h5
    obtain (c : A) (h7 : minimalElt R c B') from ih B' h6
    by_cases h8 : R b c
    · -- Case 1. h8 : R b c
      have h9 : minimalElt R b B := Lemma_6_2_1_1 h h5 h7 h8
      show ∃ (x : A), minimalElt R x B from Exists.intro b h9
      done
    · -- Case 2. h8 : ¬R b c
      have h9 : minimalElt R c B := Lemma_6_2_1_2 h h5 h7 h8
      show ∃ (x : A), minimalElt R x B from Exists.intro c h9
      done
    done
  done

lemma extendPO_is_ref {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : reflexive (extendPO R b) := sorry

lemma extendPO_is_trans {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : transitive (extendPO R b) := sorry

lemma extendPO_is_antisymm {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : antisymmetric (extendPO R b) := sorry

lemma extendPO_is_po {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : partial_order (extendPO R b) :=
  And.intro (extendPO_is_ref R b h)
    (And.intro (extendPO_is_trans R b h) (extendPO_is_antisymm R b h))

lemma extendPO_extends {A : Type} (R : BinRel A) (b : A) (x y : A) :
    R x y → extendPO R b x y := by
  assume h1 : R x y
  define
  show R x y ∨ R x b ∧ ¬R y b from Or.inl h1
  done

lemma extendPO_all_comp {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) :
    ∀ (x : A), extendPO R b b x ∨ extendPO R b x b := by
  have Rref : reflexive R := h.left
  fix x : A
  or_left with h1
  define at h1     --h1 : ¬(R x b ∨ R x b ∧ ¬R b b)
  demorgan at h1   --h1 : ¬R x b ∧ ¬(R x b ∧ ¬R b b)
  define           --Goal : R b x ∨ R b b ∧ ¬R x b
  apply Or.inr
  show R b b ∧ ¬R x b from And.intro (Rref b) h1.left
  done

theorem Exercise_6_2_2 {A : Type} (R : BinRel A) (h : partial_order R) :
    ∀ (n : Nat) (B : Set A), numElts B n → ∃ (T : BinRel A),
    partial_order T ∧ (∀ (x y : A), R x y → T x y) ∧
    ∀ x ∈ B, ∀ (y : A), T x y ∨ T y x := by
  by_induc
  · -- Base Case
    fix B : Set A
    assume h2 : numElts B 0
    rewrite [zero_elts_iff_empty] at h2
    define at h2       --h2 : ¬∃ (x : A), x ∈ B
    apply Exists.intro R
    apply And.intro h
    apply And.intro
    · -- Proof that R extends R
      fix x : A; fix y : A
      assume h3 : R x y
      show R x y from h3
      done
    · -- Proof that everything in B comparable to everything under R
      fix x : A
      assume h3 : x ∈ B
      contradict h2
      show ∃ (x : A), x ∈ B from Exists.intro x h3
      done
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ∀ (B : Set A), numElts B n → ∃ (T : BinRel A),
      partial_order T ∧ (∀ (x y : A), R x y → T x y) ∧
      ∀ (x : A), x ∈ B → ∀ (y : A), T x y ∨ T y x
    fix B : Set A
    assume h2 : numElts B (n + 1)
    have h3 : n + 1 > 0 := by linarith
    obtain (b : A) (h4 : b ∈ B) from nonempty_of_pos_numElts h2 h3
    set B' : Set A := B \ {b}
    have h5 : numElts B' n := remove_one_numElts h2 h4
    have h6 : ∃ (T : BinRel A), partial_order T ∧
      (∀ (x y : A), R x y → T x y) ∧
      ∀ (x : A), x ∈ B' → ∀ (y : A), T x y ∨ T y x := ih B' h5
    obtain (T' : BinRel A)
      (h7 : partial_order T' ∧ (∀ (x y : A), R x y → T' x y) ∧
      ∀ (x : A), x ∈ B' → ∀ (y : A), T' x y ∨ T' y x) from h6
    have T'po : partial_order T' := h7.left
    have T'extR : ∀ (x y : A), R x y → T' x y := h7.right.left
    have T'compB' : ∀ (x : A), x ∈ B' →
      ∀ (y : A), T' x y ∨ T' y x := h7.right.right
    set T : BinRel A := extendPO T' b
    apply Exists.intro T
    apply And.intro (extendPO_is_po T' b T'po)
    apply And.intro
    · -- Proof that T extends R
      fix x : A; fix y : A
      assume h8 : R x y
      have h9 : T' x y := T'extR x y h8
      show T x y from (extendPO_extends T' b x y h9)
      done
    · -- Proof that everything in B comparable to everything under T
      fix x : A
      assume h8 : x ∈ B
      by_cases h9 : x = b
      · -- Case 1. h9 : x = b
        rewrite [h9]
        show ∀ (y : A), T b y ∨ T y b from extendPO_all_comp T' b T'po
        done
      · -- Case 2. h9 : x ≠ b
        have h10 : x ∈ B' := And.intro h8 h9
        fix y : A
        have h11 : T' x y ∨ T' y x := T'compB' x h10 y
        by_cases on h11
        · -- Case 2.1. h11 : T' x y
          show T x y ∨ T y x from
            Or.inl (extendPO_extends T' b x y h11)
          done
        · -- Case 2.2. h11 : T' y x
          show T x y ∨ T y x from
            Or.inr (extendPO_extends T' b y x h11)
          done
        done
      done
    done
  done

/- Section 6.3 -/
#eval fact 4       --Answer: 24

theorem Example_6_3_1 : ∀ n ≥ 4, fact n > 2 ^ n := by
  by_induc
  · -- Base Case
    decide
    done
  · -- Induction Step
    fix n : Nat
    assume h1 : n ≥ 4
    assume ih : fact n > 2 ^ n
    have h2 : n + 1 > 2 := by linarith
    show fact (n + 1) > 2 ^ (n + 1) from
      calc fact (n + 1)
        _ = (n + 1) * fact n := by rfl
        _ > (n + 1) * 2 ^ n := by rel [ih]
        _ > 2 * 2 ^ n := by rel [h2]
        _ = 2 ^ (n + 1) := by ring
    done
  done

theorem Example_6_3_2_cheating : ∀ (a : Real) (m n : Nat),
    a ^ (m + n) = a ^ m * a ^ n := by
  fix a : Real; fix m : Nat; fix n : Nat
  ring
  done

theorem Example_6_3_2 : ∀ (a : Real) (m n : Nat),
    a ^ (m + n) = a ^ m * a ^ n := by
  fix a : Real; fix m : Nat
    --Goal : ∀ (n : Nat), a ^ (m + n) = a ^ m * a ^ n
  by_induc
  · -- Base Case
    show a ^ (m + 0) = a ^ m * a ^ 0 from
      calc a ^ (m + 0)
        _ = a ^ m := by rfl
        _ = a ^ m * 1 := (mul_one (a ^ m)).symm
        _ = a ^ m * a ^ 0 := by rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : a ^ (m + n) = a ^ m * a ^ n
    show a ^ (m + (n + 1)) = a ^ m * a ^ (n + 1) from
      calc a ^ (m + (n + 1))
        _ = a ^ ((m + n) + 1) := by rw [add_assoc]
        _ = a ^ (m + n) * a := by rfl
        _ = (a ^ m * a ^ n) * a := by rw [ih]
        _ = a ^ m * (a ^ n * a) := by rw [mul_assoc]
        _ = a ^ m * (a ^ (n + 1)) := by rfl
    done
  done

theorem Example_6_3_4 : ∀ (x : Real), x > -1 →
    ∀ (n : Nat), (1 + x) ^ n ≥ 1 + n * x := by
  fix x : Real
  assume h1 : x > -1
  by_induc
  · -- Base Case
    rewrite [Nat.cast_zero]
    linarith
    done
  · -- Induction Step
    fix n : Nat
    assume ih : (1 + x) ^ n ≥ 1 + n * x
    rewrite [Nat.cast_succ]
    have h2 : 0 ≤ 1 + x := by linarith
    have h3 : x ^ 2 ≥ 0 := sq_nonneg x
    have h4 : n * x ^ 2 ≥ 0 :=
      calc n * x ^ 2
        _ ≥ n * 0 := by rel [h3]
        _ = 0 := by ring
    show (1 + x) ^ (n + 1) ≥ 1 + (n + 1) * x from
      calc (1 + x) ^ (n + 1)
        _ = (1 + x) ^ n * (1 + x) := by rfl
        _ ≥ (1 + n * x) * (1 + x) := by rel [ih]
        _ = 1 + n * x + x + n * x ^ 2 := by ring
        _ ≥ 1 + n * x + x + 0 := by rel [h4]
        _ = 1 + (n + 1) * x := by ring
    done
  done

/- Section 6.4 -/
theorem Example_6_4_1 : ∀ m > 0, ∀ (n : Nat),
    ∃ (q r : Nat), n = m * q + r ∧ r < m := by
  fix m : Nat
  assume h1 : m > 0
  by_strong_induc
  fix n : Nat
  assume ih : ∀ n_1 < n, ∃ (q r : Nat), n_1 = m * q + r ∧ r < m
  by_cases h2 : n < m
  · -- Case 1. h2 : n < m
    apply Exists.intro 0
    apply Exists.intro n     --Goal : n = m * 0 + n ∧ n < m
    apply And.intro _ h2
    ring
    done
  · -- Case 2. h2 : ¬n < m
    have h3 : m ≤ n := by linarith
    obtain (k : Nat) (h4 : n = k + m) from Nat.exists_eq_add_of_le' h3
    have h5 : k < n := by linarith
    have h6 : ∃ (q r : Nat), k = m * q + r ∧ r < m := ih k h5
    obtain (q' : Nat)
      (h7 : ∃ (r : Nat), k = m * q' + r ∧ r < m) from h6
    obtain (r' : Nat) (h8 : k = m * q' + r' ∧ r' < m) from h7
    apply Exists.intro (q' + 1)
    apply Exists.intro r'     --Goal : n = m * (q' + 1) + r' ∧ r' < m
    apply And.intro _ h8.right
    show n = m * (q' + 1) + r' from
      calc n
        _ = k + m := h4
        _ = m * q' + r' + m := by rw [h8.left]
        _ = m * (q' + 1) + r' := by ring
    done
  done

lemma exists_eq_add_one_of_ne_zero {n : Nat}
    (h1 : n ≠ 0) : ∃ (k : Nat), n = k + 1 := by
  have h2 : 1 ≤ n := Nat.pos_of_ne_zero h1
  show ∃ (k : Nat), n = k + 1 from Nat.exists_eq_add_of_le' h2
  done

theorem exists_eq_add_two_of_ne_zero_one {n : Nat}
    (h1 : n ≠ 0) (h2 : n ≠ 1) : ∃ (k : Nat), n = k + 2 := by
  have h3 : 1 ≤ n := Nat.pos_of_ne_zero h1
  have h4 : 2 ≤ n := lt_of_le_of_ne' h3 h2
  show ∃ (k : Nat), n = k + 2 from Nat.exists_eq_add_of_le' h4
  done

example : ∀ (n : Nat), Fib n < 2 ^ n := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ n_1 < n, Fib n_1 < 2 ^ n_1
  by_cases h1 : n = 0
  · -- Case 1. h1 : n = 0
    rewrite [h1]   --Goal : Fib 0 < 2 ^ 0
    decide
    done
  · -- Case 2. h1 : ¬n = 0
    by_cases h2 : n = 1
    · -- Case 2.1. h2 : n = 1
      rewrite [h2]
      decide
      done
    · -- Case 2.2. h2 : ¬n = 1
      obtain (k : Nat) (h3 : n = k + 2) from
        exists_eq_add_two_of_ne_zero_one h1 h2
      have h4 : k < n := by linarith
      have h5 : Fib k < 2 ^ k := ih k h4
      have h6 : k + 1 < n := by linarith
      have h7 : Fib (k + 1) < 2 ^ (k + 1) := ih (k + 1) h6
      rewrite [h3]            --Goal : Fib (k + 2) < 2 ^ (k + 2)
      show Fib (k + 2) < 2 ^ (k + 2) from
        calc Fib (k + 2)
          _ = Fib k + Fib (k + 1) := by rfl
          _ < 2 ^ k + Fib (k + 1) := by rel [h5]
          _ < 2 ^ k + 2 ^ (k + 1) := by rel [h7]
          _ ≤ 2 ^ k + 2 ^ (k + 1) + 2 ^ k := by linarith
          _ = 2 ^ (k + 2) := by ring
      done
    done
  done

theorem well_ord_princ (S : Set Nat) : (∃ (n : Nat), n ∈ S) →
    ∃ n ∈ S, ∀ m ∈ S, n ≤ m := by
  contrapos
  assume h1 : ¬∃ n ∈ S, ∀ m ∈ S, n ≤ m
  quant_neg                   --Goal : ∀ (n : Nat), n ∉ S
  by_strong_induc
  fix n : Nat
  assume ih : ∀ n_1 < n, n_1 ∉ S  --Goal : n ∉ S
  contradict h1 with h2       --h2 : n ∈ S
    --Goal : ∃ n ∈ S, ∀ m ∈ S, n ≤ m
  apply Exists.intro n        --Goal : n ∈ S ∧ ∀ m ∈ S, n ≤ m
  apply And.intro h2          --Goal : ∀ m ∈ S, n ≤ m
  fix m : Nat
  assume h3 : m ∈ S
  have h4 : m < n → m ∉ S := ih m
  contrapos at h4             --h4 : m ∈ S → ¬m < n
  have h5 : ¬m < n := h4 h3
  linarith
  done

lemma sq_even_iff_even (n : Nat) : nat_even (n * n) ↔ nat_even n := sorry

theorem Theorem_6_4_5 :
    ¬∃ (q p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0 := by
  set S : Set Nat :=
    {q : Nat | ∃ (p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0}
  by_contra h1
  have h2 : ∃ (q : Nat), q ∈ S := h1
  have h3 : ∃ q ∈ S, ∀ r ∈ S, q ≤ r := well_ord_princ S h2
  obtain (q : Nat) (h4 : q ∈ S ∧ ∀ r ∈ S, q ≤ r) from h3
  have qinS : q ∈ S := h4.left
  have qleast : ∀ r ∈ S, q ≤ r := h4.right
  define at qinS     --qinS : ∃ (p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0
  obtain (p : Nat) (h5 : p * p = 2 * (q * q) ∧ q ≠ 0) from qinS
  have pqsqrt2 : p * p = 2 * (q * q) := h5.left
  have qne0 : q ≠ 0 := h5.right
  have h6 : nat_even (p * p) := Exists.intro (q * q) pqsqrt2
  rewrite [sq_even_iff_even p] at h6    --h6 : nat_even p
  obtain (p' : Nat) (p'halfp : p = 2 * p') from h6
  have h7 : 2 * (2 * (p' * p')) = 2 * (q * q) := by
    rewrite [←pqsqrt2, p'halfp]
    ring
    done
  have h8 : 2 > 0 := by decide
  rewrite [mul_left_cancel_iff_of_pos h8] at h7
    --h7 : 2 * (p' * p') = q * q
  have h9 : nat_even (q * q) := Exists.intro (p' * p') h7.symm
  rewrite [sq_even_iff_even q] at h9   --h9 : nat_even q
  obtain (q' : Nat) (q'halfq : q = 2 * q') from h9
  have h10 : 2 * (p' * p') = 2 * (2 * (q' * q')) := by
    rewrite [h7, q'halfq]
    ring
    done
  rewrite [mul_left_cancel_iff_of_pos h8] at h10
    --h10 : p' * p' = 2 * (q' * q')
  have q'ne0 : q' ≠ 0 := by
    contradict qne0 with h11
    rewrite [q'halfq, h11]
    rfl
    done
  have q'inS : q' ∈ S := Exists.intro p' (And.intro h10 q'ne0)
  have qleq' : q ≤ q' := qleast q' q'inS
  rewrite [q'halfq] at qleq'        --qleq' : 2 * q' ≤ q'
  contradict q'ne0
  linarith
  done

/- Section 6.5 -/
theorem rep_image_base {A : Type} (f : A → A) (B : Set A) :
    rep_image f 0 B = B := by rfl

theorem rep_image_step {A : Type} (f : A → A) (n : Nat) (B : Set A) :
    rep_image f (n + 1) B = image f (rep_image f n B) := by rfl

lemma rep_image_sub_closed {A : Type} {f : A → A} {B D : Set A}
    (h1 : B ⊆ D) (h2 : closed f D) :
    ∀ (n : Nat), rep_image f n B ⊆ D := by
  by_induc
  · -- Base Case
    rewrite [rep_image_base]          --Goal : B ⊆ D
    show B ⊆ D from h1
    done
  · -- Induction Step
    fix n : Nat
    assume ih : rep_image f n B ⊆ D   --Goal : rep_image f (n + 1) B ⊆ D
    fix x : A
    assume h3 : x ∈ rep_image f (n + 1) B  --Goal : x ∈ D
    rewrite [rep_image_step] at h3
    define at h3    --h3 : ∃ x_1 ∈ rep_image f n B, f x_1 = x
    obtain (b : A) (h4 : b ∈ rep_image f n B ∧ f b = x) from h3
    rewrite [←h4.right]   --Goal : f b ∈ D
    have h5 : b ∈ D := ih h4.left
    define at h2          --h2 : ∀ x ∈ D, f x ∈ D
    show f b ∈ D from h2 b h5
    done
  done

theorem Theorem_6_5_1 {A : Type} (f : A → A) (B : Set A) :
    closure f B (cumul_image f B) := by
  define
  apply And.intro
  · -- Proof that cumul_image f B ∈ {D : Set A | B ⊆ D ∧ closed f D}
    define  --Goal : B ⊆ cumul_image f B ∧ closed f (cumul_image f B)
    apply And.intro
    · -- Proof that B ⊆ cumul_image f B
      fix x : A
      assume h1 : x ∈ B
      define     --Goal : ∃ (n : Nat), x ∈ rep_image f n B
      apply Exists.intro 0
      rewrite [rep_image_base]  --Goal : x ∈ B
      show x ∈ B from h1
      done
    · -- Proof that cumul_image f B closed under f
      define
      fix x : A
      assume h1 : x ∈ cumul_image f B  --Goal : f x ∈ cumul_image f B
      define at h1
      obtain (m : Nat) (h2 : x ∈ rep_image f m B) from h1
      define     --Goal : ∃ (n : Nat), f x ∈ rep_image f n B
      apply Exists.intro (m + 1) --Goal : f x ∈ rep_image f (m + 1) B
      rewrite [rep_image_step]   --Goal : f x ∈ image f (rep_image f m B)
      define     --Goal : ∃ x_1 ∈ rep_image f m B, f x_1 = f x
      apply Exists.intro x  --Goal : x ∈ rep_image f m B ∧ f x = f x
      apply And.intro h2
      rfl
      done
    done
  · -- Proof that cumul_image f B is smallest
    fix D : Set A
    assume h1 : D ∈ {D : Set A | B ⊆ D ∧ closed f D}
    define at h1  --h1 : B ⊆ D ∧ closed f D
    define   --Goal : ∀ ⦃a : A⦄, a ∈ cumul_image f B → a ∈ D
    fix x : A
    assume h2 : x ∈ cumul_image f B  --Goal : x ∈ D
    define at h2  --h2: ∃ (n : Nat), x ∈ rep_image f n B
    obtain (m : Nat) (h3 : x ∈ rep_image f m B) from h2
    have h4 : rep_image f m B ⊆ D :=
      rep_image_sub_closed h1.left h1.right m
    show x ∈ D from h4 h3
    done
  done

-- ──── Chap7 ────
/- Copyright 2023-2025 Daniel J. Velleman -/

set_option linter.style.longFile 0

/- Definitions -/
lemma mod_succ_lt (a n : Nat) : a % (n + 1) < n + 1 := by
  have h : n + 1 > 0 := Nat.succ_pos n
  show a % (n + 1) < n + 1 from Nat.mod_lt a h
  done

def gcd (a b : Nat) : Nat :=
  match b with
    | 0 => a
    | n + 1 =>
      have : a % (n + 1) < n + 1 := mod_succ_lt a n
      gcd (n + 1) (a % (n + 1))
  termination_by b

mutual
  def gcd_c1 (a b : Nat) : Int :=
    match b with
      | 0 => 1
      | n + 1 =>
        have : a % (n + 1) < n + 1 := mod_succ_lt a n
        gcd_c2 (n + 1) (a % (n + 1))
          --Corresponds to s = t'
    termination_by b

  def gcd_c2 (a b : Nat) : Int :=
    match b with
      | 0 => 0
      | n + 1 =>
        have : a % (n + 1) < n + 1 := mod_succ_lt a n
        gcd_c1 (n + 1) (a % (n + 1)) -
          (gcd_c2 (n + 1) (a % (n + 1))) * ↑(a / (n + 1))
          --Corresponds to t = s' - t'q
    termination_by b
end

def prime (n : Nat) : Prop :=
  2 ≤ n ∧ ¬∃ (a b : Nat), a * b = n ∧ a < n ∧ b < n

def prime_factor (p n : Nat) : Prop := prime p ∧ p ∣ n

def all_prime (l : List Nat) : Prop := ∀ p ∈ l, prime p

def nondec (l : List Nat) : Prop :=
  match l with
    | [] => True   --Of course, True is a proposition that is always true
    | n :: L => (∀ m ∈ L, n ≤ m) ∧ nondec L

def nondec_prime_list (l : List Nat) : Prop := all_prime l ∧ nondec l

def prod (l : List Nat) : Nat :=
  match l with
    | [] => 1
    | n :: L => n * (prod L)

def prime_factorization (n : Nat) (l : List Nat) : Prop :=
  nondec_prime_list l ∧ prod l = n

def rel_prime (a b : Nat) : Prop := gcd a b = 1

def congr_mod (m : Nat) (a b : Int) : Prop := (↑m : Int) ∣ (a - b)

def cc (m : Nat) (a : Int) : ZMod m := (↑a : ZMod m)

notation:50 a " ≡ " b " (MOD " m ")" => congr_mod m a b

notation:max "["a"]_"m:max => cc m a

def invertible {m : Nat} (X : ZMod m) : Prop :=
  ∃ (Y : ZMod m), X * Y = [1]_m

def num_rp_below (m k : Nat) : Nat :=
  match k with
    | 0 => 0
    | j + 1 => if gcd m j = 1 then (num_rp_below m j) + 1
                else num_rp_below m j

def phi (m : Nat) : Nat := num_rp_below m m

def prod_seq {m : Nat}
    (j k : Nat) (f : Nat → ZMod m) : ZMod m :=
  match j with
    | 0 => [1]_m
    | n + 1 => prod_seq n k f * f (k + n)

def maps_below (n : Nat) (g : Nat → Nat) : Prop := ∀ i < n, g i < n

def one_one_below (n : Nat) (g : Nat → Nat) : Prop :=
  ∀ i1 < n, ∀ i2 < n, g i1 = g i2 → i1 = i2

def onto_below (n : Nat) (g : Nat → Nat) : Prop :=
  ∀ k < n, ∃ i < n, g i = k

def perm_below (n : Nat) (g : Nat → Nat) : Prop :=
  maps_below n g ∧ one_one_below n g ∧ onto_below n g

def inv_mod (m a : Nat) : Nat := Int.toNat ((gcd_c2 m a) % m)

def swap (u v i : Nat) : Nat :=
  if i = u then v else if i = v then u else i

namespace Euler  --For definitions specific to Euler's theorem

def F (m i : Nat) : ZMod m := if gcd m i = 1 then [i]_m else [1]_m

def G (m a i : Nat) : Nat := (a * i) % m

def Ginv (m a i : Nat) : Nat := G m (inv_mod m a) i

end Euler

/- Section 7.1 -/
theorem dvd_mod_of_dvd_a_b {a b d : Nat}
    (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ (a % b) := by
  set q : Nat := a / b
  have h3 : b * q + a % b = a := Nat.div_add_mod a b
  obtain (j : Nat) (h4 : a = d * j) from h1
  obtain (k : Nat) (h5 : b = d * k) from h2
  define    --Goal : ∃ (c : Nat), a % b = d * c
  apply Exists.intro (j - k * q)
  show a % b = d * (j - k * q) from
    calc a % b
      _ = b * q + a % b - b * q := (Nat.add_sub_cancel_left _ _).symm
      _ = a - b * q := by rw [h3]
      _ = d * j - d * (k * q) := by rw [h4, h5, mul_assoc]
      _ = d * (j - k * q) := (Nat.mul_sub_left_distrib _ _ _).symm
  done

theorem dvd_a_of_dvd_b_mod {a b d : Nat}
    (h1 : d ∣ b) (h2 : d ∣ (a % b)) : d ∣ a := sorry

#eval gcd 672 161    --Answer: 7

lemma gcd_base (a : Nat) : gcd a 0 = a := by
  rewrite [gcd]    --Goal : a = a
  rfl
  done

lemma gcd_nonzero (a : Nat) {b : Nat} (h : b ≠ 0) :
    gcd a b = gcd b (a % b) := by
  obtain (n : Nat) (h2 : b = n + 1) from exists_eq_add_one_of_ne_zero h
  rewrite [h2]   --Goal : gcd a (n + 1) = gcd (n + 1) (a % (n + 1))
  rewrite [gcd]
      --Goal : gcd (n + 1) (a % (n + 1)) = gcd (n + 1) (a % (n + 1))
  rfl
  done

lemma mod_nonzero_lt (a : Nat) {b : Nat} (h : b ≠ 0) : a % b < b := by
  have h1 : b > 0 := Nat.pos_of_ne_zero h
  show a % b < b from Nat.mod_lt a h1
  done

lemma dvd_self (n : Nat) : n ∣ n := by
  apply Exists.intro 1
  ring
  done

theorem gcd_dvd : ∀ (b a : Nat), (gcd a b) ∣ a ∧ (gcd a b) ∣ b := by
  by_strong_induc
  fix b : Nat
  assume ih : ∀ b_1 < b, ∀ (a : Nat), (gcd a b_1) ∣ a ∧ (gcd a b_1) ∣ b_1
  fix a : Nat
  by_cases h1 : b = 0
  · -- Case 1. h1 : b = 0
    rewrite [h1, gcd_base]   --Goal : a ∣ a ∧ a ∣ 0
    apply And.intro (dvd_self a)
    define
    apply Exists.intro 0
    rfl
    done
  · -- Case 2. h1 : b ≠ 0
    rewrite [gcd_nonzero a h1]
      --Goal : gcd b (a % b) ∣ a ∧ gcd b (a % b) ∣ b
    have h2 : a % b < b := mod_nonzero_lt a h1
    have h3 : (gcd b (a % b)) ∣ b ∧ (gcd b (a % b)) ∣ (a % b) :=
      ih (a % b) h2 b
    apply And.intro _ h3.left
    show (gcd b (a % b)) ∣ a from dvd_a_of_dvd_b_mod h3.left h3.right
    done
  done

theorem gcd_dvd_left (a b : Nat) : (gcd a b) ∣ a := (gcd_dvd b a).left

theorem gcd_dvd_right (a b : Nat) : (gcd a b) ∣ b := (gcd_dvd b a).right

lemma gcd_c1_base (a : Nat) : gcd_c1 a 0 = 1 := by
  rewrite [gcd_c1]
  rfl
  done

lemma gcd_c1_nonzero (a : Nat) {b : Nat} (h : b ≠ 0) :
    gcd_c1 a b = gcd_c2 b (a % b) := by
  obtain (n : Nat) (h2 : b = n + 1) from exists_eq_add_one_of_ne_zero h
  rewrite [h2, gcd_c1]
  rfl
  done

lemma gcd_c2_base (a : Nat) : gcd_c2 a 0 = 0 := by
  rewrite [gcd_c2]
  rfl
  done

lemma gcd_c2_nonzero (a : Nat) {b : Nat} (h : b ≠ 0) :
    gcd_c2 a b = gcd_c1 b (a % b) - (gcd_c2 b (a % b)) * ↑(a / b) := by
  obtain (n : Nat) (h2 : b = n + 1) from exists_eq_add_one_of_ne_zero h
  rewrite [h2, gcd_c2]
  rfl
  done

theorem gcd_lin_comb : ∀ (b a : Nat),
    (gcd_c1 a b) * ↑a + (gcd_c2 a b) * ↑b = ↑(gcd a b) := by
  by_strong_induc
  fix b : Nat
  assume ih : ∀ b_1 < b, ∀ (a : Nat),
    (gcd_c1 a b_1) * ↑a + (gcd_c2 a b_1) * ↑b_1 = ↑(gcd a b_1)
  fix a : Nat
  by_cases h1 : b = 0
  · -- Case 1. h1 : b = 0
    rewrite [h1, gcd_c1_base, gcd_c2_base, gcd_base]
      --Goal : 1 * ↑a + 0 * ↑0 = ↑a
    ring
    done
  · -- Case 2. h1 : b ≠ 0
    rewrite [gcd_c1_nonzero a h1, gcd_c2_nonzero a h1, gcd_nonzero a h1]
      --Goal : gcd_c2 b (a % b) * ↑a +
      -- (gcd_c1 b (a % b) - gcd_c2 b (a % b) * ↑(a / b)) * ↑b =
      -- ↑(gcd b (a % b))
    set r : Nat := a % b
    set q : Nat := a / b
    set s : Int := gcd_c1 b r
    set t : Int := gcd_c2 b r
      --Goal : t * ↑a + (s - t * ↑q) * ↑b = ↑(gcd b r)
    have h2 : r < b := mod_nonzero_lt a h1
    have h3 : s * ↑b + t * ↑r = ↑(gcd b r) := ih r h2 b
    have h4 : b * q + r = a := Nat.div_add_mod a b
    rewrite [←h3, ←h4]
    rewrite [Nat.cast_add, Nat.cast_mul]
      --Goal : t * (↑b * ↑q + ↑r) + (s - t * ↑q) * ↑b = s * ↑b + t * ↑r
    ring
    done
  done

#eval gcd_c1 672 161  --Answer: 6
#eval gcd_c2 672 161  --Answer: -25
  --Note 6 * 672 - 25 * 161 = 4032 - 4025 = 7 = gcd 672 161

theorem Theorem_7_1_6 {d a b : Nat} (h1 : d ∣ a) (h2 : d ∣ b) :
    d ∣ gcd a b := by
  rewrite [←Int.natCast_dvd_natCast]    --Goal : ↑d ∣ ↑(gcd a b)
  set s : Int := gcd_c1 a b
  set t : Int := gcd_c2 a b
  have h3 : s * ↑a + t * ↑b = ↑(gcd a b) := gcd_lin_comb b a
  rewrite [←h3]                 --Goal : ↑d ∣ s * ↑a + t * ↑b
  obtain (j : Nat) (h4 : a = d * j) from h1
  obtain (k : Nat) (h5 : b = d * k) from h2
  rewrite [h4, h5, Nat.cast_mul, Nat.cast_mul]
    --Goal : ↑d ∣ s * (↑d * ↑j) + t * (↑d * ↑k)
  define
  apply Exists.intro (s * ↑j + t * ↑k)
  ring
  done

/- Section 7.2 -/
theorem dvd_trans {a b c : Nat} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  define at h1; define at h2; define
  obtain (m : Nat) (h3 : b = a * m) from h1
  obtain (n : Nat) (h4 : c = b * n) from h2
  rewrite [h3, mul_assoc] at h4
  apply Exists.intro (m * n)
  show c = a * (m * n) from h4
  done

lemma exists_prime_factor : ∀ (n : Nat), 2 ≤ n →
    ∃ (p : Nat), prime_factor p n := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ n_1 < n, 2 ≤ n_1 → ∃ (p : Nat), prime_factor p n_1
  assume h1 : 2 ≤ n
  by_cases h2 : prime n
  · -- Case 1. h2 : prime n
    apply Exists.intro n
    define            --Goal : prime n ∧ n ∣ n
    show prime n ∧ n ∣ n from And.intro h2 (dvd_self n)
    done
  · -- Case 2. h2 : ¬prime n
    define at h2
      --h2 : ¬(2 ≤ n ∧ ¬∃ (a b : Nat), a * b = n ∧ a < n ∧ b < n)
    demorgan at h2
    disj_syll h2 h1
    obtain (a : Nat) (h3 : ∃ (b : Nat), a * b = n ∧ a < n ∧ b < n) from h2
    obtain (b : Nat) (h4 : a * b = n ∧ a < n ∧ b < n) from h3
    have h5 : 2 ≤ a := by
      by_contra h6
      have h7 : a ≤ 1 := by linarith
      have h8 : n ≤ b :=
        calc n
          _ = a * b := h4.left.symm
          _ ≤ 1 * b := by rel [h7]
          _ = b := by ring
      linarith        --n ≤ b contradicts b < n
      done
    have h6 : ∃ (p : Nat), prime_factor p a := ih a h4.right.left h5
    obtain (p : Nat) (h7 : prime_factor p a) from h6
    apply Exists.intro p
    define            --Goal : prime p ∧ p ∣ n
    define at h7      --h7 : prime p ∧ p ∣ a
    apply And.intro h7.left
    have h8 : a ∣ n := by
      apply Exists.intro b
      show n = a * b from (h4.left).symm
      done
    show p ∣ n from dvd_trans h7.right h8
    done
  done

lemma exists_least_prime_factor {n : Nat} (h : 2 ≤ n) :
    ∃ (p : Nat), prime_factor p n ∧
    ∀ (q : Nat), prime_factor q n → p ≤ q := by
  set S : Set Nat := {p : Nat | prime_factor p n}
  have h2 : ∃ (p : Nat), p ∈ S := exists_prime_factor n h
  show ∃ (p : Nat), prime_factor p n ∧
    ∀ (q : Nat), prime_factor q n → p ≤ q from well_ord_princ S h2
  done

lemma all_prime_nil : all_prime [] := by
  define     --Goal : ∀ p ∈ [], prime p
  fix p : Nat
  contrapos  --Goal : ¬prime p → p ∉ []
  assume h1 : ¬prime p
  show p ∉ [] from List.not_mem_nil
  done

lemma all_prime_cons (n : Nat) (L : List Nat) :
    all_prime (n :: L) ↔ prime n ∧ all_prime L := by
  apply Iff.intro
  · -- (→)
    assume h1 : all_prime (n :: L)  --Goal : prime n ∧ all_prime L
    define at h1  --h1 : ∀ p ∈ n :: L, prime p
    apply And.intro (h1 n List.mem_cons_self)
    define        --Goal : ∀ p ∈ L, prime p
    fix p : Nat
    assume h2 : p ∈ L
    show prime p from h1 p (List.mem_cons_of_mem n h2)
    done
  · -- (←)
    assume h1 : prime n ∧ all_prime L  --Goal : all_prime (n :: l)
    define : all_prime L at h1
    define
    fix p : Nat
    assume h2 : p ∈ n :: L
    rewrite [List.mem_cons] at h2   --h2 : p = n ∨ p ∈ L
    by_cases on h2
    · -- Case 1. h2 : p = n
      rewrite [h2]
      show prime n from h1.left
      done
    · -- Case 2. h2 : p ∈ L
      show prime p from h1.right p h2
      done
    done
  done

lemma nondec_nil : nondec [] := by
  define  --Goal : True
  trivial --trivial proves some obviously true statements, such as True
  done

lemma nondec_cons (n : Nat) (L : List Nat) :
    nondec (n :: L) ↔ (∀ m ∈ L, n ≤ m) ∧ nondec L := by rfl

lemma prod_nil : prod [] = 1 := by rfl

lemma prod_cons : prod (n :: L) = n * (prod L) := by rfl

lemma exists_cons_of_length_eq_succ {A : Type}
    {l : List A} {n : Nat} (h : l.length = n + 1) :
    ∃ (a : A) (L : List A), l = a :: L ∧ L.length = n := by
  have h1 : ¬l.length = 0 := by linarith
  rewrite [List.length_eq_zero_iff] at h1
  obtain (a : A) (h2 : ∃ (L : List A), l = a :: L) from
    List.exists_cons_of_ne_nil h1
  obtain (L : List A) (h3 : l = a :: L) from h2
  apply Exists.intro a
  apply Exists.intro L
  apply And.intro h3
  have h4 : (a :: L).length = L.length + 1 := List.length_cons
  rewrite [←h3, h] at h4
  show L.length = n from (Nat.add_right_cancel h4).symm
  done

lemma list_elt_dvd_prod_by_length (a : Nat) : ∀ (n : Nat),
    ∀ (l : List Nat), l.length = n → a ∈ l → a ∣ prod l := by
  by_induc
  · --Base Case
    fix l : List Nat
    assume h1 : l.length = 0
    rewrite [List.length_eq_zero_iff] at h1     --h1 : l = []
    rewrite [h1]                            --Goal : a ∈ [] → a ∣ prod []
    contrapos
    assume h2 : ¬a ∣ prod []
    show a ∉ [] from List.not_mem_nil
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ∀ (l : List Nat), l.length = n → a ∈ l → a ∣ prod l
    fix l : List Nat
    assume h1 : l.length = n + 1            --Goal : a ∈ l → a ∣ prod l
    obtain (b : Nat) (h2 : ∃ (L : List Nat),
      l = b :: L ∧ L.length = n) from exists_cons_of_length_eq_succ h1
    obtain (L : List Nat) (h3 : l = b :: L ∧ L.length = n) from h2
    have h4 : a ∈ L → a ∣ prod L := ih L h3.right
    assume h5 : a ∈ l
    rewrite [h3.left, prod_cons]            --Goal : a ∣ b * prod L
    rewrite [h3.left, List.mem_cons] at h5  --h5 : a = b ∨ a ∈ L
    by_cases on h5
    · -- Case 1. h5 : a = b
      apply Exists.intro (prod L)
      rewrite [h5]
      rfl
      done
    · -- Case 2. h5 : a ∈ L
      have h6 : a ∣ prod L := h4 h5
      have h7 : prod L ∣ b * prod L := by
        apply Exists.intro b
        ring
        done
      show a ∣ b * prod L from dvd_trans h6 h7
      done
    done
  done

lemma list_elt_dvd_prod {a : Nat} {l : List Nat}
    (h : a ∈ l) : a ∣ prod l := by
  set n : Nat := l.length
  have h1 : l.length = n := by rfl
  show a ∣ prod l from list_elt_dvd_prod_by_length a n l h1 h
  done

lemma exists_prime_factorization : ∀ (n : Nat), n ≥ 1 →
    ∃ (l : List Nat), prime_factorization n l := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ n_1 < n, n_1 ≥ 1 →
    ∃ (l : List Nat), prime_factorization n_1 l
  assume h1 : n ≥ 1
  by_cases h2 : n = 1
  · -- Case 1. h2 : n = 1
    apply Exists.intro []
    define
    apply And.intro
    · -- Proof of nondec_prime_list []
      define
      show all_prime [] ∧ nondec [] from
        And.intro all_prime_nil nondec_nil
      done
    · -- Proof of prod [] = n
      rewrite [prod_nil, h2]
      rfl
      done
    done
  · -- Case 2. h2 : n ≠ 1
    have h3 : n ≥ 2 := lt_of_le_of_ne' h1 h2
    obtain (p : Nat) (h4 : prime_factor p n ∧ ∀ (q : Nat),
      prime_factor q n → p ≤ q) from exists_least_prime_factor h3
    have p_prime_factor : prime_factor p n := h4.left
    define at p_prime_factor
    have p_prime : prime p := p_prime_factor.left
    have p_dvd_n : p ∣ n := p_prime_factor.right
    have p_least : ∀ (q : Nat), prime_factor q n → p ≤ q := h4.right
    obtain (m : Nat) (n_eq_pm : n = p * m) from p_dvd_n
    have h5 : m ≠ 0 := by
      contradict h1 with h6
      have h7 : n = 0 :=
        calc n
          _ = p * m := n_eq_pm
          _ = p * 0 := by rw [h6]
          _ = 0 := by ring
      rewrite [h7]
      decide
      done
    have m_pos : 0 < m := Nat.pos_of_ne_zero h5
    have m_lt_n : m < n := by
      define at p_prime
      show m < n from
        calc m
          _ < m + m := by linarith
          _ = 2 * m := by ring
          _ ≤ p * m := by rel [p_prime.left]
          _ = n := n_eq_pm.symm
      done
    obtain (L : List Nat) (h6 : prime_factorization m L)
      from ih m m_lt_n m_pos
    define at h6
    have ndpl_L : nondec_prime_list L := h6.left
    define at ndpl_L
    apply Exists.intro (p :: L)
    define
    apply And.intro
    · -- Proof of nondec_prime_list (p :: L)
      define
      apply And.intro
      · -- Proof of all_prime (p :: L)
        rewrite [all_prime_cons]
        show prime p ∧ all_prime L from And.intro p_prime ndpl_L.left
        done
      · -- Proof of nondec (p :: L)
        rewrite [nondec_cons]
        apply And.intro _ ndpl_L.right
        fix q : Nat
        assume q_in_L : q ∈ L
        have h7 : q ∣ prod L := list_elt_dvd_prod q_in_L
        rewrite [h6.right] at h7   --h7 : q ∣ m
        have h8 : m ∣ n := by
          apply Exists.intro p
          rewrite [n_eq_pm]
          ring
          done
        have q_dvd_n : q ∣ n := dvd_trans h7 h8
        have ap_L : all_prime L := ndpl_L.left
        define at ap_L
        have q_prime_factor : prime_factor q n :=
          And.intro (ap_L q q_in_L) q_dvd_n
        show p ≤ q from p_least q q_prime_factor
        done
      done
    · -- Proof of prod (p :: L) = n
      rewrite [prod_cons, h6.right, n_eq_pm]
      rfl
      done
    done
  done

theorem Theorem_7_2_2 {a b c : Nat}
    (h1 : c ∣ a * b) (h2 : rel_prime a c) : c ∣ b := by
  rewrite [←Int.natCast_dvd_natCast]  --Goal : ↑c ∣ ↑b
  define at h1; define at h2; define
  obtain (j : Nat) (h3 : a * b = c * j) from h1
  set s : Int := gcd_c1 a c
  set t : Int := gcd_c2 a c
  have h4 : s * ↑a + t * ↑c = ↑(gcd a c) := gcd_lin_comb c a
  rewrite [h2, Nat.cast_one] at h4  --h4 : s * ↑a + t * ↑c = (1 : Int)
  apply Exists.intro (s * ↑j + t * ↑b)
  show ↑b = ↑c * (s * ↑j + t * ↑b) from
    calc ↑b
      _ = (1 : Int) * ↑b := (one_mul _).symm
      _ = (s * ↑a + t * ↑c) * ↑b := by rw [h4]
      _ = s * (↑a * ↑b) + t * ↑c * ↑b := by ring
      _ = s * (↑c * ↑j) + t * ↑c * ↑b := by
            rw [←Nat.cast_mul a b, h3, Nat.cast_mul c j]
      _ = ↑c * (s * ↑j + t * ↑b) := by ring
  done

lemma le_nonzero_prod_left {a b : Nat} (h : a * b ≠ 0) : a ≤ a * b := by
  have h1 : b ≠ 0 := by
    contradict h with h1
    rewrite [h1]
    ring
    done
  have h2 : 1 ≤ b := Nat.pos_of_ne_zero h1
  show a ≤ a * b from
    calc a
        = a * 1 := (mul_one a).symm
      _ ≤ a * b := by rel [h2]
  done

lemma le_nonzero_prod_right {a b : Nat} (h : a * b ≠ 0) : b ≤ a * b := by
  rewrite [mul_comm]
  rewrite [mul_comm] at h
  show b ≤ b * a from le_nonzero_prod_left h
  done

lemma dvd_prime {a p : Nat}
    (h1 : prime p) (h2 : a ∣ p) : a = 1 ∨ a = p := sorry

lemma rel_prime_of_prime_not_dvd {a p : Nat}
    (h1 : prime p) (h2 : ¬p ∣ a) : rel_prime a p := by
  have h3 : gcd a p ∣ a := gcd_dvd_left a p
  have h4 : gcd a p ∣ p := gcd_dvd_right a p
  have h5 : gcd a p = 1 ∨ gcd a p = p := dvd_prime h1 h4
  have h6 : gcd a p ≠ p := by
    contradict h2 with h6
    rewrite [h6] at h3
    show p ∣ a from h3
    done
  disj_syll h5 h6
  show rel_prime a p from h5
  done

theorem Theorem_7_2_3 {a b p : Nat}
    (h1 : prime p) (h2 : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  or_right with h3
  have h4 : rel_prime a p := rel_prime_of_prime_not_dvd h1 h3
  show p ∣ b from Theorem_7_2_2 h2 h4
  done

lemma ge_one_of_prod_one {a b : Nat} (h : a * b = 1) : a ≥ 1 := by
  have h1 : a ≠ 0 := by
    by_contra h1
    rewrite [h1] at h
    contradict h
    linarith
    done
  show a ≥ 1 from Nat.pos_of_ne_zero h1
  done

lemma eq_one_of_prod_one {a b : Nat} (h : a * b = 1) : a = 1 := by
  have h1 : a ≥ 1 := ge_one_of_prod_one h
  have h2 : a * b ≠ 0 := by linarith
  have h3 : a ≤ a * b := le_nonzero_prod_left h2
  rewrite [h] at h3
  show a = 1 from Nat.le_antisymm h3 h1
  done

lemma eq_one_of_dvd_one {n : Nat} (h : n ∣ 1) : n = 1 := by
  obtain (j : Nat) (h1 : 1 = n * j) from h
  show n = 1 from eq_one_of_prod_one h1.symm
  done

lemma prime_not_one {p : Nat} (h : prime p) : p ≠ 1 := by
  define at h
  linarith
  done

theorem Theorem_7_2_4 {p : Nat} (h1 : prime p) :
    ∀ (l : List Nat), p ∣ prod l → ∃ a ∈ l, p ∣ a := by
  apply List.rec
  · -- Base Case.  Goal : p ∣ prod [] → ∃ a ∈ [], p ∣ a
    rewrite [prod_nil]
    assume h2 : p ∣ 1
    show ∃ a ∈ [], p ∣ a from
      absurd (eq_one_of_dvd_one h2) (prime_not_one h1)
    done
  · -- Induction Step
    fix b : Nat
    fix L : List Nat
    assume ih : p ∣ prod L → ∃ a ∈ L, p ∣ a
      --Goal : p ∣ prod (b :: L) → ∃ a ∈ b :: L, p ∣ a
    assume h2 : p ∣ prod (b :: L)
    rewrite [prod_cons] at h2
    have h3 : p ∣ b ∨ p ∣ prod L := Theorem_7_2_3 h1 h2
    by_cases on h3
    · -- Case 1. h3 : p ∣ b
      apply Exists.intro b
      show b ∈ b :: L ∧ p ∣ b from
        And.intro List.mem_cons_self h3
      done
    · -- Case 2. h3 : p ∣ prod L
      obtain (a : Nat) (h4 : a ∈ L ∧ p ∣ a) from ih h3
      apply Exists.intro a
      show a ∈ b :: L ∧ p ∣ a from
        And.intro (List.mem_cons_of_mem b h4.left) h4.right
      done
    done
  done

lemma prime_in_list {p : Nat} {l : List Nat}
    (h1 : prime p) (h2 : all_prime l) (h3 : p ∣ prod l) : p ∈ l := by
  obtain (a : Nat) (h4 : a ∈ l ∧ p ∣ a) from Theorem_7_2_4 h1 l h3
  define at h2
  have h5 : prime a := h2 a h4.left
  have h6 : p = 1 ∨ p = a := dvd_prime h5 h4.right
  disj_syll h6 (prime_not_one h1)
  rewrite [h6]
  show a ∈ l from h4.left
  done

lemma first_le_first {p q : Nat} {l m : List Nat}
    (h1 : nondec_prime_list (p :: l)) (h2 : nondec_prime_list (q :: m))
    (h3 : prod (p :: l) = prod (q :: m)) : p ≤ q := by
  define at h1; define at h2
  have h4 : q ∣ prod (p :: l) := by
    define
    apply Exists.intro (prod m)
    rewrite [←prod_cons]
    show prod (p :: l) = prod (q :: m) from h3
    done
  have h5 : all_prime (q :: m) := h2.left
  rewrite [all_prime_cons] at h5
  have h6 : q ∈ p :: l := prime_in_list h5.left h1.left h4
  have h7 : nondec (p :: l) := h1.right
  rewrite [nondec_cons] at h7
  rewrite [List.mem_cons] at h6
  by_cases on h6
  · -- Case 1. h6 : q = p
    linarith
    done
  · -- Case 2. h6 : q ∈ l
    have h8 : ∀ m ∈ l, p ≤ m := h7.left
    show p ≤ q from h8 q h6
    done
  done

lemma nondec_prime_list_tail {p : Nat} {l : List Nat}
    (h : nondec_prime_list (p :: l)) : nondec_prime_list l := by
  define at h
  define
  rewrite [all_prime_cons, nondec_cons] at h
  show all_prime l ∧ nondec l from And.intro h.left.right h.right.right
  done

lemma cons_prod_not_one {p : Nat} {l : List Nat}
    (h : nondec_prime_list (p :: l)) : prod (p :: l) ≠ 1 := by
  define at h
  have h1 : all_prime (p :: l) := h.left
  rewrite [all_prime_cons] at h1
  rewrite [prod_cons]
  by_contra h2
  show False from (prime_not_one h1.left) (eq_one_of_prod_one h2)
  done

lemma list_nil_iff_prod_one {l : List Nat} (h : nondec_prime_list l) :
    l = [] ↔ prod l = 1 := by
  apply Iff.intro
  · -- (→)
    assume h1 : l = []
    rewrite [h1]
    show prod [] = 1 from prod_nil
    done
  · -- (←)
    contrapos
    assume h1 : ¬l = []
    obtain (p : Nat) (h2 : ∃ (L : List Nat), l = p :: L) from
      List.exists_cons_of_ne_nil h1
    obtain (L : List Nat) (h3 : l = p :: L) from h2
    rewrite [h3] at h
    rewrite [h3]
    show ¬prod (p :: L) = 1 from cons_prod_not_one h
    done
  done

lemma prime_pos {p : Nat} (h : prime p) : p > 0 := by
  define at h
  linarith
  done

theorem Theorem_7_2_5 : ∀ (l1 l2 : List Nat),
    nondec_prime_list l1 → nondec_prime_list l2 →
    prod l1 = prod l2 → l1 = l2 := by
  apply List.rec
  · -- Base Case.  Goal : ∀ (l2 : List Nat), nondec_prime_list [] →
    -- nondec_prime_list l2 → prod [] = prod l2 → [] = l2
    fix l2 : List Nat
    assume h1 : nondec_prime_list []
    assume h2 : nondec_prime_list l2
    assume h3 : prod [] = prod l2
    rewrite [prod_nil, eq_comm, ←list_nil_iff_prod_one h2] at h3
    show [] = l2 from h3.symm
    done
  · -- Induction Step
    fix p : Nat
    fix L1 : List Nat
    assume ih : ∀ (L2 : List Nat), nondec_prime_list L1 →
      nondec_prime_list L2 → prod L1 = prod L2 → L1 = L2
    -- Goal : ∀ (l2 : List Nat), nondec_prime_list (p :: L1) →
    -- nondec_prime_list l2 → prod (p :: L1) = prod l2 → p :: L1 = l2
    fix l2 : List Nat
    assume h1 : nondec_prime_list (p :: L1)
    assume h2 : nondec_prime_list l2
    assume h3 : prod (p :: L1) = prod l2
    have h4 : ¬prod (p :: L1) = 1 := cons_prod_not_one h1
    rewrite [h3, ←list_nil_iff_prod_one h2] at h4
    obtain (q : Nat) (h5 : ∃ (L : List Nat), l2 = q :: L) from
      List.exists_cons_of_ne_nil h4
    obtain (L2 : List Nat) (h6 : l2 = q :: L2) from h5
    rewrite [h6] at h2    --h2 : nondec_prime_list (q :: L2)
    rewrite [h6] at h3    --h3 : prod (p :: L1) = prod (q :: L2)
    have h7 : p ≤ q := first_le_first h1 h2 h3
    have h8 : q ≤ p := first_le_first h2 h1 h3.symm
    have h9 : p = q := by linarith
    rewrite [h9, prod_cons, prod_cons] at h3
      --h3 : q * prod L1 = q * prod L2
    have h10 : nondec_prime_list L1 := nondec_prime_list_tail h1
    have h11 : nondec_prime_list L2 := nondec_prime_list_tail h2
    define at h2
    have h12 : all_prime (q :: L2) := h2.left
    rewrite [all_prime_cons] at h12
    have h13 : q > 0 := prime_pos h12.left
    have h14 : prod L1 = prod L2 := Nat.eq_of_mul_eq_mul_left h13 h3
    have h15 : L1 = L2 := ih L2 h10 h11 h14
    rewrite [h6, h9, h15]
    rfl
    done
  done

theorem fund_thm_arith (n : Nat) (h : n ≥ 1) :
    ∃! (l : List Nat), prime_factorization n l := by
  exists_unique
  · -- Existence
    show ∃ (l : List Nat), prime_factorization n l from
      exists_prime_factorization n h
    done
  · -- Uniqueness
    fix l1 : List Nat; fix l2 : List Nat
    assume h1 : prime_factorization n l1
    assume h2 : prime_factorization n l2
    define at h1; define at h2
    have h3 : prod l1 = n := h1.right
    rewrite [←h2.right] at h3
    show l1 = l2 from Theorem_7_2_5 l1 l2 h1.left h2.left h3
    done
  done

/- Section 7.3 -/
theorem congr_refl (m : Nat) : ∀ (a : Int), a ≡ a (MOD m) := by
  fix a : Int
  define                --Goal : ∃ (c : Int), a - a = ↑m * c
  apply Exists.intro 0
  ring
  done

theorem congr_symm {m : Nat} : ∀ {a b : Int},
    a ≡ b (MOD m) → b ≡ a (MOD m) := by
  fix a : Int; fix b : Int
  assume h1 : a ≡ b (MOD m)
  define at h1                 --h1 : ∃ (c : Int), a - b = ↑m * c
  define                       --Goal : ∃ (c : Int), b - a = ↑m * c
  obtain (c : Int) (h2 : a - b = m * c) from h1
  apply Exists.intro (-c)
  show b - a = m * (-c) from
    calc b - a
      _ = -(a - b) := by ring
      _ = -(m * c) := by rw [h2]
      _ = m * (-c) := by ring
  done

theorem congr_trans {m : Nat} : ∀ {a b c : Int},
    a ≡ b (MOD m) → b ≡ c (MOD m) → a ≡ c (MOD m) := sorry

/- Fundamental properties of congruence classes -/
lemma cc_eq_iff_val_eq {n : Nat} (X Y : ZMod (n + 1)) :
    X = Y ↔ X.val = Y.val := Fin.ext_iff

lemma val_nat_eq_mod (n k : Nat) :
    ([k]_(n + 1)).val = k % (n + 1) := by rfl

lemma val_zero (n : Nat) : ([0]_(n + 1)).val = 0 := by rfl

theorem cc_rep {m : Nat} (X : ZMod m) : ∃ (a : Int), X = [a]_m :=
  match m with
    | 0 => by
      apply Exists.intro X
      rfl
      done
    | n + 1 => by
      apply Exists.intro ↑(X.val)
      have h1 : X.val < n + 1 := Fin.prop X
      rewrite [cc_eq_iff_val_eq, val_nat_eq_mod, Nat.mod_eq_of_lt h1]
      rfl
      done

theorem add_class (m : Nat) (a b : Int) :
    [a]_m + [b]_m = [a + b]_m := (Int.cast_add a b).symm

theorem mul_class (m : Nat) (a b : Int) :
    [a]_m * [b]_m = [a * b]_m := (Int.cast_mul a b).symm

lemma cc_eq_iff_sub_zero (m : Nat) (a b : Int) :
    [a]_m = [b]_m ↔ [a - b]_m = [0]_m := by
  apply Iff.intro
  · -- (→)
    assume h1 : [a]_m = [b]_m
    have h2 : a - b = a + (-b) := by ring
    have h3 : b + (-b) = 0 := by ring
    show [a - b]_m = [0]_m from
      calc [a - b]_m
        _ = [a + (-b)]_m := by rw [h2]
        _ = [a]_m + [-b]_m := by rw [add_class]
        _ = [b]_m + [-b]_m := by rw [h1]
        _ = [b + -b]_m := by rw [add_class]
        _ = [0]_m := by rw [h3]
    done
  · -- (←)
    assume h1 : [a - b]_m = [0]_m
    have h2 : b + (a - b) = a := by ring
    have h3 : b + 0 = b := by ring
    show [a]_m = [b]_m from
      calc [a]_m
        _ = [b + (a - b)]_m := by rw [h2]
        _ = [b]_m + [a - b]_m := by rw [add_class]
        _ = [b]_m + [0]_m := by rw [h1]
        _ = [b + 0]_m := by rw [add_class]
        _ = [b]_m := by rw [h3]
    done
  done

lemma cc_neg_zero_of_cc_zero (m : Nat) (a : Int) :
    [a]_m = [0]_m → [-a]_m = [0]_m := by
  assume h1 : [a]_m = [0]_m
  have h2 : 0 + (-a) = -a := by ring
  have h3 : a + (-a) = 0 := by ring
  show [-a]_m = [0]_m from
    calc [-a]_m
      _ = [0 + (-a)]_m := by rw [h2]
      _ = [0]_m + [-a]_m := by rw [add_class]
      _ = [a]_m + [-a]_m := by rw [h1]
      _ = [a + (-a)]_m := by rw [add_class]
      _ = [0]_m := by rw [h3]
  done

lemma cc_neg_zero_iff_cc_zero (m : Nat) (a : Int) :
    [-a]_m = [0]_m ↔ [a]_m = [0]_m := by
  apply Iff.intro _ (cc_neg_zero_of_cc_zero m a)
  assume h1 : [-a]_m = [0]_m
  have h2 : [-(-a)]_m = [0]_m := cc_neg_zero_of_cc_zero m (-a) h1
  have h3 : -(-a) = a := by ring
  rewrite [h3] at h2
  show [a]_m = [0]_m from h2
  done

lemma cc_mod_0 (a : Int) : [a]_0 = a := by rfl

lemma cc_nat_zero_iff_dvd (m k : Nat) : [k]_m = [0]_m ↔ m ∣ k :=
  match m with
    | 0 => by
      have h : (0 : Int) = (↑(0 : Nat) : Int) := by rfl
      rewrite [cc_mod_0, cc_mod_0, h, Nat.cast_inj]
      apply Iff.intro
      · -- (→)
        assume h1 : k = 0
        rewrite [h1]
        show 0 ∣ 0 from dvd_self 0
        done
      · -- (←)
        assume h1 : 0 ∣ k
        obtain (c : Nat) (h2 : k = 0 * c) from h1
        rewrite [h2]
        ring
        done
      done
    | n + 1 => by
      rewrite [cc_eq_iff_val_eq, val_nat_eq_mod, val_zero]
      show k % (n + 1) = 0 ↔ n + 1 ∣ k from
        Nat.dvd_iff_mod_eq_zero.symm
      done

lemma cc_zero_iff_dvd (m : Nat) (a : Int) : [a]_m = [0]_m ↔ ↑m ∣ a := by
  obtain (k : Nat) (h1 : a = ↑k ∨ a = -↑k) from Int.eq_nat_or_neg a
  by_cases on h1
  · -- Case 1. h1: a = ↑k
    rewrite [h1, Int.natCast_dvd_natCast]
    show [↑k]_m = [0]_m ↔ m ∣ k from cc_nat_zero_iff_dvd m k
    done
  · -- Case 2. h1: a = -↑k
    rewrite [h1, cc_neg_zero_iff_cc_zero, Int.dvd_neg, Int.natCast_dvd_natCast]
    show [↑k]_m = [0]_m ↔ m ∣ k from cc_nat_zero_iff_dvd m k
    done
  done

theorem cc_eq_iff_congr (m : Nat) (a b : Int) :
    [a]_m = [b]_m ↔ a ≡ b (MOD m) :=
  calc [a]_m = [b]_m
    _ ↔ [a - b]_m = [0]_m := cc_eq_iff_sub_zero m a b
    _ ↔ ↑m ∣ (a - b) := cc_zero_iff_dvd m (a - b)
    _ ↔ a ≡ b (MOD m) := by rfl
/- End of fundamental properties of congruence classes -/

lemma mod_nonneg (m : Nat) [NeZero m] (a : Int) : 0 ≤ a % m := by
  have h1 : (↑m : Int) ≠ 0 := (Nat.cast_ne_zero).rtl (NeZero.ne m)
  show 0 ≤ a % m from Int.emod_nonneg a h1
  done

lemma mod_lt (m : Nat) [NeZero m] (a : Int) : a % m < m := by
  have h1 : m > 0 := Nat.pos_of_ne_zero (NeZero.ne m)
  have h2 : (↑m : Int) > 0 := (Nat.cast_pos).rtl h1
  show a % m < m from Int.emod_lt_of_pos a h2
  done

lemma congr_mod_mod (m : Nat) (a : Int) : a ≡ a % m (MOD m) := by
  define
  have h1 : m * (a / m) + a % m = a := Int.mul_ediv_add_emod a m
  apply Exists.intro (a / m)
  show a - a % m = m * (a / m) from
    calc a - (a % m)
      _ = m * (a / m) + a % m - a % m := by rw [h1]
      _ = m * (a / m) := by ring
  done

lemma mod_cmpl_res (m : Nat) [NeZero m] (a : Int) :
    0 ≤ a % m ∧ a % m < m ∧ a ≡ a % m (MOD m) :=
  And.intro (mod_nonneg m a) (And.intro (mod_lt m a) (congr_mod_mod m a))

theorem Theorem_7_3_1 (m : Nat) [NeZero m] (a : Int) :
    ∃! (r : Int), 0 ≤ r ∧ r < m ∧ a ≡ r (MOD m) := by
  exists_unique
  · -- Existence
    apply Exists.intro (a % m)
    show 0 ≤ a % m ∧ a % m < m ∧ a ≡ a % m (MOD m) from
      mod_cmpl_res m a
    done
  · -- Uniqueness
    fix r1 : Int; fix r2 : Int
    assume h1 : 0 ≤ r1 ∧ r1 < m ∧ a ≡ r1 (MOD m)
    assume h2 : 0 ≤ r2 ∧ r2 < m ∧ a ≡ r2 (MOD m)
    have h3 : r1 ≡ r2 (MOD m) :=
      congr_trans (congr_symm h1.right.right) h2.right.right
    obtain (d : Int) (h4 : r1 - r2 = m * d) from h3
    have h5 : r1 - r2 < m * 1 := by linarith
    have h6 : m * (-1) < r1 - r2 := by linarith
    rewrite [h4] at h5   --h5 : m * d < m * 1
    rewrite [h4] at h6   --h6 : m * -1 < m * d
    have h7 : (↑m : Int) ≥ 0 := Nat.cast_nonneg m
    have h8 : d < 1 := lt_of_mul_lt_mul_of_nonneg_left h5 h7
    have h9 : -1 < d := lt_of_mul_lt_mul_of_nonneg_left h6 h7
    have h10 : d = 0 := by linarith
    show r1 = r2 from
      calc r1
        _ = r1 - r2 + r2 := by ring
        _ = m * 0 + r2 := by rw [h4, h10]
        _ = r2 := by ring
    done
  done

lemma cc_eq_mod (m : Nat) (a : Int) : [a]_m = [a % m]_m :=
  (cc_eq_iff_congr m a (a % m)).rtl (congr_mod_mod m a)

theorem Theorem_7_3_6_1 {m : Nat} (X Y : ZMod m) : X + Y = Y + X := by
  obtain (a : Int) (h1 : X = [a]_m) from cc_rep X
  obtain (b : Int) (h2 : Y = [b]_m) from cc_rep Y
  rewrite [h1, h2]
  have h3 : a + b = b + a := by ring
  show [a]_m + [b]_m = [b]_m + [a]_m from
    calc [a]_m + [b]_m
      _ = [a + b]_m := add_class m a b
      _ = [b + a]_m := by rw [h3]
      _ = [b]_m + [a]_m := (add_class m b a).symm
  done

theorem Theorem_7_3_6_7 {m : Nat} (X : ZMod m) : X * [1]_m = X := by
  obtain (a : Int) (h1 : X = [a]_m) from cc_rep X
  rewrite [h1]
  have h2 : a * 1 = a := by ring
  show [a]_m * [1]_m = [a]_m from
    calc [a]_m * [1]_m
      _ = [a * 1]_m := mul_class m a 1
      _ = [a]_m := by rw [h2]
  done

theorem Exercise_7_2_6 (a b : Nat) :
    rel_prime a b ↔ ∃ (s t : Int), s * a + t * b = 1 := sorry

lemma gcd_c2_inv {m a : Nat} (h1 : rel_prime m a) :
    [a]_m * [gcd_c2 m a]_m = [1]_m := by
  set s : Int := gcd_c1 m a
  have h2 : s * m + (gcd_c2 m a) * a = gcd m a := gcd_lin_comb a m
  define at h1
  rewrite [h1, Nat.cast_one] at h2  --h2 : s * ↑m + gcd_c2 m a * ↑a = 1
  rewrite [mul_class, cc_eq_iff_congr]
  define     --Goal : ∃ (c : Int), ↑a * gcd_c2 m a - 1 = ↑m * c
  apply Exists.intro (-s)
  show a * (gcd_c2 m a) - 1 = m * (-s) from
    calc a * (gcd_c2 m a) - 1
      _ = s * m + (gcd_c2 m a) * a + m * (-s) - 1 := by ring
      _ = 1 + m * (-s) - 1 := by rw [h2]
      _ = m * (-s) := by ring
  done

theorem Theorem_7_3_7 (m a : Nat) :
    invertible [a]_m ↔ rel_prime m a := by
  apply Iff.intro
  · -- (→)
    assume h1 : invertible [a]_m
    define at h1
    obtain (Y : ZMod m) (h2 : [a]_m * Y = [1]_m) from h1
    obtain (b : Int) (h3 : Y = [b]_m) from cc_rep Y
    rewrite [h3, mul_class, cc_eq_iff_congr] at h2
    define at h2
    obtain (c : Int) (h4 : a * b - 1 = m * c) from h2
    rewrite [Exercise_7_2_6]
      --Goal : ∃ (s t : Int), s * ↑m + t * ↑a = 1
    apply Exists.intro (-c)
    apply Exists.intro b
    show (-c) * m + b * a = 1 from
      calc (-c) * m + b * a
        _ = (-c) * m + (a * b - 1) + 1 := by ring
        _ = (-c) * m + m * c + 1 := by rw [h4]
        _ = 1 := by ring
    done
  · -- (←)
    assume h1 : rel_prime m a
    define
    show ∃ (Y : ZMod m), [a]_m * Y = [1]_m from
      Exists.intro [gcd_c2 m a]_m (gcd_c2_inv h1)
    done
  done

/- Section 7.4 -/
section Euler
open Euler

lemma num_rp_below_base {m : Nat} :
    num_rp_below m 0 = 0 := by rfl

lemma num_rp_below_step_rp {m j : Nat} (h : rel_prime m j) :
    num_rp_below m (j + 1) = (num_rp_below m j) + 1 := if_pos h

lemma num_rp_below_step_not_rp {m j : Nat} (h : ¬rel_prime m j) :
    num_rp_below m (j + 1) = num_rp_below m j := if_neg h

lemma phi_def (m : Nat) : phi m = num_rp_below m m := by rfl

#eval phi 10    --Answer: 4

lemma prod_inv_iff_inv {m : Nat} {X : ZMod m}
    (h1 : invertible X) (Y : ZMod m) :
    invertible (X * Y) ↔ invertible Y := by
  apply Iff.intro
  · -- (→)
    assume h2 : invertible (X * Y)
    obtain (Z : ZMod m) (h3 : X * Y * Z = [1]_m) from h2
    apply Exists.intro (X * Z)
    rewrite [←h3]  --Goal : Y * (X * Z) = X * Y * Z
    ring     --Note that ring can do algebra in ZMod m
    done
  · -- (←)
    assume h2 : invertible Y
    obtain (Xi : ZMod m) (h3 : X * Xi = [1]_m) from h1
    obtain (Yi : ZMod m) (h4 : Y * Yi = [1]_m) from h2
    apply Exists.intro (Xi * Yi)
    show (X * Y) * (Xi * Yi) = [1]_m from
      calc X * Y * (Xi * Yi)
        _ = (X * Xi) * (Y * Yi) := by ring
        _ = [1]_m * [1]_m := by rw [h3, h4]
        _ = [1]_m := Theorem_7_3_6_7 [1]_m
    done
  done

lemma F_rp_def {m i : Nat} (h : rel_prime m i) :
    F m i = [i]_m := if_pos h

lemma F_not_rp_def {m i : Nat} (h : ¬rel_prime m i) :
    F m i = [1]_m := if_neg h

lemma prod_seq_base {m : Nat}
    (k : Nat) (f : Nat → ZMod m) : prod_seq 0 k f = [1]_m := by rfl

lemma prod_seq_step {m : Nat}
    (n k : Nat) (f : Nat → ZMod m) :
    prod_seq (n + 1) k f = prod_seq n k f * f (k + n) := by rfl

lemma prod_seq_zero_step {m : Nat}
    (n : Nat) (f : Nat → ZMod m) :
    prod_seq (n + 1) 0 f = prod_seq n 0 f * f n := by
  rewrite [prod_seq_step, zero_add]
  rfl
  done

lemma prod_one {m : Nat}
    (k : Nat) (f : Nat → ZMod m) : prod_seq 1 k f = f k := by
  rewrite [prod_seq_step, prod_seq_base, add_zero, mul_comm, Theorem_7_3_6_7]
  rfl
  done

lemma G_def (m a i : Nat) : G m a i = (a * i) % m := by rfl

lemma cc_G (m a i : Nat) : [G m a i]_m = [a]_m * [i]_m :=
  calc [G m a i]_m
    _ = [(a * i) % m]_m := by rfl
    _ = [a * i]_m := (cc_eq_mod m (a * i)).symm
    _ = [a]_m * [i]_m := (mul_class m a i).symm

lemma G_rp_iff {m a : Nat} (h1 : rel_prime m a) (i : Nat) :
    rel_prime m (G m a i) ↔ rel_prime m i := by
  have h2 : invertible [a]_m := (Theorem_7_3_7 m a).rtl h1
  show rel_prime m (G m a i) ↔ rel_prime m i from
    calc rel_prime m (G m a i)
      _ ↔ invertible [G m a i]_m := (Theorem_7_3_7 m (G m a i)).symm
      _ ↔ invertible ([a]_m * [i]_m) := by rw [cc_G]
      _ ↔ invertible [i]_m := prod_inv_iff_inv h2 ([i]_m)
      _ ↔ rel_prime m i := Theorem_7_3_7 m i
  done

lemma FG_rp {m a i : Nat} (h1 : rel_prime m a) (h2 : rel_prime m i) :
    F m (G m a i) = [a]_m * F m i := by
  have h3 : rel_prime m (G m a i) := (G_rp_iff h1 i).rtl h2
  show F m (G m a i) = [a]_m * F m i from
    calc F m (G m a i)
      _ = [G m a i]_m := F_rp_def h3
      _ = [a]_m * [i]_m := cc_G m a i
      _ = [a]_m * F m i := by rw [F_rp_def h2]
  done

lemma FG_not_rp {m a i : Nat} (h1 : rel_prime m a) (h2 : ¬rel_prime m i) :
    F m (G m a i) = [1]_m := by
  rewrite [←G_rp_iff h1 i] at h2
  show F m (G m a i) = [1]_m from F_not_rp_def h2
  done

lemma FG_prod {m a : Nat} (h1 : rel_prime m a) :
    ∀ (k : Nat), prod_seq k 0 ((F m) ∘ (G m a)) =
      [a]_m ^ (num_rp_below m k) * prod_seq k 0 (F m) := by
  by_induc
  · -- Base Case
    show prod_seq 0 0 ((F m) ∘ (G m a)) =
          [a]_m ^ (num_rp_below m 0) * prod_seq 0 0 (F m) from
      calc prod_seq 0 0 ((F m) ∘ (G m a))
        _ = [1]_m := prod_seq_base _ _
        _ = [a]_m ^ 0 * [1]_m := by ring
        _ = [a]_m ^ (num_rp_below m 0) * prod_seq 0 0 (F m) := by
              rw [num_rp_below_base, prod_seq_base]
    done
  · -- Induction Step
    fix k : Nat
    assume ih : prod_seq k 0 ((F m) ∘ (G m a)) =
      [a]_m ^ (num_rp_below m k) * prod_seq k 0 (F m)
    by_cases h2 : rel_prime m k
    · -- Case 1. h2 : rel_prime m k
      show prod_seq (k + 1) 0 ((F m) ∘ (G m a)) =
          [a]_m ^ (num_rp_below m (k + 1)) *
          prod_seq (k + 1) 0 (F m) from
        calc prod_seq (k + 1) 0 ((F m) ∘ (G m a))
          _ = prod_seq k 0 ((F m) ∘ (G m a)) *
              F m (G m a k) := prod_seq_zero_step _ _
          _ = [a]_m ^ (num_rp_below m k) * prod_seq k 0 (F m) *
              F m (G m a k) := by rw [ih]
          _ = [a]_m ^ (num_rp_below m k) * prod_seq k 0 (F m) *
              ([a]_m * F m k) := by rw [FG_rp h1 h2]
          _ = [a]_m ^ ((num_rp_below m k) + 1) *
              ((prod_seq k 0 (F m)) * F m k) := by ring
          _ = [a]_m ^ (num_rp_below m (k + 1)) *
              prod_seq (k + 1) 0 (F m) := by
                rw [num_rp_below_step_rp h2, prod_seq_zero_step]
      done
    · -- Case 2. h2 : ¬rel_prime m k
      show prod_seq (k + 1) 0 ((F m) ∘ (G m a)) =
          [a]_m ^ (num_rp_below m (k + 1)) *
          prod_seq (k + 1) 0 (F m) from
        calc prod_seq (k + 1) 0 ((F m) ∘ (G m a))
          _ = prod_seq k 0 ((F m) ∘ (G m a)) *
              F m (G m a k) := prod_seq_zero_step _ _
          _ = [a]_m ^ (num_rp_below m k) * prod_seq k 0 (F m) *
              F m (G m a k) := by rw [ih]
          _ = [a]_m ^ (num_rp_below m k) * prod_seq k 0 (F m) *
              ([1]_m) := by rw [FG_not_rp h1 h2]
          _ = [a]_m ^ (num_rp_below m k) *
              (prod_seq k 0 (F m) * ([1]_m)) := by ring
          _ = [a]_m ^ (num_rp_below m (k + 1)) *
              prod_seq (k + 1) 0 (F m) := by
                rw [num_rp_below_step_not_rp h2, prod_seq_zero_step,
                F_not_rp_def h2]
      done
    done
  done

lemma G_maps_below (m a : Nat) [NeZero m] : maps_below m (G m a) := by
  define             --Goal : ∀ i < m, G m a i < m
  fix i : Nat
  assume h1 : i < m
  rewrite [G_def]    --Goal : a * i % m < m
  show a * i % m < m from mod_nonzero_lt (a * i) (NeZero.ne m)
  done

lemma left_inv_one_one_below {n : Nat} {g g' : Nat → Nat}
    (h1 : ∀ i < n, g' (g i) = i) : one_one_below n g := sorry

lemma right_inv_onto_below {n : Nat} {g g' : Nat → Nat}
    (h1 : ∀ i < n, g (g' i) = i) (h2 : maps_below n g') :
    onto_below n g := by
  define at h2; define
  fix k : Nat
  assume h3 : k < n
  apply Exists.intro (g' k)
  show g' k < n ∧ g (g' k) = k from And.intro (h2 k h3) (h1 k h3)
  done

lemma cc_mul_inv_mod_eq_one {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    [a]_m * [inv_mod m a]_m = [1]_m := by
  have h2 : 0 ≤ (gcd_c2 m a) % m := mod_nonneg m (gcd_c2 m a)
  show [a]_m * [inv_mod m a]_m = [1]_m from
    calc [a]_m * [inv_mod m a]_m
      _ = [a]_m * [Int.toNat ((gcd_c2 m a) % m)]_m := by rfl
      _ = [a]_m * [(gcd_c2 m a) % m]_m := by rw [Int.toNat_of_nonneg h2]
      _ = [a]_m * [gcd_c2 m a]_m := by rw [←cc_eq_mod]
      _ = [1]_m := gcd_c2_inv h1
  done

lemma mul_mod_mod_eq_mul_mod (m a b : Nat) : (a * (b % m)) % m = (a * b) % m :=
  calc a * (b % m) % m
      = a % m * (b % m % m) % m := Nat.mul_mod _ _ _
    _ = a % m * (b % m) % m := by rw [Nat.mod_mod]
    _ = a * b % m := (Nat.mul_mod _ _ _).symm

lemma mod_mul_mod_eq_mul_mod (m a b : Nat) : (a % m * b) % m = (a * b) % m := by
  rewrite [mul_comm, mul_mod_mod_eq_mul_mod, mul_comm]
  rfl
  done

theorem congr_iff_mod_eq_Nat (m a b : Nat) [NeZero m] :
    ↑a ≡ ↑b (MOD m) ↔ a % m = b % m := sorry

lemma mul_inv_mod_cancel {m a i : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : i < m) : a * (inv_mod m a) * i % m = i := by
  have h3 : [a]_m * [inv_mod m a]_m = [1]_m := cc_mul_inv_mod_eq_one h1
  rewrite [mul_class, cc_eq_iff_congr, ←Nat.cast_mul, ←Nat.cast_one, congr_iff_mod_eq_Nat] at h3
  show a * inv_mod m a * i % m = i from
    calc a * (inv_mod m a) * i % m
      _ = (a * inv_mod m a) % m * i % m := by rw [mod_mul_mod_eq_mul_mod]
      _ = 1 % m * i % m := by rw [h3]
      _ = 1 * i % m := by rw [mod_mul_mod_eq_mul_mod]
      _ = i % m := by rw [one_mul]
      _ = i := Nat.mod_eq_of_lt h2
  done

lemma Ginv_def {m a i : Nat} : Ginv m a i = G m (inv_mod m a) i := by rfl

lemma Ginv_right_inv {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    ∀ i < m, G m a (Ginv m a i) = i := by
  fix i : Nat
  assume h2 : i < m
  show G m a (Ginv m a i) = i from
    calc G m a (Ginv m a i)
      _ = a * ((inv_mod m a * i) % m) % m := by rfl
      _ = a * (inv_mod m a * i) % m := by rw [mul_mod_mod_eq_mul_mod]
      _ = a * inv_mod m a * i % m := by rw [←mul_assoc]
      _ = i := mul_inv_mod_cancel h1 h2
  done

lemma Ginv_left_inv {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    ∀ i < m, Ginv m a (G m a i) = i := by
  fix i : Nat
  assume h2 : i < m
  show Ginv m a (G m a i) = i from
    calc Ginv m a (G m a i)
      _ = inv_mod m a * ((a * i) % m) % m := by rfl
      _ = inv_mod m a * (a * i) % m := by rw [mul_mod_mod_eq_mul_mod]
      _ = a * inv_mod m a * i % m := by rw [←mul_assoc, mul_comm (inv_mod m a)]
      _ = i := mul_inv_mod_cancel h1 h2
  done

lemma Ginv_maps_below (m a : Nat) [NeZero m] :
    maps_below m (Ginv m a) := G_maps_below m (inv_mod m a)

lemma G_one_one_below {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    one_one_below m (G m a) :=
  left_inv_one_one_below (Ginv_left_inv h1)

lemma G_onto_below {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    onto_below m (G m a) :=
  right_inv_onto_below (Ginv_right_inv h1) (Ginv_maps_below m a)

lemma G_perm_below {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    perm_below m (G m a) := And.intro (G_maps_below m a)
  (And.intro (G_one_one_below h1) (G_onto_below h1))

--Permuting a product of congruence classes doesn't change product
lemma swap_fst (u v : Nat) : swap u v u = v := by
  define : swap u v u
    --Goal : (if u = u then v else if u = v then u else u) = v
  have h : u = u := by rfl
  rewrite [if_pos h]
  rfl
  done

lemma swap_snd (u v : Nat) : swap u v v = u := by
  define : swap u v v
  by_cases h1 : v = u
  · -- Case 1. h1 : v = u
    rewrite [if_pos h1]
    show v = u from h1
    done
  · -- Case 2. h1 : v ≠ u
    rewrite [if_neg h1]
    have h2 : v = v := by rfl
    rewrite [if_pos h2]
    rfl
    done
  done

lemma swap_other {u v i : Nat} (h1 : i ≠ u) (h2 : i ≠ v) : swap u v i = i := by
  define : swap u v i
  rewrite [if_neg h1, if_neg h2]
  rfl
  done

lemma swap_values (u v i : Nat) : swap u v i = v ∨ swap u v i = u ∨ swap u v i = i := by
  by_cases h1 : i = u
  · -- Case 1. h1 : i = u
    apply Or.inl
    rewrite [h1]
    show swap u v u = v from swap_fst u v
    done
  · -- Case 2. h1 : i ≠ u
    apply Or.inr
    by_cases h2 : i = v
    · -- Case 2.1. h2 : i = v
      apply Or.inl
      rewrite [h2]
      show swap u v v = u from swap_snd u v
      done
    · -- Case 2.2. h2 : i ≠ v
      apply Or.inr
      show swap u v i = i from swap_other h1 h2
      done
    done
  done

lemma swap_maps_below {u v n : Nat} (h1 : u < n) (h2 : v < n) : maps_below n (swap u v) := by
  define
  fix i : Nat
  assume h3 : i < n
  have h4 : swap u v i = v ∨ swap u v i = u ∨ swap u v i = i := swap_values u v i
  by_cases on h4
  · -- Case 1. h4 : swap u v i = v
    rewrite [h4]
    show v < n from h2
    done
  · -- Case 2.
    by_cases on h4
    · -- Case 2.1. h4 : swap u v i = u
      rewrite [h4]
      show u < n from h1
      done
    · -- Case 2.2. h4 : swap u v i = i
      rewrite [h4]
      show i < n from h3
      done
    done
  done

lemma swap_swap (u v n : Nat) : ∀ i < n, swap u v (swap u v i) = i := by
  fix i : Nat
  assume h : i < n
  by_cases h1 : i = u
  · -- Case 1. h1 : i = u
    rewrite [h1, swap_fst, swap_snd]
    rfl
    done
  · -- Case 2. h1 : i ≠ u
    by_cases h2 : i = v
    · -- Case 2.1. h2 : i = v
      rewrite [h2, swap_snd, swap_fst]
      rfl
      done
    · -- Case 2.2. h2 : i ≠ v
      rewrite [swap_other h1 h2, swap_other h1 h2]
      rfl
      done
    done
  done

lemma swap_one_one_below (u v n) : one_one_below n (swap u v) :=
  left_inv_one_one_below (swap_swap u v n)

lemma swap_onto_below {u v n} (h1 : u < n) (h2 : v < n) : onto_below n (swap u v) :=
  right_inv_onto_below (swap_swap u v n) (swap_maps_below h1 h2)

lemma swap_perm_below {u v n} (h1 : u < n) (h2 : v < n) : perm_below n (swap u v) :=
  And.intro (swap_maps_below h1 h2) (And.intro (swap_one_one_below u v n) (swap_onto_below h1 h2))

lemma comp_perm_below {n : Nat} {f g : Nat → Nat}
    (h1 : perm_below n f) (h2 : perm_below n g) :
    perm_below n (f ∘ g) := sorry

lemma trivial_swap (u : Nat) : swap u u = id := by
  apply funext
  fix x : Nat
  by_cases h1 : x = u
  · -- Case 1. h1 : x = u
    rewrite [h1, swap_fst]
    rfl
    done
  · -- Case 2. h1 : x ≠ u
    rewrite [swap_other h1 h1]
    rfl
    done
  done

lemma prod_eq_fun {m : Nat} (f g : Nat → ZMod m) (k : Nat) :
    ∀ (n : Nat), (∀ i < n, f (k + i) = g (k + i)) →
      prod_seq n k f = prod_seq n k g := by
  by_induc
  · -- Base Case
    assume h : (∀ i < 0, f (k + i) = g (k + i))
    rewrite [prod_seq_base, prod_seq_base]
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : (∀ i < n, f (k + i) = g (k + i)) → prod_seq n k f = prod_seq n k g
    assume h1 : ∀ i < n + 1, f (k + i) = g (k + i)
    have h2 : ∀ i < n, f (k + i) = g (k + i) := by
      fix i : Nat
      assume h2 : i < n
      have h3 : i < n + 1 := by linarith
      show f (k + i) = g (k + i) from h1 i h3
      done
    have h3 : prod_seq n k f = prod_seq n k g := ih h2
    have h4 : n < n + 1 := Nat.lt_succ_self n
    rewrite [prod_seq_step, prod_seq_step, h3, h1 n h4]
    rfl
    done
  done

lemma swap_prod_eq_prod_below {m u n : Nat} (f : Nat → ZMod m)
    (h1 : u ≤ n) : prod_seq u 0 (f ∘ swap u n) = prod_seq u 0 f := by
  have h2 : ∀ (i : Nat), i < u → (f ∘ swap u n) (0 + i) = f (0 + i) := by
    fix i : Nat
    assume h2 : i < u
    have h3 : 0 + i ≠ u := by linarith
    have h4 : 0 + i ≠ n := by linarith
    rewrite [comp_def, swap_other h3 h4]
    rfl
    done
  show prod_seq u 0 (f ∘ swap u n) = prod_seq u 0 f from
    prod_eq_fun (f ∘ swap u n) f 0 u h2
  done

lemma swap_prod_eq_prod_between {m u j n : Nat} (f : Nat → ZMod m)
    (h1 : n = u + 1 + j) : prod_seq j (u + 1) (f ∘ swap u n) =
      prod_seq j (u + 1) f := by
  have h2 : ∀ i < j, (f ∘ swap u n) (u + 1 + i) = f (u + 1 + i) := by
    fix i : Nat
    assume h2 : i < j
    have h3 : u + 1 + i ≠ u := by linarith
    have h4 : u + 1 + i ≠ n := by linarith
    rewrite [comp_def, swap_other h3 h4]
    rfl
  show prod_seq j (u + 1) (f ∘ swap u n) = prod_seq j (u + 1) f from
    prod_eq_fun (f ∘ swap u n) f (u + 1) j h2
  done

lemma break_prod {m : Nat} (n : Nat) (f : Nat → ZMod m) :
    ∀ (j : Nat), prod_seq (n + j) 0 f = prod_seq n 0 f * prod_seq j n f := by
  by_induc
  · -- Base Case
    have h : n + 0 = n := by rfl
    rewrite [prod_seq_base, h, Theorem_7_3_6_7]
    rfl
    done
  · -- Induction Step
    fix j : Nat
    assume ih : prod_seq (n + j) 0 f = prod_seq n 0 f * prod_seq j n f
    rewrite [←add_assoc, prod_seq_zero_step, prod_seq_step, ih, mul_assoc]
    rfl
    done
  done

lemma break_prod_twice  {m u j n : Nat} (f : Nat → ZMod m)
    (h1 : n = u + 1 + j) : prod_seq (n + 1) 0 f =
      prod_seq u 0 f * f u * prod_seq j (u + 1) f * f n := by
  have h2 : prod_seq (n + 1) 0 f = prod_seq n 0 f * prod_seq 1 n f :=
    break_prod n f 1
  rewrite [prod_one] at h2
  have h3 : prod_seq (u + 1 + j) 0 f = prod_seq (u + 1) 0 f * prod_seq j (u + 1) f :=
    break_prod (u + 1) f j
  rewrite [←h1] at h3
  have h4 : prod_seq (u + 1) 0 f = prod_seq u 0 f * prod_seq 1 u f :=
    break_prod u f 1
  rewrite [prod_one] at h4
  rewrite [h3, h4] at h2
  show prod_seq (n + 1) 0 f = prod_seq u 0 f * f u * prod_seq j (u + 1) f * f n from h2
  done

lemma swap_prod_eq_prod {m u n : Nat} (f : Nat → ZMod m) (h1 : u ≤ n) :
    prod_seq (n + 1) 0 (f ∘ swap u n) = prod_seq (n + 1) 0 f := by
  by_cases h2 : u = n
  · -- Case 1. h2 : u = n
    rewrite [h2, trivial_swap n]
      --Goal : prod_seq (n + 1) 0 (f ∘ id) = prod_seq (n + 1) 0 f
    rfl
    done
  · -- Case 2. h2 : ¬u = n
    have h3 : u + 1 ≤ n := Nat.lt_of_le_of_ne h1 h2
    obtain (j : Nat) (h4 : n = u + 1 + j) from Nat.exists_eq_add_of_le h3
    have break_f : prod_seq (n + 1) 0 f =
      prod_seq u 0 f * f u * prod_seq j (u + 1) f * f n :=
      break_prod_twice f h4
    have break_fs : prod_seq (n + 1) 0 (f ∘ swap u n) =
      prod_seq u 0 (f ∘ swap u n) * (f ∘ swap u n) u *
      prod_seq j (u + 1) (f ∘ swap u n) * (f ∘ swap u n) n :=
      break_prod_twice (f ∘ swap u n) h4
    have f_eq_fs_below : prod_seq u 0 (f ∘ swap u n) =
      prod_seq u 0 f := swap_prod_eq_prod_below f h1
    have f_eq_fs_btwn : prod_seq j (u + 1) (f ∘ swap u n) =
      prod_seq j (u + 1) f := swap_prod_eq_prod_between f h4
    show prod_seq (n + 1) 0 (f ∘ swap u n) = prod_seq (n + 1) 0 f from
      calc prod_seq (n + 1) 0 (f ∘ swap u n)
        _ = prod_seq u 0 (f ∘ swap u n) * (f ∘ swap u n) u *
            prod_seq j (u + 1) (f ∘ swap u n) * (f ∘ swap u n) n :=
              break_fs
        _ = prod_seq u 0 f * (f ∘ swap u n) u *
            prod_seq j (u + 1) f * (f ∘ swap u n) n := by
              rw [f_eq_fs_below, f_eq_fs_btwn]
        _ = prod_seq u 0 f * f (swap u n u) *
            prod_seq j (u + 1) f * f (swap u n n) := by rfl
        _ = prod_seq u 0 f * f n * prod_seq j (u + 1) f * f u := by
              rw [swap_fst, swap_snd]
        _ = prod_seq u 0 f * f u * prod_seq j (u + 1) f * f n := by ring
        _ = prod_seq (n + 1) 0 f := break_f.symm
    done
  done

lemma perm_below_fixed {n : Nat} {g : Nat → Nat}
    (h1 : perm_below (n + 1) g) (h2 : g n = n) : perm_below n g := sorry

lemma perm_prod {m : Nat} (f : Nat → ZMod m) :
    ∀ (n : Nat), ∀ (g : Nat → Nat), perm_below n g →
      prod_seq n 0 f = prod_seq n 0 (f ∘ g) := by
  by_induc
  · -- Base Case
    fix g : Nat → Nat
    assume h1 : perm_below 0 g
    rewrite [prod_seq_base, prod_seq_base]
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ∀ (g : Nat → Nat), perm_below n g →
      prod_seq n 0 f = prod_seq n 0 (f ∘ g)
    fix g : Nat → Nat
    assume g_pb : perm_below (n + 1) g
    define at g_pb
    have g_ob : onto_below (n + 1) g := g_pb.right.right
    define at g_ob
    have h1 : n < n + 1 := by linarith
    obtain (u : Nat) (h2 : u < n + 1 ∧ g u = n) from g_ob n h1
    have s_pb : perm_below (n + 1) (swap u n) :=
      swap_perm_below h2.left h1
    have gs_pb_n1 : perm_below (n + 1) (g ∘ swap u n) :=
      comp_perm_below g_pb s_pb
    have gs_fix_n : (g ∘ swap u n) n = n :=
      calc (g ∘ swap u n) n
        _ = g (swap u n n) := by rfl
        _ = g u := by rw [swap_snd]
        _ = n := h2.right
    have gs_pb_n : perm_below n (g ∘ swap u n) :=
      perm_below_fixed gs_pb_n1 gs_fix_n
    have gs_prod : prod_seq n 0 f = prod_seq n 0 (f ∘ (g ∘ swap u n)) :=
      ih (g ∘ swap u n) gs_pb_n
    have h3 : u ≤ n := by linarith
    show prod_seq (n + 1) 0 f = prod_seq (n + 1) 0 (f ∘ g) from
      calc prod_seq (n + 1) 0 f
        _ = prod_seq n 0 f * f n := prod_seq_zero_step n f
        _ = prod_seq n 0 (f ∘ (g ∘ swap u n)) *
            f ((g ∘ swap u n) n) := by rw [gs_prod, gs_fix_n]
        _ = prod_seq n 0 (f ∘ g ∘ swap u n) *
            (f ∘ g ∘ swap u n) n := by rfl
        _ = prod_seq (n + 1) 0 (f ∘ g ∘ swap u n) :=
              (prod_seq_zero_step n (f ∘ g ∘ swap u n)).symm
        _ = prod_seq (n + 1) 0 ((f ∘ g) ∘ swap u n) := by rfl
        _ = prod_seq (n + 1) 0 (f ∘ g) := swap_prod_eq_prod (f ∘ g) h3
    done
  done

lemma F_invertible (m i : Nat) : invertible (F m i) := by
  by_cases h : rel_prime m i
  · -- Case 1. h : rel_prime m i
    rewrite [F_rp_def h]
    show invertible [i]_m from (Theorem_7_3_7 m i).rtl h
    done
  · -- Case 2. h : ¬rel_prime m i
    rewrite [F_not_rp_def h]
    apply Exists.intro [1]_m
    show [1]_m * [1]_m = [1]_m from Theorem_7_3_6_7 [1]_m
    done
  done

lemma Fprod_invertible (m : Nat) :
    ∀ (k : Nat), invertible (prod_seq k 0 (F m)) := by
  by_induc
  · -- Base Case
    apply Exists.intro [1]_m
    show prod_seq 0 0 (F m) * [1]_m = [1]_m from
      calc prod_seq 0 0 (F m) * [1]_m
        _ = [1]_m * [1]_m := by rw [prod_seq_base]
        _ = [1]_m := Theorem_7_3_6_7 ([1]_m)
    done
  · -- Induction Step
    fix k : Nat
    assume ih : invertible (prod_seq k 0 (F m))
    rewrite [prod_seq_zero_step]
    show invertible (prod_seq k 0 (F m) * (F m k)) from
      (prod_inv_iff_inv ih (F m k)).rtl (F_invertible m k)
    done
  done

theorem Theorem_7_4_2 {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    [a]_m ^ (phi m) = [1]_m := by
  have h2 : invertible (prod_seq m 0 (F m)) := Fprod_invertible m m
  obtain (Y : ZMod m) (h3 : prod_seq m 0 (F m) * Y = [1]_m) from h2
  show [a]_m ^ (phi m) = [1]_m from
    calc [a]_m ^ (phi m)
      _ = [a]_m ^ (phi m) * [1]_m := (Theorem_7_3_6_7 _).symm
      _ = [a]_m ^ (phi m) * (prod_seq m 0 (F m) * Y) := by rw [h3]
      _ = ([a]_m ^ (phi m) * prod_seq m 0 (F m)) * Y := by ring
      _ = prod_seq m 0 (F m ∘ G m a) * Y := by rw [FG_prod h1 m, phi_def]
      _ = prod_seq m 0 (F m) * Y := by
            rw [perm_prod (F m) m (G m a) (G_perm_below h1)]
      _ = [1]_m := by rw [h3]
  done

lemma Exercise_7_4_5_Int (m : Nat) (a : Int) :
    ∀ (n : Nat), [a]_m ^ n = [a ^ n]_m := sorry

lemma Exercise_7_4_5_Nat (m a n : Nat) :
    [a]_m ^ n = [a ^ n]_m := by
  rewrite [Exercise_7_4_5_Int]
  rfl
  done

theorem Euler's_theorem {m a : Nat} [NeZero m]
    (h1 : rel_prime m a) : a ^ (phi m) ≡ 1 (MOD m) := by
  have h2 : [a]_m ^ (phi m) = [1]_m := Theorem_7_4_2 h1
  rewrite [Exercise_7_4_5_Nat m a (phi m)] at h2
    --h2 : [a ^ phi m]_m = [1]_m
  show a ^ (phi m) ≡ 1 (MOD m) from (cc_eq_iff_congr _ _ _).ltr h2
  done

#eval gcd 10 7     --Answer: 1.  So 10 and 7 are relatively prime

#eval 7 ^ phi 10   --Answer: 2401, which is congruent to 1 mod 10.

end Euler

/- Section 7.5 -/
lemma num_rp_prime {p : Nat} (h1 : prime p) :
    ∀ k < p, num_rp_below p (k + 1) = k := sorry

lemma phi_prime {p : Nat} (h1 : prime p) : phi p = p - 1 := by
  have h2 : 1 ≤ p := prime_pos h1
  have h3 : p - 1 + 1 = p := Nat.sub_add_cancel h2
  have h4 : p - 1 < p := by linarith
  have h5 : num_rp_below p (p - 1 + 1) = p - 1 :=
    num_rp_prime h1 (p - 1) h4
  rewrite [h3] at h5
  show phi p = p - 1 from h5
  done

theorem Theorem_7_2_2_Int {a c : Nat} {b : Int}
    (h1 : ↑c ∣ ↑a * b) (h2 : rel_prime a c) : ↑c ∣ b := by
  rewrite [Int.natCast_dvd, Int.natAbs_mul,
    Int.natAbs_natCast] at h1      --h1 : c ∣ a * Int.natAbs b
  rewrite [Int.natCast_dvd]        --Goal : c ∣ Int.natAbs b
  show c ∣ Int.natAbs b from Theorem_7_2_2 h1 h2
  done

lemma Lemma_7_4_5 {m n : Nat} (a b : Int) (h1 : rel_prime m n) :
    a ≡ b (MOD m * n) ↔ a ≡ b (MOD m) ∧ a ≡ b (MOD n) := by
  apply Iff.intro
  · -- (→)
    assume h2 : a ≡ b (MOD m * n)
    obtain (j : Int) (h3 : a - b = (m * n) * j) from h2
    apply And.intro
    · -- Proof of a ≡ b (MOD m)
      apply Exists.intro (n * j)
      show a - b = m * (n * j) from
        calc a - b
          _ = m * n * j := h3
          _ = m * (n * j) := by ring
      done
    · -- Proof of a ≡ b (MOD n)
      apply Exists.intro (m * j)
      show a - b = n * (m * j) from
        calc a - b
          _ = m * n * j := h3
          _ = n * (m * j) := by ring
      done
    done
  · -- (←)
    assume h2 : a ≡ b (MOD m) ∧ a ≡ b (MOD n)
    obtain (j : Int) (h3 : a - b = m * j) from h2.left
    have h4 : (↑n : Int) ∣ a - b := h2.right
    rewrite [h3] at h4      --h4 : ↑n ∣ ↑m * j
    have h5 : ↑n ∣ j := Theorem_7_2_2_Int h4 h1
    obtain (k : Int) (h6 : j = n * k) from h5
    apply Exists.intro k    --Goal : a - b = ↑(m * n) * k
    rewrite [Nat.cast_mul]  --Goal : a - b = ↑m * ↑n * k
    show a - b = (m * n) * k from
      calc a - b
        _ = m * j := h3
        _ = m * (n * k) := by rw [h6]
        _ = (m * n) * k := by ring
    done
  done

--From exercises of Section 7.2
theorem rel_prime_symm {a b : Nat} (h : rel_prime a b) :
    rel_prime b a := sorry

lemma prime_NeZero {p : Nat} (h : prime p) : NeZero p := by
  rewrite [neZero_iff]     --Goal : p ≠ 0
  define at h
  linarith
  done

lemma Lemma_7_5_1 {p e d m c s : Nat} {t : Int}
    (h1 : prime p) (h2 : e * d = (p - 1) * s + 1)
    (h3 : m ^ e - c = p * t) :
    c ^ d ≡ m (MOD p) := by
  have h4 : m ^ e ≡ c (MOD p) := Exists.intro t h3
  have h5 : [m ^ e]_p = [c]_p := (cc_eq_iff_congr _ _ _).rtl h4
  rewrite [←Exercise_7_4_5_Nat] at h5  --h5 : [m]_p ^ e = [c]_p
  by_cases h6 : p ∣ m
  · -- Case 1. h6 : p ∣ m
    have h7 : m ≡ 0 (MOD p) := by
      obtain (j : Nat) (h8 : m = p * j) from h6
      apply Exists.intro (↑j : Int)   --Goal : ↑m - 0 = ↑p * ↑j
      rewrite [h8, Nat.cast_mul]
      ring
      done
    have h8 : [m]_p = [0]_p := (cc_eq_iff_congr _ _ _).rtl h7
    have h9 : e * d ≠ 0 := by
      rewrite [h2]
      show (p - 1) * s + 1 ≠ 0 from Nat.add_one_ne_zero _
      done
    have h10 : (0 : Int) ^ (e * d) = 0 := zero_pow h9
    have h11 : [c ^ d]_p = [m]_p :=
      calc [c ^ d]_p
        _ = [c]_p ^ d := by rw [Exercise_7_4_5_Nat]
        _ = ([m]_p ^ e) ^ d := by rw [h5]
        _ = [m]_p ^ (e * d) := by ring
        _ = [0]_p ^ (e * d) := by rw [h8]
        _ = [0 ^ (e * d)]_p := Exercise_7_4_5_Int _ _ _
        _ = [0]_p := by rw [h10]
        _ = [m]_p := by rw [h8]
    show c ^ d ≡ m (MOD p) from (cc_eq_iff_congr _ _ _).ltr h11
    done
  · -- Case 2. h6 : ¬p ∣ m
    have h7 : rel_prime m p := rel_prime_of_prime_not_dvd h1 h6
    have h8 : rel_prime p m := rel_prime_symm h7
    have h9 : NeZero p := prime_NeZero h1
    have h10 : (1 : Int) ^ s = 1 := by ring
    have h11 : [c ^ d]_p = [m]_p :=
      calc [c ^ d]_p
        _ = [c]_p ^ d := by rw [Exercise_7_4_5_Nat]
        _ = ([m]_p ^ e) ^ d := by rw [h5]
        _ = [m]_p ^ (e * d) := by ring
        _ = [m]_p ^ ((p - 1) * s + 1) := by rw [h2]
        _ = ([m]_p ^ (p - 1)) ^ s * [m]_p := by ring
        _ = ([m]_p ^ (phi p)) ^ s * [m]_p := by rw [phi_prime h1]
        _ = [1]_p ^ s * [m]_p := by rw [Theorem_7_4_2 h8]
        _ = [1 ^ s]_p * [m]_p := by rw [Exercise_7_4_5_Int]
        _ = [1]_p * [m]_p := by rw [h10]
        _ = [m]_p * [1]_p := by ring
        _ = [m]_p := Theorem_7_3_6_7 _
    show c ^ d ≡ m (MOD p) from (cc_eq_iff_congr _ _ _).ltr h11
    done
  done

theorem Theorem_7_5_1 (p q n e d k m c : Nat)
    (p_prime : prime p) (q_prime : prime q) (p_ne_q : p ≠ q)
    (n_pq : n = p * q) (ed_congr_1 : e * d = k * (p - 1) * (q - 1) + 1)
    (h1 : [m]_n ^ e = [c]_n) : [c]_n ^ d = [m]_n := by
  rewrite [Exercise_7_4_5_Nat, cc_eq_iff_congr] at h1
    --h1 : m ^ e ≡ c (MOD n)
  rewrite [Exercise_7_4_5_Nat, cc_eq_iff_congr]
    --Goal : c ^ d ≡ m (MOD n)
  obtain (j : Int) (h2 : m ^ e - c = n * j) from h1
  rewrite [n_pq, Nat.cast_mul] at h2
    --h2 : m ^ e - c = p * q * j
  have h3 : e * d = (p - 1) * (k * (q - 1)) + 1 := by
    rewrite [ed_congr_1]
    ring
    done
  have h4 : m ^ e - c = p * (q * j) := by
    rewrite [h2]
    ring
    done
  have congr_p : c ^ d ≡ m (MOD p) := Lemma_7_5_1 p_prime h3 h4
  have h5 : e * d = (q - 1) * (k * (p - 1)) + 1 := by
    rewrite [ed_congr_1]
    ring
    done
  have h6 : m ^ e - c = q * (p * j) := by
    rewrite [h2]
    ring
    done
  have congr_q : c ^ d ≡ m (MOD q) := Lemma_7_5_1 q_prime h5 h6
  have h7 : ¬q ∣ p := by
    by_contra h8
    have h9 : q = 1 ∨ q = p := dvd_prime p_prime h8
    disj_syll h9 (prime_not_one q_prime)
    show False from p_ne_q h9.symm
    done
  have h8 : rel_prime p q := rel_prime_of_prime_not_dvd q_prime h7
  rewrite [n_pq, Lemma_7_4_5 _ _ h8]
  show c ^ d ≡ m (MOD p) ∧ c ^ d ≡ m (MOD q) from
    And.intro congr_p congr_q
  done

-- ──── Chap8Part2 ────
/- Copyright 2023-2025 Daniel J. Velleman -/


open Classical

/- Definitions -/
def fnz (n : Nat) : Int := if 2 ∣ n then ↑(n / 2) else -↑((n + 1) / 2)

def fzn (a : Int) : Nat :=
  if a ≥ 0 then 2 * Int.toNat a else 2 * Int.toNat (-a) - 1

def tri (k : Nat) : Nat := k * (k + 1) / 2

def fnnn (p : Nat × Nat) : Nat := tri (p.1 + p.2) + p.1

noncomputable def num_elts_below (A : Set Nat) (m : Nat) : Nat :=
  match m with
    | 0 => 0
    | n + 1 => if n ∈ A then (num_elts_below A n) + 1
                else num_elts_below A n

def smallest_preimage_graph {U : Type}
  (g : Nat → U) (A : Set U) : Set (A × Nat) :=
  {(x, n) : A × Nat | g n = x.val ∧ ∀ (m : Nat), g m = x.val → n ≤ m}

def fqn (q : Rat) : Nat := fnnn (fzn q.num, q.den)

def set_rp_below (m : Nat) : Set Nat := {n : Nat | rel_prime m n ∧ n < m}

def func_prod {U V W X : Type} (f : U → V) (g : W → X)
  (p : U × W) : V × X := (f p.1, g p.2)

def set_prod {U V : Type} (A : Set U) (B : Set V) : Set (U × V) :=
  {(a, b) : U × V | a ∈ A ∧ b ∈ B}

notation:75 A:75 " ×ₛ " B:75 => set_prod A B

lemma elt_set_prod {U V : Type} {A : Set U} {B : Set V} (p : ↑A × ↑B) :
    (p.1.val, p.2.val) ∈ A ×ₛ B := And.intro p.1.property p.2.property

def prod_type_to_prod_set {U V : Type}
  (A : Set U) (B : Set V) (p : ↑A × ↑B) : ↑(A ×ₛ B) :=
  Subtype_elt (elt_set_prod p)

def prod_set_to_prod_type {U V : Type}
  (A : Set U) (B : Set V) (p : ↑(A ×ₛ B)) : ↑A × ↑B :=
  (Subtype_elt p.property.left, Subtype_elt p.property.right)

def qr (n a : Nat) : Nat × Nat := (a / n, a % n)

def mod_mod (m n a : Nat) : Nat × Nat := (a % m, a % n)

def seq {U : Type} (A : Set U) : Set (List U) :=
  {l : List U | ∀ x ∈ l, x ∈ A}

def seq_by_length {U : Type} (A : Set U) (n : Nat) : Set (List U) :=
  {l : List U | l ∈ seq A ∧ l.length = n}

def seq_cons (U : Type) (p : U × (List U)) : List U := p.1 :: p.2

def sbl_set {U : Type} (A : Set U) : Set (Set (List U)) :=
  {S : Set (List U) | ∃ (n : Nat), seq_by_length A n = S}

def csb_func_graph {U V : Type}
  (f : U → V) (g : V → U) (X : Set U) : Set (U × V) :=
  {(x, y) : U × V | (x ∈ X ∧ f x = y) ∨ (x ∉ X ∧ g y = x)}

/- Section 8.1 -/
#eval [fnz 0, fnz 1, fnz 2, fnz 3, fnz 4, fnz 5, fnz 6]
  --Answer: [0, -1, 1, -2, 2, -3, 3]

#eval [fzn 0, fzn (-1), fzn 1, fzn (-2), fzn 2, fzn (-3), fzn 3]
  --Answer: [0, 1, 2, 3, 4, 5, 6]

lemma fnz_even (k : Nat) : fnz (2 * k) = ↑k := by
  have h1 : 2 ∣ 2 * k := by
    apply Exists.intro k
    rfl
    done
  have h2 : 0 < 2 := by linarith
  show fnz (2 * k) = ↑k from
    calc fnz (2 * k)
      _ = ↑(2 * k / 2) := if_pos h1
      _ = ↑k := by rw [Nat.mul_div_cancel_left k h2]
  done

lemma fnz_odd (k : Nat) : fnz (2 * k + 1) = -↑(k + 1) := sorry

lemma fzn_nat (k : Nat) : fzn ↑k = 2 * k := by rfl

lemma fzn_neg_succ_nat (k : Nat) : fzn (-↑(k + 1)) = 2 * k + 1 := by rfl

--From exercises of Section 6.1
theorem Exercise_6_1_16a1 : ∀ (n : Nat), nat_even n ∨ nat_odd n := sorry

lemma fzn_fnz : fzn ∘ fnz = id := by
  apply funext        --Goal : ∀ (x : Nat), (fzn ∘ fnz) x = id x
  fix n : Nat
  rewrite [comp_def]  --Goal : fzn (fnz n) = id n
  have h1 : nat_even n ∨ nat_odd n := Exercise_6_1_16a1 n
  by_cases on h1
  · -- Case 1. h1 : nat_even n
    obtain (k : Nat) (h2 : n = 2 * k) from h1
    rewrite [h2, fnz_even, fzn_nat]
    rfl
    done
  · -- Case 2. h1 : nat_odd n
    obtain (k : Nat) (h2 : n = 2 * k + 1) from h1
    rewrite [h2, fnz_odd, fzn_neg_succ_nat]
    rfl
    done
  done

lemma fnz_fzn : fnz ∘ fzn = id  := sorry

lemma fzn_one_one : one_to_one fzn := Theorem_5_3_3_1 fzn fnz fnz_fzn

lemma fzn_onto : onto fzn := Theorem_5_3_3_2 fzn fnz fzn_fnz

lemma fnz_one_one : one_to_one fnz := Theorem_5_3_3_1 fnz fzn fzn_fnz

lemma fnz_onto : onto fnz := Theorem_5_3_3_2 fnz fzn fnz_fzn

theorem N_equinum_Z : Nat ∼ Int :=
  Exists.intro fnz (And.intro fnz_one_one fnz_onto)

theorem Z_equinum_N : Int ∼ Nat :=
  Exists.intro fzn (And.intro fzn_one_one fzn_onto)

lemma fnnn_def (a b : Nat) : fnnn (a, b) = tri (a + b) + a := by rfl

#eval [fnnn (0, 0), fnnn (0, 1), fnnn (1, 0),
  fnnn (0, 2), fnnn (1, 1), fnnn (2, 0)]
  --Answer: [0, 1, 2, 3, 4, 5]

lemma tri_step (k : Nat) : tri (k + 1) = tri k + k + 1 := sorry

lemma tri_incr {j k : Nat} (h1 : j ≤ k) : tri j ≤ tri k := sorry

lemma le_of_fnnn_eq {a1 b1 a2 b2 : Nat}
    (h1 : fnnn (a1, b1) = fnnn (a2, b2)) : a1 + b1 ≤ a2 + b2 := by
  by_contra h2
  have h3 : a2 + b2 + 1 ≤ a1 + b1 := by linarith
  have h4 : fnnn (a2, b2) < fnnn (a1, b1) :=
    calc fnnn (a2, b2)
      _ = tri (a2 + b2) + a2 := by rfl
      _ < tri (a2 + b2) + (a2 + b2) + 1 := by linarith
      _ = tri (a2 + b2 + 1) := (tri_step _).symm
      _ ≤ tri (a1 + b1) := tri_incr h3
      _ ≤ tri (a1 + b1) + a1 := by linarith
      _ = fnnn (a1, b1) := by rfl
  linarith
  done

lemma fnnn_one_one : one_to_one fnnn := by
  fix (a1, b1) : Nat × Nat
  fix (a2, b2) : Nat × Nat
  assume h1 : fnnn (a1, b1) = fnnn (a2, b2)  --Goal : (a1, b1) = (a2, b2)
  have h2 : a1 + b1 ≤ a2 + b2 := le_of_fnnn_eq h1
  have h3 : a2 + b2 ≤ a1 + b1 := le_of_fnnn_eq h1.symm
  have h4 : a1 + b1 = a2 + b2 := by linarith
  rewrite [fnnn_def, fnnn_def, h4] at h1
    --h1 : tri (a2 + b2) + a1 = tri (a2 + b2) + a2
  have h6 : a1 = a2 := Nat.add_left_cancel h1
  rewrite [h6] at h4   --h4 : a2 + b1 = a2 + b2
  have h7 : b1 = b2 := Nat.add_left_cancel h4
  rewrite [h6, h7]
  rfl
  done

lemma fnnn_onto : onto fnnn := by
  define  --Goal : ∀ (y : Nat), ∃ (x : Nat × Nat), fnnn x = y
  by_induc
  · -- Base Case
    apply Exists.intro (0, 0)
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ∃ (x : Nat × Nat), fnnn x = n
    obtain ((a, b) : Nat × Nat) (h1 : fnnn (a, b) = n) from ih
    by_cases h2 : b = 0
    · -- Case 1. h2 : b = 0
      apply Exists.intro (0, a + 1)
      show fnnn (0, a + 1) = n + 1 from
        calc fnnn (0, a + 1)
          _ = tri (0 + (a + 1)) + 0 := by rfl
          _ = tri (a + 1) := by ring
          _ = tri a + a + 1 := tri_step a
          _ = tri (a + 0) + a + 1 := by ring
          _ = fnnn (a, b) + 1 := by rw [h2, fnnn_def]
          _ = n + 1 := by rw [h1]
      done
    · -- Case 2. h2 : b ≠ 0
      obtain (k : Nat) (h3 : b = k + 1) from
        exists_eq_add_one_of_ne_zero h2
      apply Exists.intro (a + 1, k)
      show fnnn (a + 1, k) = n + 1 from
        calc fnnn (a + 1, k)
          _ = tri (a + 1 + k) + (a + 1) := by rfl
          _ = tri (a + (k + 1)) + a + 1 := by ring
          _ = tri (a + b) + a + 1 := by rw [h3]
          _ = fnnn (a, b) + 1 := by rfl
          _ = n + 1 := by rw [h1]
      done
    done
  done

theorem NxN_equinum_N : (Nat × Nat) ∼ Nat :=
  Exists.intro fnnn (And.intro fnnn_one_one fnnn_onto)

lemma neb_base (A : Set Nat) : num_elts_below A 0 = 0 := by rfl

lemma neb_step_elt {A : Set Nat} {n : Nat} (h : n ∈ A) :
    num_elts_below A (n + 1) = num_elts_below A n + 1 := if_pos h

lemma neb_step_not_elt {A : Set Nat} {n : Nat} (h : n ∉ A) :
    num_elts_below A (n + 1) = num_elts_below A n := if_neg h

lemma neb_increase {A : Set Nat} {n : Nat} (h1 : n ∈ A) :
    ∀ ⦃m : Nat⦄, m ≥ n + 1 → num_elts_below A n < num_elts_below A m := by
  by_induc
  · -- Base Case
    rewrite [neb_step_elt h1]
    linarith
    done
  · -- Induction Step
    fix m : Nat
    assume h2 : m ≥ n + 1
    assume ih : num_elts_below A n < num_elts_below A m
    by_cases h3 : m ∈ A
    · -- Case 1. h3 : m ∈ A
      rewrite [neb_step_elt h3]
      linarith
      done
    · -- Case 2. h3 : m ∉ A
      rewrite [neb_step_not_elt h3]
      show num_elts_below A n < num_elts_below A m from ih
      done
    done
  done

lemma le_of_neb_eq {A : Set Nat} {n1 n2 : Nat}
    (h1 : num_elts_below A n1 = num_elts_below A n2) (h2 : n2 ∈ A) :
    n1 ≤ n2 := by
  by_contra h3
  have h4 : n1 ≥ n2 + 1 := by linarith
  have h5 : num_elts_below A n2 < num_elts_below A n1 := neb_increase h2 h4
  linarith
  done

lemma neb_one_one_on (A : Set Nat) :
    one_one_on (num_elts_below A) A := by
  fix n1 : Nat; fix n2 : Nat
  assume h1 : n1 ∈ A
  assume h2 : n2 ∈ A
  assume h3 : num_elts_below A n1 = num_elts_below A n2
  have h4 : n1 ≤ n2 := le_of_neb_eq h3 h2
  have h5 : n2 ≤ n1 := le_of_neb_eq h3.symm h1
  linarith
  done

lemma neb_not_skip {A : Set Nat} : ∀ ⦃m : Nat⦄,
    ∀ t < num_elts_below A m, t ∈ image (num_elts_below A) A := by
  by_induc
  · -- Base Case
    rewrite [neb_base]
    fix t : Nat
    assume h : t < 0
    linarith
    done
  · -- Induction Step
    fix m : Nat
    assume ih : ∀ t < num_elts_below A m, t ∈ image (num_elts_below A) A
    fix t : Nat
    assume h1 : t < num_elts_below A (m + 1)
    by_cases h2 : m ∈ A
    · -- Case 1. h2 : m ∈ A
      rewrite [neb_step_elt h2] at h1
      by_cases h3 : t = num_elts_below A m
      · -- Case 1.1. h3 : t = num_elts_below A m
        show t ∈ image (num_elts_below A) A from
          Exists.intro m (And.intro h2 h3.symm)
        done
      · -- Case 1.2. h3 : t ≠ num_elts_below A m
        have h4 : t ≤ num_elts_below A m := Nat.le_of_lt_succ h1
        have h5 : t < num_elts_below A m := Nat.lt_of_le_of_ne h4 h3
        show t ∈ image (num_elts_below A) A from ih t h5
        done
      done
    · -- Case 2. h2 : m ∉ A
      rewrite [neb_step_not_elt h2] at h1
      show t ∈ image (num_elts_below A) A from ih t h1
      done
    done
  done

lemma neb_image_bdd {A : Set Nat} {m : Nat} (h : ∀ n ∈ A, n < m) :
    image (num_elts_below A) A = I (num_elts_below A m) := by
  apply Set.ext
  fix t : Nat
  apply Iff.intro
  · -- (→)
    assume h2 : t ∈ image (num_elts_below A) A
    obtain (n : Nat) (h3 : n ∈ A ∧ num_elts_below A n = t) from h2
    define
    rewrite [←h3.right]
    show num_elts_below A n < num_elts_below A m from
      neb_increase h3.left (h n h3.left)
    done
  · -- (←)
    assume h2 : t ∈ I (num_elts_below A m)
    define at h2
    show t ∈ image (num_elts_below A) A from neb_not_skip t h2
    done
  done

lemma bdd_subset_nat {A : Set Nat} {m : Nat}
    (h : ∀ n ∈ A, n < m) : I (num_elts_below A m) ∼ A := by
  have h2 : A ∼ image (num_elts_below A) A :=
    equinum_image (neb_one_one_on A)
  rewrite [neb_image_bdd h] at h2        --h2 : A ∼ I (num_elts_below A m)
  show I (num_elts_below A m) ∼ A from Theorem_8_1_3_2 h2
  done

lemma neb_unbdd_onto {A : Set Nat}
    (h : ∀ (m : Nat), ∃ n ∈ A, n ≥ m) :
    onto (func_restrict (num_elts_below A) A) := by
  define
  by_induc
  · -- Base Case
    obtain (m : Nat) (h2 : m ∈ A ∧ m ≥ 0) from h 0
    have h3 : 0 < num_elts_below A (m + 1) := by
      rewrite [neb_step_elt h2.left]
      linarith
      done
    obtain (n : Nat) (h4 : n ∈ A ∧ num_elts_below A n = 0) from
      neb_not_skip 0 h3
    set nA : A := Subtype_elt h4.left
    apply Exists.intro nA
    show func_restrict (num_elts_below A) A nA = 0 from h4.right
    done
  · -- Induction Step
    fix s : Nat
    assume ih : ∃ (x : A), func_restrict (num_elts_below A) A x = s
    obtain (m1 : A) (h2 : func_restrict (num_elts_below A) A m1 = s) from ih
    rewrite [fr_def] at h2
    obtain (m2 : Nat) (h3 : m2 ∈ A ∧ m2 ≥ m1.val + 1) from h (m1.val + 1)
    have h4 : num_elts_below A m1.val < num_elts_below A m2 :=
      neb_increase m1.property h3.right
    rewrite [h2] at h4
    have h5 : s + 1 < num_elts_below A m2 + 1 := by rel [h4]
    rewrite [←neb_step_elt h3.left] at h5
    obtain (n : Nat) (h6 : n ∈ A ∧ num_elts_below A n = s + 1) from
      neb_not_skip (s + 1) h5
    set nA : A := Subtype_elt h6.left
    apply Exists.intro nA
    show func_restrict (num_elts_below A) A nA = s + 1 from h6.right
    done
  done

lemma unbdd_subset_nat {A : Set Nat}
    (h : ∀ (m : Nat), ∃ n ∈ A, n ≥ m) :
    denum A := by
  rewrite [denum_def]
  set f : A → Nat := func_restrict (num_elts_below A) A
  have h1 : one_to_one f :=
    fr_one_one_of_one_one_on (neb_one_one_on A)
  have h2 : onto f := neb_unbdd_onto h
  have h3 : A ∼ Nat := Exists.intro f (And.intro h1 h2)
  show Nat ∼ A from Theorem_8_1_3_2 h3
  done

theorem set_nat_ctble (A : Set Nat) : ctble A := by
  define          --Goal : finite A ∨ denum A
  by_cases h1 : ∃ (m : Nat), ∀ n ∈ A, n < m
  · -- Case 1. h1 : ∃ (m : Nat), ∀ n ∈ A, n < m
    apply Or.inl  --Goal : finite A
    obtain (m : Nat) (h2 : ∀ n ∈ A, n < m) from h1
    define
    apply Exists.intro (num_elts_below A m)
    show I (num_elts_below A m) ∼ A from bdd_subset_nat h2
    done
  · -- Case 2. h1 : ¬∃ (m : Nat), ∀ n ∈ A, n < m
    apply Or.inr  --Goal : denum A
    push_neg at h1
      --This tactic converts h1 to ∀ (m : Nat), ∃ n ∈ A, m ≤ n
    show denum A from unbdd_subset_nat h1
    done
  done

def Univ (U : Type) : Set U := {x : U | True}

lemma elt_univ {U : Type} (x : U) : x ∈ Univ U := by
  define   --Goal : True
  trivial
  done

lemma onto_iff_range_eq_univ {U V : Type} (f : U → V) :
    onto f ↔ range f = Univ V := sorry

lemma univ_equinum_type (U : Type) : Univ U ∼ U := by
  set f : U → U := id
  have h1 : one_to_one f := id_one_one U
  have h2 : onto f := id_onto U
  rewrite [onto_iff_range_eq_univ] at h2  --h2 : range f = Univ U
  have h3 : U ∼ range f := equinum_range h1
  rewrite [h2] at h3
  show Univ U ∼ U from Theorem_8_1_3_2 h3
  done

lemma ctble_of_ctble_equinum {U V : Type}
    (h1 : U ∼ V) (h2 : ctble U) : ctble V := sorry

theorem ctble_iff_set_nat_equinum (U : Type) :
    ctble U ↔ ∃ (J : Set Nat), J ∼ U := by
  apply Iff.intro
  · -- (→)
    assume h1 : ctble U
    define at h1  --h1 : finite U ∨ denum U
    by_cases on h1
    · -- Case 1. h1 : finite U
      define at h1  --h1 : ∃ (n : Nat), I n ∼ U
      obtain (n : Nat) (h2 : I n ∼ U) from h1
      show ∃ (J : Set Nat), J ∼ U from Exists.intro (I n) h2
      done
    · -- Case 2. h1 : denum U
      rewrite [denum_def] at h1  --h1 : Nat ∼ U
      have h2 : Univ Nat ∼ Nat := univ_equinum_type Nat
      apply Exists.intro (Univ Nat)
      show Univ Nat ∼ U from Theorem_8_1_3_3 h2 h1
      done
    done
  · -- (←)
    assume h1 : ∃ (J : Set Nat), J ∼ U
    obtain (J : Set Nat) (h2 : J ∼ U) from h1
    have h3 : ctble J := set_nat_ctble J
    show ctble U from ctble_of_ctble_equinum h2 h3
    done
  done

theorem Theorem_8_1_5_1_to_2 {U : Type} {A : Set U} (h : ctble A) :
    empty A ∨ ∃ (f : Nat → U), A ⊆ range f := by
  or_right with h1                          --h1 : ∃ (x : U), x ∈ A
  obtain (a : U) (h2 : a ∈ A) from h1
  rewrite [ctble_iff_set_nat_equinum] at h  --h : ∃ (J : Set Nat), J ∼ A
  obtain (J : Set Nat) (h3 : J ∼ A) from h
  obtain (f : Nat → U) (h4 : one_one_on f J ∧ image f J = A) from
    type_to_type_of_equinum h3 a
  apply Exists.intro f                      --Goal : A ⊆ range f
  fix y : U
  assume h5 : y ∈ A
  rewrite [←h4.right] at h5
  define at h5
  obtain (n : Nat) (h6 : n ∈ J ∧ f n = y) from h5
  rewrite [←h6.right]
  show f n ∈ range f from elt_range f n
  done

lemma spg_is_func_graph {U : Type} {g : Nat → U} {A : Set U}
    (h : A ⊆ range g) : is_func_graph (smallest_preimage_graph g A) := by
  define
  fix x : A
  exists_unique
  · -- Existence
    set W : Set Nat := {n : Nat | g n = x.val}
    have h1 : ∃ (n : Nat), n ∈ W := h x.property
    show ∃ (y : Nat), (x, y) ∈ smallest_preimage_graph g A from
      well_ord_princ W h1
    done
  · -- Uniqueness
    fix n1 : Nat; fix n2 : Nat
    assume h1 : (x, n1) ∈ smallest_preimage_graph g A
    assume h2 : (x, n2) ∈ smallest_preimage_graph g A
    define at h1; define at h2
    have h3 : n1 ≤ n2 := h1.right n2 h2.left
    have h4 : n2 ≤ n1 := h2.right n1 h1.left
    linarith
    done
  done

lemma spg_one_one {U : Type} {g : Nat → U} {A : Set U} {f : A → Nat}
    (h : graph f = smallest_preimage_graph g A) : one_to_one f := by
  fix a1 : A; fix a2 : A
  assume h1 : f a1 = f a2
  set y : Nat := f a2           --h1 : f a1 = y
  have h2 : f a2 = y := by rfl
  rewrite [←graph_def, h] at h1 --h1 : (a1, y) ∈ smallest_preimage_graph g A
  rewrite [←graph_def, h] at h2 --h2 : (a2, y) ∈ smallest_preimage_graph g A
  define at h1                  --h1 : g y = a1.val ∧ ...
  define at h2                  --h2 : g y = a2.val ∧ ...
  apply Subtype.ext             --Goal : a1.val = a2.val
  rewrite [←h1.left, ←h2.left]
  rfl
  done

theorem Theorem_8_1_5_2_to_3 {U : Type} {A : Set U}
    (h : empty A ∨ ∃ (f : Nat → U), A ⊆ range f) :
    ∃ (f : U → Nat), one_one_on f A := by
  by_cases on h
  · -- Case 1. h : empty A
    set f : U → Nat := constant_func U 0
    apply Exists.intro f
    show one_one_on f A from one_one_on_empty f h
    done
  · -- Case 2. h : ∃ (f : Nat → U), A ⊆ range f
    obtain (g : Nat → U) (h1 : A ⊆ range g) from h
    have h2 : is_func_graph (smallest_preimage_graph g A) :=
      spg_is_func_graph h1
    rewrite [←func_from_graph] at h2
    obtain (F : A → Nat)
      (h3 : graph F = smallest_preimage_graph g A) from h2
    have h4 : one_to_one F := spg_one_one h3
    set f : U → Nat := func_extend F 0
    apply Exists.intro f
    show one_one_on f A from fe_one_one_on_of_one_one h4 0
    done
  done

theorem Theorem_8_1_5_3_to_1 {U : Type} {A : Set U}
    (h1 : ∃ (f : U → Nat), one_one_on f A) :
    ctble A := by
  obtain (f : U → Nat) (h2 : one_one_on f A) from h1
  have h3 : A ∼ image f A := equinum_image h2
  rewrite [ctble_iff_set_nat_equinum]
  show ∃ (J : Set Nat), J ∼ A from
    Exists.intro (image f A) (Theorem_8_1_3_2 h3)
  done

theorem Theorem_8_1_5_2 {U : Type} (A : Set U) :
    ctble A ↔ empty A ∨ ∃ (f : Nat → U), A ⊆ range f := by
  apply Iff.intro Theorem_8_1_5_1_to_2
  assume h1 : empty A ∨ ∃ (f : Nat → U), A ⊆ range f
  have h2 : ∃ (f : U → Nat), one_one_on f A := Theorem_8_1_5_2_to_3 h1
  show ctble A from Theorem_8_1_5_3_to_1 h2
  done

theorem Theorem_8_1_5_3 {U : Type} (A : Set U) :
    ctble A ↔ ∃ (f : U → Nat), one_one_on f A := by
  apply Iff.intro _ Theorem_8_1_5_3_to_1
  assume h1 : ctble A
  have h2 : empty A ∨ ∃ (f : Nat → U), A ⊆ range f := Theorem_8_1_5_1_to_2 h1
  show ∃ (f : U → Nat), one_one_on f A from Theorem_8_1_5_2_to_3 h2
  done

lemma fqn_def (q : Rat) : fqn q = fnnn (fzn q.num, q.den) := by rfl

lemma fqn_one_one : one_to_one fqn := by
  define
  fix q1 : Rat; fix q2 : Rat
  assume h1 : fqn q1 = fqn q2
  rewrite [fqn_def, fqn_def] at h1
    --h1 : fnnn (fzn q1.num, q1.den) = fnnn (fzn q2.num, q2.den)
  have h2 : (fzn q1.num, q1.den) = (fzn q2.num, q2.den) :=
    fnnn_one_one _ _ h1
  have h3 : fzn q1.num = fzn q2.num ∧ q1.den = q2.den :=
    Prod.mk.inj h2
  have h4 : q1.num = q2.num := fzn_one_one _ _ h3.left
  show q1 = q2 from Rat.ext h4 h3.right
  done

lemma range_fqn_unbdd :
    ∀ (m : Nat), ∃ n ∈ range fqn, n ≥ m := by
  fix m : Nat
  set n : Nat := fqn ↑m
  apply Exists.intro n
  apply And.intro
  · -- Proof that n ∈ range fqn
    define
    apply Exists.intro ↑m
    rfl
    done
  · -- Proof that n ≥ m
    show n ≥ m from
      calc n
        _ = tri (2 * m + 1) + 2 * m := by rfl
        _ ≥ m := by linarith
    done
  done

theorem Theorem_8_1_6 : denum Rat := by
  set I : Set Nat := range fqn
  have h1 : Nat ∼ I := unbdd_subset_nat range_fqn_unbdd
  have h2 : Rat ∼ I := equinum_range fqn_one_one
  have h3 : I ∼ Rat := Theorem_8_1_3_2 h2
  show denum Rat from Theorem_8_1_3_3 h1 h3
  done

/- Section 8.1½ -/
theorem Exercise_8_1_6b {U : Type} {A : Set U} {m n : Nat}
    (h1 : numElts A m) (h2 : numElts A n) : m = n := sorry

lemma set_rp_below_def (a m : Nat) :
    a ∈ set_rp_below m ↔ rel_prime m a ∧ a < m := by rfl

lemma neb_nrpb (m : Nat) : ∀ ⦃k : Nat⦄, k ≤ m →
    num_elts_below (set_rp_below m) k = num_rp_below m k := sorry

lemma neb_phi (m : Nat) :
    num_elts_below (set_rp_below m) m = phi m := by
  rewrite [phi_def]
  have h1 : m ≤ m := by linarith
  show num_elts_below (set_rp_below m) m = num_rp_below m m from
    neb_nrpb m h1
  done

lemma phi_is_numElts (m : Nat) :
    numElts (set_rp_below m) (phi m) := by
  rewrite [numElts_def, ←neb_phi m]
    --Goal : I (num_elts_below (set_rp_below m) m) ∼ set_rp_below m
  have h1 : ∀ n ∈ set_rp_below m, n < m := by
    fix n : Nat
    assume h2 : n ∈ set_rp_below m
    define at h2
    show n < m from h2.right
    done
  show I (num_elts_below (set_rp_below m) m) ∼ set_rp_below m from
    bdd_subset_nat h1
  done

lemma Lemma_7_4_7_aux {m n : Nat} {s t : Int}
    (h : s * m + t * n = 1) (a b : Nat) :
    t * n * a + s * m * b ≡ a (MOD m) := by
  define
  apply Exists.intro (s * (b - a))
  show t * n * a + s * m * b - a = m * (s * (b - a)) from
    calc t * n * a + s * m * b - a
      _ = (t * n - 1) * a + s * m * b := by ring
      _ = (t * n - (s * m + t * n)) * a + s * m * b := by rw [h]
      _ = m * (s * (b - a)) := by ring
  done

lemma Lemma_7_4_7 {m n : Nat} [NeZero m] [NeZero n]
    (h1 : rel_prime m n) (a b : Nat) :
    ∃ (r : Nat), r < m * n ∧ r ≡ a (MOD m) ∧ r ≡ b (MOD n) := by
  set s : Int := gcd_c1 m n
  set t : Int := gcd_c2 m n
  have h4 : s * m + t * n = gcd m n := gcd_lin_comb n m
  define at h1                      --h1 : gcd m n = 1
  rewrite [h1, Nat.cast_one] at h4  --h4 : s * m + t * n = 1
  set x : Int := t * n * a + s * m * b
  have h5 : x ≡ a (MOD m) := Lemma_7_4_7_aux h4 a b
  rewrite [add_comm] at h4          --h4 : t * n + s * m = 1
  have h6 : s * m * b + t * n * a ≡ b (MOD n) :=
    Lemma_7_4_7_aux h4 b a
  have h7 : s * m * b + t * n * a = x := by ring
  rewrite [h7] at h6                --h6 : x ≡ b (MOD n)
  have h8 : m * n ≠ 0 := mul_ne_zero (NeZero.ne m) (NeZero.ne n)
  rewrite [←neZero_iff] at h8       --h8 : NeZero (m * n)
  have h9 : 0 ≤ x % ↑(m * n) ∧ x % ↑(m * n) < ↑(m * n) ∧
    x ≡ x % ↑(m * n) (MOD m * n) := mod_cmpl_res (m * n) x
  have h10 : x % ↑(m * n) < ↑(m * n) ∧
    x ≡ x % ↑(m * n) (MOD m * n) := h9.right
  set r : Nat := Int.toNat (x % ↑(m * n))
  have h11 : x % ↑(m * n) = ↑r := (Int.toNat_of_nonneg h9.left).symm
  rewrite [h11, Nat.cast_lt] at h10 --h10 : r < m * n ∧ x ≡ r (MOD m * n)
  apply Exists.intro r
  apply And.intro h10.left
  have h12 : r ≡ x (MOD (m * n)) := congr_symm h10.right
  rewrite [Lemma_7_4_5 _ _ h1] at h12 --h12 : r ≡ x (MOD m) ∧ r ≡ x (MOD n)
  apply And.intro
  · -- Proof that r ≡ a (MOD m)
    show r ≡ a (MOD m) from congr_trans h12.left h5
    done
  · -- Proof that r ≡ b (MOD n)
    show r ≡ b (MOD n) from congr_trans h12.right h6
    done
  done

lemma func_prod_def {U V W X : Type}
    (f : U → V) (g : W → X) (u : U) (w : W) :
    func_prod f g (u, w) = (f u, g w) := by rfl

theorem Theorem_8_1_2_1_type {U V W X : Type}
    (h1 : U ∼ V) (h2 : W ∼ X) : (U × W) ∼ (V × X) := by
  obtain (f : U → V) (h3 : one_to_one f ∧ onto f) from h1
  obtain (g : W → X) (h4 : one_to_one g ∧ onto g) from h2
  apply Exists.intro (func_prod f g)
  apply And.intro
  · -- Proof of one_to_one (func_prod f g)
    fix (u1, w1) : U × W; fix (u2, w2) : U × W
    assume h5 : func_prod f g (u1, w1) = func_prod f g (u2, w2)
    rewrite [func_prod_def, func_prod_def] at h5
    have h6 : f u1 = f u2 ∧ g w1 = g w2 := Prod.mk.inj h5
    have h7 : u1 = u2 := h3.left u1 u2 h6.left
    have h8 : w1 = w2 := h4.left w1 w2 h6.right
    rewrite [h7, h8]
    rfl
    done
  · -- Proof of onto (func_prod f g)
    fix (v, x) : V × X
    obtain (u : U) (h5 : f u = v) from h3.right v
    obtain (w : W) (h6 : g w = x) from h4.right x
    apply Exists.intro (u, w)
    rewrite [func_prod_def, h5, h6]
    rfl
  done

lemma set_prod_def {U V : Type} (A : Set U) (B : Set V) (a : U) (b : V) :
    (a, b) ∈ A ×ₛ B ↔ a ∈ A ∧ b ∈ B := by rfl

lemma set_prod_equinum_type_prod {U V : Type} (A : Set U) (B : Set V) :
    ↑(A ×ₛ B) ∼ (↑A × ↑B) := by
  set F : ↑(A ×ₛ B) → ↑A × ↑B := prod_set_to_prod_type A B
  set G : ↑A × ↑B → ↑(A ×ₛ B) := prod_type_to_prod_set A B
  have h1 : F ∘ G = id := by rfl
  have h2 : G ∘ F = id := by rfl
  have h3 : one_to_one F := Theorem_5_3_3_1 F G h2
  have h4 : onto F := Theorem_5_3_3_2 F G h1
  show ↑(A ×ₛ B) ∼ (↑A × ↑B) from Exists.intro F (And.intro h3 h4)
  done

theorem Theorem_8_1_2_1_set
    {U V W X : Type} {A : Set U} {B : Set V} {C : Set W} {D : Set X}
    (h1 : A ∼ B) (h2 : C ∼ D) : A ×ₛ C ∼ B ×ₛ D := by
  have h3 : ↑(A ×ₛ C) ∼ (↑A × ↑C) := set_prod_equinum_type_prod A C
  have h4 : (↑A × ↑C) ∼ (↑B × ↑D) := Theorem_8_1_2_1_type h1 h2
  have h5 : ↑(B ×ₛ D) ∼ (↑B × ↑D) := set_prod_equinum_type_prod B D
  have h6 : (↑B × ↑D) ∼ ↑(B ×ₛ D) := Theorem_8_1_3_2 h5
  have h7 : ↑(A ×ₛ C) ∼ (↑B × ↑D) := Theorem_8_1_3_3 h3 h4
  show ↑(A ×ₛ C) ∼ ↑(B ×ₛ D) from Theorem_8_1_3_3 h7 h6
  done

lemma qr_def (n a : Nat) : qr n a = (a / n, a % n) := by rfl

lemma qr_one_one (n : Nat) : one_to_one (qr n) := by
  define
  fix a1 : Nat; fix a2 : Nat
  assume h1 : qr n a1 = qr n a2       --Goal : a1 = a2
  rewrite [qr_def, qr_def] at h1
  have h2 : a1 / n = a2 / n ∧ a1 % n = a2 % n := Prod.mk.inj h1
  show a1 = a2 from
    calc a1
      _ = n * (a1 / n) + a1 % n := (Nat.div_add_mod a1 n).symm
      _ = n * (a2 / n) + a2 % n := by rw [h2.left, h2.right]
      _ = a2 := Nat.div_add_mod a2 n
  done

lemma qr_image (m n : Nat) :
    image (qr n) (I (m * n)) = (I m) ×ₛ (I n) := sorry

lemma I_prod (m n : Nat) : I (m * n) ∼ I m ×ₛ I n := by
  rewrite [←qr_image m n]
  show I (m * n) ∼ image (qr n) (I (m * n)) from
    equinum_image (one_one_on_of_one_one (qr_one_one n) (I (m * n)))
  done

theorem numElts_prod {U V : Type} {A : Set U} {B : Set V} {m n : Nat}
    (h1 : numElts A m) (h2 : numElts B n) : numElts (A ×ₛ B) (m * n) := by
  rewrite [numElts_def] at h1     --h1 : I m ∼ A
  rewrite [numElts_def] at h2     --h2 : I n ∼ B
  rewrite [numElts_def]           --Goal : I (m * n) ∼ A ×ₛ B
  have h3 : I m ×ₛ I n ∼ A ×ₛ B := Theorem_8_1_2_1_set h1 h2
  have h4 : I (m * n) ∼ I m ×ₛ I n := I_prod m n
  show I (m * n) ∼ A ×ₛ B from Theorem_8_1_3_3 h4 h3
  done

lemma mod_mod_def (m n a : Nat) : mod_mod m n a = (a % m, a % n) := by rfl

--From exercises of Section 7.3
theorem congr_rel_prime {m a b : Nat} (h1 : a ≡ b (MOD m)) :
    rel_prime m a ↔ rel_prime m b := sorry

theorem rel_prime_mod (m a : Nat) :
    rel_prime m (a % m) ↔ rel_prime m a := sorry

--From exercises of Section 7.4
lemma Lemma_7_4_6 {a b c : Nat} :
    rel_prime (a * b) c ↔ rel_prime a c ∧ rel_prime b c := sorry

lemma left_NeZero_of_mul {m n : Nat} (h : m * n ≠ 0) : NeZero m :=
  neZero_iff.rtl (left_ne_zero_of_mul h)

lemma right_NeZero_of_mul {m n : Nat} (h : m * n ≠ 0) : NeZero n :=
  neZero_iff.rtl (right_ne_zero_of_mul h)

lemma mod_mod_one_one_on {m n : Nat} (h1 : rel_prime m n) :
    one_one_on (mod_mod m n) (set_rp_below (m * n)) := by
  define
  fix a1 : Nat; fix a2 : Nat
  assume h2 : a1 ∈ set_rp_below (m * n)
  assume h3 : a2 ∈ set_rp_below (m * n)
  assume h4 : mod_mod m n a1 = mod_mod m n a2   --Goal : a1 = a2
  define at h2; define at h3
  rewrite [mod_mod_def, mod_mod_def] at h4
  have h5 : a1 % m = a2 % m ∧ a1 % n = a2 % n := Prod.mk.inj h4
  have h6 : m * n ≠ 0 := by linarith
  have h7 : NeZero m := left_NeZero_of_mul h6
  have h8 : NeZero n := right_NeZero_of_mul h6
  rewrite [←congr_iff_mod_eq_Nat, ←congr_iff_mod_eq_Nat] at h5
      --h5 : ↑a1 ≡ ↑a2 (MOD m) ∧ ↑a1 ≡ ↑a2 (MOD n)
  rewrite [←Lemma_7_4_5 _ _ h1] at h5  --h5 : ↑a1 ≡ ↑a2 (MOD m * n)
  rewrite [congr_iff_mod_eq_Nat] at h5 --h5 : a1 % (m * n) = a2 % (m * n)
  rewrite [Nat.mod_eq_of_lt h2.right, Nat.mod_eq_of_lt h3.right] at h5
  show a1 = a2 from h5
  done

lemma mod_elt_set_rp_below {a m : Nat} [NeZero m] (h1 : rel_prime m a) :
    a % m ∈ set_rp_below m := by
  define                  --Goal : rel_prime m (a % m) ∧ a % m < m
  rewrite [rel_prime_mod] --Goal : rel_prime m a ∧ a % m < m
  show rel_prime m a ∧ a % m < m from
    And.intro h1 (mod_nonzero_lt a (NeZero.ne m))
  done

lemma mod_mod_image {m n : Nat} (h1 : rel_prime m n) :
    image (mod_mod m n) (set_rp_below (m * n)) =
      (set_rp_below m) ×ₛ (set_rp_below n) := by
  apply Set.ext
  fix (b, c) : Nat × Nat
  apply Iff.intro
  · -- (→)
    assume h2 : (b, c) ∈ image (mod_mod m n) (set_rp_below (m * n))
    define at h2
    obtain (a : Nat)
      (h3 : a ∈ set_rp_below (m * n) ∧ mod_mod m n a = (b, c)) from h2
    rewrite [set_rp_below_def, mod_mod_def] at h3
    have h4 : rel_prime (m * n) a := h3.left.left
    rewrite [Lemma_7_4_6] at h4   --h4 : rel_prime m a ∧ rel_prime n a
    have h5 : a % m = b ∧ a % n = c := Prod.mk.inj h3.right
    define
    rewrite [←h5.left, ←h5.right]
      --Goal : a % m ∈ set_rp_below m ∧ a % n ∈ set_rp_below n
    have h6 : m * n ≠ 0 := by linarith
    have h7 : NeZero m := left_NeZero_of_mul h6
    have h8 : NeZero n := right_NeZero_of_mul h6
    apply And.intro
    · -- Proof that a % m ∈ set_rp_below m
      show a % m ∈ set_rp_below m from mod_elt_set_rp_below h4.left
      done
    · -- Proof that a % n ∈ set_rp_below n
      show a % n ∈ set_rp_below n from mod_elt_set_rp_below h4.right
      done
    done
  · -- (←)
    assume h2 : (b, c) ∈ set_rp_below m ×ₛ set_rp_below n
    rewrite [set_prod_def, set_rp_below_def, set_rp_below_def] at h2
      --h2 : (rel_prime m b ∧ b < m) ∧ (rel_prime n c ∧ c < n)
    define
    have h3 : m ≠ 0 := by linarith
    have h4 : n ≠ 0 := by linarith
    rewrite [←neZero_iff] at h3
    rewrite [←neZero_iff] at h4
    obtain (a : Nat) (h5 : a < m * n ∧ a ≡ b (MOD m) ∧ a ≡ c (MOD n))
      from Lemma_7_4_7 h1 b c
    apply Exists.intro a
    apply And.intro
    · -- Proof of a ∈ set_rp_below (m * n)
      define                  --Goal : rel_prime (m * n) a ∧ a < m * n
      apply And.intro _ h5.left
      rewrite [Lemma_7_4_6]   --Goal : rel_prime m a ∧ rel_prime n a
      rewrite [congr_rel_prime h5.right.left,
        congr_rel_prime h5.right.right]
      show rel_prime m b ∧ rel_prime n c from
        And.intro h2.left.left h2.right.left
      done
    · -- Proof of mod_mod m n a = (b, c)
      rewrite [congr_iff_mod_eq_Nat, congr_iff_mod_eq_Nat] at h5
      rewrite [mod_mod_def, h5.right.left, h5.right.right]
        --Goal : (b % m, c % n) = (b, c)
      rewrite [Nat.mod_eq_of_lt h2.left.right,
        Nat.mod_eq_of_lt h2.right.right]
      rfl
      done
    done
  done

lemma set_rp_below_prod {m n : Nat} (h1 : rel_prime m n) :
    set_rp_below (m * n) ∼ (set_rp_below m) ×ₛ (set_rp_below n) := by
  rewrite [←mod_mod_image h1]
  show set_rp_below (m * n) ∼
    image (mod_mod m n) (set_rp_below (m * n)) from
    equinum_image (mod_mod_one_one_on h1)
  done

lemma eq_numElts_of_equinum {U V : Type} {A : Set U} {B : Set V} {n : Nat}
    (h1 : A ∼ B) (h2 : numElts A n) : numElts B n := by
  rewrite [numElts_def] at h2   --h2 : I n ∼ A
  rewrite [numElts_def]         --Goal : I n ∼ B
  show I n ∼ B from Theorem_8_1_3_3 h2 h1
  done

theorem Theorem_7_4_4 {m n : Nat} (h1 : rel_prime m n) :
    phi (m * n) = (phi m) * (phi n) := by
  have h2 : numElts (set_rp_below m) (phi m) := phi_is_numElts m
  have h3 : numElts (set_rp_below n) (phi n) := phi_is_numElts n
  have h4 : numElts (set_rp_below (m * n)) (phi (m * n)) :=
    phi_is_numElts (m * n)
  have h5 : numElts (set_rp_below m ×ₛ set_rp_below n) (phi (m * n)) :=
    eq_numElts_of_equinum (set_rp_below_prod h1) h4
  have h6 : numElts (set_rp_below m ×ₛ set_rp_below n) (phi m * phi n) :=
    numElts_prod h2 h3
  show phi (m * n) = phi m * phi n from Exercise_8_1_6b h5 h6
  done

/- Section 8.2 -/
--From exercises of Section 8.1
theorem ctble_set_of_ctble_type {U : Type}
    (h : ctble U) (A : Set U) : ctble A := sorry

theorem NxN_denum : denum (Nat × Nat) := Theorem_8_1_3_2 NxN_equinum_N

theorem Theorem_8_2_1_1 {U V : Type} {A : Set U} {B : Set V}
    (h1 : ctble A) (h2 : ctble B) : ctble (A ×ₛ B) := by
  rewrite [ctble_iff_set_nat_equinum] at h1
  rewrite [ctble_iff_set_nat_equinum] at h2
  obtain (J : Set Nat) (h3 : J ∼ A) from h1
  obtain (K : Set Nat) (h4 : K ∼ B) from h2
  have h5 : J ×ₛ K ∼ A ×ₛ B := Theorem_8_1_2_1_set h3 h4
  have h6 : ctble (Nat × Nat) := Or.inr NxN_denum
  have h7 : ctble (J ×ₛ K) := ctble_set_of_ctble_type h6 (J ×ₛ K)
  show ctble (A ×ₛ B) from ctble_of_ctble_equinum h5 h7
  done

--From exercises of Section 8.1
theorem Exercise_8_1_17 {U : Type} {A B : Set U}
    (h1 : B ⊆ A) (h2 : ctble A) : ctble B := sorry

--From exercises of Section 3.4
theorem Exercise_3_3_12 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋃₀ F ⊆ ⋃₀ G := sorry

lemma Lemma_8_2_2_1 {U : Type} {F : Set (Set U)} {g : Set U → Nat → U}
    (h1 : ctble F) (h2 : ¬empty F) (h3 : ∀ A ∈ F, A ⊆ range (g A)) :
    ctble (⋃₀ F) := by
  rewrite [Theorem_8_1_5_2] at h1
  disj_syll h1 h2               --h1 : ∃ (f : Nat → Set U), F ⊆ range f
  rewrite [Theorem_8_1_5_2]
  apply Or.inr                  --Goal : ∃ (f : Nat → Set U), ⋃₀F ⊆ range f
  obtain (j : Nat → Set U) (h4 : F ⊆ range j) from h1
  obtain (p : Nat → Nat × Nat) (h5 : one_to_one p ∧ onto p) from NxN_denum
  set f : Nat → U := fun (n : Nat) => g (j (p n).1) (p n).2
  apply Exists.intro f
  fix x : U
  assume h6 : x ∈ ⋃₀ F
  obtain (A : Set U) (h7 : A ∈ F ∧ x ∈ A) from h6
  obtain (n1 : Nat) (h8 : j n1 = A) from h4 h7.left
  obtain (n2 : Nat) (h9 : g A n2 = x) from h3 A h7.left h7.right
  obtain (n : Nat) (h10 : p n = (n1, n2)) from h5.right (n1, n2)
  apply Exists.intro n
  show f n = x from
    calc f n
      _ = g (j (p n).1) (p n).2 := by rfl
      _ = g (j n1) n2 := by rw [h10]
      _ = g A n2 := by rw [h8]
      _ = x := by rw [h9]
  done

lemma Lemma_8_2_2_2 {U : Type} {F : Set (Set U)} (h1 : ∀ A ∈ F, ctble A)
    (h2 : ¬empty F) (h3 : ∀ A ∈ F, ¬empty A):
    ∃ (g : Set U → Nat → U), ∀ A ∈ F, A ⊆ range (g A) := by
  have h4 : ∀ (A : Set U), ∃ (gA : Nat → U),
      A ∈ F → A ⊆ range gA := by
    fix A : Set U
    by_cases h4 : A ∈ F
    · -- Case 1. h4 : A ∈ F
      have h5 : ctble A := h1 A h4
      rewrite [Theorem_8_1_5_2] at h5
      disj_syll h5 (h3 A h4)    --h5 : ∃ (f : Nat → U), A ⊆ range f
      obtain (gA : Nat → U) (h6 : A ⊆ range gA) from h5
      apply Exists.intro gA
      assume h7 : A ∈ F
      show A ⊆ range gA from h6
      done
    · -- Case 2. h4 : A ∉ F
      rewrite [not_empty_iff_exists_elt] at h2
      obtain (A0 : Set U) (h5 : A0 ∈ F) from h2
      have h6 : ¬empty A0 := h3 A0 h5
      rewrite [not_empty_iff_exists_elt] at h6
      obtain (x0 : U) (h7 : x0 ∈ A0) from h6
      set gA : Nat → U := constant_func Nat x0
      apply Exists.intro gA
      contrapos
      assume h8 : A ⊈ range gA
      show A ∉ F from h4
      done
    done
  set g : Set U → Nat → U := fun (A : Set U) => Classical.choose (h4 A)
  apply Exists.intro g
  fix A : Set U
  show A ∈ F → A ⊆ range (g A) from Classical.choose_spec (h4 A)
  done

lemma Lemma_8_2_2_3 {U : Type} {F : Set (Set U)}
    (h1 : ctble F) (h2 : ∀ A ∈ F, ctble A) (h3 : ∀ A ∈ F, ¬empty A) :
    ctble (⋃₀ F) := by
  by_cases h4 : empty F
  · -- Case 1. h4 : empty F
    have h5 : empty (⋃₀ F) := by
      contradict h4 with h5
      rewrite [not_empty_iff_exists_elt] at h5
      obtain (x : U) (h6 : x ∈ ⋃₀ F) from h5
      obtain (A : Set U) (h7 : A ∈ F ∧ x ∈ A) from h6
      show ∃ (x : Set U), x ∈ F from Exists.intro A h7.left
      done
    rewrite [←zero_elts_iff_empty] at h5    --h5 : numElts (⋃₀ F) 0
    define
    apply Or.inl
    rewrite [finite_def]
    show ∃ (n : Nat), numElts (⋃₀ F) n from Exists.intro 0 h5
    done
  · -- Case 2. h4 : ¬empty F
    obtain (g : Set U → Nat → U) (h5 : ∀ A ∈ F, A ⊆ range (g A)) from
      Lemma_8_2_2_2 h2 h4 h3
    show ctble (⋃₀ F) from Lemma_8_2_2_1 h1 h4 h5
    done

lemma remove_empty_subset {U : Type} (F : Set (Set U)) :
    {A : Set U | A ∈ F ∧ ¬empty A} ⊆ F := by
  fix X : Set U
  assume h1 : X ∈ {A : Set U | A ∈ F ∧ ¬empty A}
  define at h1
  show X ∈ F from h1.left
  done

lemma remove_empty_union_eq {U : Type} (F : Set (Set U)) :
    ⋃₀ {A : Set U | A ∈ F ∧ ¬empty A} = ⋃₀ F := sorry

theorem Theorem_8_2_2 {U : Type} {F : Set (Set U)}
    (h1 : ctble F) (h2 : ∀ A ∈ F, ctble A) : ctble (⋃₀ F) := by
  set G : Set (Set U) := {A : Set U | A ∈ F ∧ ¬empty A}
  have h3 : G ⊆ F := remove_empty_subset F
  have h4 : ⋃₀ G = ⋃₀ F := remove_empty_union_eq F
  rewrite [←h4]
  have h5 : ctble G := Exercise_8_1_17 h3 h1
  have h6 : ∀ A ∈ G, ctble A := by
    fix A : Set U
    assume h6 : A ∈ G
    show ctble A from h2 A (h3 h6)
    done
  have h7 : ∀ A ∈ G, ¬empty A := by
    fix A : Set U
    assume h7 : A ∈ G
    define at h7
    show ¬empty A from h7.right
    done
  show ctble (⋃₀ G) from Lemma_8_2_2_3 h5 h6 h7
  done

lemma seq_def {U : Type} (A : Set U) (l : List U) :
    l ∈ seq A ↔ ∀ x ∈ l, x ∈ A := by rfl

lemma sbl_base {U : Type} (A : Set U) : seq_by_length A 0 = {[]} := by
  apply Set.ext
  fix l : List U
  apply Iff.intro
  · -- (→)
    assume h1 : l ∈ seq_by_length A 0
    define at h1   --h1 : l ∈ seq A ∧ l.length = 0
    rewrite [List.length_eq_zero_iff] at h1
    define
    show l = [] from h1.right
    done
  · -- (←)
    assume h1 : l ∈ {[]}
    define at h1     --h1 : l = []
    define           --Goal : l ∈ seq A ∧ l.length = 0
    apply And.intro _ (List.length_eq_zero_iff.rtl h1)
    define           --Goal : ∀ x ∈ l, x ∈ A
    fix x : U
    contrapos
    assume h2 : x ∉ A
    rewrite [h1]
    show x ∉ [] from List.not_mem_nil
    done
  done

lemma seq_cons_def {U : Type} (x : U) (l : List U) :
    seq_cons U (x, l) = x :: l := by rfl

lemma seq_cons_one_one (U : Type) : one_to_one (seq_cons U) := by
  fix (a1, l1) : U × List U; fix (a2, l2) : U × List U
  assume h1 : seq_cons U (a1, l1) = seq_cons U (a2, l2)
  rewrite [seq_cons_def, seq_cons_def] at h1  --h1 : a1 :: l1 = a2 :: l2
  rewrite [List.cons_eq_cons] at h1           --h1 : a1 = a2 ∧ l1 = l2
  rewrite [h1.left, h1.right]
  rfl
  done

lemma seq_cons_image {U : Type} (A : Set U) (n : Nat) :
    image (seq_cons U) (A ×ₛ (seq_by_length A n)) =
      seq_by_length A (n + 1) := sorry

lemma Lemma_8_2_4_1 {U : Type} (A : Set U) (n : Nat) :
    A ×ₛ (seq_by_length A n) ∼ seq_by_length A (n + 1) := by
  rewrite [←seq_cons_image A n]
  show A ×ₛ seq_by_length A n ∼
    image (seq_cons U) (A ×ₛ seq_by_length A n) from equinum_image
    (one_one_on_of_one_one (seq_cons_one_one U) (A ×ₛ (seq_by_length A n)))
  done

lemma Lemma_8_2_4_2 {U : Type} {A : Set U} (h1 : ctble A) :
    ∀ (n : Nat), ctble (seq_by_length A n) := by
  by_induc
  · -- Base Case
    rewrite [sbl_base]   --Goal : ctble {[]}
    define
    apply Or.inl         --Goal : finite {[]}
    rewrite [finite_def]
    apply Exists.intro 1 --Goal : numElts {[]} 1
    show numElts {[]} 1 from singleton_one_elt []
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ctble (seq_by_length A n)
    have h2 : A ×ₛ (seq_by_length A n) ∼ seq_by_length A (n + 1) :=
      Lemma_8_2_4_1 A n
    have h3 : ctble (A ×ₛ (seq_by_length A n)) := Theorem_8_2_1_1 h1 ih
    show ctble (seq_by_length A (n + 1)) from ctble_of_ctble_equinum h2 h3
    done
  done

lemma Lemma_8_2_4_3 {U : Type} (A : Set U) : ⋃₀ (sbl_set A) = seq A := by
  apply Set.ext
  fix l : List U
  apply Iff.intro
  · -- (→)
    assume h1 : l ∈ ⋃₀ (sbl_set A)
    define at h1
    obtain (S : Set (List U)) (h2 :  S ∈ sbl_set A ∧ l ∈ S) from h1
    have h3 : S ∈ sbl_set A := h2.left
    define at h3
    obtain (n : Nat) (h4 : seq_by_length A n = S) from h3
    have h5 : l ∈ S := h2.right
    rewrite [←h4] at h5
    define at h5
    show l ∈ seq A from h5.left
    done
  · -- (←)
    assume h1 : l ∈ seq A
    define
    set n : Nat := l.length
    apply Exists.intro (seq_by_length A n)
    apply And.intro
    · -- Proof of seq_by_length A n ∈ sbl_set A
      define
      apply Exists.intro n
      rfl
      done
    · -- Proof of l ∈ seq_by_length A n
      define
      apply And.intro h1
      rfl
      done
    done
  done

lemma Lemma_8_2_4_4 {U : Type} (A : Set U) : ctble (sbl_set A) := by
  rewrite [Theorem_8_1_5_2]
  apply Or.inr   --Goal : ∃ (f : Nat → Set (List U)), sbl_set A ⊆ range f
  apply Exists.intro (seq_by_length A)
  fix S : Set (List U)
  assume h1 : S ∈ sbl_set A
  define at h1; define
  show ∃ (x : Nat), seq_by_length A x = S from h1
  done

theorem Theorem_8_2_4 {U : Type} {A : Set U}
    (h1 : ctble A) : ctble (seq A) := by
  set F : Set (Set (List U)) := sbl_set A
  have h2 : ctble F := Lemma_8_2_4_4 A
  have h3 : ∀ S ∈ F, ctble S := by
    fix S : Set (List U)
    assume h3 : S ∈ F
    define at h3
    obtain (n : Nat) (h4 : seq_by_length A n = S) from h3
    rewrite [←h4]
    show ctble (seq_by_length A n) from Lemma_8_2_4_2 h1 n
    done
  rewrite [←Lemma_8_2_4_3 A]
  show ctble (⋃₀ sbl_set A) from Theorem_8_2_2 h2 h3
  done

theorem Cantor's_theorem : ¬ctble (Set Nat) := by
  by_contra h1
  rewrite [ctble_iff_set_nat_equinum] at h1
  obtain (J : Set Nat) (h2 : J ∼ Set Nat) from h1
  obtain (F : J → Set Nat) (h3 : one_to_one F ∧ onto F) from h2
  set f : Nat → Set Nat := func_extend F ∅
  set D : Set Nat := {n : Nat | n ∉ f n}
  obtain (nJ : J) (h4 : F nJ = D) from h3.right D
  set n : Nat := nJ.val
  have h5 : n ∈ D ↔ n ∉ f n := by rfl
  have h6 : f n = F nJ := fe_elt F ∅ nJ
  rewrite [h6, h4] at h5      --h5 : n ∈ D ↔ n ∉ D
  by_cases h7 : n ∈ D
  · -- Case 1. h7 : n ∈ D
    contradict h7
    show n ∉ D from h5.ltr h7
    done
  · -- Case 2. h7 : n ∉ D
    contradict h7
    show n ∈ D from h5.rtl h7
    done
  done

/- Section 8.3 -/
lemma csb_func_graph_X {U V : Type} {X : Set U} {x : U}
    (f : U → V) (g : V → U) (h : x ∈ X) (y : V) :
    (x, y) ∈ csb_func_graph f g X ↔ f x = y := by
  apply Iff.intro
  · -- (→)
    assume h1 : (x, y) ∈ csb_func_graph f g X
    define at h1
    have h2 : ¬(x ∉ X ∧ g y = x) := by
      demorgan
      show x ∈ X ∨ g y ≠ x from Or.inl h
      done
    disj_syll h1 h2        --h1 : x ∈ X ∧ f x = y
    show f x = y from h1.right
    done
  · -- (←)
    assume h1 : f x = y
    define
    apply Or.inl
    show x ∈ X ∧ f x = y from And.intro h h1
    done
  done

lemma csb_func_graph_not_X {U V : Type} {X : Set U} {x : U}
    (f : U → V) (g : V → U) (h : x ∉ X) (y : V) :
    (x, y) ∈ csb_func_graph f g X ↔ g y = x := sorry

lemma csb_func_graph_is_func_graph {U V : Type} {g : V → U} {X : Set U}
    (f : U → V) (h1 : ∀ (x : U), x ∉ X → x ∈ range g) (h2 : one_to_one g) :
    is_func_graph (csb_func_graph f g X) := by
  define
  fix x : U
  by_cases h3 : x ∈ X
  · -- Case 1. h3 : x ∈ X
    exists_unique
    · -- Existence
      apply Exists.intro (f x)
      rewrite [csb_func_graph_X f g h3]
      rfl
      done
    · -- Uniqueness
      fix y1 : V; fix y2 : V
      assume h4 : (x, y1) ∈ csb_func_graph f g X
      assume h5 : (x, y2) ∈ csb_func_graph f g X
      rewrite [csb_func_graph_X f g h3] at h4  --h4 : f x = y1
      rewrite [csb_func_graph_X f g h3] at h5  --h5 : f x = y2
      rewrite [←h4, ←h5]
      rfl
      done
    done
  · -- Case 2. h3 : x ∉ X
    exists_unique
    · -- Existence
      obtain (y : V) (h4 : g y = x) from h1 x h3
      apply Exists.intro y
      rewrite [csb_func_graph_not_X f g h3]
      show g y = x from h4
      done
    · -- Uniqueness
      fix y1 : V; fix y2 : V
      assume h4 : (x, y1) ∈ csb_func_graph f g X
      assume h5 : (x, y2) ∈ csb_func_graph f g X
      rewrite [csb_func_graph_not_X f g h3] at h4 --h4 : g y1 = x
      rewrite [csb_func_graph_not_X f g h3] at h5 --h5 : g y2 = x
      rewrite [←h5] at h4
      show y1 = y2 from h2 y1 y2 h4
      done
    done
  done

lemma csb_func_X
    {U V : Type} {f h : U → V} {g : V → U} {X : Set U} {x : U}
    (h1 : graph h = csb_func_graph f g X) (h2 : x ∈ X) : h x = f x := by
  rewrite [←graph_def, h1, csb_func_graph_X f g h2]
  rfl
  done

lemma csb_func_not_X
    {U V : Type} {f h : U → V} {g : V → U} {X : Set U} {x : U}
    (h1 : graph h = csb_func_graph f g X) (h2 : x ∉ X) : g (h x) = x := by
  have h3 : (x, h x) ∈ graph h := by rfl
  rewrite [h1, csb_func_graph_not_X f g h2] at h3
  show g (h x) = x from h3
  done

lemma csb_X_of_X
    {U V : Type} {f h : U → V} {g : V → U} {A0 : Set U} {x1 x2 : U}
    (h1 : graph h = csb_func_graph f g (cumul_image (g ∘ f) A0))
    (h2 : h x1 = h x2) (h3 : x1 ∈ cumul_image (g ∘ f) A0) :
    x2 ∈ cumul_image (g ∘ f) A0 := by
  by_contra h4                      --h4 : x2 ∉ cumul_image (g ∘ f) A0
  rewrite [csb_func_X h1 h3] at h2  --h2 : f x1 = h x2
  have h5 : (g ∘ f) x1 = x2 :=
    calc (g ∘ f) x1
      _ = g (f x1) := by rfl
      _ = g (h x2) := by rw [h2]
      _ = x2 := csb_func_not_X h1 h4
  obtain (n : Nat) (h6 : x1 ∈ rep_image (g ∘ f) n A0) from h3
  contradict h4               --Goal : x2 ∈ cumul_image (g ∘ f) A0
  apply Exists.intro (n + 1)  --Goal : x2 ∈ rep_image (g ∘ f) (n + 1) A0
  rewrite [rep_image_step]
  apply Exists.intro x1
  show x1 ∈ rep_image (g ∘ f) n A0 ∧ (g ∘ f) x1 = x2 from
    And.intro h6 h5
  done

theorem Cantor_Schroeder_Bernstein_theorem
    {U V : Type} {f : U → V} {g : V → U}
    (h1 : one_to_one f) (h2 : one_to_one g) : U ∼ V := by
  set A0 : Set U := {x : U | x ∉ range g}
  set X : Set U := cumul_image (g ∘ f) A0
  set H : Set (U × V) := csb_func_graph f g X
  have h3 : ∀ (x : U), x ∉ X → x ∈ range g := by
    fix x : U
    contrapos
    assume h3 : x ∉ range g
    define
    apply Exists.intro 0
    rewrite [rep_image_base]
    show x ∈ A0 from h3
    done
  have h4 : is_func_graph H := csb_func_graph_is_func_graph f h3 h2
  rewrite [←func_from_graph] at h4
  obtain (h : U → V) (h5 : graph h = H) from h4
  apply Exists.intro h
  apply And.intro
  · -- proof that h is one-to-one
    fix x1 : U; fix x2 : U
    assume h6 : h x1 = h x2
    by_cases h7 : x1 ∈ X
    · -- Case 1. h7 : x1 ∈ X
      have h8 : x2 ∈ X := csb_X_of_X h5 h6 h7
      rewrite [csb_func_X h5 h7, csb_func_X h5 h8] at h6 --h6 : f x1 = f x2
      show x1 = x2 from h1 x1 x2 h6
      done
    · -- Case 2. h7 : x1 ∉ X
      have h8 : x2 ∉ X := by
        contradict h7 with h8
        show x1 ∈ X from csb_X_of_X h5 h6.symm h8
        done
      show x1 = x2 from
        calc x1
          _ = g (h x1) := (csb_func_not_X h5 h7).symm
          _ = g (h x2) := by rw [h6]
          _ = x2 := csb_func_not_X h5 h8
      done
    done
  · -- proof that h is onto
    fix y : V
    by_cases h6 : g y ∈ X
    · -- Case 1. h6 : g y ∈ X
      define at h6
      obtain (n : Nat) (h7 : g y ∈ rep_image (g ∘ f) n A0) from h6
      have h8 : n ≠ 0 := by
        by_contra h8
        rewrite [h8, rep_image_base] at h7 --h7 : g y ∈ A0
        define at h7                       --h7 : ¬∃ (x : V), g x = g y
        contradict h7
        apply Exists.intro y
        rfl
        done
      obtain (k : Nat) (h9 : n = k + 1) from
        exists_eq_add_one_of_ne_zero h8
      rewrite [h9, rep_image_step] at h7
      obtain (x : U)
        (h10 : x ∈ rep_image (g ∘ f) k A0 ∧ (g ∘ f) x = g y) from h7
      have h11 : g (f x) = g y := h10.right
      have h12 : f x = y := h2 (f x) y h11
      have h13 : x ∈ X := Exists.intro k h10.left
      apply Exists.intro x
      rewrite [csb_func_X h5 h13]
      show f x = y from h12
      done
    · -- Case 2. h6 : g y ∉ X
      apply Exists.intro (g y)
      have h7 : g (h (g y)) = g y := csb_func_not_X h5 h6
      show h (g y) = y from h2 (h (g y)) y h7
      done
    done
  done


end HTPI

-- ════════════════════════════════════════════════════════════════
-- EXERCISES (258 total)
-- ════════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════════════════
-- Chapter 3: Proofs (23 exercises)
-- ════════════════════════════════════════════════════════════════

namespace HTPI.Exercises

/- Sections 3.1 and 3.2 -/
-- 1.
theorem Exercise_3_2_1a (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → R) : P → R := by

  sorry

-- 2.
theorem Exercise_3_2_1b (P Q R : Prop)
    (h1 : ¬R → (P → ¬Q)) : P → (Q → R) := by

  sorry

-- 3.
theorem Exercise_3_2_2a (P Q R : Prop)
    (h1 : P → Q) (h2 : R → ¬Q) : P → ¬R := by

  sorry

-- 4.
theorem Exercise_3_2_2b (P Q : Prop)
    (h1 : P) : Q → ¬(Q → ¬P) := by

  sorry

/- Section 3.3 -/
-- 1.
theorem Exercise_3_3_1
    (U : Type) (P Q : Pred U) (h1 : ∃ (x : U), P x → Q x) :
    (∀ (x : U), P x) → ∃ (x : U), Q x := by

  sorry

-- 2.
theorem Exercise_3_3_8 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : A ⊆ ⋃₀ F := by

  sorry

-- 3.
theorem Exercise_3_3_9 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : ⋂₀ F ⊆ A := by

  sorry

-- 4.
theorem Exercise_3_3_10 (U : Type) (B : Set U) (F : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → B ⊆ A) : B ⊆ ⋂₀ F := by

  sorry

-- 5.
theorem Exercise_3_3_13 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋂₀ G ⊆ ⋂₀ F := by

  sorry

/- Section 3.4 -/
-- 1.
theorem Exercise_3_4_2 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by

  sorry

-- 2.
theorem Exercise_3_4_4 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊈ C) : B ⊈ C := by

  sorry

-- 3.
theorem Exercise_3_3_12 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋃₀ F ⊆ ⋃₀ G := by

  sorry

-- 4.
theorem Exercise_3_3_16 (U : Type) (B : Set U)
    (F : Set (Set U)) : F ⊆ 𝒫 B → ⋃₀ F ⊆ B := by

  sorry

-- 5.
theorem Exercise_3_3_17 (U : Type) (F G : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ⊆ B) :
    ⋃₀ F ⊆ ⋂₀ G := by

  sorry

-- 6.
theorem Exercise_3_4_7 (U : Type) (A B : Set U) :
    𝒫 (A ∩ B) = 𝒫 A ∩ 𝒫 B := by

  sorry

-- 7.
theorem Exercise_3_4_17 (U : Type) (A : Set U) : A = ⋃₀ (𝒫 A) := by

  sorry

-- 8.
theorem Exercise_3_4_18a (U : Type) (F G : Set (Set U)) :
    ⋃₀ (F ∩ G) ⊆ (⋃₀ F) ∩ (⋃₀ G) := by

  sorry

-- 9.
theorem Exercise_3_4_19 (U : Type) (F G : Set (Set U)) :
    (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) ↔
      ∀ (A B : Set U), A ∈ F → B ∈ G → A ∩ B ⊆ ⋃₀ (F ∩ G) := by

  sorry

/- Section 3.5 -/
-- 1.
theorem Exercise_3_5_2 (U : Type) (A B C : Set U) :
    (A ∪ B) \ C ⊆ A ∪ (B \ C) := sorry

-- 2.
theorem Exercise_3_5_5 (U : Type) (A B C : Set U)
    (h1 : A ∩ C ⊆ B ∩ C) (h2 : A ∪ C ⊆ B ∪ C) : A ⊆ B := sorry

-- 3.
theorem Exercise_3_5_7 (U : Type) (A B C : Set U) :
    A ∪ C ⊆ B ∪ C ↔ A \ C ⊆ B \ C := sorry

-- 4.
theorem Exercise_3_5_8 (U : Type) (A B : Set U) :
    𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B) := sorry

-- 5.
theorem Exercise_3_5_17b (U : Type) (F : Set (Set U)) (B : Set U) :
    B ∪ (⋂₀ F) = {x : U | ∀ (A : Set U), A ∈ F → x ∈ B ∪ A} := sorry

-- 6.
theorem Exercise_3_5_18 (U : Type) (F G H : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ∪ B ∈ H) :
    ⋂₀ H ⊆ (⋂₀ F) ∪ (⋂₀ G) := sorry

-- 7.
theorem Exercise_3_5_24a (U : Type) (A B C : Set U) :
    (A ∪ B) ∆ C ⊆ (A ∆ C) ∪ (B ∆ C) := sorry

/- Section 3.6 -/
-- 1.
theorem Exercise_3_4_15 (U : Type) (B : Set U) (F : Set (Set U)) :
    ⋃₀ {X : Set U | ∃ (A : Set U), A ∈ F ∧ X = A \ B}
      ⊆ ⋃₀ (F \ 𝒫 B) := sorry

-- 2.
theorem Exercise_3_5_9 (U : Type) (A B : Set U)
    (h1 : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B) : A ⊆ B ∨ B ⊆ A := by
  --Hint:  Start like this:
  have h2 : A ∪ B ∈ 𝒫 (A ∪ B) := sorry
  sorry

-- 3.
theorem Exercise_3_6_6b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∪ B = A := sorry

-- 4.
theorem Exercise_3_6_7b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∩ B = A := sorry

-- 5.
theorem Exercise_3_6_8a (U : Type) : ∀ (A : Set U),
    ∃! (B : Set U), ∀ (C : Set U), C \ A = C ∩ B := sorry

-- 6.
theorem Exercise_3_6_10 (U : Type) (A : Set U)
    (h1 : ∀ (F : Set (Set U)), ⋃₀ F = A → A ∈ F) :
    ∃! (x : U), x ∈ A := by
  --Hint:  Start like this:
  set F0 : Set (Set U) := {X : Set U | X ⊆ A ∧ ∃! (x : U), x ∈ X}
  --Now F0 is in the tactic state, with the definition above
  have h2 : ⋃₀ F0 = A := sorry
  sorry

/- Section 3.7 -/
-- 1.
theorem Exercise_3_3_18a (a b c : Int)
    (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ (b + c) := sorry

-- 2.
theorem Exercise_3_4_6 (U : Type) (A B C : Set U) :
    A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  apply Set.ext
  fix x : U
  show x ∈ A \ (B ∩ C) ↔ x ∈ A \ B ∪ A \ C from
    calc x ∈ A \ (B ∩ C)
      _ ↔ x ∈ A ∧ ¬(x ∈ B ∧ x ∈ C) := sorry
      _ ↔ x ∈ A ∧ (x ∉ B ∨ x ∉ C) := sorry
      _ ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ A ∧ x ∉ C) := sorry
      _ ↔ x ∈ (A \ B) ∪ (A \ C) := sorry
  done

-- 3.
theorem Exercise_3_4_10 (x y : Int)
    (h1 : odd x) (h2 : odd y) : even (x - y) := sorry

-- 4.
theorem Exercise_3_4_27a :
    ∀ (n : Int), 15 ∣ n ↔ 3 ∣ n ∧ 5 ∣ n := sorry

-- 5.
theorem Like_Exercise_3_7_5 (U : Type) (F : Set (Set U))
    (h1 : 𝒫 (⋃₀ F) ⊆ ⋃₀ {𝒫 A | A ∈ F}) :
    ∃ (A : Set U), A ∈ F ∧ ∀ (B : Set U), B ∈ F → B ⊆ A := sorry

-- ════════════════════════════════════════════════════════════════
-- Chapter 4: Relations (37 exercises)
-- ════════════════════════════════════════════════════════════════

namespace HTPI.Exercises

/- Section 4.2 -/
-- 1.
theorem Exercise_4_2_9a {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : Dom (comp S R) ⊆ Dom R := sorry

-- 2.
theorem Exercise_4_2_9b {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : Ran R ⊆ Dom S → Dom (comp S R) = Dom R := sorry

-- 3.
--Fill in the blank to get a correct theorem and then prove the theorem
theorem Exercise_4_2_9c {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : ___ → Ran (comp S R) = Ran S := sorry

-- 4.
theorem Exercise_4_2_12a {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    (comp S R) \ (comp T R) ⊆ comp (S \ T) R := sorry

-- 5.
--You won't be able to complete this proof
theorem Exercise_4_2_12b {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S \ T) R ⊆ (comp S R) \ (comp T R) := sorry

-- 6.
--You might not be able to complete this proof
theorem Exercise_4_2_14c {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S ∩ T) R = (comp S R) ∩ (comp T R) := sorry

-- 7.
--You might not be able to complete this proof
theorem Exercise_4_2_14d {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S ∪ T) R = (comp S R) ∪ (comp T R) := sorry

/- Section 4.3 -/
-- 1.
example :
    elementhood Int 6 {n : Int | ∃ (k : Int), n = 2 * k} := sorry

-- 2.
theorem Theorem_4_3_4_1 {A : Type} (R : BinRel A) :
    reflexive R ↔ {(x, y) : A × A | x = y} ⊆ extension R := sorry

-- 3.
theorem Theorem_4_3_4_3 {A : Type} (R : BinRel A) :
    transitive R ↔
      comp (extension R) (extension R) ⊆ extension R := sorry

-- 4.
theorem Exercise_4_3_12a {A : Type} (R : BinRel A) (h1 : reflexive R) :
    reflexive (RelFromExt (inv (extension R))) := sorry

-- 5.
theorem Exercise_4_3_12c {A : Type} (R : BinRel A) (h1 : transitive R) :
    transitive (RelFromExt (inv (extension R))) := sorry

-- 6.
theorem Exercise_4_3_18 {A : Type}
    (R S : BinRel A) (h1 : transitive R) (h2 : transitive S)
    (h3 : comp (extension S) (extension R) ⊆
      comp (extension R) (extension S)) :
    transitive (RelFromExt (comp (extension R) (extension S))) := sorry

-- 7.
theorem Exercise_4_3_20 {A : Type} (R : BinRel A) (S : BinRel (Set A))
    (h : ∀ (X Y : Set A), S X Y ↔ X ≠ ∅ ∧ Y ≠ ∅ ∧
    ∀ (x y : A), x ∈ X → y ∈ Y → R x y) :
    transitive R → transitive S := sorry

-- 8.
--You might not be able to complete this proof
theorem Exercise_4_3_13b {A : Type}
    (R1 R2 : BinRel A) (h1 : symmetric R1) (h2 : symmetric R2) :
    symmetric (RelFromExt ((extension R1) ∪ (extension R2))) := sorry

-- 9.
--You might not be able to complete this proof
theorem Exercise_4_3_13c {A : Type}
    (R1 R2 : BinRel A) (h1 : transitive R1) (h2 : transitive R2) :
    transitive (RelFromExt ((extension R1) ∪ (extension R2))) := sorry

-- 10.
--You might not be able to complete this proof
theorem Exercise_4_3_19 {A : Type} (R : BinRel A) (S : BinRel (Set A))
    (h : ∀ (X Y : Set A), S X Y ↔ ∃ (x y : A), x ∈ X ∧ y ∈ Y ∧ R x y) :
    transitive R → transitive S := sorry

/- Section 4.4 -/
-- 1.
theorem Example_4_4_3_1 {A : Type} : partial_order (sub A) := sorry

-- 2.
theorem Theorem_4_4_6_1 {A : Type} (R : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R) (h2 : smallestElt R b B) :
    ∀ (c : A), smallestElt R c B → b = c := sorry

-- 3.
--If F is a set of sets, then ⋃₀ F is the lub of F in the subset ordering
theorem Theorem_4_4_11 {A : Type} (F : Set (Set A)) :
    lub (sub A) (⋃₀ F) F := sorry

-- 4.
theorem Exercise_4_4_8 {A B : Type} (R : BinRel A) (S : BinRel B)
    (T : BinRel (A × B)) (h1 : partial_order R) (h2 : partial_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      T (a, b) (a', b') ↔ R a a' ∧ S b b') :
    partial_order T := sorry

-- 5.
theorem Exercise_4_4_9_part {A B : Type} (R : BinRel A) (S : BinRel B)
    (L : BinRel (A × B)) (h1 : total_order R) (h2 : total_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ↔ R a a' ∧ (a = a' → S b b')) :
    ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ∨ L (a', b') (a, b) := sorry

-- 6.
theorem Exercise_4_4_15a {A : Type}
    (R1 R2 : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R1) (h2 : partial_order R2)
    (h3 : extension R1 ⊆ extension R2) :
    smallestElt R1 b B → smallestElt R2 b B := sorry

-- 7.
theorem Exercise_4_4_15b {A : Type}
    (R1 R2 : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R1) (h2 : partial_order R2)
    (h3 : extension R1 ⊆ extension R2) :
    minimalElt R2 b B → minimalElt R1 b B := sorry

-- 8.
theorem Exercise_4_4_18a {A : Type}
    (R : BinRel A) (B1 B2 : Set A) (h1 : partial_order R)
    (h2 : ∀ x ∈ B1, ∃ y ∈ B2, R x y) (h3 : ∀ x ∈ B2, ∃ y ∈ B1, R x y) :
    ∀ (x : A), upperBd R x B1 ↔ upperBd R x B2 := sorry

-- 9.
theorem Exercise_4_4_22 {A : Type}
    (R : BinRel A) (B1 B2 : Set A) (x1 x2 : A)
    (h1 : partial_order R) (h2 : lub R x1 B1) (h3 : lub R x2 B2) :
    B1 ⊆ B2 → R x1 x2 := sorry

-- 10.
theorem Exercise_4_4_24 {A : Type} (R : Set (A × A)) :
    smallestElt (sub (A × A)) (R ∪ (inv R))
    {T : Set (A × A) | R ⊆ T ∧ symmetric (RelFromExt T)} := sorry

/- Section 4.5 -/
-- 1.
lemma overlap_implies_equal {A : Type}
    (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ Y ∈ F, ∀ (x : A), x ∈ X → x ∈ Y → X = Y := sorry

-- 2.
lemma Lemma_4_5_7_ref {A : Type} (F : Set (Set A)) (h : partition F) :
    reflexive (EqRelFromPart F) := sorry

-- 3.
lemma Lemma_4_5_7_symm {A : Type} (F : Set (Set A)) (h : partition F) :
    symmetric (EqRelFromPart F) := sorry

-- 4.
lemma Lemma_4_5_7_trans {A : Type} (F : Set (Set A)) (h : partition F) :
    transitive (EqRelFromPart F) := sorry

-- 5.
lemma Lemma_4_5_8 {A : Type} (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ x ∈ X, equivClass (EqRelFromPart F) x = X := sorry

-- 6.
lemma elt_mod_equiv_class_of_elt
    {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ X ∈ mod A R, ∀ x ∈ X, equivClass R x = X := sorry

-- Definitions for next three exercises:
def dot {A : Type} (F G : Set (Set A)) : Set (Set A) :=
    {Z : Set A | ¬empty Z ∧ ∃ X ∈ F, ∃ Y ∈ G, Z = X ∩ Y}

def conj {A : Type} (R S : BinRel A) (x y : A) : Prop :=
    R x y ∧ S x y

-- 7.
theorem Exercise_4_5_20a {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    equiv_rel (conj R S) := sorry

-- 8.
theorem Exercise_4_5_20b {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    ∀ (x : A), equivClass (conj R S) x =
      equivClass R x ∩ equivClass S x := sorry

-- 9.
theorem Exercise_4_5_20c {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    mod A (conj R S) = dot (mod A R) (mod A S) := sorry

-- 10.
def equiv_mod (m x y : Int) : Prop := m ∣ (x - y)

theorem Theorem_4_5_10 : ∀ (m : Int), equiv_rel (equiv_mod m) := sorry

-- ════════════════════════════════════════════════════════════════
-- Chapter 5: Functions (46 exercises)
-- ════════════════════════════════════════════════════════════════

namespace HTPI.Exercises

/- Section 5.1 -/
-- 1.
theorem func_from_graph_ltr {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) → is_func_graph F := sorry

-- 2.
theorem Exercise_5_1_13a
    {A B C : Type} (R : Set (A × B)) (S : Set (B × C)) (f : A → C)
    (h1 : ∀ (b : B), b ∈ Ran R ∧ b ∈ Dom S) (h2 : graph f = comp S R) :
    is_func_graph S := sorry

-- 3.
theorem Exercise_5_1_14a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : A), R x y ↔ S (f x) (f y)) :
    reflexive S → reflexive R := sorry

-- 4.
--You might not be able to complete this proof
theorem Exercise_5_1_15a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v) :
    reflexive R → reflexive S := sorry

-- 5.
--You might not be able to complete this proof
theorem Exercise_5_1_15c
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v) :
    transitive R → transitive S := sorry

-- 6.
theorem Exercise_5_1_16b
    {A B : Type} (R : BinRel B) (S : BinRel (A → B))
    (h : ∀ (f g : A → B), S f g ↔ ∀ (x : A), R (f x) (g x)) :
    symmetric R → symmetric S := sorry

-- 7.
theorem Exercise_5_1_17a {A : Type} (f : A → A) (a : A)
    (h : ∀ (x : A), f x = a) : ∀ (g : A → A), f ∘ g = f := sorry

-- 8.
theorem Exercise_5_1_17b {A : Type} (f : A → A) (a : A)
    (h : ∀ (g : A → A), f ∘ g = f) :
    ∃ (y : A), ∀ (x : A), f x = y := sorry

/- Section 5.2 -/
-- 1.
theorem Exercise_5_2_10a {A B C : Type} (f: A → B) (g : B → C) :
    onto (g ∘ f) → onto g := sorry

-- 2.
theorem Exercise_5_2_10b {A B C : Type} (f: A → B) (g : B → C) :
    one_to_one (g ∘ f) → one_to_one f := sorry

-- 3.
theorem Exercise_5_2_11a {A B C : Type} (f: A → B) (g : B → C) :
    onto f → ¬(one_to_one g) → ¬(one_to_one (g ∘ f)) := sorry

-- 4.
theorem Exercise_5_2_11b {A B C : Type} (f: A → B) (g : B → C) :
    ¬(onto f) → one_to_one g → ¬(onto (g ∘ f)) := sorry

-- 5.
theorem Exercise_5_2_12 {A B : Type} (f : A → B) (g : B → Set A)
    (h : ∀ (b : B), g b = {a : A | f a = b}) :
    onto f → one_to_one g := sorry

-- 6.
theorem Exercise_5_2_16 {A B C : Type}
    (R : Set (A × B)) (S : Set (B × C)) (f : A → C) (g : B → C)
    (h1 : graph f = comp S R) (h2 : graph g = S) (h3 : one_to_one g) :
    is_func_graph R := sorry

-- 7.
theorem Exercise_5_2_17a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h1 : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v)
    (h2 : onto f) : reflexive R → reflexive S := sorry

-- 8.
theorem Exercise_5_2_17b
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h1 : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v)
    (h2 : one_to_one f) : transitive R → transitive S := sorry

-- 9.
theorem Exercise_5_2_21a {A B C : Type} (f : B → C) (g h : A → B)
    (h1 : one_to_one f) (h2 : f ∘ g = f ∘ h) : g = h := sorry

-- 10.
theorem Exercise_5_2_21b {A B C : Type} (f : B → C) (a : A)
    (h1 : ∀ (g h : A → B), f ∘ g = f ∘ h → g = h) :
    one_to_one f := sorry

/- Section 5.3 -/
-- 1.
theorem Theorem_5_3_2_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : f ∘ g = id := sorry

-- 2.
theorem Theorem_5_3_3_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : f ∘ g = id) : onto f := sorry

-- 3.
theorem Exercise_5_3_11a {A B : Type} (f : A → B) (g : B → A) :
    one_to_one f → f ∘ g = id → graph g = inv (graph f) := sorry

-- 4.
theorem Exercise_5_3_11b {A B : Type} (f : A → B) (g : B → A) :
    onto f → g ∘ f = id → graph g = inv (graph f) := sorry

-- 5.
theorem Exercise_5_3_14a {A B : Type} (f : A → B) (g : B → A)
    (h : f ∘ g = id) : ∀ x ∈ Ran (graph g), g (f x) = x := sorry

-- 6.
theorem Exercise_5_3_18 {A B C : Type} (f : A → C) (g : B → C)
    (h1 : one_to_one g) (h2 : onto g) :
    ∃ (h : A → B), g ∘ h = f := sorry

-- Definition for next two exercises:
def conjugate (A : Type) (f1 f2 : A → A) : Prop :=
    ∃ (g g' : A → A), (f1 = g' ∘ f2 ∘ g) ∧ (g ∘ g' = id) ∧ (g' ∘ g = id)

-- 7.
theorem Exercise_5_3_17a {A : Type} : symmetric (conjugate A) := sorry

-- 8.
theorem Exercise_5_3_17b {A : Type} (f1 f2 : A → A)
    (h1 : conjugate A f1 f2) (h2 : ∃ (a : A), f1 a = a) :
    ∃ (a : A), f2 a = a := sorry

/- Section 5.4 -/
-- 1.
example {A : Type} (F : Set (Set A)) (B : Set A) :
    smallestElt (sub A) B F → B = ⋂₀ F := sorry

-- 2.
def complement {A : Type} (B : Set A) : Set A := {a : A | a ∉ B}

theorem Exercise_5_4_7 {A : Type} (f g : A → A) (C : Set A)
    (h1 : f ∘ g = id) (h2 : closed f C) : closed g (complement C) := sorry

-- 3.
theorem Exercise_5_4_9a {A : Type} (f : A → A) (C1 C2 : Set A)
    (h1 : closed f C1) (h2 : closed f C2) : closed f (C1 ∪ C2) := sorry

-- 4.
theorem Exercise_5_4_10a {A : Type} (f : A → A) (B1 B2 C1 C2 : Set A)
    (h1 : closure f B1 C1) (h2 : closure f B2 C2) :
    B1 ⊆ B2 → C1 ⊆ C2 := sorry

-- 5.
theorem Exercise_5_4_10b {A : Type} (f : A → A) (B1 B2 C1 C2 : Set A)
    (h1 : closure f B1 C1) (h2 : closure f B2 C2) :
    closure f (B1 ∪ B2) (C1 ∪ C2) := sorry

-- 6.
theorem Theorem_5_4_9 {A : Type} (f : A → A → A) (B : Set A) :
    ∃ (C : Set A), closure2 f B C := sorry

-- 7.
theorem Exercise_5_4_13a {A : Type} (F : Set (A → A)) (B : Set A) :
    ∃ (C : Set A), closure_family F B C := sorry

/- Section 5.5 -/

--Warning!  Not all of these examples are correct!
example {A B : Type} (f : A → B) (W X : Set A) :
    image f (W ∪ X) = image f W ∪ image f X := sorry

example {A B : Type} (f : A → B) (W X : Set A) :
    image f (W \ X) = image f W \ image f X := sorry

example {A B : Type} (f : A → B) (W X : Set A) :
    W ⊆ X ↔ image f W ⊆ image f X := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y ∩ Z) =
        inverse_image f Y ∩ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y ∪ Z) =
        inverse_image f Y ∪ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y \ Z) =
        inverse_image f Y \ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    Y ⊆ Z ↔ inverse_image f Y ⊆ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (X : Set A) :
    inverse_image f (image f X) = X := sorry

example {A B : Type} (f : A → B) (Y : Set B) :
    image f (inverse_image f Y) = Y := sorry

example {A : Type} (f : A → A) (C : Set A) :
    closed f C → image f C ⊆ C := sorry

example {A : Type} (f : A → A) (C : Set A) :
    image f C ⊆ C → C ⊆ inverse_image f C := sorry

example {A : Type} (f : A → A) (C : Set A) :
    C ⊆ inverse_image f C → closed f C := sorry

example {A B : Type} (f : A → B) (g : B → A) (Y : Set B)
    (h1 : f ∘ g = id) (h2 : g ∘ f = id) :
    inverse_image f Y = image g Y := sorry

-- ════════════════════════════════════════════════════════════════
-- Chapter 6: Mathematical Induction (46 exercises)
-- ════════════════════════════════════════════════════════════════

namespace HTPI.Exercises

/- Section 6.1 -/
-- 1.
theorem Like_Exercise_6_1_1 :
    ∀ (n : Nat), 2 * Sum i from 0 to n, i = n * (n + 1) := sorry

-- 2.
theorem Like_Exercise_6_1_4 :
    ∀ (n : Nat), Sum i from 0 to n, 2 * i + 1 = (n + 1) ^ 2 := sorry

-- 3.
theorem Exercise_6_1_9a : ∀ (n : Nat), 2 ∣ n ^ 2 + n := sorry

-- 4.
theorem Exercise_6_1_13 :
    ∀ (a b : Int) (n : Nat), (a - b) ∣ (a ^ n - b ^ n) := sorry

-- 5.
theorem Exercise_6_1_15 : ∀ n ≥ 10, 2 ^ n > n ^ 3 := sorry

-- 6.
lemma nonzero_is_successor :
    ∀ (n : Nat), n ≠ 0 → ∃ (m : Nat), n = m + 1 := sorry

-- 7.
theorem Exercise_6_1_16a1 :
    ∀ (n : Nat), nat_even n ∨ nat_odd n := sorry

-- 8.
--Hint:  You may find the lemma nonzero_is_successor
--from a previous exercise useful, as well as Nat.add_right_cancel.
theorem Exercise_6_1_16a2 :
    ∀ (n : Nat), ¬(nat_even n ∧ nat_odd n) := sorry

/- Section 6.2 -/
-- 1.
lemma Lemma_6_2_1_2 {A : Type} {R : BinRel A} {B : Set A} {b c : A}
    (h1 : partial_order R) (h2 : b ∈ B) (h3 : minimalElt R c (B \ {b}))
    (h4 : ¬R b c) : minimalElt R c B := sorry

-- 2.
lemma extendPO_is_ref {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : reflexive (extendPO R b) := sorry

-- 3.
lemma extendPO_is_trans {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : transitive (extendPO R b) := sorry

-- 4.
lemma extendPO_is_antisymm {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : antisymmetric (extendPO R b) := sorry

-- 5.
theorem Exercise_6_2_3 {A : Type} (R : BinRel A)
    (h : total_order R) : ∀ n ≥ 1, ∀ (B : Set A),
    numElts B n → ∃ (b : A), smallestElt R b B := sorry

-- 6.
--Hint:  First prove that R is reflexive
theorem Exercise_6_2_4a {A : Type} (R : BinRel A)
    (h : ∀ (x y : A), R x y ∨ R y x) : ∀ n ≥ 1, ∀ (B : Set A),
    numElts B n → ∃ x ∈ B, ∀ y ∈ B, ∃ (z : A), R x z ∧ R z y := sorry

-- 7.
theorem Like_Exercise_6_2_16 {A : Type} (f : A → A)
    (h : one_to_one f) : ∀ (n : Nat) (B : Set A), numElts B n →
    closed f B → ∀ y ∈ B, ∃ x ∈ B, f x = y := sorry

-- 8.
--Hint:  Use Exercise_6_2_2
theorem Example_6_2_2 {A : Type} (R : BinRel A)
    (h1 : ∃ (n : Nat), numElts {x : A | x = x} n)
    (h2 : partial_order R) : ∃ (T : BinRel A),
      total_order T ∧ ∀ (x y : A), R x y → T x y := sorry

/- Section 6.3 -/
-- 1.
theorem Exercise_6_3_4 : ∀ (n : Nat),
    3 * (Sum i from 0 to n, (2 * i + 1) ^ 2) =
    (n + 1) * (2 * n + 1) * (2 * n + 3) := sorry

-- 2.
theorem Exercise_6_3_7b (f : Nat → Real) (c : Real) : ∀ (n : Nat),
    Sum i from 0 to n, c * f i = c * Sum i from 0 to n, f i := sorry

-- 3.
theorem fact_pos : ∀ (n : Nat), fact n ≥ 1 := sorry

-- 4.
--Hint:  Use the theorem fact_pos from the previous exercise
theorem Exercise_6_3_13a (k : Nat) : ∀ (n : Nat),
    fact (k ^ 2 + n) ≥ k ^ (2 * n) := sorry

-- 5.
--Hint:  Use the theorem in the previous exercise.
--You may find it useful to first prove a lemma:
--∀ (k : Nat), 2 * k ^ 2 + 1 ≥ k
theorem Exercise_6_3_13b (k : Nat) : ∀ n ≥ 2 * k ^ 2,
    fact n ≥ k ^ n := sorry

-- 6.
def seq_6_3_15 (k : Nat) : Int :=
    match k with
      | 0 => 0
      | n + 1 => 2 * seq_6_3_15 n + n

theorem Exercise_6_3_15 : ∀ (n : Nat),
    seq_6_3_15 n = 2 ^ n - n - 1 := sorry

-- 7.
def seq_6_3_16 (k : Nat) : Nat :=
    match k with
      | 0 => 2
      | n + 1 => (seq_6_3_16 n) ^ 2

theorem Exercise_6_3_16 : ∀ (n : Nat),
    seq_6_3_16 n = ___ := sorry

/- Section 6.4 -/
-- 1.
--Hint: Use Exercise_6_1_16a1 and Exercise_6_1_16a2
lemma sq_even_iff_even (n : Nat) :
    nat_even (n * n) ↔ nat_even n := sorry

-- 2.
--This theorem proves that the square root of 6 is irrational
theorem Exercise_6_4_4a :
    ¬∃ (q p : Nat), p * p = 6 * (q * q) ∧ q ≠ 0 := sorry

-- 3.
theorem Exercise_6_4_5 :
    ∀ n ≥ 12, ∃ (a b : Nat), 3 * a + 7 * b = n := sorry

-- 4.
theorem Exercise_6_4_7a : ∀ (n : Nat),
    (Sum i from 0 to n, Fib i) + 1 = Fib (n + 2) := sorry

-- 5.
theorem Exercise_6_4_7c : ∀ (n : Nat),
    Sum i from 0 to n, Fib (2 * i + 1) = Fib (2 * n + 2) := sorry

-- 6.
theorem Exercise_6_4_8a : ∀ (m n : Nat),
    Fib (m + n + 1) = Fib m * Fib n + Fib (m + 1) * Fib (n + 1) := sorry

-- 7.
theorem Exercise_6_4_8d : ∀ (m k : Nat), Fib m ∣ Fib (m * k) := sorry

-- 8.
def Fib_like (n : Nat) : Nat :=
  match n with
    | 0 => 1
    | 1 => 2
    | k + 2 => 2 * (Fib_like k) + Fib_like (k + 1)

theorem Fib_like_formula : ∀ (n : Nat), Fib_like n = 2 ^ n := sorry

-- 9.
def triple_rec (n : Nat) : Nat :=
  match n with
    | 0 => 0
    | 1 => 2
    | 2 => 4
    | k + 3 => 4 * triple_rec k +
                6 * triple_rec (k + 1) + triple_rec (k + 2)

theorem triple_rec_formula :
    ∀ (n : Nat), triple_rec n = 2 ^ n * Fib n := sorry

-- 10.
lemma quot_rem_unique_lemma {m q r q' r' : Nat}
    (h1 : m * q + r = m * q' + r') (h2 : r' < m) : q ≤ q' := sorry

theorem quot_rem_unique (m q r q' r' : Nat)
    (h1 : m * q + r = m * q' + r') (h2 : r < m) (h3 : r' < m) :
    q = q' ∧ r = r' := sorry

-- 11.
theorem div_mod_char (m n q r : Nat)
    (h1 : n = m * q + r) (h2 : r < m) : q = n / m ∧ r = n % m := sorry

/- Section 6.5 -/
-- Definitions for next three exercises
def rep_image_family {A : Type}
    (F : Set (A → A)) (n : Nat) (B : Set A) : Set A :=
  match n with
    | 0 => B
    | k + 1 => {x : A | ∃ f ∈ F, x ∈ image f (rep_image_family F k B)}

def cumul_image_family {A : Type}
    (F : Set (A → A)) (B : Set A) : Set A :=
  {x : A | ∃ (n : Nat), x ∈ rep_image_family F n B}

def image2 {A : Type} (f : A → A → A) (B : Set A) : Set A :=
  {z : A | ∃ (x y : A), x ∈ B ∧ y ∈ B ∧ z = f x y}

def rep_image2 {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) : Set A :=
  match n with
    | 0 => B
    | k + 1 => image2 f (rep_image2 f k B)

def cumul_image2 {A : Type} (f : A → A → A) (B : Set A) : Set A :=
  {x : A | ∃ (n : Nat), x ∈ rep_image2 f n B}

def un_image2 {A : Type} (f : A → A → A) (B : Set A) : Set A :=
  B ∪ (image2 f B)

def rep_un_image2 {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) : Set A :=
  match n with
    | 0 => B
    | k + 1 => un_image2 f (rep_un_image2 f k B)

def cumul_un_image2 {A : Type}
    (f : A → A → A) (B : Set A) : Set A :=
  {x : A | ∃ (n : Nat), x ∈ rep_un_image2 f n B}

-- 1.
theorem rep_image_family_base {A : Type}
    (F : Set (A → A)) (B : Set A) : rep_image_family F 0 B = B := by rfl

theorem rep_image_family_step {A : Type}
    (F : Set (A → A)) (n : Nat) (B : Set A) :
    rep_image_family F (n + 1) B =
    {x : A | ∃ f ∈ F, x ∈ image f (rep_image_family F n B)} := by rfl

lemma rep_image_family_sub_closed {A : Type}
    (F : Set (A → A)) (B D : Set A)
    (h1 : B ⊆ D) (h2 : closed_family F D) :
    ∀ (n : Nat), rep_image_family F n B ⊆ D := sorry

theorem Exercise_6_5_3 {A : Type} (F : Set (A → A)) (B : Set A) :
    closure_family F B (cumul_image_family F B) := sorry

-- 2.
theorem rep_image2_base {A : Type} (f : A → A → A) (B : Set A) :
    rep_image2 f 0 B = B := by rfl

theorem rep_image2_step {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) :
    rep_image2 f (n + 1) B = image2 f (rep_image2 f n B) := by rfl

--You won't be able to complete this proof
theorem Exercise_6_5_6 {A : Type} (f : A → A → A) (B : Set A) :
    closed2 f (cumul_image2 f B) := sorry

-- 3.
theorem rep_un_image2_base {A : Type} (f : A → A → A) (B : Set A) :
    rep_un_image2 f 0 B = B := by rfl

theorem rep_un_image2_step {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) :
    rep_un_image2 f (n + 1) B =
    un_image2 f (rep_un_image2 f n B) := by rfl

theorem Exercise_6_5_8a {A : Type} (f : A → A → A) (B : Set A) :
    ∀ (m n : Nat), m ≤ n →
    rep_un_image2 f m B ⊆ rep_un_image2 f n B := sorry

lemma rep_un_image2_sub_closed {A : Type} {f : A → A → A} {B D : Set A}
    (h1 : B ⊆ D) (h2 : closed2 f D) :
    ∀ (n : Nat), rep_un_image2 f n B ⊆ D := sorry

lemma closed_lemma
    {A : Type} {f : A → A → A} {B : Set A} {x y : A} {nx ny n : Nat}
    (h1 : x ∈ rep_un_image2 f nx B) (h2 : y ∈ rep_un_image2 f ny B)
    (h3 : nx ≤ n) (h4 : ny ≤ n) :
    f x y ∈ cumul_un_image2 f B := sorry

theorem Exercise_6_5_8b {A : Type} (f : A → A → A) (B : Set A) :
    closure2 f B (cumul_un_image2 f B) := sorry

-- Definitions for next four exercises
def idExt (A : Type) : Set (A × A) := {(x, y) : A × A | x = y}

def rep_comp {A : Type} (R : Set (A × A)) (n : Nat) : Set (A × A) :=
  match n with
    | 0 => idExt A
    | k + 1 => comp (rep_comp R k) R

def cumul_comp {A : Type} (R : Set (A × A)) : Set (A × A) :=
  {(x, y) : A × A | ∃ n ≥ 1, (x, y) ∈ rep_comp R n}
-- 4.
theorem rep_comp_one {A : Type} (R : Set (A × A)) :
    rep_comp R 1 = R := sorry

-- 5.
theorem Exercise_6_5_11 {A : Type} (R : Set (A × A)) :
    ∀ (m n : Nat), rep_comp R (m + n) =
    comp (rep_comp R m) (rep_comp R n) := sorry

-- 6.
lemma rep_comp_sub_trans {A : Type} {R S : Set (A × A)}
    (h1 : R ⊆ S) (h2 : transitive (RelFromExt S)) :
    ∀ n ≥ 1, rep_comp R n ⊆ S := sorry

-- 7.
theorem Exercise_6_5_14 {A : Type} (R : Set (A × A)) :
    smallestElt (sub (A × A)) (cumul_comp R)
    {S : Set (A × A) | R ⊆ S ∧ transitive (RelFromExt S)} := sorry

-- ════════════════════════════════════════════════════════════════
-- Chapter 7: Number Theory (47 exercises)
-- ════════════════════════════════════════════════════════════════

namespace HTPI.Exercises

/- Section 7.1 -/
-- 1.
theorem dvd_a_of_dvd_b_mod {a b d : Nat}
    (h1 : d ∣ b) (h2 : d ∣ (a % b)) : d ∣ a := sorry

-- 2.
lemma gcd_comm_lt {a b : Nat} (h : a < b) : gcd a b = gcd b a := sorry

theorem gcd_comm (a b : Nat) : gcd a b = gcd b a := sorry

-- 3.
theorem Exercise_7_1_5 (a b : Nat) (n : Int) :
    (∃ (s t : Int), s * a + t * b = n) ↔ (↑(gcd a b) : Int) ∣ n := sorry

-- 4.
theorem Exercise_7_1_6 (a b c : Nat) :
    gcd a b = gcd (a + b * c) b := sorry

-- 5.
theorem gcd_is_nonzero {a b : Nat} (h : a ≠ 0 ∨ b ≠ 0) :
    gcd a b ≠ 0 := sorry

-- 6.
theorem gcd_greatest {a b d : Nat} (h1 : gcd a b ≠ 0)
    (h2 : d ∣ a) (h3 : d ∣ b) : d ≤ gcd a b := sorry

-- 7.
lemma Lemma_7_1_10a {a b : Nat}
    (n : Nat) (h : a ∣ b) : (n * a) ∣ (n * b) := sorry

lemma Lemma_7_1_10b {a b n : Nat}
    (h1 : n ≠ 0) (h2 : (n * a) ∣ (n * b)) : a ∣ b := sorry

lemma Lemma_7_1_10c {a b : Nat}
    (h1 : a ∣ b) (h2 : b ∣ a) : a = b := sorry

theorem Exercise_7_1_10 (a b n : Nat) :
    gcd (n * a) (n * b) = n * gcd a b := sorry

/- Section 7.2 -/
-- 1.
lemma dvd_prime {a p : Nat}
    (h1 : prime p) (h2 : a ∣ p) : a = 1 ∨ a = p := sorry

-- 2.
-- Hints:  Start with apply List.rec.  You may find mul_ne_zero useful
theorem prod_nonzero_nonzero : ∀ (l : List Nat),
    (∀ a ∈ l, a ≠ 0) → prod l ≠ 0 := sorry

-- 3.
theorem rel_prime_iff_no_common_factor (a b : Nat) :
    rel_prime a b ↔ ¬∃ (p : Nat), prime p ∧ p ∣ a ∧ p ∣ b := sorry

-- 4.
theorem rel_prime_symm {a b : Nat} (h : rel_prime a b) :
    rel_prime b a := sorry

-- 5.
lemma in_prime_factorization_iff_prime_factor {a : Nat} {l : List Nat}
    (h1 : prime_factorization a l) (p : Nat) :
    p ∈ l ↔ prime_factor p a := sorry

-- 6.
theorem Exercise_7_2_5 {a b : Nat} {l m : List Nat}
    (h1 : prime_factorization a l) (h2 : prime_factorization b m) :
    rel_prime a b ↔ (¬∃ (p : Nat), p ∈ l ∧ p ∈ m) := sorry

-- 7.
theorem Exercise_7_2_6 (a b : Nat) :
    rel_prime a b ↔ ∃ (s t : Int), s * a + t * b = 1 := sorry

-- 8.
theorem Exercise_7_2_7 {a b a' b' : Nat}
    (h1 : rel_prime a b) (h2 : a' ∣ a) (h3 : b' ∣ b) :
    rel_prime a' b' := sorry

-- 9.
theorem Exercise_7_2_9 {a b j k : Nat}
    (h1 : gcd a b ≠ 0) (h2 : a = j * gcd a b) (h3 : b = k * gcd a b) :
    rel_prime j k := sorry

-- 10.
theorem Exercise_7_2_17a (a b c : Nat) :
    gcd a (b * c) ∣ gcd a b * gcd a c := sorry

/- Section 7.3 -/
-- 1.
theorem congr_trans {m : Nat} : ∀ {a b c : Int},
    a ≡ b (MOD m) → b ≡ c (MOD m) → a ≡ c (MOD m) := sorry

-- 2.
theorem Theorem_7_3_6_3 {m : Nat} (X : ZMod m) : X + [0]_m = X := sorry

-- 3.
theorem Theorem_7_3_6_4 {m : Nat} (X : ZMod m) :
    ∃ (Y : ZMod m), X + Y = [0]_m := sorry

-- 4.
theorem Exercise_7_3_4a {m : Nat} (Z1 Z2 : ZMod m)
    (h1 : ∀ (X : ZMod m), X + Z1 = X)
    (h2 : ∀ (X : ZMod m), X + Z2 = X) : Z1 = Z2 := sorry

-- 5.
theorem Exercise_7_3_4b {m : Nat} (X Y1 Y2 : ZMod m)
    (h1 : X + Y1 = [0]_m) (h2 : X + Y2 = [0]_m) : Y1 = Y2 := sorry

-- 6.
theorem Theorem_7_3_10 (m a : Nat) (b : Int) :
    ¬(↑(gcd m a) : Int) ∣ b → ¬∃ (x : Int), a * x ≡ b (MOD m) := sorry

-- 7.
theorem Theorem_7_3_11 (m n : Nat) (a b : Int) (h1 : n ≠ 0) :
    n * a ≡ n * b (MOD n * m) ↔ a ≡ b (MOD m) := sorry

-- 8.
theorem Exercise_7_3_16 {m : Nat} {a b : Int} (h : a ≡ b (MOD m)) :
    ∀ (n : Nat), a ^ n ≡ b ^ n (MOD m) := sorry

-- 9.
example {m : Nat} [NeZero m] (X : ZMod m) :
    ∃! (a : Int), 0 ≤ a ∧ a < m ∧ X = [a]_m := sorry

-- 10.
theorem congr_rel_prime {m a b : Nat} (h1 : a ≡ b (MOD m)) :
    rel_prime m a ↔ rel_prime m b := sorry

-- 11.
--Hint: You may find the theorem Int.ofNat_mod_ofNat useful.
theorem rel_prime_mod (m a : Nat) :
    rel_prime m (a % m) ↔ rel_prime m a := sorry

-- 12.
lemma congr_iff_mod_eq_Int (m : Nat) (a b : Int) [NeZero m] :
    a ≡ b (MOD m) ↔ a % ↑m = b % ↑m := sorry

--Hint for next theorem: Use the lemma above,
--together with the theorems Int.ofNat_mod_ofNat and Nat.cast_inj.
theorem congr_iff_mod_eq_Nat (m a b : Nat) [NeZero m] :
    ↑a ≡ ↑b (MOD m) ↔ a % m = b % m := sorry

/- Section 7.4 -/
-- 1.
--Hint:  Use induction.
--For the base case, compute [a]_m ^ 0 * [1]_m in two ways:
--by Theorem_7_3_6_7, [a] ^ 0 * [1]_m = [a]_m ^ 0
--by ring, [a]_m ^ 0 * [1]_m = [1]_m.
lemma Exercise_7_4_5_Int (m : Nat) (a : Int) :
    ∀ (n : Nat), [a]_m ^ n = [a ^ n]_m := sorry

-- 2.
lemma left_inv_one_one_below {n : Nat} {g g' : Nat → Nat}
    (h1 : ∀ i < n, g' (g i) = i) : one_one_below n g := sorry

-- 3.
lemma comp_perm_below {n : Nat} {f g : Nat → Nat}
    (h1 : perm_below n f) (h2 : perm_below n g) :
    perm_below n (f ∘ g) := sorry

-- 4.
lemma perm_below_fixed {n : Nat} {g : Nat → Nat}
    (h1 : perm_below (n + 1) g) (h2 : g n = n) : perm_below n g := sorry

-- 5.
lemma Lemma_7_4_6 {a b c : Nat} :
    rel_prime (a * b) c ↔ rel_prime a c ∧ rel_prime b c := sorry

-- 6.
example {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    a ^ (phi m + 1) ≡ a (MOD m) := sorry

-- 7.
theorem Like_Exercise_7_4_11 {m a p : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : p + 1 = phi m) :
    [a]_m * [a ^ p]_m = [1]_m := sorry

-- 8.
theorem Like_Exercise_7_4_12 {m a p q k : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : p = q + (phi m) * k) :
    a ^ p ≡ a ^ q (MOD m) := sorry

/- Section 7.5 -/
-- 1.
--Hint:  Use induction.
lemma num_rp_prime {p : Nat} (h1 : prime p) :
    ∀ k < p, num_rp_below p (k + 1) = k := sorry

-- 2.
lemma three_prime : prime 3 := sorry

-- 3.
--Hint:  Use the previous exercise, Exercise_7_2_7, and Theorem_7_4_2.
theorem Exercise_7_5_13a (a : Nat) (h1 : rel_prime 561 a) :
    a ^ 560 ≡ 1 (MOD 3) := sorry

-- 4.
--Hint:  Imitate the way Theorem_7_2_2_Int was proven from Theorem_7_2_2.
lemma Theorem_7_2_3_Int {p : Nat} {a b : Int}
    (h1 : prime p) (h2 : ↑p ∣ a * b) : ↑p ∣ a ∨ ↑p ∣ b := sorry

-- 5.
--Hint:  Use the previous exercise.
theorem Exercise_7_5_14b (n : Nat) (b : Int)
    (h1 : prime n) (h2 : b ^ 2 ≡ 1 (MOD n)) :
    b ≡ 1 (MOD n) ∨ b ≡ -1 (MOD n) := sorry

-- ════════════════════════════════════════════════════════════════
-- Chapter 8: Infinite Sets (59 exercises)
-- ════════════════════════════════════════════════════════════════

namespace HTPI.Exercises

open Classical

/- Section 8.1 -/
-- 1.
--Hint:  Use Exercise_6_1_16a2 from the exercises of Section 6.1
lemma fnz_odd (k : Nat) : fnz (2 * k + 1) = -↑(k + 1) := sorry

-- 2.
lemma fnz_fzn : fnz ∘ fzn = id  := sorry

-- 3.
lemma tri_step (k : Nat) : tri (k + 1) = tri k + k + 1 := sorry

-- 4.
lemma tri_incr {j k : Nat} (h1 : j ≤ k) : tri j ≤ tri k := sorry

-- 5.
example {U V : Type} (f : U → V) : range f = Ran (graph f) := sorry

-- 6.
lemma onto_iff_range_eq_univ {U V : Type} (f : U → V) :
    onto f ↔ range f = Univ V := sorry

-- 7.
-- Don't use ctble_iff_set_nat_equinum to prove this lemma
lemma ctble_of_ctble_equinum {U V : Type}
    (h1 : U ∼ V) (h2 : ctble U) : ctble V := sorry

-- 8.
theorem Exercise_8_1_1_b : denum {n : Int | even n} := sorry

-- 9.
theorem equinum_iff_inverse_pair (U V : Type) :
    U ∼ V ↔ ∃ (f : U → V) (g : V → U), f ∘ g = id ∧ g ∘ f = id := sorry

-- 10.
lemma image_comp_id {U V : Type} {f : U → V} {g : V → U}
    (h : g ∘ f = id) : (image g) ∘ (image f) = id := sorry

-- 11.
theorem Exercise_8_1_5_1 {U V : Type}
    (h : U ∼ V) : Set U ∼ Set V := sorry

-- Definition for next three exercises
def val_image {U : Type} (A : Set U) (X : Set A) : Set U :=
  {y : U | ∃ x ∈ X, x.val = y}

-- 12.
lemma subset_of_val_image_eq {U : Type} {A : Set U} {X1 X2 : Set A}
    (h : val_image A X1 = val_image A X2) : X1 ⊆ X2 := sorry

-- 13.
lemma val_image_one_one {U : Type} (A : Set U) :
    one_to_one (val_image A) := sorry

-- 14.
lemma range_val_image {U : Type} (A : Set U) :
    range (val_image A) = 𝒫 A := sorry

-- 15.
lemma Set_equinum_powerset {U : Type} (A : Set U) :
    Set A ∼ 𝒫 A := sorry

-- 16.
--Hint:  Use Exercise_8_1_5_1 and Set_equinum_powerset.
theorem Exercise_8_1_5_2 {U V : Type} {A : Set U} {B : Set V}
    (h : A ∼ B) : 𝒫 A ∼ 𝒫 B := sorry

-- 17.
example (U V : Type) (A : Set U) (f : A → V) (v : V) :
    func_restrict (func_extend f v) A = f := sorry

-- 18.
theorem Theorem_8_1_5_3_type {U : Type} :
    ctble U ↔ ∃ (f : U → Nat), one_to_one f := sorry

-- 19.
theorem ctble_set_of_ctble_type {U : Type}
    (h : ctble U) (A : Set U) : ctble A := sorry

-- 20.
theorem Exercise_8_1_17 {U : Type} {A B : Set U}
    (h1 : B ⊆ A) (h2 : ctble A) : ctble B := sorry

/- Section 8.1½ -/
-- 1.
lemma image_empty {U : Type} {A : Set U}
    (f : U → Nat) (h : empty A) : image f A = I 0 := sorry

-- 2.
lemma remove_one_equinum
    {U V : Type} {A : Set U} {B : Set V} {a : U} {b : V} {f : U → V}
    (h1 : one_one_on f A) (h2 : image f A = B)
    (h3 : a ∈ A) (h4 : f a = b) : ↑(A \ {a}) ∼ ↑(B \ {b}) := sorry

-- 3.
lemma singleton_of_diff_empty {U : Type} {A : Set U} {a : U}
    (h1 : a ∈ A) (h2 : empty (A \ {a})) : A = {a} := sorry

-- 4.
lemma eq_zero_of_I_zero_equinum {n : Nat} (h : I 0 ∼ I n) : n = 0 := sorry

-- 5.
--Hint: use mathematical induction
theorem Exercise_8_1_6a : ∀ ⦃m n : Nat⦄, (I m ∼ I n) → m = n := sorry

-- 6.
theorem Exercise_8_1_6b {U : Type} {A : Set U} {m n : Nat}
    (h1 : numElts A m) (h2 : numElts A n) : m = n := sorry

-- 7.
lemma neb_nrpb (m : Nat) : ∀ ⦃k : Nat⦄, k ≤ m →
    num_elts_below (set_rp_below m) k = num_rp_below m k := sorry

-- 8.
--Hint:  You might find it helpful to apply the theorem div_mod_char
--from the exercises of Section 6.4.
lemma qr_image (m n : Nat) :
    image (qr n) (I (m * n)) = I m ×ₛ I n := sorry

-- Definitions for next two exercises
lemma is_elt_snd_of_not_fst {U : Type} {A C : Set U} {x : U}
    (h1 : x ∈ A ∪ C) (h2 : x ∉ A) : x ∈ C := by
  disj_syll h1 h2
  show x ∈ C from h1
  done

def elt_snd_of_not_fst {U : Type} {A C : Set U} {x : ↑(A ∪ C)}
  (h : x.val ∉ A) : C :=
  Subtype_elt (is_elt_snd_of_not_fst x.property h)

noncomputable def func_union {U V : Type} {A C : Set U}
  (f : A → V) (g : C → V) (x : ↑(A ∪ C)) : V :=
  if test : x.val ∈ A then f (Subtype_elt test)
    else g (elt_snd_of_not_fst test)

-- 9.
lemma func_union_one_one {U V : Type} {A C : Set U}
    {f : A → V} {g : C → V} (h1 : empty (range f ∩ range g))
    (h2 : one_to_one f) (h3 : one_to_one g) :
    one_to_one (func_union f g) := sorry

-- 10.
lemma func_union_range {U V : Type} {A C : Set U}
    (f : A → V) (g : C → V) (h : empty (A ∩ C)) :
    range (func_union f g) = range f ∪ range g := sorry

-- 11.
--Hint:  Use the last two exercises.
theorem Theorem_8_1_2_2
    {U V : Type} {A C : Set U} {B D : Set V}
    (h1 : empty (A ∩ C)) (h2 : empty (B ∩ D))
    (h3 : A ∼ B) (h4 : C ∼ D) : ↑(A ∪ C) ∼ ↑(B ∪ D) := sorry

-- 12.
lemma shift_I_equinum (n m : Nat) : I m ∼ ↑(I (n + m) \ I n) := sorry

-- 13.
theorem Theorem_8_1_7 {U : Type} {A B : Set U} {n m : Nat}
    (h1 : empty (A ∩ B)) (h2 : numElts A n) (h3 : numElts B m) :
    numElts (A ∪ B) (n + m) := sorry

-- 14.
theorem equinum_sub {U V : Type} {A C : Set U} {B : Set V}
    (h1 : A ∼ B) (h2 : C ⊆ A) : ∃ (D : Set V), D ⊆ B ∧ C ∼ D := sorry

-- 15.
theorem Exercise_8_1_8b {U : Type} {A B : Set U}
    (h1 : finite A) (h2 : B ⊆ A) : finite B := sorry

-- 16.
theorem finite_bdd {A : Set Nat} (h : finite A) :
    ∃ (m : Nat), ∀ n ∈ A, n < m := sorry

-- 17.
lemma N_not_finite : ¬finite Nat := sorry

-- 18.
theorem denum_not_finite (U : Type)
    (h : denum U) : ¬finite U := sorry

-- 19.
--Hint:  Use Like_Exercise_6_2_16 from the exercises of Section 6.2.
theorem Exercise_6_2_16 {U : Type} {f : U → U}
    (h1 : one_to_one f) (h2 : finite U) : onto f := sorry

/- Section 8.2 -/
-- 1.
lemma pair_ctble {U : Type}
    (a b : U) : ctble ↑({a, b} : Set U) := sorry

-- 2.
--Hint:  Use the previous exercise and Theorem_8_2_2
theorem Theorem_8_2_1_2 {U : Type} {A B : Set U}
    (h1 : ctble A) (h2 : ctble B) : ctble ↑(A ∪ B) := sorry

-- 3.
lemma remove_empty_union_eq {U : Type} (F : Set (Set U)) :
    ⋃₀ {A : Set U | A ∈ F ∧ ¬empty A} = ⋃₀ F := sorry

-- 4.
lemma seq_cons_image {U : Type} (A : Set U) (n : Nat) :
    image (seq_cons U) (A ×ₛ (seq_by_length A n)) =
      seq_by_length A (n + 1) := sorry

-- 5.
--Hint:  Apply Theorem_8_2_4 to the set Univ U
theorem Theorem_8_2_4_type {U : Type}
    (h : ctble U) : ctble (List U) := sorry

-- 6.
def list_to_set (U : Type) (l : List U) : Set U := {x : U | x ∈ l}

lemma list_to_set_def (U : Type) (l : List U) (x : U) :
    x ∈ list_to_set U l ↔ x ∈ l := by rfl

--Hint:  Use induction on the size of A
lemma set_from_list {U : Type} {A : Set U} (h : finite A) :
    ∃ (l : List U), list_to_set U l = A := sorry

-- 7.
--Hint:  Use the previous exercise and Theorem_8_2_4_type
theorem Like_Exercise_8_2_4 (U : Type) (h : ctble U) :
    ctble {X : Set U | finite X} := sorry

-- 8.
theorem Exercise_8_2_6b (U V W : Type) :
     ((U × V) → W) ∼ (U → V → W) := sorry

-- 9.
theorem Like_Exercise_8_2_7 : ∃ (P : Set (Set Nat)),
    partition P ∧ denum P ∧ ∀ X ∈ P, denum X := sorry

-- 10.
theorem unctbly_many_inf_set_nat :
    ¬ctble {X : Set Nat | ¬finite X} := sorry

-- 11.
theorem Exercise_8_2_8 {U : Type} {A B : Set U}
    (h : empty (A ∩ B)) : 𝒫 (A ∪ B) ∼ 𝒫 A ×ₛ 𝒫 B := sorry

/- Section 8.3 -/
-- 1.
lemma csb_func_graph_not_X {U V : Type} {X : Set U} {x : U}
    (f : U → V) (g : V → U) (h : x ∉ X) (y : V) :
    (x, y) ∈ csb_func_graph f g X ↔ g y = x := sorry

-- 2.
theorem intervals_equinum :
    {x : Real | 0 < x ∧ x < 1} ∼ {x : Real | 0 < x ∧ x ≤ 1} := sorry

-- 3.
--Hint for proof:  First show that `extension R = extension S`, and then use the fact
--that `R` and `S` can be determined from `extension R` and `extension S` (see Section 4.3).
theorem relext {U V : Type} {R S : Rel U V}
    (h : ∀ (u : U) (v : V), R u v ↔ S u v) : R = S := sorry

-- Definitions for next six exercises
def EqRel (U : Type) : Set (BinRel U) :=
  {R : BinRel U | equiv_rel R}

def Part (U : Type) : Set (Set (Set U)) :=
  {P : Set (Set U) | partition P}

def EqRelExt (U : Type) : Set (Set (U × U)) :=
  {E : Set (U × U) | ∃ (R : BinRel U), equiv_rel R ∧ extension R = E}

def shift_and_zero (X : Set Nat) : Set Nat :=
  {x + 2 | x ∈ X} ∪ {0}

def shift_and_zero_comp (X : Set Nat) : Set Nat :=
  {n : Nat | n ∉ shift_and_zero X}

def saz_pair (X : Set Nat) : Set (Set Nat) :=
  {shift_and_zero X, shift_and_zero_comp X}

-- 4.
theorem EqRel_equinum_Part (U : Type) : EqRel U ∼ Part U := sorry

-- 5.
theorem EqRel_equinum_EqRelExt (U : Type) :
    EqRel U ∼ EqRelExt U := sorry

-- 6.
theorem EqRel_Nat_to_Set_Nat :
    ∃ (f : EqRel Nat → Set Nat), one_to_one f := sorry

-- 7.
theorem saz_pair_part (X : Set Nat) : saz_pair X ∈ Part Nat := sorry

-- 8.
theorem Set_Nat_to_EqRel_Nat :
    ∃ (f : Set Nat → EqRel Nat), one_to_one f := sorry

-- 9.
theorem EqRel_Nat_equinum_Set_Nat : EqRel Nat ∼ Set Nat := sorry

