Set Implicit Arguments.

Require Import Arith_base List.

(** Type definitions *)

Section TY.
  Inductive Ty : Set :=
    | Unit  : Ty
    | Arrow : Ty -> Ty -> Ty. 
End TY.

(* Contexts *)

Section CON.
  Definition Con := list Ty.

  (* variables are context membership evidence *)
  
  Inductive Member : Ty -> Con -> Prop :=
    | here  : forall c t, Member t (t :: c)
    | there : forall c t t', Member t c -> Member t (t' :: c).
End CON.

(* Terms *)

Section TERMS.
  Inductive Term c : Ty -> Type :=
    | Const : forall t, Term c t
    | Var   : forall t, Member t c -> Term c t
    | App   : forall t t', Term c (Arrow t t') -> Term c t -> Term c t'
    | Lam   : forall t t', Term (t :: c) t' -> Term c (Arrow t t').
End TERMS.

(* Normal forms for beta e eta reduction *)

Section NF.
  
  Inductive Nf : Con -> Ty -> Type :=
    | Nf_lam : forall c t t', Nf (t :: c) t' -> Nf c (Arrow t t')
    | Nf_Ne  : forall c t (x : Member t c) (ts : Sp c t Unit), Nf c Unit
  with 
    Sp : Con -> Ty -> Ty -> Type :=
      | Spe : forall c t, Sp c t t
      | Spx : forall c t t' t'', Nf c t -> Sp c t' t'' -> Sp c (Arrow t t') t''.

  (* here we will need to create a induction principle to Nf. *)

  Scheme Nf_ind_mut := Induction for Nf Sort Prop
  with   Sp_ind_mut := Induction for Sp Sort Prop.
End NF.

(* Beta eta equivalence between terms *)

Section BETAETA.

  Definition type_of {c ty} (t : Term c ty) : Ty := ty.
  Definition context_of {c ty} (t : Term c ty) : Con := c.

  Inductive BetaEtaEquiv : forall (c : Con) (ty : Ty), Term c ty -> Term c ty -> Prop :=
    | brefl : forall c ty (t : Term c ty) , BetaEtaEquiv t t
    | bsym  : forall c ty (t t' : Term c ty), BetaEtaEquiv t t' -> 
                                              BetaEtaEquiv t' t
    | btrans : forall c ty (t t' t'' : Term c ty), BetaEtaEquiv t t'   -> 
                                                   BetaEtaEquiv t' t'' -> 
                                                   BetaEtaEquiv t t''
    | blcong : forall c ty ty' (t t' : Term (ty' :: c) ty), 
                  BetaEtaEquiv t t' -> 
                  BetaEtaEquiv (Lam t) (Lam t')
    | bcapp : forall c ty' ty (t u : Term c (Arrow ty ty'))
                              (t' u' : Term c ty), 
                              BetaEtaEquiv t u   ->
                              BetaEtaEquiv t' u' ->
                              BetaEtaEquiv (App t t') (App u u').

End BETAETA.

(* Substitutions *)

