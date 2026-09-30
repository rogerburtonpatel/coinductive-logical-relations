(** * REC typing with positive [unfold]

    The syntax, reduction and typing of REC come from plst
    ([plst/rocq/rec]).  The only change to plst's typing is a side
    condition on [t_unfold]: the recursive type being eliminated must be
    positive in its bound variable.  Introduction ([t_fold]) needs no side
    condition. *)

From plst Require Export rec.typing.
Import rec.typing.Notations.

(** ** Positivity *)

(** [occurs i A]: the type variable [i] occurs free in [A]. *)
Fixpoint occurs {n} (i : fin n) (A : Ty n) : bool :=
  match A with
  | var_Ty j => fin_eqb j i
  | Void | Unit | Nat => false
  | Prod A1 A2 | Sum A1 A2 | Arr A1 A2 => occurs i A1 || occurs i A2
  | Mu A1 => occurs (shift i) A1
  end.

(** [pos i A]: [i] occurs only strictly positively in [A], i.e. never in the
    domain of an arrow. *)
Inductive pos {n} (i : fin n) : Ty n -> Prop :=
  | pos_var j : pos i (var_Ty j)
  | pos_void : pos i Void
  | pos_unit : pos i Unit
  | pos_nat : pos i Nat
  | pos_prod A1 A2 : pos i A1 -> pos i A2 -> pos i (Prod A1 A2)
  | pos_sum A1 A2 : pos i A1 -> pos i A2 -> pos i (Sum A1 A2)
  | pos_arr A1 A2 : occurs i A1 = false -> pos i A2 -> pos i (Arr A1 A2)
  | pos_mu A : @pos (S n) (shift i) A -> pos i (Mu A).

(** One-step unfolding of a recursive type: [unroll A = A[(Mu A)..]]. *)
Definition unroll (A : Ty 1) : Ty 0 := subst_Ty (scons (Mu A) var_Ty) A.

(** ** Typing (plst's, plus [pos] at [unfold]) *)

Inductive ptyping_val {n} (Γ : Ctx n) : Val n -> Ty 0 -> Prop :=
  | pt_var x :
    ptyping_val Γ (var x) (Γ x)
  | pt_zero :
    ptyping_val Γ zero Nat
  | pt_succ k :
    ptyping_val Γ k Nat ->
    ptyping_val Γ (succ k) Nat
  | pt_prod v1 v2 τ1 τ2 :
    ptyping_val Γ v1 τ1 ->
    ptyping_val Γ v2 τ2 ->
    ptyping_val Γ (prod v1 v2) (Prod τ1 τ2)
  | pt_inl v τ1 τ2 :
    ptyping_val Γ v τ1 ->
    ptyping_val Γ (inj true v) (Sum τ1 τ2)
  | pt_inr v τ1 τ2 :
    ptyping_val Γ v τ2 ->
    ptyping_val Γ (inj false v) (Sum τ1 τ2)
  | pt_abs e τ1 τ2 :
    ptyping (τ1 .: Γ) e τ2 ->
    ptyping_val Γ (abs e) (Arr τ1 τ2)
  | pt_rec v τ :
    allows_rec_ty τ = true ->
    ptyping_val (τ .: Γ) v τ ->
    ptyping_val Γ (rec v) τ
  | pt_fold v τ :
    ptyping_val Γ v (unroll τ) ->
    ptyping_val Γ (fold v) (Mu τ)
  | pt_unit :
    ptyping_val Γ unit Unit

with ptyping {n} (Γ : Ctx n) : Tm n -> Ty 0 -> Prop :=
  | pt_ret v τ :
    ptyping_val Γ v τ ->
    ptyping Γ (ret v) τ
  | pt_let e1 e2 τ1 τ2 :
    ptyping Γ e1 τ1 ->
    ptyping (τ1 .: Γ) e2 τ2 ->
    ptyping Γ (let_ e1 e2) τ2
  | pt_app v1 v2 τ1 τ2 :
    ptyping_val Γ v1 (Arr τ1 τ2) ->
    ptyping_val Γ v2 τ1 ->
    ptyping Γ (app v1 v2) τ2
  | pt_ifz v e0 e1 τ :
    ptyping_val Γ v Nat ->
    ptyping Γ e0 τ ->
    ptyping (Nat .: Γ) e1 τ ->
    ptyping Γ (ifz v e0 e1) τ
  | pt_prj1 v τ1 τ2 :
    ptyping_val Γ v (Prod τ1 τ2) ->
    ptyping Γ (prj true v) τ1
  | pt_prj2 v τ1 τ2 :
    ptyping_val Γ v (Prod τ1 τ2) ->
    ptyping Γ (prj false v) τ2
  | pt_case v e1 e2 τ1 τ2 τ :
    ptyping_val Γ v (Sum τ1 τ2) ->
    ptyping (τ1 .: Γ) e1 τ ->
    ptyping (τ2 .: Γ) e2 τ ->
    ptyping Γ (case v e1 e2) τ
  | pt_unfold v τ :
    pos var_zero τ ->
    ptyping_val Γ v (Mu τ) ->
    ptyping Γ (unfold v) (unroll τ).

Scheme ptyping_val_ind' := Induction for ptyping_val Sort Prop
  with ptyping_ind' := Induction for ptyping Sort Prop.
Combined Scheme ptyping_mutind from ptyping_val_ind', ptyping_ind'.

(** A program is safe if it never gets stuck (plst's [rec.steps.safe]). *)
Definition safe (e : Tm 0) : Prop :=
  forall e', e ~>* e' -> irreducible e' -> exists v, e' = ret v.

Definition reducible (e : Tm 0) : Prop := exists e', e ~> e'.
