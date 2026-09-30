(** * A unary logical relation for REC, without step indices

    Semantic type safety for plst's REC (fine-grained CBV with [rec] and
    iso-recursive types), in the style of [plst/rocq/rec/steps.v] but with
    no natural-number step indices:

    - Stages are elements of the clock tower ([Clock]); [x ⊏ y] plays the
      role of [j < k] and [Stage_loeb] (tower induction) the role of Löb
      induction.  It is used for [rec].
    - The computation relation [Cr Q] is a greatest fixed point (in the
      lattice of stage-indexed predicates) of the "one more step" functional:
      a term is good if, when irreducible, it is [ret v] with [v] good, and
      each step leads to a term good at all strictly earlier stages.
    - At [Mu], the value relation is the greatest fixed point of the
      upward closure of the unfolding transformer.  The upward closure makes
      it monotone for every type, so [gfp] exists and [fold] (and
      coinduction) hold for every type; [unfold] needs the recursive
      variable to be positive, which is why [pt_unfold] requires [pos]. *)

From CLR Require Export Clock PosTyping.
Import rec.typing.Notations.

(** ** Stage-indexed predicates *)

Definition VRel := Stage -> Val 0 -> Prop.
Definition CRel := Stage -> Tm 0 -> Prop.

(** Predicates we use are closed under going to earlier stages. *)
Definition smono (M : VRel) : Prop :=
  forall x y : Stage, x ⊑ y -> forall v, M x v -> M y v.

(** ** Computations *)

Program Definition Cstep (Q : VRel) : mon CRel :=
  {| body Z x e :=
       (irreducible e -> exists v, e = ret v /\ Q x v) /\
       (forall e', e ~> e' -> forall y : Stage, x ⊏ y -> Z y e') |}.
Next Obligation.
  intros Z Z' H x e [H1 H2]. split; [exact H1|].
  intros e' S y Hy. apply H, (H2 e' S y Hy).
Qed.

Definition Cr (Q : VRel) : CRel := gfp (Cstep Q).

Lemma Cr_unfold Q x e : Cr Q x e -> Cstep Q (Cr Q) x e.
Proof.
  exact (gfp_pfp (Cstep Q) x e).
Qed.

Lemma Cr_fold Q x e : Cstep Q (Cr Q) x e -> Cr Q x e.
Proof.
  exact (pfp_gfp (Cstep Q) x e).
Qed.

Lemma Cr_leq Q Q' : Q <= Q' -> Cr Q <= Cr Q'.
Proof.
  intros H. unfold Cr. apply gfp_leq.
  intros Z x e [H1 H2]. split; [|exact H2].
  intros Hi. destruct (H1 Hi) as [v [-> Hv]]. exists v. split; [reflexivity|].
  apply H, Hv.
Qed.

Lemma Cr_weq Q Q' : Q == Q' -> Cr Q == Cr Q'.
Proof.
  intros H. apply weq_spec in H as [H1 H2].
  apply antisym; apply Cr_leq; assumption.
Qed.

Lemma Cr_smono Q : smono Q ->
  forall x y : Stage, x ⊑ y -> forall e, Cr Q x e -> Cr Q y e.
Proof.
  intros HQ x y Hxy e He.
  assert (Hc : (fun y e => exists x : Stage, x ⊑ y /\ Cr Q x e) <= Cr Q).
  { apply leq_gfp. intros y' e' [x' [Hxy' He']].
    apply Cr_unfold in He' as [H1 H2]. split.
    - intros Hi. destruct (H1 Hi) as [v [-> Hv]]. exists v. split; [reflexivity|].
      exact (HQ _ _ Hxy' v Hv).
    - intros e'' S z Hz. exists z. split; [reflexivity|].
      apply (H2 e'' S z). exact (Stage_later_trans_l _ _ _ Hxy' Hz). }
  apply Hc. exists x. split; assumption.
Qed.

Lemma Cr_ret Q x v : Q x v -> Cr Q x (ret v).
Proof.
  intros Hv. apply Cr_fold. split.
  - intros _. exists v. split; [reflexivity|exact Hv].
  - intros e' S. inversion S.
Qed.

(** Backwards closure: one step buys one stage. *)
Lemma Cr_step Q x e e' :
  e ~> e' -> (forall y : Stage, x ⊏ y -> Cr Q y e') -> Cr Q x e.
Proof.
  intros S H. apply Cr_fold. split.
  - intros Hi. exfalso. exact (Hi e' S).
  - intros e'' S' y Hy. rewrite (deterministic _ _ _ S' S). apply H, Hy.
Qed.

(** Sequencing. Proved by Löb induction over the stage. *)
Lemma Cr_bind Q1 Q2 x e1 e2 : smono Q1 ->
  Cr Q1 x e1 ->
  (forall y : Stage, x ⊑ y -> forall v, Q1 y v -> Cr Q2 y (e2 [v..])) ->
  Cr Q2 x (let_ e1 e2).
Proof.
  intros HQ1. revert x e1.
  apply (Stage_loeb (fun x => forall e1, Cr Q1 x e1 ->
    (forall y : Stage, x ⊑ y -> forall v, Q1 y v -> Cr Q2 y (e2 [v..])) ->
    Cr Q2 x (let_ e1 e2))).
  intros x IH e1 He1 K.
  apply Cr_unfold in He1 as [H1 H2].
  destruct (canstep e1) as [[e1' S]|Hi].
  - apply (Cr_step _ _ _ (let_ e1' e2)); [apply Small.s_let_cong, S|].
    intros y Hy. apply IH; [exact Hy|apply (H2 e1' S y Hy)|].
    intros z Hz v Hv. apply K; [|exact Hv].
    etransitivity; [apply Stage_later_leq, Hy|exact Hz].
  - destruct (H1 Hi) as [v [-> Hv]].
    apply (Cr_step _ _ _ (e2 [v..])); [apply Small.s_letv|].
    intros y Hy. apply K; [apply Stage_later_leq, Hy|].
    exact (HQ1 _ _ (Stage_later_leq _ _ Hy) v Hv).
Qed.

(** Adequacy: a term that is good at every stage is safe. *)
Lemma Cr_safe Q e : (forall x, Cr Q x e) -> safe e.
Proof.
  intros H e' Hs Hi.
  assert (Hk : forall k, Cr Q (stage k) e) by (intros; apply H).
  clear H. revert Hk. induction Hs as [e0|e1 e2 e3 St Hs IH]; intros Hk.
  - destruct (Cr_unfold _ _ _ (Hk 0)) as [H1 _].
    destruct (H1 Hi) as [v [-> _]]. eauto.
  - apply IH; [exact Hi|]. intros k.
    destruct (Cr_unfold _ _ _ (Hk (S k))) as [_ H2].
    apply (H2 e2 St (stage k)), stage_later.
Qed.

(** ** Recursive types *)

(** Upward closure of the unfolding transformer [F].  The witness [M'] is
    required to be [smono] so that [gfp (MuF F)] is. *)
Program Definition MuF (F : VRel -> VRel) : mon VRel :=
  {| body M x v :=
       exists M', smono M' /\ M' <= M /\ exists w, v = fold w /\ F M' x w |}.
Next Obligation.
  intros M M' H x v [M'' [HM [HM'' Hw]]].
  exists M''. split; [exact HM|]. split; [|exact Hw].
  intros a a0 Ha. apply H, HM'', Ha.
Qed.

Lemma MuF_leq F F' : (forall M, F M <= F' M) -> gfp (MuF F) <= gfp (MuF F').
Proof.
  intros H. apply gfp_leq. intros M x v [M' [HM [HM' [w [-> Hw]]]]].
  exists M'. split; [exact HM|]. split; [exact HM'|].
  exists w. split; [reflexivity|]. exact (H M' x w Hw).
Qed.

Lemma MuF_weq F F' : (forall M, F M == F' M) -> gfp (MuF F) == gfp (MuF F').
Proof.
  intros H. apply antisym; apply MuF_leq; intro M;
    destruct (proj1 (weq_spec _ _) (H M)); assumption.
Qed.

Lemma mu_smono F : (forall M, smono M -> smono (F M)) -> smono (gfp (MuF F)).
Proof.
  intros HF.
  assert (Hc : (fun y v => exists x : Stage, x ⊑ y /\ gfp (MuF F) x v)
               <= gfp (MuF F)).
  { apply leq_gfp. intros y v [x [Hxy Hv]].
    destruct (gfp_pfp (MuF F) x v Hv) as [M' [HM' [HM'G [w [-> Hw]]]]].
    exists M'. split; [exact HM'|]. split.
    - intros z u Hu. exists z. split; [reflexivity|]. exact (HM'G z u Hu).
    - exists w. split; [reflexivity|]. exact (HF M' HM' x y Hxy w Hw). }
  intros x y Hxy v Hv. apply Hc. exists x. split; assumption.
Qed.

(** [fold] needs no positivity. *)
Lemma mu_fold F x w :
  smono (gfp (MuF F)) -> F (gfp (MuF F)) x w -> gfp (MuF F) x (fold w).
Proof.
  intros HG Hw. apply (pfp_gfp (MuF F)).
  exists (gfp (MuF F)). split; [exact HG|]. split; [reflexivity|].
  exists w. split; [reflexivity|exact Hw].
Qed.

(** Coinduction needs no positivity either. *)
Lemma mu_coind F (S : VRel) : smono S ->
  (forall x v, S x v -> exists w, v = fold w /\ F S x w) ->
  S <= gfp (MuF F).
Proof.
  intros HS H. apply leq_gfp. intros x v Hv.
  destruct (H x v Hv) as [w [-> Hw]].
  exists S. split; [exact HS|]. split; [reflexivity|].
  exists w. split; [reflexivity|exact Hw].
Qed.

(** [unfold] needs [F] to be monotone. *)
Lemma mu_unfold F x v :
  (forall M M', M <= M' -> F M <= F M') ->
  gfp (MuF F) x v -> exists w, v = fold w /\ F (gfp (MuF F)) x w.
Proof.
  intros HF Hv.
  destruct (gfp_pfp (MuF F) x v Hv) as [M' [HM' [HM'G [w [-> Hw]]]]].
  exists w. split; [reflexivity|]. exact (HF _ _ HM'G x w Hw).
Qed.

(** ** Type constructors *)

(** Products and functions are observed through the step they take, so
    that [rec] values (which unroll first) are covered too. *)
Definition VProd (P1 P2 : VRel) : VRel := fun x v =>
  (forall b, reducible (prj b v)) /\
  forall y : Stage, x ⊏ y -> forall e',
    (prj true v ~> e' -> Cr P1 y e') /\ (prj false v ~> e' -> Cr P2 y e').

Definition VSum (P1 P2 : VRel) : VRel := fun x v =>
  (exists v1, v = inj true v1 /\ P1 x v1) \/
  (exists v2, v = inj false v2 /\ P2 x v2).

Definition VArr (P1 P2 : VRel) : VRel := fun x v =>
  (forall w, reducible (app v w)) /\
  forall y : Stage, x ⊏ y -> forall w, P1 y w ->
    forall e', app v w ~> e' -> Cr P2 y e'.

Lemma VProd_leq P1 P2 P1' P2' :
  P1 <= P1' -> P2 <= P2' -> VProd P1 P2 <= VProd P1' P2'.
Proof.
  intros H1 H2 x v [Hr Hc]. split; [exact Hr|].
  intros y Hy e'. destruct (Hc y Hy e') as [Ha Hb]. split; intros S.
  - exact (Cr_leq _ _ H1 y e' (Ha S)).
  - exact (Cr_leq _ _ H2 y e' (Hb S)).
Qed.

Lemma VSum_leq P1 P2 P1' P2' :
  P1 <= P1' -> P2 <= P2' -> VSum P1 P2 <= VSum P1' P2'.
Proof.
  intros H1 H2 x v [[v1 [-> Hv]]|[v2 [-> Hv]]].
  - left. exists v1. split; [reflexivity|exact (H1 x v1 Hv)].
  - right. exists v2. split; [reflexivity|exact (H2 x v2 Hv)].
Qed.

Lemma VArr_leq P1 P2 P1' P2' :
  P1' <= P1 -> P2 <= P2' -> VArr P1 P2 <= VArr P1' P2'.
Proof.
  intros H1 H2 x v [Hr Hc]. split; [exact Hr|].
  intros y Hy w Hw e' S.
  exact (Cr_leq _ _ H2 y e' (Hc y Hy w (H1 y w Hw) e' S)).
Qed.

Lemma VProd_weq P1 P2 P1' P2' :
  P1 == P1' -> P2 == P2' -> VProd P1 P2 == VProd P1' P2'.
Proof.
  intros H1 H2. apply weq_spec in H1 as [H1 H1']. apply weq_spec in H2 as [H2 H2'].
  apply antisym; apply VProd_leq; assumption.
Qed.

Lemma VSum_weq P1 P2 P1' P2' :
  P1 == P1' -> P2 == P2' -> VSum P1 P2 == VSum P1' P2'.
Proof.
  intros H1 H2. apply weq_spec in H1 as [H1 H1']. apply weq_spec in H2 as [H2 H2'].
  apply antisym; apply VSum_leq; assumption.
Qed.

Lemma VArr_weq P1 P2 P1' P2' :
  P1 == P1' -> P2 == P2' -> VArr P1 P2 == VArr P1' P2'.
Proof.
  intros H1 H2. apply weq_spec in H1 as [H1 H1']. apply weq_spec in H2 as [H2 H2'].
  apply antisym; apply VArr_leq; assumption.
Qed.

Lemma VProd_smono P1 P2 : smono (VProd P1 P2).
Proof.
  intros x y Hxy v [Hr Hc]. split; [exact Hr|].
  intros z Hz. apply Hc. exact (Stage_later_trans_l _ _ _ Hxy Hz).
Qed.

Lemma VSum_smono P1 P2 : smono P1 -> smono P2 -> smono (VSum P1 P2).
Proof.
  intros H1 H2 x y Hxy v [[v1 [-> Hv]]|[v2 [-> Hv]]].
  - left. exists v1. split; [reflexivity|exact (H1 x y Hxy v1 Hv)].
  - right. exists v2. split; [reflexivity|exact (H2 x y Hxy v2 Hv)].
Qed.

Lemma VArr_smono P1 P2 : smono (VArr P1 P2).
Proof.
  intros x y Hxy v [Hr Hc]. split; [exact Hr|].
  intros z Hz. apply Hc. exact (Stage_later_trans_l _ _ _ Hxy Hz).
Qed.

(** ** The value relation *)

Fixpoint V {n} (A : Ty n) (ρ : fin n -> VRel) : VRel :=
  match A with
  | var_Ty i => ρ i
  | Void => fun _ _ => False
  | Unit => fun _ v => v = unit
  | Nat => fun _ v => is_nat v = true
  | Prod A1 A2 => VProd (V A1 ρ) (V A2 ρ)
  | Sum A1 A2 => VSum (V A1 ρ) (V A2 ρ)
  | Arr A1 A2 => VArr (V A1 ρ) (V A2 ρ)
  | Mu A1 => gfp (MuF (fun M => V A1 (M .: ρ)))
  end.

Definition env_smono {n} (ρ : fin n -> VRel) := forall i, smono (ρ i).

Lemma V_smono {n} (A : Ty n) ρ : env_smono ρ -> smono (V A ρ).
Proof.
  revert ρ. induction A as [n i|n|n|n|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A IH]; intros ρ Hρ; cbn [V].
  - apply Hρ.
  - intros x y _ v [].
  - intros x y _ v H; exact H.
  - intros x y _ v H; exact H.
  - apply VProd_smono.
  - apply VSum_smono; [apply IH1|apply IH2]; exact Hρ.
  - apply VArr_smono.
  - apply mu_smono. intros M HM. apply IH. intros [i|]; [apply Hρ|exact HM].
Qed.

(** [V A] only depends on the variables that occur in [A]. *)
Lemma V_ext {n} (A : Ty n) ρ ρ' :
  (forall i, occurs i A = true -> ρ i == ρ' i) -> V A ρ == V A ρ'.
Proof.
  revert ρ ρ'. induction A as [n i|n|n|n|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A IH]; intros ρ ρ' H; cbn [V].
  - apply H. cbn. apply fin_eqb_true.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply VProd_weq; [apply IH1|apply IH2]; intros i Hi; apply H; cbn;
      rewrite Hi; [reflexivity|apply Bool.orb_true_r].
  - apply VSum_weq; [apply IH1|apply IH2]; intros i Hi; apply H; cbn;
      rewrite Hi; [reflexivity|apply Bool.orb_true_r].
  - apply VArr_weq; [apply IH1|apply IH2]; intros i Hi; apply H; cbn;
      rewrite Hi; [reflexivity|apply Bool.orb_true_r].
  - apply MuF_weq. intros M. apply IH. intros [i|] Hi; cbn.
    + apply H. exact Hi.
    + reflexivity.
Qed.

Corollary V_ext' {n} (A : Ty n) ρ ρ' :
  (forall i, ρ i == ρ' i) -> V A ρ == V A ρ'.
Proof.
  intros H. apply V_ext. intros i _. apply H.
Qed.

Lemma V_ren {n m} (A : Ty n) (ξ : fin n -> fin m) ρ :
  V (ren_Ty ξ A) ρ == V A (ξ >> ρ).
Proof.
  revert m ξ ρ. induction A as [n i|n|n|n|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A IH]; intros m ξ ρ; cbn [ren_Ty V].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply VProd_weq; [apply IH1|apply IH2].
  - apply VSum_weq; [apply IH1|apply IH2].
  - apply VArr_weq; [apply IH1|apply IH2].
  - apply MuF_weq. intros M. etransitivity; [apply IH|].
    apply V_ext'. intros [i|]; reflexivity.
Qed.

Lemma V_subst {n m} (A : Ty n) (σ : fin n -> Ty m) ρ :
  V (subst_Ty σ A) ρ == V A (fun i => V (σ i) ρ).
Proof.
  revert m σ ρ. induction A as [n i|n|n|n|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A IH]; intros m σ ρ; cbn [subst_Ty V].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply VProd_weq; [apply IH1|apply IH2].
  - apply VSum_weq; [apply IH1|apply IH2].
  - apply VArr_weq; [apply IH1|apply IH2].
  - apply MuF_weq. intros M. etransitivity; [apply IH|].
    apply V_ext'. intros [i|].
    + unfold up_Ty_Ty. cbn. etransitivity; [apply V_ren|].
      apply V_ext'. intros j. reflexivity.
    + reflexivity.
Qed.

(** [ρ] and [ρ'] agree except at [k], where [ρ k <= ρ' k]. *)
Definition env_le {n} (k : fin n) (ρ ρ' : fin n -> VRel) :=
  (forall i, i <> k -> ρ i == ρ' i) /\ ρ k <= ρ' k.

Lemma V_mono {n} (k : fin n) (A : Ty n) ρ ρ' :
  pos k A -> env_le k ρ ρ' -> V A ρ <= V A ρ'.
Proof.
  intros Hp. revert ρ ρ'.
  induction Hp as [n k j|n k|n k|n k|n k A1 A2 _ IH1 _ IH2|n k A1 A2 _ IH1 _ IH2
                  |n k A1 A2 Hocc _ IH|n k A _ IH];
    intros ρ ρ' [Hne Hle]; cbn [V].
  - destruct (fin_eqb j k) eqn:E.
    + apply fin_eqb_eq in E. subst j. exact Hle.
    + apply fin_eqb_neq in E. intros x v Hv. exact (proj1 (Hne j E x v) Hv).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply VProd_leq; [apply IH1|apply IH2]; split; assumption.
  - apply VSum_leq; [apply IH1|apply IH2]; split; assumption.
  - apply VArr_leq; [|apply IH; split; assumption].
    assert (E : V A1 ρ == V A1 ρ').
    { apply V_ext. intros i Hi. apply Hne. intros ->. congruence. }
    apply weq_spec in E as [_ E]. exact E.
  - apply MuF_leq. intros M. apply IH. split.
    + intros [i|] Hi; cbn.
      * apply Hne. intros ->. apply Hi. reflexivity.
      * reflexivity.
    + cbn. exact Hle.
Qed.

(** ** Closed types *)

Definition VV (A : Ty 0) : VRel := V A null.
Definition CC (A : Ty 0) : CRel := Cr (VV A).

Lemma VV_smono A : smono (VV A).
Proof.
  apply V_smono. intros [].
Qed.

Lemma CC_smono A : forall x y : Stage, x ⊑ y -> forall e, CC A x e -> CC A y e.
Proof.
  apply Cr_smono, VV_smono.
Qed.

Lemma VV_unroll A : VV (unroll A) == V A (VV (Mu A) .: null).
Proof.
  unfold VV, unroll. etransitivity; [apply V_subst|].
  apply V_ext'. intros [[]|]. reflexivity.
Qed.

Lemma VV_fold A x w : VV (unroll A) x w -> VV (Mu A) x (fold w).
Proof.
  intros H. apply (proj1 (VV_unroll A x w)) in H.
  apply mu_fold; [apply (VV_smono (Mu A))|exact H].
Qed.

Lemma VV_unfold A x v : pos var_zero A ->
  VV (Mu A) x v -> exists w, v = fold w /\ VV (unroll A) x w.
Proof.
  intros Hp Hv.
  edestruct (mu_unfold (fun M => V A (M .: null)) x v) as [w [-> Hw]]; [|exact Hv|].
  - intros M M' HM. apply (V_mono var_zero); [exact Hp|].
    split; [intros [[]|] Hi; exfalso; apply Hi; reflexivity|exact HM].
  - exists w. split; [reflexivity|]. apply (proj2 (VV_unroll A x w)). exact Hw.
Qed.

Lemma VV_app A1 A2 x v w :
  VV (Arr A1 A2) x v -> VV A1 x w -> CC A2 x (app v w).
Proof.
  intros [Hr Hc] Hw. apply Cr_fold. split.
  - intros Hi. destruct (Hr w) as [e' S]. exfalso. exact (Hi e' S).
  - intros e' S y Hy. apply (Hc y Hy w); [|exact S].
    exact (VV_smono A1 _ _ (Stage_later_leq _ _ Hy) w Hw).
Qed.

Lemma VV_prj1 A1 A2 x v : VV (Prod A1 A2) x v -> CC A1 x (prj true v).
Proof.
  intros [Hr Hc]. apply Cr_fold. split.
  - intros Hi. destruct (Hr true) as [e' S]. exfalso. exact (Hi e' S).
  - intros e' S y Hy. exact (proj1 (Hc y Hy e') S).
Qed.

Lemma VV_prj2 A1 A2 x v : VV (Prod A1 A2) x v -> CC A2 x (prj false v).
Proof.
  intros [Hr Hc]. apply Cr_fold. split.
  - intros Hi. destruct (Hr false) as [e' S]. exfalso. exact (Hi e' S).
  - intros e' S y Hy. exact (proj2 (Hc y Hy e') S).
Qed.

(** ** Semantic typing *)

Definition Env n := fin n -> Val 0.

Definition sem_env {n} (Γ : Ctx n) (x : Stage) (γ : Env n) : Prop :=
  forall i, VV (Γ i) x (γ i).

Definition sem_val {n} (Γ : Ctx n) (v : Val n) (A : Ty 0) : Prop :=
  forall x γ, sem_env Γ x γ -> VV A x (v [γ]).

Definition sem_tm {n} (Γ : Ctx n) (e : Tm n) (A : Ty 0) : Prop :=
  forall x γ, sem_env Γ x γ -> CC A x (e [γ]).

Lemma sem_env_smono {n} (Γ : Ctx n) x y γ :
  x ⊑ y -> sem_env Γ x γ -> sem_env Γ y γ.
Proof.
  intros Hxy H i. exact (VV_smono _ _ _ Hxy _ (H i)).
Qed.

Lemma sem_env_cons {n} (Γ : Ctx n) A x γ v :
  VV A x v -> sem_env Γ x γ -> sem_env (A .: Γ) x (v .: γ).
Proof.
  intros Hv H [i|]; cbn; [apply H|exact Hv].
Qed.

(** ** Compatibility lemmas *)

Section Compat.
  Context {n : nat} (Γ : Ctx n).

  Lemma sem_var i : sem_val Γ (var i) (Γ i).
  Proof.
    intros x γ H. exact (H i).
  Qed.

  Lemma sem_zero : sem_val Γ zero Nat.
  Proof.
    intros x γ _. reflexivity.
  Qed.

  Lemma sem_succ v : sem_val Γ v Nat -> sem_val Γ (succ v) Nat.
  Proof.
    intros H x γ Hγ. exact (H x γ Hγ).
  Qed.

  Lemma sem_unit : sem_val Γ unit Unit.
  Proof.
    intros x γ _. reflexivity.
  Qed.

  Lemma sem_prod v1 v2 A1 A2 :
    sem_val Γ v1 A1 -> sem_val Γ v2 A2 -> sem_val Γ (prod v1 v2) (Prod A1 A2).
  Proof.
    intros H1 H2 x γ Hγ. auto_unfold. cbn [subst_Val]. split.
    - intros [|]; eexists; constructor.
    - intros y Hy e'.
      assert (Hy' := sem_env_smono Γ x y γ (Stage_later_leq _ _ Hy) Hγ).
      split; intros S; inversion S; subst; apply Cr_ret.
      + apply H1, Hy'.
      + apply H2, Hy'.
  Qed.

  Lemma sem_inl v A1 A2 : sem_val Γ v A1 -> sem_val Γ (inj true v) (Sum A1 A2).
  Proof.
    intros H x γ Hγ. left. exists (v [γ]). split; [reflexivity|apply H, Hγ].
  Qed.

  Lemma sem_inr v A1 A2 : sem_val Γ v A2 -> sem_val Γ (inj false v) (Sum A1 A2).
  Proof.
    intros H x γ Hγ. right. exists (v [γ]). split; [reflexivity|apply H, Hγ].
  Qed.

  Lemma sem_abs e A1 A2 :
    sem_tm (A1 .: Γ) e A2 -> sem_val Γ (abs e) (Arr A1 A2).
  Proof.
    intros H x γ Hγ. auto_unfold. cbn [subst_Val]. split.
    - intros w. eexists. apply Small.s_beta.
    - intros y Hy w Hw e' S. inversion S; subst.
      assert (Hy' := sem_env_smono Γ x y γ (Stage_later_leq _ _ Hy) Hγ).
      specialize (H y (w .: γ) (sem_env_cons Γ A1 y γ w Hw Hy')).
      asimpl. asimpl in H. exact H.
  Qed.

  (** The Löb argument: [rec v] is good at [x] because unrolling it takes a
      step, and at every strictly earlier stage it is good by induction. *)
  Lemma sem_rec v A :
    allows_rec_ty A = true -> sem_val (A .: Γ) v A -> sem_val Γ (rec v) A.
  Proof.
    intros HA H x γ Hγ. auto_unfold. cbn [subst_Val].
    set (v' := subst_Val (up_Val_Val γ) v).
    revert x Hγ.
    apply (Stage_loeb (fun x => sem_env Γ x γ -> VV A x (rec v'))).
    intros x IH Hγ.
    assert (Hun : forall y : Stage, x ⊏ y -> VV A y (subst_Val (scons (rec v') var) v')).
    { intros y Hy. assert (Hy' := sem_env_smono Γ x y γ (Stage_later_leq _ _ Hy) Hγ).
      specialize (H y (rec v' .: γ) (sem_env_cons Γ A y γ (rec v') (IH y Hy Hy') Hy')).
      unfold v'. asimpl. asimpl in H. exact H. }
    destruct A; try discriminate HA; split.
    - intros b. eexists. apply Small.s_prj_rec.
    - intros y Hy e'. split; intros S; inversion S; subst.
      + eapply VV_prj1. apply Hun, Hy.
      + eapply VV_prj2. apply Hun, Hy.
    - intros w. eexists. apply Small.s_app_rec.
    - intros y Hy w Hw e' S. inversion S; subst.
      eapply VV_app; [apply Hun, Hy|exact Hw].
  Qed.

  Lemma sem_fold v A : sem_val Γ v (unroll A) -> sem_val Γ (fold v) (Mu A).
  Proof.
    intros H x γ Hγ. auto_unfold. cbn [subst_Val].
    apply VV_fold. exact (H x γ Hγ).
  Qed.

  Lemma sem_ret v A : sem_val Γ v A -> sem_tm Γ (ret v) A.
  Proof.
    intros H x γ Hγ. auto_unfold. cbn [subst_Tm]. apply Cr_ret, H, Hγ.
  Qed.

  Lemma sem_let e1 e2 A1 A2 :
    sem_tm Γ e1 A1 -> sem_tm (A1 .: Γ) e2 A2 -> sem_tm Γ (let_ e1 e2) A2.
  Proof.
    intros H1 H2 x γ Hγ. auto_unfold. cbn [subst_Tm].
    apply (Cr_bind (VV A1)); [apply VV_smono|apply H1, Hγ|].
    intros y Hxy u Hu.
    specialize (H2 y (u .: γ) (sem_env_cons Γ A1 y γ u Hu (sem_env_smono Γ x y γ Hxy Hγ))).
    asimpl. asimpl in H2. exact H2.
  Qed.

  Lemma sem_app v1 v2 A1 A2 :
    sem_val Γ v1 (Arr A1 A2) -> sem_val Γ v2 A1 -> sem_tm Γ (app v1 v2) A2.
  Proof.
    intros H1 H2 x γ Hγ. auto_unfold. cbn [subst_Tm].
    eapply VV_app; [apply H1|apply H2]; exact Hγ.
  Qed.

  Lemma sem_ifz v e0 e1 A :
    sem_val Γ v Nat -> sem_tm Γ e0 A -> sem_tm (Nat .: Γ) e1 A ->
    sem_tm Γ (ifz v e0 e1) A.
  Proof.
    intros Hv H0 H1 x γ Hγ. specialize (Hv x γ Hγ). auto_unfold in *. cbn [subst_Tm].
    destruct (subst_Val γ v); cbn in Hv; try discriminate Hv.
    - apply (Cr_step _ _ _ (subst_Tm γ e0)); [apply Small.s_ifz_zero|].
      intros y Hy. apply H0. exact (sem_env_smono Γ x y γ (Stage_later_leq _ _ Hy) Hγ).
    - apply (Cr_step _ _ _ ((subst_Tm (up_Val_Val γ) e1) [v0..])); [apply Small.s_ifz_succ|].
      intros y Hy.
      specialize (H1 y (v0 .: γ) (sem_env_cons Γ Nat y γ v0 Hv
                    (sem_env_smono Γ x y γ (Stage_later_leq _ _ Hy) Hγ))).
      asimpl. asimpl in H1. exact H1.
  Qed.

  Lemma sem_prj1 v A1 A2 : sem_val Γ v (Prod A1 A2) -> sem_tm Γ (prj true v) A1.
  Proof.
    intros H x γ Hγ. auto_unfold. cbn [subst_Tm]. eapply VV_prj1, H, Hγ.
  Qed.

  Lemma sem_prj2 v A1 A2 : sem_val Γ v (Prod A1 A2) -> sem_tm Γ (prj false v) A2.
  Proof.
    intros H x γ Hγ. auto_unfold. cbn [subst_Tm]. eapply VV_prj2, H, Hγ.
  Qed.

  Lemma sem_case v e1 e2 A1 A2 A :
    sem_val Γ v (Sum A1 A2) -> sem_tm (A1 .: Γ) e1 A -> sem_tm (A2 .: Γ) e2 A ->
    sem_tm Γ (case v e1 e2) A.
  Proof.
    intros Hv H1 H2 x γ Hγ. specialize (Hv x γ Hγ). auto_unfold in *. cbn [subst_Tm].
    destruct Hv as [[v1 [E Hv1]]|[v2 [E Hv2]]]; rewrite E.
    - apply (Cr_step _ _ _ ((subst_Tm (up_Val_Val γ) e1) [v1..])); [apply Small.s_case_inj1|].
      intros y Hy. assert (Hy' := Stage_later_leq _ _ Hy).
      specialize (H1 y (v1 .: γ) (sem_env_cons Γ A1 y γ v1 (VV_smono _ _ _ Hy' _ Hv1)
                    (sem_env_smono Γ x y γ Hy' Hγ))).
      asimpl. asimpl in H1. exact H1.
    - apply (Cr_step _ _ _ ((subst_Tm (up_Val_Val γ) e2) [v2..])); [apply Small.s_case_inj2|].
      intros y Hy. assert (Hy' := Stage_later_leq _ _ Hy).
      specialize (H2 y (v2 .: γ) (sem_env_cons Γ A2 y γ v2 (VV_smono _ _ _ Hy' _ Hv2)
                    (sem_env_smono Γ x y γ Hy' Hγ))).
      asimpl. asimpl in H2. exact H2.
  Qed.

  Lemma sem_unfold v A :
    pos var_zero A -> sem_val Γ v (Mu A) -> sem_tm Γ (unfold v) (unroll A).
  Proof.
    intros Hp Hv x γ Hγ. specialize (Hv x γ Hγ). auto_unfold in *. cbn [subst_Tm].
    destruct (VV_unfold _ _ _ Hp Hv) as [w [E Hw]]. rewrite E.
    apply (Cr_step _ _ _ (ret w)); [apply Small.s_unfold|].
    intros y Hy. apply Cr_ret. exact (VV_smono _ _ _ (Stage_later_leq _ _ Hy) _ Hw).
  Qed.
End Compat.

(** ** The fundamental theorem and type safety *)

Theorem fundamental :
  (forall n (Γ : Ctx n) v A, ptyping_val Γ v A -> sem_val Γ v A) /\
  (forall n (Γ : Ctx n) e A, ptyping Γ e A -> sem_tm Γ e A).
Proof.
  pose proof (ptyping_mutind (fun n Γ v A _ => sem_val Γ v A)
                             (fun n Γ e A _ => sem_tm Γ e A)) as Hs.
  cbv beta in Hs.
  enough (Hall : forall n (Γ : Ctx n),
             (forall v A, ptyping_val Γ v A -> sem_val Γ v A) /\
             (forall e A, ptyping Γ e A -> sem_tm Γ e A))
    by (split; intros n Γ; apply Hall).
  apply Hs; clear Hs; intros.
  - apply sem_var.
  - apply sem_zero.
  - apply sem_succ; assumption.
  - apply sem_prod; assumption.
  - apply sem_inl; assumption.
  - apply sem_inr; assumption.
  - apply sem_abs; assumption.
  - apply sem_rec; assumption.
  - apply sem_fold; assumption.
  - apply sem_unit.
  - apply sem_ret; assumption.
  - eapply sem_let; eassumption.
  - eapply sem_app; eassumption.
  - apply sem_ifz; assumption.
  - eapply sem_prj1; eassumption.
  - eapply sem_prj2; eassumption.
  - eapply sem_case; eassumption.
  - apply sem_unfold; assumption.
Qed.

Corollary type_safety e A : ptyping null e A -> safe e.
Proof.
  intros H. apply (Cr_safe (VV A)). intros x.
  assert (Hn : sem_env null x var) by (intros []).
  pose proof (proj2 fundamental 0 null e A H x var Hn) as He.
  asimpl in He. exact He.
Qed.

(** ** Example: an infinite loop is safe *)

Definition loop : Tm 0 := app (rec (var var_zero)) zero.

Lemma loop_typed : ptyping null loop Nat.
Proof.
  unfold loop. eapply (pt_app null _ _ Nat Nat).
  - apply pt_rec; [reflexivity|]. apply (pt_var (Arr Nat Nat .: null) var_zero).
  - apply pt_zero.
Qed.

Corollary loop_safe : safe loop.
Proof. exact (type_safety _ _ loop_typed). Qed.
