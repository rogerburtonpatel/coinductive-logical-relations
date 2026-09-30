(** * A binary logical relation for REC, relating diverging programs

    [Cr2 Q x e e'] is a termination-insensitive approximation: if [e] runs
    to [ret v], then [e'] runs to some [ret v'] with [Q v v'] (at the
    appropriate stage), and [e] never gets stuck.  If [e] diverges, it is
    related to anything.  Structure as in [Unary]:

    - stages come from the clock tower, and [rec] is handled by
      [Stage_loeb] (tower induction);
    - [Cr2 Q] is a greatest fixed point of the "left side takes one more
      step" functional;
    - [Mu] is the [gfp] of the upward-closed unfolding transformer, so
      coinduction and [fold] work for all types, [unfold] for positive
      ones.

    The compatibility lemmas are stated for pairs of terms, so they are
    congruence rules. The fundamental theorem gives reflexivity for typed
    terms, and [adequacy] says related programs co-terminate
    (left-to-right). *)

From CLR Require Export Clock PosTyping.
Import rec.typing.Notations.

(** ** Stage-indexed relations *)

Definition BRel := Stage -> Val 0 -> Val 0 -> Prop.
Definition BCRel := Stage -> Tm 0 -> Tm 0 -> Prop.

Definition smono2 (M : BRel) : Prop :=
  forall x y : Stage, x ⊑ y -> forall v v', M x v v' -> M y v v'.

(** ** Computations *)

Program Definition Cstep2 (Q : BRel) : mon BCRel :=
  {| body Z x e e' :=
       (irreducible e -> exists v v', e = ret v /\ e' ~>* ret v' /\ Q x v v') /\
       (forall e1, e ~> e1 -> forall y : Stage, x ⊏ y -> Z y e1 e') |}.
Next Obligation.
  intros Z Z' H x e e' [H1 H2]. split; [exact H1|].
  intros e1 S y Hy. apply H, (H2 e1 S y Hy).
Qed.

Definition Cr2 (Q : BRel) : BCRel := gfp (Cstep2 Q).

Lemma Cr2_unfold Q x e e' : Cr2 Q x e e' -> Cstep2 Q (Cr2 Q) x e e'.
Proof.
  exact (gfp_pfp (Cstep2 Q) x e e').
Qed.

Lemma Cr2_fold Q x e e' : Cstep2 Q (Cr2 Q) x e e' -> Cr2 Q x e e'.
Proof.
  exact (pfp_gfp (Cstep2 Q) x e e').
Qed.

Lemma Cr2_leq Q Q' : Q <= Q' -> Cr2 Q <= Cr2 Q'.
Proof.
  intros H. unfold Cr2. apply gfp_leq.
  intros Z x e e' [H1 H2]. split; [|exact H2].
  intros Hi. destruct (H1 Hi) as [v [v' [-> [Hs Hv]]]].
  exists v, v'. split; [reflexivity|]. split; [exact Hs|]. apply H, Hv.
Qed.

Lemma Cr2_weq Q Q' : Q == Q' -> Cr2 Q == Cr2 Q'.
Proof.
  intros H. apply weq_spec in H as [H1 H2].
  apply antisym; apply Cr2_leq; assumption.
Qed.

Lemma Cr2_smono Q : smono2 Q ->
  forall x y : Stage, x ⊑ y -> forall e e', Cr2 Q x e e' -> Cr2 Q y e e'.
Proof.
  intros HQ x y Hxy e e' He.
  assert (Hc : (fun y e e' => exists x : Stage, x ⊑ y /\ Cr2 Q x e e') <= Cr2 Q).
  { apply leq_gfp. intros y' e0 e0' [x' [Hxy' He']].
    apply Cr2_unfold in He' as [H1 H2]. split.
    - intros Hi. destruct (H1 Hi) as [v [v' [-> [Hs Hv]]]].
      exists v, v'. split; [reflexivity|]. split; [exact Hs|].
      exact (HQ _ _ Hxy' v v' Hv).
    - intros e1 S z Hz. exists z. split; [reflexivity|].
      apply (H2 e1 S z). exact (Stage_later_trans_l _ _ _ Hxy' Hz). }
  apply Hc. exists x. split; assumption.
Qed.

Lemma Cr2_ret Q x v e' v' : Q x v v' -> e' ~>* ret v' -> Cr2 Q x (ret v) e'.
Proof.
  intros Hv Hs. apply Cr2_fold. split.
  - intros _. exists v, v'. split; [reflexivity|]. split; assumption.
  - intros e1 S. inversion S.
Qed.

(** The left side pays one stage per step. *)
Lemma Cr2_step Q x e1 e1' e' :
  e1 ~> e1' -> (forall y : Stage, x ⊏ y -> Cr2 Q y e1' e') -> Cr2 Q x e1 e'.
Proof.
  intros S H. apply Cr2_fold. split.
  - intros Hi. exfalso. exact (Hi e1' S).
  - intros e'' S' y Hy. rewrite (deterministic _ _ _ S' S). apply H, Hy.
Qed.

(** The right side may take any number of steps for free. *)
Lemma Cr2_anti Q x e e' e'' : e' ~>* e'' -> Cr2 Q x e e'' -> Cr2 Q x e e'.
Proof.
  intros Hs He.
  assert (Hc : (fun x e e' => exists e'', e' ~>* e'' /\ Cr2 Q x e e'') <= Cr2 Q).
  { apply leq_gfp. intros x0 e0 e0' [e1 [Hs1 H1]].
    apply Cr2_unfold in H1 as [H1 H2]. split.
    - intros Hi. destruct (H1 Hi) as [v [v' [-> [Hs' Hv]]]].
      exists v, v'. split; [reflexivity|]. split; [exact (ms_app Hs1 Hs')|exact Hv].
    - intros e2 S y Hy. exists e1. split; [exact Hs1|]. exact (H2 e2 S y Hy). }
  apply Hc. exists e''. split; assumption.
Qed.

Lemma Cr2_bind Q1 Q2 x e1 e1' e2 e2' : smono2 Q1 ->
  Cr2 Q1 x e1 e1' ->
  (forall y : Stage, x ⊑ y -> forall v v', Q1 y v v' ->
     Cr2 Q2 y (e2 [v..]) (e2' [v'..])) ->
  Cr2 Q2 x (let_ e1 e2) (let_ e1' e2').
Proof.
  intros HQ1. revert x e1 e1'.
  apply (Stage_loeb (fun x => forall e1 e1', Cr2 Q1 x e1 e1' ->
    (forall y : Stage, x ⊑ y -> forall v v', Q1 y v v' ->
       Cr2 Q2 y (e2 [v..]) (e2' [v'..])) ->
    Cr2 Q2 x (let_ e1 e2) (let_ e1' e2'))).
  intros x IH e1 e1' He1 K.
  apply Cr2_unfold in He1 as [H1 H2].
  destruct (canstep e1) as [[e1'' S]|Hi].
  - apply (Cr2_step _ _ _ (let_ e1'' e2)); [apply Small.s_let_cong, S|].
    intros y Hy. apply IH; [exact Hy|apply (H2 e1'' S y Hy)|].
    intros z Hz v v' Hv. apply K; [|exact Hv].
    etransitivity; [apply Stage_later_leq, Hy|exact Hz].
  - destruct (H1 Hi) as [v [v' [-> [Hs Hv]]]].
    apply (Cr2_step _ _ _ (e2 [v..])); [apply Small.s_letv|].
    intros y Hy. apply (Cr2_anti _ _ _ _ (e2' [v'..])).
    + eapply ms_app; [apply ms_let_cong, Hs|]. apply ms_one, Small.s_letv.
    + apply K; [apply Stage_later_leq, Hy|].
      exact (HQ1 _ _ (Stage_later_leq _ _ Hy) v v' Hv).
Qed.

(** Adequacy: related at every stage, the right side terminates whenever
    the left does. *)
Lemma Cr2_adequate Q e e' v : (forall x, Cr2 Q x e e') ->
  e ~>* ret v -> exists v', e' ~>* ret v'.
Proof.
  intros H Hs.
  assert (Hk : forall k, Cr2 Q (stage k) e e') by (intros; apply H).
  clear H. revert Hk. remember (ret v) as r eqn:Er.
  induction Hs as [e0|e1 e2 e3 St Hs IH]; intros Hk.
  - subst e0. destruct (Cr2_unfold _ _ _ _ (Hk 0)) as [H1 _].
    destruct H1 as [v0 [v' [_ [Hs' _]]]].
    + intros e0 S. inversion S.
    + exists v'. exact Hs'.
  - apply IH; [exact Er|]. intros k.
    destruct (Cr2_unfold _ _ _ _ (Hk (S k))) as [_ H2].
    apply (H2 e2 St (stage k)), stage_later.
Qed.

(** ** Recursive types *)

Program Definition MuF2 (F : BRel -> BRel) : mon BRel :=
  {| body M x v v' :=
       exists M', smono2 M' /\ M' <= M /\
       exists w w', v = fold w /\ v' = fold w' /\ F M' x w w' |}.
Next Obligation.
  intros M M' H x v v' [M'' [HM [HM'' Hw]]].
  exists M''. split; [exact HM|]. split; [|exact Hw].
  intros a a0 a1 Ha. apply H, HM'', Ha.
Qed.

Lemma MuF2_leq F F' : (forall M, F M <= F' M) -> gfp (MuF2 F) <= gfp (MuF2 F').
Proof.
  intros H. apply gfp_leq. intros M x v v' [M' [HM [HM' [w [w' [-> [-> Hw]]]]]]].
  exists M'. split; [exact HM|]. split; [exact HM'|].
  exists w, w'. split; [reflexivity|]. split; [reflexivity|]. exact (H M' x w w' Hw).
Qed.

Lemma MuF2_weq F F' : (forall M, F M == F' M) -> gfp (MuF2 F) == gfp (MuF2 F').
Proof.
  intros H. apply antisym; apply MuF2_leq; intro M;
    destruct (proj1 (weq_spec _ _) (H M)); assumption.
Qed.

Lemma mu2_smono F : (forall M, smono2 M -> smono2 (F M)) -> smono2 (gfp (MuF2 F)).
Proof.
  intros HF.
  assert (Hc : (fun y v v' => exists x : Stage, x ⊑ y /\ gfp (MuF2 F) x v v')
               <= gfp (MuF2 F)).
  { apply leq_gfp. intros y v v' [x [Hxy Hv]].
    destruct (gfp_pfp (MuF2 F) x v v' Hv) as [M' [HM' [HM'G [w [w' [-> [-> Hw]]]]]]].
    exists M'. split; [exact HM'|]. split.
    - intros z u u' Hu. exists z. split; [reflexivity|]. exact (HM'G z u u' Hu).
    - exists w, w'. split; [reflexivity|]. split; [reflexivity|].
      exact (HF M' HM' x y Hxy w w' Hw). }
  intros x y Hxy v v' Hv. apply Hc. exists x. split; assumption.
Qed.

Lemma mu2_fold F x w w' :
  smono2 (gfp (MuF2 F)) -> F (gfp (MuF2 F)) x w w' ->
  gfp (MuF2 F) x (fold w) (fold w').
Proof.
  intros HG Hw. apply (pfp_gfp (MuF2 F)).
  exists (gfp (MuF2 F)). split; [exact HG|]. split; [reflexivity|].
  exists w, w'. split; [reflexivity|]. split; [reflexivity|exact Hw].
Qed.

Lemma mu2_coind F (S : BRel) : smono2 S ->
  (forall x v v', S x v v' ->
     exists w w', v = fold w /\ v' = fold w' /\ F S x w w') ->
  S <= gfp (MuF2 F).
Proof.
  intros HS H. apply leq_gfp. intros x v v' Hv.
  destruct (H x v v' Hv) as [w [w' [-> [-> Hw]]]].
  exists S. split; [exact HS|]. split; [reflexivity|].
  exists w, w'. split; [reflexivity|]. split; [reflexivity|exact Hw].
Qed.

Lemma mu2_unfold F x v v' :
  (forall M M', M <= M' -> F M <= F M') ->
  gfp (MuF2 F) x v v' ->
  exists w w', v = fold w /\ v' = fold w' /\ F (gfp (MuF2 F)) x w w'.
Proof.
  intros HF Hv.
  destruct (gfp_pfp (MuF2 F) x v v' Hv) as [M' [HM' [HM'G [w [w' [-> [-> Hw]]]]]]].
  exists w, w'. split; [reflexivity|]. split; [reflexivity|].
  exact (HF _ _ HM'G x w w' Hw).
Qed.

(** ** Type constructors *)

Definition VProd2 (P1 P2 : BRel) : BRel := fun x v v' =>
  (forall b, reducible (prj b v)) /\
  forall y : Stage, x ⊏ y -> forall e1,
    (prj true v ~> e1 -> Cr2 P1 y e1 (prj true v')) /\
    (prj false v ~> e1 -> Cr2 P2 y e1 (prj false v')).

Definition VSum2 (P1 P2 : BRel) : BRel := fun x v v' =>
  (exists v1 v1', v = inj true v1 /\ v' = inj true v1' /\ P1 x v1 v1') \/
  (exists v2 v2', v = inj false v2 /\ v' = inj false v2' /\ P2 x v2 v2').

Definition VArr2 (P1 P2 : BRel) : BRel := fun x v v' =>
  (forall w, reducible (app v w)) /\
  forall y : Stage, x ⊏ y -> forall w w', P1 y w w' ->
    forall e1, app v w ~> e1 -> Cr2 P2 y e1 (app v' w').

Lemma VProd2_leq P1 P2 P1' P2' :
  P1 <= P1' -> P2 <= P2' -> VProd2 P1 P2 <= VProd2 P1' P2'.
Proof.
  intros H1 H2 x v v' [Hr Hc]. split; [exact Hr|].
  intros y Hy e1. destruct (Hc y Hy e1) as [Ha Hb]. split; intros S.
  - exact (Cr2_leq _ _ H1 y _ _ (Ha S)).
  - exact (Cr2_leq _ _ H2 y _ _ (Hb S)).
Qed.

Lemma VSum2_leq P1 P2 P1' P2' :
  P1 <= P1' -> P2 <= P2' -> VSum2 P1 P2 <= VSum2 P1' P2'.
Proof.
  intros H1 H2 x v v' [[v1 [v1' [-> [-> Hv]]]]|[v2 [v2' [-> [-> Hv]]]]].
  - left. exists v1, v1'. split; [reflexivity|]. split; [reflexivity|exact (H1 x v1 v1' Hv)].
  - right. exists v2, v2'. split; [reflexivity|]. split; [reflexivity|exact (H2 x v2 v2' Hv)].
Qed.

Lemma VArr2_leq P1 P2 P1' P2' :
  P1' <= P1 -> P2 <= P2' -> VArr2 P1 P2 <= VArr2 P1' P2'.
Proof.
  intros H1 H2 x v v' [Hr Hc]. split; [exact Hr|].
  intros y Hy w w' Hw e1 S.
  exact (Cr2_leq _ _ H2 y _ _ (Hc y Hy w w' (H1 y w w' Hw) e1 S)).
Qed.

Lemma VProd2_weq P1 P2 P1' P2' :
  P1 == P1' -> P2 == P2' -> VProd2 P1 P2 == VProd2 P1' P2'.
Proof.
  intros H1 H2. apply weq_spec in H1 as [H1 H1']. apply weq_spec in H2 as [H2 H2'].
  apply antisym; apply VProd2_leq; assumption.
Qed.

Lemma VSum2_weq P1 P2 P1' P2' :
  P1 == P1' -> P2 == P2' -> VSum2 P1 P2 == VSum2 P1' P2'.
Proof.
  intros H1 H2. apply weq_spec in H1 as [H1 H1']. apply weq_spec in H2 as [H2 H2'].
  apply antisym; apply VSum2_leq; assumption.
Qed.

Lemma VArr2_weq P1 P2 P1' P2' :
  P1 == P1' -> P2 == P2' -> VArr2 P1 P2 == VArr2 P1' P2'.
Proof.
  intros H1 H2. apply weq_spec in H1 as [H1 H1']. apply weq_spec in H2 as [H2 H2'].
  apply antisym; apply VArr2_leq; assumption.
Qed.

Lemma VProd2_smono P1 P2 : smono2 (VProd2 P1 P2).
Proof.
  intros x y Hxy v v' [Hr Hc]. split; [exact Hr|].
  intros z Hz. apply Hc. exact (Stage_later_trans_l _ _ _ Hxy Hz).
Qed.

Lemma VSum2_smono P1 P2 : smono2 P1 -> smono2 P2 -> smono2 (VSum2 P1 P2).
Proof.
  intros H1 H2 x y Hxy v v' [[v1 [v1' [-> [-> Hv]]]]|[v2 [v2' [-> [-> Hv]]]]].
  - left. exists v1, v1'. split; [reflexivity|]. split; [reflexivity|exact (H1 x y Hxy v1 v1' Hv)].
  - right. exists v2, v2'. split; [reflexivity|]. split; [reflexivity|exact (H2 x y Hxy v2 v2' Hv)].
Qed.

Lemma VArr2_smono P1 P2 : smono2 (VArr2 P1 P2).
Proof.
  intros x y Hxy v v' [Hr Hc]. split; [exact Hr|].
  intros z Hz. apply Hc. exact (Stage_later_trans_l _ _ _ Hxy Hz).
Qed.

(** ** The value relation *)

Fixpoint V2 {n} (A : Ty n) (ρ : fin n -> BRel) : BRel :=
  match A with
  | var_Ty i => ρ i
  | Void => fun _ _ _ => False
  | Unit => fun _ v v' => v = unit /\ v' = unit
  | Nat => fun _ v v' => v = v' /\ is_nat v = true
  | Prod A1 A2 => VProd2 (V2 A1 ρ) (V2 A2 ρ)
  | Sum A1 A2 => VSum2 (V2 A1 ρ) (V2 A2 ρ)
  | Arr A1 A2 => VArr2 (V2 A1 ρ) (V2 A2 ρ)
  | Mu A1 => gfp (MuF2 (fun M => V2 A1 (M .: ρ)))
  end.

Definition env_smono2 {n} (ρ : fin n -> BRel) := forall i, smono2 (ρ i).

Lemma V2_smono {n} (A : Ty n) ρ : env_smono2 ρ -> smono2 (V2 A ρ).
Proof.
  revert ρ. induction A as [n i|n|n|n|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A IH]; intros ρ Hρ; cbn [V2].
  - apply Hρ.
  - intros x y _ v v' [].
  - intros x y _ v v' H; exact H.
  - intros x y _ v v' H; exact H.
  - apply VProd2_smono.
  - apply VSum2_smono; [apply IH1|apply IH2]; exact Hρ.
  - apply VArr2_smono.
  - apply mu2_smono. intros M HM. apply IH. intros [i|]; [apply Hρ|exact HM].
Qed.

Lemma V2_ext {n} (A : Ty n) ρ ρ' :
  (forall i, occurs i A = true -> ρ i == ρ' i) -> V2 A ρ == V2 A ρ'.
Proof.
  revert ρ ρ'. induction A as [n i|n|n|n|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A IH]; intros ρ ρ' H; cbn [V2].
  - apply H. cbn. apply fin_eqb_true.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply VProd2_weq; [apply IH1|apply IH2]; intros i Hi; apply H; cbn;
      rewrite Hi; [reflexivity|apply Bool.orb_true_r].
  - apply VSum2_weq; [apply IH1|apply IH2]; intros i Hi; apply H; cbn;
      rewrite Hi; [reflexivity|apply Bool.orb_true_r].
  - apply VArr2_weq; [apply IH1|apply IH2]; intros i Hi; apply H; cbn;
      rewrite Hi; [reflexivity|apply Bool.orb_true_r].
  - apply MuF2_weq. intros M. apply IH. intros [i|] Hi; cbn.
    + apply H. exact Hi.
    + reflexivity.
Qed.

Corollary V2_ext' {n} (A : Ty n) ρ ρ' :
  (forall i, ρ i == ρ' i) -> V2 A ρ == V2 A ρ'.
Proof.
  intros H. apply V2_ext. intros i _. apply H.
Qed.

Lemma V2_ren {n m} (A : Ty n) (ξ : fin n -> fin m) ρ :
  V2 (ren_Ty ξ A) ρ == V2 A (ξ >> ρ).
Proof.
  revert m ξ ρ. induction A as [n i|n|n|n|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A IH]; intros m ξ ρ; cbn [ren_Ty V2].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply VProd2_weq; [apply IH1|apply IH2].
  - apply VSum2_weq; [apply IH1|apply IH2].
  - apply VArr2_weq; [apply IH1|apply IH2].
  - apply MuF2_weq. intros M. etransitivity; [apply IH|].
    apply V2_ext'. intros [i|]; reflexivity.
Qed.

Lemma V2_subst {n m} (A : Ty n) (σ : fin n -> Ty m) ρ :
  V2 (subst_Ty σ A) ρ == V2 A (fun i => V2 (σ i) ρ).
Proof.
  revert m σ ρ. induction A as [n i|n|n|n|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A1 IH1 A2 IH2|n A IH]; intros m σ ρ; cbn [subst_Ty V2].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply VProd2_weq; [apply IH1|apply IH2].
  - apply VSum2_weq; [apply IH1|apply IH2].
  - apply VArr2_weq; [apply IH1|apply IH2].
  - apply MuF2_weq. intros M. etransitivity; [apply IH|].
    apply V2_ext'. intros [i|].
    + unfold up_Ty_Ty. cbn. etransitivity; [apply V2_ren|].
      apply V2_ext'. intros j. reflexivity.
    + reflexivity.
Qed.

Definition env_le2 {n} (k : fin n) (ρ ρ' : fin n -> BRel) :=
  (forall i, i <> k -> ρ i == ρ' i) /\ ρ k <= ρ' k.

Lemma V2_mono {n} (k : fin n) (A : Ty n) ρ ρ' :
  pos k A -> env_le2 k ρ ρ' -> V2 A ρ <= V2 A ρ'.
Proof.
  intros Hp. revert ρ ρ'.
  induction Hp as [n k j|n k|n k|n k|n k A1 A2 _ IH1 _ IH2|n k A1 A2 _ IH1 _ IH2
                  |n k A1 A2 Hocc _ IH|n k A _ IH];
    intros ρ ρ' [Hne Hle]; cbn [V2].
  - destruct (fin_eqb j k) eqn:E.
    + apply fin_eqb_eq in E. subst j. exact Hle.
    + apply fin_eqb_neq in E. intros x v v' Hv. exact (proj1 (Hne j E x v v') Hv).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply VProd2_leq; [apply IH1|apply IH2]; split; assumption.
  - apply VSum2_leq; [apply IH1|apply IH2]; split; assumption.
  - apply VArr2_leq; [|apply IH; split; assumption].
    assert (E : V2 A1 ρ == V2 A1 ρ').
    { apply V2_ext. intros i Hi. apply Hne. intros ->. congruence. }
    apply weq_spec in E as [_ E]. exact E.
  - apply MuF2_leq. intros M. apply IH. split.
    + intros [i|] Hi; cbn.
      * apply Hne. intros ->. apply Hi. reflexivity.
      * reflexivity.
    + cbn. exact Hle.
Qed.

(** ** Closed types *)

Definition VV2 (A : Ty 0) : BRel := V2 A null.
Definition CC2 (A : Ty 0) : BCRel := Cr2 (VV2 A).

Lemma VV2_smono A : smono2 (VV2 A).
Proof.
  apply V2_smono. intros [].
Qed.

Lemma VV2_unroll A : VV2 (unroll A) == V2 A (VV2 (Mu A) .: null).
Proof.
  unfold VV2, unroll. etransitivity; [apply V2_subst|].
  apply V2_ext'. intros [[]|]. reflexivity.
Qed.

Lemma VV2_fold A x w w' :
  VV2 (unroll A) x w w' -> VV2 (Mu A) x (fold w) (fold w').
Proof.
  intros H. apply (proj1 (VV2_unroll A x w w')) in H.
  apply mu2_fold; [apply (VV2_smono (Mu A))|exact H].
Qed.

Lemma VV2_unfold A x v v' : pos var_zero A -> VV2 (Mu A) x v v' ->
  exists w w', v = fold w /\ v' = fold w' /\ VV2 (unroll A) x w w'.
Proof.
  intros Hp Hv.
  edestruct (mu2_unfold (fun M => V2 A (M .: null)) x v v') as [w [w' [-> [-> Hw]]]];
    [|exact Hv|].
  - intros M M' HM. apply (V2_mono var_zero); [exact Hp|].
    split; [intros [[]|] Hi; exfalso; apply Hi; reflexivity|exact HM].
  - exists w, w'. split; [reflexivity|]. split; [reflexivity|].
    apply (proj2 (VV2_unroll A x w w')). exact Hw.
Qed.

Lemma VV2_app A1 A2 x v v' w w' :
  VV2 (Arr A1 A2) x v v' -> VV2 A1 x w w' -> CC2 A2 x (app v w) (app v' w').
Proof.
  intros [Hr Hc] Hw. apply Cr2_fold. split.
  - intros Hi. destruct (Hr w) as [e1 S]. exfalso. exact (Hi e1 S).
  - intros e1 S y Hy. apply (Hc y Hy w w'); [|exact S].
    exact (VV2_smono A1 _ _ (Stage_later_leq _ _ Hy) w w' Hw).
Qed.

Lemma VV2_prj1 A1 A2 x v v' :
  VV2 (Prod A1 A2) x v v' -> CC2 A1 x (prj true v) (prj true v').
Proof.
  intros [Hr Hc]. apply Cr2_fold. split.
  - intros Hi. destruct (Hr true) as [e1 S]. exfalso. exact (Hi e1 S).
  - intros e1 S y Hy. exact (proj1 (Hc y Hy e1) S).
Qed.

Lemma VV2_prj2 A1 A2 x v v' :
  VV2 (Prod A1 A2) x v v' -> CC2 A2 x (prj false v) (prj false v').
Proof.
  intros [Hr Hc]. apply Cr2_fold. split.
  - intros Hi. destruct (Hr false) as [e1 S]. exfalso. exact (Hi e1 S).
  - intros e1 S y Hy. exact (proj2 (Hc y Hy e1) S).
Qed.

(** ** Semantic (binary) typing *)

Definition Env n := fin n -> Val 0.

Definition sem_env2 {n} (Γ : Ctx n) (x : Stage) (γ γ' : Env n) : Prop :=
  forall i, VV2 (Γ i) x (γ i) (γ' i).

Definition sem_val2 {n} (Γ : Ctx n) (v v' : Val n) (A : Ty 0) : Prop :=
  forall x γ γ', sem_env2 Γ x γ γ' -> VV2 A x (v [γ]) (v' [γ']).

Definition sem_tm2 {n} (Γ : Ctx n) (e e' : Tm n) (A : Ty 0) : Prop :=
  forall x γ γ', sem_env2 Γ x γ γ' -> CC2 A x (e [γ]) (e' [γ']).

Lemma sem_env2_smono {n} (Γ : Ctx n) x y γ γ' :
  x ⊑ y -> sem_env2 Γ x γ γ' -> sem_env2 Γ y γ γ'.
Proof.
  intros Hxy H i. exact (VV2_smono _ _ _ Hxy _ _ (H i)).
Qed.

Lemma sem_env2_cons {n} (Γ : Ctx n) A x γ γ' v v' :
  VV2 A x v v' -> sem_env2 Γ x γ γ' -> sem_env2 (A .: Γ) x (v .: γ) (v' .: γ').
Proof.
  intros Hv H [i|]; cbn; [apply H|exact Hv].
Qed.

(** ** Compatibility lemmas (congruence rules) *)

Section Compat.
  Context {n : nat} (Γ : Ctx n).

  Lemma rel_var i : sem_val2 Γ (var i) (var i) (Γ i).
  Proof.
    intros x γ γ' H. exact (H i).
  Qed.

  Lemma rel_zero : sem_val2 Γ zero zero Nat.
  Proof.
    intros x γ γ' _. split; reflexivity.
  Qed.

  Lemma rel_succ v v' : sem_val2 Γ v v' Nat -> sem_val2 Γ (succ v) (succ v') Nat.
  Proof.
    intros H x γ γ' Hγ. destruct (H x γ γ' Hγ) as [E Hn].
    split; [|exact Hn]. auto_unfold in *. cbn [subst_Val]. rewrite E. reflexivity.
  Qed.

  Lemma rel_unit : sem_val2 Γ unit unit Unit.
  Proof.
    intros x γ γ' _. split; reflexivity.
  Qed.

  Lemma rel_prod v1 v1' v2 v2' A1 A2 :
    sem_val2 Γ v1 v1' A1 -> sem_val2 Γ v2 v2' A2 ->
    sem_val2 Γ (prod v1 v2) (prod v1' v2') (Prod A1 A2).
  Proof.
    intros H1 H2 x γ γ' Hγ. auto_unfold. cbn [subst_Val]. split.
    - intros [|]; eexists; constructor.
    - intros y Hy e1.
      assert (Hy' := sem_env2_smono Γ x y γ γ' (Stage_later_leq _ _ Hy) Hγ).
      split; intros S; inversion S; subst.
      + apply (Cr2_ret _ _ _ _ (subst_Val γ' v1')); [apply H1, Hy'|].
        apply ms_one, Small.s_prj1.
      + apply (Cr2_ret _ _ _ _ (subst_Val γ' v2')); [apply H2, Hy'|].
        apply ms_one, Small.s_prj2.
  Qed.

  Lemma rel_inl v v' A1 A2 :
    sem_val2 Γ v v' A1 -> sem_val2 Γ (inj true v) (inj true v') (Sum A1 A2).
  Proof.
    intros H x γ γ' Hγ. left. exists (v [γ]), (v' [γ']).
    split; [reflexivity|]. split; [reflexivity|apply H, Hγ].
  Qed.

  Lemma rel_inr v v' A1 A2 :
    sem_val2 Γ v v' A2 -> sem_val2 Γ (inj false v) (inj false v') (Sum A1 A2).
  Proof.
    intros H x γ γ' Hγ. right. exists (v [γ]), (v' [γ']).
    split; [reflexivity|]. split; [reflexivity|apply H, Hγ].
  Qed.

  Lemma rel_abs e e' A1 A2 :
    sem_tm2 (A1 .: Γ) e e' A2 -> sem_val2 Γ (abs e) (abs e') (Arr A1 A2).
  Proof.
    intros H x γ γ' Hγ. auto_unfold. cbn [subst_Val]. split.
    - intros w. eexists. apply Small.s_beta.
    - intros y Hy w w' Hw e1 S. inversion S; subst.
      eapply Cr2_anti; [apply ms_one, Small.s_beta|].
      assert (Hy' := sem_env2_smono Γ x y γ γ' (Stage_later_leq _ _ Hy) Hγ).
      specialize (H y (w .: γ) (w' .: γ') (sem_env2_cons Γ A1 y γ γ' w w' Hw Hy')).
      asimpl. asimpl in H. exact H.
  Qed.

  Lemma rel_rec v v' A :
    allows_rec_ty A = true -> sem_val2 (A .: Γ) v v' A ->
    sem_val2 Γ (rec v) (rec v') A.
  Proof.
    intros HA H x γ γ' Hγ. auto_unfold. cbn [subst_Val].
    set (u := subst_Val (up_Val_Val γ) v).
    set (u' := subst_Val (up_Val_Val γ') v').
    revert x Hγ.
    apply (Stage_loeb (fun x => sem_env2 Γ x γ γ' -> VV2 A x (rec u) (rec u'))).
    intros x IH Hγ.
    assert (Hun : forall y : Stage, x ⊏ y ->
      VV2 A y (subst_Val (scons (rec u) var) u) (subst_Val (scons (rec u') var) u')).
    { intros y Hy. assert (Hy' := sem_env2_smono Γ x y γ γ' (Stage_later_leq _ _ Hy) Hγ).
      specialize (H y (rec u .: γ) (rec u' .: γ')
                    (sem_env2_cons Γ A y γ γ' (rec u) (rec u') (IH y Hy Hy') Hy')).
      unfold u, u'. asimpl. asimpl in H. exact H. }
    destruct A; try discriminate HA; split.
    - intros b. eexists. apply Small.s_prj_rec.
    - intros y Hy e1. split; intros S; inversion S; subst;
        (eapply Cr2_anti; [apply ms_one, Small.s_prj_rec|]).
      + eapply VV2_prj1. apply Hun, Hy.
      + eapply VV2_prj2. apply Hun, Hy.
    - intros w. eexists. apply Small.s_app_rec.
    - intros y Hy w w' Hw e1 S. inversion S; subst.
      eapply Cr2_anti; [apply ms_one, Small.s_app_rec|].
      eapply VV2_app; [apply Hun, Hy|exact Hw].
  Qed.

  Lemma rel_fold v v' A :
    sem_val2 Γ v v' (unroll A) -> sem_val2 Γ (fold v) (fold v') (Mu A).
  Proof.
    intros H x γ γ' Hγ. auto_unfold. cbn [subst_Val].
    apply VV2_fold. exact (H x γ γ' Hγ).
  Qed.

  Lemma rel_ret v v' A : sem_val2 Γ v v' A -> sem_tm2 Γ (ret v) (ret v') A.
  Proof.
    intros H x γ γ' Hγ. auto_unfold. cbn [subst_Tm].
    apply (Cr2_ret _ _ _ _ (subst_Val γ' v')); [apply H, Hγ|apply ms_refl].
  Qed.

  Lemma rel_let e1 e1' e2 e2' A1 A2 :
    sem_tm2 Γ e1 e1' A1 -> sem_tm2 (A1 .: Γ) e2 e2' A2 ->
    sem_tm2 Γ (let_ e1 e2) (let_ e1' e2') A2.
  Proof.
    intros H1 H2 x γ γ' Hγ. auto_unfold. cbn [subst_Tm].
    apply (Cr2_bind (VV2 A1)); [apply VV2_smono|apply H1, Hγ|].
    intros y Hxy u u' Hu.
    specialize (H2 y (u .: γ) (u' .: γ')
                  (sem_env2_cons Γ A1 y γ γ' u u' Hu (sem_env2_smono Γ x y γ γ' Hxy Hγ))).
    asimpl. asimpl in H2. exact H2.
  Qed.

  Lemma rel_app v1 v1' v2 v2' A1 A2 :
    sem_val2 Γ v1 v1' (Arr A1 A2) -> sem_val2 Γ v2 v2' A1 ->
    sem_tm2 Γ (app v1 v2) (app v1' v2') A2.
  Proof.
    intros H1 H2 x γ γ' Hγ. auto_unfold. cbn [subst_Tm].
    eapply VV2_app; [apply H1|apply H2]; exact Hγ.
  Qed.

  Lemma rel_ifz v v' e0 e0' e1 e1' A :
    sem_val2 Γ v v' Nat -> sem_tm2 Γ e0 e0' A -> sem_tm2 (Nat .: Γ) e1 e1' A ->
    sem_tm2 Γ (ifz v e0 e1) (ifz v' e0' e1') A.
  Proof.
    intros Hv H0 H1 x γ γ' Hγ. specialize (Hv x γ γ' Hγ). auto_unfold in *. cbn [subst_Tm].
    destruct Hv as [E Hn]. rewrite <- E.
    destruct (subst_Val γ v); cbn in Hn; try discriminate Hn.
    - apply (Cr2_step _ _ _ (subst_Tm γ e0)); [apply Small.s_ifz_zero|].
      intros y Hy. eapply Cr2_anti; [apply ms_one, Small.s_ifz_zero|].
      apply H0. exact (sem_env2_smono Γ x y γ γ' (Stage_later_leq _ _ Hy) Hγ).
    - apply (Cr2_step _ _ _ ((subst_Tm (up_Val_Val γ) e1) [v0..])); [apply Small.s_ifz_succ|].
      intros y Hy. eapply Cr2_anti; [apply ms_one, Small.s_ifz_succ|].
      assert (Hk : VV2 Nat y v0 v0) by (split; [reflexivity|exact Hn]).
      specialize (H1 y (v0 .: γ) (v0 .: γ') (sem_env2_cons Γ Nat y γ γ' v0 v0 Hk
                    (sem_env2_smono Γ x y γ γ' (Stage_later_leq _ _ Hy) Hγ))).
      asimpl. asimpl in H1. exact H1.
  Qed.

  Lemma rel_prj1 v v' A1 A2 :
    sem_val2 Γ v v' (Prod A1 A2) -> sem_tm2 Γ (prj true v) (prj true v') A1.
  Proof.
    intros H x γ γ' Hγ. auto_unfold. cbn [subst_Tm]. eapply VV2_prj1, H, Hγ.
  Qed.

  Lemma rel_prj2 v v' A1 A2 :
    sem_val2 Γ v v' (Prod A1 A2) -> sem_tm2 Γ (prj false v) (prj false v') A2.
  Proof.
    intros H x γ γ' Hγ. auto_unfold. cbn [subst_Tm]. eapply VV2_prj2, H, Hγ.
  Qed.

  Lemma rel_case v v' e1 e1' e2 e2' A1 A2 A :
    sem_val2 Γ v v' (Sum A1 A2) ->
    sem_tm2 (A1 .: Γ) e1 e1' A -> sem_tm2 (A2 .: Γ) e2 e2' A ->
    sem_tm2 Γ (case v e1 e2) (case v' e1' e2') A.
  Proof.
    intros Hv H1 H2 x γ γ' Hγ. specialize (Hv x γ γ' Hγ). auto_unfold in *. cbn [subst_Tm].
    destruct Hv as [[a [a' [Ea [Eb Ha]]]]|[a [a' [Ea [Eb Ha]]]]]; rewrite Ea; rewrite Eb.
    - apply (Cr2_step _ _ _ ((subst_Tm (up_Val_Val γ) e1) [a..])); [apply Small.s_case_inj1|].
      intros y Hy. assert (Hy' := Stage_later_leq _ _ Hy).
      eapply Cr2_anti; [apply ms_one, Small.s_case_inj1|].
      specialize (H1 y (a .: γ) (a' .: γ') (sem_env2_cons Γ A1 y γ γ' a a'
                    (VV2_smono _ _ _ Hy' _ _ Ha) (sem_env2_smono Γ x y γ γ' Hy' Hγ))).
      asimpl. asimpl in H1. exact H1.
    - apply (Cr2_step _ _ _ ((subst_Tm (up_Val_Val γ) e2) [a..])); [apply Small.s_case_inj2|].
      intros y Hy. assert (Hy' := Stage_later_leq _ _ Hy).
      eapply Cr2_anti; [apply ms_one, Small.s_case_inj2|].
      specialize (H2 y (a .: γ) (a' .: γ') (sem_env2_cons Γ A2 y γ γ' a a'
                    (VV2_smono _ _ _ Hy' _ _ Ha) (sem_env2_smono Γ x y γ γ' Hy' Hγ))).
      asimpl. asimpl in H2. exact H2.
  Qed.

  Lemma rel_unfold v v' A :
    pos var_zero A -> sem_val2 Γ v v' (Mu A) ->
    sem_tm2 Γ (unfold v) (unfold v') (unroll A).
  Proof.
    intros Hp Hv x γ γ' Hγ. specialize (Hv x γ γ' Hγ). auto_unfold in *. cbn [subst_Tm].
    destruct (VV2_unfold _ _ _ _ Hp Hv) as [w [w' [Ea [Eb Hw]]]]. rewrite Ea; rewrite Eb.
    apply (Cr2_step _ _ _ (ret w)); [apply Small.s_unfold|].
    intros y Hy. apply (Cr2_ret _ _ _ _ w').
    + exact (VV2_smono _ _ _ (Stage_later_leq _ _ Hy) _ _ Hw).
    + apply ms_one, Small.s_unfold.
  Qed.
End Compat.

(** ** Fundamental theorem (reflexivity) and adequacy *)

Theorem fundamental2 :
  (forall n (Γ : Ctx n) v A, ptyping_val Γ v A -> sem_val2 Γ v v A) /\
  (forall n (Γ : Ctx n) e A, ptyping Γ e A -> sem_tm2 Γ e e A).
Proof.
  pose proof (ptyping_mutind (fun n Γ v A _ => sem_val2 Γ v v A)
                             (fun n Γ e A _ => sem_tm2 Γ e e A)) as Hs.
  cbv beta in Hs.
  enough (Hall : forall n (Γ : Ctx n),
             (forall v A, ptyping_val Γ v A -> sem_val2 Γ v v A) /\
             (forall e A, ptyping Γ e A -> sem_tm2 Γ e e A))
    by (split; intros n Γ; apply Hall).
  apply Hs; clear Hs; intros.
  - apply rel_var.
  - apply rel_zero.
  - apply rel_succ; assumption.
  - apply rel_prod; assumption.
  - apply rel_inl; assumption.
  - apply rel_inr; assumption.
  - apply rel_abs; assumption.
  - apply rel_rec; assumption.
  - apply rel_fold; assumption.
  - apply rel_unit.
  - apply rel_ret; assumption.
  - eapply rel_let; eassumption.
  - eapply rel_app; eassumption.
  - apply rel_ifz; assumption.
  - eapply rel_prj1; eassumption.
  - eapply rel_prj2; eassumption.
  - eapply rel_case; eassumption.
  - apply rel_unfold; assumption.
Qed.

Theorem adequacy e e' A v :
  sem_tm2 null e e' A -> e ~>* ret v -> exists v', e' ~>* ret v'.
Proof.
  intros H Hs. apply (Cr2_adequate (VV2 A) e e' v); [|exact Hs].
  intros x. assert (Hn : sem_env2 null x var var) by (intros []).
  specialize (H x var var Hn). asimpl in H. exact H.
Qed.
