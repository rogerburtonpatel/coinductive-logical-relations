(** * Clocks: towers as (transfinite) step indices

    The final chain of a monotone function [b] (the predicate [C b] from
    [Coinduction.tower]) is, classically, totally ordered and well-founded
    upwards.  We use its elements as the "stages" of a logical relation:

    - [x ⊏ y] ("[y] is strictly earlier than [x]") replaces [j < k];
    - [loeb] (proved by tower induction) replaces Löb / strong induction
      on step indices.

    The concrete clock [κ] below has the chain [stage 0 ⊐ stage 1 ⊐ ... ⊐
    gfp κ], i.e. ω+1; that is enough for a deterministic language.  Nothing
    except [stage] and [stage_later] depends on the concrete clock. *)

From Stdlib Require Import Classical Arith.
From Coinduction Require Export lattice tower.

(** ** Strict order *)

Section Later.
  Context {X} {L : CompleteLattice X}.

  (** [x ⊏ y]: [y] is strictly above [x] in the chain (an earlier stage). *)
  Definition later (x y : X) := x <= y /\ ~ y <= x.

  Lemma later_leq_l x y z : x <= y -> later y z -> later x z.
  Proof.
    intros Hleqxy [Hleqyz Hnleqyx]. 
    split. 
    - now transitivity y. 
    - intro contra. apply Hnleqyx. now transitivity x. 
Qed.   

  Lemma later_leq_r x y z : later x y -> y <= z -> later x z.
  Proof.
    intros [Hleqxy Hnleqyx] Hleqyz. 
    split. 
    - now transitivity y. 
    - intro contra. apply Hnleqyx. now transitivity z. 
  Qed. 
End Later.

(** ** Linearity of the final chain *)

Section Linear.
  Context {X} {L : CompleteLattice X} (b : mon X).

  Lemma chain_pfp x : C b x -> b x <= x.
  Proof. intro Cx. exact (b_chain (chain Cx)). Qed.

  (** [c] is _extreme_ if for every chain element [x] strictly above [c], 
      [b x] is also above [c].
      informally, this means that applying [b] can't 'skip past' [c]. 
      This is also the dual of Bourbaki–Witt. *)
  Definition extreme (c : X) :=
    forall x, C b x -> later c x -> c <= b x.

  Lemma extreme_split c : C b c -> extreme c ->
    forall x, C b x -> c <= x \/ x <= b c.
  Proof.
    intros Cc Ec x Cx.
    induction Cx as [x Cx IH | T HT IH].
    - destruct IH as [H|H].
      + destruct (classic (x <= c)) as [H'|H'].
        * right. apply (Hbody b). exact H'.
        * left. apply Ec; [exact Cx|split; assumption].
      + right. apply (Hbody b). etransitivity; [exact H|]. apply chain_pfp, Cc.
    - destruct (classic (forall t, T t -> c <= t)) as [H|H].
      + left. apply inf_spec. exact H.
      + right. apply not_all_ex_not in H. destruct H as [t Ht].
        apply imply_to_and in Ht. destruct Ht as [Tt Hct].
        destruct (IH t Tt) as [H|H]; [contradiction|].
        etransitivity; [|exact H]. apply leq_infx. exact Tt.
  Qed.

  Lemma chain_extreme c : C b c -> extreme c.
  Proof.
    intro Cc. induction Cc as [c Cc IH | T HT IH].
    - intros x Cx [H1 H2].
      destruct (extreme_split c Cc IH x Cx) as [H|H].
      + apply (Hbody b). exact H.
      + contradiction.
    - intros x Cx [H1 H2].
      assert (Ht : exists t, T t /\ ~ x <= t).
      { apply NNPP. intro N. apply H2. apply inf_spec. intros t Tt.
        apply NNPP. intro N'. apply N. eauto. }
      destruct Ht as [t [Tt Hxt]].
      destruct (extreme_split t (HT t Tt) (IH t Tt) x Cx) as [H|H].
      + etransitivity. apply leq_infx, Tt. apply (IH t Tt x Cx). split; assumption.
      + exfalso. apply Hxt. etransitivity; [exact H|]. apply chain_pfp, HT, Tt.
  Qed.

  (** Every chain element is either above [c] or below [b c]. *)
  Theorem chain_split c x : C b c -> C b x -> c <= x \/ x <= b c.
  Proof.
      intros Cc Cx. exact (extreme_split c Cc (chain_extreme c Cc) x Cx).
  Qed.

  (** The final chain is totally ordered.  This is already in the library as
      [companion.chain.C_linear] (proved differently, via [Cflat]); we derive
      it from [chain_split] as the flow is slightly nicer that way. *)
  Corollary chain_total x y : C b x -> C b y -> x <= y \/ y <= x.
  Proof.
    intros Cx Cy. destruct (chain_split x y Cx Cy) as [H|H]; [left; exact H|right].
    etransitivity; [exact H|]. apply chain_pfp, Cx.
  Qed.

  (** Löb induction = tower induction.  To prove [P] at a stage one may
      assume it at all strictly earlier stages. *)
  Theorem loeb (P : Chain b -> Prop) :
    (forall x : Chain b, (forall y : Chain b, later (elem x) (elem y) -> P y) -> P x) ->
    forall x : Chain b, P x.
  Proof.
      intros H x.
    enough (G : forall z, C b z -> forall y : Chain b, z <= elem y -> P y)
      by (apply (G _ (Celem x)); reflexivity).
    intros z Cz. induction Cz as [z Cz IH | T HT IH]; intros y Hy;
      apply H; intros w [Hyw Hwy].
    - destruct (classic (z <= elem w)) as [Hzw|Hzw]; [apply IH, Hzw|].
      destruct (chain_split z (elem w) Cz (Celem w)) as [?|Hw]; [contradiction|].
      exfalso. apply Hwy. etransitivity; [exact Hw|exact Hy].
    - destruct (classic (exists t, T t /\ t <= elem w)) as [[t [Tt Htw]]|N].
      + eapply IH; eauto.
      + exfalso. apply Hwy. etransitivity; [|exact Hy]. apply inf_spec. intros t Tt.
        destruct (chain_total t (elem w) (HT t Tt) (Celem w)) as [?|?];
          [exfalso; eauto|assumption].
  Qed.
End Linear.

(** ** The concrete clock *)

(** [κ Z] shifts [Z] by one: its chain is [{n | k <= n}] for each [k],
    followed by the empty set. *)
Program Definition κ : mon (nat -> Prop) :=
  {| body Z n := match n with 0 => False | S m => Z m end |}.
Next Obligation.
  intros Z Z' H n. destruct n; cbn; [intro f; exact f|apply H].
Qed.

Definition Stage := Chain κ.

Notation "x ⊑ y" := (elem x <= elem y) (at level 70).
Notation "x ⊏ y" := (later (elem x) (elem y)) (at level 70).

Lemma Stage_refl (x : Stage) : x ⊑ x.
Proof. reflexivity. Qed.

Lemma Stage_trans (x y z : Stage) : x ⊑ y -> y ⊑ z -> x ⊑ z.
Proof. intros; etransitivity; eauto. Qed.

Lemma Stage_later_leq (x y : Stage) : x ⊏ y -> x ⊑ y.
Proof. intros [H _]. exact H. Qed.

Lemma Stage_later_trans_l (x y z : Stage) : x ⊑ y -> y ⊏ z -> x ⊏ z.
Proof. apply later_leq_l. Qed.

Lemma Stage_later_trans_r (x y z : Stage) : x ⊏ y -> y ⊑ z -> x ⊏ z.
Proof. apply later_leq_r. Qed.

Definition Stage_loeb := @loeb _ _ κ.

(** The finite stages. [stage 0] is [top]. *)
Fixpoint stage (k : nat) : Stage :=
  match k with
  | 0 => chain (Cinf (T := bot) (leq_bx _))
  | S k => chain_b (stage k)
  end.

Lemma stage_spec k n : elem (stage k) n <-> (k <= n)%nat.
Proof.
  revert n. induction k; intros n.
  - cbn. split; [intros; apply le_0_n|]. intros _ i [].
  - destruct n; cbn.
    + split; [tauto|]. intro H; inversion H.
    + rewrite IHk. split; [apply le_n_S|apply le_S_n].
Qed.

(** Every step of the clock is strict: [stage (S k)] is strictly later. *)
Lemma stage_later k : stage (S k) ⊏ stage k.
Proof.
  split.
  - apply (b_chain (stage k)).
  - intro H. assert (Hk : elem (stage k) k) by (apply stage_spec; constructor).
    apply H, stage_spec in Hk. exact (Nat.lt_irrefl k Hk).
Qed.
