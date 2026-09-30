(** * Example: two distinct stream generators are related

    [w1 = λx. fold (λ_. x x)]        [w1 w1 ~>* ret (fold (λ_. w1 w1))]
    [w2 = λx. fold (λ_. (λy. y y) x)]

    Both inhabit [stream := μα. 1 → α] and are "equal" only by coinduction:
    the relation {(s1, s2)} (at every stage) is a post-fixed point.  No
    positivity is needed: [mu2_coind] holds for every recursive type. *)

From CLR Require Import Binary.
Import rec.typing.Notations.

Definition stream : Ty 0 := Mu (Arr Unit (var_Ty var_zero)).

(** The terms are defined at every scope, since they appear under binders. *)
Definition omega {n} : Val n := abs (app (var var_zero) (var var_zero)).
Definition w1 {n} : Val n :=
  abs (ret (fold (abs (app (var (shift var_zero)) (var (shift var_zero)))))).
Definition w2 {n} : Val n :=
  abs (ret (fold (abs (app omega (var (shift var_zero)))))).
Definition s1 : Val 0 := fold (abs (app w1 w1)).
Definition s2 : Val 0 := fold (abs (app omega w2)).

Lemma step_w1 : app w1 w1 ~> ret s1.
Proof.
  exact (Small.s_beta _ _).
Qed.

Lemma step_w2 : app w2 w2 ~> ret s2.
Proof.
  exact (Small.s_beta _ _).
Qed.

(** Calling the right-hand thunk takes three steps. *)
Lemma steps_s2 u : app (abs (app omega w2)) u ~>* ret s2.
Proof.
  apply (@ms_trans _ _ _ (app omega w2)); [exact (Small.s_beta _ _)|].
  apply (@ms_trans _ _ _ (app w2 w2)); [exact (Small.s_beta _ _)|].
  apply ms_one, step_w2.
Qed.

(** The coinductive step: [S = {(s1, s2)}] is a post-fixed point, hence
    [(s1, s2) ∈ V stream] at every stage. [S] appears as the interpretation
    of the recursive variable in the obligation. *)
Lemma s1_s2_related x : VV2 stream x s1 s2.
Proof.
  set (S := fun (_ : Stage) v v' => v = s1 /\ v' = s2).
  refine (mu2_coind (fun M => V2 (Arr Unit (var_Ty var_zero)) (M .: null)) S _ _ x s1 s2 _).
  - intros ? ? _ v v' H. exact H.
  - intros y v v' [-> ->].
    exists (abs (app w1 w1)), (abs (app omega w2)).
    split; [reflexivity|]. split; [reflexivity|]. split.
    + intros u. eexists. apply Small.s_beta.
    + intros z Hz u u' _ e1 St. inversion St; subst.
      apply (Cr2_step _ _ _ (ret s1)); [exact step_w1|].
      intros z' Hz'. apply (Cr2_ret _ _ _ _ s2).
      * split; reflexivity.
      * apply steps_s2.
  - split; reflexivity.
Qed.

(** Hence the two stream generators are related as computations. *)
Theorem w1_w2_related x : CC2 stream x (app w1 w1) (app w2 w2).
Proof.
  apply (Cr2_step _ _ _ (ret s1)); [exact step_w1|].
  intros y _. apply (Cr2_ret _ _ _ _ s2); [apply s1_s2_related|apply ms_one, step_w2].
Qed.
