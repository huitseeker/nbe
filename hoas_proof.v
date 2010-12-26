Add LoadPath "ssreflect041206/group_theories".
Require Arith.
Require Eqdep.
Require Wf_nat.
Require Import Omega.
Require Import finrel.
Require Import ssreflect.
Require Import ssrnat.
Require Import ssrbool.
Require Import eqtype.


Require Import nbe_alpha_conversion.
Require Import nbe_fvc.
Require Import nbe.
Require Import List.

Notation LAM := (Var (mkid 0 (Arr (Arr Iota Iota) Iota))).
Notation APP := (Var (mkid 0 (Arr Iota (Arr Iota Iota)))).

Require Import seq.

Notation SIG := (Seq (mkid 0 (Arr (Arr Iota Iota) Iota)) (mkid 0 (Arr Iota (Arr Iota Iota)))).

Definition object := {t:term | normal t /\ WT t Iota /\ forall x, (FV t x) -> (SIG x)}.

Notation "'lam' x" := (App LAM (decomp (Arr Iota Iota) x)) (at level 69, right associativity).
Notation "'app' x ',' y" := (App (App APP x) y) (at level 70, right associativity).

Eval compute in (lam (fun x => x)).

Eval compute in (app (lam (fun x => x)),(Var (mkid 3 Iota))).

Inductive rred  : term -> term -> Type :=
|red_beta : forall (F: term -> term) (t:term), rred (app (lam F),t) (F t)
|red_lam : forall (F F': term -> term),
  (forall x:term, rred (F x) (F' x)) -> rred (lam F) (lam F')
|red_app1 : forall (e1 e1' e2:term), rred e1 e1' -> rred (app e1,e2) (app e1',e2)
|red_app2 : forall (e1 e2 e2':term), rred e2 e2' -> rred (app e1,e2) (app e1,e2').

Inductive env : Type :=
  | env_empty : env
  | env_push  : env -> term -> ST -> env.

Notation "E & x ~: T" := (env_push E x T) (at level 68).

Inductive env_has : env -> term -> ST -> Prop :=
  | env_has_init : forall E x T,
      env_has (E & x ~: T) x T
  | env_has_push : forall E x y T U,
      env_has E x T -> env_has (E & y ~: U) x T.

Notation "E 'haz' x ~: T" := (env_has E x T) (at level 68).

Inductive op (e:env): term -> ST -> Prop :=
|op_var : forall (x:id) (T:ST), e haz (Var x) ~: T -> op e (Var x) T
|op_lam : forall (T1 T2:ST) (F:term -> term), (forall (x:term), op (e & x ~:T1) (F x) T2) ->  op e (lam F) (Arr T1 T2)
|op_app : forall (T1 T2:ST)(e1 e2:term), op e e1 (Arr T1 T2) -> op e e2 T1 -> op e (app e1,e2) T2.

Axiom extens : forall (f g: term -> term) (x:term), (f x) = (g x) -> f = g.

Definition extends E F :=
  forall x U, E haz x ~: U -> F haz x ~: U.

Notation "E 'inc' F" := (extends E F) (at level 68).

Hint Unfold extends.

Lemma extends_push : forall E F x T,

  E inc F -> (E & x ~: T) inc (F & x ~: T).
rewrite /extends.
intros; inversion H0; constructor; auto.
Qed.


(****************** Substitution in Environments *******************)

Definition env_subst z E F :=
  forall x U, E haz x ~: U -> x <> z -> F haz x ~: U.

Notation "E '\' z 'incl' F" := (env_subst z E F) (at level 67).

Lemma env_subst_init : forall E z S, (E & z ~: S) \ z incl E.
by unfold env_subst; intros; inversion H; auto;
rewrite H1 in H0; contradiction H0.
Qed.

Lemma env_subst_push : forall z E F x U, x <> z ->

  E \ z incl F -> (E & x ~: U) \ z incl (F & x ~: U).
unfold env_subst. intros. inversion H1; constructor; auto.
Qed.

Hint Constructors op rred env_has.

Lemma extends_typing : forall E t T,

  op E t T -> forall F, E inc F -> op F t T.
intros E r T Typt. induction Typt; move => G Hinc; auto.
- apply op_lam; move => x;
  apply (H0 _ _ (extends_push _ _ x T1 Hinc)).
- eauto.
Qed.

Lemma inc_ind : forall (P:env -> Prop),
 (P env_empty) ->
 (forall F E, (E inc F) -> (P E) -> (P F)) ->
 forall E, P E.
Proof.
move => P H0 Hind; elim => [|e IH x T] //=.
apply Hind with e; auto.
Qed.

Axiom narrowing : forall (e : env) (t u : term) (T U: ST), op (e & t ~: T) u U -> op e t T -> op e u U.


Lemma subred : forall (t u:term), (rred t u) -> forall (e:env)(T:ST), (op e t T) -> (op e u T).
Proof.
move => t u; elim.
- move => F t0 e T H; inversion H; clear H0 H1 H3; inversion H2;
  rewrite /gensym H0 in H3; rewrite -(extens _ _ _ H3);
  apply narrowing with t0 T1; trivial.
- move => F F' IHred IHop e; case => [|T1 T2] H; inversion H;
  apply op_lam; move => x; apply IHop;
  rewrite /gensym H0 in H2; rewrite -(extens _ _ _ H2); apply H1.
- by intros; inversion H0; apply op_app with T1; trivial; apply H.
- by intros; inversion H0; apply op_app with T1; trivial; apply H.
Qed.
