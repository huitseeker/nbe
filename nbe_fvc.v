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
Require Import List.
Require Import seq.

(**************************************)
(* dummy variable in decomp treatment *)
(**************************************)

(**
  [gen_eq c as x H] takes all occurrences of [c] in the current goal's
  conclusion, replaces them by the variable [x], and introduces the equality
  [x = c] as the hypothesis H.  Useful if one needs to generalize the goal
  prior to applying an induction tactic.
*)

Tactic Notation "gen_eq" constr(c) "as" ident(x) ident(H) :=
  set (x := c); assert (H : x = c) by reflexivity; clearbody x.

(**
  A variation on the above in which all occurrences of [c] in the goal are
  replaced, not only those in the conclusion.
*)

Tactic Notation "gen_eq" constr(c) "as" ident(x) :=
  set (x := c) in *;
  let H := fresh in (assert (H : x = c) by reflexivity; clearbody x; revert H).

(** [gen] is a shortname for the [generalize dependent] tactic. *)

Tactic Notation "gen" ident(X1) :=
  generalize dependent X1.

(**************************************************************************)
(* Our goal is to prove the lemma fvc below, not just on terms that do not*)
(*contain x as a free variable, but on all terms.*)
(**************************************************************************)

Lemma fvc : forall t t' x y, x notin (FV t) ->
 conv (App t (Var x)) t' -> (y notin (FV t') -> exists t'', conv t t'' /\ ~~(FV t'' y)).
move => t t' x y Hfvx Hconv Hfvy; exists (Lam x t'); split.
apply ctrans with (Lam x (App t (Var x))).
- by apply ceta.
- by apply clam.
rewrite FV_lam_bool; case e: (FV t' y);
[by move /negP: Hfvy => Hfvy; contradiction Hfvy| by trivial].
Qed.

Inductive lambdacongr (R : term -> term -> Prop) : term -> term -> Prop :=
| cstep : forall t u, R t u -> lambdacongr R t u
| cglam : forall x t u, lambdacongr R t u -> lambdacongr R (Lam x t) (Lam x u)
| cgapp1 : forall t u v, lambdacongr R t u -> lambdacongr R (App t v) (App u v)
| cgapp2 : forall t u v, lambdacongr R t u -> lambdacongr R (App v t) (App v u).

Inductive ibeta : term -> term -> Prop :=
 | icbeta : forall t u x, ibeta (App (Lam x t) u)(subst t ((x,u) :: nil)).

Inductive ieta : term -> term -> Prop :=
| iceta : forall x t, x notin (FV t) -> ieta (Lam x (App t (Var x))) t.

Inductive iconv : term -> term -> Prop :=
| ialpha : forall t u, alphac t u -> iconv t u
| iibeta : forall t u, lambdacongr ibeta t u -> iconv t u
| iieta : forall t u, lambdacongr ieta t u -> iconv t u.

Hint Constructors lambdacongr ibeta ieta iconv.

Lemma renam_lam_inv: forall t x y x0 t0,
  (Lam x0 t0) = t [(x, Var y)::nil] ->
  exists x1, exists t1, (Lam x1 t1) = t.
elim => [i0 | i t IH | u IHu v IHv] x y x0 t0; try solve [rewrite //=].
by rewrite /subst /tassoc; case (x == i0) => H; inversion H.
by exists i; exists t.
Qed.

Lemma renam_inv: forall t x y x0 t0 u0,
  (App (Lam x0 t0) u0) = t [(x, Var y)::nil] ->
  exists x1, exists t1, exists u1, (App (Lam x1 t1) u1) = t.
elim => [i0 | [i T] t IH | u IHu v IHv] x y x0 t0 u0 //=.
by case (x == i0) => H; inversion H.
by move => H; inversion H; move : (renam_lam_inv u x y x0 t0 H1) => {H H1} H1;
inversion H1; inversion H; exists x1; exists x2; exists v; rewrite H0.
Qed.

Lemma FV_eta : forall t x y, x notin (FV t) ->
  ((FV (Lam x (App t (Var x)))) y <-> ((x!=y) && (FV t) y)).
by move => t x y H; rewrite /FV -/FV filter_cat {2}/seq.filter /setC1 eq_refl cats0 mem_filter /setI.
Qed.

Lemma FV_eta_sigma : forall t x y sigma, x notin (FV t) -> ~~((FV (tassoc x sigma)) y) ->
  ((FV ((Lam x (App t (Var x))) [sigma]))  y <-> (FV (t[sigma])) y).
move => t x y sigma H Hy;  rewrite -!FV_in; split;
move => H0; inversion H0 as [x0 H1]; move/andP: H1 => [H1 H2].
  by rewrite FV_eta in H1 => //=; move/andP: H1 => [H1 H3]; exists x0; apply/andP; auto.
  by exists x0; rewrite H2 andbT FV_eta //= H1 andbT; case e:(x == x0); [
     move/negP: Hy; move/eqP: e =>->; contradiction|trivial].
Qed.

Lemma ifvc : forall x y t t',
 iconv (App t (Var x)) t' -> (y notin (FV t') -> exists t'', iconv t t'' /\ ~~(FV t'' y)).
move => x y t t' Hiconv; inversion Hiconv.
- by move => Hfv; rewrite -(FV_alpha (App t (Var x)) t' H) in Hfv; rewrite /FV -/FV mem_cat /setU in Hfv;
  move/norP: Hfv => [Hfv1 Hfv2]; exists t; auto.
- gen_eq (App t (Var x)) as mu; gen t => {t0 u H0 H1};
  elim H => [t0 u0 Hr t | x0 t0 u0 Hr IH t| t0 u0 v0 Hr IH t| t0 u0 v0 Hr IH t] Heq.
  - by move : Heq Hr => -> Hr; inversion Hr;
    move => Hfv; exists (Lam x0 t1); split; [auto|rewrite FV_lam_bool];
    casebool e: (x0 == y); [
      rewrite andbF; auto |
      rewrite andbT; casebool f: (FV t1 y); [
          contradictionbool Hfv; rewrite -FV_in; exists y; apply/andP; split; [
            trivial |
            rewrite //= e  //= /setU1 eq_refl //=
          ]
        | trivial
      ]
    ].
  - by inversion Heq.
  - by inversion Heq; move => Hfv; exists u0; split; [rewrite H1 in Hr; auto|
    rewrite /FV -/FV mem_cat /setU in Hfv; move/norP: Hfv => {Hfv}[Hfv1 Hfv2]].
  - by inversion Heq; move => Hfv; exists v0; split; [rewrite -H1; auto|
    rewrite /FV -/FV mem_cat /setU in Hfv; move/norP: Hfv => {Hfv}[Hfv1 Hfv2]; rewrite H1].
- gen_eq (App t (Var x)) as mu; gen t => {t0 u H0 H1}.
  elim H => [t0 u0 Hr t | x0 t0 u0 Hr IH t| t0 u0 v0 Hr IH t| t0 u0 v0 Hr IH t] Heq.
  - move : Heq Hr => -> Hr; inversion Hr.
  - by inversion Heq.
  - by move => Hfv; inversion Heq; exists u0; split; [rewrite -H1; apply iieta; auto
       | rewrite /FV -/FV mem_cat /setU //= in Hfv; move/norP: Hfv => [Hfv1 Hfv2]].
  - by move => Hfv; inversion Heq; exists v0; split; [rewrite H1; apply ialpha; auto
      |rewrite /FV -/FV mem_cat /setU //= in Hfv; move/norP: Hfv => [Hfv1 Hfv2]].
Qed.

Lemma subst_renaming_nil : forall v sigma,
  is_renaming sigma ->
  v[nil@sigma] = v[sigma].
move => v sigma Hsigma; apply tassoc_sigma_equiv_equal; move => x2 Hfvx2 //=;
change ((Var x2) [nil@sigma] = (Var x2) [sigma]);
rewrite -subst_comp_unfold //=;
move : (renaming_tassoc_inv _ x2 Hsigma) => [y1 ->] //=.
Qed.

Lemma renaming_lam_inv: forall t sigma x0 t0,
  is_renaming sigma ->
  (Lam x0 t0) = t [sigma] ->
  exists x1, exists t1, (Lam x1 t1) = t.
elim => [i0 | i t IH | u IHu v IHv] sigma x0 t0 H0; try solve [rewrite //=].
by rewrite //=; move : (renaming_tassoc_inv sigma i0 H0) => [y ->]; move => H; inversion H.
by exists i; exists t.
Qed.

Lemma renaming_app_inv : forall t sigma u v,
  is_renaming sigma ->
  (App u v) = t[sigma] ->
  exists u1, exists v1, (App u1 v1) = t.
elim => [i0 | [i T] t IH | u IHu v IHv] sigma x0 t0 H0; try solve [rewrite //=].
by rewrite //=; move : (renaming_tassoc_inv sigma i0 H0) => [y ->]; move => H; inversion H.
by exists u; exists v.
Qed.

Lemma renaming_inv: forall t sigma x0 t0 u0,
  is_renaming sigma ->
  (App (Lam x0 t0) u0) = t [sigma] ->
  exists x1, exists t1, exists u1, (App (Lam x1 t1) u1) = t.
elim => [i0 | [i T] t IH | u IHu v IHv] sigma x0 t0 u0 H0 //=.
by rewrite //=; move : (renaming_tassoc_inv sigma i0 H0) => [y ->]; move => H; inversion H.
by move => H; inversion H; move : (renaming_lam_inv u sigma x0 t0 H0 H2) => {H H2} H2;
inversion H2; inversion H; exists x; exists x1; exists v; rewrite H1.
Qed.

Require Import Relation_Operators.
Require Import Operators_Properties.

Inductive clos_refl_s_trans (A:Type) (R: A -> A -> Prop)  : A-> A -> Prop :=
    | st_refl : forall x, clos_refl_s_trans A R x x
    | st_trans :
        forall x y z:A, R x y -> clos_refl_s_trans A R y z -> clos_refl_s_trans A R x z.

Implicit Arguments clos_refl_s_trans [A].

Hint Constructors clos_refl_s_trans.

Lemma R_in_clos_refl_s_trans : forall A (R: A -> A -> Prop) (x y:A),
 R x y -> clos_refl_s_trans R x y.
eauto.
Qed.

Hint Resolve R_in_clos_refl_s_trans.

Definition ticonv := clos_refl_s_trans iconv.

Hint Unfold ticonv.

Lemma alphac_var_inv : forall t x,
  alphac (Var x) t ->
  exists y, t = Var y.
move => t x; rewrite alpha_norm_equiv; gen x; gen t.
elim => [i | [i T] t0 IH | u IHu v IHv]; eauto; intros; by inversion H.
Qed.

Lemma alphac_lam_inv : forall t i0 T0 t0,
  alphac (Lam (i0^^T0) t0) t ->
  exists x, exists u, t = (Lam (x^^T0) u).
move => t i0 T0 t0; rewrite alpha_norm_equiv; gen t0; gen i0; gen t.
elim => [i | [i T] t IH | u IHu v IHv]; eauto; intros;
inversion H as [[Hbinds Htypes Hbody]]; rewrite -Htypes; eauto.
Qed.

Lemma alphac_app_inv : forall t u0 v0,
  alphac (App u0 v0) t ->
  exists u, exists v, t = (App u v).
move => t u0 v0; rewrite alpha_norm_equiv; gen v0; gen u0; gen t.
elim => [i | [i T] t IH | u IHu v IHv]; eauto; intros; by inversion H.
Qed.

Lemma alphac_renaming_lam_inv: forall t sigma x0 T0 t0,
  is_renaming sigma ->
  alphac (Lam (x0^^T0) t0)  (t [sigma]) ->
  exists x1, exists t1, alphac (Lam (x1^^T0) t1) t.
elim => [i0 | [i T] t IH | u IHu v IHv] sigma x0 T0 t0 H0.
by rewrite //=; move : (renaming_tassoc_inv sigma i0 H0) => [y ->]; rewrite alpha_norm_equiv; move => H; inversion H.
by exists i; exists t;
   rewrite //= alpha_norm_equiv in H; inversion H as [[Hbind Htypes Hbody]].
by rewrite /subst -/subst; rewrite alpha_norm_equiv; move => H; inversion H.
Qed.

Lemma alphac_renaming_app_inv : forall t sigma u v,
  is_renaming sigma ->
  alphac (App u v) (t[sigma]) ->
  exists u1, exists v1, alphac (App u1 v1) t.
move => t sigma u v Hsigma Halpha.
move : (alphac_app_inv _ _ _ Halpha) => [u0 [v0 Halpha']].
symmetry in Halpha'; move : (renaming_app_inv _ sigma _ _ Hsigma Halpha') => [u1 [v1 Heq]].
exists u1; exists v1; rewrite -Heq; trivial.
Qed.

Lemma alphac_renaming_inv: forall t sigma x0 t0 u0,
  is_renaming sigma ->
  alphac (App (Lam x0 t0) u0) (t [sigma]) ->
  exists x1, exists t1, exists u1, alphac (App (Lam x1 t1) u1) t.
elim => [i0 | [i T] t IH | u IHu v IHv] sigma [x0 T0] t0 u0 H0 //=.
by rewrite //=; move : (renaming_tassoc_inv sigma i0 H0) => [y ->]; rewrite alpha_norm_equiv; move => H; inversion H.
by rewrite alpha_norm_equiv; move => H; inversion H.
by rewrite alpha_norm_equiv => H; inversion H; change ((Lam (x0^^T0) t0)[nil] = (u[sigma])[nil]) in H2;
   rewrite -alpha_norm_equiv in H2; move : (alphac_renaming_lam_inv _ _ _ _  _ H0 H2) => [x1 [t1 Hlam]];
   rewrite -alpha_norm_equiv in H3; exists (x1^^T0); exists t1; exists v; apply aapp1.
Qed.

Lemma alphac_app_inj : forall t1 t2 u1 u2,
  alphac (App t1 t2) (App u1 u2) -> alphac t1 u1 /\ alphac t2 u2.
move => t1 t2 u1 u2.
rewrite !alpha_norm_equiv /subst -/subst => Ha; inversion Ha; split; auto.
Qed.

Lemma alphac_lam_inj : forall x y t u,
  alphac (Lam x t) (Lam y u) -> alphac (t [(x, Var y)::nil]) u.
move => [x T] [y U] t u Ha.
rewrite alpha_norm_equiv //= in Ha.
inversion Ha as [[Hbind Htypes Hbody]].
apply atrans with ((t
          [(x ^^ U,
           Var
             (max_ident
                (eFVS (seq.filter (setC1 (d:=idd) (y ^^ U)) (FV u)) nil) U
              ^^ U)) :: nil])[(
             (max_ident
                (eFVS (seq.filter (setC1 (d:=idd) (y ^^ U)) (FV u)) nil) U)^^U, Var (y^^U))::nil]).
- apply asym; apply subst_collapse_inv; last by rewrite -Hbind Htypes;
  move : (gensym_gen (eFVS (FV (Lam (x ^^ U) t)) nil) U)=> //=.
- rewrite -Htypes in Hbody; rewrite /gensym Hbind Htypes in Hbody; rewrite Hbody.
  rewrite subst_head_collapse;
  last by move: (gensym_gen (eFVS (seq.filter (setC1 (d:=idd) (y ^^ U)) (FV u)) nil) U);
  rewrite eFVS_nil => //=.
  rewrite alpha_norm_equiv subst_comp_unfold; apply tassoc_sigma_equiv_equal => x1 Hfvx1.
  by rewrite subst_comp_comm_tassoc //=; casebool e: (y ^^U == x1); try move/eqP : e => <-.
Qed.

Lemma alphac_lam_binds : forall x y t u,
  alphac (Lam x t) (Lam y u) -> y notin (FV (Lam x t)).
by move => x y t u Halpha; rewrite ((FV_alpha _ _ Halpha) y) FV_lam_bool eq_refl andbF.
Qed.

Lemma alphac_renaming_inv2: forall v sigma x1 T1 u0,
  is_renaming sigma ->
  ~~ FV u0 (x1 ^^ T1) ->
  alphac (v [sigma]) (Lam (x1 ^^ T1) (App u0 (Var (x1 ^^ T1)))) ->
  exists x2, exists u, (alphac v (Lam (x2^^T1) (App u (Var (x2^^T1)))) /\ (x2^^T1) notin (FV u)).
elim => [i0 | [i T] t IH | u IHu v IHv] sigma x1 T1 u0 Hsigma Hfv Halpha //=;
last by rewrite //= alpha_norm_equiv //= in Halpha.
- by rewrite //= in Halpha; move : (renaming_tassoc_inv sigma i0 Hsigma) => [x2 Heq];
  rewrite Heq alpha_norm_equiv //= in Halpha.
have ee: (alphac (t[(i^^T,Var (x1^^T1))::sigma]) (App u0 (Var (x1 ^^ T1))));
first by apply atrans with ((t
       [(i ^^ T,
        Var
          (gensym (eFVS (seq.filter (setC1 (d:=idd) (i ^^ T)) (FV t)) sigma)
             T)) :: sigma])
      [(gensym (eFVS (seq.filter (setC1 (d:=idd) (i ^^ T)) (FV t)) sigma) T,
       Var (x1 ^^ T1)) :: nil]);
[apply asym; apply subst_collapse_inv; apply gensym_gen|apply (alphac_lam_inj _ _ _ _ Halpha)].
have ff : (is_renaming ((i^^T, Var (x1^^T1))::sigma)); first by trivial.
move : (alphac_renaming_app_inv _ _ _ _ ff (asym _ _ ee)) => {ff}[u1 [v1 gg]].
move : (alphac_app_inv _ _ _ gg) => [t1 [t2 Heq]].
rewrite Heq; rewrite Heq in gg,ee.
rewrite //= in ee; move : (alphac_app_inj _ _ _ _ ee) => [hh ii].
rewrite alpha_norm_equiv //= subst_comp_unfold subst_renaming_nil //= in ii.
gen t2; elim => [[i0 T0] | [i0 T0] t0 IH0 | u IHu v IHv] Heq gg ee;
try solve [by move => ii; inversion ii].
rewrite //=; casebool e : (i^^T == i0^^T0).
- by rewrite //= alpha_norm_equiv in Halpha; inversion Halpha as [[Hbinds Htypes Hbody]];
  exists i; exists t1; split; [move/eqP: e =><-; rewrite -Htypes; apply arefl |
  rewrite -(FV_alpha _ _ hh (x1^^T1)) in Hfv; casebool f: (FV t1 (i^^T1));
  [contradictionbool Hfv; rewrite -FV_in; exists (i^^T1); rewrite f andTb //=;
  rewrite -Htypes; rewrite eq_refl //= /setU1 orbF eq_refl|trivial]].
- rewrite //= e in ee => Heq2; rewrite Heq //= e Heq2 in Halpha.
  have ff: (x1^^T1 notin FV(Lam (x1 ^^ T1) (App u0 (Var (x1 ^^ T1)))));
  first by rewrite FV_lam_bool eq_refl andbF.
  rewrite -(FV_alpha _ _ Halpha (x1^^T1)) in ff; rewrite FV_lam_bool in ff;
  move: ff; casebool f:(gensym
              (eFVS
                 (seq.filter (setC1 (d:=idd) (i ^^ T))
                    (cat (FV t1) (Seq (i0 ^^ T0)))) sigma) T ==
            x1 ^^ T1); first by
  move : (gensym_gen (eFVS
            (seq.filter (setC1 (d:=idd) (i ^^ T))
               (cat (FV t1) (Seq (i0 ^^ T0)))) sigma) T) => g; contradictionbool g;
  rewrite -eFVS_in; exists (i0^^T0); rewrite /setC1 in f;
  rewrite  mem_filter /setI mem_cat /setC1 e /setU //= /setU1 eq_refl orbT Heq2 //= /setU1 orbF eq_sym f.
  by rewrite andbT //= mem_cat /setU /= /setU1 eq_refl orbT.
Qed.

Require Import Operators_Properties.

(* will proceed by equivalence with reflexive transitive closure to use ind. principle & associated lemmas *)

(* shameless adaptation from Operator.Properties*)
Lemma clos_refl_trans_ind_right :
      forall (A:Type) (R:A -> A -> Prop) (M:A) (P:A -> Prop),
        P M ->
        (forall P0 N:A, clos_refl_trans A R P0 M -> P P0 -> R N P0 -> P N) ->
        forall a:A, clos_refl_trans A R a M -> P a.
    Proof.
      intros.
      generalize H H0.
      clear H H0.
      elim H1; intros; auto with sets.
      apply H2 with y; auto with sets.

      apply H0.
      apply H3; auto with sets.

      intros.
      apply H5 with P0; auto with sets.
      apply rt_trans with y; auto with sets.
    Qed.

Lemma clos_refl_s_trans_equiv_clos_refl_trans : forall t u,
  ticonv t u <-> clos_refl_trans term iconv t u.
move => t u; rewrite /ticonv; split => H.
- elim H.
  - by apply rt_refl.
  - by intros; apply rt_trans with y; [apply rt_step|trivial].
- gen t; apply clos_refl_trans_ind_right.
  - apply st_refl.
  - by intros; apply st_trans with P0.
Qed.

(* congruence properties *)

Lemma clos_refl_trans_lam : forall t u x0,
  clos_refl_trans term iconv t u ->
  clos_refl_trans term iconv (Lam x0 t) (Lam x0 u).
move => t u x0 Hconv;
  elim Hconv => [x y Hconvxy| x | x y z Hconvxy IHy Hconvyz IHz ].
- by apply rt_step; inversion Hconvxy;
  [apply ialpha; apply alam| apply iibeta; apply cglam|apply iieta; apply cglam].
- by apply rt_refl.
- by apply rt_trans with (Lam x0 y).
Qed.

Lemma clos_refl_trans_app1 : forall t u x0,
  clos_refl_trans term iconv t u ->
  clos_refl_trans term iconv (App t x0) (App u x0).
move => t u x0 Hconv;
  elim Hconv => [x y Hconvxy| x | x y z Hconvxy IHy Hconvyz IHz ].
- by apply rt_step; inversion Hconvxy;
  [apply ialpha; apply aapp1| apply iibeta; apply cgapp1|apply iieta; apply cgapp1].
- by apply rt_refl.
- by apply rt_trans with (App y x0).
Qed.

Lemma clos_refl_trans_app2 : forall t u x0,
  clos_refl_trans term iconv t u ->
  clos_refl_trans term iconv (App x0 t) (App x0 u).
move => t u x0 Hconv;
  elim Hconv => [x y Hconvxy| x | x y z Hconvxy IHy Hconvyz IHz ].
- by apply rt_step; inversion Hconvxy;
  [apply ialpha; apply aapp2| apply iibeta; apply cgapp2|apply iieta; apply cgapp2].
- by apply rt_refl.
- by apply rt_trans with (App x0 y).
Qed.

(* decreasing number of free vars along iconv *)

Lemma FV_congr_dec : forall (R:term -> term -> Prop),
  (forall t u, R t u -> (forall x, FV u x -> FV t x)) ->
  forall t u,
    lambdacongr R t u -> (forall x, FV u x -> FV t x).
move => R H t u; elim => [t0 u0 Hr| x0 t0 u0 Hr IH| t0 u0 v0 Hr IH| t0 u0 v0 Hr IH] x.
by apply H.
by rewrite !FV_lam_bool; casebool e: (x0 == x); try solve [by rewrite andbF];
rewrite !andbT; apply IH.
by rewrite //= !mem_cat /setU => Hfv; move/orP: Hfv => [Hfv|Hfv]; apply/orP; [left; apply IH|right; trivial].
by rewrite //= !mem_cat /setU => Hfv; move/orP: Hfv => [Hfv|Hfv]; apply/orP; [left; trivial|right; apply IH].
Qed.

Lemma FV_iconv_dec : forall t u,
  iconv t u ->
  forall x, (FV u) x -> (FV t) x.
move => t u Hconv; elim Hconv => t0 u0 Hr.
by move => x Hfv; rewrite (FV_alpha _ _ Hr).
- apply (FV_congr_dec ibeta); last by trivial.
  move => t1 u1; elim => [t2 u2 x x0] //=;
  rewrite -FV_in;  move => [x1 Hfv]; move/andP: Hfv => [Hfv1 Hfv2]; move: Hfv2;
  rewrite mem_cat /setU mem_filter /setI /setC1 /tassoc;
  casebool e: (x == x1) => //= Hfv2; apply/orP; [right; trivial|left];
  rewrite /setU1 orbF in Hfv2; move/eqP : Hfv2 =><-; apply/andP; split; auto;
  by apply /negP; rewrite e.
- apply (FV_congr_dec ieta); last by trivial.
  move => t1 u1; elim => [x t2 Hfvx] x0 //=;
  rewrite mem_filter /setI /setC1 mem_cat /setU //= /setU1 orbF;
  move => H; casebool e: (x == x0);
  [rwbooleqrev e in H; contradictionbool Hfvx|rewrite andTb orbF; trivial].
Qed.

Lemma FV_clos_refl_trans_dec : forall (R:term -> term -> Prop),
  (forall t u, R t u -> (forall x, FV u x -> FV t x)) ->
  forall t u,
    clos_refl_trans term R t u -> (forall x, FV u x -> FV t x).
move => R H t u; elim =>//=.
by move => x y z HRxy Hfvxy Hryz Hfvyz x0 Hfv; apply Hfvxy; apply Hfvyz.
Qed.

Lemma FV_ticonv_dec : forall t u,
  ticonv t u -> (forall x, FV u x -> FV t x).
  rewrite /ticonv; move => t u Hconv; rewrite clos_refl_s_trans_equiv_clos_refl_trans in Hconv.
  apply (FV_clos_refl_trans_dec iconv FV_iconv_dec _ _ Hconv).
Qed.

(* subst comm conv on iconv was constricted for need of subst normalization in sigma-passing terms *)

Lemma subst_comm_crt_iconv : forall t u sigma,
  is_renaming sigma ->
 clos_refl_trans term iconv (t[sigma]) u -> exists v, clos_refl_trans term iconv t v /\ alphac (v[sigma]) u.
move => t u sigma Hsigma Hconv; gen u; apply clos_refl_trans_ind_left.
by exists t; split; auto; apply rt_refl.
move => x y Hconvs [v [Hvconv Hvalpha]] Hconv; inversion Hconv;
[by exists v; split; auto; apply atrans with x
|move => {t0 H0 u0 H1}; gen t; gen v; gen sigma
|move => {t0 H0 u H1}; gen t; gen v; gen sigma];
elim H => [t0 u0 Hr | [x0 T0] t0 u0 Hr IH| t0 u0 v0 Hr IH| t0 u0 v0 Hr IH] sigma Hsigma v Halpha t Hcs Hc;
try solve [
(* congruent lambda case *)
    move : (alphac_renaming_lam_inv v sigma _ _ _ Hsigma (asym _ _ Halpha)) => [i1 [t1 H0]];
    rewrite -(alpha_norm _ _ H0 sigma) //= in Halpha;
      move : (alphac_lam_binds _ _ _ _ Halpha) => Hbinds; move : (alphac_lam_inj _ _ _ _ Halpha) => Halpha';
    have ff : (alphac (t1 [(i1 ^^ T0, Var (x0^^T0)) :: sigma]) t0); [
    apply atrans with ((t1 [(i1 ^^ T0, Var (gensym (eFVS (seq.filter (setC1 (d:=idd) (i1 ^^ T0)) (FV t1))
      sigma) T0)) :: sigma])
      [(gensym (eFVS (seq.filter (setC1 (d:=idd) (i1 ^^ T0)) (FV t1)) sigma) T0, Var (x0 ^^ T0)) :: nil]);
    [apply asym; apply subst_collapse_inv;
      move : (gensym_gen (eFVS (seq.filter (setC1 (d:=idd) (i1 ^^ T0)) (FV t1)) sigma) T0) =>//=|trivial]|
    have ee : (is_renaming ((i1 ^^ T0, Var (x0 ^^ T0)) :: sigma)); [move => //=|
    move : (IH ((i1 ^^ T0, Var (x0 ^^ T0)) :: sigma) ee t1 ff t1
      (rt_step term iconv _ _  (ialpha _ _ ff)) (rt_refl term iconv t1)) => [u1 [Hu1_conv Hu1_alpha]];
    exists (Lam (i1^^T0) u1); split; [
      apply rt_trans with v; [trivial|
      by apply rt_trans with (Lam (i1^^T0) t1); [apply rt_step; apply ialpha; apply asym; trivial| apply clos_refl_trans_lam]]|
     apply atrans with (Lam (x0^^T0) (u1 [(i1^^T0, Var (x0^^T0))::sigma])); [
       apply lam_alpha; change (~~ FV ((Lam (i1^^T0) t1)[sigma]) (x0^^T0)) in Hbinds;
        apply/negP; rewrite eFVS_FV; apply/negP;
          by casebool f: (FV (Lam (i1 ^^ T0) u1 [sigma]) (x0 ^^ T0)); [contradictionbool Hbinds|trivial];
          rewrite -FV_in in f; move: f => [x1 Hfvx1]; move/andP: Hfvx1 => [Hfvx1u1 Hfvassoc];
            move : (clos_refl_trans_lam _ _ (i1^^T0) Hu1_conv) => Hlamu1_conv;
              move: (FV_clos_refl_trans_dec iconv FV_iconv_dec _ _ Hlamu1_conv x1 Hfvx1u1) => {Hlamu1_conv Hfvx1u1} Hfvx1t1;
                by rewrite -FV_in; exists x1; apply/andP; split|
       by apply alam]]]]
|(*congruent left application case*)
    move : (alphac_app_inv _ _ _ (asym _ _ Halpha)) => [u1 [v1 Heq]]; symmetry in Heq;
    move : (renaming_app_inv _ sigma _ _ Hsigma Heq) => {u1 v1 Heq} [u1 [v1 Heq]];
    rewrite -Heq in Halpha;
    move : (alphac_app_inj _ _ _ _ Halpha) => [Halphau1 Halphav1];
    move : (IH sigma Hsigma u1 Halphau1 u1
      (rt_step term iconv _ _ (ialpha _ _ Halphau1)) (rt_refl term iconv u1)) => [u2 [Hu2_conv Hu2_alpha]];
    by exists (App u2 v1); split;
      [apply rt_trans with (App u1 v1); [rewrite -Heq in Hc| apply clos_refl_trans_app1]
      |rewrite //=; apply atrans with (App u0 (v1[sigma])); auto]
|(*congruent right application case*)
    move : (alphac_app_inv _ _ _ (asym _ _ Halpha)) => [u1 [v1 Heq]]; symmetry in Heq;
    move : (renaming_app_inv _ sigma _ _ Hsigma Heq) => {u1 v1 Heq} [u1 [v1 Heq]];
    rewrite -Heq //= in Halpha;
    move : (alphac_app_inj _ _ _ _ Halpha) => [Halphau1 Halphav1];
    move : (IH sigma Hsigma v1 Halphav1 v1
      (rt_step term iconv _ _ (ialpha _ _ Halphav1)) (rt_refl term iconv v1)) => [v2 [Hv2_conv Hv2_alpha]];
    by exists (App u1 v2); split;
      [apply rt_trans with (App u1 v1); [rewrite -Heq in Hc| apply clos_refl_trans_app2]
      |rewrite //=; apply atrans with (App (u1[sigma]) u0); auto]].
(* beta-reduction case*)
   inversion Hr;
    rewrite -H0 in Halpha,Hr; move: (alphac_renaming_inv _ _  _ _ _  Hsigma (asym _ _ Halpha)) => [[i T] [t2 [u2 Hu]]];
    exists (t2 [(i^^T,u2)::nil]); split.
    - apply rt_trans with v; first by trivial.
      apply rt_trans with (App (Lam (i ^^ T) t2) u2);
        [by apply rt_step; apply ialpha; apply asym| apply rt_step; apply iibeta; auto].
    - rewrite subst_comp_unfold //=;
      apply atrans with ((t2 [(i ^^ T,
        Var (gensym (eFVS (seq.filter (setC1 (d:=idd) (i ^^ T)) (FV t2)) sigma) T)) :: sigma])
        [(max_ident (eFVS (seq.filter (setC1 (d:=idd) (i ^^ T)) (FV t2)) sigma) T ^^ T, u2 [sigma]) :: nil]);
      first by apply asym; rewrite /gensym; apply subst_collapse_inv;
      move : (gensym_gen (eFVS (seq.filter (setC1 (d:=idd) (i ^^ T)) (FV t2)) sigma) T).
      rewrite -(alpha_norm _ _ Hu sigma) in Halpha; rewrite //= in Halpha;
      move : (alphac_app_inj _ _ _ _ Halpha) => [Hlam Hargs];
      apply atrans with ((t2 [(i ^^ T,
        Var (gensym (eFVS (seq.filter (setC1 (d:=idd) (i ^^ T)) (FV t2)) sigma) T)) :: sigma])
        [(max_ident (eFVS (seq.filter (setC1 (d:=idd) (i ^^ T)) (FV t2)) sigma) T ^^ T, u1) :: nil]);
      first by rewrite alpha_norm_equiv !subst_comp_unfold; apply tassoc_sigma_equiv_equal => x1 Hfvx1;
        rewrite !subst_comp_comm_tassoc; apply tassoc_sigma_equiv_equal => x2 Hfvx2;
          rewrite !subst_comp_comm_tassoc -alpha_norm_equiv //=;
            case (max_ident (eFVS (seq.filter (setC1 (d:=idd) (i ^^ T)) (FV t2)) sigma) T ^^ T == x2); trivial.
      move : Hlam; case x0 => [x1 T0] Hlam; rewrite alpha_norm_equiv //= in Hlam;
      inversion Hlam as [[Hbind Htypes Hbody]];
      rewrite Htypes in Hbind; rewrite /gensym Hbind in Hbody;
      apply atrans with (((t2 [(i ^^ T0,
        Var (max_ident (eFVS (seq.filter (setC1 (d:=idd) (i ^^ T0)) (FV t2)) sigma) T0 ^^ T0)) :: sigma])
        [(max_ident (eFVS (seq.filter (setC1 (d:=idd) (i ^^ T0)) (FV t2)) sigma) T0 ^^ T0,
         Var (max_ident (eFVS (seq.filter (setC1 (d:=idd) (x1 ^^ T0)) (FV t1)) nil) T0 ^^ T0)) :: nil])
        [((max_ident (eFVS (seq.filter (setC1 (d:=idd) (x1 ^^ T0)) (FV t1)) nil) T0 ^^ T0), u1)::nil]).
      apply asym; apply subst_collapse_inv;
      first by rewrite eFVS_nil -Hbind;
      move: (gensym_gen (eFVS (seq.filter (setC1 (d:=idd)
        (max_ident (eFVS (seq.filter (setC1 (d:=idd) (i ^^ T0)) (FV t2)) sigma) T0 ^^ T0))
        (FV (t2 [(i ^^ T0, Var (gensym (eFVS (seq.filter (setC1 (d:=idd) (i ^^ T0)) (FV t2))
                                 sigma) T0)) :: sigma]))) nil) T0) => //=; rewrite eFVS_nil.
      rewrite Hbody; apply subst_collapse_inv; by
      move : (gensym_gen (eFVS (FV (Lam (x1 ^^ T0) t1)) nil) T0) => //=.
(* eta-reduction case *)
  inversion Hr;
    gen x0; move => x0; case x0 => [x1 T1] H0 H3;
    rewrite  H2 in H3 => {t1 H2}; rewrite <- H3 in * => {t0 H3};
    move : (alphac_renaming_inv2 _ _ _ _ _ Hsigma H0 Halpha) => [x2 [u [Halpha' Hfv']]];
    exists u; split; first by apply rt_trans with v;
      [trivial|
        apply rt_trans with (Lam (x2 ^^ T1) (App u (Var (x2 ^^ T1))));
          [apply rt_step; apply ialpha; trivial |
            apply rt_step; apply iieta; auto]].
    rewrite (alpha_norm _ _  Halpha' sigma) //= in Halpha;
    move : (alphac_lam_inj _ _ _ _ Halpha); rewrite eq_refl //= eq_refl => Halpha2;
    move : (alphac_app_inj _ _ _ _ Halpha2) => [Halpha3 Halpha4];
    apply atrans with ((u [(x2 ^^ T1, Var (gensym
    (eFVS (seq.filter (setC1 (d:=idd) (x2 ^^ T1)) (cat (FV u) (Seq (x2 ^^ T1)))) sigma) T1)):: sigma])
    [(gensym (eFVS (seq.filter (setC1 (d:=idd) (x2 ^^ T1)) (cat (FV u) (Seq (x2 ^^ T1)))) sigma) T1,
                Var (x1 ^^ T1)) :: nil]); last by trivial.
    apply atrans with ((u [(x2^^T1, Var (x1^^T1))::sigma])).
    - rewrite (tassoc_sigma_equiv_equal u sigma ((x2^^T1,Var (x1^^T1))::sigma)); first by apply arefl.
      by move => x3 Hfv3; rewrite //=; casebool e: (x2^^T1 == x3);
        [rwbooleqrev e in Hfv3; contradictionbool Hfv'|trivial].
    - apply asym; apply subst_collapse_inv;
      move: (gensym_gen (eFVS (seq.filter (setC1 (d:=idd) (x2 ^^ T1))
        (cat (FV u) (Seq (x2 ^^ T1)))) sigma) T1) => f;
      casebool e : (eFVS (FV (Lam (x2 ^^ T1) u)) sigma
        (gensym (eFVS (seq.filter (setC1 (d:=idd) (x2 ^^ T1))
                 (cat (FV u) (Seq (x2 ^^ T1)))) sigma) T1)); last by trivial.
      by contradictionbool f; rewrite <- eFVS_in in e |-*;
        move: e => [x3 Hx3]; move/andP: Hx3 => [Hfvx3 Hgenx3];
          exists x3; apply /andP; split;
            [rewrite FV_lam_bool in Hfvx3; move/andP:Hfvx3 => [Hfvx3 Hneq];
              rewrite mem_filter /setC1 /setI mem_cat /setU //= /setU1 Hneq andTb Hfvx3 orTb|trivial].
Qed.

Lemma subst_comm_ticonv : forall t u sigma,
  is_renaming sigma ->
 ticonv (t[sigma]) u -> exists v, ticonv t v /\ alphac (v[sigma]) u.
move => t u sigma Hsigma Hconv;
rewrite clos_refl_s_trans_equiv_clos_refl_trans in Hconv;
move : (subst_comm_crt_iconv t u sigma Hsigma Hconv) => [v [H H1]];
rewrite -clos_refl_s_trans_equiv_clos_refl_trans in H; exists v; split; trivial.
Qed.

Lemma alphac_eta_inv : forall x T t u,
  alphac (Lam (x^^T) (App t (Var (x^^T)))) u ->
  exists i, exists v, u = (Lam (i^^T) (App v (Var (i^^T)))).
move => x T t u; rewrite alpha_norm_equiv; gen t; gen T; gen x; gen u.
elim => [i | [i T0] t IH | u IHu v IHv] x T; try solve [intros; inversion H].
by move => t0; rewrite -alpha_norm_equiv => H;
move : (alphac_lam_inj _ _ _ _ H) => H1; rewrite //= eq_refl in H1;
move : (alphac_app_inv _ _ _ H1) => [u [v Heq]]; rewrite Heq in H1;
rewrite Heq; move : (alphac_app_inj _ _ _ _ H1) => [Hu Hv]; rewrite alpha_norm_equiv //= in Hv;
gen v; move => v; case v => [i0 | [i1 T1] z|z z'] Heq H1 Hv; try solve [inversion Hv];
rewrite //= in Hv; rewrite -Hv; exists i; exists u;
rewrite alpha_norm_equiv //= in H; inversion H as [[Hbind Htypes Hbody]]; rewrite -Htypes.
Qed.

Lemma tifvc : forall t t' x y,
 ticonv (App t (Var x)) t' -> (y notin (FV t') -> exists t'', ticonv t t'' /\ ~~(FV t'' y)).
move => t t' x y; rewrite /ticonv.
move => h.
have ee : (forall u, iconv (App u (Var x)) (App t (Var x)) ->
    ~~ FV t' y ->
   exists t'' : term, clos_refl_s_trans iconv u t'' /\ ~~ FV t'' y); last by apply (ee t); apply ialpha.
elim h.
move => x0 u Hconv Hfv; move: (ifvc x y u x0 Hconv Hfv) => [s [Hs Hfvs]]; exists s; split; auto.
move=> {t t' h} z w v rzw rwv IH u g.
inversion g => {H0 H1}.
- by move : (alphac_app_inv _ _ _ H) => [u1 [v1 Hv1]] Hfv;
     rewrite Hv1 in H; move : (alphac_app_inj _ _ _ _ H) => [H1 H2];
     rewrite alpha_norm_equiv /subst -/subst !tassoc_nil in H2;
     gen v1; move => v1; case v1 => {v1} [i | [i0 T] *|*] //= Hv1 H H2;
     rewrite H2 in IH; symmetry in Hv1;
     rewrite -Hv1 in rzw;
     move : (IH u1 rzw Hfv) => [s [Hs Hfvs]];
     exists s; split; trivial;
     apply st_trans with u1; [apply ialpha|trivial].
- inversion H.
  - move => {t0 H1 u1 H2}; inversion H0.
    rewrite -H1 in rzw.
    have ee: (is_renaming ((x0, Var x)::nil)); first by trivial.
    have ff :(ticonv (t0 [(x0, Var x)::nil]) v); first by rewrite /ticonv; apply st_trans with w.
    move : (subst_comm_ticonv _ _ _ ee ff) => {ee} [v0 [Hconv_v0 Hfv_v0]] Hfv.
    exists (Lam x0 v0); split.
    by rewrite clos_refl_s_trans_equiv_clos_refl_trans; apply clos_refl_trans_lam;
      rewrite -clos_refl_s_trans_equiv_clos_refl_trans.
    by rewrite -(FV_alpha _ _ Hfv_v0 y) in Hfv;
    casebool e: (FV (Lam x0 v0) y); [contradictionbool Hfv| trivial];
    rewrite FV_lam_bool in e; move/andP: e => [e f];
    rewrite -FV_in; exists y; rewrite e andTb //=; move/negbET : f =>-> //=; rewrite /setU1 eq_refl.
  - move=> Hfv; rewrite -H1 in rzw; move: (IH u1 rzw Hfv) => [s [Hconv_s Hfv_s]];
    exists s; split; [by apply st_trans with u1;[apply iibeta|trivial]|auto].
  - by inversion H3; inversion H4.
- inversion H.
  - by move => {t0 u0 H1 H2 t u1}; inversion H0.
  - move => {t0 v0 H0 H2} Hfv; rewrite <-H1 in *; move : (IH u1 rzw Hfv) => [s [Hs Hfvs]];
    exists s; split; try apply st_trans with u1; auto.
  - inversion H3; inversion H4.
Qed.

Inductive relaxalphac : term -> term -> Prop :=
| relaxarefl : forall t, relaxalphac t t
| relaxasym : forall t u, relaxalphac t u -> relaxalphac u t
| relaxatrans : forall t u v, relaxalphac t u -> relaxalphac u v -> relaxalphac t v
| relaxaalphac : forall x y t1 t2,
  y notin (FV (Lam x t1)) ->
  relaxalphac (t1 [(x, Var y)::nil]) t2 ->
  relaxalphac (Lam x t1)(Lam y t2)
| relaxaapp1 : forall u1 u2 v, relaxalphac u1 u2 -> relaxalphac (App u1 v)(App u2 v)
| relaxaapp2 : forall u v1 v2, relaxalphac v1 v2 -> relaxalphac (App u v1)(App u v2)
| relaxalam : forall x t1 t2, relaxalphac t1 t2 -> relaxalphac (Lam x t1)(Lam x t2).

Inductive relaxiconv : term -> term -> Prop :=
| relaxialpha : forall t u, relaxalphac t u -> relaxiconv t u
| relaxiibeta : forall t u, lambdacongr ibeta t u -> relaxiconv t u
| relaxiieta : forall t u, lambdacongr ieta t u -> relaxiconv t u.

Definition relaxtconv := clos_refl_trans term relaxiconv.

Definition sym_relaxtconv := clos_refl_sym_trans term relaxiconv.

(* CR property on untyped alpha-beta-eta conversion,
   formalized in

   More Church-Rosser Proofs (in Isabelle/HOL), Tobias Nipkow
   Proceedings of the 13th International Conference on Automated Deduction (CADE-13),(1996)

   (using deBruijn indices)
   *)

Axiom CR : forall t u,
  sym_relaxtconv t u ->
  exists v, (relaxtconv t v /\ relaxtconv u v).

Inductive betaeta : term -> term -> Prop :=
| _ibeta : forall t u, lambdacongr ibeta t u -> betaeta t u
| _ieta : forall t u, lambdacongr ieta t u -> betaeta t u.

Definition tbetaeta := clos_refl_s_trans betaeta.

Hint Constructors relaxalphac relaxiconv betaeta.

Hint Unfold relaxtconv tbetaeta sym_relaxtconv.

(* postponability of alpha-conversion on untyped terms, wrt. beta-eta conversion *)

Axiom alphac_postponable : forall t u,
  relaxtconv t u ->
  exists v, tbetaeta t v /\ relaxalphac v u.

Lemma sym_relaxtconv_inv : forall t u,
  sym_relaxtconv t u ->
  exists v, exists w, tbetaeta t v /\ relaxalphac v w /\ tbetaeta u w.
move => t u Hconv;
move : (CR _ _ Hconv) => [v [Hconv1 Hconv2]];
move : (alphac_postponable _ _ Hconv1) => [v1 [Hb1 Halpha1]];
move : (alphac_postponable _ _ Hconv2) => [v2 [Halpha2 Hb2]];
by exists v1; exists v2; split; trivial; split; trivial;
apply relaxatrans with v; trivial; apply relaxasym.
Qed.

(* preservation of free variables along relaxalphac *)

Lemma FV_relaxalpha : forall t t', relaxalphac t t' -> forall x, FV t x = FV t' x.
induction 1; auto.
- by move=> x; apply trans_equal with (FV u x).
- move=> z; rewrite /= !mem_filter /setI /setC1.
 case xz : ( x == z) => /=.
  rewrite -(IHrelaxalphac z).
  move/eqP: xz=>->.
  move: (FV_subst t1 ((z,Var y) :: nil) z).
  case yz : (y == z) => //=.
  rewrite //= /setU1 yz !orbF eq_refl /negb andbF; case: FV => //=.
  move=> a e. case: setU1=> //=.
  by intro h; assert false; auto.
 case yz: (y == z) => //=.
  move/eqP: yz xz =><-.
  rewrite /negb /andb in H; move: H; case xy: ( x == y ) => //=;
  case FV => x0 s //=.
  rewrite /setC1 /setU1.
  case f: (x == x0) => //=.
  rewrite mem_filter /setI xy //=.
  case (s y) => //=; move/eqP: f=><-.
  by rewrite xy.
  rewrite /setU1;  case (x0 == y) => //=.
  rewrite mem_filter /setI xy.
  by case (s y).
  rewrite -(IHrelaxalphac z).
 by move: (FV_subst t1 ((x, Var y) :: nil) z);
 move: (FV_subst2 t1 ((x, Var y) :: nil) z);
 rewrite /= /setU1 xz //= /setU1 yz /= orbF andbT; case (FV t1 z);
 case: (FV _ z) => //= h1 h2; try (by elim h1); try elim h2.
- by move=> x; rewrite /= 2!mem_cat /setU IHrelaxalphac.
- by move=> x; rewrite /= 2!mem_cat /setU IHrelaxalphac.
- by move=> y; rewrite /= 2!mem_filter /setC1 /setI IHrelaxalphac.
Qed.

Lemma conv_to_sym_relaxtconv : forall t u,
  conv t u -> sym_relaxtconv t u.
move => t u Hconv.
elim Hconv.
(* reflexivity *)
by move => t0; rewrite /sym_relaxtconv; apply rst_refl.
(* symmetry *)
by move => t0 u0 Hconv' Hsym; rewrite /sym_relaxtconv; apply rst_sym.
(* transitivity *)
by move => t0 u0 v Hconv1 Hsym1 Hconv2 Hsym2; rewrite /sym_relaxtconv; apply rst_trans with u0; auto.
(* beta-reduction *)
by move => t0 u0 x; rewrite /sym_relaxtconv; apply rst_step; apply relaxiibeta; apply cstep; auto.
(* strict to relaxed alpha-conversion case *)
by move => {t u Hconv} x y T t1 t2 Hfv Hconv Hsym;
rewrite /sym_relaxtconv; apply rst_trans with (Lam (y^^T) (t1 [(x^^T, Var (y^^T))::nil]));
[apply rst_step; apply relaxialpha; apply relaxaalphac
|elim Hsym; try solve [ move => x0; apply rst_refl |move => x0 y0 Hc IH; apply rst_sym; auto
                       |move => x0 y0 z Hc1 IH1 Hc2 IH2; apply rst_trans with (Lam (y^^T) y0); auto];
 move => x0 y0 Hx0y0; inversion Hx0y0; apply rst_step; [apply relaxialpha| apply relaxiibeta| apply relaxiieta]]; auto.
by move => x t0 Hfv; rewrite /sym_relaxtconv; apply rst_sym; apply rst_step; apply relaxiieta; apply cstep; auto.
(* congruent left application *)
by move => {t u Hconv} u1 u2 v Hconv Hsym;
   elim Hsym; rewrite /sym_relaxtconv;
   try solve [ move => x0; apply rst_refl |move => x0 y0 Hc IH; apply rst_sym; auto
                       |move => x0 y0 z Hc1 IH1 Hc2 IH2; apply rst_trans with (App y0 v); auto];
   move => x y Hxy; inversion Hxy; apply rst_step; [apply relaxialpha| apply relaxiibeta| apply relaxiieta]; auto.
(* congruent right application *)
by move => {t u Hconv} u1 u2 v Hconv Hsym;
   elim Hsym; rewrite /sym_relaxtconv;
   try solve [ move => x0; apply rst_refl |move => x0 y0 Hc IH; apply rst_sym; auto
                       |move => x0 y0 z Hc1 IH1 Hc2 IH2; apply rst_trans with (App u1 y0); auto];
   move => x y Hxy; inversion Hxy; apply rst_step; [apply relaxialpha| apply relaxiibeta| apply relaxiieta]; auto.
(* congruent abstraction case *)
by move => {t u Hconv} u1 u2 v Hconv Hsym;
   elim Hsym; rewrite /sym_relaxtconv;
   try solve [ move => x0; apply rst_refl |move => x0 y0 Hc IH; apply rst_sym; auto
                       |move => x0 y0 z Hc1 IH1 Hc2 IH2; apply rst_trans with (Lam u1 y0); auto];
   move => x y Hxy; inversion Hxy; apply rst_step; [apply relaxialpha| apply relaxiibeta| apply relaxiieta]; auto.
Qed.

Lemma tbetaeta_to_ticonv : forall t u,
  tbetaeta t u -> ticonv t u.
move => t u Hconv; elim Hconv; first by move => x; rewrite /ticonv; apply st_refl.
move => x y z Hxy Hyz IH; rewrite /ticonv; apply st_trans with y; auto;
inversion Hxy;[apply iibeta|apply iieta]; auto.
Qed.

Lemma ticonv_to_conv : forall t u,
  ticonv t u -> conv t u.
move => t u Hconv; elim Hconv; first by move => x; rewrite /ticonv; apply crefl.
move => x y z Hxy Hyz IH; apply ctrans with y; last by trivial.
inversion Hxy.
by apply alphac_beta.
by elim H; auto; move => t1 u1 Hbeta; inversion Hbeta; apply cbeta.
by apply csym; elim H; auto; move => t1 u1 Heta; inversion Heta; apply ceta.
Qed.

Lemma real_fvc : forall t t' x y,
 conv (App t (Var x)) t' -> (y notin (FV t') -> exists t'', conv t t'' /\ ~~(FV t'' y)).
move => t t' x y Hconv Hfv.
move : (conv_to_sym_relaxtconv _ _ Hconv) => Hsym.
move : (sym_relaxtconv_inv _ _ Hsym) => [u [v [Hbe1 [Halpha Hbe2]]]].
move : (tbetaeta_to_ticonv _ _ Hbe1) => Hticonv.
move : (tbetaeta_to_ticonv _ _ Hbe2) => Hticonv_for_fvs.
move : (FV_ticonv_dec _ _ Hticonv_for_fvs) => Hfvtrans.
have ee : (y notin (FV v));
first by casebool e : (FV v y); [contradictionbool Hfv; apply (Hfvtrans _ e)|trivial].
rewrite -(FV_relaxalpha _ _ Halpha) in ee.
by move : (tifvc _ _ _ _ Hticonv ee) => [t'' [Hconv'' Hfv'']]; exists t''; split; [apply ticonv_to_conv|trivial].
Qed.

(*********************************************)
(* END of dummy variable in decomp treatment *)
(*********************************************)
