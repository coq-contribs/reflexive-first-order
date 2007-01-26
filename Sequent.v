Require Import Bintree.
Require Import Bool.
Require Import Env.
Require Import Free_algebra.
Require Import Form.

Unset Boxed Definitions.

Section with_env.

Variable Denv : domain_env.
Variable Sigma : Free_algebra.signature Denv.
Variable Pi : signature Denv.

Notation "[ T ; i ]" := (mkE Denv i T).

Fixpoint interp_vars (V:var_ctx) (F:Full V) (Inside:var_env Denv -> Prop) 
{struct F} : Prop :=
match F with
  F_empty => Inside empty
| F_push dom V0 F0 => 
      interp_vars V0 F0 
	(fun Venv => forall var: interp_domain Denv dom,
	            (Inside (Venv \ (mkE Denv dom var)))) 
end.

Fixpoint interp_hyps (hyps: hyp_ctx) (F:Full hyps) (Inside:var_env Denv -> Prop) 
{struct F} :var_env Denv -> Prop :=
match F with
  F_empty => Inside
| F_push f hyps0 F0 => 
      interp_hyps hyps0 F0 
	(fun Venv => interp_form Denv Sigma Pi Venv nil f -> Inside Venv) 
end.

Fixpoint interp_var_list (Venv:var_env Denv) (V:list domain) 
(Inside: var_env Denv -> Prop)  {struct V} : Prop :=
 match V with 
 nil => Inside Venv
| dom::V0 => 
 forall var: interp_domain Denv dom, 
 interp_var_list (Venv\mkE Denv dom var) V0 Inside
end.

Fixpoint interp_hyp_list (hyps: list form) (Head: var_env Denv -> Prop) 
{struct hyps} : var_env Denv -> Prop :=
  match hyps with
  nil => Head
  | f::hyps0 => 
       fun Venv => interp_form Denv Sigma Pi Venv nil f -> interp_hyp_list hyps0 Head Venv
end.

Definition interp_seq (V:var_ctx) (FV:Full V) (hyps:hyp_ctx) (F:Full hyps)  (goal:form) : Prop :=
interp_vars V FV (interp_hyps hyps F 
(fun Venv => interp_form Denv Sigma Pi Venv nil goal)).

Definition interp (V:list domain) (hyps:list form) (goal:form) :Prop :=
interp_var_list empty V (interp_hyp_list hyps 
	(fun Venv => interp_form Denv Sigma Pi Venv nil goal)).

Inductive WF_hyp_ctx (V:var_ctx) : 
  forall hyps:hyp_ctx, Full hyps -> Prop :=
    WF_empty : WF_hyp_ctx V empty F_empty
  | WF_push_hyp : forall gamma f F, WF_form Denv Sigma Pi V nil f -> 
    WF_hyp_ctx V gamma F ->  
    WF_hyp_ctx V (gamma \ f) (F_push f gamma F).

Inductive WF_seq (V:var_ctx) (hyps:hyp_ctx) (F:Full hyps) (goal:form) :Prop :=  
WF_turnstyle : 
WF_hyp_ctx V hyps F -> WF_form Denv Sigma Pi V nil goal -> WF_seq V hyps F goal. 

Fixpoint check_ctx (V:var_ctx) (hyps:hyp_ctx) (F:Full hyps) {struct F} : bool :=
  match F with 
    F_empty => true
  | F_push f hyps0 F0 =>
         if check_form Denv Sigma Pi V nil f then 
           check_ctx V hyps0 F0 
       else false
end.

Definition check_seq (V:var_ctx) (hyps:hyp_ctx) (F:Full hyps) (goal:form) : bool :=
 if check_form Denv Sigma Pi V nil goal then check_ctx V hyps F else false.

Lemma WF_checked_ctx : forall V ctx F, 
  check_ctx V ctx F = true -> WF_hyp_ctx V ctx F. 
induction F. 
constructor 1.
simpl.
caseq (check_form Denv Sigma Pi V nil a).
constructor 2.
apply WF_checked_form;assumption.
apply IHF;assumption.
congruence.
Qed.

Lemma WF_checked_seq : forall V ctx F goal, 
check_seq V ctx F goal = true -> WF_seq V ctx F goal. 
intros V ctx F goal;unfold check_seq.
caseq (check_form Denv Sigma Pi V nil goal).
split.
apply WF_checked_ctx;assumption.
apply WF_checked_form;assumption.
congruence.
Qed.

Lemma Weak_WF_ctx : forall vars hyps F dom,
Full vars ->
WF_hyp_ctx vars hyps F ->
WF_hyp_ctx (vars\dom) hyps F.
induction F.
left.
right;inversion H0;dependent rewrite H8 in H9;simpl in H9;subst.
apply Weak_WF_form;auto.
apply IHF;auto.
Qed.

(* si une formule est tautologique alors elle est vraie dans tout contexte *) 
Lemma Compose0 : forall vars F' hyps F  (A:var_env Denv -> Prop),
(forall Venv, Instanceof Denv vars F' Venv -> A Venv) ->
interp_vars vars F' (interp_hyps  hyps F A).
intros vars F' hyps F .
induction F;induction F';intros A H;simpl in * |-*. 
apply H;left.
eauto.
apply (IHF' (fun Venv : var_env Denv =>
   forall var : interp_domain Denv a, A (Venv \ [var; a]))).
intros Venv Inst x.
apply H;right;auto.
eauto.
eauto.
Qed.

Lemma Compose1 : forall vars F' hyps F  (A B:var_env Denv -> Prop),
(forall Venv, Instanceof Denv vars F' Venv -> A Venv -> B Venv) ->
interp_vars vars F' (interp_hyps hyps F A) ->
interp_vars vars F' (interp_hyps hyps F B).
intros vars F' hyps F .
induction F;
induction F';intros A B H;simpl in * |-*. 
apply H;left.
intros; apply (IHF' (fun Venv : var_env Denv =>
   forall var : interp_domain Denv a, A (Venv \ [var; a]))
   (fun Venv : var_env Denv =>
   forall var : interp_domain Denv a, B (Venv \ [var; a])));auto.
intros Venv Inst HA x.
apply H.
right;auto.
auto.
apply IHF;eauto.
apply IHF;eauto.
Qed.

Lemma Compose2 : forall vars F' hyps F  (A B C:var_env Denv -> Prop),
(forall Venv, Instanceof Denv vars F' Venv -> A Venv -> B Venv -> C Venv) ->
interp_vars vars F' (interp_hyps hyps F A) ->
interp_vars vars F' (interp_hyps hyps F B) ->
interp_vars vars F' (interp_hyps hyps F C).
intros vars F' hyps F .
induction F;
induction F';intros A B C H;simpl in * |-*. 
apply H;left.
intros HA HB.
apply (IHF' (fun Venv : var_env Denv =>
   forall var : interp_domain Denv a, A (Venv \ [var; a]))
   (fun Venv : var_env Denv =>
   forall var : interp_domain Denv a, B (Venv \ [var; a]))
   (fun Venv : var_env Denv =>
   forall var : interp_domain Denv a, C (Venv \ [var; a])));auto.
intros Venv Inst HAA HBB x.
apply H;auto.
right;auto.
apply IHF;eauto.
apply IHF;eauto.
Qed.

Lemma Compose3 : forall vars F' hyps F  (A B C D:var_env Denv -> Prop),
(forall Venv, Instanceof Denv vars F' Venv -> A Venv -> B Venv -> C Venv -> D Venv) ->
interp_vars vars F' (interp_hyps hyps F A) ->
interp_vars vars F' (interp_hyps hyps F B) ->
interp_vars vars F' (interp_hyps hyps F C) ->
interp_vars vars F' (interp_hyps hyps F D).
intros vars F' hyps F .
induction F;
induction F';intros A B C D H;simpl in * |-*. 
apply H ;left.
intros HA HB HC.
apply (IHF' (fun Venv : var_env Denv =>
   forall var : interp_domain Denv a, A (Venv \ [var; a]))
   (fun Venv : var_env Denv =>
   forall var : interp_domain Denv a, B (Venv \ [var; a]))
   (fun Venv : var_env Denv =>
   forall var : interp_domain Denv a, C (Venv \ [var; a]))
   (fun Venv : var_env Denv =>
   forall var : interp_domain Denv a, D (Venv \ [var; a])));auto.
intros Venv Inst HAA HBB HCC x.
apply H;auto.
right;auto.
apply IHF;eauto.
apply IHF;eauto.
Qed.

Ltac norefl := repeat match goal with [ H: ?x = ?x |- _ ] => clear H end. 

Lemma Global_bind : 
forall dom vars Fv hyps Fh Inside,
WF_hyp_ctx vars hyps Fh ->
interp_vars vars Fv
  (fun Venv : var_env Denv =>
   forall var : interp_domain Denv dom,
   interp_hyps hyps Fh Inside (Venv \ [var; dom])) ->
interp_vars vars Fv
  (interp_hyps hyps Fh
     (fun Venv : var_env Denv =>
      forall var : interp_domain Denv dom, Inside (Venv \ [var; dom]))).

induction Fh;simpl.
auto.
intros Inside W;inversion W;simpl;subst.
norefl.
intro h.
cut 
(interp_vars vars Fv
  (interp_hyps S Fh
     (fun Venv : var_env Denv =>
     forall var : interp_domain Denv dom,
     (fun V => 
      interp_form Denv Sigma Pi V nil a ->
      Inside V) (Venv \ [var; dom])))).
apply (Compose1 vars Fv S Fh).
intros Venv Inst hh Ha x.
apply (hh x).
apply (proj1 (Weak_interp_form _ _ _ _ _ _ [x;dom] a nil Inst H2) Ha).
dependent rewrite H6 in H7 ;simpl in H7.
change 
(interp_vars vars Fv
  (interp_hyps S Fh
     (fun Venv : var_env Denv =>
      forall var : interp_domain Denv dom,
      (fun V => 
      interp_form Denv Sigma Pi V nil a ->
      Inside  V) (Venv \ [var; dom])))).
apply IHFh;auto.
Qed.

Lemma WF_form_In : forall V hyps F f,
In f hyps F ->
WF_hyp_ctx V hyps F ->
WF_form Denv Sigma Pi V nil f .
induction F;simpl In.
intros;elim H.
intros f [H | H] W;subst;inversion W.
trivial.
apply IHF;trivial.
change 
(let (x,P) := existS (fun S: Store form => Full S) S F1 in
             WF_hyp_ctx V x P) in H8.
rewrite H7 in H8.
assumption.
Qed.

Lemma WF_form_hyp : forall V hyps F i f,
get i hyps = PSome f ->
WF_hyp_ctx V hyps F ->
WF_form Denv Sigma Pi V nil f. 
intros hyps F V i f ei.
apply WF_form_In.
apply get_In with i;trivial.
Qed.

Theorem Project_In : forall V F hyps Fh f, In f hyps Fh -> 
WF_hyp_ctx V hyps Fh ->
interp_seq V F hyps Fh f.
induction Fh.
simpl;intros f H _;elim H.
simpl In.
intros f [H | H] W.
subst;unfold interp_seq;simpl interp_hyps.
apply (Compose0 V F S Fh) ;auto.
inversion W.
change 
(let (x,P) := existS (fun S : Store form => Full S) S F1 in
             WF_hyp_ctx V x P) in H8.
rewrite H7 in H8. 
simpl in H8.
generalize (IHFh f H H8).
unfold interp_seq;simpl.
apply Compose1.
auto.
Qed.

Theorem Project : forall V F hyps Fh i f, 
get i hyps = PSome f -> 
WF_hyp_ctx V hyps Fh ->
interp_seq V F hyps Fh f.
intros; apply Project_In;trivial.
apply get_In with i;assumption.
Qed.

Lemma interp_list_app_var : forall l dom (Inside: var_env Denv -> Prop),
interp_var_list empty l
  (fun Venv => forall x,  Inside (Venv \ [ x ; dom ] )) <->
interp_var_list empty (l ++ dom :: nil) Inside.
intros l dom;generalize (@empty (obj_entry Denv)) (@F_empty (obj_entry Denv)). 
induction l.
intros S F Inside.
simpl;split;trivial.
simpl.
intros S F Inside .
elim (IHl S F Inside).
split;
intros h1 var;elim (IHl (S \ [var;a]) (F_push _ _ F) Inside);
auto.
Qed.

Lemma interp_list_app_form : forall l f Venv (Inside: var_env Denv -> Prop),
interp_hyp_list l
  (fun Venv => interp_form Denv Sigma Pi Venv nil f -> Inside Venv) Venv <->
interp_hyp_list (l ++ f :: nil) Inside Venv.
intros l f.
induction l;simpl.
simpl;split;trivial.
intros Venv Inside.
split;
intros h1 var;elim (IHl Venv  Inside);
auto.
Qed.

Definition form_Eq p q := forall vars rels , 
 (interp_form Denv Sigma Pi vars rels p <-> interp_form Denv Sigma Pi vars rels q).

Lemma interp_seq_interp:   forall goal,
  forall vars Fv lvars,
  Equiv domain (@eq domain) lvars vars Fv ->
  forall hyps Fh lhyps,
  Equiv form form_Eq lhyps hyps Fh ->
  (interp_seq vars Fv hyps  Fh goal <-> 
  interp lvars lhyps goal).
intros goal vars Fv lvars Ev hyps Fh lhyps Eh.
unfold interp_seq,interp.
apply iff_trans with 
(interp_vars vars Fv
  (interp_hyp_list lhyps
     (fun Venv : var_env Denv => interp_form Denv Sigma Pi Venv nil goal))).
generalize lhyps Eh
(fun Venv : var_env Denv => interp_form Denv Sigma Pi Venv nil goal);
clear lhyps Eh;induction Fh;intros lhyps Eh Inside;inversion Eh;simpl.
split;trivial.
apply iff_trans with 
    (interp_vars vars Fv
    (interp_hyp_list l 
    (fun Venv : var_env Denv =>
    interp_form Denv Sigma Pi Venv nil a -> Inside Venv))).
dependent rewrite H7 in H3;simpl in H3;subst.
apply IHFh;auto.
simpl;split.
apply (Compose1 vars Fv empty F_empty
     (interp_hyp_list l
     (fun Venv : var_env Denv =>
      interp_form Denv Sigma Pi Venv nil a -> Inside Venv))
      (interp_hyp_list (l ++ a0 :: nil) Inside)).
intros Venv Inst.
elim (interp_list_app_form l a0 Venv Inside).
intros hh _ h;apply hh;clear hh;generalize h;clear h.
generalize l;induction l0;simpl.
assert (h:=proj1(H8 Venv nil));auto.
auto.
apply (Compose1 vars Fv empty F_empty
      (interp_hyp_list (l ++ a0 :: nil) Inside)
     (interp_hyp_list l
     (fun Venv : var_env Denv =>
      interp_form Denv Sigma Pi Venv nil a -> Inside Venv))).
intros Venv Inst.
elim (interp_list_app_form l a Venv Inside).
intros _ hh h;apply hh;clear hh;generalize h;clear h.
generalize l;induction l0;simpl.
assert (h:=proj2(H8 Venv nil));auto.
auto.
generalize lvars Ev (interp_hyp_list lhyps
     (fun Venv : var_env Denv => interp_form Denv Sigma Pi Venv nil goal));
clear lvars Ev;induction Fv;intros lvars Ev Inside;inversion Ev;simpl.
split;trivial.
apply iff_trans with 
    (interp_var_list empty l
    (fun Venv : var_env Denv =>
    forall var : interp_domain Denv a, Inside (Venv \ [var; a])));auto.
dependent rewrite H7 in H3;simpl in H3.
apply IHFv;auto.
subst.
apply interp_list_app_var.
Qed.

End with_env.



