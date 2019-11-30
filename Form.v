Require Import Bintree.
Require Import Bool.
Require Import Env.
Require Import Free_algebra.

Section with_env.

Variable Denv: domain_env.

Record pred_entry : Type :=
mkP{P_arity: arity;
           P_it: abstract Denv P_arity Prop}.

Definition signature := Store pred_entry.

Inductive form : Set :=
  Atom : positive -> args -> form
| Equal : domain -> term -> term -> form
| Absurd : form
| Arrow : form  -> form -> form
| And : form -> form -> form
| Or : form -> form -> form
| Forall : domain -> form -> form
| Exists : domain -> form -> form.

Inductive occ_form : Set :=
  Stop : occ_form 
| In_Atom : occ_args -> occ_form
| In_Eq : occ_term -> occ_term -> occ_form 
| In_Bin : occ_form -> occ_form -> occ_form
| In_Quant : occ_form -> occ_form.

Definition hyp_ctx := Store form.

Notation "A =>> B":= (Arrow A B) (at level 58, right associativity) : form_scope.
Infix "//\\" := And (at level 56, right associativity).
Infix "\\//" := Or (at level 57, right associativity).
Notation " !! d , F" := (Forall d F) (at level 59, right associativity) : form_scope.
Notation " ?? d , F" := (Exists d F) (at level 59, right associativity) : form_scope.
Notation "#" := Absurd.

Open Scope form_scope.


Fixpoint form_eq (p q:form) {struct p} :bool :=
match p, q with
  Atom hp argsp, Atom hq argsq =>
     if pos_eq hp hq then args_eq argsp argsq else false
 | Arrow p1 p2, Arrow q1 q2 =>
     if form_eq p1 q1 then form_eq p2 q2 else false
 | And p1 p2,And q1 q2 =>
     if form_eq p1 q1 then form_eq p2 q2 else false 
 | Or p1 p2,Or q1 q2 =>
     if form_eq p1 q1 then form_eq p2 q2 else false
 | Forall dp p0, Forall dq q0 => 
     if pos_eq dp dq then form_eq p0 q0 else false
 | Exists dp p0, Exists dq q0 =>
    if pos_eq dp dq then form_eq p0 q0 else false
 | Absurd,Absurd => true
 | Equal dp tp1 tp2, Equal dq tq1 tq2 =>   
    if pos_eq dp dq then 
    if term_eq tp1 tq1 then
       term_eq tp2 tq2 else false else false
 | _,_ => false
end.

Lemma refl_form_eq : forall f:form, form_eq f f = true.
induction f;simpl;
repeat (rewrite refl_pos_eq|| rewrite refl_args_eq || rewrite refl_term_eq||
rewrite IHf1||rewrite IHf2||rewrite IHf );reflexivity.
Qed.

Fixpoint inst_form (t:term) (n:nat) (f:form) {struct f} :form :=
 match f with 
  Atom p a => Atom p (inst_args t n a)
| Equal d t1 t2 => Equal d (inst_term t n t1) (inst_term t n t2)
| Absurd => Absurd
| Arrow f1 f2 => Arrow (inst_form t n f1) (inst_form t n f2)
| And f1 f2 => And (inst_form t n f1) (inst_form t n f2)
| Or f1 f2 => Or (inst_form t n f1) (inst_form t n f2)
| Forall d f0 => Forall d (inst_form t (S n) f0)
| Exists d f0 => Exists d (inst_form t (S n) f0)
end.

Fixpoint rewrite_form (ta tb:term) (occ:occ_form) (G:form) {struct G} :
 option form :=
  match occ,G with 
    Stop, _ => Some G
  | In_Atom aocc, Atom p a => 
    match rewrite_args ta tb aocc a with None => None
    | Some ra => Some (Atom p ra) 
    end
  | In_Eq occ1 occ2, Equal d t1 t2 =>
    match rewrite_term ta tb occ1 t1,rewrite_term ta tb occ2 t2 with
      Some rt1,Some rt2 => Some (Equal d rt1 rt2)
    | _,_ => None
    end
  | In_Bin occ1 occ2, Arrow G1 G2 =>
    match rewrite_form ta tb occ1 G1,rewrite_form ta tb occ2 G2 with
      Some rG1,Some rG2 => Some (Arrow rG1 rG2)
    | _,_ => None
    end
  | In_Bin occ1 occ2, And G1 G2 =>
    match rewrite_form ta tb occ1 G1,rewrite_form ta tb occ2 G2 with
      Some rG1,Some rG2 => Some (And rG1 rG2)
    | _,_ => None
    end
  | In_Bin occ1 occ2, Or G1 G2 =>
    match rewrite_form ta tb occ1 G1,rewrite_form ta tb occ2 G2 with
      Some rG1,Some rG2 => Some (Or rG1 rG2)
    | _,_ => None
    end
  | In_Quant occ0, Forall d G0 =>
    match rewrite_form ta tb occ0 G0 with None => None
    | Some rG0 => Some (Forall d rG0)
    end
  | In_Quant occ0, Exists d G0 =>
    match rewrite_form ta tb occ0 G0 with None => None
    | Some rG0 => Some (Exists d rG0)
    end
  | _,_ => None
end.

Variable Sigma : Free_algebra.signature Denv.
Variable Pi : signature.

Fixpoint interp_form (vars:var_env Denv) (rels:rel_env Denv) (f:form) {struct f}: Prop:=
match f with
  Atom hd a =>
  match get hd Pi with
    PNone => True
  | PSome (mkP rge head) =>
    match interp_args Denv Sigma vars rels a rge Prop head with
      PNone => True
    | PSome P => P
    end
  end
| Equal dom t1 t2 =>
  match interp_term Denv Sigma vars rels t1 dom,
               interp_term Denv Sigma vars rels t2 dom with
    Some x1, Some x2 => x1=x2
   | _,_ => True
  end
| Absurd => False
| Arrow f1 f2 => interp_form vars rels f1 -> interp_form vars rels f2
| And f1 f2 => interp_form vars rels f1 /\ interp_form vars rels f2
| Or f1 f2 => interp_form vars rels f1 \/ interp_form vars rels f2
| Forall dom f0 => forall rel:interp_domain Denv dom,
   interp_form vars (mkE Denv dom rel::rels) f0
| Exists dom f0 => exists rel:interp_domain Denv dom,
   interp_form vars (mkE Denv dom rel::rels) f0
end.

Inductive WF_form (gamma:var_ctx) : (list domain) ->  form -> Prop :=
  WF_Atom : forall rels n a rge p,
    get n Pi = PSome (mkP rge p) ->  
    WF_args Denv Sigma gamma rels a rge -> 
    WF_form gamma rels (Atom n a)
| WF_Equal : forall rels dom t1 t2,
    WF_term Denv Sigma gamma rels t1 dom ->
    WF_term Denv Sigma gamma rels t2 dom ->
    WF_form gamma rels (Equal dom t1 t2)
| WF_Absurd : forall rels,WF_form gamma rels Absurd
| WF_Arrow : forall rels f1 f2,  
    WF_form gamma rels f1 -> 
    WF_form gamma rels f2 -> 
    WF_form gamma rels (Arrow f1 f2)
| WF_And : forall rels f1 f2,  
    WF_form gamma rels f1 -> 
    WF_form gamma rels f2 -> 
    WF_form gamma rels (And f1 f2)
| WF_Or : forall rels f1 f2,  
    WF_form gamma rels f1 -> 
    WF_form gamma rels f2 -> 
    WF_form gamma rels (Or f1 f2)
| WF_Forall : forall rels dom f0,
  WF_form gamma (dom::rels) f0 -> 
  WF_form gamma rels (Forall dom f0)
| WF_Exists : forall rels dom f0,
  WF_form gamma (dom::rels) f0 -> 
  WF_form gamma rels (Exists dom f0). 

Fixpoint check_form (gamma:var_ctx) (rels:list domain) (f:form) 
{struct f}: bool :=
match f with
  Atom p a => 
  match get p Pi with
    PNone => false
  | PSome (mkP rge _) =>
          check_args Denv Sigma gamma rels a rge 
  end
| Equal dom t1 t2 =>
  if check_term Denv Sigma gamma rels t1 dom 
  then check_term Denv Sigma gamma rels t2 dom else false
| Absurd => true
| Arrow f1 f2 | And f1 f2 | Or f1 f2 =>
  if check_form gamma rels f1 then check_form gamma rels f2 else false
| Forall dom f | Exists dom f =>
  check_form gamma (dom::rels) f
end.

Lemma WF_checked_form : forall hyps f rels, 
check_form hyps rels f = true ->
WF_form hyps rels f.
induction f;simpl.
caseq (get p Pi).
intros [rge head].
intros eget rels Hargs.
constructor 1 with rge head;try assumption.
apply WF_checked_args;assumption.
congruence.
intro rels;caseq (check_term Denv Sigma hyps rels t d);clean.
intros et1 et2;constructor 2.
apply WF_checked_term;assumption.
apply WF_checked_term;assumption.
constructor.
intro rels;caseq (check_form hyps rels f1);clean;intros;constructor;auto.
intro rels;caseq (check_form hyps rels f1);clean;intros;constructor;auto.
intro rels;caseq (check_form hyps rels f1);clean;intros;constructor;auto.
constructor;apply IHf;assumption.
constructor;apply IHf;assumption.
Qed.

Theorem form_eq_refl: forall p q ,form_eq p q = true ->
forall vars rels , 
 (interp_form vars rels p <-> interp_form vars rels q).
induction p;destruct q;simpl;try congruence.
caseq (pos_eq p p0);simpl;try congruence.
intros ep ea vars rels;rewrite <-(pos_eq_refl _ _ ep);clear ep.
case (get p Pi).
intros [doms hd].
rewrite (args_eq_refl Denv Sigma vars rels doms Prop hd a a0);auto.
apply iff_refl.
apply iff_refl.
caseq (pos_eq d d0);simpl;try congruence.
caseq (term_eq t t1);simpl;try congruence.
intros et1 ed et2 vars rels.
rewrite <- (pos_eq_refl _ _ ed);clear ed.
rewrite (term_eq_refl Denv Sigma vars rels d t t1);auto.
rewrite (term_eq_refl Denv Sigma vars rels d t0 t2);auto.
apply iff_refl.
intros;apply iff_refl.
caseq (form_eq p1 q1);clean.
intros e1 e2 vars rels. 
generalize (IHp1 q1 e1 vars rels) (IHp2 q2 e2 vars rels).
intros [h1 h2] [h3 h4];split ;auto.
caseq (form_eq p1 q1);clean.
intros e1 e2 vars rels. 
generalize (IHp1 q1 e1 vars rels) (IHp2 q2 e2 vars rels).
intros [h1 h2] [h3 h4];split ; intros [h5 h6];split;auto.
caseq (form_eq p1 q1);clean.
intros e1 e2 vars rels. 
generalize (IHp1 q1 e1 vars rels) (IHp2 q2 e2 vars rels ).
intros [h1 h2] [h3 h4];split.
intros [h5 | h5];[left | right];auto.
intros [h5 | h5];[left | right];auto.
caseq (pos_eq d d0);try congruence;intros ed ep vars rels.
rewrite <- (pos_eq_refl _ _ ed);clear ed.
split; intros h x; assert (hh:=h x);
elim (IHp q ep vars ((mkE Denv d x) :: rels));auto.
caseq (pos_eq d d0);try congruence;intros ed ep vars rels.
rewrite <- (pos_eq_refl _ _ ed);clear ed.
split; intros [x h];split with x;
elim (IHp q ep vars ((mkE Denv d x) :: rels));auto.
Qed.

Lemma WF_Forall_instx : forall V (F:Full V) dom G,
WF_form V nil (!!dom, G) ->
WF_form (V \ dom) nil (inst_form (mkVar (index V)) 0 G).
intros V F dom G W.
inversion_clear W.
change (WF_form V (app nil (dom::nil)) G) in H.
replace O with (@length domain nil);trivial.
generalize H.
pattern (@nil domain) at -2.
apply  (fun (P: list domain -> Prop) (H:forall p, P p) => H nil).
clear H;induction G;intros rc W;inversion W;subst;simpl inst_form.
constructor 1 with rge p0;trivial.
apply WF_args_instx;auto.
constructor 2;apply WF_term_instx;auto.
constructor 3.
simpl;constructor;auto.
simpl;constructor;auto.
simpl;constructor;auto.
replace (S (length rc)) with (length (d :: rc));constructor;auto.
replace (S (length rc)) with (length (d :: rc));constructor;auto.
Qed.

Lemma WF_Exists_instx : forall V (F:Full V) dom G,
WF_form V nil (??dom, G) ->
WF_form (V \ dom) nil (inst_form (mkVar (index V)) 0 G).
intros V F dom G W.
inversion_clear W.
change (WF_form V (app nil (dom::nil)) G) in H.
replace O with (@length domain nil);trivial.
generalize H.
pattern (@nil domain) at -2.
apply  (fun (P: list domain -> Prop) (H:forall p, P p) => H nil).
clear H;induction G;intros rc W;inversion W;subst;simpl inst_form.
constructor 1 with rge p0;trivial.
apply WF_args_instx;auto.
constructor 2;apply WF_term_instx;auto.
constructor 3.
simpl;constructor;auto.
simpl;constructor;auto.
simpl;constructor;auto.
replace (S (length rc)) with (length (d :: rc));constructor;auto.
replace (S (length rc)) with (length (d :: rc));constructor;auto.
Qed.

Notation "[ T ; i ]" := (mkE Denv i T).

Lemma form_instx :
 forall hyps F Venv, Instanceof Denv hyps F Venv ->
 forall dom rel G rc, WF_form hyps 
(List.map (E_domain Denv) (rc ++ [rel;dom] :: nil)) G -> 
(interp_form (Venv\ [rel;dom])
       rc (inst_form (mkVar (index hyps)) (length rc) G) <->
interp_form Venv (rc ++ [rel;dom] :: nil) G).
intros hyps F Venv Inst dom rel.
induction G;intros rc W;inversion W;subst;simpl.
rewrite H2.
rewrite (args_instx _ Sigma _ F Venv);trivial.
split;trivial.
rewrite (term_instx  _ Sigma _ F Venv);trivial.
case (interp_term Denv Sigma Venv (rc ++ [rel; dom] :: nil) t d).
intro x1.
rewrite (term_instx _ Sigma _ F Venv);trivial.
split;trivial.
split;trivial.
split;trivial.
assert (HG1:=IHG1 rc H2).
assert (HG2:=IHG2 rc H3).
destruct HG1.
destruct HG2.
split;auto.
assert (HG1:=IHG1 rc H2).
assert (HG2:=IHG2 rc H3).
destruct HG1.
destruct HG2.
split;intros [HH1 HH2];split;auto.
assert (HG1:=IHG1 rc H2).
assert (HG2:=IHG2 rc H3).
destruct HG1.
destruct HG2.
split;(intro HH;destruct HH ; [left|right];auto).
split;intros H rel0;assert (H0:= IHG ([rel0;d] :: rc) H1);destruct H0;
simpl in H2;auto.
split; intros [rel0 H0];split with rel0;
assert (H:= IHG ([rel0;d] :: rc) H1);
destruct H;auto.
Qed.

Lemma WF_form_inst : forall hyps t dom,
WF_ground_term Denv Sigma hyps t dom ->
forall G rc,
WF_form hyps (rc ++ dom::nil)  G ->
WF_form hyps rc (inst_form t (length rc) G).
intros hyps t dom Wgt; induction G;intros rc W;inversion W; subst;simpl inst_form.
constructor 1 with rge p0;trivial.
apply WF_args_inst with dom;auto.
constructor 2;auto.
apply WF_term_inst with dom;auto.
apply WF_term_inst with dom;auto.
constructor 3.
constructor;auto.
constructor;auto.
constructor;auto.
replace (S (length rc)) with (length (d :: rc));trivial;constructor;auto.
replace (S (length rc)) with (length (d :: rc));trivial;constructor;auto.
Qed.


Lemma form_inst : forall hyps F Venv t dom x, Instanceof Denv hyps F Venv -> 
WF_ground_term Denv Sigma hyps t dom ->
interp_term Denv Sigma Venv nil t dom = Some x ->
forall G rc, 
WF_form hyps 
(List.map (E_domain Denv) (rc ++ [x;dom] :: nil)) G -> 
(interp_form Venv (rc ++ [x;dom] :: nil) G <->
interp_form Venv rc (inst_form t (length rc) G)).
intros hyps F Venv t dom x Inst Wgt et G;induction G;intros rc W;inversion W;
subst;simpl.
rewrite H2.
replace 
(interp_args Denv Sigma Venv rc (inst_args t (length rc) a) rge Prop p0)
with
(interp_args Denv Sigma Venv (rc ++ [x;dom] :: nil) a rge Prop p0).
split;trivial.
apply args_inst with hyps F;trivial.
replace 
(interp_term Denv Sigma Venv rc (inst_term t (length rc) t0) d)
with
(interp_term Denv Sigma Venv (rc ++ [x; dom] :: nil) t0 d).
replace 
(interp_term Denv Sigma Venv rc (inst_term t (length rc) t1) d)
with
(interp_term Denv Sigma Venv (rc ++ [x; dom] :: nil) t1 d).
split;trivial.
apply term_inst with hyps F;trivial.
apply term_inst with hyps F;trivial.
split;trivial.
elim (IHG1 rc H2);elim (IHG2 rc H3);split;auto.
elim (IHG1 rc H2);elim (IHG2 rc H3);split;intros [HH1 HH2];split;auto.
elim (IHG1 rc H2);elim (IHG2 rc H3);split;(intros [HH1 | HH2];[left| right];auto).
split;intros HH rel;elim (IHG (mkE Denv d rel :: rc) H1);simpl length.
intros h _;apply h;apply (HH rel).
auto.
split;intros [rel HH];split with rel;elim (IHG (mkE Denv d rel :: rc) H1);auto.
Qed.

Lemma Weak_WF_form : forall hyps H G rc,
Full hyps ->
WF_form hyps rc G ->
WF_form (hyps\H) rc G.
induction G;intros rc F W;inversion W;subst;try (constructor;auto).
constructor 1 with rge p0;auto;apply Weak_WF_args;auto.
apply Weak_WF_term;auto.
apply Weak_WF_term;auto.
Qed.

Lemma Weak_interp_form: forall hyps F  Venv var G rc,
Instanceof Denv hyps F Venv ->
WF_form hyps (List.map (E_domain Denv) rc) G ->
(interp_form Venv rc G <->
 interp_form (Venv\var) rc G).
intros hyps F Venv var.
induction G;intros rc Inst W;inversion_clear W;subst;simpl interp_form.
rewrite H.
clear p H.
rewrite <- (Weak_interp_args _ Sigma _ F Venv);trivial.
split;trivial.
simpl interp_form.
rewrite <- (Weak_interp_term _ Sigma _ F Venv);trivial.
rewrite <- (Weak_interp_term _ Sigma _ F Venv);trivial.
split;trivial.
split;trivial.
generalize (IHG1 rc Inst H) (IHG2 rc Inst H0);tauto.
generalize (IHG1 rc Inst H) (IHG2 rc Inst H0);tauto.
generalize (IHG1 rc Inst H) (IHG2 rc Inst H0);tauto.
simpl interp_form;split;
intros H0 varx;generalize (H0 varx) (IHG ([varx;d] :: rc) Inst);tauto.
split;intros [varx H0];split with varx;
generalize (IHG ([varx;d] :: rc) Inst H);tauto.
Qed.

Lemma Bind_WF_form : forall hyps delta G rc,
WF_form hyps rc G ->
WF_form hyps (rc ++ delta) G.
induction G;intros rc W;inversion W;subst;try constructor;auto.
constructor 1 with rge p0;trivial.
apply Bind_WF_args;trivial.
apply Bind_WF_term;trivial.
apply Bind_WF_term;trivial.
replace (d :: rc ++ delta) with ((d :: rc) ++ delta);auto.
replace (d :: rc ++ delta) with ((d :: rc) ++ delta);auto.
Qed.


Lemma Bind_interp_form : forall hyps F Venv delta G rc,
Instanceof Denv hyps F Venv ->
WF_form hyps (List.map (E_domain Denv) rc) G ->
(interp_form Venv rc G <->
 interp_form Venv (rc ++ delta) G).
induction G;intros rc Inst W;inversion W;subst;simpl.
rewrite H2;rewrite (Bind_interp_args _ Sigma _ F Venv delta);trivial.
split;auto.
rewrite (Bind_interp_term _ Sigma _ F Venv delta);trivial.
case (interp_term Denv Sigma Venv (rc ++ delta) t d);trivial.
rewrite (Bind_interp_term _ Sigma _ F Venv delta);trivial.
split;trivial.
split;trivial.
split;trivial.
elim (IHG1 _ Inst H2). 
elim (IHG2 _ Inst H3). 
split;auto.
elim (IHG1 _ Inst H2). 
elim (IHG2 _ Inst H3). 
split;intros [h1 h2];split;auto.
elim (IHG1 _ Inst H2). 
elim (IHG2 _ Inst H3). 
split;(intros [ h | h ];[left | right];auto).
split;intros h rel;assert (hh:=h rel);clear h.
change 
(WF_form hyps (List.map (E_domain Denv) ([rel;d]::rc)) G) in H1.
change (interp_form Venv (([rel; d] :: rc) ++ delta) G).
elim (IHG _ Inst H1);auto.
change 
(WF_form hyps (List.map (E_domain Denv) ([rel;d]::rc)) G) in H1.
change (interp_form Venv (([rel; d] :: rc) ++ delta) G) in hh.
elim (IHG _ Inst H1);auto.
split;intros [rel h];split with rel.
change 
(WF_form hyps (List.map (E_domain Denv) ([rel;d]::rc)) G) in H1.
change (interp_form Venv (([rel; d] :: rc) ++ delta) G).
elim (IHG _ Inst H1);auto.
change 
(WF_form hyps (List.map (E_domain Denv) ([rel;d]::rc)) G) in H1.
change (interp_form Venv (([rel; d] :: rc) ++ delta) G) in h.
elim (IHG _ Inst H1);auto.
Qed.

Lemma WF_rewrite_form : forall hyps dom t1 t2,
WF_ground_term Denv Sigma hyps t1 dom ->
WF_ground_term Denv Sigma hyps t2 dom ->
forall G occ rG rc,
rewrite_form t1 t2 occ G = Some rG ->
WF_form hyps rc G ->
WF_form hyps rc rG.
intros hyps dom t1 t2 Wt1 Wt2.
induction G;intros [ | occa |occ1 occ2 | occ1 occ2 | occ0];simpl;
clean;intros rG rc e W;inversion_clear W;
generalize e;clear e.
caseq (rewrite_args t1 t2 occa a);clean.
intros ra era e;injection e;clear e;intro e;subst.
apply WF_Atom with rge p0;trivial.
apply WF_rewrite_args with dom t1 t2 a occa;trivial.
caseq (rewrite_term t1 t2 occ1 t);clean.
intros rt et. 
caseq (rewrite_term t1 t2 occ2 t0);clean.
intros rt0 et0 e;injection e;clear e;intro e;subst.
apply WF_Equal.
apply WF_rewrite_term with dom t1 t2 t occ1;trivial.
apply WF_rewrite_term with dom t1 t2 t0 occ2;trivial.
caseq (rewrite_form t1 t2 occ1 G1);clean.
intros rG1 e1.
caseq (rewrite_form t1 t2 occ2 G2);clean.
intros rG2 e2 e;injection e;clear e;intro e;subst.
constructor;eauto.
caseq (rewrite_form t1 t2 occ1 G1);clean.
intros rG1 e1.
caseq (rewrite_form t1 t2 occ2 G2);clean.
intros rG2 e2 e;injection e;clear e;intro e;subst.
constructor;eauto.
caseq (rewrite_form t1 t2 occ1 G1);clean.
intros rG1 e1.
caseq (rewrite_form t1 t2 occ2 G2);clean.
intros rG2 e2 e;injection e;clear e;intro e;subst.
constructor;eauto.
caseq (rewrite_form t1 t2 occ0 G);clean.
intros rG0 e0 e;injection e;clear e;intro e;subst.
constructor;eauto.
caseq (rewrite_form t1 t2 occ0 G);clean.
intros rG0 e0 e;injection e;clear e;intro e;subst.
constructor;eauto.
Qed.

Lemma WF_eq_members : forall hyps dom t1 t2,
WF_form hyps nil (Equal dom t1 t2) ->
WF_ground_term Denv Sigma hyps t1 dom /\
WF_ground_term Denv Sigma hyps t2 dom.
intros hyps dom t1 t2 W;inversion W;split;apply WF_term_nil_ground_term;trivial.
Qed.

Lemma form_rewrite :
forall hyps F Venv,
Instanceof Denv hyps F Venv ->
forall dom t1 t2 it1 it2,  
WF_ground_term Denv Sigma hyps t1 dom ->
WF_ground_term Denv Sigma hyps t2 dom ->
interp_term Denv Sigma Venv nil t1 dom = Some it1 ->
interp_term Denv Sigma Venv nil t2 dom = Some it2 ->
it1 = it2 ->
forall G occ rc rG, 
rewrite_form t1 t2 occ G = Some rG ->
WF_form hyps (List.map (E_domain Denv) rc) G ->
(interp_form Venv rc G <-> interp_form Venv rc rG).
induction G;intros [ |occa | occ1 occ2 | occ1 occ2 | occ0] rc rG;simpl rewrite_form;
try solve [intro e;inversion e;split;trivial].
caseq (rewrite_args t1 t2 occa a);clean.
intros ra era e W;inversion e;inversion_clear W.
simpl.
rewrite H5.
replace 
(interp_args Denv Sigma Venv rc ra rge Prop p0) 
with
(interp_args Denv Sigma Venv rc a rge Prop p0).
split;trivial.
apply args_rewrite with hyps F dom t1 t2 it1 it2 occa;trivial.
caseq (rewrite_term t1 t2 occ1 t);clean.
intros rt et.
caseq (rewrite_term t1 t2 occ2 t0);clean.
intros rt0 et0 e W;inversion e;inversion_clear W.
simpl.
replace 
(interp_term Denv Sigma Venv rc rt d)
with
(interp_term Denv Sigma Venv rc t d).
replace 
(interp_term Denv Sigma Venv rc rt0 d)
with
(interp_term Denv Sigma Venv rc t0 d).
split;trivial.
apply term_rewrite with hyps F dom t1 t2 it1 it2 occ2;trivial.
apply term_rewrite with hyps F dom t1 t2 it1 it2 occ1;trivial.
caseq (rewrite_form t1 t2 occ1 G1);clean.
caseq (rewrite_form t1 t2 occ2 G2);clean.
intros rG2 e2 rG1 e1 e W;inversion e;inversion_clear W.
elim (IHG1 occ1 rc rG1 e1 H5).
elim (IHG2 occ2 rc rG2 e2 H7).
simpl;split;auto.
caseq (rewrite_form t1 t2 occ1 G1);clean.
caseq (rewrite_form t1 t2 occ2 G2);clean.
intros rG2 e2 rG1 e1 e W;inversion e;inversion_clear W.
elim (IHG1 occ1 rc rG1 e1 H5).
elim (IHG2 occ2 rc rG2 e2 H7).
simpl;tauto.
caseq (rewrite_form t1 t2 occ1 G1);clean.
caseq (rewrite_form t1 t2 occ2 G2);clean.
intros rG2 e2 rG1 e1 e W;inversion e;inversion_clear W.
elim (IHG1 occ1 rc rG1 e1 H5).
elim (IHG2 occ2 rc rG2 e2 H7).
simpl;tauto.
caseq (rewrite_form t1 t2 occ0 G);clean.
intros rG0 eG0 e W;inversion e;inversion_clear W.
simpl;split;intros h x;
elim (IHG occ0 (mkE Denv d x :: rc) rG0 eG0 H5);auto.
caseq (rewrite_form t1 t2 occ0 G);clean.
intros rG0 eG0 e W;inversion e;inversion_clear W.
simpl;split;intros [x h];split with x;
elim (IHG occ0 (mkE Denv d x :: rc) rG0 eG0 H5);auto.
Qed.

End with_env.



