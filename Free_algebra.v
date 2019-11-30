Require Import Bintree.
Require Import Env.

Section with_Denv.

Variable Denv:domain_env.

Record fun_entry : Type :=
mkF{F_arity: arity;
          F_result:domain;
          F_it: abstract Denv F_arity (interp_domain Denv F_result)}.

Definition signature := Store fun_entry.

Inductive term: Set :=
  App : positive -> args -> term  
| DB : nat -> term
| Var : positive -> term
 with args : Set :=
  No_args : args
| More_args : term -> args -> args.
 
Inductive occ_term :Set :=
  Not_here: occ_term
| Here: occ_term
| In_args: occ_args -> occ_term
with occ_args : Set :=
  No_occ: occ_args
| Skip_occ : occ_args -> occ_args
| More_occ : occ_term -> occ_args -> occ_args.

Definition mkVar := Var.

Fixpoint term_eq (p q:term) {struct p} :bool :=
 match p, q with
   App fp argsp,App fq argsq =>  
   if pos_eq fp fq then args_eq argsp argsq else false
 | DB ip, DB iq => nat_eq ip iq
 | Var vp, Var vq => pos_eq vp vq
 | _, _ => false
end
with args_eq (ap aq:args) {struct ap} : bool :=
  match ap, aq with
  No_args, No_args => true
  | More_args tp aap, More_args tq aaq => 
    if  term_eq tp tq then args_eq aap aaq else false
  | _, _ => false 
  end.

Lemma refl_term_eq : forall t, term_eq t t =true.
fix refl_term_eq 1.
intros [f a |i|n];simpl.
rewrite refl_pos_eq.
induction a;simpl;clean.
rewrite refl_term_eq;auto.
apply refl_nat_eq.
apply refl_pos_eq.
Qed.

Lemma refl_args_eq : forall a, args_eq a a =true.
induction a;simpl;clean.
rewrite refl_term_eq;auto.
Qed.

Fixpoint inst_term (t:term) (n:nat) (s:term) {struct s} :term :=
match s with 
  App f a => App f (inst_args t n a)
| DB i =>  if nat_eq i n then t else DB i
| Var v => Var v
end
with inst_args (t:term) (n:nat) (a:args) {struct a} :args :=
match a with
  No_args => No_args 
| More_args arg more => More_args (inst_term t n arg) (inst_args t n more)
end.

Fixpoint rewrite_term (ta tb:term) (occ:occ_term) (t:term) {struct t} :
 option term :=
  match occ with Not_here => Some t
  | Here => if term_eq t ta then Some tb else None
  | In_args aocc =>
    match t with 
       App f a => 
       match rewrite_args ta tb aocc a with None => None
       | Some rargs => Some (App f rargs)
       end
       | _ => None
     end end
with rewrite_args (ta tb:term) (aocc:occ_args) (a:args) {struct a} : 
  option args:=
  match aocc with 
    No_occ => Some a
  | Skip_occ occq => 
    match a with No_args => None
       | More_args t q => 
       match rewrite_args ta tb occq q with None => None
        | Some rq => Some (More_args t rq)
     end end
  | More_occ occ occq =>
    match a with No_args => None
    | More_args t q =>
     match rewrite_term ta tb occ t,rewrite_args ta tb occq q with
       Some rt,Some rq => Some (More_args rt rq)
     | _,_ => None
     end end end.

Variable Sigma : signature.

Fixpoint check_ground_term (C:var_ctx) (t:term) (expected:domain) 
{struct t}: bool :=
match t with
  App t a => 
   match  get t Sigma with PNone => false | PSome TE =>
   if pos_eq expected (F_result TE) then
   check_ground_args C a (F_arity TE) 
   else false end
| DB n => false
| Var p => 
  match get p C with PSome dom => pos_eq dom expected | _ => false end
end
with check_ground_args (C:var_ctx) (a:args) (rge:list domain) {struct a} : bool :=
     match a, rge with
         No_args, nil => true
       | More_args arg argv, dom::domv =>  
         if check_ground_term C arg dom then
            check_ground_args C argv domv
            else false
        | _, _ => false end.

Inductive WF_ground_term : var_ctx -> term -> domain -> Prop :=
  WF_ground_App : 
  forall hyps p argv rge dom t,
    get p Sigma=PSome (mkF rge dom t) ->
    WF_ground_args hyps argv rge -> 
    WF_ground_term hyps (App p argv) dom
| WF_ground_Var : 
  forall hyps n dom,
    get n hyps = PSome dom ->
    WF_ground_term hyps (Var n) dom 
with WF_ground_args :  var_ctx -> args -> list domain -> Prop :=
    WF_ground_No : forall hyps , WF_ground_args  hyps No_args nil
  | WF_ground_More : forall hyps arg argv dom domv, 
WF_ground_term hyps arg dom -> WF_ground_args hyps argv domv ->
WF_ground_args hyps (More_args arg argv) (dom::domv).

Lemma WF_checked_ground_term : 
  forall vars t expected, 
  check_ground_term vars t expected = true ->
  WF_ground_term vars t expected.
fix WF_checked_ground_term 2;intros hyps t expected;destruct t;simpl.
caseq (get p Sigma).
intros FE e;destruct FE;simpl.
caseq (pos_eq expected F_result0).
intro ee;rewrite (pos_eq_refl _ _ ee).
intro Hargs;left with F_arity0 F_it0;auto.
generalize F_arity0 Hargs;clear Hargs.
induction a;intro rge;destruct rge;simpl;try congruence.
left.
intro Hargs;
caseq (check_ground_term hyps t d);intro e0;rewrite e0 in Hargs.
right.
apply WF_checked_ground_term;auto.
apply IHa;auto.
congruence.
congruence.
congruence.
congruence.
caseq (get p hyps).
intro d.
intros e e0;rewrite <-(pos_eq_refl _ _ e0).
right;auto.
congruence.
Qed.

Fixpoint check_term (gamma:var_ctx) (rels:rel_ctx) (t:term) (expected:domain) 
{struct t}: bool :=
match t with
  App t a => 
  match  get t Sigma with
    PNone => false
  | PSome (mkF rge dom _) =>
    if pos_eq expected dom then
      check_args gamma rels a rge
    else false
  end
| DB n => 
  match Lget n rels with
    None => false 
  | Some dom => pos_eq expected dom 
  end 
| Var p => 
  match get p gamma with 
    PSome dom => pos_eq expected dom
  | _ => false 
 end
end
with check_args  (gamma:var_ctx) (rels:list domain) (a:args) (rge:arity) 
{struct a} : bool :=
  match a,rge with
    No_args,nil => true
  | More_args arg argv,dom::domv => 
    if check_term gamma rels arg dom then
      check_args gamma rels argv domv
    else false
  | _ , _ => false
  end.
 
Inductive WF_term (gamma:var_ctx) (rels:list domain) : term -> domain -> Prop :=
  WF_App : forall n a rge dom t, 
  get n Sigma = PSome (mkF rge dom t) -> 
 WF_args gamma rels a rge -> WF_term gamma rels (App n a) dom
| WF_DB : forall i dom, Lget i rels = Some dom -> 
      WF_term gamma rels (DB i) dom
| WF_Var : forall n dom, get n gamma = PSome dom -> 
      WF_term gamma rels (Var n) dom
with WF_args (gamma:var_ctx) (rels:list domain) : args -> arity -> Prop :=
  WF_nil : WF_args gamma rels No_args nil
| WF_cons : forall a rge arg dom, 
WF_term gamma rels arg dom -> WF_args gamma rels a rge -> 
WF_args gamma rels (More_args arg a) (dom :: rge).

Lemma WF_checked_term : forall vars rels t expected, 
check_term vars rels t expected = true ->
WF_term vars rels t expected.
fix WF_checked_term 3;intros vars rels t;destruct t;simpl.
caseq (get p Sigma).
intros [rge dom head];intros ep expected.
caseq (pos_eq expected dom).
intros edom Hargs.
rewrite (pos_eq_refl _ _ edom).
constructor 1 with rge head.
assumption.
generalize rge Hargs;clear rge head ep Hargs dom edom;induction a;
intros [ |dom domv];simpl.
left.
congruence.
congruence.
right.
generalize Hargs;clear Hargs.
caseq (check_term vars rels t dom).
intros H _ ;apply WF_checked_term;assumption.
congruence.
generalize Hargs;clear Hargs.
caseq (check_term vars rels t dom).
intros _ H;apply IHa;assumption.
congruence.
congruence.
congruence.
caseq (Lget n rels).
intros dom en expected edom.
rewrite (pos_eq_refl _ _ edom);constructor 2;assumption.
congruence.
caseq (get p vars).
intros dom.
intros en expected edom; rewrite (pos_eq_refl _ _ edom);constructor 3;assumption.
congruence.
Qed.

Lemma WF_checked_args : forall vars rels a rge, 
check_args vars rels a rge = true ->
WF_args vars rels a rge.
induction a;intros [ | dom domv].
left.
simpl;congruence.
simpl;congruence.
simpl;caseq (check_term vars rels t dom).
intros et ea;right.
apply WF_checked_term;assumption.
apply IHa;assumption.
congruence.
Qed.

Lemma WF_ground_term_term : 
  forall hyps rc t dom,
  WF_ground_term hyps t dom ->
  WF_term hyps rc t dom.
intros hyps rc;fix WF_ground_term_term 1.
intros [ f a | i | n ] dom W; inversion W;subst.
constructor 1 with rge t;trivial.
generalize rge H4;clear rge t H2 H4 W.
induction a;intros rge W;inversion W;subst.
left.
right;trivial.
apply WF_ground_term_term;trivial.
apply IHa;trivial.
constructor 3;trivial.
Qed.

Lemma WF_term_nil_ground_term :
 forall hyps t dom,
  WF_term hyps nil t dom ->
  WF_ground_term hyps t dom.
intros hyps; fix WF_term_nil_ground_term 1.
intros [ f a | i | n ] dom W; inversion W;subst.
constructor 1 with rge t;trivial.
generalize rge H3;clear rge t H1 H3 W.
induction a;intros rge W;inversion W;subst.
left.
right;trivial.
apply WF_term_nil_ground_term;trivial.
apply IHa;trivial.
destruct i;simpl in H0;clean.
constructor 2;trivial.
Qed.

Fixpoint interp_term 
(gamma:var_env Denv) (rc:rel_env Denv) (t:term) (expected:domain) {struct t}:
option (interp_domain Denv expected) :=
match t with
  App hd a =>
  match get hd Sigma with
    PNone => None
  | PSome (mkF rge dom head) => 
    match pos_eq_dec dom expected with
      right _ => None
    | left e => 
      match interp_args gamma rc a rge (interp_domain Denv dom) head with
        PNone => None
      | PSome it => Some (eq_rec _ (interp_domain Denv) it _ e)
      end
    end
  end
| DB i => 
  match Lget i rc with
    None => None
  | Some (mkE dom it) =>
    match pos_eq_dec dom expected with
      right _ => None
    | left e => Some (eq_rec _ (interp_domain Denv) it _ e)
    end
  end
| Var n =>
  match get n gamma with
    PNone => None
  | PSome (mkE dom it) =>
    match pos_eq_dec dom expected with
      right _ => None
    | left e => Some (eq_rec _ (interp_domain Denv) it _ e)
    end
  end
end
with interp_args
(gamma:var_env Denv) (rc:rel_env Denv) (a:args) (rge:arity) (S:Type) {struct a}: 
abstract Denv rge S -> Poption S := 
match a,rge return abstract Denv rge S -> Poption S with
  No_args,nil =>  @PSome _
| More_args t argv,dom::domv =>
  match interp_term gamma rc t dom with
    None => (fun _ => PNone)
  | Some arg =>
    (fun f => interp_args gamma rc argv domv S (f arg))
  end
| _ , _ => (fun _ => PNone)
end.

Lemma EFQ: forall P:Prop, false=true -> P.
congruence.
Qed.

Fixpoint term_eq_id p q  {struct p}: term_eq p q = true -> p = q :=
 match p , q  return term_eq p q = true -> p = q with
     App fp argsp, App fq argsq => 
     (if pos_eq fp fq as test return 
       pos_eq fp fq =test -> (if test then args_eq argsp argsq else false) = true ->
       App fp argsp = App fq argsq then
         (fun testf testargs =>  
          f_equal2 _ (pos_eq_refl fp fq testf) (args_eq_id argsp argsq testargs))
       else  (fun _ h => EFQ _ h)) (refl_equal (pos_eq fp fq))
    | DB ip,DB iq =>(fun h => f_equal _ (nat_eq_refl _ _ h))
    | Var vp,Var vq => (fun h => f_equal _ (pos_eq_refl _ _ h))
    | _,_ => EFQ _ 
end
with args_eq_id ap aq {struct ap}: args_eq ap aq = true -> ap = aq :=
   match ap , aq  return args_eq ap aq = true -> ap = aq with
     More_args tp argsp, More_args tq argsq => 
     (if term_eq tp tq as test return 
       term_eq tp tq = test -> (if test then args_eq argsp argsq else false) =true ->
       More_args tp argsp = More_args tq argsq then
         (fun testt testargs =>  
         f_equal2 _ (term_eq_id tp tq testt) (args_eq_id argsp argsq testargs))
       else  (fun _ h => EFQ _ h)) (refl_equal (term_eq tp tq))
   | No_args,No_args => (fun _ => refl_equal No_args)
   | _,_ => EFQ _
end.

Lemma term_eq_refl: forall vars rels dom t1 t2,
  term_eq t1 t2 = true -> 
  interp_term vars rels t1 dom =  
  interp_term vars rels t2 dom.
intros until t2; intro e; generalize (term_eq_id _ _ e).
congruence.
Qed.

Lemma args_eq_refl: forall vars rels doms T hd a1 a2,
  args_eq a1 a2 = true -> 
  interp_args vars rels a1 doms T hd =  
  interp_args vars rels a2 doms T hd.
intros until a2; intro e; generalize (args_eq_id _ _ e).
congruence.
Qed.

Lemma ground_term_invar : 
  forall hyps Venv rc t dom,
  WF_ground_term hyps t dom ->
  interp_term Venv rc t dom =
  interp_term Venv nil t dom .
intros hyps Venv rc;fix ground_term_invar 1.
intros [ f a | i | n ] dom W; inversion W;subst;simpl.
rewrite H2.
rewrite pos_eq_dec_refl.
replace (interp_args Venv rc a rge (interp_domain Denv dom) t) 
with (interp_args Venv nil a rge (interp_domain Denv dom) t). 
reflexivity.
generalize rge (interp_domain Denv dom) t H4.
clear rge t H2  H4 W.
induction a;intros rge P head W;inversion W;subst;simpl.
reflexivity.
rewrite ground_term_invar;trivial. 
case (interp_term Venv nil t dom0);trivial.
intro i;apply IHa;trivial.
reflexivity.
Qed.

Lemma interp_WF_ground_term_Some : 
  forall hyps F Venv,
  Instanceof Denv hyps F Venv->
  forall t dom, 
  WF_ground_term hyps t dom ->
  (exists x, interp_term Venv nil t dom = Some x).
intros hyps F Venv Inst. fix interp_WF_ground_term_Some 1.
intros [ f a | i | n ] dom W; inversion W;subst;simpl.
rewrite H2.
rewrite pos_eq_dec_refl;simpl.
cut (ex (fun X =>  
interp_args Venv nil a rge (interp_domain Denv dom) t =PSome X)).
intro H;destruct H;rewrite H.
exists x;trivial.
generalize rge (interp_domain Denv dom) t H4; clear rge t H2 H4 W.
induction a;intros rge P T W;inversion W;subst;simpl.
exists T;reflexivity.
elim (interp_WF_ground_term_Some t dom0 );trivial.
intros x ex;rewrite ex;apply IHa;trivial.
elim (get_Instanceof _ _ _ _ _ Inst _ H1);intros x ex.
rewrite ex.
rewrite pos_eq_dec_refl;simpl.
exists x;reflexivity.
Qed.

Lemma WF_term_instx : forall V (F:Full V) rels dom t expected,
WF_term V (rels ++ dom :: nil) t expected ->
WF_term (V \ dom) rels
  (inst_term (mkVar (index V)) (length rels) t) expected.
fix WF_term_instx 5.
intros hyps F rc dom [ f a | i | n ] expected W;simpl inst_term;inversion W;subst.
constructor 1 with rge t;trivial.
generalize rge H3;clear rge t H1 H3 W.
induction a;intros rge W;inversion W;subst;simpl inst_args.
left.
right.
apply WF_term_instx;trivial.
apply IHa;trivial.
caseq (nat_eq i (length rc));intro ei.
constructor 3.
rewrite get_push_Full;trivial.
rewrite Pcompare_refl.
rewrite Lget_app in H0.
rewrite ei in H0.
congruence.
constructor 2.
rewrite Lget_app in H0.
rewrite ei in H0;assumption.
constructor 3.
apply (Full_push_compat _ _ dom  _ F _ H0).
Qed.

Lemma WF_args_instx :forall V (F:Full V) rels dom a doms,
WF_args V (rels ++ dom :: nil) a doms ->
WF_args (V \ dom) rels
  (inst_args (mkVar (index V)) (length rels) a) doms.
induction a;intros rge W;inversion W;subst;simpl inst_args.
left.
right.
apply WF_term_instx;trivial.
apply IHa;trivial.
Qed.

Lemma term_instx : forall V F Venv, Instanceof Denv V F Venv ->
forall dom rel rels t expected, WF_term V 
(List.map (E_domain Denv) (rels ++ (mkE Denv dom rel) :: nil)) t expected ->
interp_term (Venv\mkE Denv dom rel) rels
    (inst_term (mkVar (index V)) (length rels) t) expected =
interp_term Venv (rels ++ (mkE Denv dom rel) :: nil) t expected.
intros hyps F Venv Inst dom rel rc.
fix term_instx 1.
intros [f a | i | n] expected W; inversion W;subst;simpl.
rewrite H1.
rewrite pos_eq_dec_refl.
replace
 (interp_args (Venv \ mkE Denv dom rel) rc
    (inst_args (mkVar (index hyps)) (length rc) a) rge
    (interp_domain Denv expected) t)
with
 (interp_args Venv (rc ++ mkE Denv dom rel :: nil) a rge
    (interp_domain Denv expected) t).
case  (interp_args Venv (rc ++ mkE Denv dom rel :: nil) a rge
    (interp_domain Denv expected) t);reflexivity.
generalize (interp_domain Denv expected) rge H3 t ; clear rge t H1 H3 W. 
induction a; intros P rge W; inversion W;subst;simpl.
reflexivity.
rewrite term_instx;trivial.
case (interp_term Venv (rc ++ (mkE Denv dom rel) :: nil) t dom0);clean.
intros i t0;apply IHa;trivial.
rewrite Lget_app.
caseq (nat_eq i (length rc));simpl.
rewrite get_push_Full;trivial.
rewrite (index_Instanceof Denv hyps F Venv);trivial.
rewrite Pcompare_refl.
reflexivity.
exact (Instanceof_Full _ _ _ _ Inst).
reflexivity.
elim (get_Instanceof _ _ _ _ _ Inst _ H0).
intros var en;simpl.
assert (FF:=Instanceof_Full _ _ _ _ Inst).
rewrite get_push_Full;trivial.
rewrite en.
caseq (n ?= index Venv);intro PCn.
rewrite (Pcompare_Eq_eq _ _ PCn) in en.
rewrite get_Full_Eq in en;trivial;congruence.
reflexivity.
rewrite get_Full_Gt in en;trivial;congruence.
Qed.

Lemma args_instx : forall V F Venv, Instanceof Denv V F Venv ->
forall dom rel rels a doms (T:Type) head, WF_args V 
(List.map (E_domain Denv) (rels ++ (mkE Denv dom rel) :: nil)) a doms ->
interp_args (Venv\mkE Denv dom rel) rels
     (inst_args (mkVar (index V)) (length rels) a) doms T head =
interp_args Venv (rels ++ (mkE Denv dom rel) :: nil) a doms T
     head.
induction a; intros rge T head W;inversion W;subst;simpl;clean.
rewrite (term_instx _ F Venv);trivial.
destruct (interp_term Venv (rels ++ mkE Denv dom rel :: nil) t dom0).
 apply IHa;trivial.
reflexivity.
Qed.

Lemma WF_term_inst : forall V t dom,
WF_ground_term V t dom ->
forall rels tt dd,
WF_term V (rels ++ dom :: nil) tt dd ->
WF_term V rels (inst_term t (length rels) tt) dd.
intros hyps t dom Wgt rc; fix WF_term_inst 1;intros [ f a | i | n] dd W;inversion W;
subst;simpl inst_term.
constructor 1 with rge t0;trivial.
generalize rge H3;clear W rge t0 H1 H3.
induction a;intros rge W;inversion W;subst;simpl inst_args.
left.
right.
apply WF_term_inst;trivial.
apply IHa;trivial.
rewrite Lget_app in H0.
caseq (nat_eq i (length rc));intro ei;rewrite ei in H0.
apply WF_ground_term_term.
replace dd with dom;[auto|congruence].
constructor 2;trivial.
constructor 3;trivial.
Qed.

Lemma WF_args_inst : forall V t dom,
WF_ground_term V t dom ->
forall rels a doms,
WF_args V (rels ++ dom :: nil) a doms ->
WF_args V rels (inst_args t (length rels) a) doms.
intros hyps t dd Wgt rc;induction a;intros rge W;inversion W;subst;
simpl inst_args. 
left.
right.
apply WF_term_inst with dd;trivial.
apply IHa;trivial.
Qed.

Lemma term_inst : forall V F Venv t dom x, 
Instanceof Denv V F Venv -> 
WF_ground_term V t dom ->
interp_term Venv nil t dom = Some x ->
forall rels tt dd, 
WF_term V 
(List.map (E_domain Denv) (rels ++ (mkE Denv dom x) :: nil)) tt dd -> 
interp_term Venv (rels ++ (mkE Denv dom x) :: nil) tt dd =
interp_term Venv rels (inst_term t (length rels) tt) dd.
intros hyps F Venv t dom x Inst Wgt et rc;fix term_inst 1.
intros [ f a | i | n] expected W;inversion W;subst;simpl.
rewrite H1;rewrite pos_eq_dec_refl.
replace (interp_args Venv (rc ++ mkE Denv dom x :: nil) a rge
    (interp_domain Denv expected) t0)
with (interp_args Venv rc (inst_args t (length rc) a) rge
    (interp_domain Denv expected) t0);trivial.
generalize rge (interp_domain Denv expected) t0 H3;clear rge t0 H1 H3 W.
induction a;intros rge P head W;inversion W;subst;simpl;trivial.
rewrite term_inst;trivial.
case (interp_term Venv rc (inst_term t (length rc) t0) dom0);trivial.
intro i;apply IHa;trivial.
rewrite Lget_app.
generalize H0;clear H0. 
rewrite map_app;simpl.
rewrite Lget_app.
rewrite length_map.
caseq (nat_eq i (length rc)).
intros ei edom; injection edom;clear edom;intro edom.
pattern expected;rewrite <- edom.
rewrite pos_eq_dec_refl;
rewrite (ground_term_invar hyps Venv);trivial.
rewrite et;reflexivity.
reflexivity.
reflexivity.
Qed.

Lemma args_inst : forall V F Venv t dom x,
Instanceof Denv V F Venv -> 
WF_ground_term V t dom ->
interp_term Venv nil t dom = Some x ->
forall rels a doms T P, 
WF_args V 
(List.map (E_domain Denv) (rels ++ (mkE Denv dom x) :: nil)) a doms -> 
interp_args Venv (rels ++ (mkE Denv dom x) :: nil) a doms T P =
interp_args Venv rels (inst_args t (length rels) a) doms T P.
intros hyps F Venv t dom x Inst Wgt et rc; induction a; intros rge T P W;
inversion W;subst;simpl;trivial.
replace (interp_term Venv (rc ++ (mkE Denv dom x) :: nil) t0 dom0)
 with (interp_term Venv rc (inst_term t (length rc) t0) dom0).
case (interp_term Venv rc (inst_term t (length rc) t0) dom0);trivial.
intro i;apply IHa;trivial.
symmetry;apply term_inst with hyps F;trivial.
Qed.

Lemma Weak_WF_term : forall vars dom rels t expected,
Full vars ->
WF_term vars rels t expected ->
WF_term (vars\dom) rels t expected.
fix Weak_WF_term 4.
intros hyps H rc [f a|n|i] expected F; intro W;inversion W;subst.
constructor 1 with rge t;auto.
generalize rge H4; clear rge H2 H4 t W.
induction a;intros rge W;inversion W.
left.
right.
apply Weak_WF_term;assumption.
apply IHa;assumption.
constructor 2;assumption.
constructor 3.
apply Full_push_compat;assumption.
Qed.

Lemma Weak_WF_args :forall vars dom rels a doms,
Full vars ->
WF_args vars rels a doms ->
WF_args (vars\dom) rels a doms.
induction a;intros rge F W;inversion W;subst.
left.
right.
apply Weak_WF_term;auto.
apply IHa;auto.
Qed.

Lemma Weak_interp_term:  forall V F Venv var t rels expected,
Instanceof Denv V F Venv ->
WF_term V (List.map (E_domain Denv) rels) t expected ->
interp_term Venv rels t expected=
interp_term (Venv\var)  rels t expected.
fix Weak_interp_term 5;
intros hyps F Venv var [f a | n | i] rc expected Inst W;inversion_clear W;simpl.
rewrite H.
rewrite pos_eq_dec_refl.
generalize rge  t H0.
clear H t H0 rge.
induction a;simpl interp_args.
intros rge head Wa;inversion Wa.
reflexivity.
intros rge head Wa;inversion Wa.
subst.
simpl.
rewrite <- (Weak_interp_term hyps F Venv);auto.
case (interp_term Venv rc t dom);auto.
reflexivity.
assert (FF:=Instanceof_Full _ _ _ _ Inst).
elim (get_Instanceof _ _ _ _ _ Inst _ H);trivial.
rewrite get_push_Full;trivial.
caseq (i ?= index Venv).
intro e;rewrite (Pcompare_Eq_eq _ _ e) in H.
rewrite <- (index_Instanceof _  hyps F Venv) in H;trivial.
rewrite get_Full_Eq in H;trivial;try congruence.
reflexivity.
intro e;rewrite <- (index_Instanceof _  hyps F Venv) in e;trivial.
rewrite get_Full_Gt in H;trivial;congruence.
Qed.

Lemma Weak_interp_args: forall V F Venv var S rels a doms Kont,
Instanceof Denv V F Venv ->
WF_args V (List.map (E_domain Denv) rels) a doms ->
interp_args Venv rels a doms S Kont=
interp_args (Venv\var) rels a doms S Kont.
induction a;intro rge;case rge;simpl;try reflexivity.
intros dom domv Kont Inst Wa. 
inversion Wa.
rewrite <- (Weak_interp_term _ F Venv);try assumption.
case (interp_term Venv rels t dom).
intro arg0;apply IHa;assumption.
reflexivity.
Qed.

Lemma Bind_WF_term: forall vars delta rels t expected,
WF_term vars rels t expected ->
WF_term vars (rels ++ delta) t expected.
fix Bind_WF_term 4;intros hyps delta rc [f a| i|n] dom W;inversion W;subst;try constructor.
constructor 1 with rge t;trivial.
generalize rge H3; clear rge t H1 H3 W.
induction a;intros rge W;inversion W;subst;constructor.
apply Bind_WF_term;trivial.
apply IHa;trivial.
apply Lget_app_Some;trivial.
trivial.
Qed.

Lemma Bind_WF_args : forall vars delta rels a doms,
WF_args vars rels a doms ->
WF_args vars (rels ++ delta) a doms.
induction a;intros rge W;inversion W;subst;try constructor.
apply Bind_WF_term;trivial.
apply IHa;trivial.
Qed.

Lemma Bind_interp_term: forall V F Venv delta rels t expected,
Instanceof Denv V F Venv ->
WF_term V (List.map (E_domain Denv) rels) t expected ->
interp_term Venv rels t expected =
interp_term Venv (rels++delta) t expected.
intros hyps F Venv delta rc; fix Bind_interp_term 1;
intros [ f a | i | n ] expected Inst W;inversion W; subst;simpl.
rewrite H1;rewrite pos_eq_dec_refl.
replace 
  (interp_args Venv rc a rge (interp_domain Denv expected) t)
with
  (interp_args Venv (rc ++ delta) a rge
    (interp_domain Denv expected) t);trivial.
generalize rge (interp_domain Denv expected) t H3;clear rge t H1 H3 W.
induction a;intros rge P head W;inversion W;subst;simpl;trivial.
rewrite Bind_interp_term;trivial.
case (interp_term Venv (rc ++ delta) t dom);trivial.
intro i;apply IHa;trivial.
caseq (Lget i rc);trivial.
intros o ei;rewrite (Lget_app_Some _ _ delta _ _ ei);trivial.
intro ei;assert (HH:=Lget_map _ _ (E_domain Denv) i rc).
rewrite H0 in HH;rewrite ei in HH;congruence.
reflexivity.
Qed.

Lemma Bind_interp_args: forall V F Venv delta S rels a doms Kont,
Instanceof Denv V F Venv ->
WF_args V (List.map (E_domain Denv) rels) a doms ->
interp_args Venv rels a doms S Kont=
interp_args Venv (rels++delta) a doms S Kont.
induction a;intros rge Kont Inst W;inversion W;subst;simpl;trivial.
rewrite (Bind_interp_term _ F Venv delta);trivial.
case  (interp_term Venv (rels ++ delta) t dom);trivial.
intro i;apply IHa;trivial.
Qed.

Definition type_of (hyps:var_ctx) (t:term) :
  option domain := 
  match t with 
    App f _ => 
    match get f Sigma with
      PSome (mkF _ dom _ ) => Some dom
    | PNone => None
    end
  | DB i => None
  | Var n => 
    match get n hyps with
      PSome dom => Some dom
    | _ => None
    end
end.

Lemma type_of_regular : forall hyps dom t, 
WF_ground_term hyps t dom ->
type_of hyps t = Some dom.
intros hyps dom [f a | i | n] W;inversion_clear W;simpl;rewrite H;split.
Qed.

Lemma WF_rewrite_term : forall vars dom t1 t2 rels,
WF_ground_term vars t1 dom ->
WF_ground_term vars t2 dom ->
forall t occ rt expected,
rewrite_term t1 t2 occ t = Some rt ->
WF_term vars rels t expected ->
WF_term vars rels rt expected.
intros hyps dom t1 t2 rc Wt1 Wt2. 
fix WF_rewrite_term 1;intros [ f a | i | n ] [ | | occa] rt expected;clean;simpl;intros e W.
change ((if term_eq (App f a) t1 then Some t2 else None (A:=term)) =
             Some rt) in e.
inversion_clear W;generalize e;clear e.
caseq (term_eq (App f a) t1);clean.
intros ee e;injection e;clear e;intro e;rewrite <- e.
apply WF_ground_term_term.
assert (e' := type_of_regular _ _ _ Wt1).
rewrite <- (term_eq_id _ _ ee) in e'.
simpl in e';rewrite H in e'.
inversion e';trivial.
inversion_clear W;generalize e;clear e.
caseq (rewrite_args t1 t2 occa a);clean.
intros rargs erargs e; injection e;clear e;intro e;rewrite <- e.
constructor 1 with rge t;trivial.
generalize occa rargs rge erargs H0;
clear occa rge t H H0 rargs erargs e;induction a;
intros [ | occa |occt occa] rargs rge;simpl;clean;intros e W.
inversion_clear W;generalize e;clear e.
caseq (rewrite_args t1 t2 occa a);clean.
intros ra ea e;injection e;clear e;intro e;subst.
right;auto.
apply IHa with occa;trivial.
inversion_clear W;generalize e;clear e.
caseq (rewrite_term t1 t2 occt t);clean.
intros rt0 et0.
caseq (rewrite_args t1 t2 occa a);clean.
intros ra ea e;injection e;clear e;intro e;subst.
right.
apply WF_rewrite_term with t occt;trivial.
apply IHa with occa;trivial.
clear WF_rewrite_term.
destruct t1;clean;inversion Wt1.
caseq t1.
intros p a et1;rewrite et1 in e;clean. 
intros i et1;rewrite et1 in e;clean. 
intros p et1;rewrite et1 in e.
caseq (pos_eq n p);
intros ee;rewrite ee in e;clean; rewrite <- (pos_eq_refl _ _ ee) in et1. 
assert (e' := type_of_regular _ _ _ Wt1).
rewrite et1 in e'.
inversion_clear W.
simpl in e';rewrite H in e'.
apply WF_ground_term_term.
congruence.
Qed.

Lemma WF_rewrite_args : forall vars dom t1 t2 rels,
WF_ground_term vars t1 dom ->
WF_ground_term vars t2 dom ->
forall a occ ra doms,
rewrite_args t1 t2 occ a = Some ra ->
WF_args vars rels a doms ->
WF_args vars rels ra doms.
intros hyps dom t1 t2 rc Wt1 Wt2 a.
induction a;intros [ | occa |occt occa] rargs rge;simpl;clean;intros e W.
inversion_clear W;generalize e;clear e.
caseq (rewrite_args t1 t2 occa a);clean.
intros ra ea e;injection e;clear e;intro e;subst.
right;auto.
apply IHa with occa;auto.
inversion_clear W;generalize e;clear e.
caseq (rewrite_term t1 t2 occt t);clean.
intros rt et.
caseq (rewrite_args t1 t2 occa a);clean.
intros ra ea e;injection e;clear e;intro e;subst.
right.
apply WF_rewrite_term with dom t1 t2 t occt;auto.
apply IHa with occa;auto.
Qed.

Lemma term_rewrite : forall V F Venv,
Instanceof Denv V F Venv->
forall dom t1 t2 it1 it2,  
WF_ground_term V t1 dom ->
WF_ground_term V t2 dom ->
interp_term Venv nil t1 dom = Some it1 ->
interp_term Venv nil t2 dom = Some it2 ->
it1 = it2 ->
forall rels t occ rt expected,
rewrite_term t1 t2 occ t = Some rt ->
WF_term V (List.map (E_domain Denv) rels) t expected ->
interp_term Venv rels t expected =
interp_term Venv rels rt expected.
intros ctx F Venv Inst dom t1 t2 it1 it2 Wt1 Wt2 et1 et2 eit rels
;fix term_rewrite 1;intros [f a | i | n ] [ | | occa] rt expected; clean.
intro e;simpl rewrite_term in e;congruence.
intro e;change ((if term_eq (App f a) t1 then Some t2 else None) = Some rt) in e.
caseq (term_eq (App f a) t1);intro e';rewrite e' in e;clean.
assert (ee:=(term_eq_id _ _ e'));clear e'.
injection e;clear e;intro e.
intro W;inversion_clear W.
generalize (type_of_regular _ _ _ Wt1).
rewrite <- ee;simpl type_of.
rewrite H.
intro eee;injection eee;clear eee;intro eee.
rewrite ee.
rewrite <- e.
rewrite eee.
rewrite (ground_term_invar _ Venv rels t1 dom Wt1).
rewrite (ground_term_invar _ Venv rels t2 dom Wt2).
congruence.
simpl.
caseq (rewrite_args t1 t2 occa a);clean.
intros ra ea e W;inversion e;inversion W;simpl.
rewrite H2;rewrite pos_eq_dec_refl.
replace 
(interp_args Venv rels ra rge (interp_domain Denv expected) t)
with 
(interp_args Venv rels a rge (interp_domain Denv expected) t).
reflexivity.
subst.
generalize occa ra rge (interp_domain Denv expected) t ea H4.
clear occa expected ra ea W rge t H2 H4 e.
induction a;intros [ |occq| occa occq ] rargs rge T K;clean;
try solve [intro e;inversion e;split;trivial].
simpl.
caseq (rewrite_args t1 t2 occq a);clean.
intros rq eq e W;inversion e;inversion W;subst.
simpl.
case (interp_term Venv rels t dom0);trivial.
intro i;apply IHa with occq;trivial.
simpl.
caseq (rewrite_term t1 t2 occa t);clean.
intros rt et.
caseq (rewrite_args t1 t2 occq a);clean.
intros rq eq e W;inversion e;inversion W;subst.
simpl.
replace 
(interp_term Venv rels rt dom0)
with 
(interp_term Venv rels t dom0).
case (interp_term Venv rels t dom0);trivial.
intro i;apply IHa with occq;trivial.
apply term_rewrite with occa;trivial.
simpl rewrite_term;congruence.
intro e;change ((if term_eq (DB i) t1 then Some t2 else None) = Some rt) in e.
generalize e;clear e.
caseq ( term_eq (DB i) t1);clean.
intro e;rewrite <- (term_eq_id _ _ e) in et1;inversion et1.
simpl rewrite_term;congruence.
intro e;change ((if term_eq (Var n) t1 then Some t2 else None) = Some rt) in e.
generalize e;clear e.
caseq (term_eq (Var n) t1);clean.
intro e';assert (e:= term_eq_id _ _ e').
rewrite e.
clear e';intro e';injection e';clear e';intro e'.
rewrite <- e'.
intro W; rewrite <- e in W;inversion_clear W.
generalize (type_of_regular _ _ _ Wt1).
rewrite <- e;simpl type_of;rewrite H.
intro eee;injection eee;clear eee;intro eee.
rewrite e.
rewrite eee.
rewrite (ground_term_invar _ Venv rels t1 dom Wt1).
rewrite (ground_term_invar _ Venv rels t2 dom Wt2).
congruence.
Qed.


Lemma args_rewrite :
forall V F Venv,
Instanceof Denv V F Venv->
forall dom t1 t2 it1 it2,  
WF_ground_term V t1 dom ->
WF_ground_term V t2 dom ->
interp_term Venv nil t1 dom = Some it1 ->
interp_term Venv nil t2 dom = Some it2 ->
it1 = it2 ->
forall rels a occ ra doms T K,
rewrite_args t1 t2 occ a = Some ra ->
WF_args V (List.map (E_domain Denv) rels) a doms ->
interp_args Venv rels a doms T K =
interp_args Venv rels ra doms T K.
induction a;intros [ |occq| occa occq ] rargs rge T K;clean;
try solve [intro e;inversion e;split;trivial].
simpl.
caseq (rewrite_args t1 t2 occq a);clean.
intros rq eq e W;inversion e;inversion W.
generalize H3;clear H3;subst;intro H3.
simpl.
case (interp_term Venv rels t dom0);trivial.
intro i.
apply IHa with occq;trivial.
simpl.
caseq (rewrite_term t1 t2 occa t);clean.
intros rt et.
caseq (rewrite_args t1 t2 occq a);clean.
intros rq eq e W;inversion e;inversion W.
generalize H3;clear H3;subst;intro H3.
simpl.
replace 
(interp_term Venv rels rt dom0)
with 
(interp_term Venv rels t dom0).
case (interp_term Venv rels t dom0);trivial.
intro i.
apply IHa with occq;trivial.
apply term_rewrite with V F dom t1 t2 it2 it2 occa;trivial.
Qed.

End with_Denv.
