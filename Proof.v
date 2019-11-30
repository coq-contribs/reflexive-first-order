Require Import Bintree.
Require Import Bool.
Require Import Env.
Require Import Free_algebra.
Require Import Form.
Require Import Sequent.

Section With_env.

Variable Denv: domain_env.
Variable Sigma: Free_algebra.signature Denv.
Variable Pi : signature Denv.

Notation "[ T ; i ]" := (mkE Denv i T).

Inductive dir:Set := fore:dir | back:dir.

Inductive proof:Set :=
  Ax : positive -> proof
| I_Equal : proof
| E_Equal_in_concl : positive -> dir -> occ_form -> proof -> proof
| E_Equal_in_hyp : positive -> positive -> dir -> occ_form -> proof -> proof
| D_Equal : positive -> proof -> proof
| E_Absurd : positive -> proof
| I_Arrow : proof -> proof
| E_Arrow : positive -> positive -> proof -> proof
| D_Arrow : positive -> proof -> proof -> proof
| I_And : proof -> proof -> proof
| E_And : positive -> proof -> proof
| D_And : positive -> proof -> proof
| I_Or1 : proof -> proof
| I_Or2 : proof -> proof
| E_Or : positive -> proof -> proof -> proof
| D_Or : positive -> proof -> proof
| I_Forall : proof -> proof
| E_Forall : positive -> term -> proof -> proof
| D_Forall : positive -> proof -> proof -> proof
| I_Exists : term -> proof -> proof
| E_Exists : positive -> proof -> proof
| D_Exists : positive -> proof -> proof
| Cut : form -> proof -> proof -> proof
| Dynamic : (var_ctx -> hyp_ctx -> form -> proof) -> proof

(*| Meta : forall lvars lhyps G, interp Denv Sigma Pi lvars lhyps G -> proof*).

Notation "A =>> B":= (Arrow A B) (at level 58, right associativity) : form_scope.
Infix "//\\" := And (at level 56, right associativity).
Infix "\\//" := Or (at level 57, right associativity).
Notation " !! d , F" := (Forall d F) (at level 59, right associativity) : form_scope.
Notation " ?? d , F" := (Exists d F) (at level 59, right associativity) : form_scope.
Notation "#" := Absurd.

Open Scope form_scope.

Fixpoint check_proof (vars:var_ctx) (hyps:hyp_ctx) (gl:form) (P:proof) {struct P}: bool :=
 match P with
   Ax i => 
     match get i hyps with
         PSome F => form_eq F gl
        | _ => false
    end
| I_Equal =>
     match gl with
        Equal dom t1 t2 => term_eq t1 t2
        | _ => false
     end
| E_Equal_in_concl i sign occ p =>
     match get i hyps with
         PSome (Equal dom t1 t2) =>
       match 
         (if sign then rewrite_form t1 t2 occ gl else rewrite_form t2 t1 occ gl) 
       with None => false
       | Some rgl => check_proof vars hyps rgl p
       end
       | _ => false
     end
| E_Equal_in_hyp i j sign occ p =>
     match get i hyps,get j hyps with
         PSome G,PSome (Equal dom t1 t2) =>
       match 
         (if sign then rewrite_form t1 t2 occ G else rewrite_form t2 t1 occ G) 
       with None => false
       | Some rG => check_proof vars (hyps \ rG) gl p
       end
       | _,_ => false
     end
| D_Equal i p =>
    match get i hyps with
       PSome (Equal dom t1 t2 =>> C) => 
       if term_eq t1 t2 then
          check_proof vars (hyps \ C) gl p
       else false
        | _ => false
     end
| E_Absurd i =>
    match get i hyps with
      PSome # =>true
    | _ => false
    end
| I_Arrow p =>
   match gl with
      A =>> B  => check_proof vars (hyps \ A) B p
   | _ => false        
    end 
| E_Arrow i j p =>
   match get i hyps with
       PSome A =>
   match get j hyps with
       PSome (B =>> C) =>
         if form_eq A B then 
            check_proof vars (hyps \ C) gl p
         else false
      | _  => false
    end
    | _ => false
    end
| D_Arrow i p1 p2 => 
   match get i hyps with
      PSome  ((A =>>B)=>>C) =>
     if  (check_proof vars (hyps \ (B =>> C) \ A) B p1) then
      (check_proof vars (hyps \ C) gl p2)
      else false 
    | _ => false
  end
| I_And p1 p2 =>
  match gl with
      A //\\ B  => 
      if check_proof vars hyps A p1 then check_proof vars hyps B p2 else false
   | _ => false        
  end 
| E_And i p =>
  match get i hyps with
       PSome (A //\\ B) =>
            check_proof vars (hyps \ A \ B) gl p
       | _  => false
    end
| D_And i p =>
  match get i hyps with
       PSome (A //\\ B =>> C) =>
            check_proof vars (hyps \ (A =>> B =>> C)) gl p
       | _  => false
    end
| I_Or1 p =>
  match gl with
      A \\// B  => 
        check_proof vars hyps A p
   | _ => false        
  end 
| I_Or2 p =>
  match gl with
      A \\// B  => 
        check_proof vars hyps B p
   | _ => false        
  end 
| E_Or i p1 p2 =>
 match get i hyps with
   PSome (A \\// B) =>
     if check_proof vars (hyps \ A) gl p1 then
        check_proof vars (hyps \ B) gl p2 else false
    | _ => false
  end
| D_Or i p =>
  match get i hyps with
       PSome (A \\// B =>> C) =>
            check_proof vars (hyps \ (A =>> C) \ (B =>> C)) gl p
       | _  => false
    end
| I_Forall p =>
   match gl with
      !! d, F => check_proof (vars \ d) hyps (inst_form (mkVar (index vars)) 0 F)  p
   | _ => false        
    end 
| E_Forall i t p =>
   match get i hyps with
       PSome (!! d, F) =>
       if check_ground_term Denv Sigma vars t d then 
       check_proof vars (hyps \ inst_form t 0 F) gl p
       else false
    | _ => false
    end
| D_Forall i p1 p2 => 
   match get i hyps with
      PSome ((!!d,F)=>>C) =>
     if  (check_proof vars hyps (!!d,F) p1) then
      (check_proof vars (hyps \ C) gl p2)
      else false 
    | _ => false
  end
| I_Exists t p =>
   match gl with 
     ?? d, F =>
       if check_ground_term Denv Sigma vars t d then 
       check_proof vars hyps  (inst_form t 0 F) p
       else false
    | _ => false
    end
| E_Exists i p =>
   match get i hyps with
      PSome (?? d, F) =>
      check_proof (vars \ d) (hyps \ inst_form (mkVar (index vars)) 0 F) gl p
      | _ => false
   end
| D_Exists i p =>
    match get i hyps with
      PSome ((?? d, F) =>> C) =>
      check_proof vars (hyps \ (!! d, F =>> C))  gl p
      | _ => false
   end
| Cut A p1 p2 =>
    if check_form Denv Sigma Pi vars nil A then
    if check_proof vars hyps A p1 then
       check_proof vars (hyps \ A) gl  p2
       else false else false
| Dynamic F => check_proof vars hyps gl (F vars hyps gl) 
(*| Meta lvars lhyps goal  H =>
    if form_eq goal gl then
    if equiv domain pos_eq lvars 1 vars then
       equiv form form_eq lhyps 1 hyps 
       else false
       else false *)
end. 


Inductive WF_proof: var_ctx -> hyp_ctx -> form -> proof -> Prop :=
  WF_Ax : 
  forall vars hyps goal goal' i ,
    get i hyps = PSome goal' ->
    form_eq goal' goal = true -> 
    WF_proof vars hyps goal (Ax i)
| WF_I_Equal : 
  forall vars hyps dom t1 t2,
     term_eq t1 t2 = true -> 
     WF_proof vars hyps (Equal dom t1 t2) I_Equal
| WF_E_Equal_fore_in_concl :
  forall vars hyps dom t1 t2 goal i occ rgoal prf,
     get i hyps = PSome (Equal dom t1 t2) ->
     rewrite_form t1 t2 occ goal=Some rgoal ->
     WF_proof vars hyps rgoal prf ->
     WF_proof vars hyps goal (E_Equal_in_concl i fore occ prf)
| WF_E_Equal_back_in_concl :
  forall vars hyps dom t1 t2 goal i occ rgoal prf,
     get i hyps = PSome (Equal dom t1 t2) ->
     rewrite_form t2 t1 occ goal=Some rgoal ->
     WF_proof vars hyps rgoal prf ->
     WF_proof vars hyps goal (E_Equal_in_concl i back occ prf)
| WF_E_Equal_fore_in_hyp :
  forall vars hyps dom t1 t2 G rG goal i j occ prf,
     get i hyps = PSome G ->
     get j hyps = PSome (Equal dom t1 t2) ->
     rewrite_form t1 t2 occ G=Some rG ->
     WF_proof vars (hyps \ rG) goal prf ->
     WF_proof vars hyps goal (E_Equal_in_hyp i j fore occ prf)
| WF_E_Equal_back_in_hyp :
  forall vars hyps dom t1 t2 G rG goal i j occ prf,
     get i hyps = PSome G ->
     get j hyps = PSome (Equal dom t1 t2) ->
     rewrite_form t2 t1 occ G=Some rG ->
     WF_proof vars (hyps \ rG) goal prf ->
     WF_proof vars hyps goal (E_Equal_in_hyp i j back occ prf)
| WF_D_Equal :
  forall vars hyps dom t1 t2 C goal i prf,
    get i hyps = PSome (Equal dom t1 t2 =>> C) ->
  term_eq t1 t2 = true ->
  WF_proof vars (hyps \ C) goal prf ->
  WF_proof vars hyps goal (D_Equal i prf)
| WF_E_Absurd :
  forall vars hyps goal i,
    get i hyps = PSome # ->
  WF_proof vars hyps goal (E_Absurd i)
| WF_I_Arrow : 
  forall vars hyps hyp goal prf,
    WF_proof vars (hyps \ hyp) goal prf ->
    WF_proof vars hyps (hyp =>> goal) (I_Arrow prf)
| WF_E_Arrow :
  forall vars hyps A A' B goal i j prf,
    get i hyps = PSome A ->
    get j hyps = PSome (A' =>> B) ->
    form_eq A A' = true ->
    WF_proof vars (hyps \ B) goal prf ->
    WF_proof vars hyps goal (E_Arrow i j prf)
| WF_D_Arrow :
  forall vars hyps A B C goal i prf1 prf2,
    get i hyps = PSome ((A=>>B)=>>C) ->
    WF_proof vars (hyps \ (B =>> C) \ A) B prf1 ->
    WF_proof vars (hyps \ C) goal prf2 ->
    WF_proof vars hyps goal (D_Arrow i prf1 prf2)
| WF_I_And : 
  forall vars hyps A B prf1 prf2,
    WF_proof vars hyps A prf1 ->
    WF_proof vars hyps B prf2 ->
    WF_proof vars hyps (A //\\ B) (I_And prf1 prf2)
| WF_E_And :
  forall vars hyps A B goal i prf,
    get i hyps = PSome (A //\\ B) ->
    WF_proof vars (hyps \ A \ B) goal prf ->
    WF_proof vars hyps goal (E_And i prf)
| WF_D_And :
  forall vars hyps A B C goal i prf,
    get i hyps = PSome ((A //\\ B)=>>C) ->
    WF_proof vars (hyps \ (A =>> B =>> C)) goal prf ->
    WF_proof vars hyps goal (D_And i prf)
| WF_I_Or1 : 
  forall vars hyps A B prf,
    WF_proof vars hyps A prf ->
    WF_proof vars hyps (A \\// B) (I_Or1 prf)
| WF_I_Or2 : 
  forall vars hyps A B prf,
    WF_proof vars hyps B prf ->
    WF_proof vars hyps (A \\// B) (I_Or2 prf)
| WF_E_Or :
  forall vars hyps A B goal i prf1 prf2,
    get i hyps = PSome (A \\// B) ->
    WF_proof vars (hyps \ A) goal prf1 ->
    WF_proof vars (hyps \ B) goal prf2 ->
    WF_proof vars hyps goal (E_Or i prf1 prf2)
| WF_D_Or :
  forall vars hyps A B C goal i prf,
    get i hyps = PSome ((A \\// B)=>>C) ->
    WF_proof vars (hyps \ (A =>> C) \ (B =>> C)) goal prf ->
    WF_proof vars hyps goal (D_Or i prf)
| WF_I_Forall :
  forall vars hyps dom goal prf,
     WF_proof (vars \ dom) hyps (inst_form (mkVar (index vars)) 0 goal) prf ->
     WF_proof vars hyps (!!dom,goal) (I_Forall prf)
| WF_E_Forall :
  forall vars hyps dom F t goal i prf,
     get i hyps = PSome (!!dom,F) ->
     WF_ground_term Denv Sigma vars t dom ->
     WF_proof vars (hyps \ (inst_form t 0 F)) goal prf ->
     WF_proof vars hyps goal (E_Forall i t prf)
| WF_D_Forall :
   forall vars hyps dom F C goal i prf1 prf2,
     get i hyps = PSome ((!!dom,F) =>> C) ->
     WF_proof vars hyps (!!dom,F) prf1 ->
     WF_proof vars (hyps \ C) goal prf2 ->
     WF_proof vars hyps goal (D_Forall i prf1 prf2)
| WF_I_Exists :
 forall vars hyps dom F t prf,
    WF_ground_term Denv Sigma vars t dom ->
    WF_proof vars hyps (inst_form t 0 F) prf ->
    WF_proof vars hyps (?? dom,F) (I_Exists t prf)
| WF_E_Exists :
  forall vars hyps dom F goal i prf,
     get i hyps = PSome (??dom,F) ->
     WF_proof (vars \ dom) (hyps \ inst_form (mkVar (index vars)) 0 F) goal prf ->
     WF_proof vars hyps goal (E_Exists i prf)
| WF_D_Exists :
   forall vars hyps dom F C goal i prf,
     get i hyps = PSome ((??dom,F) =>> C) ->
     WF_proof vars (hyps \ (!!dom,F=>>C)) goal prf ->
     WF_proof vars hyps goal (D_Exists i prf)
| WF_Cut :
  forall vars hyps goal A prf1 prf2,
  WF_form Denv Sigma Pi vars nil A -> 
  WF_proof vars hyps A prf1 ->
  WF_proof vars (hyps \ A) goal prf2 ->
  WF_proof vars hyps goal (Cut A prf1 prf2)
| WF_Dynamic :
  forall vars hyps goal F,
  WF_proof vars hyps goal (F vars hyps goal) ->
  WF_proof vars hyps goal (Dynamic F)
(*| WF_Meta : 
   forall vars hyps lvars lhyps goal goal' 
   (H:interp Denv Sigma Pi lvars lhyps goal'),
   equiv domain pos_eq lvars 1 vars = true ->
   equiv form form_eq lhyps 1 hyps = true -> 
   form_eq goal' goal=true ->
   WF_proof vars hyps goal (Meta lvars lhyps goal' H)*).

Lemma WF_checked_proof : 
  forall prf vars hyps goal,
    check_proof vars hyps goal prf = true ->
    WF_proof vars hyps goal prf.
induction prf;simpl;intros vars hyps goal.
caseq (get p hyps);intros f ep;clean.
intro ef.
apply WF_Ax with f;auto.
destruct goal;clean.
intro et;apply WF_I_Equal;auto.
caseq (get p hyps);intros f ef;destruct f;clean;destruct d.
caseq (rewrite_form t t0 o goal);clean.
intros;apply WF_E_Equal_fore_in_concl with d0 t t0 f;auto.
caseq (rewrite_form t0 t o goal);clean.
intros;apply WF_E_Equal_back_in_concl with d0 t t0 f;auto.
caseq (get p hyps);intros f ef;clean.
caseq (get p0 hyps);intros f0 ef0;clean.
destruct f0;clean;destruct d.
caseq (rewrite_form t t0 o f);clean.
intros;apply WF_E_Equal_fore_in_hyp with d0 t t0 f f0;auto.
caseq (rewrite_form t0 t o f);clean.
intros;apply WF_E_Equal_back_in_hyp with d0 t t0 f f0;auto.
caseq (get p hyps);intros f ef;destruct f;clean.
destruct f1;clean.
caseq (term_eq t t0);clean.
intros et ee.
 apply WF_D_Equal with d t t0 f2;auto.
caseq (get p hyps);intros f ef;destruct f;clean.
intros;apply WF_E_Absurd; auto.
destruct goal;clean.
intros;apply WF_I_Arrow; auto.
caseq (get p hyps);intros f ef;clean.
caseq (get p0 hyps);intros f0 ef0;clean.
destruct f0;clean.
caseq (form_eq f f0_1);clean.
intros ee ec;apply WF_E_Arrow with f f0_1 f0_2;auto.
caseq (get p hyps);intros f ef;destruct f;clean.
destruct f1;clean.
caseq (check_proof vars (hyps \ (f1_2 =>> f2) \ f1_1) f1_2 prf1);clean.
intros;apply WF_D_Arrow with f1_1 f1_2 f2;auto.
destruct goal;clean.
caseq (check_proof vars hyps goal1 prf1);clean.
intros;apply WF_I_And;auto.
caseq (get p hyps);intros f ef;destruct f;clean.
intros;apply WF_E_And with f1 f2;auto.
caseq (get p hyps);intros f ef;destruct f;clean.
destruct f1;clean.
intros;apply WF_D_And with f1_1 f1_2 f2;auto.
destruct goal;clean.
intros;apply WF_I_Or1;auto.
destruct goal;clean.
intros;apply WF_I_Or2;auto.
caseq (get p hyps);intros f ef;destruct f;clean.
caseq (check_proof vars (hyps \ f1) goal prf1);clean.
intros;apply WF_E_Or with f1 f2;auto.
caseq (get p hyps);intros f ef;destruct f;clean.
destruct f1;clean.
intros;apply WF_D_Or with f1_1 f1_2 f2;auto.
destruct goal;clean.
intros;apply WF_I_Forall;auto.
caseq (get p hyps);intros f ef;destruct f;clean.
caseq (check_ground_term Denv Sigma vars t d);clean.
intros;apply WF_E_Forall with d f;auto.
apply WF_checked_ground_term;auto.
caseq (get p hyps);intros f ef;destruct f;clean.
destruct f1;clean. 
caseq (check_proof vars hyps (!!d,f1) prf1);clean.
intros;apply WF_D_Forall with d f1 f2;auto.
destruct goal;clean.
caseq (check_ground_term Denv Sigma vars t d);clean.
intros;apply WF_I_Exists ;auto.
apply WF_checked_ground_term;auto.
caseq (get p hyps);intros f ef;destruct f;clean.
intros;apply WF_E_Exists with d f;auto.
caseq (get p hyps);intros f ef;destruct f;clean;destruct f1;clean.
intros;apply WF_D_Exists with d f1 f2;auto.
caseq (check_form Denv Sigma Pi vars nil f);clean.
intro ef.
caseq (check_proof vars hyps f prf1);clean.
intros e1 e2.
apply WF_Cut;auto.
apply WF_checked_form;assumption.
intro;apply WF_Dynamic;apply H;assumption.
(*caseq (form_eq G goal);clean.
intro he;caseq (equiv domain pos_eq lvars 1 vars);clean.
intros ev eh.
apply WF_Meta;auto.*)
Qed.

Theorem Fundamental:forall prf vars Fv hyps Fh goal, 
WF_proof vars hyps goal prf -> 
WF_seq Denv Sigma Pi vars hyps Fh goal -> 
interp_seq Denv Sigma Pi vars Fv hyps Fh goal.

Proof.

intros prf vars Fv hyps Fh goal WFP.

induction WFP;simpl;intro W;inversion W.

(* axiom *)

generalize (Project Denv Sigma Pi  _ Fv _ _ _ _ H H1) .
unfold interp_seq;apply Compose1.
intros Venv Inst.
apply (proj1 (form_eq_refl Denv Sigma Pi _ _ H0 Venv nil)).

(* equal intro (reflexivity) *)

unfold interp_seq;simpl;apply Compose0;intros Venv Inst.
rewrite (term_eq_refl Denv Sigma Venv nil dom _ _ H).
destruct (interp_term Denv Sigma Venv nil t2 dom);auto.

(* equal elim (rewrite) fore in concl *)

assert (Wi:=WF_form_hyp _ _ _ _ _ _ _ _ H H1).
elim (WF_eq_members _ _ _ _ _ _ _  Wi).
intros W1 W2.
assert (HH:interp_seq Denv Sigma Pi vars Fv hyps Fh rgoal).
apply IHWFP.
split;trivial.
apply WF_rewrite_form with dom t1 t2 goal occ;trivial.
generalize (Project  _ _ _ _ Fv _ Fh _ _ H H1) HH.
unfold interp_seq;simpl;apply Compose2;intros Venv Inst.
generalize (interp_WF_ground_term_Some _ _ _ _ _ Inst _ _ W1)
(interp_WF_ground_term_Some _ _ _ _ _ Inst _ _ W2).
intros [it1 e1] [it2 e2].
rewrite e1;rewrite e2;intro e3.
elim (form_rewrite _ _ _ _ _ _ Inst _ _ _ _ _ W1 W2 e1 e2 e3 _ _ nil _ H0 H2).
auto.

(* equal elim (rewrite) back in concl *)

assert (Wi:=WF_form_hyp _ _ _ _ _ _ _ _ H H1).
elim (WF_eq_members _ _ _ _ _ _ _ Wi).
intros W1 W2.
assert (HH:interp_seq Denv Sigma Pi vars Fv hyps Fh rgoal).
apply IHWFP.
split;trivial.
apply WF_rewrite_form with dom t2 t1 goal occ;trivial.
generalize (Project  _ _ _ _ Fv _ Fh _ _ H H1) HH.
unfold interp_seq;simpl;apply Compose2;intros Venv Inst.
generalize (interp_WF_ground_term_Some _ _ _ _ _ Inst _ _ W1)
(interp_WF_ground_term_Some _ _ _ _ _ Inst _ _ W2).
intros [it1 e1] [it2 e2].
rewrite e1;rewrite e2;intro e3;symmetry in e3.
elim (form_rewrite _ _ _ _ _ _ Inst _ _ _ _ _ W2 W1 e2 e1 e3 _ _ nil _ H0 H2).
auto.

(* equal elim (rewrite) fore in hyp *)

assert (Wi:=WF_form_hyp _ _ _ _ _ _ _ _ H H2).
assert (Wj:=WF_form_hyp _ _ _ _ _ _ _ _ H0 H2).
elim (WF_eq_members _ _ _ _ _ _ _  Wj).
intros W1 W2.
assert (HH:interp_seq Denv Sigma Pi vars Fv (hyps \ rG) (F_push _ _ Fh) goal).
apply IHWFP.
split;trivial.
constructor 2;trivial.
apply WF_rewrite_form with dom t1 t2 G occ;trivial.
generalize (Project  _ _ _ _ Fv _ Fh _ _ H0 H2) (Project  _ _ _ _ Fv _ Fh _ _ H H2) HH.
unfold interp_seq;simpl;apply Compose3;intros Venv Inst.
generalize (interp_WF_ground_term_Some _ _ _ _ _ Inst _ _ W1)
(interp_WF_ground_term_Some _ _ _ _ _ Inst _ _ W2).
intros [it1 e1] [it2 e2].
rewrite e1;rewrite e2;intro e3.
elim (form_rewrite _ _ _ _ _ _ Inst _ _ _ _ _ W1 W2 e1 e2 e3 _ _ nil _ H1 Wi).
auto.

(* equal elim (rewrite) back in hyp *)

assert (Wi:=WF_form_hyp _ _ _ _ _ _ _ _ H H2).
assert (Wj:=WF_form_hyp _ _ _ _ _ _ _ _ H0 H2).
elim (WF_eq_members _ _ _ _ _ _ _  Wj).
intros W1 W2.
assert (HH:interp_seq Denv Sigma Pi vars Fv (hyps \ rG) (F_push _ _ Fh) goal).
apply IHWFP.
split;trivial.
constructor 2;trivial.
apply WF_rewrite_form with dom t2 t1 G occ;trivial.
generalize (Project  _ _ _ _ Fv _ Fh _ _ H0 H2) (Project  _ _ _ _ Fv _ Fh _ _ H H2) HH.
unfold interp_seq;simpl;apply Compose3;intros Venv Inst.
generalize (interp_WF_ground_term_Some _ _ _ _ _ Inst _ _ W1)
(interp_WF_ground_term_Some _ _ _ _ _ Inst _ _ W2).
intros [it1 e1] [it2 e2].
rewrite e1;rewrite e2;intro e3;symmetry in e3.
elim (form_rewrite _ _ _ _ _ _ Inst _ _ _ _ _ W2 W1 e2 e1 e3 _ _ nil _ H1 Wi).
auto.

(* equal destruct (reflexivity) *)

assert (Wi:=WF_form_hyp _ _ _ _ _ _ _ _ H H1).
generalize (Project  _ _ _ _ Fv _ Fh _ _ H H1).
assert (HW:WF_seq Denv Sigma Pi vars (hyps \ C) 
                    (F_push C hyps Fh) goal).
constructor;trivial.
inversion_clear Wi;auto.
constructor;trivial.
assert (He:interp_seq Denv Sigma Pi vars Fv hyps Fh (Equal dom t1 t2)).
unfold interp_seq;simpl;apply Compose0;intros Venv Inst;trivial.
rewrite (term_eq_refl Denv Sigma Venv nil dom _ _ H0).
destruct (interp_term Denv Sigma Venv nil t2 dom);auto.
generalize He (IHWFP Fv (F_push _ _ Fh) HW).
unfold interp_seq;simpl.
apply Compose3;auto.

(* absurd elim (EFQ) *)

generalize (Project  _ _ _ _ Fv _ _ _ _ H H0).
unfold interp_seq;simpl;apply Compose1;intros Venv Inst h;elim h.

(* arrow intro *)

apply (IHWFP Fv (F_push _ _ Fh)).
inversion H0.
constructor 1;trivial.
constructor 2;trivial.

(* arrow elim *)

assert (HH:interp_seq Denv Sigma Pi vars Fv (hyps \ B) (F_push _ _ Fh) goal).
apply IHWFP.
split;trivial.
constructor 2;trivial.
cut (WF_form Denv Sigma Pi vars nil (A' =>> B)).
intro WW;inversion WW;trivial.
apply WF_form_hyp with hyps Fh j;trivial.
generalize HH;cut (interp_seq Denv Sigma Pi vars Fv hyps Fh B).
unfold interp_seq;simpl; apply Compose2; auto.
generalize (Project _ _ _ _ Fv _ _ _ _ H H2) (Project _ _ _ _ Fv _ _ _ _ H0 H2).
unfold interp_seq;simpl; apply Compose2;intros Venv Inst;
assert (h:=proj1 (form_eq_refl Denv Sigma Pi _ _ H1 Venv nil));auto.

(* arrow destruct *) 

assert (WW:WF_form Denv Sigma Pi vars nil ((A =>> B) =>> C)).
apply WF_form_hyp with hyps Fh i;trivial.
inversion WW;inversion H5;trivial.
subst.
assert (HH1:interp_seq Denv Sigma Pi vars Fv (hyps \ (B =>> C) \ A) 
           (F_push _ _ (F_push _ _ Fh)) B).
apply IHWFP1;split;auto.
constructor 2;auto. 
constructor;trivial.
constructor;trivial.
assert (HH2:interp_seq Denv Sigma Pi vars Fv (hyps \ C ) 
           (F_push _ _ Fh) goal).
apply IHWFP2;split;auto.
constructor 2;trivial.
generalize (Project _ _ _ _ Fv _ _ _ _ H H0) HH1 HH2;
unfold interp_seq;simpl;apply Compose3.
intros Venv Inst h h1 h2.
apply h2;apply h;intro hA;apply h1.
intro hB;apply h;intros _;apply hB.
apply hA.

(* and intro *)

inversion_clear H0.
assert (HH1:interp_seq Denv Sigma Pi vars Fv hyps Fh A).
apply IHWFP1;split;trivial.
assert (HH2:interp_seq Denv Sigma Pi vars Fv hyps Fh B).
apply IHWFP2;split;trivial.
generalize HH1 HH2;unfold interp_seq;simpl;apply Compose2.
intros Venv Inst h1 h2;split;trivial.

(* and elim *)

assert (Wi:=WF_form_hyp _ _ _ _ _ _ _ _ H H0).
inversion_clear Wi.
assert (HH:interp_seq Denv Sigma Pi vars Fv (hyps \ A \ B) 
                   (F_push _ _ (F_push _ _ Fh)) goal).
apply IHWFP;split;auto.
constructor 2;auto.
constructor 2;trivial.
generalize (Project  _ _ _ _ Fv _ _ _ _ H H0) HH.
unfold interp_seq;simpl.
apply Compose2;intros Venv Inst.
intros [ha hb] hab;auto.

(* and destruct *)

assert (Wi:=WF_form_hyp _ _ _ _ _ _ _ _ H H0).
inversion_clear Wi;inversion_clear H2;auto.
assert (HH:interp_seq Denv Sigma Pi vars Fv (hyps \ (A =>> B =>> C)) 
                   (F_push _ _ Fh) goal).
apply IHWFP;split;trivial.
constructor 2;trivial.
constructor;trivial.
constructor;trivial.
generalize (Project  _ _ _ _ Fv  _ _ _ _ H H0) HH.
unfold interp_seq;simpl.
apply Compose2;intros Venv Inst.
auto.

(* or intro 1 *)

inversion_clear H0.
assert (HH:interp_seq Denv Sigma Pi vars Fv hyps Fh A).
apply IHWFP;split;trivial.
generalize HH;unfold interp_seq;simpl;apply Compose1.
intros Venv Inst h1;left;trivial.

(* or intro 2 *)

inversion_clear H0.
assert (HH:interp_seq Denv Sigma Pi vars Fv hyps Fh B).
apply IHWFP;split;trivial.
generalize HH;unfold interp_seq;simpl;apply Compose1.
intros Venv Inst h2;right;trivial.

(* or elim *)

assert (Wi:=WF_form_hyp _ _ _ _ _ _ _ _ H H0).
inversion_clear Wi.
assert (HH1:interp_seq Denv Sigma Pi vars Fv (hyps \ A) 
                   (F_push _ _ Fh) goal).
apply IHWFP1;split;trivial.
constructor 2;trivial.
assert (HH2:interp_seq Denv Sigma Pi vars Fv (hyps \ B) 
                   (F_push _ _ Fh) goal).
apply IHWFP2;split;trivial.
constructor 2;trivial.
generalize (Project  _ _ _ _ Fv _ _ _ _ H H0) HH1 HH2.
unfold interp_seq;simpl.
apply Compose3;intros Venv Inst.
intros [ha | hb] hab;auto.

(* or destruct *)

assert (Wi:=WF_form_hyp _ _ _ _ _ _ _ _ H H0).
inversion_clear Wi.
inversion_clear H2.
assert (HH:interp_seq Denv Sigma Pi vars Fv
                 (hyps \ (A =>> C) \ (B =>> C)) 
                 (F_push _ _ (F_push _ _ Fh)) goal).
apply IHWFP;split;trivial.
constructor 2;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
generalize (Project  _ _ _ _ Fv _ _ _ _ H H0) HH.
unfold interp_seq;simpl.
apply Compose2;intros Venv Inst.
auto.

(* forall intro *)

assert (HH:interp_seq Denv Sigma Pi (vars\dom) (F_push _ _ Fv) hyps Fh
          (inst_form (mkVar (index vars)) 0 goal)).
apply IHWFP;split;trivial.
apply Weak_WF_ctx;auto.
apply WF_Forall_instx;trivial.
unfold interp_seq;simpl interp_form.
cut 
(interp_vars Denv vars Fv
  (interp_hyps Denv Sigma Pi hyps Fh
  (fun Venv => 
  forall var : interp_domain Denv dom,
     (fun V =>
            interp_form Denv Sigma Pi V nil 
            (inst_form (mkVar (index vars)) 0 goal)) (Venv\[var; dom])))).
apply Compose1.
intros Venv Inst h x;assert (h2:= h x);clear h.
inversion H0.
apply (proj1 (form_instx _ _ _ _ _ _ Inst dom x goal nil H3));auto.
change 
(interp_vars Denv vars Fv
  (interp_hyps Denv Sigma Pi hyps Fh
     (fun Venv : var_env Denv =>
      forall var : interp_domain Denv dom,
      (fun V=> 
      interp_form Denv Sigma Pi V nil
        (inst_form (mkVar (index vars)) 0 goal)) (Venv \ [var; dom]) ))).
apply Global_bind;auto.

(* forall elim *)

assert (HH:interp_seq Denv Sigma Pi vars Fv (hyps \ (inst_form t 0 F)) 
                (F_push _ _ Fh) goal).
apply IHWFP.
split;trivial.
constructor 2;trivial.
assert (HW:=WF_form_hyp _ _ _ _ _ _ _ _ H H1).
replace O with (@length domain nil);trivial.
apply WF_form_inst with dom;trivial.
inversion HW;trivial.
generalize (Project _ _ _ _ Fv _ _ _ _ H H1) HH.
unfold interp_seq;simpl;apply Compose2.
intros Venv Inst h h1.
apply h1.
replace O with (@length (obj_entry Denv) nil);trivial.
elim (interp_WF_ground_term_Some _ _ _ _ _ Inst _ _ H0).
intros x ex;
elim (form_inst Denv Sigma Pi vars Fv Venv t dom x Inst H0 ex F nil);simpl.
intros hh _;apply hh;simpl;apply h.
assert (WW:=WF_form_hyp _ _ _ _ _ _ _ _ H H1).
inversion WW;trivial.

(* forall destruct. *)

assert (WW:WF_form Denv Sigma Pi vars nil ((!!dom, F) =>> C)).
apply WF_form_hyp with hyps Fh i;trivial.
assert (HH1:interp_seq Denv Sigma Pi vars Fv hyps Fh (!!dom, F)).
apply IHWFP1;split;trivial.
inversion WW;trivial.
assert (HH2:interp_seq Denv Sigma Pi vars Fv (hyps \ C ) 
           (F_push _ _ Fh) goal).
apply IHWFP2;split;trivial.
constructor 2;trivial.
inversion WW;trivial.
generalize (Project _ _ _ _ Fv _ _ _ _ H H0) HH1 HH2;
unfold interp_seq;simpl;apply Compose3.
intros Venv Inst h h1 h2;auto.

(* exists intro *)

inversion H1;subst.
assert (HH:interp_seq Denv Sigma Pi vars Fv hyps Fh (inst_form t 0 F)).
apply IHWFP;split;trivial.
replace O with (@length domain nil);trivial.
apply WF_form_inst with dom;trivial.
generalize HH.
unfold interp_seq;simpl interp_form;apply Compose1.
intros Venv Inst HHH.
elim (interp_WF_ground_term_Some _ _ _ _ _ Inst _ _ H).
intros x ex;split with x.
elim (form_inst Denv Sigma Pi vars Fv Venv t dom x Inst H ex F nil);auto.

(* exists elim *)

assert (Hi :=WF_form_hyp _ _ _ _ _ _ _ _ H H0).
assert (HH:interp_seq Denv Sigma Pi (vars \ dom) (F_push _ _ Fv)
          (hyps \ inst_form (mkVar (index vars)) 0 F) (F_push _ _ Fh) goal).
apply IHWFP.
constructor;trivial.
constructor;trivial.
apply WF_Exists_instx;trivial.
apply Weak_WF_ctx;trivial.
apply Weak_WF_form;trivial.

generalize (Project _ _ _ _ Fv _ _ _ _ H H0).
unfold interp_seq;simpl interp_hyps;simpl interp_form.
cut (interp_vars Denv vars Fv
(interp_hyps Denv Sigma Pi hyps Fh 
(fun Venv : var_env Denv =>
forall var : interp_domain Denv dom,
(fun V=>
interp_form Denv Sigma Pi V nil (inst_form (mkVar (index vars)) 0 F) ->
interp_form Denv Sigma Pi V nil goal)(Venv \ [var; dom])) )).
apply Compose2.
intros Venv Inst h [x h1];auto.
assert (h2 := h x);clear h.
elim (Weak_interp_form Denv Sigma Pi vars Fv Venv [x;dom] goal nil);trivial.
intros _ h;apply h;clear h;apply h2.
elim (form_instx Denv Sigma Pi vars Fv Venv Inst dom x F nil );simpl;auto.
inversion Hi;trivial.
unfold interp_seq in HH;simpl in HH.
change 
(interp_vars Denv vars Fv
  (interp_hyps Denv Sigma Pi hyps Fh
     (fun Venv : var_env Denv =>
      forall var : interp_domain Denv dom,
      (fun V => 
      interp_form Denv Sigma Pi V nil
        (inst_form (mkVar (index vars)) 0 F) ->
      interp_form Denv Sigma Pi V nil goal) (Venv \ [var; dom])))).
apply Global_bind;auto.

(* exists destruct *)

assert (Hi :=WF_form_hyp _ _ _ _ _ _ _ _ H H0).
assert (HH:interp_seq Denv Sigma Pi vars Fv
           (hyps \ (!!dom, F =>> C))
           (F_push (!!dom, F =>> C) hyps Fh) goal).
apply IHWFP;split;trivial.
constructor;trivial.
inversion_clear Hi;inversion_clear H2;constructor;trivial.
constructor;trivial.
change 
(WF_form Denv Sigma Pi vars (nil ++ dom :: nil) C).
apply Bind_WF_form;trivial.
generalize HH (Project _ _ _ _ Fv _ _ _ _ H H0).
unfold interp_seq;simpl interp_hyps;simpl interp_form;apply Compose2.
intros Venv Inst h1 h2;apply h1.
intros rel h.
inversion Hi.
apply (proj1 (Bind_interp_form Denv Sigma Pi _ _ _ ([rel; dom] :: nil) C nil Inst H6));simpl.
apply h2;split with rel;apply h.

(* Cut *)

assert (W1: WF_seq Denv Sigma Pi vars hyps Fh A).
split;auto.
assert (W2: WF_seq Denv Sigma Pi vars (hyps \ A) 
                  (F_push _ _ Fh) goal).
split.
constructor 2;assumption.
assumption.
generalize (IHWFP1 Fv Fh W1) (IHWFP2 Fv (F_push _ _ Fh) W2). 
unfold interp_seq;simpl;apply Compose2;auto.

(* Dynamic *)
unfold interp_seq;simpl;apply IHWFP;assumption.

(*
(* Meta *)
assert (Ev:=equiv_Equiv _ _ (@eq domain) pos_eq_refl _ _ Fv H0).
assert (Eh:=equiv_Equiv _ _ (form_Eq Denv Sigma Pi) (form_eq_refl Denv Sigma Pi)  _ _ Fh H1).
generalize (proj2 (interp_seq_interp Denv Sigma Pi goal' _ _ _ Ev _ _ _ Eh) H);auto.
unfold interp_seq;apply Compose1.
intros Venv Inst;
apply (proj1 (form_eq_refl Denv Sigma Pi _ _ H2 Venv nil)).
*)
Qed.

Theorem Wrapper :forall prf lvars lhyps goal,
let  (vars,Fv) := mkenv _ lvars in
let  (hyps,Fh) := mkenv _ lhyps in
check_proof vars hyps goal prf && 
check_seq Denv Sigma Pi vars hyps Fh goal = true -> 
interp_seq Denv Sigma Pi vars Fv hyps Fh goal.
intros prf lvars lhyps goal;case (mkenv _ lvars);case (mkenv _ lhyps).
intros hyps Fh vars Fv.
caseq (check_proof vars hyps goal prf);clean.
intros CP CS;apply Fundamental with prf.
apply WF_checked_proof;trivial.
apply WF_checked_seq;trivial.
Qed.

Definition Reflect := Wrapper.
(*
Definition check prf lvars lhyps goal :=
let  (vars,Fv) := mkenv domain lvars in
let  (hyps,Fh) := mkenv form lhyps in
  if check_seq Denv Sigma Pi vars hyps Fh goal then
     check_proof vars hyps goal prf
  else false.

Theorem Reflect: forall prf vars hyps goal,
if check prf vars hyps goal then
interp Denv Sigma Pi vars hyps goal
else True.
intros prf lvars lhyps goal; 
unfold check;
caseq (mkenv _ lvars);intros vars Fv;
caseq (mkenv _ lhyps);intros hyps Fh;
caseq (check_seq Denv Sigma Pi vars hyps Fh goal);auto.
caseq (check_proof vars hyps goal prf);auto.
intros eproof eseq eWFh eWFv.
assert (Ev:=mkenv_Equiv _ pos_eq (@eq domain) pos_eq_refl refl_pos_eq lvars).
assert (Eh:=mkenv_Equiv _ (form_eq) (form_Eq Denv Sigma Pi)
  (form_eq_refl Denv Sigma Pi) refl_form_eq lhyps).
unfold domain in eWFv.
rewrite eWFv in Ev.
rewrite eWFh in Eh.
assert (h:=proj1 (interp_seq_interp Denv Sigma Pi goal vars Fv lvars Ev hyps Fh lhyps Eh)).
apply h.
assert (hh:=Wrapper prf lvars lhyps goal).
unfold domain in hh.
rewrite eWFv in hh.
rewrite eWFh in hh.
auto.
Qed.
*)
End With_env.
(*
Implicit Arguments Ax [Denv Sigma Pi].
Implicit Arguments I_Equal [Denv Sigma Pi].
Implicit Arguments E_Equal_in_concl [Denv Sigma Pi].
Implicit Arguments E_Equal_in_hyp [Denv Sigma Pi].
Implicit Arguments D_Equal [Denv Sigma Pi].
Implicit Arguments E_Absurd [Denv Sigma Pi].
Implicit Arguments I_Arrow [Denv Sigma Pi].
Implicit Arguments E_Arrow [Denv Sigma Pi].
Implicit Arguments D_Arrow [Denv Sigma Pi].
Implicit Arguments I_And [Denv Sigma Pi].
Implicit Arguments E_And [Denv Sigma Pi].
Implicit Arguments D_And [Denv Sigma Pi].
Implicit Arguments I_Or1 [Denv Sigma Pi].
Implicit Arguments I_Or2 [Denv Sigma Pi].
Implicit Arguments E_Or [Denv Sigma Pi].
Implicit Arguments D_Or [Denv Sigma Pi].
Implicit Arguments I_Forall [Denv Sigma Pi].
Implicit Arguments E_Forall [Denv Sigma Pi].
Implicit Arguments D_Forall [Denv Sigma Pi].
Implicit Arguments I_Exists [Denv Sigma Pi].
Implicit Arguments E_Exists [Denv Sigma Pi].
Implicit Arguments D_Exists [Denv Sigma Pi].
Implicit Arguments Cut [Denv Sigma Pi].
Implicit Arguments Meta [Denv Sigma Pi].

Definition Proof Denv Sigma Pi (p:proof Denv Sigma Pi) := p. *)

















