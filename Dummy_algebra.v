Require Import Bintree.
Require Import Env.

Section with_env.

Definition signature (Denv:domain_env):= True.

Definition term:=unit.
Definition args:=unit.
Definition occ_term:=unit.
Definition occ_args:=unit.

Definition mkVar (p: positive) :term := tt.

Definition term_eq (t1 t2:term) := true.
Definition args_eq (a1 a2:args) :=true.

Lemma refl_term_eq : forall t:term,term_eq t t=true.
auto.
Qed.

Lemma refl_args_eq : forall a:args,args_eq a a=true.
auto.
Qed.

Definition inst_term : term -> nat -> term -> term := fun _ _ t => t.
Definition inst_args : term -> nat -> args -> args := fun _ _ a => a.

Definition rewrite_term : term -> term -> occ_term -> term -> option term := fun _ _ _ _ => Some tt.
Definition rewrite_args : term -> term -> occ_args -> args -> option args := fun _ _ _ _ => Some tt.

Definition check_ground_term : 
   forall Denv, signature Denv -> var_ctx -> term -> domain -> bool:=fun _ _ _ _ _ => false.
Definition WF_ground_term : 
   forall Denv, signature Denv -> var_ctx -> term -> domain -> Prop:=fun _ _ _ _ _ => False.
Lemma WF_checked_ground_term :
  forall Denv Sigma vars t dom, 
  check_ground_term Denv Sigma vars t dom = true ->
  WF_ground_term Denv Sigma vars t dom.
compute;congruence.
Qed.

Definition check_term : forall Denv,
  signature Denv -> var_ctx -> rel_ctx -> term -> domain -> bool:= fun _ _ _ _ _ _ => false.
Definition check_args : forall Denv,
  signature Denv -> var_ctx -> rel_ctx -> args -> arity -> bool:= fun _ _ _ _ _ l =>
match l with nil => true | _ => false end.

Definition WF_term : forall Denv,
  signature Denv -> var_ctx -> rel_ctx -> term -> domain -> Prop:=fun _ _ _ _ _ _ => False.
Definition WF_args : forall Denv,
  signature Denv -> var_ctx -> rel_ctx -> args -> arity -> Prop:=fun _ _ _ _ _ l => 
match l with nil => True | _ => False end.

Lemma WF_checked_term :
  forall Denv Sigma vars rels t dom, 
  check_term Denv Sigma vars rels t dom = true ->
  WF_term Denv Sigma vars rels t dom.
compute;congruence.
Qed.

Lemma WF_checked_args :
  forall Denv Sigma vars rels args doms, 
  check_args Denv Sigma vars rels args doms = true ->
  WF_args Denv Sigma vars rels args doms.
compute; intros _ _ _ _ _ [| _ _ ] h;trivial||congruence.
Qed.

Lemma WF_ground_term_term : 
  forall Denv Sigma vars rels t dom,
  WF_ground_term Denv Sigma vars t dom ->
  WF_term Denv Sigma vars rels t dom.
compute;trivial.
Qed.

Lemma WF_term_nil_ground_term :
  forall Denv Sigma vars t dom,
  WF_term Denv Sigma vars nil t dom ->
  WF_ground_term Denv Sigma vars t dom.
compute;trivial.
Qed.

Definition interp_term: forall Denv,
  signature Denv -> var_env Denv -> rel_env Denv -> term -> 
  forall (expected:domain), option (interp_domain Denv expected):=fun _ _ _ _ _ _ => None.
Definition interp_args: forall Denv,
  signature Denv -> var_env Denv -> rel_env Denv -> args -> 
  forall (doms:arity) (S:Type), abstract Denv doms S -> Poption S:=fun Denv _ _ _ _ doms S => 
match doms return  abstract Denv doms S -> Poption S with
nil => fun s => PSome s 
| _ => fun _ => PNone
end.

Lemma interp_WF_ground_term_Some : 
  forall Denv Sigma V F Venv,
  Instanceof Denv V F Venv->
  forall t dom, 
  WF_ground_term Denv Sigma V t dom ->
  (exists x, interp_term Denv Sigma Venv nil t dom = Some x).
compute;intros  Denv Sigma V F Venv Inst t dom W;elim W.
Qed.

Lemma term_eq_refl: forall Denv Sigma vars rels dom t1 t2,
  term_eq t1 t2 = true -> 
  interp_term Denv Sigma vars rels t1 dom =  
  interp_term Denv Sigma vars rels t2 dom.
compute;reflexivity.
Qed.

Lemma args_eq_refl: forall Denv Sigma vars rels doms T hd a1 a2,
  args_eq a1 a2 = true -> 
  interp_args Denv Sigma vars rels a1 doms T hd =  
  interp_args Denv Sigma vars rels a2 doms T hd.
compute;reflexivity.
Qed.

Lemma WF_term_instx : forall Denv Sigma V (F:Full V) rels dom t expected,
WF_term Denv Sigma V (rels ++ dom :: nil) t expected ->
WF_term Denv Sigma (V \ dom) rels
  (inst_term (mkVar (index V)) (length rels) t) expected.
compute;trivial.
Qed.

Lemma WF_args_instx : forall Denv Sigma V (F:Full V) rels dom a doms,
WF_args Denv Sigma V (rels ++ dom :: nil) a doms ->
WF_args Denv Sigma (V \ dom) rels
  (inst_args (mkVar (index V)) (length rels) a) doms.
compute;trivial.
Qed.

Lemma term_instx : forall Denv Sigma V F Venv, Instanceof Denv V F Venv ->
forall dom rel rels t expected, WF_term Denv Sigma V 
(List.map (E_domain Denv) (rels ++ (mkE Denv dom rel) :: nil)) t expected ->
interp_term Denv Sigma (Venv\mkE Denv dom rel) rels
    (inst_term (mkVar (index V)) (length rels) t) expected =
interp_term Denv Sigma Venv (rels ++ (mkE Denv dom rel) :: nil) t expected.
compute;trivial.
Qed.

Lemma args_instx : forall Denv Sigma V F Venv, Instanceof Denv V F Venv ->
forall dom rel rels a doms (T:Type) head, WF_args Denv Sigma V 
(List.map (E_domain Denv) (rels ++ (mkE Denv dom rel) :: nil)) a doms ->
interp_args Denv Sigma (Venv\mkE Denv dom rel) rels
     (inst_args (mkVar (index V)) (length rels) a) doms T head =
interp_args Denv Sigma Venv (rels ++ (mkE Denv dom rel) :: nil) a doms T
     head.
compute;trivial.
Qed.

Lemma WF_term_inst : forall Denv Sigma V t dom,
WF_ground_term Denv Sigma V t dom ->
forall rels tt dd,
WF_term Denv Sigma V (rels ++ dom :: nil) tt dd ->
WF_term Denv Sigma V rels (inst_term t (length rels) tt) dd.
compute;trivial.
Qed.

Lemma WF_args_inst : forall Denv Sigma V t dom,
WF_ground_term Denv Sigma V t dom ->
forall rels a doms,
WF_args Denv Sigma V (rels ++ dom :: nil) a doms ->
WF_args Denv Sigma V rels (inst_args t (length rels) a) doms.
compute;trivial.
Qed.

Lemma term_inst : forall Denv Sigma V F Venv t dom x, 
Instanceof Denv V F Venv -> 
WF_ground_term Denv Sigma V t dom ->
interp_term Denv Sigma Venv nil t dom = Some x ->
forall rels tt dd, 
WF_term Denv Sigma V 
(List.map (E_domain Denv) (rels ++ (mkE Denv dom x) :: nil)) tt dd -> 
interp_term Denv Sigma Venv (rels ++ (mkE Denv dom x) :: nil) tt dd =
interp_term Denv Sigma Venv rels (inst_term t (length rels) tt) dd.
compute;trivial.
Qed.

Lemma args_inst : forall Denv Sigma V F Venv t dom x,
Instanceof Denv V F Venv -> 
WF_ground_term Denv Sigma V t dom ->
interp_term Denv Sigma Venv nil t dom = Some x ->
forall rels a doms T P, 
WF_args Denv Sigma V 
(List.map (E_domain Denv) (rels ++ (mkE Denv dom x) :: nil)) a doms -> 
interp_args Denv Sigma Venv (rels ++ (mkE Denv dom x) :: nil) a doms T P =
interp_args Denv Sigma Venv rels (inst_args t (length rels) a) doms T P.
compute;trivial.
Qed.

Lemma Weak_WF_term : forall Denv Sigma vars dom rels t expected,
Full vars ->
WF_term Denv Sigma vars rels t expected ->
WF_term Denv Sigma (vars\dom) rels t expected.
compute;trivial.
Qed.

Lemma Weak_WF_args : forall Denv Sigma vars dom rels a doms,
Full vars ->
WF_args Denv Sigma vars rels a doms ->
WF_args Denv Sigma (vars\dom) rels a doms.
compute;trivial.
Qed.

Lemma Weak_interp_term: forall Denv Sigma V F Venv var t rels expected,
Instanceof Denv V F Venv ->
WF_term Denv Sigma V (List.map (E_domain Denv) rels) t expected ->
interp_term Denv Sigma Venv rels t expected=
interp_term Denv Sigma (Venv\var)  rels t expected.
compute;trivial.
Qed.

Lemma Weak_interp_args: forall Denv Sigma V F Venv var S rels a doms Kont,
Instanceof Denv V F Venv ->
WF_args Denv Sigma V (List.map (E_domain Denv) rels) a doms ->
interp_args Denv Sigma Venv rels a doms S Kont=
interp_args Denv Sigma (Venv\var) rels a doms S Kont.
compute;trivial.
Qed.

Lemma Bind_WF_term: forall Denv Sigma vars delta rels t expected,
WF_term Denv Sigma vars rels t expected ->
WF_term Denv Sigma vars (rels ++ delta) t expected.
compute;trivial.
Qed.

Lemma Bind_WF_args : forall Denv Sigma vars delta rels a doms,
WF_args Denv Sigma vars rels a doms ->
WF_args Denv Sigma vars (rels ++ delta) a doms.
compute;trivial.
Qed.

Lemma Bind_interp_term: forall Denv Sigma V F Venv delta rels t expected,
Instanceof Denv V F Venv ->
WF_term Denv Sigma V (List.map (E_domain Denv) rels) t expected ->
interp_term Denv Sigma Venv rels t expected =
interp_term Denv Sigma Venv (rels++delta) t expected.
compute;trivial.
Qed.

Lemma Bind_interp_args: forall Denv Sigma V F Venv delta S rels a doms Kont,
Instanceof Denv V F Venv ->
WF_args Denv Sigma V (List.map (E_domain Denv) rels) a doms ->
interp_args Denv Sigma Venv rels a doms S Kont=
interp_args Denv Sigma Venv (rels++delta) a doms S Kont.
compute;trivial.
Qed.

Lemma WF_rewrite_term : forall Denv Sigma vars dom t1 t2 rels,
WF_ground_term Denv Sigma vars t1 dom ->
WF_ground_term Denv Sigma vars t2 dom ->
forall t occ rt expected,
rewrite_term t1 t2 occ t = Some rt ->
WF_term Denv Sigma vars rels t expected ->
WF_term Denv Sigma vars rels rt expected.
compute;trivial.
Qed.

Lemma WF_rewrite_args : forall Denv Sigma vars dom t1 t2 rels,
WF_ground_term Denv Sigma vars t1 dom ->
WF_ground_term Denv Sigma vars t2 dom ->
forall a occ ra doms,
rewrite_args t1 t2 occ a = Some ra ->
WF_args Denv Sigma vars rels a doms ->
WF_args Denv Sigma vars rels ra doms.
compute;trivial.
Qed.

Lemma term_rewrite : forall Denv Sigma V F Venv,
Instanceof Denv V F Venv->
forall dom t1 t2 it1 it2,  
WF_ground_term Denv Sigma V t1 dom ->
WF_ground_term Denv Sigma V t2 dom ->
interp_term Denv Sigma Venv nil t1 dom = Some it1 ->
interp_term Denv Sigma Venv nil t2 dom = Some it2 ->
it1 = it2 ->
forall rels t occ rt expected,
rewrite_term t1 t2 occ t = Some rt ->
WF_term Denv Sigma V (List.map (E_domain Denv) rels) t expected ->
interp_term Denv Sigma Venv rels t expected =
interp_term Denv Sigma Venv rels rt expected.
compute;trivial.
Qed.

Lemma args_rewrite :
forall Denv Sigma V F Venv,
Instanceof Denv V F Venv->
forall dom t1 t2 it1 it2,  
WF_ground_term Denv Sigma V t1 dom ->
WF_ground_term Denv Sigma V t2 dom ->
interp_term Denv Sigma Venv nil t1 dom = Some it1 ->
interp_term Denv Sigma Venv nil t2 dom = Some it2 ->
it1 = it2 ->
forall rels a occ ra doms T K,
rewrite_args t1 t2 occ a = Some ra ->
WF_args Denv Sigma V (List.map (E_domain Denv) rels) a doms ->
interp_args Denv Sigma Venv rels a doms T K =
interp_args Denv Sigma Venv rels ra doms T K.
compute;trivial.
Qed.

End with_env.
