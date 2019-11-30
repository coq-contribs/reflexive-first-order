Require Import Bintree.
Require Import Env.

Module Type Algebra.

Local Parameter signature: domain_env -> Type.

Local Parameters term args occ_term occ_args : Set.

Local Parameter mkVar : positive -> term.

Local Parameter term_eq : term -> term -> bool.
Local Parameter args_eq : args -> args -> bool.

Local Parameter refl_term_eq : forall t:term,term_eq t t=true.
Local Parameter refl_args_eq : forall a:args,args_eq a a=true.

Local Parameter inst_term : term -> nat -> term -> term.
Local Parameter inst_args : term -> nat -> args -> args.

Local Parameter rewrite_term : term -> term -> occ_term -> term -> option term.
Local Parameter rewrite_args : term -> term -> occ_args -> args -> option args.

Local Parameter check_ground_term : 
   forall Denv, signature Denv -> var_ctx -> term -> domain -> bool.
Local Parameter WF_ground_term : 
   forall Denv, signature Denv -> var_ctx -> term -> domain -> Prop.
Local Parameter WF_checked_ground_term :
  forall Denv Sigma vars t dom, 
  check_ground_term Denv Sigma vars t dom = true ->
  WF_ground_term Denv Sigma vars t dom.

Local Parameter check_term : forall Denv,
  signature Denv -> var_ctx -> rel_ctx -> term -> domain -> bool.
Local Parameter check_args : forall Denv,
  signature Denv -> var_ctx -> rel_ctx -> args -> arity -> bool.

Local Parameter WF_term : forall Denv,
  signature Denv -> var_ctx -> rel_ctx -> term -> domain -> Prop.
Local Parameter WF_args : forall Denv,
  signature Denv -> var_ctx -> rel_ctx -> args -> arity -> Prop.

Local Parameter WF_checked_term :
  forall Denv Sigma vars rels t dom, 
  check_term Denv Sigma vars rels t dom = true ->
  WF_term Denv Sigma vars rels t dom.
Local Parameter WF_checked_args :
  forall Denv Sigma vars rels args doms, 
  check_args Denv Sigma vars rels args doms = true ->
  WF_args Denv Sigma vars rels args doms.

Local Parameter WF_ground_term_term : 
  forall Denv Sigma vars rels t dom,
  WF_ground_term Denv Sigma vars t dom ->
  WF_term Denv Sigma vars rels t dom.

Local Parameter WF_term_nil_ground_term :
  forall Denv Sigma vars t dom,
  WF_term Denv Sigma vars nil t dom ->
  WF_ground_term Denv Sigma vars t dom.

Local Parameter interp_term: forall Denv,
  signature Denv -> var_env Denv -> rel_env Denv -> term -> 
  forall (expected:domain), option (interp_domain Denv expected).
Local Parameter interp_args: forall Denv,
  signature Denv -> var_env Denv -> rel_env Denv -> args -> 
  forall (doms:arity) (S:Type), abstract Denv doms S -> Poption S.

Local Parameter interp_WF_ground_term_Some : 
  forall Denv Sigma V F Venv,
  Instanceof Denv V F Venv->
  forall t dom, 
  WF_ground_term Denv Sigma V t dom ->
  (exists x, interp_term Denv Sigma Venv nil t dom = Some x).

Local Parameter term_eq_refl: forall Denv Sigma vars rels dom t1 t2,
  term_eq t1 t2 = true -> 
  interp_term Denv Sigma vars rels t1 dom =  
  interp_term Denv Sigma vars rels t2 dom.
Local Parameter args_eq_refl: forall Denv Sigma vars rels doms T hd a1 a2,
  args_eq a1 a2 = true -> 
  interp_args Denv Sigma vars rels a1 doms T hd =  
  interp_args Denv Sigma vars rels a2 doms T hd.

Local Parameter WF_term_instx : forall Denv Sigma V (F:Full V) rels dom t expected,
WF_term Denv Sigma V (rels ++ dom :: nil) t expected ->
WF_term Denv Sigma (V \ dom) rels
  (inst_term (mkVar (index V)) (length rels) t) expected.
Local Parameter WF_args_instx : forall Denv Sigma V (F:Full V) rels dom a doms,
WF_args Denv Sigma V (rels ++ dom :: nil) a doms ->
WF_args Denv Sigma (V \ dom) rels
  (inst_args (mkVar (index V)) (length rels) a) doms.

Local Parameter term_instx : forall Denv Sigma V F Venv, Instanceof Denv V F Venv ->
forall dom rel rels t expected, WF_term Denv Sigma V 
(List.map (E_domain Denv) (rels ++ (mkE Denv dom rel) :: nil)) t expected ->
interp_term Denv Sigma (Venv\mkE Denv dom rel) rels
    (inst_term (mkVar (index V)) (length rels) t) expected =
interp_term Denv Sigma Venv (rels ++ (mkE Denv dom rel) :: nil) t expected.

Local Parameter args_instx : forall Denv Sigma V F Venv, Instanceof Denv V F Venv ->
forall dom rel rels a doms (T:Type) head, WF_args Denv Sigma V 
(List.map (E_domain Denv) (rels ++ (mkE Denv dom rel) :: nil)) a doms ->
interp_args Denv Sigma (Venv\mkE Denv dom rel) rels
     (inst_args (mkVar (index V)) (length rels) a) doms T head =
interp_args Denv Sigma Venv (rels ++ (mkE Denv dom rel) :: nil) a doms T
     head.

Local Parameter WF_term_inst : forall Denv Sigma V t dom,
WF_ground_term Denv Sigma V t dom ->
forall rels tt dd,
WF_term Denv Sigma V (rels ++ dom :: nil) tt dd ->
WF_term Denv Sigma V rels (inst_term t (length rels) tt) dd.

Local Parameter WF_args_inst : forall Denv Sigma V t dom,
WF_ground_term Denv Sigma V t dom ->
forall rels a doms,
WF_args Denv Sigma V (rels ++ dom :: nil) a doms ->
WF_args Denv Sigma V rels (inst_args t (length rels) a) doms.

Local Parameter term_inst : forall Denv Sigma V F Venv t dom x, 
Instanceof Denv V F Venv -> 
WF_ground_term Denv Sigma V t dom ->
interp_term Denv Sigma Venv nil t dom = Some x ->
forall rels tt dd, 
WF_term Denv Sigma V 
(List.map (E_domain Denv) (rels ++ (mkE Denv dom x) :: nil)) tt dd -> 
interp_term Denv Sigma Venv (rels ++ (mkE Denv dom x) :: nil) tt dd =
interp_term Denv Sigma Venv rels (inst_term t (length rels) tt) dd.

Local Parameter args_inst : forall Denv Sigma V F Venv t dom x,
Instanceof Denv V F Venv -> 
WF_ground_term Denv Sigma V t dom ->
interp_term Denv Sigma Venv nil t dom = Some x ->
forall rels a doms T P, 
WF_args Denv Sigma V 
(List.map (E_domain Denv) (rels ++ (mkE Denv dom x) :: nil)) a doms -> 
interp_args Denv Sigma Venv (rels ++ (mkE Denv dom x) :: nil) a doms T P =
interp_args Denv Sigma Venv rels (inst_args t (length rels) a) doms T P.

Local Parameter Weak_WF_term : forall Denv Sigma vars dom rels t expected,
Full vars ->
WF_term Denv Sigma vars rels t expected ->
WF_term Denv Sigma (vars\dom) rels t expected.
Local Parameter Weak_WF_args : forall Denv Sigma vars dom rels a doms,
Full vars ->
WF_args Denv Sigma vars rels a doms ->
WF_args Denv Sigma (vars\dom) rels a doms.

Local Parameter Weak_interp_term: forall Denv Sigma V F Venv var t rels expected,
Instanceof Denv V F Venv ->
WF_term Denv Sigma V (List.map (E_domain Denv) rels) t expected ->
interp_term Denv Sigma Venv rels t expected=
interp_term Denv Sigma (Venv\var)  rels t expected.
Local Parameter Weak_interp_args: forall Denv Sigma V F Venv var S rels a doms Kont,
Instanceof Denv V F Venv ->
WF_args Denv Sigma V (List.map (E_domain Denv) rels) a doms ->
interp_args Denv Sigma Venv rels a doms S Kont=
interp_args Denv Sigma (Venv\var) rels a doms S Kont.

Local Parameter Bind_WF_term: forall Denv Sigma vars delta rels t expected,
WF_term Denv Sigma vars rels t expected ->
WF_term Denv Sigma vars (rels ++ delta) t expected.
Local Parameter Bind_WF_args : forall Denv Sigma vars delta rels a doms,
WF_args Denv Sigma vars rels a doms ->
WF_args Denv Sigma vars (rels ++ delta) a doms.

Local Parameter Bind_interp_term: forall Denv Sigma V F Venv delta rels t expected,
Instanceof Denv V F Venv ->
WF_term Denv Sigma V (List.map (E_domain Denv) rels) t expected ->
interp_term Denv Sigma Venv rels t expected =
interp_term Denv Sigma Venv (rels++delta) t expected.
Local Parameter Bind_interp_args: forall Denv Sigma V F Venv delta S rels a doms Kont,
Instanceof Denv V F Venv ->
WF_args Denv Sigma V (List.map (E_domain Denv) rels) a doms ->
interp_args Denv Sigma Venv rels a doms S Kont=
interp_args Denv Sigma Venv (rels++delta) a doms S Kont.

Local Parameter WF_rewrite_term : forall Denv Sigma vars dom t1 t2 rels,
WF_ground_term Denv Sigma vars t1 dom ->
WF_ground_term Denv Sigma vars t2 dom ->
forall t occ rt expected,
rewrite_term t1 t2 occ t = Some rt ->
WF_term Denv Sigma vars rels t expected ->
WF_term Denv Sigma vars rels rt expected.

Local Parameter WF_rewrite_args : forall Denv Sigma vars dom t1 t2 rels,
WF_ground_term Denv Sigma vars t1 dom ->
WF_ground_term Denv Sigma vars t2 dom ->
forall a occ ra doms,
rewrite_args t1 t2 occ a = Some ra ->
WF_args Denv Sigma vars rels a doms ->
WF_args Denv Sigma vars rels ra doms.

Local Parameter term_rewrite : forall Denv Sigma V F Venv,
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

Local Parameter args_rewrite :
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

End Algebra.

