Require Import Bintree.

Unset Boxed Definitions.

Definition domain_env := Store Set.
Definition domain := positive.
Definition arity := list domain.
Definition var_ctx := Store domain.
Definition  rel_ctx := list domain.

Section with_Denv.

Variable Denv:domain_env.

Definition interp_domain d := 
match get d Denv with
  PSome s => s 
| PNone => unit
end.

Record obj_entry: Set :=
mkE{E_domain:domain ;
          E_it:interp_domain E_domain}.

Fixpoint abstract (doms:arity) (hd:Type) {struct doms}:Type :=
  match doms with
     nil =>  hd
| r::q => interp_domain r -> (abstract q hd)
end.

Definition var_env:=Store obj_entry.
Definition rel_env:=list obj_entry.

Notation "[ T ; i ]" := (mkE i T).

Inductive Instanceof : forall V:var_ctx, Full V ->
forall (Venv:var_env), Type :=
  I_empty : Instanceof empty F_empty empty
| I_var : 
  forall hyps F Venv dom var, Instanceof hyps F Venv-> 
  Instanceof (hyps \ dom) (F_push dom hyps F)  (Venv\ [ var ; dom ]).

Lemma Instanceof_Full: forall hyps Fh Venv,
	Instanceof hyps Fh Venv -> Full Venv.
intros hyps Fh Venv Inst; induction Inst;[left|right;assumption].
Qed.

Lemma index_Instanceof: forall hyps F Venv,
Instanceof hyps F Venv -> index hyps = index Venv.
intros hyps F Venv Inst.
induction Inst;clean.
Qed.

Lemma get_Instanceof : forall n hyps F Venv, 
Instanceof hyps F Venv -> forall dom,
get n hyps = PSome dom ->
(exists var, get n Venv = PSome [var;dom])  .
intros n hyps F Venv Inst.
induction Inst;intro dom0.
unfold get;case n;simpl;congruence.
repeat rewrite get_push_Full;trivial.
rewrite (index_Instanceof hyps F Venv);trivial.
caseq (Pcompare n (index Venv) Eq).
intros en edom;
replace dom0 with dom;(try exists var);congruence.
auto.
congruence.
apply (Instanceof_Full _ _ _ Inst).
Qed.

End with_Denv.
