Require Export Bintree.
Require Export Env.
Require Export Free_algebra.
Require Export Form.
Require Export Sequent.
Require Export Proof.



Bind Scope term_scope with term.
Bind Scope args_scope with args.
Bind Scope form_scope with form.

Notation "A =>> B":= (Arrow A B) (at level 58, right associativity) : form_scope.
Infix "//\\" := And (at level 56, right associativity).
Infix "\\//" := Or (at level 57, right associativity).
Notation " !! d , F" := (Forall d F) (at level 59, right associativity) : form_scope.
Notation " ?? d , F" := (Exists d F) (at level 59, right associativity) : form_scope.
Notation "#" := Absurd.

Notation " [ arg0 ; .. ; argn ]" := (More_args arg0 .. (More_args argn No_args) ..)   
: args_scope.
Notation "# i" := (DB i) (at level 35) : term_scope.
Notation "! n" := (Var n) (at level 35): term_scope.
Notation "& f" := (App f No_args) (at level 35): term_scope.

Open Scope args_scope.
Open Scope term_scope.
Open Scope form_scope.
