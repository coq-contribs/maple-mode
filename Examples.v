(* Examples.v *)

Require Maple.
Require Reals.

(**** Tactic Simplify ****)

Lemma simp0:(x:R)``x<>0``->``x/x==1``.
Proof.
  Intros.
  Simplify ``x/x``.
  Reflexivity.
  Assumption.
Save.

Lemma simp1:(x,y:R)``(1+x)<>0``->``((1+x)/(1+x))*(1+y)-(1+y)>=0``.
Proof.
  Intros.
  Simplify ``(1+x)/(1+x)``.
  Ring ``1*(1+y)-(1+y)``.
  Unfold Rge;Right;Reflexivity.
  Assumption.
Save.

Lemma simp2:(x,y:R)``x<>0``->``y<>0``->``(x/y+y/x)*x*y-(x*x+y*y)+1>0``.
Proof.
  Intros.
  Simplify ``(x/y+y/x)*x*y-(x*x+y*y)+1``.
  Sup0.
  SplitRmult;Assumption.
Save.

Lemma simp3:(x,y:R)``(x+y)<>0``->``x/(x+y)+y/(x+y)==1``.
Proof.
  Intros.
  Simplify ``x/(x+y)+y/(x+y)``.
  Reflexivity.
  Assumption.
Save.

(**** Tactic Factor ****)

Lemma fact0:(a,b:R)``a*a+2*a*b+b*b==(a+b)*(a+b)``.
Proof.
  Intros.
  Factor ``a*a+2*a*b+b*b``.
  Reflexivity.
Save.

Lemma fact1:(a,b:R)``a*a-2*a*b+b*b==(a-b)*(a-b)``.
Proof.
  Intros.
  Factor ``a*a-2*a*b+b*b``.
  Reflexivity.
Save.

Lemma fact2:(a,b:R)``a*a-b*b==(a-b)*(a+b)``.
Proof.
  Intros.
  Factor ``a*a-b*b``.
  Reflexivity.
Save.

Lemma fact3:(a,b:R)``a*a*a+3*a*a*b+3*a*b*b+b*b*b==(a+b)*(a+b)*(a+b)``.
Proof.
  Intros.
  Factor ``a*a*a+3*a*a*b+3*a*b*b+b*b*b``.
  Reflexivity.
Save.

(**** Tactic Expand ****)

Lemma expd0:(a,b:R)``(a+b)*(a+b)==a*a+2*a*b+b*b``.
Proof.
  Intros.
  Expand ``(a+b)*(a+b)``.
  Reflexivity.
Save.

Lemma expd1:(a,b:R)``(a-b)*(a-b)==a*a-2*a*b+b*b``.
Proof.
  Intros.
  Expand ``(a-b)*(a-b)``.
  Reflexivity.
Save.

Lemma expd2:(a,b:R)``(a-b)*(a+b)==a*a-b*b``.
Proof.
  Intros.
  Expand ``(a-b)*(a+b)``.
  Reflexivity.
Save.

Lemma expd3:(a,b:R)``(a+b)*(a+b)*(a+b)==a*a*a+3*a*a*b+3*a*b*b+b*b*b``.
Proof.
  Intros.
  Expand ``(a+b)*(a+b)*(a+b)``.
  Reflexivity.
Save.

(**** Tactic Normal ****)

Lemma norm0:(x,y:R)``x<>0``->``y<>0``->``x/y+y/x==(x*x+y*y)*/y*/x``.
Proof.
  Intros.
  Normal ``x/y+y/x``.
  Reflexivity.
  SplitRmult;Assumption.
Save.

Lemma norm1:(x:R)``x<>0``->``x+1<>0``->``/x+x/(x+1)==(x+1+x*x)*/x*/(x+1)``.
Proof.
  Intros.
  Normal ``/x+x/(x+1)``.
  Reflexivity.
  SplitRmult;Assumption.
Save.

Lemma norm2:(x,y:R)``x-y<>0``->
                   ``x*x/((x-y)*(x-y))-y*y/((x-y)*(x-y))==(x+y)/(x-y)``.
Proof.
  Intros x y H.
  Normal ``x*x/((x-y)*(x-y))-y*y/((x-y)*(x-y))``.
  Reflexivity.
  Unfold Rminus in H;SplitRmult;Assumption.
Save.

Lemma norm3:(x,y:R)``x-y<>0``->``x+y<>0``->``x*x-y*y<>0``->
                   ``x/(x-y)+y/(x+y)+2*y*y/(x*x-y*y)==(x+y)/(x-y)``.
Proof.
  Intros x y H H0 H1.
  Normal ``x/(x-y)+y/(x+y)+2*y*y/(x*x-y*y)``.
  Unfold Rminus;Reflexivity.
  Unfold Rminus in H H1;SplitRmult;Assumption.
Save.

(**** Eval <Maple Tactic> in ****)

Lemma eval_simp0:(x,y:R)``x*y<>0``->``x/x+y/y==2``.
Proof.
  Intros.
  Let t = Eval Simplify in ``x/x+y/y`` In
  Replace ``x/x+y/y`` with t.
  Reflexivity.
  Field;Assumption.
Save.

Lemma eval_fact0:(x,y:R)``x<>0``->``y<>0``->``x/x+x/y==(x+y)/y``.
Proof.
  Intros.
  Let t = Eval Factor in ``x/x+x/y`` In
  Replace ``x/x+x/y`` with t.
  Rewrite Rplus_sym;Reflexivity.
  Field;SplitRmult;Assumption.
Save.

Lemma eval_expd0:(x,y:R)``(3*x+3)*(y-5/3)==3*x*y+ -(5*x)+3*y+ -5``.
Proof.
  Intros.
  Let t = Eval Expand in ``(3*x+3)*(y-5/3)`` In
  Replace ``(3*x+3)*(y-5/3)`` with t.
  Reflexivity.
  Field;DiscrR.
Save.

Lemma eval_norm0:(x,y:R)``x<>0``->``y<>0``->``y/(x*y)+y/x==(1+y)/x``.
Proof.
  Intros.
  Let t = Eval Normal in ``y/(x*y)+y/x`` In
  Replace ``y/(x*y)+y/x`` with t.
  Unfold Rdiv;Reflexivity.
  Field;SplitRmult;Assumption.
Save.

Definition def0 := Eval Simplify in ``1/1``.

Definition def1 [x,y:R] := Eval Simplify in ``(x/y+y)*y``.

Definition def2 [x,y:R] := Eval Factor in ``x*y+x`` .

Definition def3 [x,y:R] := Eval Factor in ``x*y-3*x+7*y-21``.

Definition def4 [x,y:R] := Eval Expand in ``(x+y)*x``.

Definition def5 [x,y:R] := Eval Expand in ``(x-7)*(y+4)``.

Definition def6 [x,y:R] := Eval Normal in ``/x+/y``.

Definition def7 [x,y:R] := Eval Normal in ``x*x*y/(x+y)+y*x*y/(x+y)``.
