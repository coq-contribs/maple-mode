(* Examples.v *)

Require Export Maple.
Require Export Reals.

(**** Tactic Simplify ****)

Lemma simp0 : forall x : R, x <> 0%R -> (x / x)%R = 1%R.
Proof.
  intros.
  simplify (x / x)%R.
  reflexivity.
  assumption.
Qed.

Lemma simp1 :
 forall x y : R,
 (1 + x)%R <> 0%R -> ((1 + x) / (1 + x) * (1 + y) - (1 + y) >= 0)%R.
Proof.
  intros.
  simplify ((1 + x) / (1 + x))%R.
  ring (1 * (1 + y) - (1 + y))%R.
  unfold Rge in |- *; right; reflexivity.
  assumption.
Qed.

Lemma simp2 :
 forall x y : R,
 x <> 0%R ->
 y <> 0%R -> ((x / y + y / x) * x * y - (x * x + y * y) + 1 > 0)%R.
Proof.
  intros.
  simplify ((x / y + y / x) * x * y - (x * x + y * y) + 1)%R.
  prove_sup0.
  split_Rmult; assumption.
Qed.

Lemma simp3 :
 forall x y : R, (x + y)%R <> 0%R -> (x / (x + y) + y / (x + y))%R = 1%R.
Proof.
  intros.
  simplify (x / (x + y) + y / (x + y))%R.
  reflexivity.
  assumption.
Qed.

(**** Tactic Factor ****)

Lemma fact0 :
 forall a b : R, (a * a + 2 * a * b + b * b)%R = ((a + b) * (a + b))%R.
Proof.
  intros.
  factor (a * a + 2 * a * b + b * b)%R.
  reflexivity.
Qed.

Lemma fact1 :
 forall a b : R, (a * a - 2 * a * b + b * b)%R = ((a - b) * (a - b))%R.
Proof.
  intros.
  factor (a * a - 2 * a * b + b * b)%R.
  reflexivity.
Qed.

Lemma fact2 : forall a b : R, (a * a - b * b)%R = ((a - b) * (a + b))%R.
Proof.
  intros.
  factor (a * a - b * b)%R.
  reflexivity.
Qed.

Lemma fact3 :
 forall a b : R,
 (a * a * a + 3 * a * a * b + 3 * a * b * b + b * b * b)%R =
 ((a + b) * (a + b) * (a + b))%R.
Proof.
  intros.
  factor (a * a * a + 3 * a * a * b + 3 * a * b * b + b * b * b)%R.
  reflexivity.
Qed.

(**** Tactic Expand ****)

Lemma expd0 :
 forall a b : R, ((a + b) * (a + b))%R = (a * a + 2 * a * b + b * b)%R.
Proof.
  intros.
  expand ((a + b) * (a + b))%R.
  reflexivity.
Qed.

Lemma expd1 :
 forall a b : R, ((a - b) * (a - b))%R = (a * a - 2 * a * b + b * b)%R.
Proof.
  intros.
  expand ((a - b) * (a - b))%R.
  reflexivity.
Qed.

Lemma expd2 : forall a b : R, ((a - b) * (a + b))%R = (a * a - b * b)%R.
Proof.
  intros.
  expand ((a - b) * (a + b))%R.
  reflexivity.
Qed.

Lemma expd3 :
 forall a b : R,
 ((a + b) * (a + b) * (a + b))%R =
 (a * a * a + 3 * a * a * b + 3 * a * b * b + b * b * b)%R.
Proof.
  intros.
  expand ((a + b) * (a + b) * (a + b))%R.
  reflexivity.
Qed.

(**** Tactic Normal ****)

Lemma norm0 :
 forall x y : R,
 x <> 0%R -> y <> 0%R -> (x / y + y / x)%R = ((x * x + y * y) * / y * / x)%R.
Proof.
  intros.
  normal (x / y + y / x)%R.
  reflexivity.
  split_Rmult; assumption.
Qed.

Lemma norm1 :
 forall x : R,
 x <> 0%R ->
 (x + 1)%R <> 0%R ->
 (/ x + x / (x + 1))%R = ((x + 1 + x * x) * / x * / (x + 1))%R.
Proof.
  intros.
  normal (/ x + x / (x + 1))%R.
  reflexivity.
  split_Rmult; assumption.
Qed.

Lemma norm2 :
 forall x y : R,
 (x - y)%R <> 0%R ->
 (x * (x / ((x - y) * (x - y))) - y * (y / ((x - y) * (x - y))))%R =
 ((x + y) / (x - y))%R.
Proof.
  intros x y H.
  normal (x * (x / ((x - y) * (x - y))) - y * (y / ((x - y) * (x - y))))%R.
  reflexivity.
  unfold Rminus in H; split_Rmult; assumption.
Qed.

Lemma norm3 :
 forall x y : R,
 (x - y)%R <> 0%R ->
 (x + y)%R <> 0%R ->
 (x * x - y * y)%R <> 0%R ->
 (x / (x - y) + y / (x + y) + 2 * y * (y / (x * x - y * y)))%R =
 ((x + y) / (x - y))%R.
Proof.
  intros x y H H0 H1.
  normal (x / (x - y) + y / (x + y) + 2 * y * (y / (x * x - y * y)))%R.
  unfold Rminus in |- *; reflexivity.
  unfold Rminus in H, H1; split_Rmult; assumption.
Qed.

(**** Eval <Maple Tactic> in ****)

Lemma eval_simp0 :
 forall x y : R, (x * y)%R <> 0%R -> (x / x + y / y)%R = 2%R.
Proof.
  intros.
  let t := eval simplify 0 in (x / x + y / y)%R in
  replace (x / x + y / y)%R with t.
  reflexivity.
  field; assumption.
Qed.

Lemma eval_fact0 :
 forall x y : R, x <> 0%R -> y <> 0%R -> (x / x + x / y)%R = ((x + y) / y)%R.
Proof.
  intros.
  let t := eval factor 0 in (x / x + x / y)%R in
  replace (x / x + x / y)%R with t.
  rewrite Rplus_comm; reflexivity.
  field; split_Rmult; assumption.
Qed.

Lemma eval_expd0 :
 forall x y : R,
 ((3 * x + 3) * (y - 5 / 3))%R = (3 * x * y + - (5 * x) + 3 * y + -5)%R.
Proof.
  intros.
  let t := eval expand 0 in ((3*x+3)*(y-5/3))%R in
  replace ((3*x+3)*(y-5/3))%R with t.
  reflexivity.
  field;discrR.
Save.

Lemma eval_norm0 :
 forall x y : R,
 x <> 0%R -> y <> 0%R -> (y / (x * y) + y / x)%R = ((1 + y) / x)%R.
Proof.
  intros.
  let t := eval normal 0 in (y / (x * y) + y / x)%R in
  replace (y / (x * y) + y / x)%R with t.
  unfold Rdiv in |- *; reflexivity.
  field; split_Rmult; assumption.
Qed.

Definition def0 := Eval simplify 0 in (1 / 1)%R.

(* no longer supported
Definition def1 (x,y:R) := Eval simplify 0 in (x/y+y)*y)%R.

Definition def2 (x,y:R) := Eval factor 0 in (x*y+x)%R .

Definition def3 (x,y:R) := Eval factor 0 in (x*y-3*x+7*y-21)%R.

Definition def4 (x,y:R) := Eval expand 0 in ((x+y)*x)%R.

Definition def5 (x,y:R) := Eval expand 0 in ((x-7)*(y+4))%R.

Definition def6 (x,y:R) := Eval normal 0 in (/x+/y)%R.

Definition def7 (x,y:R) := Eval normal 0 in (x*x*y/(x+y)+y*x*y/(x+y))%R.
*)
