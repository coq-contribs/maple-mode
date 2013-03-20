(* maple.ml4 *)

open Util
open Pp
open Flags

open Names
open Nameops
open Term
open Termops
open Environ
open Reductionops
open Libnames
open Proof_type
open Tacinterp
open Tacticals
open Tacexpr
open Namegen

(* Returns the version of Maple *)
let version maple =
  let tmp = Filename.temp_file "maple" "version" in
  let ins = "echo quit | "^maple^
            " | sed -n -e 's|.*\\(Maple*.*Release\\)|\\1|p' > "^tmp in
  begin
    let _ = Sys.command ins in ();
    let inc = open_in tmp in
    let ver = input_line inc in
    begin
      close_in inc;
      Sys.remove tmp;
      ver
    end
  end

(* Prints the Coq-Maple logo *)
let print_logo maple =
  let ver =
    if Filename.basename maple = "fake_maple" then "fake_maple"
    else version maple in
  begin
    print_endline ("\nCoq is now powered by Maple ["^ver^"]\n");
    print_endline "       |\\^/|              v";
    print_endline "   ._|\\|   |/|_.  ====>  <O___,,";
    print_endline "    \\  MAPLE  /   ====>   \\VV/";
    print_endline "    <____ ____>            //";
    print_endline "         |"
  end

(* Tries the MAPLE environment variable or else simply maple *)
let select_name () =
  try let maple = Sys.getenv "MAPLE" in
    if (Sys.command ("sh -c \"echo quit | "^maple^" -q\" 2>/dev/null"))=0 then
      maple
    else ""
  with Not_found ->
    try
      if (Sys.command "sh -c \"echo quit | maple -q\" 2>/dev/null")=0 then
	"maple"
      else ""
    with Not_found -> ""

(* Verifies that Maple is available *)
let is_maple flag =
  let maple = select_name () in
  if maple<>"" then
    (if flag then if_verbose print_logo maple)
  else
    (if flag then print_endline "\nError: Cannot find Maple"
     else errorlabstrm "is_maple" (str "Cannot find Maple"));
  maple

(* The expression data type *)
type expr =
  | Cst of Bigint.bigint
  | Var of int
  | Add of expr*expr
  | Opp of expr
  | Mul of expr*expr
  | Inv of expr
  | Pow of expr*int

let constr_from dir s =
  let id = id_of_string s in
  try
    constr_of_reference (Nametab.global_of_path (make_path dir id))
  with Not_found -> anomaly ("Could not find '"^s^"'.")

(* Builds the constants of the Field reflexion structure *)
let path_field_theory =
  make_dirpath (List.map id_of_string
    (List.rev ["Coq";"setoid_ring";"Field_theory"]))

let fcst = constr_from path_field_theory "FEc"
let fadd = constr_from path_field_theory "FEadd"
let fsub = constr_from path_field_theory "FEsub"
let fopp = constr_from path_field_theory "FEopp"
let fmul = constr_from path_field_theory "FEmul"
let fdiv = constr_from path_field_theory "FEdiv"
let finv = constr_from path_field_theory "FEinv"
let fpow = constr_from path_field_theory "FEpow"
let fvar = constr_from path_field_theory "FEX"

let path_nat =  make_dirpath (List.map id_of_string
    (List.rev ["Coq";"Init";"Datatypes"]))

let eO = constr_from path_nat "O"
let eS = constr_from path_nat "S";;

let path_bin =  make_dirpath (List.map id_of_string
    (List.rev ["Coq";"Numbers";"BinNums"]))

let zcoq = constr_from path_bin "Z"
let z0   = constr_from path_bin "Z0"
let zpos = constr_from path_bin "Zpos"
let zneg = constr_from path_bin "Zneg"
let xH   = constr_from path_bin "xH"
let xI   = constr_from path_bin "xI"
let xO   = constr_from path_bin "xO"
let n0   = constr_from path_bin "N0"
let npos = constr_from path_bin "Npos"


(* Generic transformers between various flavours of numbers *)
type 'a pos = P1 | PO of 'a | PI of 'a
type 'a z = Z0 | Zpos of 'a | Zneg of 'a
let bin_trans (dz, dp) (f0, fpos, fneg, f1, f2n, f2n1) n =
  let rec trad n =
    match dp n with
      | P1 -> f1
      | PO p -> f2n (trad p)
      | PI p -> f2n1 (trad p) in
  match dz n with
    | Z0 -> f0
    | Zpos p -> fpos (trad p)
    | Zneg p -> fneg (trad p)

let mk_int =
  (0, (fun x->x), (fun x-> -x), 1, (fun x->2*x), (fun x->2*x+1))

let mk_bigint =
  (Bigint.zero, (fun x->x), Bigint.neg, Bigint.one, Bigint.mult_2,
   (fun x->Bigint.add_1(Bigint.mult_2 x)))

let mk_pos =
  (xH, (fun x->x), (fun _ -> failwith"not a positive"),
   xH, (fun x->mkApp(xO,[|x|])), (fun x->mkApp(xI,[|x|])))

let mk_N =
  (n0, (fun x->mkApp(npos,[|x|])), (fun _ -> failwith"negative"),
   xH, (fun x->mkApp(xO,[|x|])), (fun x->mkApp(xI,[|x|])))

let mk_Z =
  (z0, (fun x->mkApp(zpos,[|x|])), (fun x->mkApp(zneg,[|x|])), 
   xH, (fun x->mkApp(xO,[|x|])), (fun x->mkApp(xI,[|x|])))

let dest_int =
  ((fun n ->
      if n=0 then Z0
      else if n<0 then Zneg n
      else Zpos n),
   (fun n -> 
      if n=1 then P1
      else if n mod 2 = 1 then PI (n/2) else PO (n/2)))

let dest_bigint =
  ((fun n ->
      if n=Bigint.zero then Z0
      else if Bigint.is_strictly_neg n then Zneg n
      else Zpos n),
   (fun n -> 
      if n=Bigint.one then P1
      else
	let (q,r) = Bigint.div2_with_rest n in
	if r then PI q else PO q))

let whd_all t = whd_betadeltaiota (Global.env()) Evd.empty t

let dest_pos =
  ((fun p -> Zpos p),
   (fun p ->
      let p = whd_all p in
      if p=xH then P1 else
	match kind_of_term p with
	    App(h,[|q|]) ->
	      if h=xO then PO q
	      else if h=xI then PI q
	      else failwith "not a ground positive"
	  | _ -> failwith "not a ground positive"))

let dest_N =
  ((fun n ->
      let n = whd_all n in
      if n=n0 then Z0 else
	match kind_of_term n with
	    App(h,[|q|]) when h=npos -> Zpos q
	  | _ -> failwith "not a ground N natural"),
   snd dest_pos)

let dest_Z =
  ((fun n ->
      let n = whd_all n in
      if n=z0 then Z0 else
	match kind_of_term n with
	    App(h,[|q|]) ->
	      if h=zpos then Zpos q
	      else if h=zneg then Zneg q
	      else failwith "not a ground Z number"
	  | _ -> failwith "not a ground Z number"),
   snd dest_pos)

(* Builds expr expressions from ExprA expressions *)
let rec expra_to_expr csr =
  match kind_of_term csr with
  | App(c,[|_;t1;t2|]) ->
      let op = List.assoc c
	[fadd,(fun () -> Add(expra_to_expr t1, expra_to_expr t2));
	 fsub,(fun () -> Add(expra_to_expr t1, Opp(expra_to_expr t2)));
	 fmul,(fun () -> Mul(expra_to_expr t1, expra_to_expr t2));
	 fdiv,(fun () -> Mul(expra_to_expr t1, Inv(expra_to_expr t2)));
	 fpow,(fun () -> Pow(expra_to_expr t1, bin_trans dest_N mk_int t2))] in
      op()
  | App(c,[|_;t|]) ->
      let op = List.assoc c
	[fopp,(fun () -> Opp(expra_to_expr t));
	 finv,(fun () -> Inv(expra_to_expr t));
	 fvar,(fun () -> Var(bin_trans dest_pos mk_int t));
	 fcst,(fun () -> Cst(bin_trans dest_Z mk_bigint t))] in
      op()
  | _ -> raise Not_found

let expra_to_expr c =
  try expra_to_expr c
  with Not_found ->
    errorlabstrm "expra_to_expr" (str "This term is not of type FExpr")

(* Builds ExprA expressions from expr expressions *)
let rec expr_to_expra = function
  | Cst n -> mkApp (fcst,[|zcoq;bin_trans dest_bigint mk_Z n|])
  | Var n -> mkApp (fvar,[|zcoq;bin_trans dest_int mk_pos n|])
  | Opp e -> mkApp (fopp,[|zcoq;expr_to_expra e|])
  | Inv e -> mkApp (finv,[|zcoq;expr_to_expra e|])
  | Add (e1,e2) -> mkApp (fadd,[|zcoq;expr_to_expra e1;expr_to_expra e2|])
  | Mul (e1,e2) -> mkApp (fmul,[|zcoq;expr_to_expra e1;expr_to_expra e2|])
  | Pow (e,n) -> mkApp (fpow,[|zcoq;expr_to_expra e;bin_trans dest_int mk_N n|])

(* Prepares the call to Maple *)
let rec string_of_expr = function
  | Cst n -> Bigint.to_string n
  | Var n -> "x"^string_of_int (n-1)
  | Opp e -> "(-"^string_of_expr e^")"
  | Inv e -> "(1/"^string_of_expr e^")"
  | Add (e1,e2) -> "("^string_of_expr e1^"+"^string_of_expr e2^")"
  | Mul (e1,e2) -> "("^string_of_expr e1^"*"^string_of_expr e2^")"
  | Pow (e,n) -> "("^string_of_expr e^"^"^string_of_int n^")"

(* Gives the index of xi *)
let var_of_string x =
  try int_of_string (String.sub x 1 ((String.length x)-1)) + 1
  with _ -> error "Unable to parse Maple answer"

(* Parsing of Maple expressions *)
IFDEF CAMLP5 THEN
let gram = Grammar.gcreate (Plexer.gmake ())
ELSE
let gram = Grammar.create (Plexer.make ())
END;;

let mexpr_s = Grammar.Entry.create gram "mexpr_s";;
let mexpr = Grammar.Entry.create gram "mexpr";;

EXTEND
  mexpr_s: [ [ "p"; ":="; m = mexpr; ";" -> m ] ];
  mexpr:
    [ "plus" LEFTA
      [ x = mexpr; "+"; y = mexpr -> Add (x,y)
      | x = mexpr; "-"; y = mexpr -> Add (x,Opp y) ]
    | "mult" LEFTA
      [ x = mexpr; "*"; y = mexpr -> Mul (x,y) ]
    | "div" LEFTA
      [ INT "1"; "/"; x = mexpr -> Inv x
      | x = mexpr; "/"; y = mexpr -> Mul (x,Inv y) ]
    | "simple" NONA
      [ "-"; x = mexpr -> Opp x
      | x = mexpr; "^"; n = INT -> Pow(x,int_of_string n)
      | n = INT -> Cst(Bigint.of_string n)
      | x = LIDENT -> Var (var_of_string x)
      | "("; e = mexpr; ")" -> e ] ];
END;;

(* Calls Maple with the corresponding operation *)
let maple_call exe =
  let tmp = Filename.temp_file "coq" "maple" in
  let ins = "p := "^exe^":\nsave p,\\\""^tmp^"\\\":" in
  begin
    let maple = is_maple false in
    let _ = Sys.command ("echo \""^ins^"\" | "^maple^" -q") in ();
    let inc = open_in tmp in
    let exp =
      try Grammar.Entry.parse mexpr_s (Stream.of_channel inc)
      with Compat.Loc.Exc_located (_,e) -> raise e in
    begin
      close_in inc;
      Sys.remove tmp;
      exp
    end
  end

(* Generic operation of Maple *)
let operation ope csr g =
  let ste = string_of_expr (expra_to_expr csr) in
  let res = maple_call (ope^"("^ste^")") in
  expr_to_expra res

(* Replace rels by names *)
let name_rels env c =
  let (env,subst) =
    fold_rel_context (fun _ (na,b,t) (env,subst) ->
      let id = match na with
	| Name id -> id
	| _ -> next_ident_away (id_of_string "x") (ids_of_context env) in
      (push_named (substl_named_decl subst (id,b,t)) env, mkVar id :: subst))
      env
      ~init:(reset_with_named_context (named_context_val env) env, []) in
  (env, List.map destVar subst, substl subst c)

let apply_ope ope env sigma c =
  let (env,vars,c) = name_rels env c in
  let g, _, sigma =
    Goal.V82.mk_goal sigma (named_context_val env) (*Dummy goal*) mkProp Store.empty in
  let g = { Evd.it=g; Evd.sigma=sigma } in
  subst_vars vars (ope c g)

let maple ope = apply_ope (operation ope)

(* Declare the new reductions (used by "eval" commands and "Eval" constr) *)
let _ = Redexpr.declare_reduction "raw_simplify" (maple "simplify") in
let _ = Redexpr.declare_reduction "raw_factor" (maple "factor") in
let _ = Redexpr.declare_reduction "raw_expand" (maple "expand") in
let _ = Redexpr.declare_reduction "raw_normal" (maple "normal") in ()

(* Iterates the tactic over the term list *)
let tac_iter tac lcr =
  List.fold_right (fun c a -> tclTHENFIRST (tac c) a) lcr tclIDTAC


TACTIC EXTEND maple_fun_simplify
| [ "tac_iter" tactic0(tac) ne_constr_list(cl) ] ->
     [ tac_iter (fun c -> Newring.ltac_apply tac [Newring.carg c]) cl ]
END

let constr_from_goal gls =
  match gls.Evd.it with
      [concl] ->
        let g = Goal.V82.concl gls.Evd.sigma concl in
	(match kind_of_term g with
	     Prod(_,eq,_) ->
	       (match kind_of_term eq with
		    App(h,[|_;lhs;_|]) -> lhs
		  | _ -> failwith "ill-formed goal")
	   | _ -> failwith "ill-formed goal")
    | _ -> failwith "ill-formed goal"

let red_of_tac tac c g =
  let ist =
    { lfun = []; avoid_ids = [];
      debug = Tactic_debug.DebugOff; trace = [] } in
(*  let tac = ltac_letin ("F", Tacexp tac) (ltac_lcall "F" [carg c]) in*)
  let tac = Newring.ltac_call tac [Newring.carg c] in
  match val_interp ist g tac with
    | sigma, (VFun _ as v) ->
        let g = { g with Evd.sigma=sigma } in
	constr_from_goal (interp (Tacexpr.TacArg(dummy_loc,valueIn v)) g)
    | _ -> assert false

let apply_tac tac =
  apply_ope (red_of_tac tac)

(*
let declare_redexpr id tac =
  Redexpr.declare_reduction id (apply_tac tac)

VERNAC COMMAND EXTEND NewRed
  | [ "Add" "Reduction" ident(id) ":=" tactic(tac) ] ->
    [ declare_redexpr (string_of_id id) (glob_tactic tac) ]
END
*)
let maple_tac s =
  let dp = make_dirpath (List.map id_of_string ["Maple";"MapleMode"]) in
  lazy(make_kn (MPfile dp) (make_dirpath []) (mk_label s))

let maple_reduce ope =
  apply_tac (maple_tac ope)

let _ = Redexpr.declare_reduction "simplify" (maple_reduce "red_simplify") in
let _ = Redexpr.declare_reduction "factor" (maple_reduce "red_factor") in
let _ = Redexpr.declare_reduction "expand" (maple_reduce "red_expand") in
let _ = Redexpr.declare_reduction "normal" (maple_reduce "red_normal") in ()

(* Verifies if Maple is available during the ML loading *)
let _ = is_maple true
