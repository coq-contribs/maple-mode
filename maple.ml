(* maple.ml4 *)

open Command
open Declare
open Field
open Names
open Libnames
open Options
open Pp
open Proof_type
open Safe_typing
open Tacinterp
open Tacticals
open Tacmach
open Term
open Util
open Vernacinterp
open Evd

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
  let ver = version maple in
  begin
    print_endline ("\nCoq is now powered by Maple ["^ver^"]\n");
    print_endline "    |\^/|              v";
    print_endline "._|\|   |/|_.  ====>  <O___,,";
    print_endline " \  MAPLE  /   ====>   \VV/";
    print_endline " <____ ____>            //";
    print_endline "      |"
  end

(* Tries the MAPLE environment variable or else simply maple *)
let select_name () =
  try let maple = Sys.getenv "MAPLE" in
    if (Sys.command ("sh -c \"echo quit | "^maple^" -q\" 2>/dev/null"))=0 then
      maple
    else ""
  with Not_found ->
    if (Sys.command "sh -c \"echo quit | maple -q\" 2>/dev/null")=0 then
      "maple"
    else ""

(* Verifies that Maple is available *)
let is_maple flag =
  let maple = select_name () in
  begin
    if maple<>"" then
      (if flag then if_verbose print_logo maple)
    else
      (if flag then print_endline "\nError: Cannot find Maple"
               else errorlabstrm "is_maple" (str "Cannot find Maple"));
    maple
  end

(* The expression data type *)
type expr =
  | Zero
  | One
  | Var of int
  | Opp of expr
  | Inv of expr
  | Plus of expr*expr
  | Mult of expr*expr

(* Builds the constants of the Field reflexion structure *)
let path_field_theory =
  make_dirpath (List.map id_of_string
    (List.rev ["Coq";"field";"Field_Theory"]))

let path_nat =  make_dirpath (List.map id_of_string
    (List.rev ["Coq";"Init";"Datatypes"]))

let constr_from dir s =
  let id = id_of_string s in
  constr_of_reference (Nametab.absolute_reference (make_path dir id))

let eazero = constr_from path_field_theory "EAzero"
let eaone  = constr_from path_field_theory "EAone"
let eaplus = constr_from path_field_theory "EAplus"
let eamult = constr_from path_field_theory "EAmult"
let eaopp  = constr_from path_field_theory "EAopp"
let eainv  = constr_from path_field_theory "EAinv"
let eavar  = constr_from path_field_theory "EAvar"

let eO = constr_from path_nat "O"
let eS = constr_from path_nat "S";;

(* Gives an int from a nat constr *)
let rec int_of_constr csr =
  match (kind_of_term csr) with
  | c when c = (kind_of_term eO) -> 0
  | App(c,t) when c = eS -> (int_of_constr t.(0))+1
  | _ ->
    errorlabstrm "int_of_constr"
      (str "This term is not a closed natural number")

(* Builds expr expressions from ExprA expressions *)
let rec expra_to_expr csr =
  match (kind_of_term csr) with
  | c when c = (kind_of_term eazero) -> Zero
  | c when c = (kind_of_term eaone)  -> One
  | App(c,t) when (c = eaplus || c = eamult) ->
    let e1 = expra_to_expr t.(0)
    and e2 = expra_to_expr t.(1) in
    if c = eaplus then Plus (e1,e2)
    else Mult (e1,e2)
  | App(c,t) when c = eaopp || c = eainv ->
    let e = expra_to_expr t.(0) in
    if c = eaopp then Opp e
    else Inv e
  | App(c,t) when c = eavar -> Var (int_of_constr t.(0))    
  | _ -> errorlabstrm "expra_to_expr" (str "This term is not of type ExprA")

(* Gives a nat constr from an int *)
let rec constr_of_int n =
  if n = 0 then eO
  else applist (eS,[constr_of_int (n-1)])

(* Builds ExprA expressions from expr expressions *)
let rec expr_to_expra = function
  | Zero -> eazero
  | One  -> eaone
  | Var n -> applist (eavar,[constr_of_int n])
  | Opp e -> applist (eaopp,[expr_to_expra e])
  | Inv e -> applist (eainv,[expr_to_expra e])
  | Plus (e1,e2) -> applist (eaplus,[expr_to_expra e1;expr_to_expra e2])
  | Mult (e1,e2) -> applist (eamult,[expr_to_expra e1;expr_to_expra e2])

(* Prepares the call to Maple *)
let rec string_of_expr = function
  | Zero -> "0"
  | One  -> "1"
  | Var n -> "x"^(string_of_int n)
  | Opp e -> "(-"^(string_of_expr e)^")"
  | Inv e -> "(1/"^(string_of_expr e)^")"
  | Plus (e1,e2) -> "("^(string_of_expr e1)^"+"^(string_of_expr e2)^")"
  | Mult (e1,e2) -> "("^(string_of_expr e1)^"*"^(string_of_expr e2)^")"

(* Gives the expr expression corresponding to an int *)
let rec int_decomp m =
  if Bigint.equal m Bigint.zero then [0] else
  if Bigint.equal m Bigint.one then [1] else
  let (m',b) = Bigint.euclid m Bigint.two in
  (if Bigint.equal b Bigint.zero then 0 else 1) :: int_decomp m'

let rec mexpr_of_int n =
 let list_ch = int_decomp n in
 let two = Plus (One,One) in
 let rec mk_r l =
   match l with
   | [] -> failwith "Error r_of_posint"
   | [a] -> if a=1 then One else Zero
   | a::[b] -> if a==1 then Plus (One,two) else two
   | a::l' ->
      if a=1 then Plus (One, Mult (two, mk_r l'))
      else Mult (two, mk_r l')
 in mk_r list_ch

(* Gives the index of xi *)
let var_of_string x =
  try int_of_string (String.sub x 1 ((String.length x)-1))
  with _ -> error "Unable to parse Maple answer"

(* Expands the power operation *)
let rec expand_power x n =
  if n < 2 then assert false
  else if n = 2 then Mult (x,x)
  else Mult (expand_power x (n-1),x)

(* Ensures left associativity for Mult (necessary after power unfoldings *)
let left_assoc x y =
  match y with
  | Mult (a,b) -> Mult (Mult (x,a),b)
  | _ -> Mult (x,y)

(* Parsing of Maple expressions *)
let gram = Grammar.create (Plexer.make ());;
let mexpr_s = Grammar.Entry.create gram "mexpr_s";;
let mexpr = Grammar.Entry.create gram "mexpr";;

EXTEND
  mexpr_s: [ [ "p"; ":="; m = mexpr; ";" -> m ] ];
  mexpr:
    [ "plus" LEFTA
      [ x = mexpr; "+"; y = mexpr -> Plus (x,y)
      | x = mexpr; "-"; y = mexpr -> Plus (x,Opp y) ]
    | "mult" LEFTA
      [ x = mexpr; "*"; y = mexpr -> left_assoc x y ]
    | "div" LEFTA
      [ INT "1"; "/"; x = mexpr -> Inv x
      | x = mexpr; "/"; y = mexpr -> Mult (x,Inv y) ]
    | "simple" NONA
      [ "-"; x = mexpr -> Opp x
      | x = mexpr; "^"; n = INT -> expand_power x (int_of_string n)
      | n = INT -> mexpr_of_int (Bigint.of_string n)
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
      with Stdpp.Exc_located (_,e) -> raise e in
    begin
      close_in inc;
      Sys.remove tmp;
      exp
    end
  end

(* Returns the constr tactic_arg or globalizes the identifier tactic_arg *)
let constr_or_id env tca =
  try (constr_of_VConstr env tca)
  with Anomaly ("constr_of_Constr",_) ->
    constr_of_id env (id_of_Identifier env tca)

let constrInArg x = valueIn (VConstr x)

(* Applies the metaification *)
let metaification ist gl th csr =
  let ca = constrInArg csr in
  let tac = glob_tactic <:tactic<(build_varlist $th $ca)>> in
  let lvar = constr_of_VConstr (pf_env gl) (val_interp ist gl tac) in
  let meta = constr_or_id (pf_env gl) (val_interp ist gl 
    (let lvar = constrInArg lvar in
     glob_tactic <:tactic<(interp_A $th $lvar $ca)>>)) in
  (constrIn lvar,meta)

(* Generic operation of Maple *)
let operation ope csr ist g =
  let th = guess_theory (pf_env g) (project g) [csr]
  and ca = constrInArg csr in
  let th_arg = constrInArg th in
  let cex = constr_of_VConstr (pf_env g) (val_interp ist g
    (glob_tactic <:tactic<init_exp $th_arg $ca>>)) in
  let (lvar,meta) = metaification ist g th_arg cex in
  let ste = string_of_expr (expra_to_expr meta) in
  let exs = constrIn (expr_to_expra (maple_call (ope^"("^ste^")"))) in
  constr_of_VConstr (pf_env g) (val_interp ist g
    (let th = constrIn th in
    glob_tactic <:tactic<eval compute in (interp_ExprA $th $lvar $exs)>>))

(* Replace rels by names *)
open Environ
open Nameops
open Termops
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

(* Applies the operation on the constant body *)
let apply_ope ope env sigma c =
  let (env,vars,c) = name_rels env c in
  let ist = {lfun=[];debug=get_debug ()} in
  let g =
    Proof_trees.mk_goal (named_context_val env) (*Dummy goal*) mkProp
  in
  let g = { it=g; sigma=sigma } in
  subst_vars vars (operation ope c ist g)

(* Declare the new reductions (used by "eval" commands and "Eval" constr) *)
 let _ = Redexpr.declare_red_expr "simplify" (apply_ope "simplify") in
 let _ = Redexpr.declare_red_expr "factor" (apply_ope "factor") in
 let _ = Redexpr.declare_red_expr "expand" (apply_ope "expand") in
 let _ = Redexpr.declare_red_expr "normal" (apply_ope "normal") in ()

(* Generic tactic operation *)
let tactic_operation ope csr g =
  let ist = {lfun=[];debug=get_debug ()} in
  let css = operation ope csr ist g in
  let tac = 
    Tacexpr.TacArg (valueIn (VTactic (dummy_loc,Equality.replace csr css)))
  and fld = Tacexpr.TacArg (valueIn (VTactic (dummy_loc,field))) in
  (interp_tac_gen ist.lfun ist.debug
    <:tactic<$tac;[idtac|$fld]>>) g

(* Iterates the tactic over the term list *)
let tac_iter tac lcr =
  List.fold_right (fun c a -> tclTHENFIRST (tac c) a) lcr tclIDTAC

(* Builds the tactic from the name *)
let build_tactic nme = tac_iter (tactic_operation nme)

(* Declaration of the generic tactic *)
TACTIC EXTEND maple_fun_simplify
| [ "simplify" ne_constr_list(cl) ] -> [ build_tactic "simplify" cl ]
END

TACTIC EXTEND maple_fun_factor
| [ "factor" ne_constr_list(cl) ] -> [ build_tactic "factor" cl ]
END

TACTIC EXTEND maple_fun_expand
| [ "expand" ne_constr_list(cl) ] -> [ build_tactic "expand" cl ]
END

TACTIC EXTEND maple_fun_normal
| [ "normal" ne_constr_list(cl) ] -> [ build_tactic "normal" cl ]
END

(* Verifies if Maple is available during the ML loading *)
let _ = is_maple true
