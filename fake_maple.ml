let answers =
 [ "p := simplify((x0*(1/x0))):", "1";
   "p := simplify(((1+x0)*(1/(1+x0)))):", "1";
   "p := simplify(((((((x1*(1/x0))+(x0*(1/x1)))*x1)*x0)+(-((x1*x1)+(x0*x0))))+1)):", "1";
   "p := simplify(((x1*(1/(x1+x0)))+(x0*(1/(x1+x0))))):", "1";
   "p := factor((((x1*x1)+(((1+1)*x1)*x0))+(x0*x0))):", "(x1 + x0)^2";
   "p := factor((((x1*x1)+(-(((1+1)*x1)*x0)))+(x0*x0))):", "(x1-x0)^2";
   "p := factor(((x1*x1)+(-(x0*x0)))):", "(x1-x0)*(x1+x0)";
   "p := factor((((((x1*x1)*x1)+((((1+(1+1))*x1)*x1)*x0))+((((1+(1+1))*x1)*x0)*x0))+((x0*x0)*x0))):", "(x1+x0)^3";
   "p := expand(((x1+x0)*(x1+x0))):", "x1^2+2*x1*x0+x0^2";
   "p := expand(((x1+(-x0))*(x1+(-x0)))):", "x1^2-2*x1*x0+x0^2";
   "p := expand(((x1+(-x0))*(x1+x0))):", "x1^2-x0^2";
   "p := expand((((x1+x0)*(x1+x0))*(x1+x0))):", "x1^3+3*x1^2*x0+3*x1*x0^2+x0^3";
   "p := normal(((x1*(1/x0))+(x0*(1/x1)))):", "(x1^2+x0^2)/x0/x1";
   "p := normal(((1/x0)+(x0*(1/(x0+1))))):", "(x0+1+x0^2)/x0/(x0+1)";
   "p := normal(((x1*(x1*(1/((x1+(-x0))*(x1+(-x0))))))+(-(x0*(x0*(1/((x1+(-x0))*(x1+(-x0))))))))):", "(x1+x0)/(x1-x0)";
   "p := normal((((x1*(1/(x1+(-x0))))+(x0*(1/(x1+x0))))+(((1+1)*x0)*(x0*(1/((x1*x1)+(-(x0*x0)))))))):", "(x1+x0)/(x1-x0)";
   "p := simplify(((x1*(1/x1))+(x0*(1/x0)))):", "2";
   "p := factor(((x1*(1/x1))+(x1*(1/x0)))):", "(x0+x1)/x0";
   "p := expand(((((1+(1+1))*x1)+(1+(1+1)))*(x0+(-((1+((1+1)*(1+1)))*(1/(1+(1+1)))))))):", "3*x1*x0-5*x1+3*x0-5";
   "p := normal(((x1*(1/(x0*x1)))+(x1*(1/x0)))):", "(1+x1)/x0";
   "p := simplify((1*(1/1))):", "1";
 ]
;;

let main () =
 (* A query has the following form:                          *)
 (* p := simplify((x0*(1/x0))):save p,"/tmp/coqc5a0d6maple": *)
 let compute = read_line () in
 if compute = "quit" then exit 0 ;
 let save = read_line () in
 assert(try ignore (read_line ()) ; false with End_of_file -> true);
 let filename =
  match Str.split (Str.regexp "\"") save with
     [ "save p," ; filename; ":" ] -> filename
   | _ -> assert false
 in
  let ans =
   try List.assoc compute answers
    (* for debugging only: the query is returned as the answer *)
   with Not_found -> compute in
  let fo = open_out filename in
   output_string fo ("p := " ^ ans ^ ";");
   close_out fo
;;

main ()
