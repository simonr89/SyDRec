(* Copyright Université d'Orléans (France)
   contributor : Simon Robillard (2014)
   simon.robillard@univ-orleans.fr

   This software is a computer program whose purpose is to provide
   functionalities to construct and derive programs with the Coq Proof
   Assistant.

   This software is governed by the CeCILL-C license under French law
   and abiding by the rules of distribution of free software.  You can
   use, modify and/ or redistribute the software under the terms of
   the CeCILL-C license as circulated by CEA, CNRS and INRIA at the
   following URL "http://www.cecill.info".

   As a counterpart to the access to the source code and rights to
   copy, modify and redistribute granted by the license, users are
   provided only with a limited warranty and the software's author,
   the holder of the economic rights, and the successive licensors
   have only limited liability.

   In this respect, the user's attention is drawn to the risks
   associated with loading, using, modifying and/or developing or
   reproducing the software by the user in light of its specific
   status of free software, that may mean that it is complicated to
   manipulate, and that also therefore means that it is reserved for
   developers and experienced professionals having in-depth computer
   knowledge. Users are therefore encouraged to load and test the
   software's suitability as regards their requirements in conditions
   enabling the security of their systems and/or data to be ensured
   and, more generally, to use and operate it in the same conditions
   as regards security.

   The fact that you are presently reading this means that you have
   had knowledge of the CeCILL-C license and that you accept its
   terms. *)

open Decl_kinds   (* libray/decl_kinds.mli *)
open Declare      (* library/declare.mli *)
open Entries      (* kernel/entries.mli *)
open Inductiveops (* pretyping/inductiveops.mli *)
open Libnames     (* library/libnames.mli *)
open Names        (* kernel/toplevel.mli *)
open Pp           (* lib/pp/mli *)
open Tacticals    (* tactics.tacticals.mli *)
open Tactics      (* tactics/tactics.mli *)
open Term         (* kernel/term.mli *)
open Termops      (* pretyping/termops.mli *)
open Util         (* lib/util.mli *)

type morphism = Cata | Para

(* This file is about catamorphism/paramorphism and fusion theorem
   generation from an inductive type definition.

   We rely on the following type for examples and explanations:

   Inductive ilist (T : Type) : nat -> Type :=
   | inil : ilist T O
   | icons : forall n, T -> ilist T n -> ilist T (S n).

   This declaration covers every possibility: it features a parameter
   A and an argument n, and of course is inductive.

   A note on numbering : inductive type constructors are numbered
   starting from 1. Throughout this file, we follow this numbering
   convention: everything that is related to a constructor (e.g.
   catamorphism arguments or theorem conditions) is named with a
   number that matches that of the constructor. Everything else
   (parameters, constructor arguments) is numbered starting from 0.
*)

(************************* Coq references ***************************)

(* These references must be called lazily in case the module has not
   yet been compiled/required *)
let coq_eq =
  lazy (Coqlib.gen_constant "BMF module" ["Init" ; "Logic"] "eq")

(************************ Utility functions *************************)

(* String of the reference without the path *)
let short_string_of_reference = function
  | Qualid (_, qid) ->
    let (_, id) = repr_qualid qid in
    string_of_id id
  | Ident (_, id) -> string_of_id id

(* builds [f a, f (a + 1), ..., f (b - 1)] *)
let from_to f a b =
  let rec aux acc a b =
    if a >= b
    then List.rev acc
    else aux (f a :: acc) (a + 1) b
  in aux [] a b

(* Returns (a, b) where a is the sublist of the n first elements of l
   and b the other elements of l *)
let take_drop n l =
  let rec aux acc n l =
    if n <= 0
    then (List.rev acc, l)
    else match l with
      | [] -> (List.rev acc, l)
      | x :: xs -> aux (x :: acc) (n - 1) xs
  in aux [] n l

(* This returns true iff c1 and c2 represent the same inductive type,
   with the same parameters (if any) but possibly different real
   arguments.

   In our example: (ilist A n) and (ilist A m) are equivalent
                   (ilist A n) and (ilist B n) are not

   c1 and c2 should have type Set, Prop or Type : (ilist A) has type
   nat -> Type and therefore comparing it with anything, including
   itself, will return false.
*)
let rec eq_ind_modulo_args c1 c2 =
  match kind_of_term c1, kind_of_term c2 with
    | Ind i1, Ind i2 -> eq_ind i1 i2
    | App (s1, a1), App (s2, a2) when isInd s1 && isInd s2 ->
      let (i1, i2) = (destInd s1, destInd s2) in
      let (npar, nargs) = inductive_nargs (Global.env ()) i1 in
      if (npar + nargs) <> Array.length a1 ||
	Array.length a1 <> Array.length a2 ||
	not (eq_ind i1 i2)
      then false
      else
	begin
	  try
	    for i = 0 to npar - 1 do
	      if not (eq_constr a1.(i) a2.(i))
	      then raise Exit
	    done;
	    true
	  with Exit -> false
	end
    | _ -> false

(********************* Catamorphism generation **********************)

(* The definitions we want to generate are the following:

   cata_ilist =
   fun (p0 A : Type) (f1 : A) (f2 : nat -> p0 -> A -> A) =>
   fix rec (a0 : nat) (x : ilist p0 a0) : A :=
     match x with
     | inil => f1
     | icons y0 y1 y2 => f2 y0 y1 (rec y0 y2)
     end.

   para_ilist =
   fun (p0 A : Type) (f1 : A) (f2 : forall (a0 :nat), p0 -> ilist p0 a0 -> A -> A) =>
   fix rec (a0 : nat) (x : ilist p0 a0) : A :=
     match x with
     | inil => f1
     | icons y0 y1 y2 => f2 y0 y1 y2 (rec y0 y2)
     end.
*)

(* Morphism range type *)
let t_morphism_id = id_of_string "A"

let t_morphism = mkVar t_morphism_id

let t_morphism_sort = mkType (Univ.fresh_local_univ ())

(* Main morphism argument *)
let arg_id = id_of_string "x"

let arg = mkVar arg_id

(* Morphism arguments (one per type constrcutor) *)
let morphism_param_id n = id_of_string ("f"^(string_of_int n))

let morphism_param n = mkVar (morphism_param_id n)

(* Morphism parameters (that mirror the type parameters) *)
let param_id n = id_of_string ("p"^string_of_int n)

let param_var n = mkVar (param_id n)

(* Morphism arguments (that mirror the type real arguments) *)
let realarg_id n = id_of_string ("a"^string_of_int n)

let realarg_var n = mkVar (realarg_id n)

(* Constructor arguments (as used in pattern matching) *)
let cons_arg_id n = id_of_string ("y"^string_of_int n)

let cons_arg n = mkVar (cons_arg_id n)

(* Type of ith constructor (counting from 1). Type parameters are
   applied with variables p0 ... pn *)
let applied_type_of_ith_constructor ind i =
  let (npar, _) = inductive_nargs (Global.env ()) ind in
  let ctype = type_of_constructor (Global.env ()) (ind, i) in
  prod_applist ctype (from_to (fun n -> param_var n) 0 npar)

(* Inductive type term, after application of the parameters with
   variables p0 ... pn a0 .. am *)
let applied_ind ind =
  let (npar, nargs) = inductive_nargs (Global.env ()) ind in
  let ind_var = mkInd ind in
  if npar + nargs = 0
  then ind_var
  else let args =
	 from_to param_var 0 npar @
	   from_to realarg_var 0 nargs
       in
       mkApp (ind_var, Array.of_list args)

(* Type signature of the morphism argument associated with the ith
   constructor (counting from 1) of type ind *)
let rec mk_morphism_case_type mphism ind i t_trg =
  let t_src = applied_ind ind in
  let rec aux c n =
    match kind_of_term c with
      | Prod (_, t, _) ->
	begin
	(* prod_applist is there to rename arguments, as DB indexes
	   can be offset *)
	  let c' = aux (prod_applist c [cons_arg n]) (n + 1) in
	  match eq_ind_modulo_args t t_src, mphism with
	    | false, _ -> mkNamedProd (cons_arg_id n) t c'
	    | _, Cata -> mkNamedProd (cons_arg_id n) t_trg c'
	    | _, Para -> mkNamedProd (cons_arg_id n) t (mkArrow t_trg c')
	end
      | _ -> t_trg
  in aux (applied_type_of_ith_constructor ind i) 0

(* constr -> constr array
   Used to extract the correct arguments for recursive calls in the
   morphism definition*)
let args_of_ind c =
  match kind_of_term c with
    | App (i, args) when isInd i ->
      let (npar, nargs) =
	inductive_nargs (Global.env ()) (destInd i)
      in Array.sub args npar nargs
    | Ind _ -> [||]
    | _ -> assert false

(* Body of the ith (counting from 1) matching clause of the
   morphism. *)
let mk_morphism_case_body mphism ind i =
  let t_src = applied_ind ind in
  let t_cons = applied_type_of_ith_constructor ind i in
  let nargs = (mis_constr_nargs ind).(i - 1) in
  let (_, nrealargs) = inductive_nargs (Global.env ()) ind in
  let rec aux acc1 acc2 n x =
    match kind_of_term x with
      | Prod (name, t, c) ->
	let id = cons_arg_id n in
	let ci =
	  if eq_ind_modulo_args t t_src
	  then
	    (* the DB index represents the morphism fixpoint constant *)
	    let rec_app =
	      mkApp (mkRel (2 + nargs + nrealargs),
		     Array.append (args_of_ind t) [|mkVar id|])
	    in
	    match mphism with
	      | Cata ->	[ rec_app ]
	      | Para -> [ rec_app; mkVar id ]
	  else [ mkVar id ]
	in
	let c' =
	  match name with
	    | Anonymous -> c
	    | Name _ ->
	      (* renaming of real arg (dependent product) *)
	      prod_applist x [cons_arg n]
	in aux ((id, None, t) :: acc1) (ci @ acc2) (n + 1) c'
      | _ -> (List.rev acc1, List.rev acc2)
  in
  match kind_of_term t_cons with
    | Prod _ ->
      (* constructor has args, we must build a lambda *)
      let (args, app) = aux [] [] 0 t_cons in
      it_mkNamedLambda_or_LetIn
	(mkApp (morphism_param i, Array.of_list app))
	(List.rev args)
    | _ -> morphism_param i (* constructor with no arg *)

(* ind -> named_declaration list * named_declaration list *)
let params_decl_list ind =
  let (npar, nargs) = inductive_nargs (Global.env ()) ind in
  let rec aux acc n c =
    match kind_of_term c with
      | Prod (name, t, cs) ->
	let id =
	  if n < npar
	  then param_id n
	  else realarg_id (n - npar)
	in
	let c' = match name with
	  | Anonymous -> cs
	  | Name _ -> prod_applist c [mkVar id]
	in
	aux ((id, None, t) :: acc) (n + 1) c'
      | _ -> List.rev acc
  in
  let l = aux [] 0 (type_of_inductive (Global.env ()) ind) in
  take_drop npar l

let morphism_term mphism ind =
  let t_src = applied_ind ind in
  let ncons = nconstructors ind in
  let (params, realargs) = params_decl_list ind in
  let case_body = mkCase
    (make_case_info (Global.env ()) ind MatchStyle,
    (it_mkNamedLambda_or_LetIn
       t_morphism
       ((arg_id, None, t_src) :: List.rev realargs)),
     arg,
     Array.of_list (from_to (mk_morphism_case_body mphism ind) 1 (ncons + 1)))
  in
  let fix_body =
    it_mkNamedLambda_or_LetIn
      case_body
      ((arg_id, None, t_src) :: List.rev realargs)
  in
  let t_fix =
    it_mkNamedProd_or_LetIn (mkArrow t_src t_morphism) (List.rev realargs)
  in
  let fix = mkFix (([|List.length realargs|], 0),
		   ([|Name (id_of_string "morphism_fix")|],
		    [|t_fix|],
		    [|fix_body|]))
  in
  let args =
    (t_morphism_id, None, t_morphism_sort) ::
      from_to
      (fun i -> morphism_param_id i, None, mk_morphism_case_type mphism ind i t_morphism)
      1 (ncons + 1)
  in
  it_mkNamedLambda_or_LetIn fix (List.rev (params @ args))

(* Declares some arguments of the morphism implicit: the output
   type parameter and the arguments that correspond to parameters of
   the original inductive type.

   In our example this would be equivalent to the vernacular command:
   Arguments morphism_ilist {P0 T} _ _ {a0} _. *)
let morphism_implicits ind cst =
  let (npar, nargs) = inductive_nargs (Global.env ()) ind in
  let ncons = nconstructors ind in
  (* build a list of argument positions *)
  let pos n = Topconstr.ExplByPos (n, None), (true, true, false) in
  Impargs.declare_manual_implicits
    false
    (ConstRef cst)
    ~enriching:false
    [ from_to pos 1 (npar + 2) @
	from_to pos (npar + ncons + 2) (npar + ncons + nargs + 2) ]

let declare_morphism mphism ind s =
  let id = match mphism with
    | Cata -> id_of_string ("cata_"^s)
    | Para -> id_of_string ("para_"^s)
  in
  if exists_name id
  then alreadydeclared (Nameops.pr_id id ++ str " already exists")
  else let def_entry = {
	 const_entry_body   = morphism_term mphism ind;
	 const_entry_secctx = None;
	 const_entry_type   = None;
	 const_entry_opaque = false
       }
       in
       let c =
	 declare_constant
	   id
	   (DefinitionEntry def_entry, IsDefinition Definition)
       in
       morphism_implicits ind c;
       definition_message id;
       c

(******************** Fusion theorem generation *********************)

(* Here is the statement of the theorems we want to generate. The proof
   term is built internally in proof mode (another idea would be to
   build it manually, but it would be needlessly complicated).

   cata_ilist_fusion
     (P0 A B : Type)
     (f1 : A) (f2 : nat -> P0 -> A -> A)
     (h : A -> B)
     (g1 : B) (g2 : nat -> P0 -> B -> B),
     (H1 : g1 = h f1)
     (H2 : forall (y0 : nat) (y1 : P0) (y2 : A),
             g2 y0 y1 (h y2) = h (f2 y0 y1 y2)) :
   forall (a0 : nat) (x : ilist P0 a0),
     h (cata_ilist f1 f2 x) = cata_ilist g1 g2 x

   para_ilist_fusion
     (P0 A B : Type)
     (f1 : A) (f2 : forall (n : nat), P0 -> ilist p0 n -> A -> A)
     (h : A -> B)
     (g1 : B) (g2 : forall (n : nat), P0 -> ilist p0 n -> B -> B),
     (H1 : g1 = h f1)
     (H2 : forall (y0 : nat) (y1 : P0) (y2 : ilist p0 y0) (y3 : A),
             g2 y0 y1 y2 (h y3) = h (f2 y0 y1 y2 y3)) :
   forall (a0 : nat) (x : ilist P0 a0),
     h (para_ilist f1 f2 x) = para_ilist g1 g2 x
*)

(* Final morphism range type *)
let t_morphism2_id = id_of_string "B"

let t_morphism2 = mkVar t_morphism2_id

let t_morphism2_sort = mkType (Univ.fresh_local_univ ())

(* Intermediate function *)
let hfun_id = id_of_string "h"

let hfun = mkVar hfun_id

let hfun_sort = mkArrow t_morphism t_morphism2

(* Final morphism arguments (one per type constructor) *)
let morphism2_param_id n = id_of_string ("g"^(string_of_int n))

let morphism2_param n = mkVar (morphism2_param_id n)

(* Fusion theorem hypotheses *)
let hyp_id n = id_of_string ("H"^string_of_int n)

let hyp n = mkVar (hyp_id n)

(* Left hand side of the ith fusion hypothesis; it has the form [gi
   y0' ... yn']. yi' is either [h yi] if the ith constructor argument
   is inductive, or simply yi otherwise. For paramorphisms, count one
   more argument per recursive constructor argument (see example). *)
let mk_ith_hyp_lhs mphism ind i =
  let t_src = applied_ind ind in
  let rec aux acc t n =
    match kind_of_term t with
      | Prod (_, t, c) ->
	let (a, n') =
	  if eq_ind_modulo_args t t_src
	  then
	    match mphism with
	      | Cata -> ([ mkApp (hfun, [| cons_arg n |]) ], n + 1)
	      | Para -> ([ mkApp (hfun, [| cons_arg (n + 1) |]); cons_arg n ], n + 2)
	  else ([ cons_arg n ], n + 1)
	in
	aux (a @ acc) c n'
      | _ -> List.rev acc
  in
  mkApp (morphism2_param i,
	 Array.of_list (aux [] (applied_type_of_ith_constructor ind i) 0))

(* Right hand side of the ith fusion hypothesis; it has the form [h
   (ci y0 .. yn)] where ci is the ith constructor *)
let mk_ith_hyp_rhs mphism ind i =
  let t_src = applied_ind ind in
  let rec count_recargs acc t =
    match kind_of_term t with
      | Prod (_, t, c) ->
	if eq_ind_modulo_args t t_src
	then count_recargs (acc + 1) c
	else count_recargs acc c
      | _ -> acc
  in
  let n = (mis_constr_nargs ind).(i - 1) in
  let m = match mphism with
    | Cata -> 0
    | Para -> (count_recargs 0 (applied_type_of_ith_constructor ind i))
  in
  mkApp (hfun,
	 [| mkApp (morphism_param i,
		   Array.of_list (from_to cons_arg 0 (n + m))) |])

(* Type of the fusion hypothesis associated with the ith constructor
   (counting from 1). It has the form: [forall y0 ... yn, lhs = rhs]
   where n is the number of arguments of the constructor *)
let mk_ith_hyp mphism ind i =
  let t_src = applied_ind ind in
  let lhs = mk_ith_hyp_lhs mphism ind i in
  let rhs = mk_ith_hyp_rhs mphism ind i in
  let rec mk_prod c n =
    match kind_of_term c with
      | Prod (_, t, _) ->
	begin
	  let c' = prod_applist c [ cons_arg n ] in
	  match eq_ind_modulo_args t t_src, mphism with
	    | false, _ -> mkNamedProd (cons_arg_id n) t (mk_prod c' (n + 1))
	    | _, Cata ->
	      mkNamedProd (cons_arg_id n) t_morphism (mk_prod c' (n + 1))
	    | _, Para ->
	      mkNamedProd (cons_arg_id n) t
		(mkNamedProd (cons_arg_id (n + 1)) t_morphism
		   (mk_prod c' (n + 2)))
	end
      | _ -> mkApp (Lazy.force coq_eq, [|t_morphism2; lhs; rhs|])
  in mk_prod (applied_type_of_ith_constructor ind i) 0

let mk_theorem_args mphism ind =
  let ncons = nconstructors ind in
  let (params, realargs) = params_decl_list ind in
  let morphism1param i =
    (morphism_param_id i, None, mk_morphism_case_type mphism ind i t_morphism)
  in
  let morphism2param i =
    (morphism2_param_id i, None, mk_morphism_case_type mphism ind i t_morphism2)
  in
  (* Type parameters *)
  params @
    (* Morphisms output types *)
    [(t_morphism_id, None, t_morphism_sort);
     (t_morphism2_id, None, t_morphism2_sort)] @
    (* First morphism arguments *)
    from_to morphism1param 1 (ncons + 1) @
    (* Function h *)
    [(hfun_id, None, hfun_sort)] @
    (* Final morphism arguments *)
    from_to morphism2param 1 (ncons + 1) @
    (* Hypotheses *)
    from_to (fun n -> (hyp_id n, None, mk_ith_hyp mphism ind n)) 1 (ncons + 1) @
    (* Type real arguments *)
    realargs @
    (* Theorem argument *)
    [(arg_id, None, applied_ind ind)]

let mk_theorem_statement mphism ind morphism_cst =
  let ncons = nconstructors ind in
  let (npar, nargs) = inductive_nargs (Global.env ()) ind in
  let params = from_to param_var 0 npar in
  let args = from_to realarg_var 0 nargs @ [arg] in
  let morphism1_args =
    params @
      t_morphism :: from_to morphism_param 1 (ncons + 1) @
      args
  in
  let morphism2_args =
    params @
      t_morphism2 :: from_to morphism2_param 1 (ncons + 1) @
      args
  in
  let lhs =
    mkApp (hfun,
	   [| mkApp (mkConst morphism_cst, Array.of_list morphism1_args) |])
  in
  let rhs = mkApp (mkConst morphism_cst, Array.of_list morphism2_args) in
  it_mkNamedProd_or_LetIn
    (mkApp (Lazy.force coq_eq, [|t_morphism2; lhs; rhs|])) (* conclucion *)
    (List.rev (mk_theorem_args mphism ind)) (* args and hypotheses *)

(* Builds the intro pattern for the ith induction goal, as well as
   the tactic to solve it (that way we can call the objects we
   introduced by the identifiers we gave them) *)
let mk_ith_intro_pattern_and_tac_case ind i =
  let t_cons = applied_type_of_ith_constructor ind i in
  let idIH n = id_of_string ("IH"^string_of_int n) in
  let t_src = applied_ind ind in
  let loc = Util.dummy_loc in
  let rec aux acc1 acc2 t n =
    match kind_of_term t with
      | Prod (_, t, c) ->
	let intro_var = (loc, Genarg.IntroAnonymous) in
	if eq_ind_modulo_args t_src t
	then let id = idIH n in
	     let intro_hyp = (loc, Genarg.IntroIdentifier id) in
	     let tac = Equality.rewriteLR (mkVar id) in
	     aux (intro_hyp :: intro_var :: acc1) (tac :: acc2) c (n + 1)
	else aux (intro_var :: acc1) acc2 c (n + 1)
      | _ -> (List.rev acc1, tclTHENLIST (List.rev (apply (hyp i) :: acc2)))
  in aux [] [] t_cons 0
		     
(* This creates a tactic to solve the fusion theorem goal
   internally. Like the goal, the tactic script can be derived from
   the inductive type. In our example the produced tactic would be:

   intros; symmetry; induction x as [ _ | _ _ _ IH1 ]; simpl;
   [ apply H1 | rewrite IH1 ; apply H2]
*)
let custom_tactic ind =
  let ncons = nconstructors ind in
  let (pattern_list, tac_list) =
    List.split
      (from_to
	 (mk_ith_intro_pattern_and_tac_case ind) 1 (ncons + 1))
  in
  let ind_arg =
    (Tacexpr.ElimOnConstr (Evd.empty, (arg, Glob_term.NoBindings)),
     (None, Some (Util.dummy_loc, Genarg.IntroOrAndPattern pattern_list)))
  in
  let induction_x =
    induction_destruct true false ([ind_arg], None, None)
  in
  tclTHENS
    (tclTHENLIST [intros; symmetry; induction_x ; simpl_in_concl])
    tac_list

(* Fusion theorem term generation. We create a conclusion term, start
   a proof to which we apply a tactic created on the fly and get back
   the term. *)
let fusion_theorem_term mphism ind morphism_cst =
  let st = mk_theorem_statement mphism ind morphism_cst in
  let p = Proof.start [(Global.env (), st)] in
  let t = custom_tactic ind in
  Proof.run_tactic (Global.env ()) (Proofview.V82.tactic t) p;
  match Proof.return p with
    | [(c, _)] -> c
    | _ -> assert false

let declare_fusion_theorem mphism ind morphism_cst s =
  let id =
    match mphism with
      | Cata -> id_of_string ("cata_"^s^"_fusion")
      | Para -> id_of_string ("para_"^s^"_fusion")
  in
  if exists_name id
  then alreadydeclared (Nameops.pr_id id ++ str " already exists")
  else let def_entry = {
	 const_entry_body   = fusion_theorem_term mphism ind morphism_cst;
	 const_entry_secctx = None;
	 const_entry_type   = None;
	 const_entry_opaque = false
       }
       in
       let c =
	 declare_constant
	   id
	   (DefinitionEntry def_entry, IsProof Theorem)
       in
       definition_message id;
       c

(*************************** Declaration ****************************)

(* If r is a reference to an inductive type in Type or Set, this
   function attempts (provided the names are available) to declare a
   morphism function and a fusion theorem for the type. If not it
   will throw a NotFound exception. *)
let declarations mphism r =
  (* the Smartlocate function may raise a NotFound exception. No need
     to catch it, it will trigger a (useful) user message *)
  let ind = Smartlocate.global_inductive_with_alias r in
  let s = short_string_of_reference r in
  let (_, mip) = Global.lookup_inductive ind in
  match Inductive.inductive_sort_family mip with
    | InProp -> error ("Morphism generation impossible: "^s^" has type Prop")
    | _ -> let morphism_cst = declare_morphism mphism ind s in
	   ignore (declare_fusion_theorem mphism ind morphism_cst s)
