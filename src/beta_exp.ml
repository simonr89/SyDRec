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

open Names     (* kernel/names.mli *)
open Pp        (* lib/pp.mli *)
open Term      (* kernel/term.mli *)
open Tacmach   (* proof/tacmach.mli *)
open Tacticals (* tactics/tacticals.mli *)
open Tactics   (* tactics/tactics.mli *)
open Termops   (* pretyping/termops.mli *)

(* References to Coq definitions. Laziness is used in case the
   relevant modules have not yet been required or compiled *)
let eq_ref = lazy (Coqlib.gen_constant "Beta" ["Init"; "Logic"] "eq")

let eq_ind_r_ref = lazy (Coqlib.gen_constant "Beta" ["Init"; "Logic"] "eq_ind_r")

let eq_refl_ref = lazy (Coqlib.gen_constant "Beta" ["Init"; "Logic"] "eq_refl")

(* Build the term corresponding to (fun x => x y = e) *)
let mkP gl y e =
  let id_x = pf_get_new_id (id_of_string "x") gl in
  let ty = pf_type_of gl y in
  let te = pf_type_of gl e in
  let lambda_body =
    mkApp (Lazy.force eq_ref, [|te; mkApp (mkVar id_x, [|y|]); e|])
  in
  mkNamedLambda id_x (mkArrow ty te) lambda_body

(* Build the abstraction (fun x => e[y := x]) *)
let mkLambdaH gl y e f =
  let id_x = pf_get_new_id (id_of_string "x") gl in
  mkNamedLambda id_x (pf_type_of gl y) (replace_term y (mkVar id_x) e)

(* Build the proof term (fun H => eq_ind_r P eq_refl H) *)
let pf_term gl f x e =
  let l = mkLambdaH gl x e f in
  let th = mkApp (Lazy.force eq_ref, [|pf_type_of gl f; f; l|]) in
  let p = mkP gl x e in
  let eq_refl = mkApp (Lazy.force eq_refl_ref, [|pf_type_of gl e; e|]) in
  let id_h = pf_get_new_id (id_of_string "H") gl in
  let pf_body =
    mkApp (Lazy.force eq_ind_r_ref, [|pf_type_of gl f; l; p; eq_refl; f; mkVar id_h|])
  in
  mkNamedLambda id_h th pf_body

(* Given a function symbol f and a list of its arguments x_1 ... x_n,
   this returns the term corresponding to the partial application
   f x_1 ... x_n-1 and the last argument x_n *)
let separate_last_arg f_symb f_args =
  let len = Array.length f_args in
  let last = f_args.(len - 1) in
  if len = 1
  then (f_symb, last)
  else (mkApp (f_symb, Array.sub f_args 0 (len - 1)), last)

let beta_tac gl =
  (* match only conclusion of the form f x = e *)
  let msg = "Goal does not have the required form: f x = e" in
  match kind_of_term (pf_concl gl) with
    | App (eq, [|_; lhs; rhs|]) when eq_constr eq (Lazy.force eq_ref) ->
      begin
	match kind_of_term lhs with
	  | App (f_symb, f_args) ->
	    let (f, x) = separate_last_arg f_symb f_args in
	  (* construct and apply proof term *)
	    apply (pf_term gl f x rhs) gl
	  | _ -> tclFAIL 0 (str msg) gl
      end
    | _ -> tclFAIL 0 (str msg) gl
