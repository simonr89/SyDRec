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

(*i camlp4deps: "parsing/grammar.cma" i*)

(* Command registration *)

VERNAC COMMAND EXTEND Catamorphism
  | [ "Catamorphism" reference(r) ] ->
    [ Morphism_gen.declarations Morphism_gen.Cata r ]
END

VERNAC COMMAND EXTEND Paramorphism
  | [ "Paramorphism" reference(r) ] ->
    [ Morphism_gen.declarations Morphism_gen.Para r ]
END
