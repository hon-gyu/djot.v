open Ast
open Datatypes
open FMapAVL
open InlineTable
open List0
open ListDef
open MSetAVL
open Nat0
open OrderedTypeEx
open OrdersEx
open Reparse
open Step
open Strings

module StrSet :
 sig
  module Raw :
   sig
    type elt = string

    type tree =
    | Leaf
    | Node of Int.Z_as_Int.t * tree * string * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : string -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : string list -> tree -> string list

    val elements : tree -> string list

    val rev_elements_aux : string list -> tree -> string list

    val rev_elements : tree -> string list

    val cardinal : tree -> int

    val maxdepth : tree -> int

    val mindepth : tree -> int

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      string -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> string -> tree -> bool

    val subsetr : (tree -> bool) -> string -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Int.Z_as_Int.t

    val singleton : string -> tree

    val create : t -> string -> t -> tree

    val assert_false : t -> string -> t -> tree

    val bal : t -> string -> t -> tree

    val add : string -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> t * elt

    val merge : tree -> tree -> tree

    val remove : string -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : string -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> t * t

    val ltb_tree : string -> tree -> bool

    val gtb_tree : string -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = string

          val compare : string -> string -> comparison

          val eq_dec : string -> string -> bool
         end

        module TO :
         sig
          type t = string

          val compare : string -> string -> comparison

          val eq_dec : string -> string -> bool
         end
       end

      val eq_dec : string -> string -> bool

      val lt_dec : string -> string -> bool

      val eqb : string -> string -> bool
     end

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = string

            val compare : string -> string -> comparison

            val eq_dec : string -> string -> bool
           end

          module TO :
           sig
            type t = string

            val compare : string -> string -> comparison

            val eq_dec : string -> string -> bool
           end
         end

        val eq_dec : string -> string -> bool

        val lt_dec : string -> string -> bool

        val eqb : string -> string -> bool
       end
     end

    val flatten_e : enumeration -> elt list
   end

  module E :
   sig
    type t = string

    val compare : string -> string -> comparison

    val eq_dec : string -> string -> bool
   end

  type elt = string

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> int

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val eq_dec : t -> t -> bool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option
 end

module StrMap :
 sig
  module E :
   sig
    type t = string

    val compare : string -> string -> string OrderedType.coq_Compare

    val eq_dec : string -> string -> bool
   end

  module Raw :
   sig
    type key = string

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Int.Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
      Int.Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
      Int.Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Int.Z_as_Int.t

    val cardinal : 'a1 tree -> int

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : string -> 'a1 tree -> bool

    val find : string -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : string -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : string -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

    val elements : 'a1 tree -> (key * 'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> string -> 'a1 -> ('a1 enumeration -> bool) ->
      'a1 enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = string
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : string -> string -> bool

        val lt_dec : string -> string -> bool

        val eqb : string -> string -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = string
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : string -> string -> bool

          val lt_dec : string -> string -> bool

          val eqb : string -> string -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = string
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : string -> string -> bool

          val lt_dec : string -> string -> bool

          val eqb : string -> string -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = string
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : string -> string -> bool

            val lt_dec : string -> string -> bool

            val eqb : string -> string -> bool
           end
         end

        type key = string

        type 'elt t = (string * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key * 'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key * 'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = string

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

val inline_text : inline -> string

val inlines_text : inlines -> string

val is_id_sep : char -> bool

val id_base : string -> string

val id_candidate : string -> int -> string

type id_state = { id_used : string list; id_refs : reference_map;
                  id_count : int; id_used_set : StrSet.t;
                  id_ref_labels : StrSet.t; id_next : int StrMap.t;
                  id_derived : string list }

val id_state_init : id_state

val take_id : string -> id_state -> id_state

val add_auto_ref : string -> string -> id_state -> id_state

val register_id : attr -> id_state -> id_state

val fresh_index : StrSet.t -> string -> int -> int -> int

val fresh_for : id_state -> string -> int

val assign_heading_id :
  pos -> attr -> int -> inlines -> id_state -> id_state * block node

module Ids :
 sig
  val of_block : block -> pos -> attr -> id_state -> id_state * block node

  val of_node : block node -> id_state -> id_state * block node

  val of_list : blocks -> id_state -> id_state * blocks
 end

type sect_state = ((int * attr) * blocks) list

val sect_init : sect_state

val section_node : coq_PosPolicy -> attr -> blocks -> block node

val close_ge : coq_PosPolicy -> int -> blocks -> sect_state -> sect_state

val close_all : coq_PosPolicy -> blocks -> sect_state -> sect_state

val sect_push : block node -> sect_state -> sect_state

val sect_step : coq_PosPolicy -> sect_state -> block node -> sect_state

val sect_bottom : sect_state -> blocks

val sectionize : coq_PosPolicy -> blocks -> blocks

val add_ref : pos -> attr -> block -> reference_map -> reference_map

module Refs :
 sig
  val of_block : block -> pos -> attr -> reference_map -> reference_map

  val of_list : blocks -> reference_map -> reference_map
 end

module Notes :
 sig
  val of_block : block -> note_map -> note_map

  val of_list : blocks -> note_map -> note_map
 end

val doc_pass : coq_PosPolicy -> blocks -> doc

val parse_doc : dtable -> bconfig -> coq_PosPolicy -> string -> doc

val parse_doc_located : dtable -> bconfig -> string -> doc
