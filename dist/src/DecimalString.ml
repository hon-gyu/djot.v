open Decimal

module NilEmpty =
 struct
  (** val string_of_uint : uint -> string **)

  let rec string_of_uint = function
  | Nil -> ""
  | D0 d0 ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      ('0', (string_of_uint d0))
  | D1 d0 ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      ('1', (string_of_uint d0))
  | D2 d0 ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      ('2', (string_of_uint d0))
  | D3 d0 ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      ('3', (string_of_uint d0))
  | D4 d0 ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      ('4', (string_of_uint d0))
  | D5 d0 ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      ('5', (string_of_uint d0))
  | D6 d0 ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      ('6', (string_of_uint d0))
  | D7 d0 ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      ('7', (string_of_uint d0))
  | D8 d0 ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      ('8', (string_of_uint d0))
  | D9 d0 ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      ('9', (string_of_uint d0))
 end

module NilZero =
 struct
  (** val string_of_uint : uint -> string **)

  let string_of_uint d = match d with
  | Nil -> "0"
  | _ -> NilEmpty.string_of_uint d
 end
