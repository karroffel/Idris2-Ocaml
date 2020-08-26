exception Idris2_Exception of string;;

(* int64 needs to always be boxed, should be a good enough for opaque types *)
type idr2_opaque = int64;;

let as_variant : 'a -> (int * idr2_opaque) = Obj.magic;;
let as_lazy : 'a -> idr2_opaque lazy_t = Obj.magic;;
let as_fun : 'a -> ('b -> 'c) = Obj.magic;;
let as_opaque : 'a -> idr2_opaque = Obj.magic;;
let as_ref : 'a -> idr2_opaque ref = Obj.magic;;
let as_array : 'a -> idr2_opaque array = Obj.magic;;

let as_erased : 'a -> unit = Obj.magic;;
let as_int : 'a -> int = Obj.magic;;
let as_bint : 'a -> Z.t = Obj.magic;;
let as_bits8 : 'a -> int = Obj.magic;;
let as_bits16 : 'a -> int = Obj.magic;;
let as_bits32 : 'a -> int = Obj.magic;;
let as_bits64 : 'a -> int64 = Obj.magic;;
let as_string : 'a -> string = Obj.magic;;
let as_char : 'a -> char = Obj.magic;;
let as_double : 'a -> float = Obj.magic;;
let as_world : 'a -> unit = Obj.magic;;

(* Used to give type hints for function return types *)

let hint_erased (x : unit) : unit = x;;
let hint_int (x : int) : int = x;;
let hint_bint (x : Z.t) : Z.t = x;;
let hint_bits8 (x : int) : int = x;;
let hint_bits16 (x : int) : int = x;;
let hint_bits32 (x : int) : int = x;;
let hint_bits64 (x : int64) : int64 = x;;
let hint_string (x : string) : string = x;;
let hint_char (x : char) : char = x;;
let hint_double (x : float) : float = x;;
let hint_world (x : unit) : unit = x;;
let hint_opaque (x : idr2_opaque) : idr2_opaque = x;;


(* Primitive functions *)

let ensure_bits8 (x : int) : int =
  let max = 1 lsl 8 in
  let x' = x mod max in
  if x' < 0
    then max + x'
    else x';;

let ensure_bits16 (x : int) : int =
  let max = 1 lsl 16 in
  let x' = x mod max in
  if x' < 0
    then max + x'
    else x';;

let ensure_bits32 (x : int) : int =
  let max = 1 lsl 32 in
  let x' = x mod max in
  if x' < 0
    then max + x'
    else x';;

(* TODO handle signedness and overflow *)
let cast_bint_int (x : Z.t) : int =
  let upper = Z.shift_left Z.one (Sys.int_size) in
  Z.to_int (Z.rem x upper);;

(* TODO handle signedness and overflow *)
let cast_bits64_int (x : int64) : int = Int64.to_int (Int64.unsigned_rem x (Int64.of_int (1 lsl 63)));;;;

let cast_int_bits8 (x : int) : int = ensure_bits8 x;;
let cast_bint_bits8 (x : Z.t) : int = ensure_bits8 (Z.to_int (Z.rem x (Z.of_int (1 lsl 8))));;
let cast_bits64_bits8 (x : int64) : int = ensure_bits8 (Int64.to_int (Int64.unsigned_rem x (Int64.of_int (1 lsl 8))));;

let cast_int_bits16 (x : int) : int = ensure_bits16 x;;
let cast_bint_bits16 (x : Z.t) : int = ensure_bits16 (Z.to_int (Z.rem x (Z.of_int (1 lsl 16))));;
let cast_bits64_bits16 (x : int64) : int = ensure_bits16 (Int64.to_int (Int64.unsigned_rem x (Int64.of_int (1 lsl 16))));;

let cast_int_bits32 (x : int) : int = ensure_bits32 x;;
let cast_bint_bits32 (x : Z.t) : int = ensure_bits32 (Z.to_int (Z.rem x (Z.of_int (1 lsl 32))));;
let cast_bits64_bits32 (x : int64) : int = ensure_bits32 (Int64.to_int (Int64.unsigned_rem x (Int64.of_int (1 lsl 32))));;

(* TODO this doesn't handle signed numbers yet *)
let cast_bint_bits64 (x : Z.t) : int64 =
  let upper_32 = Z.shift_left Z.one 32 in
  let upper_64 = Z.shift_left upper_32 32 in
  Z.to_int64 (Z.rem x upper_64);;


let int_of_bool (b : bool) : int = Bool.to_int b;;

let string_reverse (s : string) : string =
  let len = String.length s in
  String.init len (fun i -> s.[len - 1 - i]);;
let string_head (s : string) : char = s.[0];;
let string_tail (s : string) : string =
  let len = String.length s in
  String.sub s 1 (len - 1);;
let string_cons (c : char) (s : string) : string =
  String.init (String.length s + 1) (fun i -> if i == 0 then c else s.[i - 1]);;

let string_fast_concat (strings : idr2_opaque) : string =
  let rec s_foldl : 'a . 'a -> ('a -> string -> 'a) -> idr2_opaque -> 'a = fun acc f v -> (
        match as_variant v with
        | (0, _) -> acc
        | (1, fields') ->
            let (s, rest) : (string * idr2_opaque) = Obj.magic fields' in
            s_foldl (f acc s) f rest
  ) in
  let len = s_foldl 0 (fun acc s -> acc + String.length s) strings in
  let b = Bytes.create len in
  let _ = s_foldl (b, 0) (fun (buf, ofs) s -> 
      let s_len = String.length s in
      Bytes.blit_string s 0 buf ofs s_len;
      (buf, ofs + s_len)
  ) strings in
  Bytes.to_string b;;


(*
 * Generated code
 *)

let rec start_generated_code = ()

