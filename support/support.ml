exception Idris2_Exception of string;;

(* int64 needs to always be boxed, should be a good enough for opaque types *)
type idr2_opaque = int64;;

let as_variant : 'a -> (int * idr2_opaque) = Obj.magic;;
let as_lazy : 'a -> idr2_opaque lazy_t = Obj.magic;;
let as_fun : 'a -> ('b -> 'c) = Obj.magic;;
let as_opaque : 'a -> idr2_opaque = Obj.magic;;

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

let cast_bint_int (x : Z.t) : int = Z.to_int (Z.rem x (Z.of_int (1 lsl 63)));;;;
let cast_bits64_int (x : int64) : int = Int64.to_int (Int64.unsigned_rem x (Int64.of_int (1 lsl 63)));;;;

let cast_int_bits8 (x : int) : int = x mod (1 lsl 8);;
let cast_bint_bits8 (x : Z.t) : int = Z.to_int (Z.rem x (Z.of_int (1 lsl 8)));;
let cast_bits64_bits8 (x : int64) : int = Int64.to_int (Int64.unsigned_rem x (Int64.of_int (1 lsl 8)));;

let cast_int_bits16 (x : int) : int = x mod (1 lsl 16);;
let cast_bint_bits16 (x : Z.t) : int = Z.to_int (Z.rem x (Z.of_int (1 lsl 16)));;
let cast_bits64_bits16 (x : int64) : int = Int64.to_int (Int64.unsigned_rem x (Int64.of_int (1 lsl 16)));;

let cast_int_bits32 (x : int) : int = x mod (1 lsl 32);;
let cast_bint_bits32 (x : Z.t) : int = Z.to_int (Z.rem x (Z.of_int (1 lsl 32)));;
let cast_bits64_bits32 (x : int64) : int = Int64.to_int (Int64.unsigned_rem x (Int64.of_int (1 lsl 32)));;

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



let idr2_print_string (s : string) _ = print_string s; as_opaque ();;




let rec start_generated_code = ()

