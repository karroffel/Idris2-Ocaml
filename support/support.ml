exception Idris2_Exception of string;;

(* int64 needs to always be boxed, should be a good enough for opaque types *)
type idr2_opaque = int64;;

let as_fun : 'a -> ('b -> 'c) = Obj.magic;;
let as_opaque : 'a -> idr2_opaque = Obj.magic;;

let as_erased : 'a -> unit = Obj.magic;;
let as_int : 'a -> int = Obj.magic;;
let as_bint : 'a -> int64 = Obj.magic;;
let as_bits8 : 'a -> int32 = Obj.magic;;
let as_bits16 : 'a -> int32 = Obj.magic;;
let as_bits32 : 'a -> int32 = Obj.magic;;
let as_bits64 : 'a -> int64 = Obj.magic;;
let as_string : 'a -> string = Obj.magic;;
let as_char : 'a -> char = Obj.magic;;
let as_double : 'a -> float = Obj.magic;;
let as_world : 'a -> () = Obj.magic;;

(* Used to give type hints for function return types *)

let hint_erased (x : unit) : unit = x;;
let hint_int (x : int) : int = x;;
let hint_bint (x : int64) : int64 = x;;
let hint_bits8 (x : int32) : int32 = x;;
let hint_bits16 (x : int32) : int32 = x;;
let hint_bits32 (x : int32) : int32 = x;;
let hint_bits64 (x : int64) : int64 = x;;
let hint_string (x : string) : string = x;;
let hint_char (x : char) : char = x;;
let hint_double (x : float) : float = x;;
let hint_world (x : ()) : () = x;;
let hint_opaque (x : idr2_opaque) : idr2_opaque = x;;

let rec start_generated_code = ()

