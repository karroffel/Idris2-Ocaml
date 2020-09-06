exception Idris2_Exception of string;;

type idr2_char = char;; (* is actually just a byte? Not enough for code points *)

let as_lazy : Obj.t -> Obj.t lazy_t = Obj.obj;;
let as_fun : Obj.t -> (Obj.t -> Obj.t) = Obj.obj;;
let as_ref : Obj.t -> Obj.t ref = Obj.obj;;
let as_array : Obj.t -> Obj.t array = Obj.obj;;

let as_erased (x : Obj.t) : unit = ();;
let as_int : Obj.t -> int = Obj.obj;;
let as_bint : Obj.t -> Z.t = Obj.obj;;
let as_bits8 : Obj.t -> int = Obj.obj;;
let as_bits16 : Obj.t -> int = Obj.obj;;
let as_bits32 : Obj.t -> int = Obj.obj;;
let as_bits64 : Obj.t -> int64 = Obj.obj;;
let as_string : Obj.t -> string = Obj.obj;;
let as_char : Obj.t -> idr2_char = Obj.obj;;
let as_double : Obj.t -> float = Obj.obj;;
let as_world (x : Obj.t) : unit = ();;


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

let get_tag (o : Obj.t) : int =
  if Obj.is_int o
    then Obj.obj o
    else Obj.tag o;;



(* These types are made to match the Idris representation *)
module Types = struct
    type world = World
    type os_clock

    module IdrisList = struct
        type 'a idris_list =
            | Nil                         (* int 0 *)
            | UNUSED of int               (* block, tag 0 *)
            | Cons of 'a * 'a idris_list  (* block, tag 1 *)

        let rec of_list = function
            | [] -> Nil
            | x :: xs -> Cons (x, of_list xs)

        let rec to_list = function
            | Nil -> []
            | UNUSED _ -> failwith "UNUSED tag in idris list"
            | Cons (x, xs) -> x :: to_list xs

        let rec foldl f z = function
            | Nil -> z
            | UNUSED _ -> failwith "UNUSED tag in idris list"
            | Cons (x, xs) -> foldl f (f z x) xs
    end

end
open Types
open Types.IdrisList

let not_implemented msg = failwith ("not implemented yet: " ^ msg)

module Debug = struct
    (* %foreign "ML:Rts.Debug.inspect"
     * prim__inspect : {a : Type} -> (x : a) -> (1 w : %World) -> IORes ()
     *
     * inspect : a -> IO ()
     * inspect x = primIO (prim__inspect x)
     *)
    external inspect : 'ty -> 'a -> unit = "inspect"
end

module IORef = struct
    let write (r : 'a ref) (x : 'a) : unit = r := x
end

module System = struct
    let get_args (_ : world) : string idris_list =
        IdrisList.of_list (Array.to_list Sys.argv)

    let fork_thread (sub : world -> unit) : Thread.t =
        Thread.create sub World

    let os_name (_ : world) : string =
        match Sys.os_type with
        | "Unix" -> "unix"
        | "Win32" -> "windows"
        | "Cygwin" -> "windows"
        | _ -> "unknown"
    
    external clocktime_gc_cpu : world -> os_clock = "ml_clocktime_gc_cpu"
    external clocktime_gc_real : world -> os_clock = "ml_clocktime_gc_real"
    external clocktime_monotonic : world -> os_clock = "ml_clocktime_monotonic"
    external clocktime_process : world -> os_clock = "ml_clocktime_process"
    external clocktime_thread : world -> os_clock = "ml_clocktime_thread"
    external clocktime_utc : world -> os_clock = "ml_clocktime_utc"
    external os_clock_nanosecond : os_clock -> int64 = "ml_os_clock_nanosecond"
    external os_clock_second : os_clock -> int64 = "ml_os_clock_second"
    external os_clock_valid : os_clock -> int = "ml_os_clock_valid"
end

module String = struct
    external reverse : string -> string = "ml_string_reverse"
    external substring : int -> int -> string -> string = "ml_string_substring"
    external cons : char -> string -> string = "ml_string_cons"
    external length : string -> int = "ml_string_length"
    external head : string -> char = "ml_string_head"
    external tail : string -> string = "ml_string_tail"
    external get : string -> int -> char = "ml_string_get"
    external unpack : string -> char idris_list = "ml_string_unpack"
    external pack : char idris_list -> string = "ml_string_pack"

    type char_result
    external readChar : int -> string -> char_result = "ml_string_readChar"

    let of_char (c : char) : string = String.make 1 c
end

module Bytes = struct
    (* pre-allocate a big buffer once and copy all strings in it *)
    external concat : string idris_list -> string = "ml_string_concat"

    (* implemented in C for easier debugging
    let concat (ssi : bytes idris_list) : bytes =
        let ss = IdrisList.to_list ssi in
        let total_length = List.fold_left (fun l s -> l + Bytes.length s) 0 ss in
        let result = Bytes.create total_length in
        let rec write_strings (ofs : int) = function
            | IdrisList.Nil -> ()
            | IdrisList.UNUSED _ -> failwith "UNUSED"
            | IdrisList.Cons (src, rest) ->
                let len = Bytes.length src in
                Bytes.blit src 0 result ofs len;
                write_strings (ofs+len) rest
          in
        write_strings 0 ssi;
        result
    *)

    let append (x : bytes) (y : bytes) : bytes =
        let xlen = Bytes.length x in
        let ylen = Bytes.length y in
        let result = Bytes.create (xlen + ylen) in
        Bytes.blit x 0 result 0 xlen;
        Bytes.blit y 0 result xlen ylen;
        result
end

module C = struct
    type 'a pointer
(*    type 'file file_pointer *)
    type filep

    module Lib_libidris2_support = struct
        external idris2_putStr : string -> unit = "ml_idris2_putStr"
        external idris2_isNull : 'a pointer -> bool = "ml_idris2_isNull"
        external idris2_getString : string pointer -> string = "ml_idris2_getString"
        external idris2_getStr : world -> string = "ml_idris2_getStr"
        external idris2_getEnvPair : int -> string pointer = "ml_idris2_getEnvPair"

        (* idris_file.h *)
        external idris2_openFile : string -> string -> filep = "ml_idris2_openFile"
        external idris2_closeFile : filep -> unit = "ml_idris2_closeFile"
        external idris2_fileError : filep -> int = "ml_idris2_fileError"

        external idris2_fileErrno : world -> int = "ml_idris2_fileErrno"

        external idris2_removeFile : string -> int = "ml_idris2_removeFile"
        external idris2_fileSize : filep -> int = "ml_idris2_fileSize"

        external idris2_fpoll : filep -> int = "ml_idris2_fpoll"

        external idris2_readLine : filep -> string pointer = "ml_idris2_readLine"
        external idris2_readChars : int -> filep -> string pointer = "ml_idris2_readChars"

        external idris2_writeLine : filep -> string -> int = "ml_idris2_writeLine"

        external idris2_eof : filep -> int = "ml_idris2_eof"
        external idris2_fileAccessTime : filep -> int = "ml_idris2_fileAccessTime"
        external idris2_fileModifiedTime : filep -> int = "ml_idris2_fileModifiedTime"
        external idris2_fileStatusTime : filep -> int = "ml_idris2_fileStatusTime"

        external idris2_stdin : unit -> filep = "ml_idris2_stdin"
        external idris2_stdout : unit -> filep = "ml_idris2_stdout"
        external idris2_stderr : unit -> filep = "ml_idris2_stderr"

        (* idris_directory.h *)
        external idris2_currentDirectory : world -> string = "ml_idris2_currentDirectory"
        external idris2_changeDir : string -> int = "ml_idris2_changeDir"
        external idris2_createDir : string -> int = "ml_idris2_createDir"
        external idris2_openDir : string -> 'a pointer = "ml_idris2_openDir"
        external idris2_closeDir : 'a pointer -> unit = "ml_idris2_closeDir"
        external idris2_removeDir : string -> int = "ml_idris2_removeDir"
        external idris2_nextDirEntry : 'a pointer -> string = "ml_idris2_nextDirEntry"

        (* idris_buffer.h *)
        external idris2_newBuffer : int -> 'buffer pointer = "ml_idris2_newBuffer"
        external idris2_freeBuffer : 'buffer pointer -> unit = "ml_idris2_freeBuffer"
        external idris2_getBufferSize : 'buffer pointer -> int = "ml_idris2_getBufferSize"

        external idris2_setBufferByte : 'buffer pointer -> int -> int -> unit = "ml_idris2_setBufferByte"
        external idris2_setBufferInt : 'buffer pointer -> int -> int -> unit = "ml_idris2_setBufferInt"
        external idris2_setBufferBits8 : 'buffer pointer -> int -> int -> unit = "ml_idris2_setBufferBits8"
        external idris2_setBufferBits16 : 'buffer pointer -> int -> int -> unit = "ml_idris2_setBufferBits16"
        external idris2_setBufferBits32 : 'buffer pointer -> int -> int -> unit = "ml_idris2_setBufferBits32"
        external idris2_setBufferBits64 : 'buffer pointer -> int -> int64 -> unit = "ml_idris2_setBufferBits64"
        external idris2_setBufferDouble : 'buffer pointer -> int -> float -> unit = "ml_idris2_setBufferDouble"
        external idris2_setBufferString : 'buffer pointer -> int -> string -> unit = "ml_idris2_setBufferString"

        external idris2_copyBuffer : 'buffer pointer -> int -> int -> 'buffer pointer -> int -> unit = "ml_idris2_copyBuffer"

        external idris2_readBufferData : filep -> 'buffer pointer -> int -> int -> int = "ml_idris2_readBufferData"
        external idris2_writeBufferData : filep -> 'buffer pointer -> int -> int -> int = "ml_idris2_writeBufferData"

        external idris2_getBufferByte : 'buffer pointer -> int -> int = "ml_idris2_getBufferByte"
        external idris2_getBufferInt : 'buffer pointer -> int -> int = "ml_idris2_getBufferInt"
        external idris2_getBufferBits8 : 'buffer pointer -> int -> int = "ml_idris2_getBufferBits8"
        external idris2_getBufferBits16 : 'buffer pointer -> int -> int = "ml_idris2_getBufferBits16"
        external idris2_getBufferBits32 : 'buffer pointer -> int -> int = "ml_idris2_getBufferBits32"
        external idris2_getBufferBits64 : 'buffer pointer -> int -> int64 = "ml_idris2_getBufferBits64"
        external idris2_getBufferDouble : 'buffer pointer -> int -> float = "ml_idris2_getBufferDouble"
        external idris2_getBufferString : 'buffer pointer -> int -> int -> string = "ml_idris2_getBufferString"

        (* idris_net *)
        (* FIXME: this should work with buffers *)
        external idrnet_malloc : int -> 'buffer pointer = "ml_idrnet_malloc"
        external idrnet_free : 'buffer pointer -> unit = "ml_idrnet_free"
        external idrnet_peek : 'buffer pointer -> int -> int = "ml_idrnet_peek"
        external idrnet_poke : 'buffer pointer -> int -> int = "ml_idrnet_poke"

        external idrnet_errno : world -> int = "ml_idrnet_errno"

        external idrnet_socket : int -> int -> int -> int = "ml_idrnet_socket"

        external idrnet_bind : int -> int -> int -> string -> int -> int = "ml_idrnet_bind"

        external idrnet_getsockname : int -> 'address pointer -> 'address pointer -> int = "ml_idrnet_getsockname"
        external idrnet_connect : int -> int -> int -> string -> int = "ml_idrnet_connect"

        external idrnet_sockaddr_family : 'sockaddr pointer -> int = "ml_idrnet_sockaddr_family"
        external idrnet_sockaddr_ipv4 : 'sockaddr pointer -> string = "ml_idrnet_sockaddr_ipv4"
        external idrnet_sockaddr_ipv4_port : 'sockaddr pointer -> int = "ml_idrnet_sockaddr_ipv4_port"
        external idrnet_create_sockaddr : world -> 'sockaddr pointer = "ml_idrnet_create_sockaddr"

        external idrnet_accept : int -> 'sockaddr pointer -> int = "ml_idrnet_accept"

        external idrnet_send : int -> string -> int = "ml_idrnet_send"
        external idrnet_send_buf : int -> 'buffer pointer -> int -> int = "ml_idrnet_send_buf"

        external idrnet_recv : int -> int -> 'buffer pointer = "ml_idrnet_recv"
        external idrnet_recv_buf : int -> 'buffer pointer -> int -> int = "ml_idrnet_recv_buf"

        external idrnet_sendto : int -> string -> string -> int -> int -> int = "ml_idrnet_sendto"
        external idrnet_sendto_buf : int -> 'buffer pointer -> int -> string -> int -> int -> int = "ml_idrnet_sendto_buf_bytecode" "ml_idrnet_sendto_buf_native"

        external idrnet_recvfrom : int -> int -> 'buffer pointer = "ml_idrnet_recvfrom"
        external idrnet_recvfrom_buf : int -> 'buffer pointer -> int -> 'buffer pointer = "ml_idrnet_recvfrom"

        external idrnet_get_recv_res : 'result pointer -> int = "ml_idrnet_get_recv_res"
        external idrnet_get_recv_payload : 'result pointer -> string = "ml_idrnet_get_recv_payload"
        external idrnet_free_recv_struct : 'result pointer -> unit = "ml_idrnet_free_recv_struct"

        external idrnet_get_recvfrom_res : 'result pointer -> int = "ml_idrnet_get_recvfrom_res"
        external idrnet_get_recvfrom_payload : 'result pointer -> string = "ml_idrnet_get_recvfrom_payload"
        external idrnet_get_recvfrom_sockaddr : 'result pointer -> 'buffer pointer = "ml_idrnet_get_recvfrom_sockaddr"
        external idrnet_free_recvfrom_struct : 'result pointer -> unit = "ml_idrnet_free_recvfrom_struct"

        external idrnet_geteagain : world -> int = "ml_idrnet_geteagain"

        (* idris2_term.h *)
        external idris2_setupTerm : world -> unit = "ml_idris2_setupTerm"
        external idris2_getTermCols : world -> int = "ml_idris2_getTermCols"
        external idris2_getTermLines : world -> int = "ml_idris2_getTermLines"

    end

    module Lib_libc6 = struct

        external getenv : string -> string pointer = "ml_getenv"
        external system : string -> int = "ml_system"
        external exit : int -> unit = "ml_exit"
        external fflush : filep -> int = "ml_fflush"
        external fdopen : int -> string -> filep = "ml_fdopen"
        external chmod : string -> int -> int = "ml_chmod"

        external putchar : char -> int = "ml_putchar"
        external getchar : world -> int = "ml_getchar"
        external strlen : string -> int = "ml_strlen"

        external fgetc : filep -> int = "ml_fgetc"
        external listen : int -> int -> int = "ml_idris2_listen"
    end
end
