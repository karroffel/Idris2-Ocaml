(* These types are made to match the Idris representation *)
module Types = struct
    type world = World

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

        external idris2_stdin_ : unit -> filep = "ml_idris2_stdin"
        let idris2_stdin : filep = idris2_stdin_ ()
        external idris2_stdout_ : unit -> filep = "ml_idris2_stdout"
        let idris2_stdout : filep = idris2_stdout_ ()
        external idris2_stderr_ : unit -> filep = "ml_idris2_stderr"
        let idris2_stderr : filep = idris2_stderr_ ()

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
        external idris2_setBufferDouble : 'buffer pointer -> int -> float -> unit = "ml_idris2_setBufferDouble"
        external idris2_setBufferString : 'buffer pointer -> int -> string -> unit = "ml_idris2_setBufferString"

        external idris2_copyBuffer : 'buffer pointer -> int -> int -> 'buffer pointer -> int -> unit = "ml_idris2_copyBuffer"

        external idris2_readBufferData : filep -> 'buffer pointer -> int -> int -> int = "ml_idris2_readBufferData"
        external idris2_writeBufferData : filep -> 'buffer pointer -> int -> int -> int = "ml_idris2_writeBufferData"

        external idris2_getBufferByte : 'buffer pointer -> int -> int = "ml_idris2_getBufferByte"
        external idris2_getBufferInt : 'buffer pointer -> int -> int = "ml_idris2_getBufferInt"
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
