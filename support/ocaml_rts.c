#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <stdio.h>
#include <string.h>

#include <time.h>

#include "getline.h"
#include "idris_buffer.h"
#include "idris_directory.h"
#include "idris_file.h"
#include "idris_net.h"
#include "idris_support.h"
#include "idris_term.h"

#include "sys/stat.h"


/* FILE* as custom caml val */


CAMLprim value c_hello(value i) {
	CAMLparam0();
	const char * const msg = "hello from C!";
	printf("this is C; we received %d from OCaml\n", Int_val(i));
	CAMLreturn(caml_alloc_initialized_string(strlen(msg), msg));
}


// apparently this could be done using the OCaml Obj module from the stdlib
// but this is already written so let's keep it
void inspect_(int indent, value x) {
	for (int i = 0; i < indent; ++i) printf("  ");
	if (Is_block(x)) {
		switch (Tag_val(x)) {
			case Double_tag:
				printf("double: %f\n", Double_val(x));
				break;

			case String_tag:
				printf("string: %s\n", String_val(x));
				break;

			case Custom_tag:
				printf("custom tag\n");
				break;

			default:
				printf(
					"block(tag = %d, size = %d)\n",
					Tag_val(x),
					Wosize_val(x)
				);

				if (Tag_val(x) < 16) {
					// probably an ADT
					for (int i = 0; i < Wosize_val(x); ++i) {
						inspect_(indent+1, Field(x, i));
					}
				} else {
					for (int i = 0; i < indent+1; ++i) printf("  ");
					printf("(fields omitted because tag too high)\n");
				}
				break;
		}
	} else {
		printf("int %d\n", Int_val(x));
	}
}

// returns the number of bytes read
// 0 = malformed
static inline size_t utf8_read(const uint8_t * bytes, size_t length, uint32_t * out_cp)
{
	if (length < 1) {
		return 0;
	}

	if (bytes[0] < 0x80) {
		// one-byte representation
		*out_cp = (uint32_t) bytes[0];
		return 1;
	}

	if (bytes[0] < 0xC0) {
		// continuation bytes cannot appear here
		return 0;
	}

	if (bytes[0] < 0xE0) {
		// two-byte representation
		if (length < 2) {
			return 0;
		}

		if ((bytes[1] & 0xC0) != 0x80) {
			// malformed continuation byte: must be 0b10xx_xxxx
			return 0;
		}

		*out_cp =
			  ((uint32_t) (bytes[0] & 0x1F) << 6)
			|  (uint32_t) (bytes[1] & 0x3F)
			;
		return 2;
	}

	if (bytes[0] < 0xF0) {
		// three-byte representation
		if (length < 3) {
			return 0;
		}

		if (
			   (bytes[1] & 0xC0) != 0x80
			|| (bytes[2] & 0xC0) != 0x80
		) {
			// malformed continuation byte: must be 0b10xx_xxxx
			return 0;
		}

		*out_cp =
			  ((uint32_t) (bytes[0] & 0x0F) << 12)
			| ((uint32_t) (bytes[1] & 0x3F) <<  6)
			|  (uint32_t) (bytes[2] & 0x3F)
			;
		return 3;
	}

	if (bytes[0] < 0xF8) {
		// four-byte representation
		if (length < 4) {
			return 0;
		}

		if (
			   (bytes[1] & 0xC0) != 0x80
			|| (bytes[2] & 0xC0) != 0x80
			|| (bytes[3] & 0xC0) != 0x80
		) {
			// malformed continuation byte: must be 0b10xx_xxxx
			return 0;
		}

		*out_cp =
			  ((uint32_t) (bytes[0] & 0x07) << 18)
			| ((uint32_t) (bytes[1] & 0x3F) << 12)
			| ((uint32_t) (bytes[2] & 0x3F) <<  6)
			|  (uint32_t) (bytes[3] & 0x3F)
			;
		return 4;
	}

	return 0;
}

// zero = error
static inline size_t utf8_width(uint32_t cp)
{
	if (cp < 0x80) {
		return 1;
	}

	if (cp < 0x800) {
		return 2;
	}

	if (cp < 0x10000) {
		return 3;
	}

	if (cp < 0x110000) {
		return 4;
	}

	return 0;  // code too high
}

static inline void utf8_write(uint8_t * buf, size_t cp_width, uint32_t cp)
{
	switch (cp_width) {
		case 1:
			buf[0] = cp & 0x7F;
			break;

		case 2:
			buf[0] = ((cp >> 6) & 0x1F) | 0xC0;
			buf[1] = ( cp       & 0x3F) | 0x80;
			break;

		case 3:
			buf[0] = ((cp >> 12) & 0x0F) | 0xE0;
			buf[1] = ((cp >>  6) & 0x3F) | 0x80;
			buf[2] = ( cp        & 0x3F) | 0x80;
			break;

		case 4:
			buf[0] = ((cp >> 18) & 0x07) | 0xF0;
			buf[1] = ((cp >> 12) & 0x3F) | 0x80;
			buf[2] = ((cp >>  6) & 0x3F) | 0x80;
			buf[3] = ( cp        & 0x3F) | 0x80;
			break;

		default:
			caml_failwith("utf8_write: invalid code point width");
			break;
	}
}

CAMLprim value ml_string_readChar(value ofs, value src)
{
	CAMLparam2(ofs, src);
	CAMLlocal1(result);

	uint32_t cp;
	const size_t cp_width = utf8_read(
		Bytes_val(src) + Int_val(ofs),
		caml_string_length(src) - Int_val(ofs),
		&cp
	);

	if (cp_width == 0) {
		result = Val_int(0);  // EOF, int 0
	} else {
		result = caml_alloc(2, 1);  // Character, block tag 1
		Store_field(result, 0, Val_int(cp));
		Store_field(result, 1, Val_int(cp_width));
	}

	CAMLreturn(result);
}

CAMLprim value ml_string_reverse(value src)
{
	CAMLparam1(src);
	CAMLlocal1(dst);

	const size_t src_length = caml_string_length(src);
	dst = caml_alloc_string(src_length);

	// all allocations are done, now we're going to take (char *) pointers
	// don't do any allocations anymore because it may invalidate the pointers!

	const uint8_t * src_start = Bytes_val(src);
	const uint8_t * src_end = src_start + src_length;
	const uint8_t * srcp = src_start;

	uint8_t * dst_start = Bytes_val(dst);
	uint8_t * dst_end = dst_start + src_length;
	uint8_t * dstp = dst_end;

	size_t bytes_remaining = src_length;
	while (srcp < src_end && dstp > dst_start) {
		uint32_t cp;
		const size_t cp_width = utf8_read(srcp, bytes_remaining, &cp);
		if (cp_width == 0) {
			caml_failwith("ml_string_reverse: malformed utf8 input");
		}

		utf8_write(dstp-cp_width, cp_width, cp);

		bytes_remaining -= cp_width;
		srcp += cp_width;
		dstp -= cp_width;
	}

	if (srcp != src_end || dstp != dst_start) {
		caml_failwith("ml_string_reverse: desynchronised");
	}

	CAMLreturn(dst);
}

// will return the pointer to the NUL byte if out of bounds
const uint8_t * utf8_skip_chars(const uint8_t * buf, size_t buf_length, size_t n_chars)
{
	while (n_chars > 0 && buf_length > 0)
	{
		uint32_t cp;
		const size_t cp_width = utf8_read(buf, buf_length, &cp);
		if (cp_width == 0) {
			caml_failwith("utf8_skip_chars: out of bounds or malformed string");
		}

		buf += cp_width;
		buf_length -= cp_width;
		n_chars--;
	}

	return buf;
}

CAMLprim value ml_string_substring(value n_skip, value n_chars, value src)
{
	CAMLparam3(n_skip, n_chars, src);
	CAMLlocal1(dst);

	const uint8_t * src_start = Bytes_val(src);
	const uint8_t * src_end = src_start + caml_string_length(src);

	const uint8_t * substr_start = utf8_skip_chars(src_start, src_end - src_start, Int_val(n_skip));
	const uint8_t * substr_end   = utf8_skip_chars(substr_start, src_end - substr_start, Int_val(n_chars));
	const size_t subst_ofs = substr_start - src_start;
	const size_t substr_width = substr_end - substr_start;

	// here we allocate so pointers taken above are no longer valid
	// hence we need to take Bytes_val() again, and refer only to the length
	dst = caml_alloc_string(substr_end - substr_start);
	memcpy(Bytes_val(dst), Bytes_val(src) + subst_ofs, substr_width);

	CAMLreturn(dst);
}

CAMLprim value ml_string_cons(value cpv, value src)
{
	CAMLparam2(cpv, src);
	CAMLlocal1(dst);

	const size_t src_length = caml_string_length(src);
	const uint32_t cp = Int_val(cpv);
	const size_t cp_width = utf8_width(cp);

	dst = caml_alloc_string(cp_width + src_length);

	// we take the pointer after allocation so it's fine
	uint8_t * dstp = Bytes_val(dst);

	utf8_write(dstp, cp_width, cp);
	memcpy(dstp+cp_width, Bytes_val(src), src_length);

	CAMLreturn(dst);
}

CAMLprim value ml_string_length(value src)
{
	CAMLparam1(src);

	const uint8_t * srcp = Bytes_val(src);
	size_t bytes_remaining = caml_string_length(src);

	size_t n_chars = 0;
	while (bytes_remaining > 0)
	{
		uint32_t cp;
		size_t cp_width = utf8_read(srcp, bytes_remaining, &cp);
		if (cp_width == 0)
		{
			caml_failwith("ml_string_length: malformed string");
		}

		srcp += cp_width;
		bytes_remaining -= cp_width;
		n_chars += 1;
	}

	CAMLreturn(Val_int(n_chars));
}

CAMLprim value ml_string_head(value src)
{
	CAMLparam1(src);

	uint32_t cp;
	const size_t cp_width = utf8_read(Bytes_val(src), caml_string_length(src), &cp);
	if (cp_width == 0) {
		caml_failwith("ml_string_head: empty or malformed string");
	}

	CAMLreturn(Val_int(cp));
}

CAMLprim value ml_string_tail(value src)
{
	CAMLparam1(src);
	CAMLlocal1(dst);

	const uint8_t * srcp = Bytes_val(src);
	const size_t src_length = caml_string_length(src);

	uint32_t cp;
	const size_t cp_width = utf8_read(srcp, src_length, &cp);
	if (cp_width == 0) {
		caml_failwith("ml_string_tail: empty or malformed string");
	}

	// allocation invalidates srcp
	dst = caml_alloc_string(src_length - cp_width);

	memcpy(Bytes_val(dst), Bytes_val(src) + cp_width, src_length - cp_width);
	
	CAMLreturn(dst);
}

CAMLprim value ml_string_get(value src, value i)
{
	CAMLparam2(src, i);

	const uint8_t * src_start = Bytes_val(src);
	const uint8_t * src_end = src_start + caml_string_length(src);

	const uint8_t * p = utf8_skip_chars(src_start, src_end - src_start, Int_val(i));
	if (p == src_end)
	{
		caml_failwith("ml_string_get: index out of bounds");
	}
	
	uint32_t cp;
	const size_t cp_width = utf8_read(p, src_end - p, &cp);
	if (cp_width == 0)
	{
		caml_failwith("ml_string_get: out of bounds or malformed string");
	}

	CAMLreturn(Val_int(cp));
}

// useful for debugging UTF8, memory b0rkage and such
void sanity_check(const char * msg, value s)
{
	const uint8_t * p = Bytes_val(s);
	size_t bytes_remaining = caml_string_length(s);

	printf("validating: %s\n", p);
	printf("strlen = %d, caml_string_length = %d\n", strlen(p), bytes_remaining);
	printf("---------------------------------------------------\n");

	while (bytes_remaining > 0)
	{
		uint32_t cp;
		const size_t cp_width = utf8_read(p, bytes_remaining, &cp);
		if (cp_width == 0)
		{
			printf("%p: %s\n", p, p);
			printf("%s: sanity check failed\n", msg);
			*((int *) 0) = 0;  // segfault for gdb
			caml_failwith("sanity_check: malformed string");
		}

		p += cp_width;
		bytes_remaining -= cp_width;
	}
}

CAMLprim value ml_string_unpack(value src)
{
	CAMLparam1(src);
	CAMLlocal3(fst, prev, next);

	fst = Val_int(0);  // represents idris's Nil

	size_t ofs = 0;
	size_t bytes_remaining = caml_string_length(src);

	while (bytes_remaining > 0)
	{
		uint32_t cp;
		const size_t cp_width = utf8_read(Bytes_val(src) + ofs, bytes_remaining, &cp);
		if (cp_width == 0)
		{
			caml_failwith("ml_string_unpack: malformed string");
		}

		// special case for the first cell
		if (Is_long(fst)) {
			fst = caml_alloc(2, 1);  // idris's (::) has tag 1
			Store_field(fst, 0, Val_int(cp));
			Store_field(fst, 1, Val_int(0));  // points to Nil

			prev = fst;
		} else {
			next = caml_alloc(2, 1);
			Store_field(next, 0, Val_int(cp));
			Store_field(next, 1, Val_int(0));  // points to Nil

			Store_field(prev, 1, next);  // point prev->next to next
			prev = next;
		}

		bytes_remaining -= cp_width;
		ofs += cp_width;
	}

	CAMLreturn(fst);
}

CAMLprim value ml_string_pack(value cps)
{
	CAMLparam1(cps);
	CAMLlocal2(p, dst);

	// first pass: get the total number of bytes
	size_t total_width = 0;
	for (p = cps; Is_block(p); p = Field(p, 1))
	{
		const uint32_t cp = Int_val(Field(p, 0));
		const size_t cp_width = utf8_width(cp);
		if (cp_width == 0)
		{
			caml_failwith("ml_string_pack: code point out of range");
		}

		total_width += cp_width;
	}

	// second pass: encode the characters
	dst = caml_alloc_string(total_width);
	uint8_t * dstp = Bytes_val(dst);  // must come after the allocation
	for (p = cps; Is_block(p); p = Field(p, 1))
	{
		const uint32_t cp = Int_val(Field(p, 0));
		const size_t cp_width = utf8_width(cp);
		if (cp_width == 0)
		{
			caml_failwith("ml_string_pack: impossible: code point out of range despite previous check");
		}

		utf8_write(dstp, cp_width, cp);
		dstp += cp_width;
	}

	CAMLreturn(dst);
}

CAMLprim value ml_string_concat(value ss)
{
	CAMLparam1(ss);
	CAMLlocal3(p, s, dst);

	// first pass: get the total number of bytes
	size_t total_width = 0;
	for (p = ss; Is_block(p); p = Field(p, 1))
	{
		total_width += caml_string_length(Field(p, 0));
	}

	// second pass: copy the strings
	dst = caml_alloc_string(total_width);
	uint8_t * dstp = Bytes_val(dst);  // must come after the allocation
	for (p = ss; Is_block(p); p = Field(p, 1))
	{
		s = Field(p, 0);

		const uint8_t * srcp = Bytes_val(s);
		const size_t width = caml_string_length(s);

		memcpy(dstp, srcp, width);

		dstp += width;
	}

	CAMLreturn(dst);
}

CAMLprim value inspect(value ty, value x)
{
	CAMLparam2(ty, x);
	inspect_(0, x);
	CAMLreturn(Val_int(0));  // return unit
}

CAMLprim value ml_idris2_getStr(value unit)
{
	CAMLparam1(unit);
	CAMLlocal1(result);

	char * rptr = idris2_getStr();
	result = caml_copy_string(rptr);
	free(rptr);

	CAMLreturn(result);
}

CAMLprim value ml_idris2_getString(value sptr)
{
	CAMLparam1(sptr);
	// sptr represents Ptr String
	//
	// which is either 0L
	// or a caml string
	//
	// since we always need an is_Null check before calling this function
	// the former can never be the case
	CAMLreturn(sptr);
}

CAMLprim value ml_idris2_getEnvPair(value i)
{
	CAMLparam1(i);
	const char * result = idris2_getEnvPair(Int_val(i));
	CAMLreturn((value) result);
}

CAMLprim value ml_idris2_isNull(value ptr)
{
	CAMLparam1(ptr);
	const int result = idris2_isNull((void *) ptr);
	CAMLreturn(Val_int(result));
}




CAMLprim value ml_idris2_putStr(value s)
{
	CAMLparam1(s);
	idris2_putStr(String_val(s));
	CAMLreturn(Val_int(0));
}

CAMLprim value ml_idris2_openFile(value name, value mode) {
	CAMLparam2(name, mode);
	const FILE* result = idris2_openFile(String_val(name), String_val(mode));
	CAMLreturn((value) result);
}

CAMLprim value ml_idris2_closeFile(value file) {
  CAMLparam1(file);
  idris2_closeFile((FILE *) file);
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idris2_fileError(value file) {
  CAMLparam1(file);
  const int result = idris2_fileError((FILE *) file);
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_fileErrno(value unit)
{
	CAMLparam1(unit);
	const int result = idris2_fileErrno();
	CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_removeFile(value name) {
  CAMLparam1(name);
  const int result = idris2_removeFile(String_val(name));
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_fileSize(value file) {
  CAMLparam1(file);
  const int result = idris2_fileSize((FILE *) file);
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_fpoll(value file) {
  CAMLparam1(file);
  const int result = idris2_fpoll((FILE *) file);
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_readLine(value file) {
  CAMLparam1(file);
  CAMLlocal1(result);

  char * rptr = idris2_readLine((FILE *) file);
  result = rptr ? caml_copy_string(rptr) : 0;
  free(rptr);

  CAMLreturn(result);
}

CAMLprim value ml_idris2_readChars(value num, value file) {
  CAMLparam2(num, file);
  CAMLlocal1(result);

  char * rptr = idris2_readChars(Int_val(num), (FILE *) file);
  result = rptr ? caml_copy_string(rptr) : 0;
  free(rptr);

  CAMLreturn(result);
}

CAMLprim value ml_idris2_writeLine(value file, value str) {
  CAMLparam2(file, str);
  const int result = idris2_writeLine((FILE *) file, String_val(str));
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_eof(value file) {
  CAMLparam1(file);
  const int result = idris2_eof((FILE *)file);
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_fileAccessTime(value file) {
  CAMLparam1(file);
  const int result = idris2_fileAccessTime((FILE *)file);
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_fileModifiedTime(value file) {
  CAMLparam1(file);
  const int result = idris2_fileModifiedTime((FILE *)file);
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_fileStatusTime(value file) {
  CAMLparam1(file);
  const int result = idris2_fileStatusTime((FILE *)file);
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_stdin(value unit) {
  CAMLparam1(unit);
  FILE* result = idris2_stdin();
  CAMLreturn((value) result);
}

CAMLprim value ml_idris2_stdout(value unit) {
  CAMLparam1(unit);
  FILE* result = idris2_stdout();
  CAMLreturn((value) result);
}

CAMLprim value ml_idris2_stderr(value unit) {
  CAMLparam1(unit);
  FILE* result = idris2_stderr();
  CAMLreturn((value) result);
}

CAMLprim value ml_idris2_currentDirectory(value unit) {
  CAMLparam1(unit);
  CAMLlocal1(result);

  char * rptr = idris2_currentDirectory();
  result = rptr ? caml_copy_string(rptr) : 0;
  free(rptr);

  CAMLreturn(result);
}

CAMLprim value ml_idris2_changeDir(value dir) {
  CAMLparam1(dir);
  const int result = idris2_changeDir(String_val(dir));
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_createDir(value dir) {
  CAMLparam1(dir);
  const int result = idris2_createDir(String_val(dir));
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_openDir(value dir) {
  CAMLparam1(dir);
  const void *result = idris2_openDir(String_val(dir));
  CAMLreturn((value) result);
}

CAMLprim value ml_idris2_closeDir(value dirInfo) {
  CAMLparam1(dirInfo);
  idris2_closeDir((void *)dirInfo);
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idris2_removeDir(value dir) {
  CAMLparam1(dir);
  const int result = idris2_removeDir(String_val(dir));
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_nextDirEntry(value dirInfo) {
  CAMLparam1(dirInfo);
  CAMLlocal1(result);

  const char * rptr = idris2_nextDirEntry((void *)dirInfo);
  result = rptr ? caml_copy_string(rptr) : 0;
  // do NOT free rptr here

  CAMLreturn(result);
}

/*  libc stuff  */

CAMLprim value ml_getenv(value s)
{
	CAMLparam1(s);
	CAMLlocal1(result);

	const char * rptr = getenv(String_val(s));
	result = rptr ? caml_copy_string(rptr) : 0;
	// do NOT free rptr

	CAMLreturn(result);
}

CAMLprim value ml_system(value s)
{
	CAMLparam1(s);
	const int result = system(String_val(s));
	CAMLreturn(Val_int(result));
}

CAMLprim value ml_exit(value s)
{
	CAMLparam1(s);
	exit(Int_val(s));
	CAMLreturn(Val_int(0));
}

CAMLprim value ml_fflush(value file) {
  CAMLparam1(file);
  const int result = fflush((FILE *)file);
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_fdopen(value fd, value mode) {
  CAMLparam2(fd, mode);
  FILE * result = fdopen(Int_val(fd), String_val(mode));
  CAMLreturn((value) result);
}

CAMLprim value ml_chmod(value path, value mode) {
  CAMLparam2(path, mode);
  const int result = chmod(String_val(path), Int_val(mode));
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_putchar(value c) {
  CAMLparam1(c);
  const int result = putchar(Int_val(c));
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_getchar(value unit) {
  CAMLparam1(unit);
  const int result = getchar();
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_strlen(value str) {
  CAMLparam1(str);
  size_t len = strlen(String_val(str));
  CAMLreturn(Val_int(len));
}

CAMLprim value ml_fgetc(value fptr) {
  CAMLparam1(fptr);
  CAMLreturn(Val_int(fgetc((FILE *)fptr)));
}

/* buffer stuff */

CAMLprim value ml_idris2_newBuffer(value size) {
  CAMLparam1(size);
  CAMLlocal1(result);
  result = caml_alloc_string(Int_val(size));
  CAMLreturn(result);
}

CAMLprim value ml_idris2_freeBuffer(value buffer) {
  CAMLparam1(buffer);
  // nothing to do
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idris2_getBufferSize(value buffer) {
  CAMLparam1(buffer);
  const int result = caml_string_length(buffer);
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_setBufferByte(value buffer, value loc, value val) {
  CAMLparam3(buffer, loc, val);
  ((uint8_t *) Bytes_val(buffer))[Int_val(loc)] = (uint8_t) Int_val(val);
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idris2_setBufferInt(value buffer, value loc, value val) {
  CAMLparam3(buffer, loc, val);
  int64_t iv = Int_val(val);
  memcpy(Bytes_val(buffer) + Int_val(loc), &iv, sizeof(iv));
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idris2_setBufferBits8(value buffer, value loc, value val) {
  CAMLparam3(buffer, loc, val);
  int8_t iv = Int_val(val);
  memcpy(Bytes_val(buffer) + Int_val(loc), &iv, sizeof(iv));
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idris2_setBufferBits16(value buffer, value loc, value val) {
  CAMLparam3(buffer, loc, val);
  int16_t iv = Int_val(val);
  memcpy(Bytes_val(buffer) + Int_val(loc), &iv, sizeof(iv));
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idris2_setBufferBits32(value buffer, value loc, value val) {
  CAMLparam3(buffer, loc, val);
  int32_t iv = Int_val(val);
  memcpy(Bytes_val(buffer) + Int_val(loc), &iv, sizeof(iv));
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idris2_setBufferBits64(value buffer, value loc, value val) {
  CAMLparam3(buffer, loc, val);
  int64_t iv = Int64_val(val);
  memcpy(Bytes_val(buffer) + Int_val(loc), &iv, sizeof(iv));
  CAMLreturn(Val_int(0));
}


CAMLprim value ml_idris2_setBufferDouble(value buffer, value loc, value val) {
  CAMLparam3(buffer, loc, val);
  double dv = Double_val(val);
  memcpy(Bytes_val(buffer) + Int_val(loc), &dv, sizeof(dv));
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idris2_setBufferString(value buffer, value loc, value val) {
  CAMLparam3(buffer, loc, val);
  memcpy(Bytes_val(buffer) + Int_val(loc), String_val(val), strlen(String_val(val)));
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idris2_copyBuffer(value from, value start, value len, value to, value loc) {
  CAMLparam5(from,start,len,to,loc);
  memcpy(Bytes_val(to) + Int_val(loc), Bytes_val(from) + Int_val(start), Int_val(len));
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idris2_readBufferData(value file, value buffer, value loc, value max) {
	CAMLparam4(file, buffer, loc, max);
	const size_t result = fread(Bytes_val(buffer) + Int_val(loc), 1, Int_val(max), (FILE *) file);
	CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_writeBufferData(value file, value buffer, value loc, value len) {
	CAMLparam4(file, buffer, loc, len);
	const size_t result = fwrite(Bytes_val(buffer) + Int_val(loc), 1, Int_val(len), (FILE *) file);
	CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_getBufferByte(value buffer, value loc) {
  CAMLparam2(buffer, loc);
  const uint8_t result = ((uint8_t *) Bytes_val(buffer))[Int_val(loc)];
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_getBufferInt(value buffer, value loc) {
  CAMLparam2(buffer, loc);
  int64_t iv;
  memcpy(&iv, Bytes_val(buffer) + Int_val(loc), sizeof(iv));
  CAMLreturn(Val_int(iv));
}

CAMLprim value ml_idris2_getBufferBits8(value buffer, value loc) {
  CAMLparam2(buffer, loc);
  int8_t iv;
  memcpy(&iv, Bytes_val(buffer) + Int_val(loc), sizeof(iv));
  CAMLreturn(Val_int(iv));
}

CAMLprim value ml_idris2_getBufferBits16(value buffer, value loc) {
  CAMLparam2(buffer, loc);
  int16_t iv;
  memcpy(&iv, Bytes_val(buffer) + Int_val(loc), sizeof(iv));
  CAMLreturn(Val_int(iv));
}

CAMLprim value ml_idris2_getBufferBits32(value buffer, value loc) {
  CAMLparam2(buffer, loc);
  int32_t iv;
  memcpy(&iv, Bytes_val(buffer) + Int_val(loc), sizeof(iv));
  CAMLreturn(Val_int(iv));
}

CAMLprim value ml_idris2_getBufferBits64(value buffer, value loc) {
  CAMLparam2(buffer, loc);
  int64_t iv;
  memcpy(&iv, Bytes_val(buffer) + Int_val(loc), sizeof(iv));
  CAMLreturn(caml_copy_int64(iv));
}

CAMLprim value ml_idris2_getBufferDouble(value buffer, value loc) {
  CAMLparam2(buffer, loc);
  CAMLlocal1(result);

  double dv;
  memcpy(&dv, Bytes_val(buffer) + Int_val(loc), sizeof(dv));
  result = caml_copy_double(dv);

  CAMLreturn(result);
}

CAMLprim value ml_idris2_getBufferString(value src, value ofs, value max_width) {
  CAMLparam3(src, ofs, max_width);
  CAMLlocal1(dst);

  // idris2_getBufferString uses strncpy so we have to find where the NUL terminator is
  const size_t nbytes = strnlen(Bytes_val(src) + Int_val(ofs), Int_val(max_width));
  dst = caml_alloc_string(nbytes);  // ocaml null-terminates all strings
  memcpy(Bytes_val(dst), Bytes_val(src) + Int_val(ofs), nbytes);

  CAMLreturn(dst);
}

/* Idrnet */

CAMLprim value ml_idrnet_malloc(value size) {
  CAMLparam1(size);
  void * result = idrnet_malloc(Val_int(size));
  CAMLreturn((value) result);
}

CAMLprim value ml_idrnet_free(value buffer) {
  CAMLparam1(buffer);
  idrnet_free((void *) buffer);
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idrnet_peek(value buffer, value loc) {
  CAMLparam2(buffer, loc);
  // TODO
  CAMLreturn(Val_int(0));
}
CAMLprim value ml_idrnet_poke(value buffer, value loc, value val) {
  CAMLparam3(buffer, loc, val);
  // TODO
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idrnet_errno() {
  CAMLparam0();

  const int errno = idrnet_errno();

  CAMLreturn(Val_int(errno));
}

CAMLprim value ml_idrnet_socket(value domain, value type, value protocol) {
  CAMLparam3(domain, type, protocol);
  // TODO
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idrnet_bind(value sockfd, value family, value socket_type, value host, value port) {
  CAMLparam5(sockfd, family, socket_type, host, port);
  // TODO
  CAMLreturn(Val_int(0));
}

CAMLprim value ml_idrnet_getsockname(value sockfd, value address, value len) {
  CAMLparam3(sockfd, address, len);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_connect(value sockfd, value family, value socket_type, value host, value port) {
  CAMLparam5(sockfd, family, socket_type, host, port);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_sockaddr_family(value sockaddr) {
  CAMLparam1(sockaddr);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_sockaddr_ipv4(value sockaddr) {
  CAMLparam1(sockaddr);
  value result = Val_int(0);
  CAMLreturn(result);
}
CAMLprim value ml_idrnet_sockaddr_ipv4_port(value sockaddr) {
  CAMLparam1(sockaddr);
  value result = Val_int(0);
  CAMLreturn(result);
}
CAMLprim value ml_idrnet_create_sockaddr() {
  CAMLparam0();
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_accept(value sockaddr) {
  CAMLparam1(sockaddr);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_send(value sockfd, value data) {
  CAMLparam2(sockfd, data);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_send_buf(value sockfd, value data, value len) {
  CAMLparam3(sockfd, data, len);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_recv(value sockfd, value len) {
  CAMLparam2(sockfd, len);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_recv_buf(value sockfd, value buf, value len) {
  CAMLparam3(sockfd, buf, len);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_sendto(value sockfd, value data, value host, value port, value family) {
  CAMLparam5(sockfd, data, host, port, family);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_sendto_buf_native(value sockfd, value buf, value len, value host, value port, value family) {
  CAMLparam5(sockfd, buf, len, host, port);
  CAMLxparam1(family);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_sendto_buf_bytecode(value * argv, int argn ) {
  // TODO: Assert argn == 6?
  return ml_idrnet_sendto_buf_native(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

CAMLprim value ml_idrnet_recvfrom(value sockfd, value len) {
  CAMLparam2(sockfd, len);
  value result = Val_int(0);
  CAMLreturn(result);
}
CAMLprim value ml_idrnet_recvfrom_buf(value sockfd, value buf, value len) {
  CAMLparam3(sockfd, buf, len);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_get_recv_res(value res_struct) {
  CAMLparam1(res_struct);
  value result = Val_int(0);
  CAMLreturn(result);
}
CAMLprim value ml_idrnet_get_recv_payload(value res_struct) {
  CAMLparam1(res_struct);
  value result = Val_int(0);
  CAMLreturn(result);
}
CAMLprim value ml_idrnet_free_recv_struct(value res_struct) {
  CAMLparam1(res_struct);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_get_recvfrom_res(value res_struct) {
  CAMLparam1(res_struct);
  value result = Val_int(0);
  CAMLreturn(result);
}
CAMLprim value ml_idrnet_get_recvfrom_payload(value res_struct) {
  CAMLparam1(res_struct);
  value result = Val_int(0);
  CAMLreturn(result);
}
CAMLprim value ml_idrnet_get_recvfrom_sockaddr(value res_struct) {
  CAMLparam1(res_struct);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_free_recvfrom_struct(value res_struct) {
  CAMLparam1(res_struct);
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idrnet_geteagain() {
  CAMLparam0();
  value result = Val_int(0);
  CAMLreturn(result);
}

CAMLprim value ml_idris2_listen(value socket, value backlog) {
  CAMLparam2(socket, backlog);
  const int result = listen(socket, backlog);
  CAMLreturn(Val_int(result));
}

CAMLprim value ml_idris2_setupTerm(value world) {
	CAMLparam1(world);
	idris2_setupTerm();
	CAMLreturn(Val_int(0));  // unit
}

CAMLprim value ml_idris2_getTermCols(value world) {
	CAMLparam1(world);
	int ncols = idris2_getTermCols();
	CAMLreturn(Val_int(ncols));
}

CAMLprim value ml_idris2_getTermLines(value world) {
	CAMLparam1(world);
	int nlines = idris2_getTermLines();
	CAMLreturn(Val_int(nlines));
}

// external clocktime_gc_cpu : world -> os_clock = "ml_clocktime_gc_cpu"

CAMLprim value ml_clocktime_gc_cpu(value world) {
	CAMLparam1(world);
	CAMLreturn((value) NULL);
}

// external clocktime_gc_real : world -> os_clock = "ml_clocktime_gc_real"
    
CAMLprim value ml_clocktime_gc_real(value world) {
	CAMLparam1(world);
	CAMLreturn((value) NULL);
}

// external clocktime_monotonic : world -> os_clock = "ml_clocktime_monotonic"
    
CAMLprim value ml_clocktime_monotonic(value world) {
	CAMLparam1(world);
	struct timespec ts = {};
	int res = clock_gettime(CLOCK_MONOTONIC, &ts);
	if (res < 0) {
		CAMLreturn((value) NULL);
	}
	
	CAMLlocal1(result);
	result = caml_alloc_string(Int_val(sizeof(ts)));
	
	memcpy(Bytes_val(result), &ts, sizeof(ts));
	
	CAMLreturn(result);
}

// external clocktime_process : world -> os_clock = "ml_clocktime_process"

CAMLprim value ml_clocktime_process(value world) {
	CAMLparam1(world);
	struct timespec ts = {};
	int res = clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts);
	if (res < 0) {
		CAMLreturn((value) NULL);
	}
	
	CAMLlocal1(result);
	result = caml_alloc_string(Int_val(sizeof(ts)));
	
	memcpy(Bytes_val(result), &ts, sizeof(ts));
	
	CAMLreturn(result);
}

// external clocktime_thread : world -> os_clock = "ml_clocktime_thread"
    
CAMLprim value ml_clocktime_thread(value world) {
	CAMLparam1(world);
	struct timespec ts = {};
	int res = clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts);
	if (res < 0) {
		CAMLreturn((value) NULL);
	}
	
	CAMLlocal1(result);
	result = caml_alloc_string(Int_val(sizeof(ts)));
	
	memcpy(Bytes_val(result), &ts, sizeof(ts));
	
	CAMLreturn(result);
}


// external clocktime_utc : world -> os_clock = "ml_clocktime_utc"

CAMLprim value ml_clocktime_utc(value world) {
	CAMLparam1(world);
	time_t sec = time(NULL);
	if ((long) sec == 0) {
		CAMLreturn((value) NULL);
	}
	
	struct timespec ts = {};
	ts.tv_sec = sec;
	ts.tv_nsec = 0;
	
	CAMLlocal1(result);
	result = caml_alloc_string(Int_val(sizeof(ts)));
	
	memcpy(Bytes_val(result), &ts, sizeof(ts));
	
	CAMLreturn(result);
}

// external os_clock_nanosecond : os_clock -> world -> int64 = "ml_os_clock_nanosecond"

CAMLprim value ml_os_clock_nanosecond(value clock) {
	CAMLparam1(clock);
	
	if ((void *) clock == NULL) {
		CAMLreturn(caml_copy_int64(0));
	}
	
	struct timespec ts = {};
	
	memcpy(&ts, Bytes_val(clock), sizeof(ts));
	
	CAMLreturn(caml_copy_int64(ts.tv_nsec));
}

// external os_clock_second : os_clock -> world -> int64 = "ml_os_clock_second"

CAMLprim value ml_os_clock_second(value clock) {
	CAMLparam1(clock);
	
	if ((void *) clock == NULL) {
		CAMLreturn(caml_copy_int64(0));
	}
	
	struct timespec ts = {};
	
	memcpy(&ts, Bytes_val(clock), sizeof(ts));
	
	CAMLreturn(caml_copy_int64(ts.tv_sec));
}
    
// external os_clock_valid : os_clock -> world -> int = "ml_os_clock_valid"

CAMLprim value ml_os_clock_valid(value clock) {
	CAMLparam1(clock);
	
	if ((void *) clock == NULL) {
		CAMLreturn(Val_int(0));
	} else {
		CAMLreturn(Val_int(1));
	}
}
