#ifndef ANNOTATIONS_H_
#define ANNOTATIONS_H_


/*@
pred_prim strbuf<hd,size,sl:int,zeroflag:bool>
	inv hd != null // hd is non-null root ptr
	& hd <= self <= hd+bsize // can self point from hd to at most "0" position
//	& (zeroflag & 0 <= sl < size) // string length should exclude 0
;
*/


char *my_malloc(size_t size)
/*@
	requires size > 0
	ensures res::strbuf<hd, size, _, False>
		& res = hd;
*/
;

char *my_calloc(size_t size)
/*@
	requires size > 0
	ensures res::strbuf<hd, size, 0, True>
		& res = hd;
*/
;

char *my_declare()
/*@
	requires true
	ensures res::strbuf<hd, _, _, False>
		& res = hd;
*/
;

char *my_assign(size_t str_len, size_t str_size)
/*@
	requires str_size > 0
	ensures res::strbuf<hd, bsize, sl, True>
		& bsize = str_size
		& sl = str_len
		& res = hd;
*/
;

char *my_literal(size_t size)
/*@
	requires true
	ensures res::strbuf<hd, size + 1, size, True>
		& res = hd;
*/
;

char *my_strcpy(char *dest, char *src)
/*@
	requires dest::strbuf<hd_d, bsize_d, sl_d, _>
		* src::strbuf<hd_s, bsize_s, sl_s, True>@L
		& sl_s - (src - hd_s) < bsize_d - (dest - hd_d)
	ensures dest::strbuf<hd_d, bsize_d, (dest - hd_d) + sl_s - (src - hd_s), True>
		& res = hd_d;
*/
;


char *my_strncpy(char *dest, char *src, size_t nbyte)
/*@
	requires dest::strbuf<hd_d, bsize_d, sl_d, _>
		* src::strbuf<hd_s, bsize_s, sl_s, _>@L
		& sl_s - (src - hd_s) >= nbyte
		& dest + nbyte < hd_d + bsize_d
	ensures dest::strbuf<hd_d, bsize_d, dest - hd_d + nbyte, True>
		& res = dest;

	requires dest::strbuf<hd_d, bsize_d, sl_d, _>
		* src::strbuf<hd_s, bsize_s, sl_s, True>@L
		& sl_s - (src - hd_s) < nbyte
		& dest + (sl_s - (src - hd_s)) < hd_d + bsize_d
	ensures dest::strbuf<hd_d, bsize_d, (dest - hd_d) + (sl_s - (src - hd_s)), True>
		& res = dest;
*/
;

size_t my_gets(int fildes, char *buf)
/*@
	requires buf::strbuf<hd, bsize, _, _>@L
		& 0 > 10
	ensures fail;
*/
;

size_t my_read(int fildes, char *src, size_t nbyte)
/*@
	requires src::strbuf<hd, bsize, _, _>
		& src + nbyte <= hd + bsize
		& nbyte > 0
	ensures src::strbuf<hd, bsize, nbyte, True>
		 & res = nbyte;
*/
;

/* Nu am cum sa verific care este dimensiunea datelor date in format, dar pot macar sa verific ca formatul incape */
int my_sprintf(char *str, const char *format)
/*@
	requires str::strbuf<hd_s, bsize_s, sl_s, _>
		* format::strbuf<hd_f, bsize_f, sl_f, True>@L
		& sl_f - (format - hd_f) < bsize_s - (str - hd_s)
	ensures str::strbuf<hd_s, bsize_s, _, True>
		& res = 0;
*/
;

int my_snprintf(char *str, size_t size, const char *format)
/*@
	requires str::strbuf<hd_s, bsize_s, sl_s, _>
		* format::strbuf<hd_f, bsize_f, sl_f, _>@L
		& offset_s = str - hd_s
		& offset_f = format - hd_f
		& sl_f - offset_f > size 
		& str + size < hd_s + bsize_s
	ensures str::strbuf<hd_s, bsize_s, offset_s + size, True>
		& res = size;
	requires str::strbuf<hd_s, bsize_s, sl_s, _>
		* format::strbuf<hd_f, bsize_f, sl_f, True>@L
		& offset_s = str - hd_s
		& offset_f = format - hd_f
		& sl_f - offset_f <= size
		& str + (sl_f - offset_f) < hd_s + bsize_s
	ensures str::strbuf<hd_s, bsize_s, offset_s + (sl_f - offset_f), True>
		& res = sl_f - offset_f;
*/
;

char *my_strcat(char *dest, const char *src)
/*@
	requires dest::strbuf<hd_d, bsize_d, sl_d, True>@L
		* src::strbuf<hd_s, bsize_s, sl_s, True>
		& sl_d + sl_s - (src - hd_s) < bsize_d
	ensures dest::strbuf<hd_d, bsize_d, sl_d + sl_s - (src - hd_s), True>
		& res = dest;*/
;

char *my_strncat(char *dest, const char *src, size_t nbyte)
/*@
	requires src::strbuf<hd_s, bsize_s, sl_s, _>@L
		* dest::strbuf<hd_d, bsize_d, sl_d, True>
		& sl_s - (src - hd_s) <= nbyte
		& sl_d + sl_s - (src - hd_s) < bsize_d
	ensures dest::strbuf<hd_d, bsize_d, sl_d + sl_s - (src - hd_s), True>
		& res = hd_d;

	requires src::strbuf<hd_s, bsize_s, sl_s, True>@L
		* dest::strbuf<hd_d, bsize_d, sl_d, True>
		& sl_s - (src - hd_s) > nbyte
		& sl_d + nbyte < bsize_d
	ensures dest::strbuf<hd_d, bsize_d, sl_d + nbyte, True>
		& res = hd_d;
*/
;

int my_strlen(char *str)
/*@
	requires str::strbuf<hd, bsize, sl, True>@L
	ensures res = sl;
*/
;

void my_string_index(char *str, int i)
/*@
	requires str::strbuf<hd, bsize, sl, zeroflag>@L
		& str + i <= hd + bsize
	ensures true;
*/
;

char *my_string_offset(char *str, int i)
/*@
	requires str::strbuf<hd, bsize, sl, zeroflag>@L
		& i < bsize
	ensures res::strbuf<hd, bsize, sl, zeroflag>
		& res = str + i;
*/
;

void my_free(void *p)
/*@
	requires true
	ensures true;
*/
;
#endif
