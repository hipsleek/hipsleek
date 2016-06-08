
/* data str_buf{ */
/*    int offset; */
/*    string s; */
/*    int size; */
/* } */

/* pred str_obj<offset,s,length> == */
/*   self::str_buf<offset,s,length> & endzero(s) & slen(s)<=length */
/*            & 0<=offset<length */
/*   inv endzero(s) & slen(s)<=length & 0<=offset<length. */

/* str_buf plus_plus(ref str_buf s) */
/*   requires s::str_obj<offset,str,length> & offset < length-1 */
/*   ensures s'::str_obj<offset+1,str,length> & offset <= length-1 & res = s'; */
/* { */
/*   s.offset = s.offset+1; */
/*   return s; */
/* } */

/* char chrAt(int offset, string s) */
/*   requires 0<=offset<slen(s) */
/*   ensures res = charAt(s, offset); */

/* char char_at (str_buf s) */
/*   requires s::str_obj<offset,str,length> & 0<=offset<slen(str) */
/*   ensures s::str_obj<offset,str, length> & res = charAt(str, offset); */
/* { */
/*   return chrAt(s.offset, s.s); */
/* } */

/*
     while (*s != '\0')
         s++;
*/

void while1(ref str_buf s)
  requires s::str_obj<offset,str,length> & 0 <= offset < slen(str)
  ensures s'::str_obj<(slen(str)-1),str,length>;
{
  char c = char_at(s);
  if (c != '\x00'){
    s = plus_plus(s);
    while1(s);
    }
}
