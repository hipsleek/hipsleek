
data str_buf{
   int offset;
   string s;
   int size;
}

pred str_obj<offset,s,length> ==
  self::str_buf<offset,s,length> & 0 <= clen(s) & slen(s)<=length
           & 0<=offset<length
  inv 0 <= clen(s) & slen(s)<=length & 0<=offset<length.

str_buf plus_plus(ref str_buf s)
  requires s::str_obj<offset,str,length> & offset < length-1
  ensures s::str_obj<offset+1,str,length> & offset <= length-1 & res = s;
{
  s.offset = s.offset+1;
  return s;
}

char chrAt(int offset, string s)
  requires 0<=offset<slen(s)
  ensures res = charAt(s, offset);

char char_at (str_buf s)
  requires s::str_obj<offset,str,length> & 0<=offset<slen(str)
  ensures res = charAt(str, offset);
{
  return chrAt(s.offset, s.s);
}


string chrUp(string s, int offset, char c)
 requires 0<= offset < slen(s) & clen(s) < slen(s) & endzero(s,clen(s))
 case {
  c = '\x00' -> case{
    offset < clen(s) -> ensures endzero(res,offset) & slen(res) = slen(s) & res = charUp(s,offset,c);
    offset >= clen(s) -> ensures endzero(res,clen(s)) & slen(res) = slen(s) & res = charUp(s,offset,c);
    }
  c != '\x00' -> case{
    offset != clen(s) -> ensures endzero(res,clen(s)) & slen(res) = slen(s) & res = charUp(s,offset,c);
    offset = clen(s) -> ensures nonzero(res,offset) & slen(res) = slen(s) & res = charUp(s,offset,c);
  }
 }

void char_update (str_buf s, char c)
  requires s::str_obj<offset,str,length> & offset < slen(str) /* & offset != clen(str) */
  ensures s::str_obj<offset,charUp(str,offset,c),length>;
{
  s.s = chrUp(s.s, s.offset, c);
}

/*
     while ((*s++ = *s2++) != '\0')
         ;
*/
/* void while2(str_buf s1, str_buf s2) */
/*   requires s1::str_obj<o1,str1,l1>*s2::str_obj<o2,str2,l2> & o1 < slen(str1) &  o2 < slen(str2) */
/*   ensures true; */
/* { */
/*   char x = char_at(s2); */
/*   char_update(s1, x); */
/*   s1 = plus_plus(s1); */
/*   s2 = plus_plus(s2); */
/*   if (x != '\x00'){ */
/*     while2(s1,s2); */
/*     } */
/* } */
