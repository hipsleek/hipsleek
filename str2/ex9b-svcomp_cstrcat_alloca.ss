
data str_buf{
   int offset;
   string s;
   int size;
}

pred nullt_str<offset,s,length> ==
  self::str_buf<offset,s,length> & endzero(s) & slen(s)<=length
           & 0<=offset<length
  inv slen(s)<=length & 0<=offset<length.

pred str_obj<offset,s,length> ==
  self::str_buf<offset,s,length> & nonzero(s) & slen(s)<=length
           & 0<=offset<length
  inv slen(s)<=length & 0<=offset<length.

str_buf plus_plus(str_buf s)
  requires s::str_obj<offset,str,length> & offset < length-1
  ensures s::str_obj<offset+1,str,length> & offset <= length-1 & res = s;
  /* requires s::nullt_str<offset,str,length> & offset < length-1 */
  /* ensures  s::nullt_str<offset+1,str,length> & offset < length & res = s; */
{
  s.offset = s.offset+1;
  return s;
}

char chrAt(int offset, string s)
  requires 0<=offset<slen(s)
  ensures res = charAt(s, offset);

char char_at (str_buf s)
  requires s::str_obj<offset,str,length>@L & 0<=offset<slen(str)
  ensures res = charAt(str, offset);
{
  return chrAt(s.offset, s.s);
}

string chrApp(string s, char c) //append character
  requires true
  ensures res = s^c;

string chrUp(string s, int offset, char c)
 requires 0<= offset < slen(s) & endzero(s)
 case {
  c = '\x00' -> endzero(res) & res = charUp(s,offset,c);
  c != '\x00' -> case{
    offset != clen(s) ->
       ensures endzero(res) & res = charUp(s,offset,c);
    offset = clen(s) ->
       ensures nonzero(res) & res = charUp(s,offset,c);
  }
 }

void char_update (str_buf s, char c)
  requires s::str_obj<offset,str,length>
  case {
    offset < slen(str) -> s::str_obj<offset,charUp(str,offset,c),length>;

  }
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
