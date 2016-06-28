pred_prim str_nullt<hd,str:string,size:int>
  inv hd<=self & (self<=hd+slen(str)) & (slen(str)<=size) & self<hd+size & endzero(str);

pred_prim strbuf<hd,str:string,size:int>
  inv hd<=self & (self<=hd+slen(str)) & (slen(str)<=size) & self<hd+size;

lemma self::str_nullt<hd,str,sz> & hd<=self2
  & (self2<=hd+slen(str)) & self2<hd+sz
  -> self2::str_nullt<hd,str,sz>.

lemma self::strbuf<hd,str,sz> & hd<=self2
  & (self2<=hd+slen(str)) & self2<hd+sz
  -> self2::strbuf<hd,str,sz>.

//lemma self::str_nullt<hd,str,sz> & s2 = charUp(str, i, c) & i < slen(str)
//    -> self2::str_nullt<hd,s2,sz> & slen(s2) = slen(str).

lemma self::strbuf<hd,str,sz> & endzero(str) <-> self::str_nullt<hd,str,sz>.

strbuf plus_plus(strbuf cptr)
  requires cptr::strbuf<hd,str,size>
             & hd<=cptr+1 & (cptr+1<=hd+slen(str)) & cptr+1<hd+size
  ensures  res::strbuf<hd,str,size> & res=cptr+1;

char char_at (str_nullt cptr)
 requires cptr::str_nullt<hd,str,size>@L & cptr<hd+slen(str)
 ensures res = charAt(str,(cptr-hd));

void char_append(strbuf cptr, char c)
  requires cptr::strbuf<hd,str,size> & (cptr = hd+slen(str)) & (cptr+1) < (hd+size) & nonzero(str)
  case{
    c = '\x00' -> ensures cptr::str_nullt<hd,str^c,size>;
    c != '\x00' -> ensures cptr::strbuf<hd,str^c,size>;
  }

char get_char(string s, int i)
  requires 0<= i < slen(s)
  ensures res = charAt(s,i);

int get_slen(string s)
  requires true
  ensures res = slen(s);

strbuf string_append(strbuf cptr, string s, int i)
  requires cptr::strbuf<hd,str,size> & (cptr = hd+slen(str))
         & (0<=i<slen(s)) & (cptr+slen(s)-i+1) < (hd+size) & endzero(s) & nonzero(str)
  ensures cptr::strbuf<hd,str2,size>;
{
  if (i+1 >= get_slen(s))
    return cptr;
  else{
    char sc = get_char(s,i);
    char_append(cptr,sc);
    cptr = plus_plus(cptr);
    i = i+1;
    return string_append(cptr,s,i);
  }
}
