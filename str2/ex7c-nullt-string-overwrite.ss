pred_prim str_nullt<hd,str:string,size:int>
  inv hd<=self & (self<=hd+slen(str)) & (slen(str)<=size) & self<hd+size & endzero(str);

lemma self::str_nullt<hd,str,sz> & hd<=self2
  & (self2<=hd+slen(str)) & self2<hd+sz
  -> self2::str_nullt<hd,str,sz>.

lemma self::str_nullt<hd,str,sz> & s2 = charUp(str, i, c) & i < slen(str)
    -> self2::str_nullt<hd,s2,sz> & slen(s2) = slen(str).

str_nullt plus_plus(str_nullt cptr)
  requires cptr::str_nullt<hd,str,size>
             & hd<=cptr+1 & (cptr+1<=hd+slen(str)) & cptr+1<hd+size
  ensures  res::str_nullt<hd,str,size> & res=cptr+1;

char char_at (str_nullt cptr)
 requires cptr::str_nullt<hd,str,size>@L & cptr<hd+slen(str)
 ensures res = charAt(str,(cptr-hd));

void char_update(str_nullt cptr, char c)
  requires cptr::str_nullt<hd,str,size> & cptr < hd+slen(str)
  ensures cptr::str_nullt<hd,charUp(str,(cptr-hd),c),size>;

char get_char(string s, int i)
  requires i < slen(s)
  ensures res = charAt(s,i);

int get_slen(string s)
  requires true
  ensures res = slen(s);

str_nullt string_overwrite(str_nullt cptr, string s, int i)
  requires cptr::str_nullt<hd,str,size> & (cptr < hd+slen(str)) & (i < slen(s)) & (cptr+slen(s)-i) < (hd+size)
  ensures res::str_nullt<hd,str2,size> & slen(str) = slen(str2);
{
  char c = char_at(cptr);
  if ((c == '\x00') || (i+1 >= get_slen(s)))
      return cptr;
  else{
    char sc = get_char(s,i);
    char_update(cptr,sc);
    cptr = plus_plus(cptr);
    i = i+1;
    return string_overwrite(cptr,s,i);
  }
}
