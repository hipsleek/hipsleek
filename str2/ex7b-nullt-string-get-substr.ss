pred_prim str_nullt<hd,str:string,size:int>
  inv hd<=self & (self<=hd+slen(str)) & (slen(str)<=size) & self<hd+size & endzero(str);

str_nullt plus_plus(str_nullt cptr)
  requires cptr::str_nullt<hd,str,size>
             & hd<=cptr+1 & (cptr+1<=hd+slen(str)) & cptr+1<hd+size
  ensures  res::str_nullt<hd,str,size> & res=cptr+1;

char char_at (str_nullt cptr)
 requires cptr::str_nullt<hd,str,size>@L & cptr<hd+slen(str)
 ensures res = charAt(str,(cptr-hd));

lemma self::str_nullt<hd,str,sz> & hd<=self2
  & (self2<=hd+slen(str)) & self2<hd+sz
  -> self2::str_nullt<hd,str,sz>.

string get_substr(str_nullt cptr)
  requires cptr::str_nullt<hd,str,size> & (cptr<hd+slen(str))
  ensures  cptr::str_nullt<hd,str,size> & slen(res) = (hd+slen(str)-1)-cptr;
{
  char c = char_at(cptr);
  if (c == '\x00') return "";
     else {
       cptr = plus_plus(cptr);
       string s = get_substr(cptr);
       return c^s;
    }
}
