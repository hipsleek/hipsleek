pred_prim str_nullt<hd,str:string,size:int>
  inv hd<=self & (self<=hd+slen(str)) & (slen(str)<=size) & self<hd+size & endzero(str);

pred_prim strbuf<hd,str:string,size:int>
  inv hd<=self & (self<=hd+slen(str)) & (slen(str)<=size) & self<hd+size;

lemma self::strbuf<hd,str,sz> & hd<=self2
  & (self2<=hd+slen(str)) & self2<hd+sz
  -> self2::strbuf<hd,str,sz>.

lemma self::str_nullt<hd,str,sz> & hd<=self2
  & (self2<=hd+slen(str)) & self2<hd+sz
  -> self2::str_nullt<hd,str,sz>.

strbuf plus_plus(strbuf cptr)
  requires cptr::strbuf<hd,str,size>
             & hd<=cptr+1 & (cptr+1<=hd+slen(str)) & cptr+1<hd+size
  ensures  res::strbuf<hd,str,size> & res=cptr+1;
  requires cptr::str_nullt<hd,str,size>
             & hd<=cptr+1 & (cptr+1<=hd+slen(str)) & cptr+1<hd+size
  ensures  res::str_nullt<hd,str,size> & res=cptr+1;


char char_at (str_nullt cptr)
 requires cptr::str_nullt<hd,str,size>@L & cptr<hd+slen(str)
 ensures res = charAt(str,(cptr-hd));

void char_append(strbuf cptr, char c)
  requires cptr::strbuf<hd,str,size> & (cptr = hd+slen(str)) & (cptr+1) < (hd+size) & nonzero(str)
  case{
    c = '\x00' -> ensures cptr::str_nullt<hd,str^c,size>;
    c != '\x00' -> ensures cptr::strbuf<hd,str^c,size>;
  }

void str_append(strbuf cptr, string s)
  requires cptr::strbuf<hd,str,size> & (cptr = hd+slen(str)) & (cptr+slen(s)) < (hd+size) & nonzero(str)
  case{
    endzero(s) -> ensures cptr::str_nullt<hd,str^s,size>;
    !(endzero(s)) -> ensures cptr::strbuf<hd,str^s,size>;
  }

char get_char(string s, int i)
  requires 0<= i < slen(s)
  ensures res = charAt(s,i);

int get_slen(string s)
  requires true
  ensures res = slen(s);

strbuf string_append(strbuf cptr, string s, int i)
  requires cptr::strbuf<hd,str,size> & (cptr = hd+slen(str))
         & (0<=i<slen(s)) & (cptr+slen(s)-i) < (hd+size) & endzero(s) & nonzero(str)
  ensures res::str_nullt<hd,str2,size>;
{
  char c = get_char(s,i);
  char_append(cptr,c);
  cptr = plus_plus(cptr);
  if (c == '\x00'){
    return cptr;
  }
  else{
    i = i+1;
    return string_append(cptr,s,i);
  }
}
