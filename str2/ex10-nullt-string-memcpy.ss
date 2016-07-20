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

char get_char(strbuf s)
  requires s::strbuf<hd,str,size>
  ensures res = charAt(str,(s-hd));

//Include both update and append
void char_write(strbuf cptr, char c)
  requires cptr::strbuf<hd,str,size>
  case{
    cptr < hd+slen(str) -> ensures cptr::strbuf<hd,charUp(str,(cptr-hd),c),size>;
    cptr >= hd+slen(str) ->
      case{
        c = '\x00' -> ensures cptr::str_nullt<hd,str^c,size>;
        c != '\x00' -> ensures cptr::strbuf<hd,str^c,size>;
      }
  }

void mem_cpy(strbuf dest, strbuf src, int n)
  requires dest::strbuf<hd1,str1,size1>*src::strbuf<hd2,str2,size2> & (dest + n) < (hd1+size1) & n > 0
  ensures dest::strbuf<hd1,str3,size>;
{
  char c = get_char(src);
  char_write(dest,c);
  n = n-1;
  if (n>0){
    dest = plus_plus(dest);
    src = plus_plus(src);
    mem_cpy(dest,src,n);
  }
}
