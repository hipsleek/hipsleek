pred_prim str_nullt<hd,str:string,size:int>
  inv hd<=self & (self<=hd+slen(str)) & (slen(str)<=size) & self<hd+size & endzero(str);

pred_prim strbuf<hd,str:string,size:int>
  inv hd<=self & (self<=hd+slen(str)) & (slen(str)<=size) & self<hd+size;

lemma self::strbuf<hd,str,sz> & hd<=self2
  & (self2<=hd+slen(str)) & self2<hd+sz
  -> self2::strbuf<hd,str,sz>.

/* lemma self::str_nullt<hd,str,sz> & hd<=self2 */
/*   & (self2<=hd+slen(str)) & self2<hd+sz */
/*   -> self2::str_nullt<hd,str,sz>. */

strbuf plus_plus(strbuf cptr)
  requires cptr::strbuf<hd,str,size> & (cptr+1<=hd+slen(str)) & cptr+1<hd+size
  ensures  res::strbuf<hd,str,size> & res=cptr+1;
  /* requires cptr::str_nullt<hd,str,size> */
  /*            & hd<=cptr+1 & (cptr+1<=hd+slen(str)) & cptr+1<hd+size */
  /* ensures  res::str_nullt<hd,str,size> & res=cptr+1; */

char get_char(strbuf s)
  requires s::strbuf<hd,str,size>@L
  ensures res = charAt(str,(s-hd));

//Include both update and append
void char_write(strbuf cptr, char c)
  requires cptr::strbuf<hd,str,size>
  case{
    cptr < hd+slen(str) -> ensures cptr::strbuf<hd,charUp(str,(cptr-hd),c),size>;
    cptr >= hd+slen(str) -> ensures cptr::strbuf<hd,str^c,size>;
      /* case{ */
      /*   c = '\x00' -> ensures cptr::str_nullt<hd,str^c,size>; */
      /*   c != '\x00' -> ensures cptr::strbuf<hd,str^c,size>; */
      /* } */
  }

void mem_cpy(strbuf src, ref int n)
  requires src::strbuf<hd,str,size> & (src+n<=hd+slen(str)) & (src+n<hd+size) & n>0
  ensures n' = 0;
{
  char c = get_char(src);
  n = n-1;
  src = plus_plus(src);
  if (n>0){
    mem_cpy(src,n);
  }
}
