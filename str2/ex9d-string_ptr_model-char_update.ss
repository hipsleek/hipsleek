pred_prim strbuf<hd,str:string,size:int>
  inv hd<=self & (self<=hd+slen(str)) & (slen(str)<=size) & self<hd+size;

strbuf plus_plus(strbuf cptr)
  requires cptr::strbuf<x,str,size>
             & x<=cptr+1 & (cptr+1<=x+slen(str)) & cptr+1<x+size
  ensures  res::strbuf<x,str,size> & res=cptr+1;


strbuf minus_minus(strbuf cptr)
  requires cptr::strbuf<x,str,size>
             & x<=cptr-1 & (cptr-1<=x+slen(str)) & cptr-1<x+size
  ensures  res::strbuf<x,str,size> & res=cptr-1;

char char_at (strbuf cptr)
 requires cptr::strbuf<x,str,size>@L & cptr<x+slen(str)
 case {
    cptr+1=x+slen(str) -> ensures res='\x00';
    (cptr+1)!=(x+slen(str)) -> ensures res = charAt(str,(cptr-x)) & res != '\x00' ;
 }

strbuf char_update (strbuf cptr, char c)
  requires cptr::strbuf<x,str,size> & slen(str) < size
  case {
    cptr = x+slen(str) -> ensures res::strbuf<x,str^c,size>;
    cptr != x+slen(str) -> ensures res::strbuf<x,charUp(str,(cptr-x),c),size>;
  }

lemma self::strbuf<hd,str,sz> & hd<=self2
  & (self2<=hd+slen(str)) & self2<hd+sz
  -> self2::strbuf<hd,str,sz>.
