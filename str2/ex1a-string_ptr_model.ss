pred_prim strbuf<hd,str:string,size:int>
  inv hd<=self & (self<=hd+slen(str)) & (slen(str)<=size) & self<hd+size;

strbuf plus_plus(strbuf cptr)
  requires cptr::strbuf<hd,str,size>
             & hd<=cptr+1 & (cptr+1<=hd+slen(str)) & cptr+1<hd+size
  ensures  res::strbuf<hd,str,size> & res=cptr+1;

char char_at (strbuf cptr)
 requires cptr::strbuf<hd,str,size>@L & cptr<hd+slen(str)
 case {
    cptr+1=hd+slen(str) -> ensures res='\x00';
    (cptr+1)!=(hd+slen(str)) -> ensures res = charAt(str,(cptr-hd))
                                & res != '\x00' ;
 }

lemma self::strbuf<hd,str,sz> & hd<=self2
  & (self2<=hd+slen(str)) & self2<hd+sz
  -> self2::strbuf<hd,str,sz>.

int clent(strbuf cptr)
  requires cptr::strbuf<x,str,size> & (cptr<x+slen(str))
  ensures  cptr::strbuf<x,str,size> & res = slen(str)-1-(cptr-x);
 {
     char c = char_at(cptr);
     if (c == '\x00') return 0;
     else {
       cptr = plus_plus(cptr);
       int r = clent(cptr);
       return 1+r;
    }
 }

