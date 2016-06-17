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
  requires cptr::strbuf<x,str,size>
  case {
    cptr = x+slen(str) -> ensures res::strbuf<x,str^c,size>;
    cptr != x+slen(str) -> ensures res::strbuf<x,charUp(str,(cptr-x),c),size>;
  }

lemma self::strbuf<hd,str,sz> & hd<=self2
  & (self2<=hd+slen(str)) & self2<hd+sz
  -> self2::strbuf<hd,str,sz>.

/*
     while (*s != '\0')
         s++;
*/

void while1(ref strbuf cptr)
  requires cptr::strbuf<x,str,size> & cptr < x+slen(str)
  ensures cptr'::strbuf<x,str,size> & cptr'+1 = x+slen(str);
{
  char c = char_at(cptr);
  if (c != '\x00'){
    cptr = plus_plus(cptr);
    while1(cptr);
    }
}

/*
     while ((*s++ = *s2++) != '\0')
         ;
*/

void while2(strbuf s1, strbuf s2)
  requires s1::strbuf<x,str1,size1>*s2::strbuf<xx,str2,size2>
         & ((s1-x)+slen(str2))<=size1 & s2 < xx+slen(str2)
  ensures s1::strbuf<x, substr(str1,0,(s1-x)),size1>;
{
  char x = char_at(s2);
  char_update(s1, x);
  //dprint;
  s1 = plus_plus(s1);
  s2 = plus_plus(s2);
  if (x != '\x00'){
    while2(s1,s2);
    }
}
