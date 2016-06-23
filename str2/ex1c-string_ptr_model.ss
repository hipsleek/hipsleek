pred_prim strbuf<hd,str:string,size:int>
  inv hd<=self & (self<=hd+slen(str)) & (slen(str)<=size) & self<hd+size;

strbuf plus_plus(strbuf cptr)
  requires cptr::strbuf<hd,str,size>
             & hd<=cptr+1 & (cptr+1<=hd+slen(str)) & cptr+1<hd+size
  ensures  res::strbuf<hd,str,size> & res=cptr+1;

char char_at (strbuf cptr)
 requires cptr::strbuf<hd,str,size>@L & cptr<hd+slen(str)
 case {
    cptr+1=hd+slen(str) -> ensures res='\x00'; //not always correct
    (cptr+1)!=(hd+slen(str)) -> ensures res = charAt(str,(cptr-hd))
                                & res != '\x00' ;
 }

lemma self::strbuf<hd,str,sz> & hd<=self2
  & (self2<=hd+slen(str)) & self2<hd+sz
  -> self2::strbuf<hd,str,sz>.

strbuf char_update(strbuf cptr, char c)
  requires cptr::strbuf<hd,str,size> & cptr < hd+slen(str)
  ensures res::strbuf<hd,charUp(str,(cptr-hd),c),size>;

strbuf char_append(strbuf cptr, char c)
  requires cptr::strbuf<hd,str,size> & cptr-hd = slen(str) & cptr-hd < size
  ensures res::strbuf<hd,str^c,size>;

string get_substr(strbuf cptr) //get the sub-string not include zero
  requires cptr::strbuf<hd,str,size> & (cptr < hd+slen(str))
  ensures cptr::strbuf<hd,str,size> /* & slen(res) = (hd+slen(str)-1)-cptr */
     & res = substr(str,(cptr-hd),(hd+slen(str))-cptr);
{
  char c = char_at(cptr);
  if (c == '\x00') return "";
  else {
    cptr = plus_plus(cptr);
    string s = get_substr(cptr);
    return c^s;
  }
}

/*=================================================================
Checking procedure get_substr$strbuf...

Post condition cannot be derived:
(may) cause: [  (must) cause:  cptr<(size+hd) & (slen(str))<=size & cptr<=((slen(str))+hd) 
& hd<=cptr &  res="" & cptr<((slen(str))+hd) & 1+cptr=(slen(str))+hd 
|-  res=substr(str, cptr+(-1*hd), (slen(str))+(-1*cptr)+hd). LOCS:[2;35;30;29;0;34;32] (must-bug),valid]

solver returns a model: hd = -6, cptr = -1

Muoi: I think we need the negated pointer model.

*/
