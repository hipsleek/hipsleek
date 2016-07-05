pred_prim strbuf<hd,sl:int,length:int>
  inv hd<=self & self<=hd+sl & sl<=length & self<hd+length;
  //iroot cptr;

lemma self::strbuf<hd,sl,ln> --> self::strbuf<hd,sl,ln>.

strbuf plus_plus(strbuf cptr)
  requires cptr::strbuf<x,sl,ln> 
             & cptr+1<=x+sl & cptr+1<x+ln
  ensures  res::strbuf<x,sl,ln> & res=cptr+1;

/*
  requires cptr::strbuf<x,sl,ln>@L
             & cptr+1<=x+sl & cptr+1<x+ln
  ensures  res=cptr+1;
*/

strbuf minus_minus(strbuf cptr)
  requires cptr::strbuf<x,sl,ln> 
             & cptr-1<=x+sl & cptr-1<x+ln
  ensures  res::strbuf<x,sl,ln> & res=cptr-1;


int char_at (strbuf cptr)
 requires cptr::strbuf<xx,sl,length>@L & cptr<xx+sl
 case { 
    cptr+1=xx+sl -> ensures res=0;
    (cptr+1)!=(xx+sl) -> ensures res>0 ;
 }


// To verify clen, we need the following lemma
// ptr::stfbuf<hd,sl,size> &  hd<=ptr2 & ptr2<=hd+sl & ptr2<hd+length
//    --> ptr2::stfbuf<hd,sl,size>

int clen(strbuf cptr)
  requires cptr::strbuf<xxx,sl,length> & cptr<xxx+sl & cptr<xxx+length
  ensures  cptr::strbuf<xxx,sl,length> & res = sl-1-(cptr-xxx) 
              & cptr-xxx=sl-1
              //& cptr'=xxx+sl-1
              ;
 {
     int c = char_at(cptr);
     if (c==0) return 0;
     else {
       dprint;
        cptr = plus_plus(cptr);
        int r = clen(cptr);
        cptr = minus_minus(cptr);
        return 1+r;
    }
 }

/*


 view_prim strbuf{}[]<cptr:int,sl:int,length:int>= 
  view_domains: 
   view_prim strbuf<cptr:int,sl:int,length:int>= 
    EBase 
      (* lbl: *){228}->emp&{FLOW,(1,28)=__flow#E}[]
  view vars: cptr:int,sl:int,length:int
  cont vars: 


    self:strbuf<=cptr:int & cptr:int<=(sl:int+self:strbuf) & 
    sl:int<=length:int & cptr:int<(length:int+self:strbuf)

# seems that cptr is being inferred as int..

(FIXED)

checkentail x::strbuf<cp,sl,l> |- cp>=x.
expect Valid.

checkentail x::strbuf<cp,sl,l> |- cp>x.
expect Fail_May.

checkentail x::strbuf<cp,sl,l> |- cp<x.
expect Fail_Must.
  */
