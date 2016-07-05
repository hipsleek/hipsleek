pred_prim strbuf<cptr,sl:int,length:int>
  inv self<=cptr & cptr<=self+sl & sl<=length & cptr<self+length;
  //iroot cptr;

strbuf plus_plus(ref strbuf cptr)
  requires x::strbuf<cptr,sl,ln> 
            & cptr+1<=x+sl 
            & cptr+1<x+ln
  ensures  x::strbuf<cptr',sl,ln> & cptr'=cptr+1;


 int char_at (strbuf cptr)
  requires xx::strbuf<cptr,sl,length>@L & cptr<xx+sl
  case { 
    cptr+1=xx+sl -> ensures res=0;
    (cptr+1)!=(xx+sl) -> ensures res>0 ;
 }

 int clen(strbuf cptr)
  requires xxx::strbuf<cptr,sl,length>@L & cptr<xxx+sl
  ensures res = sl-1;
 {
     int c = char_at(cptr);
     if (c==0) return 0;
     else {
       plus_plus(cptr);
        return 1+clen(cptr);
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
