pred_prim strbuf<hd,sl:int,length:int>
  inv hd<=self & self<=hd+sl & sl<=length & self<hd+length;
  //iroot cptr;

strbuf plus_plus(strbuf cptr)
  requires cptr::strbuf<x,sl,ln> 
             & x<=cptr+1 & cptr+1<=x+sl & cptr+1<x+ln
  ensures  res::strbuf<x,sl,ln> & res=cptr+1;


strbuf minus_minus(strbuf cptr)
  requires cptr::strbuf<x,sl,ln> 
        & x<=cptr-1 & cptr-1<=x+sl & cptr-1<x+ln
  ensures  res::strbuf<x,sl,ln> & res=cptr-1;



int char_at (strbuf cptr)
 requires cptr::strbuf<xx,sl,length>@L & cptr<xx+sl
 case { 
    cptr+1=xx+sl -> ensures res=0;
    (cptr+1)!=(xx+sl) -> ensures res>0 ;
 }

lemma self::strbuf<hd,sl,ln> & hd<=self2 & self2<=hd+sl & self2<hd+ln
  -> self2::strbuf<hd,sl,ln>.

// universal lemma for ls splitting
// self::ls<n,p> & n1+n2=n & n1,n2>=0 => self::ls<n1,q>*q::ls<n2,p>

int clen(strbuf cptr)
  requires cptr::strbuf<xxx,sl,length> & cptr<xxx+sl & cptr<xxx+length
  ensures  cptr::strbuf<xxx,sl,length> & res = sl-1-(cptr-xxx) 
              //& cptr'-xxx=sl-1
              //& cptr'=xxx+sl-1
              ;
 {
     int c = char_at(cptr);
     if (c==0) return 0;
     else {
       dprint;
        cptr = plus_plus(cptr);
        int r = clen(cptr);
        //cptr = minus_minus(cptr);
        return 1+r;
    }
 }


/*


Lemma "lem_11":  self::strbuf<hd,sl,ln>@M&hd<=self2 & self2<=(sl+hd) & self2<(ln+hd)&
{FLOW,(4,5)=__norm#E}[]==> self2::strbuf<hd,sl,ln>@M&{FLOW,(4,5)=__norm#E}[]
 head match:strbuf
 body view:
 body pred_list:[strbuf]
 coercion_univ_vars: [self2]
 materialized vars:  []
 coercion_case: Simple
 head:  self::strbuf<hd,sl,ln>@M&hd<=self2 & self2<=(sl+hd) & self2<(ln+hd)&
{FLOW,(4,5)=__norm#E}[]
 body:  self2::strbuf<hd,sl,ln>@M&{FLOW,(4,5)=__norm#E}[]
 head_norm:  (exists hd_2063,sl_2064,ln_2065,
self: self::strbuf<hd_2063,sl_2064,ln_2065>@M&
hd<=self2 & self2<=(sl+hd) & self2<(ln+hd) & hd_2063=hd & sl_2064=sl & 
ln_2065=ln&{FLOW,(4,5)=__norm#E}[])
 body_norm:  EBase 


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
