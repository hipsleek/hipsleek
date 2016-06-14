pred_prim strbuf<cptr:int,s:string,length:int>
        inv 0<=cptr<=slen(s) & slen(s)<=length & cptr<length;
        /* mem [0,length-1]; */

str_buf plus_plus(ref str_buf cptr)
 requires x::strbuf<cptr,str,length>  & cptr+1<=x+slen(s) & cptr+1<x+length
 ensures  x::strbuf<cptr',str,length> & cptr'=cptr+1;
