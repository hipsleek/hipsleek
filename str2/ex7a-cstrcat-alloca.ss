data str_buf{
   int offset;
   string s;
   int size;
}

pred str_obj<offset,s,length> ==
   self::str_buf<offset,s,length> & exists (s1: s=s1^"0" &  slen(s)<=length
           & 0<=offset<=length-1)
   inv exists (s1: s=s1^"0" &  slen(s)<=length & 0<=offset<=length-1).

void plus_plus(str_buf s)
   requires s::str_obj<offset,str,length> & offset<length-1
   ensures s::str_obj<offset+1,str,length>;
{
    s.offset = s.offset+1;
}
