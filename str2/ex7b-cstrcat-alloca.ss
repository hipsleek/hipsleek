data str_buf{
   int offset;
   string s;
   int size;
}

pred str_obj<offset,s,length> ==
  self::str_buf<offset,s,length> & endzero(s) & slen(s)<=length
           & 0<=offset<=length
  inv endzero(s) & slen(s)<=length & 0<=offset<=length.

void plus_plus(ref str_buf s)
  requires s::str_obj<offset,str,length> & offset<length
  ensures s'::str_obj<offset+1,str,length>;
{
  s.offset = s.offset+1;
}

void minus_minus(ref str_buf s)
  requires s::str_obj<offset,str,length> & offset>0
  ensures s'::str_obj<offset-1,str,length>;
{
  s.offset = s.offset-1;
}

char char_at(int offset, string s)
  requires 0<=offset<=slen(s)
  ensures res = charAt(s, offset);

char rhs_deref (str_buf s)
  requires s::str_obj<offset,str,length> & 0<=offset<=slen(str)
  ensures s::str_obj<offset,str, length> & res = charAt(str, offset);
{
  return char_at(s.offset, s.s);
}

string char_up(string s, int offset, char c)
  requires 0<=offset<=slen(s)
  ensures res = charUp(s,offset,c) & slen(res) = slen(s);

void lhs_deref (str_buf s, char c)
  requires s::str_obj<offset,str,length> & 0<=offset<=slen(str)
  ensures s::str_obj<offset,charUp(str, offset, c),length>;
{
  s.s = char_up(s.s, s.offset, c);
}
