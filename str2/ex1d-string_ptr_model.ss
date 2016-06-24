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

lemma self::strbuf<hd,str,sz> & s2 = charUp(str, i, c) & i < slen(str)
    -> self2::strbuf<hd,s2,sz> & slen(s2) = slen(str).

void char_update(strbuf cptr, char c)
  requires cptr::strbuf<hd,str,size> & cptr < hd+slen(str)
  ensures cptr::strbuf<hd,charUp(str,(cptr-hd),c),size>;

strbuf char_append(strbuf cptr, char c)
  requires cptr::strbuf<hd,str,size> & cptr-hd = slen(str) & cptr-hd < size
  ensures res::strbuf<hd,str^c,size>;

char get_char(string s, int i)
  requires i < slen(s)
  ensures res = charAt(s,i);

int get_slen(string s)
  requires true
  ensures res = slen(s);

strbuf string_overwrite(strbuf cptr, string s, int i)
  requires cptr::strbuf<hd,str,size> & (cptr < hd+slen(str)) & (i < slen(s)) & (cptr+slen(s)-i) < (hd+size)
  ensures res::strbuf<hd,str2,size> & slen(str) = slen(str2);
{
  char c = char_at(cptr);
  if ((c == '\x00') || (i+1 >= get_slen(s)))
      return cptr;
  else{
    char sc = get_char(s,i);
    char_update(cptr,sc);
    cptr = plus_plus(cptr);
    i = i+1;
    return string_overwrite(cptr,s,i);
  }
}

/* hd+size > cptr+slen(s) > i+cptr+1 >= cptr+1 |- hd+size>cptr+1 */
