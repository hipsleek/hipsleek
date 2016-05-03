void concat(string x, ref string y)
  case {
       slen(x) > 0 -> ensures slen(y') > slen(y);
       slen(x) = 0 -> ensures y' = y;
       }
{
  y = y^x;
}
