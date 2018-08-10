int modulo(int x, int y)
    requires x >= 0 & y > 0 ensures exists r: res = x - r * y & 0 <= res < y & r >= 0;
{
  if (x < y) return x;
  else return modulo(x - y, y);
}

// int mod(int x)
// requires exists r,m: x >= 0 & x = r *10 + m & 0 <= m < 10 & r >= 0
// ensures res = m;

// {
//   if (x < 9) return x;
//   else return mod(x - 10);
// }

 // y<=x & 0<y & 0<=x & res+(r_1865*y)+y=x |-  exists(r_1866:res+(r_1866*y)=x)
// rhs = exists r: res + r * y = res + r_65*y + y
// <=> exists r: r * y = r_65 * y + y