func int tf(int z) == ?.

// int sum(int x, int y)
// requires true ensures res = x + y;
// {
//    return x + y;
// }

// bool foo(int x, int y, int z)
// requires z > x + y ensures res = true;
// {
//   bool r;
//   r = x < tf(z);
//   return r;
// }


bool foo(int x, int y)
requires x - y > 0 ensures res = true;
{
     bool r;
     r = (2*x > y);
     return r;
} 