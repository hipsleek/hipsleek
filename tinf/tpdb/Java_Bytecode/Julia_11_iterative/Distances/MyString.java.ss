
global char[] MyString_charSet = { 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z' };

global int MyString_charSetLen = _this.charSet.length;
data MyString
{
char[] values;
}
 int MyString_length(MyString _this)
{
  return _this.values.length;
}

char MyString_charAt(MyString _this, int index)
{
  if (0 <= index && index < _this.values.length)
    return _this.values[index];
  else
    throw new ArrayIndexOutOfBoundsException();
}

void MyString_append(MyString _this, char c)
{
  int len = _this.values.length;
  char[] temp = new char[len + 1];
  
  int i = 0;
  while (i < len) {
    temp[i] = _this.values[i];
    i++;
  }
  
  temp[len] = c;
  _this.values = temp;
}



data Distances
{

}
 int Distances_max(int a, int b)
{
  return a < b ? b : a;
}

int Distances_min(int a, int b)
{
  return a > b ? b : a;
}

int Distances_min(int a, int b, int c)
{
  return Distances_min(a, Distances_min(b, c));
}

int Distances_levenshtein(MyString s1, MyString s2)
{
  int len1 = MyString_length();
  int len2 = MyString_length();
  int[][] d = new int[len1 + 1][len2 + 1];
  
  int i = 0;
  while (i <= len1) {
    d[i][0] = i;
    i++;
  }
  
  
  int j = 0;
  while (j <= len2) {
    d[0][j] = j;
    j++;
  }
  
  
  int j = 0;
  while (j < len2) {
    
    int i = 0;
    while (i < len1) {
      if (MyString_charAt(i) == MyString_charAt(j))
        d[i + 1][j + 1] = d[i][j];
      else
        d[i + 1][j + 1] = Distances_min(d[i][j + 1] + 1, d[i + 1][j] + 1, d[i][j] + 1);
      i++;
    }
    
    j++;
  }
  
  return d[len1][len2];
}

int Distances_abs(int n)
{
  return n >= 0 ? n : -1 * n;
}

int Distances_hamming(MyString s1, MyString s2)
{
  int l = MyString_length();
  if (l != MyString_length())
    return -1;
  int d = 0;
  
  int i = 0;
  while (i < l) {
    if (MyString_charAt(i) != MyString_charAt(i))
      d++;
    i++;
  }
  
  return d;
}

MyString Distances_findMatch(MyString s1, boolean[] b)
{
  MyString __res = new MyString();
  
  int i = 0;
  while (i < MyString_length()) {
    if (b[i])
      MyString_append(MyString_charAt(i));
    i++;
  }
  
  return __res;
}

int Distances_jaro(MyString s1, MyString s2)
{
  int len1 = MyString_length();
  int len2 = MyString_length();
  boolean[] b1 = new boolean[len1];
  boolean[] b2 = new boolean[len2];
  
  int i = 0;
  while (i < len1) {
    b1[i] = false;
    i++;
  }
  
  
  int i = 0;
  while (i < len2) {
    b2[i] = false;
    i++;
  }
  
  int m = 0;
  int threshold = Distances_max(len1, len2) / 2 - 1;
  
  int i = 0;
  while (i < len1) {
    
    int j = Distances_max(i - threshold, 0);
    while (j <= Distances_min(i + threshold, len2 - 1)) {
      if (MyString_charAt(i) == MyString_charAt(j)) {
        m++;
        b1[i] = true;
        b2[j] = true;
        break;
      }
      j++;
    }
    
    i++;
  }
  
  if (m == 0)
    return 0;
  MyString s1Matches = Distances_findMatch(s1, b1);
  MyString s2Matches = Distances_findMatch(s2, b2);
  int t = 0;
  
  int i = 0;
  while (i < MyString_length()) {
    if (MyString_charAt(i) != MyString_charAt(i))
      t++;
    i++;
  }
  
  t /= 2;
  return (m / len1 + m / len2 + (m - t) / m) / 3;
}

void Distances_main(String[] args)
{
  
  int i = 1;
  while (i <= args.length) {
    MyString s1 = new MyString(i, 2);
    MyString s2 = new MyString(i, 3);
    if (i % 2 == 0)
      if (Distances_levenshtein(s1, s2) < i / 2)
        Distances_hamming(s1, s2);
      else
        Distances_jaro(s1, s2);
    else if (i % 3 == 0)
      if (Distances_levenshtein(s1, s2) < i / 3)
        Distances_hamming(s1, s2);
      else
        Distances_jaro(s1, s2);
    else if (i % 5 == 0)
      if (Distances_levenshtein(s1, s2) < i / 5)
        Distances_hamming(s1, s2);
      else
        Distances_jaro(s1, s2);
    else
      
      int j = 0;
      while (j < 100) {
        ;
        j++;
      }
      
    i++;
  }
  
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;