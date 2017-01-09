public class Distances {

    public static int max(int a, int b) {
	return (a < b ? b : a);
    }

    public static int min(int a, int b) {
	return (a > b ? b : a);
    }

    public static int min(int a, int b, int c) {
	return min(a, min(b, c));
    }

    public static int levenshtein(MyString s1, MyString s2) {
	int len1 = s1.length(), len2 = s2.length();
	int d[][] = new int[len1+1][len2+1];

	for (int i = 0; i <= len1; i++) d[i][0] = i;
	for (int j = 0; j <= len2; j++) d[0][j] = j;

	for (int j = 0; j < len2; j++)
	    for (int i = 0; i < len1; i++)
		if (s1.charAt(i) == s2.charAt(j))  d[i+1][j+1] = d[i][j];
		else d[i+1][j+1] = min(d[i][j+1]+1, d[i+1][j]+1, d[i][j]+1);

	return d[len1][len2];
    }

    public static int abs(int n) {
	return (n >= 0 ? n : -1*n);
    } 

    public static int hamming(MyString s1, MyString s2) {
	int l = s1.length();

	if (l != s2.length()) return -1;

	int d = 0;
	for (int i = 0; i < l; i++)
	    if (s1.charAt(i) != s2.charAt(i)) d++;
	return d;
    }

    private static MyString findMatch(MyString s1, boolean b[]) {
	MyString res = new MyString();
	for (int i = 0; i < s1.length(); i++)
	    if (b[i]) res.append(s1.charAt(i));
	return res;
    }

    public static int jaro(MyString s1, MyString s2) {
	int len1 = s1.length(), len2 = s2.length();
	boolean b1[] = new boolean[len1];
	boolean b2[] = new boolean[len2];
	for (int i = 0; i < len1; i++) b1[i] = false;
	for (int i = 0; i < len2; i++) b2[i] = false;

	// number of matching characters:
	int m = 0;
	int threshold = max(len1, len2)/2 - 1;
	for (int i = 0; i < len1; i++)
	    for (int j = max(i-threshold, 0); j <= min(i+threshold, len2-1); j++)
		if (s1.charAt(i) == s2.charAt(j)) {
		    m++;
		    b1[i] = true;
		    b2[j] = true;
		    break;
		}
	if (m == 0) return 0;

	// number of transpositions:
	MyString s1Matches = findMatch(s1, b1);
	MyString s2Matches = findMatch(s2, b2);
	int t = 0;
	for (int i = 0; i < s1Matches.length(); i++)
	    if (s1Matches.charAt(i) != s2Matches.charAt(i)) t++;
	t /= 2;

	// Jaro distance:
	return (m/len1 + m/len2 + (m-t)/m) / 3;
    }

    public static void main(String args[]) {
	for (int i = 1; i <= args.length; i++) {
	    MyString s1 = new MyString(i, 2);
	    MyString s2 = new MyString(i, 3);
	    if (i % 2 == 0) 
		if (levenshtein(s1, s2) < i/2) hamming(s1, s2);
		else jaro(s1, s2);
	    else if (i % 3 == 0)
		if (levenshtein(s1, s2) < i/3) hamming(s1, s2);
  		else jaro(s1, s2);
	    else if (i % 5 == 0)
		if (levenshtein(s1, s2) < i/5) hamming(s1, s2);
  		else jaro(s1, s2);
	    else for (int j = 0; j < 100; j++);
	}
    }
}