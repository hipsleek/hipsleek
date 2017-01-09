public class MyString {
    private static char charSet[] = {'a','b','c','d','e','f','g','h','i','j','k','l','m',
				     'n','o','p','q','r','s','t','u','v','w','x','y','z'};
    private static int charSetLen = charSet.length;

    private char[] values;

    public MyString() {
	values = new char[0];
    }

    public MyString(int len, int n) {
	values = new char[len];

	for (int i = 0; i < len; i++)
	    values[i] = charSet[(i+n) % charSetLen];
    }

    public MyString(char s[]) {
	values = new char[s.length];

	for (int i = 0; i < values.length; i++)
	    values[i] = s[i];
    }

    public int length() {
	return values.length;
    }

    public char charAt(int index) {
	if (0 <= index && index < values.length)
	    return values[index];
	else throw new ArrayIndexOutOfBoundsException();
    }

    public void append(char c) {
	int len = values.length;
	char temp[] = new char[len + 1];
	for (int i = 0; i < len; i++) temp[i] = values[i];
	temp[len] = c;
	values = temp;
    }

    /*
    public String toString() {
	String s = "";
	for (int i = 0; i < values.length; i++)
	    s += values[i];
	return s;
    }
    */
}