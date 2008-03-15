class tnode {
int val;
tnode next;
}

public class test_java {
public static void main(String[] args) {
{ int  i=10;;
 System.out.print("i="); i = read_int(); ;
;
 System.out.println("You entered i=" + i); ;
 }

}
static int  read_int() 
{
{ int  i1=0 - 1;;

	try {
		java.io.InputStreamReader stdin =
				new java.io.InputStreamReader(System.in);
		java.io.BufferedReader console =
				new java.io.BufferedReader(stdin);

		String s1 = console.readLine();
		i1 = Integer.parseInt(s1);
	}
	catch (Exception e) {}
	;
;
return i1;
 }

}

}