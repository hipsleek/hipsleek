public class Diff {
    // We assume that A and B have no repetitions.
 static void dif(int[] A, int[] B, int[] D){
    int k=0;
    int i=0;
    int l1=A.length;
    int l2=B.length;
    boolean found;
    while(i<l1){
        int j=0;
        found=false;
	while((j<l2)&&(!found)){
	  if(A[i]==B[j]) found=true;
	  else j++;
         }

	if (!found) {
            D[k]=A[i];
	    k++;
	}
      i++;
    }
 }

    public static void main(String[] args) {
	dif(new int[20],new int[20],new int[20]);
    }
}
