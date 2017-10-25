#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

int main() {
  int i, j;
  int length = __VERIFIER_nondet_int();
  if (length < 1 || length >= 2147483647 / sizeof(int)) length = 1;
  int *arr = alloca(length*sizeof(int));
  if (!arr) return 0;
  int *a = arr;
  /* i = *a; */
  /* *a = i; */
  /* *a =  *(arr + length - 1); */

  while (*a != *(arr + length - 1))
    /*@
      requires arr::AsegNE<k, length> & a=arr+k & k>=0 & k<=length
      ensures arr::AsegNE<k, length>;
     */
    {
      /* *a += *(arr + length - 1); */
      a++;
    }
  return 0;
}

/*
int main$()
{((((int length;
     int tmp);
    int_star arr);
   void_star tmp___0);
  {(((((tmp = (int v_nd_6_2021;
	       (v_nd_6_2021 = __VERIFIER_nondet_int$();
		v_nd_6_2021));
	length = tmp);
       (boolean v_bool_7_2039;
	(v_bool_7_2039 = {((int v_int_7_2026;
			    v_int_7_2026 = 1);
			   lt___$int~int(length,v_int_7_2026))};
	  if (v_bool_7_2039) {[LABEL! 112,0: length = 1]}
	  else
	    {[LABEL! 112,1: (boolean v_bool_7_2038;
			     (v_bool_7_2038 = {((int v_int_7_2037;
						 v_int_7_2037 = {((int v_int_7_2032;
								   (v_int_7_2032 = 2147483647;
								    (int v_int_7_2031;
								     v_int_7_2031 = 1)));
								  div___$int~int(v_int_7_2032,v_int_7_2031))});
						gte___$int~int(length,v_int_7_2037))};
			       if (v_bool_7_2038) [LABEL! 113,0: length = 1]
				 else [LABEL! 113,1: ]
			       ))]}
	  )));
      (tmp___0 = {((int v_int_8_2049;
		    v_int_8_2049 = {((int v_int_8_2044;
				      v_int_8_2044 = 1);
				     mult___$int~int(length,v_int_8_2044))});
		   __builtin_alloca$int(v_int_8_2049))};
	arr = {__cast_void_pointer_to_int_star__$void_star(tmp___0)}));
     (boolean v_bool_9_2064;
      (v_bool_9_2064 = {((int v_int_9_2062;
			  v_int_9_2062 = (int ){__make_not_of_int_star__$int_star(arr)});
			 __bool_of_int___$int(v_int_9_2062))};
	if (v_bool_9_2064) [LABEL! 124,0: (int v_int_9_2063;
					   (v_int_9_2063 = 0;
					    ret# v_int_9_2063))]
	  else [LABEL! 124,1: ]
	)));
    (int v_int_15_2065;
     (v_int_15_2065 = 0;
      ret# v_int_15_2065)))})}
*/
/*
  int main$()
  {((((int length;
  int tmp);
  int_star arr);
  void_star tmp___0);
  {(((
  (tmp = (int v_nd_6_1994;
  (v_nd_6_1994 = __VERIFIER_nondet_int$();
  v_nd_6_1994));
  length = tmp);
  (boolean v_bool_7_2012;
  (v_bool_7_2012 = {((int v_int_7_1999;
  v_int_7_1999 = 1);
  lt___$int~int(length,v_int_7_1999))};
  if (v_bool_7_2012) {[LABEL! 106,0: length = 1]}
  else
  {[LABEL! 106,1:
  (boolean v_bool_7_2011;
  (v_bool_7_2011 = {((int v_int_7_2010;
  v_int_7_2010 = {((int v_int_7_2005;
  (v_int_7_2005 = 2147483647;
  (int v_int_7_2004;
  v_int_7_2004 = 1)));
  div___$int~int(v_int_7_2005,v_int_7_2004))});
  gte___$int~int(length,v_int_7_2010))};
  if (v_bool_7_2011) [LABEL! 107,0: length = 1]
  else [LABEL! 107,1: ]
  ))]}
  )));
  (tmp___0 = {((int v_int_8_2022;
  v_int_8_2022 = {((int v_int_8_2017;
  v_int_8_2017 = 1);
  mult___$int~int(length,v_int_8_2017))});
  __builtin_alloca$int(v_int_8_2022))};
  arr = {__cast_void_pointer_to_int_star__$void_star(tmp___0)}));
  (int v_int_15_2027;
  (v_int_15_2027 = 0;
  ret# v_int_15_2027)))})}
*/
