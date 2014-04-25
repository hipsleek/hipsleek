
/*  -*- Last-Edit:  Fri Jan 29 11:13:27 1993 by Tarak S. Goradia; -*- */
/* $Log: tcas.c,v $
 * Revision 1.2  1993/03/12  19:29:50  foster
 * Correct logic bug which didn't allow output of 2 - hf
 * */

//#include <stdio.h>
relation dom(int[] a, int x, int y) == true.

//#define OLEV       600		/* in feets/minute */
//#define MAXALTDIFF 600		/* max altitude difference in feet */
//#define MINSEP     300          /* min separation in feet */
//#define NOZCROSS   100		/* in feet */
				/* variables */

//typedef int bool;

global int Cur_Vertical_Sep;
global bool High_Confidence;
global bool Two_of_Three_Reports_Valid;

global int Own_Tracked_Alt;
global int Own_Tracked_Alt_Rate;
global int Other_Tracked_Alt;

global int Alt_Layer_Value;		/* 0, 1, 2, 3 */
//int Positive_RA_Alt_Thresh[4];

global int Up_Separation;
global int Down_Separation;

				/* state variables */
global int Other_RAC;			/* NO_INTENT, DO_NOT_CLIMB, DO_NOT_DESCEND */
//#define NO_INTENT 0
//#define DO_NOT_CLIMB 1
//#define DO_NOT_DESCEND 2

global int Other_Capability;		/* TCAS_TA, OTHER */
//#define TCAS_TA 1
//#define OTHER 2

global bool Climb_Inhibit;		/* true/false */

//#define UNRESOLVED 0
//#define UPWARD_RA 1
//#define DOWNWARD_RA 2

void initialize(ref int[] arr)
  infer [arr]
  requires dom(arr, 0, 3)
  ensures true;
{
    arr[0] = 400;
    arr[1] = 500;
    arr[2] = 640;
    arr[3] = 740;
}

int ALIM (int[] arr,  int i)
 requires  dom(arr, 0, 3) & 0<=i<=3
 ensures   res=arr[i];
{
 int k =  arr[i];
 return k;
}

int iALIM (int[] arr,  int i)
  infer[i]
  requires  dom(arr, 0, 3) //& 0<=i<=3
 ensures   res=arr[i];
{
 int k =  arr[i];
 return k;
}
