/*  -*- Last-Edit:  Mon Dec  7 10:31:51 1992 by Tarak S. Goradia; -*- */

//extern void	exit();
//# include <stdio.h>

//void	Caseerror();

//typedef char	bool;
//# define false 0
//# define true  1
//# define NULL 0

//# define MAXSTR 100
//# define MAXPAT MAXSTR

//# define ENDSTR  '\0'
//# define ESCAPE  '@'
//# define CLOSURE '*'
//# define BOL     '%'
//# define EOL     '$'
//# define ANY     '?'
//# define CCL     '['
//# define CCLEND  ']'
//# define NEGATE  '^'
//# define NCCL    '!'
//# define LITCHAR 'c'
//# define DITTO   -1
//# define DASH    '-'

//# define TAB     9
//# define NEWLINE 10

//# define CLOSIZE 1

//typedef char	character;
//typedef char string[MAXSTR];
/*
relation identical(int[] a, int[] b,int i,int j) == forall(k: k<i | k>j | a[k] = b[k]).
relation identical_dist(int[] a, int[] b, int i, int j, int d) == 
  forall(k : (k<i & k>(j-d) | a[k] = b[k+d])).
// Two array are identical between i, j except m
  relation identicalEx1(int[] a, int[] b, int i, int j, int m) ==
forall(k: k<i | k>j | k=m | a[k] = b[k]).
//all array members between i, j is m 
relation identicalChar(int[] a, int i, int j, int m) == forall(k : (k<i | k>j | a[k] = m)).
*/
int fgets(int [] s, int maxsize, int pstream)
  requires true
  ensures dom(s,0,maxsize) & s[maxsize]=0;

bool getline(int [] s, int maxsize)
  requires true
  ensures  dom(s,0,maxsize) & s[maxsize]=0;
{
    int result;
    result = fgets(s, maxsize, 1);//stdin
    return (result != 0);//NULL
}
bool addstr(int c, ref int [] outset, ref int j, int maxset)
  requires dom(outset,0,maxset) & maxset>=0
 case {
  j=maxset -> ensures dom(outset',0,maxset) & j'=j & !res;
  j<maxset -> requires j>=0
    ensures dom(outset',0,maxset) & j'=j+1 & outset'[j'-1]=c & res & j'<=maxset;//'
  j>maxset -> ensures true;//'
}
{
    bool result;
    if (j >= maxset)
	result = false;
    else {
      outset[j] = c;
      j = j + 1;
      result = true;
    }
    return result;
}

int esc(ref int[] s, ref int i)
  requires dom(s,0,100) & i>=0 & i<100
 case {
  s[i]!=27 -> ensures dom(s',0,100) & res=s[i] & s'=s & i'=i;//'
  s[i]=27 -> case {
    s[i+1]=0 -> ensures dom(s',0,100)& s'=s & res=27 & i'=i;//'
    s[i+1]=110 ->ensures dom(s',0,100)&res=10 & s'=s & i'=i+1;//'
    s[i+1]=9 ->ensures dom(s',0,100)& res=9 & s'=s & i'=i+1;//'
    s[i+1]!=0 & s[i+1]!=110 & s[i+1]!=9 -> ensures dom(s',0,100)& s'=s &
						       res=s[i+1]&i'=i+1;//'
  }
}
{
    int result;
    if (s[i] != 27)//ESCAPE
	result = s[i];
    else
      if (s[i + 1] == 0)//ENDSTR 0
        result = 27; //ESCAPE
      else {
        i = i + 1;
        if (s[i] == 110)// n 110
          result = 10;//NEWLINE 10
        else
          if (s[i] == 9)// t 9
            result = 9;//TAB
          else
            result = s[i];
      }
    return result;
}

bool isalpha(int ch)
   requires true
 case{
  ch < 65 -> ensures !res;
  ch>=65 & ch<=90 -> ensures res;
  ch>90 & ch<97 -> ensures !res;
  ch>=97 & ch<=122 -> ensures res;
  ch>122 -> ensures !res;
}

bool isdigit(int ch)
   requires true
 case{
  ch < 48 -> ensures !res;
  ch>=48 & ch<=57 -> ensures res;
  ch>57 -> ensures !res;
}

bool isalnum(int ch)
   requires true
 case{
  ch < 48 -> ensures !res;
  ch>=48 & ch<=57 -> ensures res;
  ch>57 & ch<65 -> ensures !res;
  ch>=65 & ch<=90 -> ensures res;
  ch>90 & ch<97 -> ensures !res;
  ch>=97 & ch<=122 -> ensures res;
  ch>122 -> ensures !res;
}
/*
{
  if(!isalpha(ch))
    if(!isdigit(ch)) // Check for digit and alpha
      return false;
  return true;
}
*/
void dodash_loop1(int[] src, ref int i, int [] dest, ref int j, int maxset,
		  ref int k, ref bool junk)
 requires dom(src,0,maxset) & dom(dest,0,maxset) & src[maxset]=0 &
                             i>=1 & i<maxset & maxset>=0 & j>=0 & j<=maxset
 case {
  k<=src[i+1] -> ensures j'>=j & j'<=maxset & i'=i; //'
  k>src[i+1] -> ensures j'=j & i'=i;//'
}
{
  if (k<=src[i+1]){
    junk = addstr(k, dest, j, maxset);
    k = k+1;
    dodash_loop1(src,i,dest,j, maxset, k, junk);
  }
}

void dodash(int delim, ref int[] src, ref int i, ref int [] dest, ref int j, int maxset)
  requires dom(src,0,100) & dom(dest,0,100) & src[100]=0 & i>=1 & i<=100 & maxset=100
                             & delim = 93 & j>=0 & j<=maxset
case{
  i=100 -> case {
    src[i]=0 -> ensures dom(src',0,maxset) & src'[maxset]=0 & dom(dest',0,maxset) & i'=i & j'=j;//'
    //arg'=arg & sub'=sub
    src[i]!=0-> ensures true;//unreachable
  }
  i<100 -> case {
    src[i]=delim -> ensures dom(src',0,maxset) & src'[maxset]=0 & dom(dest',0,100) & i'=i & j'=j;//'
    src[i]!=delim -> case {
      src[i-1]=27 -> ensures dom(src',0,maxset) & src'[maxset]=0 & dom(dest',0,100) & i'>=i & j'>=j & i'<=100 & j'<=maxset
                              ;//'can be more precise  & i'-i<100 & j'-j<=maxset
      src[i-1]!=27 -> case {
         src[i]!=45 -> ensures dom(src',0,maxset) & src'[maxset]=0 & dom(dest',0,100) & i'>=i & j'>=j &
                                                 i'<=100 & j'<=maxset;//'
         src[i]=45 -> case {
           j<=1 | src[i+1]=0 -> ensures dom(src',0,maxset) & src'[maxset]=0 & dom(dest',0,100) & i'>=i & j'>=j &
                                                 i'<=100 & j'<=maxset;//'
           j>1 & src[i+1]!=0 -> case {
              src[i-1]>=48 & src[i-1]<=57 & src[i+1]>=48 & src[i+1]<=57 -> case {
                src[i-1]<=src[i+1] -> ensures dom(src',0,maxset) & src'[maxset]=0 & dom(dest',0,100) & i'>=i&
                                           j'>=j & i'<=100 & j'<=maxset;//'
                src[i-1]>src[i+1] -> ensures dom(src',0,maxset) & src'[maxset]=0 & dom(dest',0,100) &
                                           i'>=i & j'>=j & i'<=100 & j'<=maxset;//'
              }
              src[i-1]<48 | src[i-1]>57 | src[i+1]<48 | src[i+1]>57->
                   ensures dom(src',0,maxset) & src'[maxset]=0 & dom(dest',0,100) & i'>=i & j'>=j & i'<=100 & j'<=maxset;//'
          }
        }
      }
    }
  }
  i>100 -> requires false ensures true;//unreachable
}
{
  int k;
  bool junk;
  int escjunk;

  if(src[i] != 0){ // ENDSTR 0
    if (src[i] != delim){
      if (src[i - 1] == 27){//ESCAPE 27
	    escjunk = esc(src, i);
	    junk = addstr(escjunk, dest, j, maxset);
      } else if(src[i] != 45){//DASH
        junk = addstr(src[i], dest, j, maxset);
      }
      else if (j <= 1 || src[i + 1] == 0){//ENDSTR
        junk = addstr(45, dest, j, maxset);//DASH
      }
      else if (isalnum(src[i - 1])){
        if (isalnum(src[i + 1])){
          if (src[i - 1] <= src[i + 1]) {
            k = src[i-1]+1;
            dodash_loop1(src,i,dest,j, maxset, k,junk);
            i = i + 1;
          }
        }
      }
      else {
        junk = addstr(45, dest, j, maxset);//DASH
      }

       i = i + 1;
      dodash(delim, src, i, dest, j, maxset);
    }
  }

}

bool getccl(int [] arg, ref int i, ref int[] pat, ref int j)
  requires dom(arg,0,100) & dom(pat,0,100) & arg[100]=0 & i>=0 & i<100 & j>=0 & j<=100
  ensures true;
{
    int	jstart;
    bool junk;

    i = i + 1;
    if (arg[i] == 94) {//NEGATE
      junk = addstr(33, pat, j, 100);//NCCL MAXPAT
      i = i + 1;
    } else
      junk = addstr(91, pat, j, 100); //CCL MAXPAT
    jstart = j;
    junk = addstr(0, pat, j, 100);//MAXPAT
    dodash(93, arg, i, pat, j, 100);//CCLEND MAXPAT
    pat[jstart] = j - jstart - 1;
    return (arg[i] == 93);//CCLEND
}

void stclose_loop(ref int[] pat, int lastj, ref int jp)
  requires dom(pat,0,100) & jp>=-1 & jp<=99 & lastj>=0 & lastj<=100
 case {
  jp>=lastj -> ensures dom(pat',0,100) & jp'<jp & jp'<lastj;//'
  jp<lastj -> ensures dom(pat',0,100) & jp'=jp;
} 
{
  int	jt;
  bool junk;
  assume(jp>0);
  if (jp >= lastj) {
    jt = jp + 1;//CLOSIZE
    junk = addstr(pat[jp], pat, jt, 100);//MAXPAT
    jp = jp -1;
    stclose_loop(pat, lastj, jp);
  }
}

void stclose(ref int[] pat, ref int j, int lastj)
  requires dom(pat,0,100) & lastj>=0 & lastj<=100 & j>=0 & j<=100
  ensures dom(pat',0,100) & j'=j+1 & pat'[lastj]=42;//'
{
    
    int	jp;
    jp = j - 1;

    stclose_loop(pat, lastj, jp);
    j = j + 1;//CLOSIZE
    pat[lastj] = 42;//CLOSURE
}

bool in_set_2(int c)
 case {
  c=37 -> ensures res; c=36 -> ensures res; c=42 -> ensures res;
  c!=37 & c!=36 &c!=42 -> ensures !res;
}
{
  return (c == 37 || c == 36 || c == 42);//BOL EOL CLOSURE
}      

bool in_pat_set(int c)
case {
  c=99 -> ensures res;
  c=37 -> ensures res;  c=36 -> ensures res;
  c=63 -> ensures res;  c=91 -> ensures res;
  c=33 -> ensures res; c=42 -> ensures res;
  c!=99 & c!=37 & c!=36 & c!=63 & c!=91 & c!=33 & c!=42 -> ensures !res;
}
{
  return (c == 99 || c == 37  || c == 36 || c == 63 
	     || c == 91 || c == 33 || c == 42);
 //LITCHAR BOL EOL ANY CCL NCCL CLOSURE
}

void makepat_loop(int[] arg, int start, int delim, int[] pat, ref bool done,
		 ref int escjunk, ref bool getres, int i, int j,
		 ref int lastj, ref int lj,ref bool junk)
  requires dom(arg, 0, 100) &dom(pat, 0, 100) & arg[100]=0 & j>=0 & j<=100 & i>=0 & i<=100 &
              lastj>=0 & lastj<=100
  ensures true;
{
  if(!done){
    if(arg[i] != delim){
      if(arg[i] != 0) {//ENDSTR
        lj = j;
        if ((arg[i] == 63))//ANY
          junk = addstr(63, pat, j, 100);//ANY MAXPAT
        else if (arg[i] == 37){
          if (i == start)//BOL
            junk = addstr(37, pat, j, 100);//BOL MAXPAT
        }
        else if (arg[i] == 36){
          if (arg[i+1] == delim)//EOL
            junk = addstr(36, pat, j, 100);//EOL MAXPAT
        }
        else if (arg[i] == 91){ //CCL
          getres = getccl(arg, i, pat, j);
          if (!getres) done = true;
          else done =false;
        }
        else if (arg[i] == 42){
          if(i > start){ //CLOSURE
            lj = lastj;
            if (in_set_2(pat[lj]))
              done = true;
            else
              stclose(pat, j, lastj);//increase j here
          }
        }
        else{
          junk = addstr(99, pat, j, 100);//LITCHAR MAXPAT
          escjunk = esc(arg, i);
          junk = addstr(escjunk, pat, j, 100);//MAXPAT
        }
        lastj = lj;
        if (!done)
          i = i + 1;
        //  makepat_loop(arg, start, delim, pat, done, escjunk, getres, i,j,lastj,lj, junk);
      }
    }
  }
}

int makepat(int[] arg, int start, int delim, ref int[] pat)
  requires dom(arg, 0, 100) &dom(pat, 0, 100) & arg[100]=0 &
start>=0 & start<=100 & delim=0
  ensures true;
{
    int	result;
    int	i, j, lastj, lj;
    bool done, junk;
    bool getres;
    int escjunk;

    j = 0;
    i = start;
    lastj = 0;
    done = false;

    makepat_loop(arg, start, delim, pat, done, escjunk, getres, i,j,lastj,lj, junk);

    junk = addstr(0, pat, j, 100); //ENDSTR MAXPAT
    if ((done) || (arg[i] != delim))
	result = 0;
    else
	if ((!junk))
	    result = 0;
	else
	    result = i;
    return result;
}

bool getpat(int[] arg,ref int[] pat)
  requires dom(arg, 0, 100) &dom(pat, 0, 100)& arg[100]=0
  ensures true;
{
    int	makeres;

    makeres = makepat(arg, 0, 0, pat);//ENDSTR
    return (makeres > 0);
}

void makesub_loop(ref int[] arg, int from, int delim, ref int[] sub,ref int i, ref int j)
 requires dom(arg,0,100) & dom(sub,0,100) & arg[100]=0 & i>=0 & from=0 &
	      delim=0 & j>=0 & j<=100
 case{
  i=100 -> case {
    arg[i]=0 -> ensures dom(arg',0,100) & arg'[100]=0 & dom(sub',0,100) & i'=i & j'=j;//'
    //arg'=arg & sub'=sub
    arg[i]!=0-> ensures true;//unreachable
  }/*
  i=99 -> case {
    arg[i]=0 -> ensures dom(arg',0,100) & arg'[100]=0 & dom(sub',0,100) & i'=i & j'=j;//'
    //arg'=arg & sub'=sub
    arg[i]=38-> ensures dom(arg',0,100) & arg'[100]=0 & dom(sub',0,100)
         & i'>i & j'>=j & i'<=100;//'
    arg[i]=27 ->case{
      arg[i+1]=0 ->ensures dom(arg',0,100)&arg'[100]=0 & dom(sub',0,100)&i'>i & j'>=j
                & i'<=100 ;//'
    //arg'=arg & sub'=sub 100
      arg[i+1]!=0 ->ensures true;//unreachable
    }
    arg[i]!=0&arg[i]!=38&arg[i]!=27-> ensures dom(arg',0,100) & arg'[100]=0 &
	dom(sub',0,100) & i'>i & j'>=j & i'<=100;//'
    }*/
  i<100 -> case {
    arg[i]=0 -> ensures dom(arg',0,100)& arg'[100]=0 & dom(sub',0,100)
          & i'=i & j'=j;//'
    //arg'=arg & sub'=sub
    arg[i]=38 -> ensures dom(arg',0,100) & arg'[100]=0 & dom(sub',0,100)
         & i'>i & j'>=j & i'<=100;//'
    arg[i]=27 ->case{
      arg[i+1]=0 ->ensures dom(arg',0,100)&arg'[100]=0 & dom(sub',0,100)&i'>i
							     & j'>=j& i'<=100;//'
    //arg'=arg & sub'=sub 100
      arg[i+1]!=0 ->ensures dom(arg',0,100)&arg'[100]=0 & dom(sub',0,100)&i'>i+1 
							       & j'>=j&i'<=100;//'
    }
     arg[i]!=0&arg[i]!=38&arg[i]!=27-> ensures dom(arg',0,100)&arg'[100]=0 & 
				  dom(sub',0,100)&i'>i & j'>=j& i'<=100;//'
  }
  i>100 -> requires false ensures true;//unreachable
}
{
  int escjunk;
  // assume(i=1);
  //assume(arg[1]=38);
  if(arg[i] != 0){//ENDSTR
    if (arg[i] != delim){
      if (arg[i] == 38)//'&'
        addstr(-1, sub, j, 100);//DITTO  MAXPAT j++ here
      else {
        escjunk = esc(arg, i);
        addstr(escjunk, sub, j, 100);//MAXPAT j++ here
      }
      i = i + 1;
      makesub_loop(arg, from, delim, sub,i,j);
    }
  }
}

int makesub(int[] arg, int from, int delim, ref int[] sub)
  requires dom(arg,0,100) & dom(sub,0,100) & arg[100]=0 & from=0 & delim=0
  ensures true;
{
    int  result;
    int	i, j;
    bool junk;

    j = 0;
    i = from;

    makesub_loop(arg, from, delim, sub,i,j);

    if (arg[i] != delim) //it means arg[i]=0
      result = 0;
    else {
      junk = addstr(0, sub, j, 100);//ENDSTR  MAXPAT
      if (!junk)
        result = 0;
      else
        result = i;
    }
    return result;
}

bool getsub(int[] arg, ref int[] sub)
  requires dom(arg,0,100) & dom(sub,0,100) & arg[100]=0
  ensures true;
{
    int	makeres;

    makeres = makesub(arg, 0, 0, sub);//ENDSTR
    return (makeres > 0);
}
                                //pat[offset]
void locate_loop(int c, ref int[] pat, int offset, ref int i, ref bool flag)
requires dom(pat,0,100) & offset>=0 & offset<=100 & (i <= offset+pat[offset]) & (offset+pat[offset]<100) & !flag
 case{
  i>offset -> case {
    c=pat[i] -> ensures dom(pat',0,100) & flag' & i'>offset;//'
    c!=pat[i] -> ensures dom(pat',0,100) & (flag' & i'>offset)|(!flag' & i'=offset);//'
  }
  i<=offset -> case {
    c=pat[i] -> ensures dom(pat',0,100) & !flag' & i'=i;//'for v6
    c!=pat[i] -> ensures dom(pat',0,100) & !flag' & i'=i;//'
  }
}
{
  if(i > offset){ //v6 i>= offset
     if (c == pat[i]) {
       flag = true;
       //i = offset;
       return;
     } else
       i = i - 1;
     locate_loop(c,pat,offset,i,flag);
   }
}

bool locate(int c, int[] pat, int offset)
  requires dom(pat,0,100) & (offset+1<100) & offset>=0
  case {
  pat[offset+1]=c-> ensures res;
  pat[offset+1]!=c-> ensures !res;
}
/*
{
  int	i;
  bool flag;

  flag = false;
  i = offset + 2;//pat[offset];

  locate_loop(c,pat,offset,i,flag);
  return flag;
}
*/

bool omatch(int [] lin, ref int i, int[] pat, int j)
  requires dom(lin,0,100) & dom(pat,0,100) & i>=0 & i<=100 & j>=0 & j<98
 case{
lin[i]=0 -> ensures !res;
lin[i]!=0 -> case {
  pat[j]=99 -> ensures true; pat[j]=37 -> ensures true;
  pat[j]=36 -> case {//v24, v25
   lin[i]=10-> ensures res;
   lin[i]!=10-> ensures !res;
  }
  pat[j]=63 -> ensures true;  pat[j]=91 -> ensures true;
  pat[j]=33 -> case {
    lin[i]!=10 -> case{
       pat[j+1+1]=lin[i]-> ensures !res;
       pat[j+1+1]!=lin[i]-> ensures res;
    }
    lin[i]=10 -> ensures !res;
  }
  pat[j]=42 -> ensures true;
  pat[j]!=99 & pat[j]!=37 & pat[j]!=36 & pat[j]!=63 & pat[j]!=91 & pat[j]!=33 &
   pat[j]!=42 -> ensures !res;//error
 }
}
{
    int	advance;
    bool result;

    advance = -1;
    if (lin[i] == 0)//ENDSTR
      result = false;
    else {
      if (!in_pat_set(pat[j])){
	//(void)fprintf(stdout, "in omatch: can't happen\n");
	//  abort();
        return false;
      } else {
        if (pat[j] == 99) {	//LITCHAR
          if (lin[i] == pat[j + 1])
            advance = 1;
        }
        else if (pat[j] == 37) {//BOL
          if (i == 0)
            advance = 0;
        }
        else if (pat[j] == 63) {//ANY
          if(lin[i] != 10)//NEWLINE
            advance = 1;
        }
        else if (pat[j] == 36) {//EOL
          if (lin[i] == 10)//NEWLINE
            advance = 0;
        }
        else if (pat[j] == 91) {//CCL
          if (locate(lin[i], pat, j + 1))
            advance = 1;
        }
        else if (pat[j] == 33) {//NCCL
          if (lin[i] != 10) //NEWLINE
            if (!locate(lin[i], pat, j+1))
              advance = 1;
        }
        else {
          // Caseerror(pat[j]);
          return false;//requires ... this case ensure true & __Error
        };
      }
    }
    if ((advance >= 0))
      {
        i = i + advance;
        result = true;
      } else
      result = false;
    return result;
}


int patsize(ref int [] pat, int n)
  requires dom(pat,0,100) & n>=0 & n<99
case {
  pat[n]=99 -> ensures res=2;
  pat[n]=37 -> ensures res=1;  pat[n]=36 -> ensures res=1;
  pat[n]=63 -> ensures res=1;  pat[n]=91 -> ensures res=pat[n+1]+2;
  pat[n]=33 -> ensures res=pat[n+1]+2; pat[n]=42 -> ensures res=1;
  pat[n]!=99 & pat[n]!=37 & pat[n]!=36 & pat[n]!=63 & pat[n]!=91 & pat[n]!=33 & pat[n]!=42 -> ensures res=-1;//error
}
{
    int size;
    if (!in_pat_set(pat[n])) {
      //(void)fprintf(stdout, "in patsize: can't happen\n");
      //abort();
      return -1;
    } else
      if (pat[n] == 99){ //LITCHAR
        size = 2;
      }
      else if (pat[n] == 37 || pat[n] == 36 || pat[n] == 63){//BOL EOL ANY
        size = 1;
      }
      else if (pat[n] == 91 || pat[n] == 33){//CCL NCCL
	    size = pat[n + 1] + 2;
      }
      else if (pat[n] == 42){// CLOSURE:
        size = 1;//CLOSIZE
      }
      else{
	//Caseerror(pat[n]);
        size = -1;
      }
    return size;
}

/*
void amatch_loop1(int[] lin, ref int offset, ref int[] pat, int j, ref int i,
	   ref int k, ref bool result, ref bool done)
  requires true
  ensures true;

{
  if(!done) {
    if (lin[i] != 0) {//ENDSTR
      result = omatch(lin, i, pat, j);
      if (!result)
        done = true;
      amatch_loop1(lin, offset, pat, j, i, k, result, done);
    }
  }
}

void amatch_loop2(int[] lin, ref int offset, ref int[] pat, int j, ref int i,
	   ref int k, ref bool result, ref bool done)
  requires true
  ensures true;
{
  if (!done) {
    if(i >= offset) {
      k = amatch(lin, i, pat, j + patsize(pat, j));
      if ((k >= 0))
	done = true;
      else
	i = i - 1;
       amatch_loop2(lin, offset, pat, j, i, k, result, done);
    }
  }
}
*/
  /*
void amatch_loop(int[] lin, ref int offset, ref int[] pat, int j, ref int i,
	   ref int k, ref bool result, ref bool done)
  requires true
  ensures true;
{
  if (!done){
    if(pat[j] != 0){//ENDSTR
      if ((pat[j] == 42)) {//CLOSURE
        j = j + patsize(pat, j);
        i = offset;

        amatch_loop1(lin, offset, pat, j, i, k, result, done);

        done = false;

        amatch_loop2(lin, offset, pat, j, i, k, result, done);

        offset = k;
        done = true;
      } else {
        result = omatch(lin, offset, pat, j);
        if ((!result)) {
          offset = -1;
          done = true;
        } else
          j = j + patsize(pat, j);
      }
      amatch_loop(lin, offset, pat,j, i, k, result, done);
    }
  }
}
*/

int amatch(int[] lin, int offset, ref int[] pat, int j)
  requires true
  ensures res>=-1 & res<=100;
/*
{
    int	i, k;
    bool result, done;

    done = false;
    amatch_loop(lin, offset, pat,j, i, k, result, done);
    return offset;
}
*/
void putsub(int [] lin, int s1, int s2, int[] sub)
  requires dom(sub,0,100)
  ensures true;
{
    int	i;
    int		j;

    i = 0;
    // while ((sub[i] != 0)) {//ENDSTR
      if ((sub[i] == -1))//DITTO
	/*	for (j = s1; j < s2; j++) 
	  {
	    fputc(lin[j],stdout);
	  }	
      else	
	{
	    fputc(sub[i],stdout);
	    }*/
	i = i + 1;
	// }
}


void subline_loop(int [] lin, ref int[] pat, int[] sub, ref int i,
		  ref int lastm, ref int m)
requires dom(lin,0,100) & lin[100]=0 & i>=0 & i<=100  & m>=-1 & m<=100 &
  dom(sub,0,100)
case {
  i=100 -> case {
    lin[100]=0 -> ensures (i'=i);
    lin[100]!=0 -> ensures true;//'
  }
  i<100 -> ensures (i'>=0 & i'<=100);
  i>100 -> ensures true;
}
{
  if (lin[i] != 0){//ENDSTR
    m = amatch(lin, i, pat, 0);
    if(m >= 0){
      if (lastm != m){//v3
        putsub(lin, i, m, sub);
        lastm = m;
      }
    }
    if ((m == -1) || (m == i)) {
      //fputc(lin[i],stdout);
      i = i + 1;
    } else
      i = m;
    subline_loop(lin,pat,sub, i,lastm, m);
  }
}

void subline(int [] lin, ref int[] pat, ref int[] sub)
  requires dom(lin,0,100) & lin[100]=0 & dom(sub,0,100)
  ensures true;
{
  int i, lastm, m=-1;

  lastm = -1;
  i = 0;
  subline_loop(lin,pat,sub, i,lastm, m);
}

void change(ref int[] pat,ref int[] sub)
  requires dom(sub,0,100)
  ensures true;
{
    int[]  line;
    bool result;
    
    result = getline(line, 100);//MAXSTR
    // while ((result)) {
	subline(line, pat, sub);
	result = getline(line, 100);//MAXSTR
	//}
}

void exit(int i)
  requires true
  ensures true;

int main(int argc)
  requires true
  ensures true;
{
   int[] pat, sub;
   assume (dom(pat',0,100));
   assume (dom(sub',0,100));
   bool result;

   if (argc < 2) 
   {
     // (void)fprintf(stdout, "usage: change from [to]\n");
     exit(1);
   };

   //result = getpat(, pat);
   if (!result)
   {
     // (void)fprintf(stdout, "change: illegal \"from\" pattern\n");
       exit(2);
   }

   if (argc >= 3)
   {
     //result = getsub(argv[2], sub);
       if (!result)
       {
	 //(void)fprintf(stdout, "change: illegal \"to\" string\n");
	   exit(3);
       }
   } else
   {
       sub[0] = 0;
   }
   
   //change(pat, sub);
   return 0;
}

void Caseerror(int n)
  requires true
  ensures true;
{
  //(void)fprintf(stdout, "Missing case limb: line %d\n", n);
  exit(4);
}
