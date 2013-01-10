/***********************************************/
/*  assgnment.5  Shu Z. A00042813 for CS453    */
/*  using the tokenizer and stream module      */
/*  print_tokens.c Code                        */
/***********************************************/

/***********************************************/
/* NAME:	print_tokens                   */
/* INPUT:	a filename                     */
/* OUTPUT:      print out the token stream     */
/* DESCRIPTION: using the tokenizer interface  */
/*              to print out the token stream  */
/***********************************************/
//#include <stdio.h>
//#include <ctype.h>
//#include <string.h>
//#include "tokens.h"
//#define TRUE 1
//#define FALSE 0

relation identical(int[] a, int[] b,int i,int j) == forall(k: k<i | k>j | a[k] = b[k]).
relation identicalOut(int[] a, int[] b,int i,int j) == forall(k: k>=i | k<=j | a[k] = b[k]).
relation identical_dist(int[] a, int[] b, int i, int j, int d) == 
  forall(k : (k<i & k>(j-d) | a[k] = b[k+d])).
// Two array are identical between i, j except m
  relation identicalEx1(int[] a, int[] b, int i, int j, int m) ==
forall(k: k<i | k>j | k=m | a[k] = b[k]).
//all array members between i, j is m 
relation identicalChar(int[] a, int i, int j, int m) == forall(k : (k<i | k>j | a[k] = m)).

  //token = int[]

void main(int argc)
  requires Term
  ensures true;
{  int [] fname;
   int [] tok;
   int tp;
   tp = 0;
   /*     if(argc==1)                  // if not given filename,take as
       {
        fname= (char *) malloc(sizeof(char));
        *fname = '\0';
       }
     else if(argc==2)
        fname= argv[1];
     else
       { fprintf(stdout, "Error!,please give the token stream\n");
         exit(0);
       }
    tp=open_token_stream(fname);  // open token stream
    tok=get_token(tp);
    while (is_eof_token(tok) ==FALSE) // take one token each time until eof
    {
       print_token(tok);
       tok=get_token(tp);
    }
   print_token(tok); // print eof signal
    exit(0);*/
}

/* stream.c code */

/***********************************************/
/* NMAE:	open_character_stream          */
/* INPUT:       a filename                     */
/* OUTPUT:      a pointer to chacracter_stream */
/* DESCRIPTION: when not given a filename,     */
/*              open stdin,otherwise open      */
/*              the existed file               */
/***********************************************/
int fopen(int fp)
  requires Term
  ensures res=2;

int open_character_stream(int fname)
requires Term
  ensures true;
{ int fp;
  if(fname == 0) //NULL 0
    fp=1; //stdin=1
  else//NULL 0
  {
    fp=fopen(fname);
    //fprintf(stdout, "The file %s doesn't exists\n",fname);
    //  exit(0);
  }
  return(fp);
}

/**********************************************/
/* NAME:	get_char                      */
/* INPUT:       a pointer to char_stream      */
/* OUTPUT:      a character                   */
/**********************************************/
int getc(int fp)
  requires Term
  ensures res>=-1 & res<=126;//-1 is EOF

int get_char(int fp)
  requires Term
  ensures res>=-1 & res<=126;//-1 is EOF
{ int ch;
  ch=getc(fp);
  return(ch);
}

/***************************************************/
/* NAME:      unget_char                           */
/* INPUT:     a pointer to char_stream,a character */
/* OUTPUT:    a character                          */
/* DESCRIPTION:when unable to put back,return EOF  */
/***************************************************/
int ungetc (int ch, int fp)
  requires ch>=-1 & ch<=126 & Term
  ensures res=ch or res=-1;

int unget_char(int ch, int fp)
  requires ch>=-1 & ch<=126 & Term
  ensures res=ch or res=-1;
{ int c;
  c=ungetc(ch,fp);
  if(c ==-1)//EOF -1
    {
     return(c);
    }
  else
     return(c);
}

/* tokenizer.c code */


//global int [] buffer;  /* 81 fixed array length MONI */ /* to store the token temporar */


//static int is_spec_symbol();
//static int is_token_end();
//static unget_error();
//static int is_keyword();
//static int is_identifier();
//static int is_num_constant();
//static int is_char_constant();
//static int is_str_constant();
//static int is_comment();
//static void print_spec_symbol();

/********************************************************/
/* NAME:	open_token_stream                       */
/* INPUT:       a filename                              */
/* OUTPUT:      a pointer to a token_stream             */
/* DESCRIPTION: when filename is EMPTY,choice standard  */
/*              input device as input source            */
/********************************************************/
int open_token_stream(int fname)
  requires Term
  ensures true;
{
 int fp;
 //strcmp(fname,"")==0)
 if(fname==0)
   fp=open_character_stream(0);//NULL 0
 else
    fp=open_character_stream(fname);
 return(fp);
}

/********************************************************/
/* NAME :	get_token                               */
/* INPUT: 	a pointer to the tokens_stream          */
/* OUTPUT:      a token                                 */
/* DESCRIPTION: according the syntax of tokens,dealing  */
/*              with different case  and get one token  */
/********************************************************/
void initialize(ref int[] buffer)
 requires dom(buffer,0,80) & Term
  ensures dom(buffer',0,80) & identicalChar(buffer', 0, 80, 0);

int get_token_loop1(int tp)
  requires Term
  ensures res>=-1 & res<=126 & res!=32 & res!=10;//32 blank, 10 new line

/*while (is_token_end(id,ch) == FALSE)// until meet the end character
   {
       i++;
       buffer[i]=ch;
       ch=get_char(tp);
   }

spec with termination
requires dom(buffer,0,80) & i>=0 & (id=0 |id=1 | id=2) &
  ch>=-1 & ch<=126
 case {
  ch=-1|ch=10 -> ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
  ch=34 -> case{
    id=1 -> ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
    id!=1 -> ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80& i'>=i;//'
  }
 ch=40 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
    id!=0 ->  ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80 & i'>=i;//'
  }
 ch=41 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
    id!=0 ->  ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80 & i'>=i;//'
  }
ch=91 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
    id!=0 ->  ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80 & i'>=i;//'
  }
ch=93 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
    id!=0 ->  ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80 & i'>=i;//'
  }
ch=96 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
    id!=0 ->  ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80 & i'>=i;//'
  }
ch=44 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
    id!=0 ->  ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80 & i'>=i;//'
  }
ch=32 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
    id!=0 ->  ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80 & i'>=i;//'
  }
ch=59 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
    id!=0 ->  ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80 & i'>=i;//'
  }
 ch!=-1&ch!=10&ch!=34&ch!=40&ch!=41&ch!=91&ch!=93&ch!=44&ch!=96&ch!=32&ch!=59->
   ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80 & i'>=i;// & flow __false;//'
}
*/
int get_token_loop21(ref int[] buffer, int tp, int id,int ch, ref int i)
 requires dom(buffer,0,80) & i>=0 & i<=80 & (id=0 |id=1 | id=2) & ch>=-1 & ch<=126 & Term[80-i]
 case {
  ch=-1|ch=10 -> ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
  ch=34 -> case{
    id=1 -> ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
    id!=1 -> ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80& i'>=i;//'
  }
 ch=40|ch=41|ch=91|ch=93|ch=44|ch=96|ch=32|ch=59 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i;//'
    id!=0 ->  ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80 & i'>=i;//'
  }
 ch!=-1&ch!=10&ch!=34&ch!=40&ch!=41&ch!=91&ch!=93&ch!=44&ch!=96&ch!=32&ch!=59->
   ensures dom(buffer',0,80) & res>=-1 & res<=126 & i'<80 & i'>=i;// & flow __false;//'
}
{
  assume (i<79);//for termination
  if(!(is_token_end(id,ch))){
    //  if (i>=79) return ch;
    i = i+ 1;
	//dprint;
    buffer[i]=ch;
    ch=get_char(tp);
    return get_token_loop21(buffer, tp, id, ch, i);
  }
  return ch;
}
                         /*
requires dom(buffer,0,80) & i>=0 & ch>=-1 & ch<=126 & identicalChar(buffer,i+1,80,0)
 case {
  ch=-1|ch=10 -> ensures dom(buffer',0,80) & res=ch  & i'<80 & i'=i & identicalChar(buffer',i',80,0) & buffer'[0]=buffer[0];//'v3
  ch=34 -> case{
    id=1 -> ensures dom(buffer',0,80) & res=ch  & i'<80 & i'=i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=1 -> ensures dom(buffer',0,80) & res=-2 & i'<80& i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
 ch=41 | ch=91 | ch=40 | ch=93 |ch=96 |ch=44 | ch=32 | ch=59  -> case {
    id=0 ->  ensures dom(buffer',0,80)  & res=ch & i'<80 & i'=i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=0 ->  ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
 ch!=-1&ch!=10&ch!=34&ch!=40&ch!=41&ch!=91&ch!=93&ch!=44&ch!=96&ch!=32&ch!=59->
   ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];// & flow __false;//'
}

requires dom(buffer,0,80) & i>=0 & ch>=-1 & ch<=126 & identicalChar(buffer,i+1,80,0)
 case {
  ch=-1|ch=10 -> ensures dom(buffer',0,80) & res=ch  & i'<80 & i'=i & identicalChar(buffer',i',80,0) & buffer'[0]=buffer[0];//'v3
  ch=34 -> case{
    id=1 -> ensures dom(buffer',0,80) & res=ch  & i'<80 & i'=i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=1 -> ensures dom(buffer',0,80) & res=-2 & i'<80& i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
 ch=41 -> case {
    id=0 ->  ensures dom(buffer',0,80)  & res=ch & i'<80 & i'=i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=0 ->  ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
  ch=91 -> case {
    id=0 ->  ensures dom(buffer',0,80)  & res=ch & i'<80 & i'=i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=0 ->  ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
  ch=40 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=0 ->  ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
ch=93 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=0 ->  ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
ch=96 -> case {
    id=0 ->  ensures dom(buffer',0,80) &  res=ch & i'<80 & i'=i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=0 ->  ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
ch=44 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=0 ->  ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
ch=32 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=0 ->  ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
ch=59 -> case {
    id=0 ->  ensures dom(buffer',0,80) & res=ch & i'<80 & i'=i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=0 ->  ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
 ch!=-1&ch!=10&ch!=34&ch!=40&ch!=41&ch!=91&ch!=93&ch!=44&ch!=96&ch!=32&ch!=59->
   ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];// & flow __false;//'
}
            */
int get_token_loop2(ref int[] buffer, int tp, int id,int ch, ref int i)
requires dom(buffer,0,80) & i>=0 & ch>=-1 & ch<=126 & identicalChar(buffer,i+1,80,0) & Term
 case {
  ch=-1|ch=10 -> ensures dom(buffer',0,80) & res=ch  & i'<80 & i'>i & identicalChar(buffer',i',80,0) & buffer'[0]=buffer[0];//'v3
  ch=34 -> case{
    id=1 -> ensures dom(buffer',0,80) & res=ch  & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=1 -> ensures dom(buffer',0,80) & res=-2 & i'<80& i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
 ch=41 | ch=91 | ch=40 | ch=93 |ch=96 |ch=44 | ch=32 | ch=59  -> case {
    id=0 ->  ensures dom(buffer',0,80)  & res=ch & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
    id!=0 ->  ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];//'
  }
 ch!=-1&ch!=10&ch!=34&ch!=40&ch!=41&ch!=91&ch!=93&ch!=44&ch!=96&ch!=32&ch!=59->
   ensures dom(buffer',0,80) & res=-2 & i'<80 & i'>i & identicalChar(buffer',i',80,0)& buffer'[0]=buffer[0];// & flow __false;//'
}
			 /*
{
  assume (i<79);//for termination
  if(!(is_token_end(id,ch))){
    //  if (i>=79) return ch;
    i = i+ 1;
    buffer[i]=ch;
    ch=get_char(tp);
    return get_token_loop2(buffer, tp, id, ch, i);
  }
  return ch;
}
			 */
                         /*
requires dom(buffer,0,80) &i=0 & id=0
 ensures (ch'=-1 & id'!=1) or (ch'=-1 & id'=1 & dom(buffer',0,80) & buffer'[i']=0) or (ch'=10) or (ch'=34 & id'=1) or
       (ch'=40) or (ch'=41) or (ch'=91) or (ch'=93) or (ch'=44) or (ch'=96) or (ch'=32 & id'=0) or (ch'=59 & id'=0)
       or (ch'=-2);//'not termination
// requires dom(buffer,0,80) &i=0 & id=0 ensures (buffer'[0]=59 & id'!=0) or buffer'[0]!=59; for version 4

requires dom(buffer,0,80) &i=0 & id=0
 ensures (ch'=-1 & i'=0) or (ch'=-1 & i'>0 & id'!=1)
or (ch'=-1 & id'=1 & dom(buffer',0,80) & buffer'[i']=0 & i'>0) or (ch'=10) or (ch'=34 & id'=1) or
       (ch'=40) or (ch'=41) or (ch'=91) or (ch'=93) or (ch'=44) or (ch'=96) or (ch'=32 & id'=0) or (ch'=59 & id'=0)
       or (ch'=-2);//'not termination
// requires dom(buffer,0,80) &i=0 & id=0 ensures (buffer'[0]=59 & id'!=0) or buffer'[0]!=59; for version 4

                          */
int[] get_token(int tp, ref int[] buffer, ref int i, ref int id, ref int ch)
requires dom(buffer,0,80) &i=0 & id=0 & Term
ensures (ch'=-1 & id'!=1) or (ch'=-1 & id'=1 & dom(buffer',0,80) & buffer'[i']=0) or (ch'=10) or (ch'=34 & id'=1) or
       (ch'=40 | ch'=41 | ch'=91 | ch'=93 | ch'=44 | ch'=96 | ch'=32 | ch'=59)
       or (ch'=-2);//'not termination
// requires dom(buffer,0,80) &i=0 & id=0 ensures (buffer'[0]=59 & id'!=0) or buffer'[0]!=59; //for version 4
{
  //int j;
  //int id=0;
  // int ch;
  int [] ch1;
  assume(dom(ch1',0,1));//'
  // for (j=0;j<=80;j++)          /* initial the buffer   */
  //    { buffer[j]='\0';}
  initialize(buffer);
  ch1[0]=0;
  ch1[1]=0;//'\0';
  ch=get_char(tp);
             // while(ch==' '||ch=='\n')      /* strip all blanks until meet characters */
                  //{
             //ch=get_char(tp);
             // }
   ch = get_token_loop1(tp);
             //  assume(ch=34);
   buffer[i]=ch;
   if(is_eof_token(ch)) return(buffer);
   if(is_spec_symbol(ch)) return(buffer);
   if(ch == 34)id=1;    /* prepare for string '"' 34*/
   if(ch ==59) id=2;    /* prepare for comment */
   ch=get_char(tp);
   // while (is_token_end(id,ch) == FALSE)/* until meet the end character */
   //{
             //   i++;
             //buffer[i]=ch;
             //ch=get_char(tp);
             //}
   ch = get_token_loop2(buffer, tp, id, ch, i);
	     //ch1[0]=ch;                        /* hold the end charcater          */
   if(is_eof_token(ch))       /* if end character is eof token    */
      { ch=unget_char(ch,tp);        /* then put back eof on token_stream */
        if(ch==-1) unget_error(tp);//EOF -1
         return buffer;
      }
   if(is_spec_symbol(ch))     /* if end character is special_symbol */
      { ch=unget_char(ch,tp);        /* then put back this character       */
        if(ch==-1) unget_error(tp);//EOF -1
        return buffer;
      }
   if(id==1)                  /* if end character is " and is string */
     { i = i + 1;                     /* case,hold the second " in buffer    */
       buffer[i]=ch;
        return buffer;
     }
     if(id==0) {
       if(ch==59)
                                  /* when not in string or comment,meet ";" */
       { ch=unget_char(ch,tp);       /* then put back this character         */
       if(ch==-1) unget_error(tp);//EOF -1
       return buffer;
     }}
  return buffer;                   /* return nomal case token             */
}

/*******************************************************/
/* NAME:	is_token_end                           */
/* INPUT:       a character,a token status             */
/* OUTPUT:	a BOOLEAN value                        */
/*******************************************************/
bool is_token_end(int str_com_id,int ch)
requires (str_com_id=0 | str_com_id=1|str_com_id=2)&ch>=-1 &ch<=126 & Term
case {
  ch=-1 ->  ensures res;
  ch=10 ->  ensures res;
  ch=34 -> case{
    str_com_id=1 -> ensures res;
    str_com_id!=1 -> ensures !res;
  }
  ch=59 -> case {
    str_com_id=0 -> ensures res;
    str_com_id!=0 -> ensures !res;
  }
  ch=91|ch=41|ch=40|ch=93|ch=44|ch=96|ch=32 -> case {
    str_com_id=0 -> ensures res;
    str_com_id!=0 -> ensures !res;
  }
  ch!=-1&ch!=10&ch!=34&ch!=40&ch!=41&ch!=91&ch!=93&ch!=44&ch!=96&ch!=32&ch!=59->ensures !res;
}
{ int [] ch1;  /* fixed array declaration MONI */
  assume(dom(ch1',0,1));//'
 ch1[0]=ch;
 ch1[1]= 0; //'\0'
 if(is_eof_token(ch)) return true; /* is eof token? */
 if(str_com_id==1)          /* is string token */
   { if(ch==34 || ch==10)   /* for string until meet another "'\n'10 '\"' 34*/
       return true;
     else
       return false;
   }

 if(str_com_id==2)    /* is comment token */
   { if(ch==10 /*|| ch==12 --v9*/)     /* for comment until meet end of line '\n' 10*/
        return true;
      else
        return false;
   }
if(is_spec_symbol(ch1[0])) return true; /* is special_symbol? */
             if(ch ==32 || ch==10 || ch==59 /*|| ch==12 --v8*/) return true;
                              /* others until meet blank 32 or tab or 59 */
 return false;               /* other case,return FALSE */
}

/****************************************************/
/* NAME :	token_type                          */
/* INPUT:       a pointer to the token              */
/* OUTPUT:      an integer value                    */
/* DESCRIPTION: the integer value is corresponding  */
/*              to the different token type         */
/****************************************************/
int token_type(int[] tok)
requires dom(tok, 0, 80)& tok[80]=0 & Term
ensures true;
{
  if(is_keyword(tok)) return 1; //keyword 1
  if(is_spec_symbol(tok[0])) return 2;//spec_symbol 2
  if(is_identifier(tok)) return 3; //identifier
  if(is_num_constant(tok)) return 41;//num_constant 41
  if(is_str_constant(tok)) return 42; //str_constant 42
 if(is_char_constant(tok)) return 43;//char_constant
 if(is_comment(tok)) return 5; //comment 5
 if(is_eof_token(tok[0])) return 6;//end
 return 0;                    /* else look as error token error 0*/
}

/****************************************************/
/* NAME:	print_token                         */
/* INPUT:	a pointer to the token              */
/* OUTPUT:      a BOOLEAN value,print out the token */
/*              according the forms required        */
/****************************************************/
void print_token(int[] tok)
requires dom(tok, 0, 80)& tok[80]=0 & Term
ensures true;
{ int type;
  type=token_type(tok);
  /*
 if(type==error)
   { //fprintf(stdout, "error,\"%s\".\n",tok);
   }
 if(type==keyword)
   {//fprintf(stdout, "keyword,\"%s\".\n",tok);
   }
 if(type==spec_symbol) print_spec_symbol(tok);
 if(type==identifier)
   {//fprintf(stdout, "identifier,\"%s\".\n",tok);
   }
 if(type==num_constant)
   {//fprintf(stdout, "numeric,%s.\n",tok);
   }
 if(type==str_constant)
   {//fprintf(stdout, "string,%s.\n",tok);
   }
 if(type==char_constant)
   {//tok=tok+1;
     //fprintf(stdout, "character,\"%s\".\n",tok);
   }
 if(type==end)
   //fprintf(stdout, "eof.\n");
   */
   }

/* the code for tokens judgment function */

/*************************************/
/* NAME:	is_eof_token         */
/* INPUT: 	a pointer to a token */
/* OUTPUT:      a BOOLEAN value      */
/*************************************/
bool is_eof_token(int tok)
	 //requires tok>=-1 & tok<=126 //dom(tok, 0, 1)
  requires Term
  case { 
  tok=-1-> ensures res;
  tok!=-1-> ensures !res;
}
{
  if( tok==-1) //EOF -1
      return true;
  else
      return false;
}

/*************************************/
/* NAME:	is_comment           */
/* INPUT: 	a pointer to a token */
/* OUTPUT:      a BOOLEAN value      */
/*************************************/
bool is_comment(int[] ident)
  requires dom(ident, 0, 80) & Term
  ensures true;
{
  if( (ident[0]) ==59 )   /* the char is 59   */
     return true;
  else
     return false;
}

/*************************************/
/* NAME:	is_keyword           */
/* INPUT: 	a pointer to a token */
/* OUTPUT:      a BOOLEAN value      */
/*************************************/
/*
case {
  str[0]=97 -> case {
    str[1]=110 -> case {
      str[2]=100 -> ensures true;
       str[2]!=100 -> ensures true;
    }
    str[1]!=110 -> ensures true;
  }
  str[0]=111 -> case {
    str[1]=114 ->  ensures true;
    str[1]!=114 -> ensures true;
  }
  str[0]=105 -> case {
    str[1]=102 ->  ensures true;
    str[1]!=102 -> ensures true;
  }
  str[0]!=97 & str[0]!=111 & str[0]!=105 -> ensures true;
}
*/
bool is_keyword(int[] str)
 requires dom(str, 0, 80) & Term
 ensures true;
{ // a 97 n110 d 100,0 111 r 114, i 105 f 102, x 120, l 108 m 109 b 98;= 61 >62
  /*
  if ((str[0] == 97 && str[1]==110 && str[2] == 100) || //"and"
  (str[0] == 111 && str[1]==114) ||//or
  (str[0] == 105 && str[1]==102) || //if
      (str[0] == 120 && str[1]==111 && str[2] == 114)|| //xor
      (str[0] == 108 && str[1]==97 && str[2] == 109 && str[3] == 100 && str[4]==97)|| //lamda
      (str[0] == 61 && str[1]==62)) //=>
      return true;
  else
      return false;
  */
  return true;
}

/*************************************/
/* NAME:	is_char_constant     */
/* INPUT: 	a pointer to a token */
/* OUTPUT:      a BOOLEAN value      */
/*************************************/
bool isalpha(int ch)
   requires Term
 case{
  ch < 65 -> ensures !res;
  ch>=65 & ch<=90 -> ensures res;
  ch>90 & ch<97 -> ensures !res;
  ch>=97 & ch<=122 -> ensures res;
  ch>122 -> ensures !res;
}

bool is_char_constant(int[] str)
requires dom(str, 0, 80) & Term
  ensures true;
{
  if (str[0]==35 && isalpha(str[1])) // #35
     return true;
  else
     return false;
}
/*************************************/
/* NAME:	is_num_constant      */
/* INPUT: 	a pointer to a token */
/* OUTPUT:      a BOOLEAN value      */
/*************************************/
bool isdigit(int ch)
   requires Term
 case{
  ch < 48 -> ensures !res;
  ch>=48 & ch<=57 -> ensures res;
  ch>57 -> ensures !res;
}

bool is_num_constant_loop(int[] str, ref int i)
  requires dom(str, 0, 80) & str[80]=0 & i>=1 & i<=80 & Term[80-i]
  ensures i'>=i;//'
{
  /*
  while ( *(str+i) != '\0' )   // until meet token end sign /
    {
      if(isdigit(*(str+i)))
        i++;
       else
         return(FALSE);
    }                         // end WHILE /
    return(TRUE);
  */
  if (str[i]!=0){
    if(isdigit(str[i])){
        i=i+1;
        return is_num_constant_loop(str, i);
    }
    else
      return false;
  }
  return true;
}

bool is_num_constant(int[] str)
  requires dom(str, 0, 80) & str[80]=0 & Term
  ensures true;
{
  int i=1;

  if ( isdigit(str[0])){
    return is_num_constant_loop(str,i);
  }
  else
   return false;               /* other return FALSE */
}

/*************************************/
/* NAME:	is_str_constant      */
/* INPUT: 	a pointer to a token */
/* OUTPUT:      a BOOLEAN value      */
/*************************************/
bool is_str_constant_loop(int[] str, ref int i)
         requires dom(str, 0, 80) & str[80]=0 & i>=1 & i<=80 & Term[80-i]
  case {
  i = 80 -> case {
     str[i]=0 -> ensures i'=i & !res;
     str[i]!=0 -> ensures true;//'
  }
  i< 80 -> case {
    str[i]=0 -> ensures i'=i & !res;
    str[i]=34 -> ensures i'=i & res;
    str[i]!=0 & str[i]!=34-> ensures i'>i;//'
  }
  i > 80 -> ensures true;
}
{
  /*
while (*(str+i)!='\0')  // until meet the token end sign /
         { if(*(str+i)=='"')
             return(TRUE);        // meet the second '"' /
           else
           i++;
         }               // end WHILE /
     return(FALSE);
   */
  if (str[i] != 0){
    if(str[i]==34) return true;
    else {
      i = i+1;
      return is_str_constant_loop(str,i);
    }
  }
  return false;
}

bool is_str_constant(int[] str)
  requires dom(str, 0, 80) & str[80]=0 & Term
  case {
  str[0]=34 -> ensures true;//(i'<81 & str[i']=34 & res) or (i'<81 & str[i']=0 & !res);//'
  str[0]!=34 -> ensures !res;
}
{
  int i=1;

  if ( str[0] ==34){//" 34
    return is_str_constant_loop(str, i);
  }
  else
    return false;       /* other return FALSE */
}
/*************************************/
/* NAME:	is_identifier         */
/* INPUT: 	a pointer to a token */
/* OUTPUT:      a BOOLEAN value      */
/*************************************/
bool is_identifier_loop(int[] str, ref int i)
requires dom(str, 0, 80) & str[80]=0 & i>=1 & i<=80 & Term[80-i]
  ensures i'>=i;//'
 {
   /*
     while(  *(str+i) !='\0' )   // unti meet the end token sign /
     {
       if(isalpha(*(str+i)) || isdigit(*(str+i)))
         i++;
       else
         return(FALSE);
     }      // end WHILE /
     return(TRUE);
    */
   if(str[i]!=0){
     if(isalpha(str[i]) || isdigit(str[i])){
       i = i+1;
       return is_identifier_loop(str,i);
     }
     else return false;
   }
   return true;
 }

bool is_identifier(int[] str)
  requires dom(str, 0, 80) & str[80]=0 & Term
  ensures true;
{
  int i=1;

  if ( isalpha(str[0]) ){
    return is_identifier_loop(str,i);
  }
  else
     return false;
}

/******************************************/
/* NAME:	unget_error               */
/* INPUT:       a pointer to token stream */
/* OUTPUT: 	print error message       */
/******************************************/
void unget_error(int fp)
 requires Term
 ensures true;


/*************************************************/
/* NAME:        print_spec_symbol                */
/* INPUT:       a pointer to a spec_symbol token */
/* OUTPUT :     print out the spec_symbol token  */
/*              according to the form required   */
/*************************************************/
//bool strcmp(str,"'")

void print_spec_symbol(int[] str)
 requires dom(str, 0, 80) & Term
 ensures true;
{
    if (str[0]==40){// (40
      // fprintf(stdout, "%s\n","lparen.");
      return;
    }
    if (str[0]==41)// ")"
    {
      //fprintf(stdout, "%s\n","rparen.");
      return;
    }
    if (str[0]==91)//"["
    {
      //printf(stdout, "%s\n","lsquare.");
      return;
    }
    if (str[0]==93)//"]"
    {
      //fprintf(stdout, "%s\n","rsquare.");
      return;
    }
    if (str[0]==44)//"'"
    {
      //fprintf(stdout, "%s\n","quote.");
      return;
    }
    if (str[0]==96)//"`"
    {
      //fprintf(stdout, "%s\n","bquote.");
      return;
    }

    //fprintf(stdout, "%s\n","comma.");
}


/*************************************/
/* NAME:        is_spec_symbol       */
/* INPUT:       a pointer to a token */
/* OUTPUT:      a BOOLEAN value      */
/*************************************/
// str=40 | str=41 | str=91 | str=93 | str=44 | str=96 -> ensures res;
bool is_spec_symbol(int str)
 requires Term
 case {
  str=40  -> ensures res;
  str=41  -> ensures res;
   str=91 -> ensures res;
 str=93  -> ensures res;
 str=44  -> ensures res;
 str=96 -> ensures res;
  str!=40 & str!=41 & str!=91 & str!=93 & str!=44 & str!=96 -> ensures !res;
}
{
     if (str==40){// (40
      return true;
    }
    if (str==41)// ")"
    {
      return true;
    }
    if (str==91)//"["
    {
      return true;
    }
    if (str==93)//"]"
    {
      return true;
    }
    if (str==44)//"'"
    {
      return true;
    }
    if (str==96)//"`"
    {
      return true;
    }
    return false;  /* others return FALSE */
}


