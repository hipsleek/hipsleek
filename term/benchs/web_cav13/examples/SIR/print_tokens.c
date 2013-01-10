

//# include <ctype.h>

//# define START  5
//# define TRUE  1
//# define FALSE 0

//typedef int BOOLEAN;
//typedef char *string;

//# include <stdio.h>
//# include "tokens.h"
// Two array are identical between i, j
relation identical(int[] a, int[] b,int i,int j) == forall(k: k<i | k>j | a[k] = b[k]).
relation identical_dist(int[] a, int[] b, int i, int j, int d) == 
  forall(k : (k<i & k>(j-d) | a[k] = b[k+d])).
// Two array are identical between i, j except m
  relation identicalEx1(int[] a, int[] b, int i, int j, int m) ==
forall(k: k<i | k>j | k=m | a[k] = b[k]).
//all array members between i, j is m 
relation identicalChar(int[] a, int i, int j, int m) == forall(k : (k<i | k>j | a[k] = m)).

data token {
  int token_id;
  int [] token_string;//80
}

data cstream{
  int fp;  /* File pointer to stream */
  int stream_ind; /* buffer index */
  int [] stream;  /* buffer for the file 80*/
}

void main(int argc)
  requires Term
  ensures true;
{
      token token_ptr;
      cstream stream_ptr;
      int filename;
      //if(argc>2)
      //{
      //   fprintf(stdout, "The format is print_tokens filename(optional)\n");
      //    exit(1);
      //}
      // stream_ptr=open_token_stream(argv[1]);

      //stream_ptr=open_token_stream(filename);

      //while(!is_eof_token((token_ptr=get_token(stream_ptr))))
      //          print_token(token_ptr);
      //print_token(token_ptr);
      //exit(0);

      // token_ptr=get_token(stream_ptr);
      //is_eof_token(token_ptr);
      //print_token(token_ptr);
}



/* *********************************************************************
       Function name : open_character_stream
       Input         : filename 
       Output        : charactre stream.
       Exceptions    : If file name doesn't exists it will
                       exit from the program.
       Description   : The function first allocates the memory for 
                       the structure and initilizes it. The constant
                       START gives the first character available in
                       the stream. It ckecks whether the filename is
                       empty string. If it is it assigns file pointer
                       to stdin else it opens the respective file as input.
 * ******************************************************************* */

cstream open_character_stream(int FILENAME)
  requires Term
  ensures true;
{
      cstream stream_ptr;
      int [] s;
      assume dom(s', 0, 80);//'
      s[5]=0;
      //stream_ptr=(character_stream)malloc(sizeof(struct stream_type));
      //stream_ptr->stream_ind=START;5
      //stream_ptr->stream[START]='\0';
      stream_ptr = new cstream(-1,5,s);
      if(FILENAME == 0)
	stream_ptr.fp=1;//stdin 1
      else stream_ptr.fp=2;
	//if((stream_ptr->fp=fopen(FILENAME,"r"))==NULL)
	//  {
        //       fprintf(stdout, "The file %s doesn't exists\n",FILENAME);
        //       exit(0);
        //   }
      return(stream_ptr);
}

/* *********************************************************************
   Function name : get_char
   Input         : charcter_stream.
   Output        : character.
   Exceptions    : None.
   Description   : This function takes character_stream type variable 
                   as input and returns one character. If the stream is
                   empty then it reads the next line from the file and
                   returns the character.       
 * ****************************************************************** */
int fgets(ref int [] s, int end, int fp, ref int line_num)
 requires Term
 ensures dom(s',0,80) & s'[80]=0 & res=1 & line_num'=line_num+1;
 //ensures dom(s',0,80) & s'[80]=0 & s'[5]=-2 & res=0;

int get_char(ref cstream stream_ptr, ref int line_num)
  requires stream_ptr::cstream<fp,sind,s> & dom(s,0,80) & sind>=0 & sind<=80 & s[80]=0 & Term
  case{
    sind=80 -> ensures stream_ptr'::cstream<fp,sind1,s1> & dom(s1,0,80) & 
              (sind1=6) & res=s1[5] & s1[80]=0 & //'res=-2 or s1[5]
			  line_num'=line_num+1;
    sind<80 ->
    case {
      s[sind]=0 -> ensures stream_ptr'::cstream<fp,sind1,s1> & dom(s1,0,80) & 
	             (sind1=6) & res=s1[5] & s1[80]=0 & //'res=-2 or s1[5]
				 line_num'=line_num+1;
      s[sind]!=0 -> ensures stream_ptr'::cstream<fp,sind1,s> & 
	             (sind1=sind+1)& sind1>=1 & sind1<=80 & res=s[sind] &
				 line_num'=line_num;
    }
    sind>80 -> ensures true; //unreachable
 }
{
  if(stream_ptr.stream[stream_ptr.stream_ind] == 0) //'\0'
  {
    if(fgets(stream_ptr.stream,80-5,stream_ptr.fp,line_num) == 0)//START 5
      // Fix bug: add -START - hf - NULL 0/
      stream_ptr.stream[5]=-2;//EOF -2 START= 5
    stream_ptr.stream_ind=5;//START 5
  }
  int r = stream_ptr.stream[stream_ptr.stream_ind];
  stream_ptr.stream_ind = stream_ptr.stream_ind + 1;
  return r;
}

/* *******************************************************************
   Function name : is_end_of_character_stream.
   Input         : character_stream.
   Output        : Boolean value.
   Description   : This function checks whether it is end of character
                   stream or not. It returns BOOLEANvariable which is 
                   true or false. The function checks whether the last 
                   read character is end file character or not and
                   returns the value according to it.
 * ****************************************************************** */

bool is_end_of_character_stream(cstream stream_ptr)
  requires stream_ptr::cstream<fp,sind,s> & dom(s,0,80) & sind>=1 & sind<=80 & s[80]=0 & Term
 case{
   s[sind-1]=-2 -> ensures stream_ptr::cstream<fp,sind,s> & res;
   s[sind-1]!=-2 -> ensures stream_ptr::cstream<fp,sind,s> & !res;
 }
{
  int ind = stream_ptr.stream_ind-1;
  if(stream_ptr.stream[ind] == -2)//EOF -2
    return true;
  else
    return false;
}

/* *********************************************************************
   Function name : unget_char
   Input         : character,character_stream.
   Output        : void.
   Description   : This function adds the character ch to the stream. 
                   This is accomplished by decrementing the stream_ind
                   and storing it in the stream. If it is not possible
                   to unget the character then it returns
 * ******************************************************************* */
void unget_char(int ch, ref cstream stream_ptr)
  requires stream_ptr::cstream<fp,sind,s> & sind>=0 & sind<=80 & dom(s,0,80) & s[80]=0 & Term
 case {
  sind=0 ->ensures stream_ptr'::cstream<fp,sind,s>;//'
  sind>0 ->ensures stream_ptr'::cstream<fp,sind1,s1> & sind1 = sind-1 & dom(s1,0,80) &
 s1[80]=0 & identicalEx1(s1,s,0,79,sind1) & s1[sind1]=ch & sind1>=0 & sind1<=79;//'
  sind<0 ->ensures true;
  }
{
  if(stream_ptr.stream_ind != 0){
    int inx;
    stream_ptr.stream_ind = stream_ptr.stream_ind - 1;
    inx = stream_ptr.stream_ind;
    stream_ptr.stream[inx]=ch;
  }
  return;
}

/* *******************************************************************
   Function name : open_token_stream
   Input         : filename
   Output        : token_stream
   Exceptions    : Exits if the file specified by filename not found.
   Description   : This function takes filename as input and opens the
                   token_stream which is nothing but the character stream.
                   This function allocates the memory for token_stream 
                   and calls open_character_stream to open the file as
                   input. This function returns the token_stream.
 * ****************************************************************** */

cstream open_token_stream(int FILENAME)
  requires Term
  ensures true;
{
    cstream token_ptr;
  
    //token_ptr=(token_stream)malloc(sizeof(struct token_stream_type));
    token_ptr =open_character_stream(FILENAME);/* Get character
                                                             stream  */
    return(token_ptr);
}

/* ********************************************************************
   Function name : get_token
   Input         : token_stream
   Output        : token
   Exceptions    : none.
   Description   : This function returns the next token from the
                   token_stream.The type of token is integer and specifies 
                   only the type of the token. DFA is used for finding the
                   next token. cu_state is initialized to zero and charcter
                   are read until the the is the final state and it
                   returns the token type.
* ******************************************************************* */
/*
case{
  cu_state=31 -> case {
    ch=62 ->  case {
      token_ind <80 -> ensures token_ptr'::token<id,s1> & dom(s1,0,80) & s1[0]=0
                 & res=token_ptr'& cu_state'=31 & id=32;//'v1
      token_ind>=80 -> ensures true;
      //token_ind>80 -> ensures true;
    }
    ch!=62 -> ensures true;
  }
   cu_state=5 -> case {
    ch=97 -> case{
      token_ind <80 -> case {
	s[sind]=98-> ensures tstream_ptr'::cstream<_,sind1,_> & cu_state'=6 & sind1=sind+1;//'v3
        s[sind]!=98 -> ensures true;
      }
      token_ind>=80 -> ensures true;
      // token_ind>80 -> ensures true;
    }
    ch!=97 -> ensures true;
    }
  cu_state=0 -> case {
    ch=105 -> case{
      token_ind <80 -> ensures cu_state'=12;//'v2
      token_ind>=80 -> ensures true;
      //token_ind>80 -> ensures true;
    }
    ch=59 -> case{
      token_ind <80 -> ensures cu_state'=0 & token_ind'=0;//'v2
      token_ind>=80 -> ensures true;
      //token_ind>80 -> ensures true;
    }
    ch!=105&ch!=59 -> ensures true;
  }
  cu_state!=31 & cu_state!=0 & cu_state!=5-> ensures true;
 }
 ***********************
(cu_state=0|
      cu_state=1|cu_state=2|cu_state=3|cu_state=4|cu_state=5|cu_state=6|cu_state=8|cu_state=9|cu_state=10|cu_state=11|
      cu_state=12|cu_state=13|cu_state=13|cu_state=14|cu_state=15|cu_state=16|cu_state=17|cu_state=18|cu_state=26|
      cu_state=31|cu_state=32|cu_state=51|cu_state=52|cu_state=54)
 */
token get_token_loop(ref cstream tstream_ptr,ref token token_ptr, ref int ch,ref int cu_state,ref int token_ind)
 requires tstream_ptr::cstream<fp,sind,s>*token_ptr::token<_,ts> & dom(s,0,80) & s[80]=0 & sind>=1 & sind<=80 & cu_state>=0 & cu_state<=54
		    & token_ind>=0 & token_ind<=80 & dom(ts,0,80) & Term
case{
   token_ind<80 -> case {
     cu_state=31 -> case {
       ch=62 ->  ensures token_ptr'::token<id,s1> & dom(s1,0,80) & s1[0]=0
                 & res=token_ptr'& cu_state'=31 & id=32;//'v1
       ch!=62 -> requires false ensures true;
     }
     cu_state=5 -> case {
       ch=97 ->  case {
	s[sind]=98-> ensures tstream_ptr'::cstream<_,sind1,_> & cu_state'=6 & sind1=sind+1;//'v3
        s[sind]!=98 -> requires false ensures true;
      }
       ch!=97 ->requires false ensures true;
     }
     cu_state=0 -> case {
       ch=105 ->  ensures cu_state'=12;//'v2
       ch=59 -> ensures cu_state'=0 & token_ind'=0;//'v5
       ch!=105&ch!=59 -> requires false ensures true;
     }
     cu_state!=0 & cu_state!=5 & cu_state!=31 -> requires false ensures true;
   }
   token_ind>=80 -> ensures cu_state'=cu_state;//'
 }
{
  int [] token_str; /* This buffer stores the current token */
  int next_st;

  assume (dom(token_str', 0, 80));//'
             //assume token_str'[80]=0;
  if(token_ind < 80) /* ADDED ERROR CHECK - hf */{
    token_str[token_ind]=ch;
    token_ind = token_ind + 1;
    assume(ch>=0);
    assume(ch<=126);
    next_st=next_state(cu_state,ch);//next_st may be -1 here but token_index=1
  }
  else {
    next_st = -1; /* - hf */
  }
    if (next_st == -1) { /* ERROR or EOF case */
    return (error_or_eof_case(tstream_ptr, 
			     token_ptr,cu_state,token_str,token_ind,ch));
  } else if (next_st == -2) {/* This is numeric case. */
    return(numeric_case(tstream_ptr,token_ptr,ch,
			token_str,token_ind));
  } else if (next_st == -3) {/* This is the IDENTIFIER case */
    token_ptr.token_id=17;//IDENTIFIER
    unget_char(ch,tstream_ptr);
    token_ind = token_ind-1;
    get_actual_token(token_str,token_ind);
    strcpy(token_ptr.token_string,token_str);
    return(token_ptr);
  }
  //keyword
    if (next_st == 6 || next_st == 9 || next_st == 11 /*|| next_st == 12*/ || next_st == 13 ||
      next_st == 16 ){
    ch=get_char(tstream_ptr,0);
    if(check_delimiter(ch)) {
      token_ptr.token_id=keyword(next_st);
      unget_char(ch,tstream_ptr);
      token_ptr.token_string[0]=0;//'\0'
      return(token_ptr);
    }
    unget_char(ch,tstream_ptr);
  }// These are all special SPECIAL character
  else if (next_st == 19 || next_st == 20 || next_st == 21 || next_st == 22 ||
	   next_st == 23 ||  next_st == 24 || next_st == 25 || next_st == 32){
    token_ptr.token_id=special(next_st);
    token_ptr.token_string[0]=0;//'\0'
    return token_ptr;
  } // These are constant cases
  else if (next_st == 27 || next_st == 29){
    token_ptr.token_id=constant(next_st,token_str,token_ind);
    get_actual_token(token_str,token_ind);
    strcpy(token_ptr.token_string,token_str);
    return(token_ptr);
  }//This is COMMENT case
  else if (next_st == 30){
    skip(tstream_ptr);
    token_ind=0;
    next_st=0;
  }
  cu_state=next_st;
  ch=get_char(tstream_ptr,0);
  return token_ptr;
   //return get_token_loop(tstream_ptr, token_ptr, ch, cu_state, token_ind);
}

token get_token(cstream tstream_ptr, token token_ptr)
  requires tstream_ptr::cstream<fp,sind,s>*token_ptr::token<_,ts> & dom(s,0,80) & s[80]=0 
          & sind>=1 & sind<=80 & dom(ts,0,80) & Term
  requires false
  ensures true;
{
  int token_ind;      /* Index to the token_str  */
  int ch;
  int cu_state;//,token_found;

  //token_ptr=(token)(malloc(sizeof(struct token_type)));
  ch=get_char(tstream_ptr,0);
  cu_state=0;
  token_ind=0;
  //token_found=0;
  // while(!token_found)
  // {
  return get_token_loop(tstream_ptr, token_ptr, ch, cu_state, token_ind);
}

/* ******************************************************************
   Function name : numeric_case
   Input         : tstream_ptr,token_ptr,ch,token_str,token_ind
   Output        : token_ptr;
   Exceptions    : none 
   Description   : It checks for the delimiter, if it is then it
                   forms numeric token else forms error token.
 * ****************************************************************** */
 void numeric_case_loop (ref int token_ind, ref cstream tstream_ptr, ref int [] token_str,ref int ch)
  requires tstream_ptr::cstream<fp,sind,s> & dom(s, 0, 80) & s[80]=0 & sind>=1 & sind<=80
   & dom(token_str, 0, 80) & token_ind>=1 & token_ind<=80 & Term[80-token_ind]
 case{
   (ch<48 | ch>57 & ch<65 | ch>90 & ch<97 | ch>122)-> ensures tstream_ptr'::cstream<fp,sind,s> & token_ind'=token_ind & token_str'=token_str & ch'=ch;/*true case*/
   (ch>=48 & ch<=57 | ch>=65 & ch<=90 | ch>=97 & ch<=122) -> case {
   token_ind=80 -> ensures tstream_ptr'::cstream<fp,sind,s> & token_ind'=token_ind &
     token_str'=token_str & ch'=ch;//'
   token_ind<80 -> ensures tstream_ptr'::cstream<fp,sind1,s1> & dom(s1, 0, 80) & sind1>=1 & sind1<=80 & s1[80]=0 & dom(token_str', 0, 80) & token_ind'>token_ind & token_ind'<=80;
   //  &token_str'[token_ind'-1]=ch';//' &
     token_ind>80 -> ensures true;//unreachable
   }/*false case*/
}
 //  ensures true;//token_ind'>=80;//'
{
  /*
    while(check_delimiter(ch)==false)
	    {
		if(token_ind >= 80) break; // Added protection - hf
		token_str[token_ind++]=ch=get_char(tstream_ptr);
	    }
   */
  if (!check_delimiter(ch))
    {
      //assume(token_ind < 80);
      if(token_ind >= 80) return;
      ch=get_char(tstream_ptr,0);
      token_str[token_ind]=ch;
      token_ind = token_ind+1;
      numeric_case_loop(token_ind, tstream_ptr,token_str, ch);
    }
}

void strcpy(ref int [] des, int [] src)
  requires dom(des, 0, 80) & dom(src, 0, 80) & Term
  ensures  dom(des', 0, 80) & identical(des', src,0, 80);//'

//ensures more precise info at token_ptr.token_string
token numeric_case(ref cstream tstream_ptr, ref token token_ptr, int ch, int[] token_str, int token_ind)
  requires tstream_ptr::cstream<fp,sind,s>*token_ptr::token<id,tstring> & dom(s, 0, 80)&
	 s[80]=0 & sind>=1 & sind<=80 & token_ind>=1 & token_ind<=80 &
	 dom(tstring, 0, 80) & dom(token_str, 0, 80) & Term
 case{
  (ch<48 | ch>57 & ch<65 | ch>90 & ch<97 | ch>122)-> ensures tstream_ptr'::cstream<fp,sind1,s1>*token_ptr'::token<id1,tstring1> & id1=18 & res=token_ptr';/*true case*///'
    (ch>=48 & ch<=57 | ch>=65 & ch<=90 | ch>=97 & ch<=122) -> ensures tstream_ptr'::cstream<fp,sind1,s1>*token_ptr'::token<id1,tstring1> & id1=-1 & res=token_ptr';//'
 }/*false*/
{
  if(!check_delimiter(ch)){   /* Error case */
    token_ptr.token_id=-1;//ERROR
    numeric_case_loop(token_ind, tstream_ptr, token_str, ch);
    unget_char(ch,tstream_ptr);
    token_ind = token_ind-1;
    get_actual_token(token_str,token_ind);
    strcpy(token_ptr.token_string,token_str);
    return token_ptr;
  }
  token_ptr.token_id=18; /*NUMERIC 18  Numeric case */
  unget_char(ch,tstream_ptr);
  token_ind = token_ind-1;
  get_actual_token(token_str,token_ind);
  strcpy(token_ptr.token_string,token_str);
  return token_ptr;
}

/* *****************************************************************
   Function name : error_or_eof_case 
   Input         : tstream_ptr,token_ptr,cu_state,token_str,token_ind,ch
   Output        : token_ptr 
   Exceptions    : none 
   Description   : This function checks whether it is EOF or not.
                   If it is it returns EOF token else returns ERROR 
                   token.
 * *****************************************************************/
//can be more precise spec if necessary
token error_or_eof_case(ref cstream tstream_ptr, ref token token_ptr,int cu_state,int[] token_str,int token_ind, int ch) 
  requires tstream_ptr::cstream<fp,sind,s>*token_ptr::token<_, tstring>  & s[80]=0 & sind>=1 & sind<=80 & token_ind>=1
        & token_ind<=80 & dom(token_str, 0, 80) & dom(s, 0, 80) & dom(tstring, 0, 80) & Term
case{
  s[sind-1]=-2 /*EOF*/->
  ensures tstream_ptr'::cstream<fp,sind,s>*token_ptr'::token<0,tstring1>&dom(tstring1,0,80) & identicalEx1(tstring1,tstring,0,80,0) & tstring1[0]=0 &res=token_ptr';//'
  s[sind-1]!=-2/*ERROR*/ ->
 case{
   cu_state=0 -> ensures tstream_ptr'::cstream<fp,sind1,s1>
    *token_ptr'::token<id,tstring1>&dom(tstring1,0,80) & id=-1 & res=token_ptr';//'
   cu_state!=0 ->ensures tstream_ptr'::cstream<fp,sind1,s1>*token_ptr'::token<id,tstring1>&dom(tstring1,0,80) & id=-1 &
   res=token_ptr';//'
  }
}
{
  if(is_end_of_character_stream(tstream_ptr)){
	token_ptr.token_id = 0;//EOTSTREAM 0
	token_ptr.token_string[0]=0;//'\0'
	return(token_ptr);
  }
  if(cu_state !=0){
	unget_char(ch,tstream_ptr);
    token_ind = token_ind-1;
  }
  token_ptr.token_id=-1;//ERROR
  get_actual_token(token_str,token_ind);
  strcpy(token_ptr.token_string,token_str);
  return(token_ptr);
}

/* *********************************************************************
   Function name : check_delimiter
   Input         : character
   Output        : boolean
   Exceptions    : none.
   Description   : This function checks for the delimiter. If ch is not
                   alphabet and non numeric then it returns TRUE else 
                   it returns FALSE. 
 * ******************************************************************* */
bool isalpha(int ch)
   requires Term
 case{
  ch < 65 -> ensures !res;
  ch>=65 & ch<=90 -> ensures res;
  ch>90 & ch<97 -> ensures !res;
  ch>=97 & ch<=122 -> ensures res;
  ch>122 -> ensures !res;
}

bool isdigit(int ch)
   requires Term
 case{
  ch < 48 -> ensures !res;
  ch>=48 & ch<=57 -> ensures res;
  ch>57 -> ensures !res;
}

bool check_delimiter(int ch)
   requires Term
 case{
  ch < 48 -> ensures res;
  ch>=48 & ch<=57 -> ensures !res;
  ch>57 & ch<65 -> ensures res;
  ch>=65 & ch<=90 -> ensures !res;
  ch>90 & ch<97 -> ensures res;
  ch>=97 & ch<=122 -> ensures !res;
  ch>122 -> ensures res;
}
{
  if(!isalpha(ch))
    if(!isdigit(ch)) /* Check for digit and alpha */
      return(true);
  return(false);
}

/* ********************************************************************
   Function name : keyword
   Input         : state of the DFA
   Output        : Keyword.
   Exceptions    : If the state doesn't represent a keyword it exits.
   Description   : According to the final state specified by state the
                   respective token_id is returned.
 * ***************************************************************** */

int keyword(int state)
  requires Term
 case {
  state = 6 -> ensures res = 6; state = 9 -> ensures res = 9;
  state = 11 -> ensures res = 11; state = 13 -> ensures res = 13;
  state = 16 -> ensures res = 16;
  state!=6 & state!=9 & state!=11 & state!=13 & state!=16 -> ensures res = -1;
}
{
  /* Return the respective macro for the Keyword. */
  if (state == 6) return 6;//LAMBDA 6
  else if (state == 9) return 9;//AND 9
  else if (state == 11) return 11;//OR 11
  else if (state == 13) return 13;//IF 13
  else if (state == 16) return 16;//XOR 16
  else return -1;// error
}

/* ********************************************************************
   Function name : special
   Input         : The state of the DFA.
   Output        : special symbol.
   Exceptions    : if the state doesn't belong to a special character
                   it exits.
   Description   : This function returns the token_id according to the
                   final state given by state.
 * ****************************************************************** */

int special(int state)
 requires Term
 case {
  state = 19 -> ensures res = 19; state = 20 -> ensures res = 20;
  state = 21 -> ensures res = 21; state = 22 -> ensures res = 22;
  state = 23 -> ensures res = 23; state = 24 -> ensures res = 24;
  state = 25 -> ensures res = 25; state = 32 -> ensures res = 32;
  state!=19 & state!=20 & state!=21 & state!=22 &state!=23 & state!=24 &
  state!=25 & state!=32 -> ensures res = -1;
}
{
  //return the respective macro for the special character.
   if (state == 19) return 19;//LPAREN 19
  else if (state == 20) return 20;//RPAREN 20
  else if (state == 21) return 21;//LSQUARE 21
  else if (state == 22) return 22;//RSQUARE 22
  else if (state == 23) return 23;//QUOTE 23
  else if (state == 24) return 24;//BQUOTE 24
  else if (state == 25) return 25;//COMMA 25
  else if (state == 32) return 32;//EQUALGREATER 32
  else return -1;// error
}

/* **********************************************************************
   Function name : skip
   Input         : character_stream
   Output        : void.
   Exceptions    : none.
   Description   : This function skips the comment part of the program.
                   It takes charcter_stream as input and reads character
                   until it finds new line character or
                   end_of_character_stream.
 * ******************************************************************* */
//Assume the file size is finite by the constraint line_num<=100
void skip_loop (ref int c, ref cstream stream_ptr, ref int line_num)
  requires stream_ptr::cstream<fp,sind,s> & dom(s,0,80) & sind>=1 & sind<=80 & s[80]=0 & line_num<=100
  case {
  c=10 | s[sind-1]=-2 -> 
	requires Term 
	ensures stream_ptr'::cstream<fp,sind,s> & c'=c;
  c!=10 & s[sind-1]!=-2 -> 
	requires Term[100-line_num,80-sind] 
	ensures stream_ptr'::cstream<fp,sind1,s1> & dom(s1,0,80) & sind1>=1 & sind1<=80 & s1[80]=0; //'
 }
{
  /*
  while((c=get_char(stream_ptr))!='\n' &&
               !is_end_of_character_stream(stream_ptr))
    ; // Skip the characters until EOF or EOL found.
  */
  if (line_num<100) {
	  if (c!=10)//'\n'
		if (!is_end_of_character_stream(stream_ptr)) {
		  c=get_char(stream_ptr,line_num);
		  skip_loop(c, stream_ptr,line_num);
		}
  }
  return;
}
void skip(ref cstream stream_ptr)
  requires stream_ptr::cstream<fp,sind,s> & dom(s,0,80) & sind>=0 & sind<=80 & s[80]=0 & Term
  ensures  stream_ptr'::cstream<fp,sind1,s1> & dom(s1,0,80) & sind1>=0 & sind1<=80 & s1[80]=0;//'
{
  int c;
  int line_num = 0;
  c=get_char(stream_ptr,line_num);
  skip_loop(c, stream_ptr,line_num);
  if(c==-2) unget_char(c, stream_ptr);//EOF -2
  // Put back to leave gracefully - hf
  return;
}

/* *********************************************************************
   Function name : constant
   Input         : state of DFA, Token string, Token id.
   Output        : constant token.
   Exceptions    : none.
   Description   : This function returns the token_id for the constatnts
                   speccified by  the final state. 
 * ****************************************************************** */

int constant(int state,ref int[] token_str,int token_ind)
  requires dom(token_str, 0, 80) & Term
 case{
  state = 27 -> ensures dom(token_str', 0, 80) & res=27 & token_str'=token_str;
  state = 29 -> requires token_ind>=1 & token_ind<=80
  ensures dom(token_str', 0, 80) & identicalEx1(token_str',token_str, 0, 80,token_ind-1) & token_str'[token_ind-1]= 32 & res=29;//'
  state!=27 & state!=29 ->ensures dom(token_str',0,80) & token_str'=token_str & res=-1;
}
{
  //Return the respective CONSTANT macro.
  if(state == 27) return 27;//STRING_CONSTANT 27
  else if (state == 29){
    token_str[token_ind-1]= 32;//' ' 32
    return 29;
  }//CHARACTER_CONSTANT 29
  else return -1;//error
}


/* *******************************************************************
   Function name : next_state
   Input         : current state, character
   Output        : next state of the DFA
   Exceptions    : none.
   Description   : This function returns the next state in the transition
                   diagram. The next state is determined by the current
                   state state and the inpu character ch.
 * ****************************************************************** */
int base(int i)
			    /* requires i=0|i=1|i=2|i=3|i=4|i=5|i=6|i=8|i=9|i=10|i=11|i=12|i=13|i=13|i=14|i=15|i=16|
            i=17|i=18|i=26|i=31|i=32|i=51|i=52|i=54
			    */
  requires i>=0 & i<=59 & Term
  case {
  i=31 -> ensures res=0;//v1
  i=0 -> ensures res=-32;//v2
  i=5 -> ensures res=-87;//v3
  i=27 -> ensures res=-1;//v4
  i=28 -> ensures res=233;//v4
  i=10 -> ensures res=-99;//v6
  i=17 -> ensures res=53;//v6
  i=51 -> ensures res=46;//v6
  i!=31 & i!=0 & i!=5 & i!=27 & i!=28 & i!=10 & i!=17 & i!=51-> ensures res>=-105 & res<=232;
}
                           /*
  case{
  i=0-> ensures res=-32;
  i=1 -> ensures res=-96;
  i=2 -> ensures res=-105;
  i=6|i=9|i=11|i=13|i=16-> ensures res=-1;
  i=17-> ensures res=53;
  i=51-> ensures res=46;
  i=52-> ensures res=40;
  i=54-> ensures res=151;
  i!=0&i!=6&i!=9&i!=11&i!=13&i!=16&i!=17&i!=51&i!=52&i!=54 -> ensures true;//unreachable
}
                            */
/*
requires i=0|i=6|i=9|i=11|i=13|i=16|i=17|i=51|i=52|i=54
 ensures i=-3|i=-1|i=0|i=6|i=9|i=11|i=13|i=16|i=17|i=51|i=52|i=54;
-3 -1 0 6 9 11 13 16 17 51 52 54
*/
int default1(int i)
 requires i>=0 & i<=59 & Term
  case{
  i<0 -> ensures true;
  i=0 ->  ensures res=54;
  i>=1 & i<=16 -> ensures res=17;
  i=17 -> ensures res=51;
  i=18 -> ensures res=-2;
  i>=19 & i<=50 -> ensures res=-1;
  i=51 -> ensures res=52;
  i=52 -> ensures res=-3;
  i>=53 & i<=59 -> ensures res=-1;
  i>59 -> ensures true;
}

int next(int i)
 requires i>=0 & i<=359 & Term
  case {
  i=62 -> ensures res=32;//v1
  i=73 -> ensures res=12;//v2
  i=10 -> ensures res=6;//v3
  i=359 -> ensures res=29;//v4
  i=27 -> ensures res=30;//v5
  i=128 -> ensures res=17;//v6
  i=164 -> ensures res=-1;//v6
  i!=62 & i!=73 & i!=10 & i!=359 & i!=27 & i!=164& i!=128->ensures res>=-1 & res<=32 & res!=7 & res!=28;
}

int check(int i)
 requires i>=0 & i<=359 & Term
  case{
  i=62 -> ensures res=31;//v1
  i=73-> ensures res=0;//v2
  i=10 -> ensures res=5;//v3
  i=359 -> ensures res=28;//v4
  i=27 -> ensures res=0;//v5
  i=164 -> ensures res=-1;//v6
  i=135|i=128 -> ensures res=51;//v6
  i!=62 & i!=73 & i!=10& i!=359 & i!=27 & i!=164&i!=135&i!=128 -> ensures res>=-1 & res<=54;
}
			    /*
state=-3|state=-2|state=-1|state=0|state=1|state=2|state=3|state=4|state=5|state=6|
            state=8|state=9|state=10|state=11|state=12|state=13|state=13|state=14|state=15|state=16|
            state=17|state=18|state=26|state=31|state=32|state=51|state=52|state=54 //from default1
     //from get_token
			    */
int next_state(int state, int ch) 
 requires state>=-3 & state<=54 & ch>=-2 & ch<=126 //-2 EOF
  case {
  state<0 -> requires Term ensures res=state;
  state=0 -> requires Term case {
    ch=105 -> ensures res=12; //v2
    ch=59  ->  ensures res=30; //v5
    ch!=105 & ch!=59 -> ensures res>=-3 & res<=32 & res!=7 & res!=28;
  }
  state=5 -> requires Term case {
    ch=97 -> ensures res=6; //v3
    ch!=97 -> ensures res>=-3 & res<=32 & res!=7 & res!=28;
  }
  state=10 | state=17 | state=51 -> requires Term[54-state] case {
    ch=82 -> ensures res=17; //v6
    ch!=82 -> ensures res>=-3 & res<=32 & res!=7 & res!=28;
  }
  state=28 -> requires Term case {
    ch=126 -> ensures res=29; //v4
    ch!=126 -> ensures res>=-3 & res<=32 & res!=7 & res!=28;
  }
  state=31 -> requires Term case {
    ch=62 -> ensures res=32; //v1
    ch!=62 -> ensures res>=-3 & res<=32 & res!=7 & res!=28;
  }
  state>0 & state!=5 & state!=10 & state!=17 & state!=51 & state!=28 & state!=31 -> 
		requires Term[54-state] ensures res>=-3 & res<=32 & res!=7 & res!=28;
}
{
  int tmp;
  if(state < 0)
    return(state);
  tmp = base(state);
  if(tmp+ch >= 0)
  {
    if(check(tmp+ch) == state) /* Check for the right state */
      return(next(tmp+ch));
    else
      return(next_state(default1(state),ch));
  }
  else
    return(next_state(default1(state),ch));
}

/* *********************************************************************
   Function name : is_eof_token
   Input         : token
   Output        : Boolean
   Exceptions    : none.
   Description   : This function checks whether the token t is eof_token 
                   or not. If the integer value stored in the t is
                   EOTSTREAM then it is eof_token.
 * ***************************************************************** */

bool is_eof_token(token t)
requires t::token<id, _> & Term //& dom(tstring, 0, 79)
  case {
  id=0 -> ensures res;
  id!=0 -> ensures !res;
 }
{
  if(t.token_id==0)//EOTSTREAM 0
        return true;
    return false;
}

/* ********************************************************************
   Function name : print_token
   Input         : token
   Output        : Boolean
   Exceptions    : none.
   Description   : This function  prints the token. The token_id gives 
                   the type of token not the token itself. So, in the
                   case of identifier,numeric,  string,character it is
                   required to print the actual token  from token_str. 
                   So, precaution must be taken when printing the token.
                   This function is able to print the current token only
                   and it is the limitation of the program.
 * ******************************************************************** */

bool print_token(token token_ptr)
 requires token_ptr::token<id, _> & Term //& dom(tstring, 0, 79)
  case{
 id=-1 | id=0 | id=6 | id=9 | id=11 | id=13 | id=16 | id=17 | id=18 | id=19 | id=20
 | id=21 | id=22 | id=23 | id=24 | id=25 | id=27 | id=29 | id=32 -> ensures res;
 id!=-1 & id!=0 & id!=6 & id!=9 & id!=11 & id!=13 & id!=16 & id!=17 & id!=18 & id!=19 &
 id!=20 & id!=21 & id!=22&id!=23&id!=24&id!=25&id!=27&id!=29 & id!=32 -> ensures !res;
}
{
  // Print the respective tokens.
  if (token_ptr.token_id == -1) //ERROR -1
    //fprintf(stdout, "error,\t\"");fprintf(stdout, "%s",token_ptr->token_string);
    return true;
  else if (token_ptr.token_id == 0) //EOTSTREAM 0
    //fprintf(stdout, "eof.\n");return(TRUE);
    return true;
   else if (token_ptr.token_id == 6)
     //fprintf(stdout, "keyword,\t\"lambda\".\n");
    return true;
   else if (token_ptr.token_id == 9)
     // fprintf(stdout, "keyword,\t\"and\".\n");
    return true;
   else if (token_ptr.token_id == 11)
     //fprintf(stdout, "keyword,\t\"or\".\n");
    return true;
   else if (token_ptr.token_id == 13)
     // fprintf(stdout, "keyword,\t\"if\".\n");
    return true;
   else if (token_ptr.token_id == 16)
     // fprintf(stdout, "keyword,\t\"if\".\n");
    return true;
   else if (token_ptr.token_id == 17)
     // fprintf(stdout, "identifier,\t\"");fprintf(stdout, "%s",token_ptr->token_string);
    return true;
   else if (token_ptr.token_id == 18)
     //fprintf(stdout, "numeric,\t");fprintf(stdout, "%s",token_ptr->token_string);
     return true;
   else if (token_ptr.token_id == 19)
     // fprintf(stdout, "lparen.\n");
     return true;
   else if (token_ptr.token_id == 20)
     // fprintf(stdout, "rparen.\n");
     return true;
   else if (token_ptr.token_id == 21)
     //fprintf(stdout, "lsquare.\n");
     return true;
   else if (token_ptr.token_id == 22)
     //fprintf(stdout, "rsquare.\n");
     return true;
   else if (token_ptr.token_id == 23)
     //fprintf(stdout, "quote.\n");
    return true;
   else if (token_ptr.token_id == 24)
     //fprintf(stdout, "bquote.\n");
     return true;
   else if (token_ptr.token_id == 25)
     // fprintf(stdout, "comma.\n");
    return true;
  else if  (token_ptr.token_id == 27)
     // fprintf(stdout, "string,\t");fprintf(stdout, "%s",token_ptr->token_string);
    return true;
  else if  (token_ptr.token_id == 29)
     //fprintf(stdout, "character,\t\"");fprintf(stdout, "%s",token_ptr->token_string);
    return true;
  else if  (token_ptr.token_id == 32)
     // fprintf(stdout, "keyword,\t\"=>\".\n");
    return true;
  else return false;
}

/* **********************************************************************
   Function name : get_actual_token
   Input         : token string and token id.
   Output        : void.
   Exceptions    : none.
   Description   : This function prints the actual token in the case of
                   identifier,numeric,string and character. It removes
                   the leading and trailing  spaces and prints the token.
 * ****************************************************************** */
bool isspace(int c)
	requires Term
  case { c=32 -> ensures res; c!=32 -> ensures !res;}

  /*
case {
  ind=0 |ind=-1 ->  ensures dom(token_str', 0, 79) & ind'=ind & token_str'=token_str;//'
  ind>0 -> ensures dom(token_str', 0, 79) & ind'>=0 & ind'<=ind &
    token_str'=token_str & identicalChar(token_str',ind',ind-1,32);//'
  ind < -1 -> ensures true; //unreacheable
}
*/
void gat_loop1(ref int [] token_str,ref int ind)
 requires dom(token_str, 0, 80) & ind>=0 & ind<=80 & Term[ind]
 ensures dom(token_str', 0, 80) & ind'>=0 & ind'<=ind &
token_str'=token_str & identicalChar(token_str',ind',ind-1,32);//'
{
  if (ind>0)
    if (isspace(token_str[ind-1]))
    {
      ind = ind -1;
      gat_loop1(token_str, ind);
    }
  return;
}
 /*
case {
   ind=upb -> ensures dom(token_str', 0, 79) & ind'=ind & token_str'=token_str;//'
   ind<upb -> ensures dom(token_str', 0, 79) & ind'>=ind & ind'<=upb &
        token_str'=token_str & identicalChar(token_str,ind,ind'-1,32);//'
    ind>upb -> ensures true;
}
*/
 void gat_loop2(ref int [] token_str, ref int ind, int upb)
 requires dom(token_str, 0, 80) & ind>=0 & ind<=upb & upb >=0 & upb <=80 & Term[upb-ind]
 ensures dom(token_str', 0, 80) & ind'>=ind & ind'<=upb &
        token_str'=token_str & identicalChar(token_str,ind,ind'-1,32);//'
{
  //for(ind=0;ind<token_ind;++ind)
  //if(!isspace(token_str[ind]))
  //   break;
  if (ind<upb)
    if (isspace(token_str[ind]))
    {
      ind = ind +1;
      gat_loop2(token_str, ind, upb);
    }
  return;
}

void strcpy_dist(ref int [] des, int [] src, int ind)
requires dom(des, 0, 80) & dom(src, 0, 80) & ind >=0 & ind <=80 & Term
  ensures dom(des', 0, 80) & identical_dist(des', src,0, 80,ind);//'

void get_actual_token(ref int [] token_str,int token_ind)
 requires dom(token_str, 0, 80) & token_ind>=0 & token_ind<=80 & Term
 ensures  dom(token_str', 0, 80);//'should be more precise if necessary
{
  int ind,start;
  ind=token_ind;
  gat_loop1(token_str, ind);
  //Delete the trailing white spaces & protect - hf
  token_str[ind]=0;//'\0'
  token_ind=ind;
  ind=0;
  gat_loop2(token_str, ind, token_ind);
  strcpy_dist(token_str,token_str, ind);
  // for(start=0;ind<=token_ind;++start,++ind)
  // Delete the leading white spaces.
  //  token_str[start]=token_str[ind];
  return;
}
