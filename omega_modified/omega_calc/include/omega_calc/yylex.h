//modified by locle 16384
#ifndef YY_EXIT_FAILURE
#define YY_EXIT_FAILURE 2
#endif
#ifndef YY_BUF_SIZE
#define YY_BUF_SIZE 16384
#endif
typedef struct yy_buffer_state *YY_BUFFER_STATE;
typedef unsigned int yy_size_t;
//--------------------------------------------
extern int yylex(void);
extern void yyerror(const char *);
extern void initializeScanBuffer();
extern void flushScanBuffer();

//modified by locle
extern YY_BUFFER_STATE yy_scan_buffer(char *, yy_size_t);
extern YY_BUFFER_STATE yy_scan_bytes(const char *, int);
extern void yy_switch_to_buffer ( YY_BUFFER_STATE );
extern YY_BUFFER_STATE yy_create_buffer ( FILE *, int  );