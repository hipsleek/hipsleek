#include <stdio.h>
#include <sys/types.h>
#include <unistd.h>
#include <malloc.h>
#include <string.h>

int main(int argc, char** argv) {
  char           buf[2560];
  FILE         * file;
  FILE * log_file;
  void *tmp;
  int n = strlen("VmPeak:");

  if (argc != 3) {
	printf("Usage: %s <pid> <logfile>\n", argv[0]);
	exit(-1);
  }

  snprintf(buf, sizeof(buf), "/proc/%s/status", argv[1]);

  if ((file = fopen( buf, "r" )) == NULL) {
	perror( "open" );
	return 0;
  }

  if ((log_file = fopen(argv[2], "a") == NULL) {
		perror("open");
		exit(-1);
	  }

  while (1) {
	fgets( buf, sizeof(buf), file );
	if (!strncmp(buf, "VmPeak:", n)) {
	  
	}
  }
    
  return 0;
}


