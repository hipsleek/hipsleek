#include <signal.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/wait.h>
#include <stdlib.h>
#include <string.h>

int main()
{
	char buffer[500];
	int fd[2], fd2[2];
	pipe(fd);
	pipe(fd2);  /* just 1 pipe is enough...no need for 2 pipes */
	pid_t pid = fork();
	if(pid == 0) {
		dup2(fd[0], STDIN_FILENO);
		close(fd[0]);  /* no need redirecting stdin because the child isnt getting any external input */
		close(fd[1]);
		
		dup2(fd2[1], STDOUT_FILENO);
		close(fd2[0]);  /* this also doesnt make sense but you dont need 2 pipes */
		close(fd2[1]);
		
		execlp("/home/locle/workspace/omega/omega_calc/obj/oc", "/home/locle/workspace/omega/omega_calc/obj/oc", (char*)0);
		//execlp("./lexEx", "./lexEx", (char*)0);
		//execlp("./oc_test", "./oc_test", (char*)0);
		//execlp("/usr/local/bin/oc", "/usr/local/bin/oc", 0);
	}
	else {
	    FILE *fwriter;
	
	fwriter = fopen(".test", "w");
	fprintf(fwriter, "%s\n", buffer);
	fflush(fwriter);
	
	
	
		close(fd2[1]);
		read(fd2[0], buffer, 500);
		//printf("test==>welcome: %s", buffer);
		//fflush(stdout);
		
		fprintf(fwriter, "%s\n", buffer);
	fflush(fwriter);
	
		
		memset(&buffer[0], 0, sizeof(buffer));
		
		close(fd[0]);
		//first cmd--------------------------------------------
		//fgets(buffer, 500, stdin);
		sprintf(buffer, "%s\n", "{[i ] : ((i<5)&(i>7))};"); 
		//sprintf(buffer, "%s\n", "stop"); 
		
		
		//send cmd to oc
		write(fd[1], buffer, strlen(buffer));
		//fflush(fd[1]);
		memset(&buffer[0], 0, sizeof(buffer));
		//receive the result
		int stop = 0;
		while (stop == 0){
		  read(fd2[0], buffer, 500);
		  fprintf(fwriter, "%s\r\n", buffer);
	      fflush(fwriter);
		  //printf("test==> %s",buffer);
		  if (buffer[0] != '#')
		    stop = 1;
		  else
		    memset(&buffer[0], 0, sizeof(buffer));
		
		}	
		
		//second cmd-------------------------------------------------
		sprintf(buffer, "%s\n", "complement{[i,iPRMD]:(((not((exists(i:(((i<0)&(i<-5))&(iPRMD=i+10))))))|(iPRMD>15)))};"); 
		//sprintf(buffer, "%s\n", "stop"); 
				
		//send cmd to oc
		write(fd[1], buffer, strlen(buffer));
		//fflush(fd[1]);
		memset(&buffer[0], 0, sizeof(buffer));
		//receive the result
		stop = 0;
		while (stop == 0){
		  read(fd2[0], buffer, 500);
		  fprintf(fwriter, "%s\r\n", buffer);
	      fflush(fwriter);
		  //printf("test==> %s",buffer);
		  if (buffer[0] != '#')
		    stop = 1;
		  else
		    memset(&buffer[0], 0, sizeof(buffer));
		
		}	
		
		printf("test==> bye\n");
		
		fflush(stdout);
		
		close(fd[1]);
		close(fd2[0]);
		
		fclose(fwriter);
	}
	
	return 0;
}