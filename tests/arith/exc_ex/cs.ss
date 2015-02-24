data socket 
{
	int name;
	int port;
}
data BufferedReader{}
data InputStream{}
data InputStreamReader{InputStream is; }
data PrintWriter{}
data OutputStream{}

class IOException extends __Exc {}

void println(PrintWriter p, int i) requires true ensures true {}

int read(BufferedReader br) throws IOException 
			requires br::BufferedReader<> ensures br::BufferedReader<>& flow __normal;
			requires br::BufferedReader<> ensures br::BufferedReader<>& flow IOException;
			{return 0;}
			
OutputStream getOutputStream(socket s) throws IOException
	requires s::socket<> ensures s::socket<>*res::OutputStream<> & flow __normal;
	requires s::socket<> ensures s::socket<> & flow IOException;
	{return new OutputStream();}
 
InputStream getOutputStream(socket s) throws IOException
	requires s::socket<> ensures s::socket<>*res::InputStream<> & flow __normal;
	requires s::socket<> ensures s::socket<> & flow IOException;
	{return new InputStream();} 




void client_main() {

      Socket         sock = null;                              // Socket object for communicating
      PrintWriter     pw   = null;                              // socket output to server
      BufferedReader  br   = null;                              // socket input from server
 
      try {
            sock = new Socket(serverIPname,serverPort);       // create socket and connect
            pw   = new PrintWriter(getOutputStream(sock));  // create reader and writer
            br   = new BufferedReader(new InputStreamReader(getInputStream(sock)));
            println(2);
 
            pw.println("Message from the client");                      // send msg to the server
            println("Sent message to server");
            int answer = readLine(br);                              // get data from the server
            println("Response from the server >" + answer);
 
            pw.close();                                                 // close everything
            br.close();
            sock.close();
      } catch (Throwable e) {
            println("Error " + e.getMessage());
            e.printStackTrace();
      }
}
}
 
void server_main() {
      ServerSocket   sock = null;                              // original server socket
      Socket         clientSocket = null;                      // socket created by accept
      PrintWriter     pw   = null;                              // socket output stream
      BufferedReader  br   = null;                              // socket input stream
 
      try {
            sock = new java.net.ServerSocket(serverPort);               // create socket and bind to port
            System.out.println("waiting for client to connect");
            clientSocket = sock.accept();                               // wait for client to connect
            System.out.println("client has connected");
            pw   = new java.io.PrintWriter(clientSocket.getOutputStream(),true);
            br   = new java.io.BufferedReader(
new java.io.InputStreamReader(clientSocket.getInputStream()));
 
            String msg = br.readLine();                                 // read msg from client
            println("Message from the client >" + msg);
            pw.println("Got it!");                                      // send msg to client
 
            pw.close();                                                 // close everything
            br.close();
            clientSocket.close();
            sock.close();
      } catch (Throwable e) {
            System.out.println("Error " + e.getMessage());
            e.printStackTrace();
      }
}
}